using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Linq;
using System.Runtime.ExceptionServices;
using System.Text;

namespace csharp_expr_rs
{
    static class StringExtensions
    {
        static Encoding unicode = new UnicodeEncoding();

        public static FFICSharpStringHolder MakeFFICSharpStringHolder(this string str)
        {
            if (str == null || str.Length == 0)
            {
                return new FFICSharpStringHolder
                {
                    ffiStr = new FFICSharpString { len = (UIntPtr)0 }
                };
            }

            var result = new FFICSharpStringHolder
            {
                dotnetStr = str
            };

            unsafe
            {
                var len = (UIntPtr)(str.Length * sizeof(char));

                if (str.Length < 2)
                {
                    result.shortStr = unicode.GetBytes(str);
                    fixed (byte* ptr = result.shortStr)
                    {
                        var sharpString = new FFICSharpString { ptr = ptr, len = len };
                        result.ffiStr = sharpString;
                        return result;
                    }
                }
                else
                {
                    fixed (char* ptr = result.dotnetStr)
                    {
                        var sharpString = new FFICSharpString { ptr = (byte*)ptr, len = len };
                        result.ffiStr = sharpString;
                        return result;
                    }
                }
            }
        }
    }

    /// <summary>
    /// If non sealed, implement the proper disposable pattern !
    /// </summary>
    public sealed class Expression : IDisposable
    {
        private readonly FFIExpressionHandle _expressionHandle;
        private readonly HashSet<string> _identifiers;

        public Expression(string expression)
            : this(PrepareExpression(expression))
        { }

        [HandleProcessCorruptedStateExceptions]
        static (FFIExpressionHandle _expressionHandle, HashSet<string> _identifiers, bool isDeterministic) PrepareExpression(string expression)
        {
            try
            {
                var FFIResultPointer = Native.ffi_parse_and_prepare_expr(expression);
                if (FFIResultPointer.is_error)
                {
                    var errorMsg = FFIResultPointer.GetError().AsStringAndDispose();
                    throw new ExpressionParsingException(errorMsg);
                }

                var expressionHandle = FFIResultPointer.GetContent();
                var identifiers = new HashSet<string>(
                    Native.ffi_get_identifiers(expressionHandle)
                        .AsStringAndDispose()
                        .Split(new[] { '|' }, StringSplitOptions.RemoveEmptyEntries)
                    );
                var isDeterministic = Native.ffi_is_deterministic(expressionHandle);

                return (expressionHandle, identifiers, isDeterministic);
            }
            catch (Exception ex)
            {
                throw new ExpressionParsingException(ex.Message, ex);
            }
        }

        internal Expression((FFIExpressionHandle expressionHandle, HashSet<string> identifiers, bool isDeterministic) preparedExpression)
        {
            _expressionHandle = preparedExpression.expressionHandle;
            _identifiers = preparedExpression.identifiers;
            Identifiers = _identifiers.ToArray();
            IsDeterministic = preparedExpression.isDeterministic;
        }

        public string[] Identifiers { get; }
        public bool IsDeterministic { get; }

        readonly FFIIdentifierKeyValue[] _emptyValues = new FFIIdentifierKeyValue[0];

        public (bool is_error, string content) Execute(IReadOnlyDictionary<string, string> identifierValues)
            => Execute((IEnumerable<KeyValuePair<string, string>>)identifierValues);

        [HandleProcessCorruptedStateExceptions]
        public (bool is_error, string content) Execute(IEnumerable<KeyValuePair<string, string>> identifierValues)
        {
            try
            {
                var idValues = _emptyValues;

                if (identifierValues != null)
                {
                    idValues = identifierValues
                        .Select(kv => new FFIIdentifierKeyValue { key = kv.Key, value = kv.Value ?? string.Empty })
                        .ToArray();
                }

                var result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length);
                var stringResult = result.GetContent().AsStringAndDispose();
                return (result.is_error, stringResult);
            }
            catch (Exception ex)
            {
                throw new ExpressionInvokeException(ex.Message, ex);
            }
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
