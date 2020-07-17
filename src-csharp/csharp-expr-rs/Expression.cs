using System;
using System.Collections.Generic;
using System.Collections.ObjectModel;
using System.Linq;
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

    public class SomeTest
    {
        public void Test()
        {
            Native.ffi_test("test".MakeFFICSharpStringHolder().ffiStr).AsStringAndDispose();

            //var pCh1 = test.GetPinnableReference();
            //byte* pc = (byte*)&pCh1;
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
            : this(Native.ffi_parse_and_prepare_expr(expression.MakeFFICSharpStringHolder().ffiStr))
        { }

        internal Expression(FFIParseResult FFIResultPointer)
        {
            if (FFIResultPointer.is_error)
            {
                var errorMsg = FFIResultPointer.GetError().AsStringAndDispose();
                throw new ExpressionParsingException(errorMsg);
            }

            _expressionHandle = FFIResultPointer.GetContent();
            _identifiers = new HashSet<string>(
                Native.ffi_get_identifiers(_expressionHandle)
                    .AsStringAndDispose()
                    .Split(new[] { '|' }, StringSplitOptions.RemoveEmptyEntries)
                );
            Identifiers = _identifiers.ToArray();
            IsDeterministic = Native.ffi_is_deterministic(_expressionHandle);
        }

        public string[] Identifiers { get; }
        public bool IsDeterministic { get; }

        readonly FFIIdentifierKeyValue[] _emptyValues = new FFIIdentifierKeyValue[0];

        public (bool is_error, string content) Execute(IReadOnlyDictionary<string, string> identifierValues)
            => Execute((IEnumerable<KeyValuePair<string, string>>)identifierValues);

        public (bool is_error, string content) Execute(IEnumerable<KeyValuePair<string, string>> identifierValues)
        {
            unsafe
            {
                var idValues = _emptyValues;

                (string key, FFICSharpStringHolder holder)[] holders;

                if (identifierValues != null)
                {
                    holders = identifierValues
                        .Where(kv => _identifiers.Contains(kv.Key))
                        .Select(kv => (kv.Key, kv.Value.MakeFFICSharpStringHolder()))
                        .ToArray();
                    idValues = holders
                        .Select(h => new FFIIdentifierKeyValue { key = h.key, value = h.holder.ffiStr })
                        .ToArray();
                }

                var result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length);
                var stringResult = result.GetContent().AsStringAndDispose();
                return (result.is_error, stringResult);
            }
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
