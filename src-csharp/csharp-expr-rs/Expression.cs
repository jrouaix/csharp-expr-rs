using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs
{
    static class StringExtensions
    {
        public static FFICSharpString MakeFFICSharpString(this string str)
        {
            unsafe
            {
                fixed (char* ptr = str)
                {
                    var len = (UIntPtr)(str.Length * sizeof(char));
                    var sharpString = new FFICSharpString { ptr = ptr, len = len };
                    return sharpString;
                }
            }
        }
    }

    public class SomeTest
    {
        public void Test()
        {
            Native.ffi_test("test".MakeFFICSharpString()).AsStringAndDispose();

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
            : this(Native.ffi_parse_and_prepare_expr(expression.MakeFFICSharpString()))
        { }

        internal Expression(FFIExpressionHandle expressionFFIPointer)
        {
            _expressionHandle = expressionFFIPointer;
            _identifiers = new HashSet<string>(
                Native.ffi_get_identifiers(_expressionHandle)
                    .AsStringAndDispose()
                    .Split(new[] { '|' }, StringSplitOptions.RemoveEmptyEntries)
                    );
        }

        public string[] Identifiers => _identifiers.ToArray();

        readonly FFIIdentifierKeyValue[] _emptyValues = new FFIIdentifierKeyValue[0];

        public (bool is_error, string content) Execute(IReadOnlyDictionary<string, string> identifierValues)
            => Execute((IEnumerable<KeyValuePair<string, string>>)identifierValues);

        public (bool is_error, string content) Execute(IEnumerable<KeyValuePair<string, string>> identifierValues)
        {
            unsafe
            {
                var idValues = identifierValues == null
                    ? _emptyValues
                    : identifierValues
                        .Where(kv => _identifiers.Contains(kv.Key))
                        .Select(kv => new FFIIdentifierKeyValue { key = kv.Key, value = kv.Value.MakeFFICSharpString() })
                        .ToArray();

                var result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length);
                var stringResult = result.GetContent().AsStringAndDispose();
                return (result.is_error, stringResult);

                //return default;

                //Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length, out var result);


                //var result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length);
                //return (false, "");
            }
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
