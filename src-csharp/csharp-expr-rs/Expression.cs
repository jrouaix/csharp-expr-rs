using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs
{
    /// <summary>
    /// If non sealed, implement the proper disposable pattern !
    /// </summary>
    public sealed class Expression : IDisposable
    {
        private readonly FFIExpressionHandle _expressionHandle;
        private readonly HashSet<string> _identifiers;

        public Expression(string expression)
            : this(Native.ffi_parse_and_prepare_expr(expression))
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

        public string Execute(Dictionary<string, string> identifierValues)
        {
            var idValues = identifierValues
                .Where(kv => _identifiers.Contains(kv.Key))
                .Select(kv => new FFIIdentifierKeyValue { key = kv.Key, value = kv.Value }).ToArray();

            var str = "test";// Guid.NewGuid().ToString();
            var utf8 = Encoding.UTF8.GetBytes(str);
            var utf16 = Encoding.Default.GetBytes(str);
            unsafe
            {
                //var t = (Span<string>)null;
                fixed (char* ptr = str)
                {
                    var len = (UIntPtr)(str.Length * sizeof(Char));
                    var res = Native.test(ptr, len).AsStringAndDispose();

                    var ok = str == res;
                }


                //var pCh1 = test.GetPinnableReference();
                //byte* pc = (byte*)&pCh1;

            }

            string result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length)
                .AsStringAndDispose();
            return result;
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
