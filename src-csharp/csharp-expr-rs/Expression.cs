using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs
{
    public class SomeTest
    {
        public void Test()
        {
            unsafe
            {
                var str = "test";

                fixed (char* ptr = str)
                {
                    var len = (UIntPtr)(str.Length * sizeof(char));
                    Native.ffi_test(new FFICSharpString { ptr = ptr, len = len }).AsStringAndDispose();
                }
            }
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
            unsafe
            {
                var idValues = identifierValues
                    .Where(kv => _identifiers.Contains(kv.Key))
                    .Select(kv =>
                    {
                        var str = kv.Value;
                        var len = (UIntPtr)(str.Length * sizeof(char));
                        fixed (char* ptr = str)
                        {
                            return new FFIIdentifierKeyValue { key = kv.Key, value = new FFICSharpString { ptr = ptr, len = len } };
                        }
                    })
                    .ToArray();

                string result = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length)
                    .AsStringAndDispose();

                return result;
            }
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
