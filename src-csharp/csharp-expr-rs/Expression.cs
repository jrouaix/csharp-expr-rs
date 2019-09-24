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
            var stringHandle = Native.ffi_get_identifiers(_expressionHandle);
            try
            {
                _identifiers = new HashSet<string>(
                    stringHandle
                        .AsString()
                        .Split(new[] { '|' }, StringSplitOptions.RemoveEmptyEntries)
                    );
            }
            finally
            {
                stringHandle.Dispose();
            }
        }

        public string Execute(Dictionary<string, string> identifierValues)
        {
            var idValues = identifierValues
                .Where(kv => _identifiers.Contains(kv.Key))
                .Select(kv => new FFIIdentifierKeyValue { key = kv.Key, value = kv.Value }).ToArray();

            var stringHandle = Native.ffi_exec_expr(_expressionHandle, idValues, (UIntPtr)idValues.Length);
            string result;
            try
            {
                result = stringHandle.AsString();
            }
            finally
            {
                stringHandle.Dispose();
            }
            return result;
        }

        public void Dispose()
        {
            _expressionHandle.Dispose();
        }
    }
}
