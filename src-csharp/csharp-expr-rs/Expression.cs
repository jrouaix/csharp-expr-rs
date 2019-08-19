using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs
{
    public interface IExpression : IDisposable
    {
        string Execute(Dictionary<string, string> identifierValues);
    }

    public class Expression : IExpression
    {
        public Expression(string expression)
            : this(Native.ffi_parse_expr(expression))
        { }

        private readonly FFIExpressionHandle _expressionHandle;
        internal Expression(FFIExpressionHandle expressionFFIPointer)
        {
            _expressionHandle = expressionFFIPointer;
        }

        public string Execute(Dictionary<string, string> identifierValues)
        {
            var idValues = identifierValues.Select(kv => new FFIIdentifierKeyValue { key = kv.Key, value = kv.Value }).ToArray();

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
