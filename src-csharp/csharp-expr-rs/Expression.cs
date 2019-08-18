using System;
using System.Collections.Generic;
using System.Text;

namespace csharp_expr_rs
{
    public interface IExpression : IDisposable
    {
        string Execute();
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

        public string Execute()
        {
            var stringHandle = Native.ffi_exec_expr(_expressionHandle);
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
