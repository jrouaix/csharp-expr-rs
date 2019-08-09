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
            : this(CsharpExprLib.ffi_parse_expr(expression))
        { }

        private readonly CsharpExprLib.ExpressionFFIPointer _expressionFFIPointer;
        internal Expression(CsharpExprLib.ExpressionFFIPointer expressionFFIPointer)
        {
            _expressionFFIPointer = expressionFFIPointer;
        }

        public string Execute()
        {
            var stringHandle = CsharpExprLib.ffi_exec_expr(_expressionFFIPointer);

            try
            {
                return stringHandle.AsString();
            }
            finally
            {
                stringHandle.Dispose();
            }
        }

        public void Dispose()
        {
            CsharpExprLib.ffi_free_expr(_expressionFFIPointer);
        }
    }
}
