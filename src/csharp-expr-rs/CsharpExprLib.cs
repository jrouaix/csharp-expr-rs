using System;
using System.Runtime.InteropServices;


namespace csharp_expr_rs
{
    public interface IExpression : IDisposable
    {
        string Execute();
    }

    public static class CsharpExprLib
    {
        public const string LIB_NAME = "csharp_expr.dll";

        [StructLayout(LayoutKind.Sequential)]
        public struct ExpressionFFIPointer
        {
            public IntPtr expression;
        }

        [DllImport(LIB_NAME)]
        static extern ExpressionFFIPointer ffi_parse_expr(string expression);
        [DllImport(LIB_NAME)]
        static extern void free_expr(ExpressionFFIPointer ffi_struct);

        public class Expression : IExpression
        {
            private readonly ExpressionFFIPointer _expressionFFIPointer;

            public Expression(ExpressionFFIPointer expressionFFIPointer)
            {
                _expressionFFIPointer = expressionFFIPointer;
            }

            public string Execute()
            {
                throw new NotImplementedException();
            }

            public void Dispose()
            {
                free_expr(_expressionFFIPointer);
            }
        }

        public static IExpression GetExpression(string expression)
        {
            var exprPtr = ffi_parse_expr(expression);
            return new Expression(exprPtr);
        }
    }
}
