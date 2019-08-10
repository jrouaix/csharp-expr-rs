using System;

namespace csharp_expr_rs.ConsoleTests
{
    class Program
    {
        static void Main(string[] args)
        {
            var expression = new Expression("test(1,2,3)");
            var result = expression.Execute();
            expression.Dispose();
        }
    }
}
