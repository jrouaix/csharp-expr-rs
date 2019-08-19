using System;
using System.Collections.Generic;

namespace csharp_expr_rs.ConsoleTests
{
    class Program
    {
        static void Main(string[] args)
        {
            var expression = new Expression("test(1,2,3)");
            var result = expression.Execute(new Dictionary<string, string>());
            expression.Dispose();
        }
    }
}
