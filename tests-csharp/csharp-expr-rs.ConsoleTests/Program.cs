using System;
using System.Collections.Generic;

namespace csharp_expr_rs.ConsoleTests
{
    class Program
    {
        static void Main(string[] args)
        {
            var shoulbe = Guid.NewGuid().ToString();
            //Console.WriteLine($"Should be : {shoulbe}.");
            var expression = new Expression("first(aa,1)");
            var result = expression.Execute(new Dictionary<string, string>() { { "aa", shoulbe } });
            expression.Dispose();
            Console.WriteLine($"RESULT : {result}");
        }
    }
}
