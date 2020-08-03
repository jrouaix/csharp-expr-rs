using System;
using System.Collections.Generic;

namespace csharp_expr_rs.ConsoleTests
{
    class Program
    {
        //static void Main(string[] args)
        //{
        //    var shoulbe = Guid.NewGuid().ToString();
        //    Console.WriteLine($"Should be : {shoulbe}.");
        //    using var expression = new Expression("concat(aa,\"---------OK\")");
        //    var result = expression.Execute(new Dictionary<string, string>() { { "aa", shoulbe } });
        //    Console.WriteLine($"RESULT : {result}");
        //}

        static void Main(string[] args)
        {
            new NativePassStringTests().Test();
        }

    }
}
