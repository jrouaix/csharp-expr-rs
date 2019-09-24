using System;
using System.Collections.Generic;
using System.Linq;
using System.Security.Cryptography;
using BeezUP2.Framework.Expressions;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Configs;
using BenchmarkDotNet.Running;

namespace csharp_expr_rs.Benchmarks
{
    public class Program
    {
        public static void Main(string[] args)
        {
            //var randy = new Random();
            //var chars = "abcdefghijklmnopqrsrtwxyz";

            //var rustParameters = Enumerable.Range(0, 10)
            //    .ToDictionary(i => $"a{i}", i => new String(chars[randy.Next(chars.Length)], 100));

            //var firstFunction = (Func<object, int, int, object>)((a, b, c) => new[] { a, b, c }.First());
            //var expression = "first(first(first(first(first(first(first(first(first(first(first([a0],2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3)";
            //var bzExpression = new CSharpExpressionDynamicExpresso(expression, null, new Dictionary<string, Delegate> { { "first", firstFunction } });
            //var res = bzExpression.Invoke(rustParameters);

            //var identifierValues = new Dictionary<string, string>() { { "test", "42" } };
            //for (int i = 0; i < 1000000000; i++)
            //{
            //    var expression = new Expression("test");
            //    try
            //    {
            //        var result = expression.Execute(identifierValues);
            //        Console.WriteLine(result);
            //    }
            //    finally
            //    {
            //        expression.Dispose();
            //    }
            //}

            BenchmarkRunner.Run<TinyExpressionBenchmark>();
            //BenchmarkRunner.Run<CompilationBenchmark>();
        }
    }
}
