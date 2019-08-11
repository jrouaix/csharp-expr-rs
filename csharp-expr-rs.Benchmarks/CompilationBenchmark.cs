using BenchmarkDotNet.Attributes;
using DynamicExpresso;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs.Benchmarks
{
    [MemoryDiagnoser]
    public class CompilationBenchmark
    {
        const string expression = "first(first(first(first(first(first(first(first(first(first(first(1,2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3)";

        [Benchmark(Baseline = true)]
        public void DynamicExpresso()
        {
            // DynamicExpresso
            var interpreter = new Interpreter(InterpreterOptions.DefaultCaseInsensitive);
            interpreter.SetFunction("first", (Func<object, int, int, object>)((a, b, c) => new[] { a, b, c }.First()));
            var dynamicExpression = interpreter.Parse(expression);
        }

        [Benchmark]
        public void Rust()
        {
            Expression rustExpression = null;
            try
            {
                rustExpression = new Expression(expression);
            }
            finally
            {
                rustExpression?.Dispose();
            }

        }
    }
}
