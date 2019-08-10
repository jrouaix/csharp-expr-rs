using BenchmarkDotNet.Attributes;
using DynamicExpresso;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs.Benchmarks
{
    public class TinyExpressionBenchmark : IDisposable
    {
        private Lambda _dynamicExpression;
        private Expression _rustExpression;

        [GlobalSetup]
        public void GlobalSetup()
        {
            // DynamicExpresso
            var interpreter = new Interpreter(InterpreterOptions.DefaultCaseInsensitive);
            interpreter.SetFunction("first", (Func<object, int, int, object>)((a, b, c) => new[] { a, b, c }.First()));

            _dynamicExpression = interpreter.Parse("first(1,2,3)");

            //Rust
            _rustExpression = new Expression("first(1,2,3)");
        }

        [GlobalCleanup]
        public void GlobalCleanup()
        {
            _rustExpression.Dispose();
        }

        [Benchmark(Baseline = true)]
        public object DynamicExpresso() => _dynamicExpression.Invoke();

        [Benchmark]
        public object Rust() => _rustExpression.Execute();
    }
}
