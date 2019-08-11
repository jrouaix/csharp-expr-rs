using BenchmarkDotNet.Attributes;
using DynamicExpresso;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs.Benchmarks
{
    [MemoryDiagnoser]
    public class TinyExpressionBenchmark
    {
        private Lambda _dynamicExpression;
        private Expression _rustExpression;

        [GlobalSetup]
        public void GlobalSetup()
        {
            var expression = "first(first(first(first(first(first(first(first(first(first(first(1,2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3)";

            // DynamicExpresso
            var interpreter = new Interpreter(InterpreterOptions.DefaultCaseInsensitive);
            interpreter.SetFunction("first", (Func<object, int, int, object>)((a, b, c) => new[] { a, b, c }.First()));
            _dynamicExpression = interpreter.Parse(expression);

            //Rust
            _rustExpression = new Expression(expression);
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
