using BeezUP2.Framework.Expressions;
using BenchmarkDotNet.Attributes;
using BenchmarkDotNet.Engines;
using DynamicExpresso;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

namespace csharp_expr_rs.Benchmarks
{
    [SimpleJob(RunStrategy.Throughput, targetCount: 50)]
    [MemoryDiagnoser]
    //[NativeMemoryDiagnoser] // Use it when available : https://github.com/dotnet/BenchmarkDotNet/pull/1131 / https://github.com/dotnet/BenchmarkDotNet/releases -> 0.11.6
    public class TinyExpressionBenchmark
    {
        private Lambda _dynamicExpression;
        private Expression _rustExpression;
        private CSharpExpressionDynamicExpresso _bzExpression;
        private Dictionary<string, string> _rustParameters;

        [Params(10, 25, 50, 200)] public int IdentifiersCount { get; set; }
        [Params(10, 100, 1000)] public int IdentifiersValueSize { get; set; }
        //[Params(10, 50, 100)] public int ExpressionSize { get; set; }

        [IterationSetup]
        public void GlobalSetup()
        {
            var randy = new Random();
            var chars = "abcdefghijklmnopqrsrtwxyz";

            _rustParameters = Enumerable.Range(0, IdentifiersCount)
                .ToDictionary(i => $"a{i}", i => new String(chars[randy.Next(chars.Length)], IdentifiersValueSize));

            var expression = "first(first(first(first(first(first(first(first(first(first(first(1,2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3)";

            var firstFunction = (Func<object, int, int, object>)((a, b, c) => new[] { a, b, c }.First());

            // DynamicExpresso
            var interpreter = new Interpreter(InterpreterOptions.DefaultCaseInsensitive);
            interpreter.SetFunction("first", firstFunction);
            _dynamicExpression = interpreter.Parse(expression);

            //bz
            var expression2 = "first(first(first(first(first(first(first(first(first(first(first([a0],2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3),2,3)";
            _bzExpression = new CSharpExpressionDynamicExpresso(expression2, null, new Dictionary<string, Delegate> { { "first", firstFunction } });

            //Rust
            _rustExpression = new Expression(expression);
        }

        [IterationCleanup]
        public void GlobalCleanup()
        {
            _rustExpression.Dispose();
        }

        [Benchmark]
        public object DynamicExpresso() => _dynamicExpression.Invoke(_rustParameters.Select(kv => new Parameter(kv.Key, kv.Value)).ToArray());

        [Benchmark(Baseline = true)]
        public object BzExpression() => _bzExpression.Invoke(_rustParameters);

        [Benchmark]
        public object Rust() => _rustExpression.Execute(_rustParameters);


        private Dictionary<string, string> _noParams = new Dictionary<string, string>();
        [Benchmark]
        public object RustNoParams() => _rustExpression.Execute(_noParams);
    }
}
