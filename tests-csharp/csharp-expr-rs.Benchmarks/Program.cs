using BenchmarkDotNet.Running;

namespace csharp_expr_rs.Benchmarks
{
    public class Program
    {
        public static void Main(string[] args)
        {
            BenchmarkRunner.Run<TinyExpressionBenchmark>();
            //BenchmarkRunner.Run<CompilationBenchmark>();
        }
    }
}
