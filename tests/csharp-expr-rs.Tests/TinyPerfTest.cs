using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using DynamicExpresso;
using Xunit;
using Xunit.Abstractions;

namespace csharp_expr_rs.Tests
{
    public class TinyPerfTest
    {
        private readonly ITestOutputHelper _output;

        public TinyPerfTest(ITestOutputHelper output)
        {
            _output = output;
        }

        const int NB = 1_000_000;

        [Fact]
        public void DynamicExpresso()
        {
            var interpreter = new Interpreter(InterpreterOptions.DefaultCaseInsensitive);
            interpreter.SetFunction("first", (Func<object, int, int, object>)((a,b,c) => new[] { a, b, c }.First()));

            var exp = interpreter.Parse("first(first(first(1,2,3),2,3),2,3)");
            for (int i = 0; i < 10_000_000; i++)
            {
                var test = exp.Invoke();
            }

            //var exp = interpreter.Parse("first(1,2,3)");
            //var test = exp.Invoke();
            //_output.WriteLine(test?.ToString());
        }
    }
}
