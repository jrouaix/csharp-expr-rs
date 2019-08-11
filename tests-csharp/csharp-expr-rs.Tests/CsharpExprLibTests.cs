using Shouldly;
using System;
using System.IO;
using Xunit;
using Xunit.Abstractions;

namespace csharp_expr_rs.Tests
{
    public class CsharpExprLibTests
    {
        private readonly ITestOutputHelper _output;

        public CsharpExprLibTests(ITestOutputHelper output)
        {
            _output = output;
        }

        [Fact]
        public void Test1()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                try
                {
                    var expression = new Expression("first(1,2,3)");
                    var result = expression.Execute();
                    _output.WriteLine(result);
                    expression.Dispose();
                }
                finally
                {
                    _output.WriteLine(sw.ToString());
                }
            }
        }
    }
}
