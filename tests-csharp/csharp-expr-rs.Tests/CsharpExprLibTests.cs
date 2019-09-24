using Shouldly;
using System;
using System.Collections.Generic;
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
        public void Exec_function()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                var expression = new Expression("first(1,2,3)");
                try
                {
                    var result = expression.Execute(new Dictionary<string, string>());
                    _output.WriteLine(result);
                    result.ShouldBe("1");
                }
                finally
                {
                    expression.Dispose();
                    _output.WriteLine(sw.ToString());
                }
            }
        }

        [Fact]
        public void Get_identifier_value()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                var expression = new Expression("test");

                try
                {
                    var result = expression.Execute(new Dictionary<string, string>() { { "test", "42" } });
                    _output.WriteLine(result);
                    result.ShouldBe("42");


                    result = expression.Execute(new Dictionary<string, string>() { { "test", "43" } });
                    result.ShouldBe("43");
                }
                finally
                {
                    expression.Dispose();
                    _output.WriteLine(sw.ToString());
                }
            }
        }


        [Fact(Skip = "A memory leak can be observed when debugging this unit test. Same code, looping for an insane amount of time, produce no memory increase in a console app.")]
        //[Fact]
        public void Fast_try_thousands()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);
                var identifierValues = new Dictionary<string, string>() { { "test", "42" } };

                for (int i = 0; i < 100000; i++)
                {
                    var expression = new Expression("test");
                    try
                    {
                        expression.Execute(identifierValues);
                    }
                    finally
                    {
                        expression.Dispose();
                        _output.WriteLine(sw.ToString());
                    }
                }
            }
        }
    }
}
