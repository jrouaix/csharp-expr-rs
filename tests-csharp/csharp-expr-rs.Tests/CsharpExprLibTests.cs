using Shouldly;
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
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

        [Theory]
        [InlineData("\"euro€\"", "euro€")]
        [InlineData("\"€euro\"", "€euro")]
        [InlineData("\"€\"", "€")]
        public void Exec(string expression, string expectedResult)
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);
                try
                {
                    using (var expr = new Expression(expression))
                    {
                        var result = expr.Execute(new Dictionary<string, string>());
                        _output.WriteLine(result.content);
                        result.content.ShouldBe(expectedResult);
                    }
                }
                finally
                {
                    _output.WriteLine(sw.ToString());
                }
            }
        }


        [Fact]
        public void Exec_function()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                var expression = new Expression("Concat(1,2,3)");
                try
                {
                    var result = expression.Execute(new Dictionary<string, string>());
                    _output.WriteLine(result.content);
                    result.content.ShouldBe("123");
                }
                finally
                {
                    expression.Dispose();
                    _output.WriteLine(sw.ToString());
                }
            }
        }

        [Theory]
        [InlineData("22", true)]
        [InlineData("Today()", false)]
        [InlineData("LocalDate(\"2019-08-06\")", true)]
        [InlineData("DateFormat(LocalDate(\"2020-03-04\"), \"yyyy-MM-dd HH\")", true)]
        public void Determinism(string expr, bool determinist)
        {
            var expression = new Expression(expr);
            expression.IsDeterministic.ShouldBe(determinist);
        }

        [Fact]
        public void HandleParseError()
        {
            Should.NotThrow(() => new Expression("func()"));
            Should.Throw<ExpressionParsingException>(() => new Expression("func() .. / \" wtf"));
        }

        [Fact]
        public void Get_identifier_value()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                using (var expression = new Expression("test"))
                {
                    (bool is_error, string content) result;
                    try
                    {
                        result = expression.Execute(new Dictionary<string, string>() { { "test", "42" } });
                        result.content.ShouldBe("42");

                        result = expression.Execute(new Dictionary<string, string>() { { "test", "43" } });
                        result.content.ShouldBe("43");

                        result = expression.Execute(new Dictionary<string, string>() { { "test", null } });
                        result.content.ShouldBe("");

                        result = expression.Execute(new Dictionary<string, string>() { { "test", "" } });
                        result.content.ShouldBe("");

                        result = expression.Execute(new Dictionary<string, string>() { { "test", "1" } });
                        result.content.ShouldBe("1");

                        result = expression.Execute(new Dictionary<string, string>() { { "test", "euro€" } });
                        result.content.ShouldBe("euro€");
                    }
                    finally
                    {
                        _output.WriteLine(sw.ToString());
                    }
                }
            }
        }

        //[Fact(Skip = "A memory leak can be observed when debugging this unit test. Same code, looping for an insane amount of time, produce no memory increase in a console app.")]
        [Fact]
        public void Fast_try_thousands()
        {
            using (var sw = new StringWriter())
            {
                Console.SetOut(sw);

                var s = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";
                var identifierValues = new Dictionary<string, string>() { { "test", s } };
                for (int i = 0; i < 1000; i++)
                {
                    var expression = new Expression("test");
                    try
                    {
                        var result = expression.Execute(identifierValues);
                        result.content.ShouldBe(s);
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
