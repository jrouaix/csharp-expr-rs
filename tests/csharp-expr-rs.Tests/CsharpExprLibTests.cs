using Shouldly;
using System;
using Xunit;

namespace csharp_expr_rs.Tests
{
    public class CsharpExprLibTests
    {
        [Fact]
        public void Test1()
        {
            var expression = new Expression("test(1,2,3)");
            var result = expression.Execute();
            expression.Dispose();
        }
    }
}
