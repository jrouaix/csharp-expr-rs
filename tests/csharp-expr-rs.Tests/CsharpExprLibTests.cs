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
            var result = CsharpExprLib.GetExpression();
            result.Dispose();
        }
    }
}
