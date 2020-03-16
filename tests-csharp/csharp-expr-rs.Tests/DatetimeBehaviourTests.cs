using Shouldly;
using System;
using System.Collections.Generic;
using System.Text;
using Xunit;
using Xunit.Abstractions;

namespace csharp_expr_rs.Tests
{
    public class DatetimeBehaviourTests
    {
        private readonly ITestOutputHelper _output;

        public DatetimeBehaviourTests(ITestOutputHelper output)
        {
            _output = output;
        }

        [Fact]
        public void Tests()
        {
            new DateTime(2020, 1, 1).AddYears(1).ShouldBe(new DateTime(2021, 1, 1)); // Leap year yet it's on time
            //new DateTime(2020, 1, 1).AddYears(0.5).ShouldBe(new DateTime(2021, 1, 1);
        }
    }
}
