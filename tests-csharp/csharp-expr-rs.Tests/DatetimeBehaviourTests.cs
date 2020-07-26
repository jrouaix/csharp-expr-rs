using Shouldly;
using System;
using System.Collections.Generic;
using System.Text;
using TimeZoneConverter;
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


        [Fact]
        public void PrintWindowsTimezonesToIanaTz()
        {
            var sb = new StringBuilder();
            foreach (var z in TimeZoneInfo.GetSystemTimeZones())
            {
                var iana = TZConvert.WindowsToIana(z.Id);
                var chonotz = iana
                    .Replace("Port-au-Prince", "PortauPrince")
                    .Replace("/", "::").Replace("+", "Plus").Replace("-", "Minus");

                string line = $"m.insert(\"{z.Id}\", chrono_tz::{chonotz});";
                sb.AppendLine(line);
                _output.WriteLine(line);
            }
        }

        [Fact]
        public void PrintWindowsTimezonesToOffsets()
        {
            var sb = new StringBuilder();
            foreach (var z in TimeZoneInfo.GetSystemTimeZones())
            {
                var offset = z.BaseUtcOffset;
                var direction = (offset >= TimeSpan.Zero) ? "east" : "west";
                var seconds = (int)Math.Abs(offset.TotalSeconds);

                string line = $"m.insert(\"{z.Id}\", FixedOffset::{direction}({seconds}));";
                sb.AppendLine(line);
                _output.WriteLine(line);
            }
        }
    }
}
