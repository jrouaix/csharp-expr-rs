using System;
using System.Collections.Generic;
using System.Text;

namespace csharp_expr_rs
{
    [Serializable]
    public class ExpressionParsingException : Exception
    {
        public ExpressionParsingException(string message) : base(message) { }
        public ExpressionParsingException(string message, Exception inner) : base(message, inner) { }
        protected ExpressionParsingException(
          System.Runtime.Serialization.SerializationInfo info,
          System.Runtime.Serialization.StreamingContext context) : base(info, context) { }
    }
}
