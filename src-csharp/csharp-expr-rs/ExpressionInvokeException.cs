using System;
using System.Collections.Generic;
using System.Text;

namespace csharp_expr_rs
{
    [Serializable]
    public class ExpressionInvokeException : Exception
    {
        public ExpressionInvokeException(string message) : base(message) { }
        public ExpressionInvokeException(string message, Exception inner) : base(message, inner) { }
        protected ExpressionInvokeException(
          System.Runtime.Serialization.SerializationInfo info,
          System.Runtime.Serialization.StreamingContext context) : base(info, context) { }
    }
}
