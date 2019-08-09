using System;
using System.Runtime.InteropServices;
using System.Text;

namespace csharp_expr_rs
{
    internal static class CsharpExprLib
    {
        public const string LIB_NAME = "csharp_expr.dll";

        [DllImport(LIB_NAME)]
        public static extern ExpressionFFIPointer ffi_parse_expr(string expression);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_expr(ExpressionFFIPointer ffi_struct);
        [DllImport(LIB_NAME)]
        public static extern FFIStringHandle ffi_exec_expr(ExpressionFFIPointer ffi_struct);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_cstring(IntPtr s);


        [StructLayout(LayoutKind.Sequential)]
        public struct ExpressionFFIPointer
        {
            public IntPtr expression;
        }
   
    }


    internal class FFIStringHandle : SafeHandle
    {
        public FFIStringHandle() : base(IntPtr.Zero, true) { }

        public override bool IsInvalid => false;

        public string AsString()
        {
            int len = 0;
            while (Marshal.ReadByte(handle, len) != 0) { ++len; }
            byte[] buffer = new byte[len];
            Marshal.Copy(handle, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
        }

        protected override bool ReleaseHandle()
        {
            CsharpExprLib.ffi_free_cstring(handle);
            return true;
        }
    }
}
