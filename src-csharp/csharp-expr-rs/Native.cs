using System;
using System.Runtime.InteropServices;
using System.Text;

namespace csharp_expr_rs
{
    internal static class Native
    {
        public const string LIB_NAME = "csharp_expr.dll";

        [DllImport(LIB_NAME)]
        public static extern FFIExpressionHandle ffi_parse_expr(string expression);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_expr(IntPtr ptr);
        [DllImport(LIB_NAME)]
        public static extern FFIStringHandle ffi_exec_expr(FFIExpressionHandle ptr, FFIIdentifierKeyValue[] identifier_values, UIntPtr identifier_values_len);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_cstring(IntPtr ptr);
    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct FFIIdentifierKeyValue
    {
        public string key;
        public string value;
    };

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
            Native.ffi_free_cstring(handle);
            return true;
        }
    }

    internal class FFIExpressionHandle : SafeHandle
    {
        public FFIExpressionHandle() : base(IntPtr.Zero, true) { }

        public override bool IsInvalid => false;

        protected override bool ReleaseHandle()
        {
            Native.ffi_free_expr(handle);
            return true;
        }
    }
}
