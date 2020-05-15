using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Text;

[assembly: InternalsVisibleTo("csharp-expr-rs.Tests")]

namespace csharp_expr_rs
{
    internal static class Native
    {
        public const string LIB_NAME = "csharp_expr.dll";

        [DllImport(LIB_NAME, CharSet = CharSet.Ansi)]
        public static extern FFIExpressionHandle ffi_parse_and_prepare_expr(FFICSharpString expression);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_expr(IntPtr ptr);

        [DllImport(LIB_NAME)]
        public static extern FFIStringHandle ffi_get_identifiers(FFIExpressionHandle ptr);
        [DllImport(LIB_NAME, CharSet = CharSet.Ansi)]
        public static extern FFIExecResult ffi_exec_expr(FFIExpressionHandle ptr, FFIIdentifierKeyValue[] identifier_values, UIntPtr identifier_values_len);
        [DllImport(LIB_NAME)]
        public static extern bool get_last_is_error();
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_cstring(IntPtr ptr);

        [DllImport(LIB_NAME)]
        public static unsafe extern FFIStringHandle ffi_test(FFICSharpString sharpString);
    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct FFIIdentifierKeyValue
    {
        public string key;
        public FFICSharpString value;
    }

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe struct FFICSharpString
    {
        public char* ptr;
        public UIntPtr len;
    }

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe struct FFIExecResult
    {
        [MarshalAs(UnmanagedType.I1)]
        public bool is_error;
        public IntPtr content;

        public FFIStringHandle GetContent() => new FFIStringHandle(content);
    }


    internal class FFIStringHandle : SafeHandle
    {
        public FFIStringHandle() : base(IntPtr.Zero, true) { }
        public FFIStringHandle(IntPtr intPtr) : base(intPtr, true) { }

        public override bool IsInvalid => false;

        public string AsString()
        {
            int len = 0;
            while (Marshal.ReadByte(handle, len) != 0)
            { ++len; }
            byte[] buffer = new byte[len];
            Marshal.Copy(handle, buffer, 0, buffer.Length);
            return Encoding.UTF8.GetString(buffer);
        }

        public string AsStringAndDispose()
        {
            try
            {
                return AsString();
            }
            finally
            {
                Dispose();
            }
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
