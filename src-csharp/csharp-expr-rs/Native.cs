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

        // https://docs.microsoft.com/fr-fr/dotnet/framework/interop/default-marshaling-for-strings

        [DllImport(LIB_NAME)]
        public static extern FFIParseResult ffi_parse_and_prepare_expr([MarshalAs(UnmanagedType.LPUTF8Str)] string expression);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_expr(IntPtr ptr);

        [DllImport(LIB_NAME)]
        public static extern FFIStringHandle ffi_get_identifiers(FFIExpressionHandle ptr);
        [DllImport(LIB_NAME)]
        [return: MarshalAs(UnmanagedType.I1)]
        public static extern bool ffi_is_deterministic(FFIExpressionHandle ptr);

        [DllImport(LIB_NAME, CharSet = CharSet.Ansi)]
        public static extern FFIExecResult ffi_exec_expr(FFIExpressionHandle ptr, FFIIdentifierKeyValue[] identifier_values, UIntPtr identifier_values_len);
        [DllImport(LIB_NAME)]
        public static extern void ffi_free_cstring(IntPtr ptr);
    }

    [StructLayout(LayoutKind.Sequential)]
    internal struct FFIIdentifierKeyValue
    {
        [MarshalAs(UnmanagedType.LPUTF8Str)]
        public string key;
        [MarshalAs(UnmanagedType.LPUTF8Str)]
        public string value;
    }

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe struct FFICSharpString
    {
        public byte* ptr;
        public UIntPtr len;
    }

    internal unsafe class FFICSharpStringHolder
    {
        public byte[] shortStr;
        public string dotnetStr;
        public FFICSharpString ffiStr;
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

    [StructLayout(LayoutKind.Sequential)]
    internal unsafe struct FFIParseResult
    {
        [MarshalAs(UnmanagedType.I1)]
        public bool is_error;
        public IntPtr error;
        public IntPtr content;

        public FFIExpressionHandle GetContent()
        {
            if (is_error)
                throw new InvalidOperationException("Cannot get the content, it's an error");
            return new FFIExpressionHandle(content);
        }

        public FFIStringHandle GetError()
        {
            if (!is_error)
                throw new InvalidOperationException("Cannot get the content as string, it's not an error");
            return new FFIStringHandle(error);
        }
    }

    internal class FFIExpressionHandle : SafeHandle
    {
        public FFIExpressionHandle() : base(IntPtr.Zero, true) { }
        public FFIExpressionHandle(IntPtr intPtr) : base(intPtr, true) { }

        public override bool IsInvalid => false;

        public IntPtr RawPtr => handle;

        protected override bool ReleaseHandle()
        {
            Native.ffi_free_expr(handle);
            return true;
        }
    }
}
