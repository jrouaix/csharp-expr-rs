using System;
using System.Collections.Generic;
using System.Runtime.InteropServices;
using System.Text;

namespace csharp_expr_rs.ConsoleTests
{
    public class NativePassStringTests
    {
        public void Test()
        {
            var str = "€";
            //NativePassString.PassLPStr(str); // exception when €
            //NativePassString.PassLPWStr(str);
            //NativePassString.PassLPTStr(str);
            NativePassString.PassLPUTF8Str(str);
            //NativePassString.PassBStr(str);
        }
    }

    /// <summary>
    /// https://docs.microsoft.com/fr-fr/dotnet/framework/interop/default-marshaling-for-strings
    /// </summary>
    internal static class NativePassString
    {
        public const string LIB_NAME = "csharp_expr.dll";

        [DllImport(LIB_NAME)]
        public static extern void PassLPStr([MarshalAs(UnmanagedType.LPStr)] string s);
        [DllImport(LIB_NAME)]
        public static extern void PassLPWStr([MarshalAs(UnmanagedType.LPWStr)] string s);
        [DllImport(LIB_NAME)]
        public static extern void PassLPTStr([MarshalAs(UnmanagedType.LPTStr)] string s);
        [DllImport(LIB_NAME)]
        public static extern void PassLPUTF8Str([MarshalAs(UnmanagedType.LPUTF8Str)] string s);
        [DllImport(LIB_NAME)]
        public static extern void PassBStr([MarshalAs(UnmanagedType.BStr)] string s);
    }
}
