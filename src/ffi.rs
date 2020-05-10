use crate::expressions::*;

use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::rc::Rc;
use std::slice;
use std::{cell::RefCell, vec::Vec};
use unicase::UniCase;

fn str_from_c_char_ptr<'a>(s: *const c_char) -> &'a str {
    unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    }
    .to_str()
    .unwrap()
}

fn string_from_c_char_ptr(s: *const c_char) -> String {
    str_from_c_char_ptr(s).to_string()
}

static UTF16: Lazy<&'static encoding_rs::Encoding> = Lazy::new(|| {
    let encoding = encoding_rs::Encoding::for_label("UTF-16".as_bytes()).unwrap();
    encoding
});

fn string_from_csharp_string_ptr(s: FFICSharpString) -> String {
    unsafe {
        let slice = slice::from_raw_parts(s.ptr, s.len);
        let mut decoder = UTF16.new_decoder();
        let mut utf8 = String::with_capacity(s.len);
        let recode_result = decoder.decode_to_string(slice, &mut utf8, true);
        utf8
    }
}

#[no_mangle]
extern "C" fn ffi_parse_and_prepare_expr(expression: *const c_char) -> *mut ExprAndIdentifiers {
    let r_str = str_from_c_char_ptr(expression);
    let expr = parse_expr(r_str).unwrap();

    let funcs = crate::functions::get_functions();

    let expr = prepare_expr_and_identifiers(expr, &funcs);
    Box::into_raw(Box::new(expr))
}

#[no_mangle]
extern "C" fn ffi_get_identifiers(ptr: *mut ExprAndIdentifiers) -> *mut c_char {
    let expr = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    let identifiers_separated = expr.identifiers_names.iter().cloned().collect::<Vec<String>>().join("|");
    let c_str_result = CString::new(identifiers_separated).unwrap();
    c_str_result.into_raw()
}

#[repr(C)]
#[derive(Debug)]
pub struct IdentifierKeyValue {
    key: *const c_char,
    value: FFICSharpString,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct FFICSharpString {
    ptr: *const u8,
    len: usize,
}

// #[repr(C)]
// #[derive(Debug, Copy, Clone)]
// pub struct FFIExecResult {
//     is_error: bool,
//     content: *mut c_char,
// }

// https://michael-f-bryan.github.io/rust-ffi-guide/errors/return_types.html#return-types
// https://blog.datalust.co/rust-at-datalust-how-we-integrate-rust-with-csharp/

thread_local! {
    static LAST_ERROR: RefCell<bool> = RefCell::new(false);
}
/// Update the most recent error, clearing whatever may have been there before.
pub fn set_last_is_error(b: bool) {
    LAST_ERROR.with(|prev| {
        *prev.borrow_mut() = b;
    });
}
/// Retrieve the most recent error, clearing it in the process.
#[no_mangle]
extern "C" fn get_last_is_error() -> bool {
    LAST_ERROR.with(|v| *v.borrow())
}

#[no_mangle]
extern "C" fn ffi_exec_expr(ptr: *mut ExprAndIdentifiers, identifier_values: *const IdentifierKeyValue, identifier_values_len: usize) -> *mut c_char {
    let expr = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    let vals = unsafe {
        assert!(!identifier_values.is_null());
        slice::from_raw_parts(identifier_values, identifier_values_len)
    };

    let mut values = IdentifierValues::new();
    for ikv in vals.iter() {
        let k = string_from_c_char_ptr(ikv.key);
        let get_v = Box::new(move || string_from_csharp_string_ptr(ikv.value));
        values.insert(UniCase::new(k), get_v);
    }

    let result = exec_expr(&expr.expr, &values);

    match result {
        Err(e) => {
            let c_str_result = CString::new(e).unwrap();
            set_last_is_error(true);
            c_str_result.into_raw()
        }
        Ok(r) => {
            let s_result = r.to_string();
            let c_str_result = CString::new(s_result).unwrap();
            set_last_is_error(false);
            c_str_result.into_raw()
        }
    }
}

#[no_mangle]
extern "C" fn ffi_free_expr(ptr: *mut ExprAndIdentifiers) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Box::from_raw(ptr);
    }
}

#[no_mangle]
extern "C" fn ffi_free_cstring(ptr: *mut c_char) {
    if ptr.is_null() {
        return;
    }
    unsafe { CString::from_raw(ptr) };
}

#[no_mangle]
extern "C" fn ffi_test(param: FFICSharpString) -> *mut c_char {
    assert!(!param.ptr.is_null());

    let utf8 = string_from_csharp_string_ptr(param);
    println!("utf-16 to utf-8 decoded: {}", utf8);

    return CString::new("ok").unwrap().into_raw();
    // let c_str_result = CString::new(s).unwrap();
    // c_str_result.into_raw()
}
