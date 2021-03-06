use crate::expressions::*;

use once_cell::sync::Lazy;
use std::cell::RefCell;
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::ptr;
use std::rc::Rc;
use std::slice;
use std::vec::Vec;
use unicase::UniCase;

fn str_from_c_char_ptr<'a>(s: *const c_char) -> Result<&'a str, std::str::Utf8Error> {
    unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    }
    .to_str()
}

fn string_from_c_char_ptr(s: *const c_char) -> Result<String, std::str::Utf8Error> {
    Ok(str_from_c_char_ptr(s)?.to_string())
}

static UTF16: Lazy<&'static encoding_rs::Encoding> = Lazy::new(|| {
    let encoding = encoding_rs::Encoding::for_label("UTF-16".as_bytes()).unwrap();
    encoding
});

fn string_from_csharp(s: *const c_char) -> String {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };
    let r_str = c_str.to_str().unwrap();
    r_str.into()
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct FFIParseResult {
    is_error: bool,
    error: *mut c_char,
    content: *mut ExprAndIdentifiers,
}

#[no_mangle]
extern "C" fn ffi_parse_and_prepare_expr(expression: *const c_char) -> FFIParseResult {
    let r_str = string_from_csharp(expression);
    let result = parse_expr(&r_str);
    match result {
        Err(err) => FFIParseResult {
            is_error: true,
            error: CString::new(err).unwrap().into_raw(),
            content: ptr::null_mut(),
        },
        Ok(expr) => {
            let funcs = crate::functions::get_functions();
            let expr = prepare_expr_and_identifiers(expr, &funcs, Rc::new(crate::functions::f_operators));
            FFIParseResult {
                is_error: false,
                error: ptr::null_mut(),
                content: Box::into_raw(Box::new(expr)),
            }
        }
    }
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

#[no_mangle]
extern "C" fn ffi_is_deterministic(ptr: *mut ExprAndIdentifiers) -> bool {
    let expr = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    match expr.determinism {
        FunctionDeterminism::Deterministic => true,
        FunctionDeterminism::NonDeterministic => false,
    }
}

#[repr(C)]
#[derive(Debug)]
pub struct IdentifierKeyValue {
    key: *const c_char,
    value: *const c_char,
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct FFIExecResult {
    is_error: bool,
    content: *mut c_char,
}

struct IdentifierStringValueLazyGetter {
    value_ptr: *const c_char,
    value: Option<Rc<String>>,
}

impl IdentifierStringValueLazyGetter {
    fn new(value_ptr: *const c_char) -> IdentifierStringValueLazyGetter {
        IdentifierStringValueLazyGetter { value_ptr, value: None }
    }

    fn get_value(&mut self) -> Rc<String> {
        match &self.value {
            Some(rc) => rc.clone(),
            None => {
                let s = string_from_csharp(self.value_ptr);
                let rc = Rc::new(s);
                self.value = Some(rc.clone());
                rc
            }
        }
    }
}

#[no_mangle]
extern "C" fn ffi_exec_expr(ptr: *mut ExprAndIdentifiers, identifier_values: *const IdentifierKeyValue, identifier_values_len: usize) -> FFIExecResult {
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
        let k = string_from_c_char_ptr(ikv.key).unwrap();
        let lazy_getter = IdentifierStringValueLazyGetter::new(ikv.value);
        let lazy_refcell = RefCell::new(lazy_getter);
        let get_v = Box::new(move || lazy_refcell.borrow_mut().get_value());
        values.insert(k, get_v);
    }

    let result = exec_expr(&expr.expr, &mut values);

    match result {
        Ok(r) => FFIExecResult {
            is_error: false,
            content: CString::new(r.to_string()).unwrap().into_raw(),
        },
        Err(e) => FFIExecResult {
            is_error: true,
            content: CString::new(e).unwrap().into_raw(),
        },
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

// =========================================
// =========================================
//                  TESTING
// =========================================
// =========================================

#[no_mangle]
extern "C" fn PassLPStr(s: *const c_char) {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };

    let r_str = c_str.to_str().unwrap();
    dbg!("PassLPStr", r_str);
}
#[no_mangle]
extern "C" fn PassLPWStr(s: *const c_char) {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };

    let r_str = c_str.to_str().unwrap();
    dbg!("PassLPWStr", r_str);
}
#[no_mangle]
extern "C" fn PassLPTStr(s: *const c_char) {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };

    let r_str = c_str.to_str().unwrap();
    dbg!("PassLPTStr", r_str);
}
#[no_mangle]
extern "C" fn PassLPUTF8Str(s: *const c_char) {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };

    let r_str = c_str.to_str().unwrap();
    dbg!("PassLPUTF8Str", r_str);
}
#[no_mangle]
extern "C" fn PassBStr(s: *const c_char) {
    let c_str = unsafe {
        assert!(!s.is_null());
        CStr::from_ptr(s)
    };

    let r_str = c_str.to_str().unwrap();
    dbg!("PassBStr", r_str);
}
