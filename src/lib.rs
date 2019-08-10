// #![cfg(feature = "alloc")]

// extern crate nom;
// extern crate jemallocator;

// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

#![feature(result_map_or_else)]

//external crates
use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::rc::Rc;
// use libc::{c_char, uint32_t};
// use std::ffi::CStr;

use nom::{
    branch::alt,
    bytes::complete::{escaped, tag, take_while},
    character::complete::{alpha1, alphanumeric0, alphanumeric1, char, one_of},
    combinator::{cut, map, opt},
    error::{context, convert_error, ErrorKind, ParseError, VerboseError},
    multi::separated_list,
    number::complete::double,
    sequence::{delimited, pair, preceded, separated_pair, terminated, tuple},
    Err, IResult,
};
use std::collections::HashMap;
use std::str;

// got this list from rust : https://github.com/rust-lang/rust/blob/master/src/libsyntax/util/parser.rs
#[derive(PartialEq, Debug)]
pub enum AssocOp {
    /// `+`
    Add,
    /// `-`
    Subtract,
    /// `*`
    Multiply,
    /// `/`
    Divide,
    /// `%`
    Modulus,
    /// `&&`
    LAnd,
    /// `||`
    LOr,
    /// `==`
    Equal,
    /// `<`
    Less,
    /// `<=`
    LessEqual,
    /// `!=`
    NotEqual,
    /// `>`
    Greater,
    /// `>=`
    GreaterEqual,
}

#[repr(C)]
// #[derive(Debug, PartialEq)]
pub enum Expr {
    Str(String),
    Boolean(bool),
    Num(f64),
    Array(Vec<Expr>),
    Object(HashMap<String, Expr>),
    FunctionCall(String, Vec<Expr>),
    PreparedFunctionCall(String, Vec<Expr>, Rc<FunctionImpl>), // BinaryOperator(Box<Expr>, Box<Expr>, AssocOp)
}

type FunctionImpl = dyn Fn(&Vec<Expr>) -> Result<&Expr, String>;
type FunctionImplList = HashMap<String, Rc<FunctionImpl>>;

/// A nom parser has the following signature:
/// `Input -> IResult<Input, Output, Error>`, with `IResult` defined as:
/// `type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;`

/// spaces combinator
fn sp<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    let chars = " \t\r\n";
    take_while(move |c| chars.contains(c))(i)
}

/// string interior combinator
fn parse_str<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    escaped(alphanumeric1, '\\', one_of("\"n\\"))(i)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    alt((map(tag("false"), |_| false), map(tag("true"), |_| true)))(input)
}

/// full string combinator
fn string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "string",
        preceded(char('\"'), cut(terminated(parse_str, char('\"')))),
    )(i)
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<Expr>, E> {
    context(
        "array",
        preceded(
            char('['),
            cut(terminated(
                separated_list(preceded(sp, char(',')), value),
                preceded(sp, char(']')),
            )),
        ),
    )(i)
}

/// key : value combinator
fn key_value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (&'a str, Expr), E> {
    separated_pair(preceded(sp, string), cut(preceded(sp, char(':'))), value)(i)
}

/// hash { key : value, ... } combinator
fn hash<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, HashMap<String, Expr>, E> {
    context(
        "map",
        preceded(
            char('{'),
            cut(terminated(
                map(
                    separated_list(preceded(sp, char(',')), key_value),
                    |tuple_vec| {
                        tuple_vec
                            .into_iter()
                            .map(|(k, v)| (String::from(k), v))
                            .collect()
                    },
                ),
                preceded(sp, char('}')),
            )),
        ),
    )(i)
}

/// here, we apply the space parser before trying to parse a value
fn value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    preceded(
        sp,
        alt((
            map(double, Expr::Num),
            map(boolean, Expr::Boolean),
            map(string, |s| Expr::Str(String::from(s))),
            map(function_call, |(f_name, params)| {
                Expr::FunctionCall(String::from(f_name), params)
            }),
            map(hash, Expr::Object),
            map(array, Expr::Array),
        )),
    )(i)
}

fn identifier<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "identifier",
        preceded(opt(sp), preceded(opt(tag("_")), alphanumeric0)),
    )(i)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<Expr>, E> {
    context(
        "parameters",
        preceded(
            char('('),
            cut(terminated(
                separated_list(preceded(sp, char(',')), value),
                preceded(sp, char(')')),
            )),
        ),
    )(i)
}

fn function_call<'a, E: ParseError<&'a str>>(
    i: &'a str,
) -> IResult<&'a str, (&'a str, Vec<Expr>), E> {
    pair(identifier, parameters)(i)
}

fn expr<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(opt(sp), value, opt(sp))(i)
}

fn parse_expr<'a>(expression: &'a str) -> Result<Expr, String> {
    let expr = expr::<(&str, ErrorKind)>(expression);
    match expr {
        Ok(ok) => Ok(ok.1),
        Err(_err_kind) => Err(String::from("error")),
    }
}

fn prepare_expr(expr: Expr, funcs: &FunctionImplList) -> Expr {
    if let Expr::FunctionCall(name, parameters) = expr {
        println!("{}", name);
        match &funcs.get(&name) {
            Some(fnc) => {
              let parameters = parameters.into_iter().map(|p| prepare_expr(p, &funcs)).collect();
              Expr::PreparedFunctionCall(name, parameters, Rc::clone(&fnc))
            },
            None => Expr::FunctionCall(name, parameters),
        }
    } else {
        expr
    }
}

fn exec_expr<'a>(expr: &'a Expr) -> Result<&'a Expr, String> {
    match expr {
        Expr::Str(_) => Ok(expr),
        Expr::Boolean(_) => Ok(expr),
        Expr::Num(_) => Ok(expr),
        Expr::Array(_) => Ok(expr),
        Expr::Object(_) => Ok(expr),
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(name, _parameters) => {
            Err(format!("Unable to find the function named '{}'", name))
        }
        Expr::PreparedFunctionCall(name, parameters, fnc) => {
            let call_result = fnc(parameters)?;
            exec_expr(call_result)
        }
    }
}

fn parse_exec_expr<'a>(expression: &'a str, funcs: &FunctionImplList) -> String {
    let expr = parse_expr(expression).unwrap();
    let expr = prepare_expr(expr, &funcs);
    let result = exec_expr(&expr).unwrap();
    expr_to_string(result)
}

fn expr_to_string<'a>(expr: &'a Expr) -> String {
    match expr {
        Expr::Str(s) => s.to_string(),
        Expr::Boolean(b) => b.to_string(),
        Expr::Num(n) => n.to_string(),
        Expr::Array(_) => "Array".to_string(),
        Expr::Object(_) => "Object".to_string(),
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(_, _) => "FunctionCall".to_string(),
        Expr::PreparedFunctionCall(_, _, _) => "PreparedFunctionCall".to_string(),
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;

    #[test]
    fn execute_one_expression() {
        let mut funcs: FunctionImplList = HashMap::new();

        funcs.insert(
            "true".to_string(),
            Rc::new(|_: &Vec<Expr>| Ok(&Expr::Boolean(true))),
        );

        funcs.insert(
            "first".to_string(),
            Rc::new(|v: &Vec<Expr>| v.first().ok_or("There was no first value.".to_string())),
        );

        let expression = "first(first(first(1,2,3),2,3),2,3)";
        let result = parse_exec_expr(expression, &funcs);
        assert_eq!(result, "1");
        println!("{:?}", result);
    }
}

// https://dev.to/living_syn/calling-rust-from-c-6hk
// http://jakegoulding.com/rust-ffi-omnibus/
// https://dev.to/luzero/building-crates-so-they-look-like-c-abi-libraries-1ibn

#[no_mangle]
pub extern "C" fn ffi_parse_expr(expression: *const c_char) -> *mut Expr {
    let c_str = unsafe {
        assert!(!expression.is_null());
        CStr::from_ptr(expression)
    };

    let r_str = c_str.to_str().unwrap();
    let expr = parse_expr(r_str).unwrap();

    let mut funcs: FunctionImplList = HashMap::new();

    funcs.insert(
        "true".to_string(),
        Rc::new(|_: &Vec<Expr>| Ok(&Expr::Boolean(true))),
    );

    funcs.insert(
        "first".to_string(),
        Rc::new(|v: &Vec<Expr>| v.first().ok_or("There was no first value.".to_string())),
    );

    let expr = prepare_expr(expr, &funcs);

    let b = Box::new(expr);
    Box::into_raw(b)
}

#[no_mangle]
pub extern "C" fn ffi_exec_expr(ptr: *mut Expr) -> *mut c_char {
    let expr = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    // println!("Haaaaaaaaaaaa");
    // println!("{:?}", expr);
    let result = exec_expr(&expr).unwrap();
    let s_result = expr_to_string(result);

    // CString::new("test").unwrap().into_raw()
    // Box::into_raw(expr); // so the memory is not freed and the box is still living

    let c_str_result = CString::new(s_result).unwrap();
    c_str_result.into_raw()
}

#[no_mangle]
pub extern "C" fn ffi_free_expr(ptr: *mut Expr) {
    if ptr.is_null() {
        return;
    }
    unsafe {
        Box::from_raw(ptr);
    }
}

#[no_mangle]
pub extern "C" fn ffi_free_cstring(ptr: *mut c_char) {
    if ptr.is_null() {
        return;
    }
    unsafe { CString::from_raw(ptr) };
}

// #[no_mangle]
// pub extern fn add_numbers(number1: i32, number2: i32) -> i32 {
//     number1 + number2
// }
