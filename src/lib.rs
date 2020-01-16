// #![cfg(feature = "alloc")]

// extern crate nom;
// extern crate jemallocator;

// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

// #![feature(result_map_or_else)]
#![deny(bare_trait_objects)]

//external crates
// use once_cell::unsync::Lazy;
use std::cmp;
use std::collections::HashSet;
use std::ffi::{CStr, CString};
use std::fmt;
use std::os::raw::c_char;
use std::rc::Rc;
use std::slice;
use std::vec::Vec;

// use libc::{c_char, uint32_t};
// use std::ffi::CStr;

use unescape::unescape;

use nom::{
    branch::alt,
    bytes::complete::{escaped, tag, take_while}, // escaped_transform
    character::complete::{alphanumeric0, alphanumeric1, char, one_of},
    combinator::{cut, map, map_opt, not, opt, recognize},
    error::{context, ErrorKind, ParseError},
    multi::separated_list,
    number::complete::double,
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult,
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

type RcExpr = Rc<Expr>;
type VecRcExpr = Vec<RcExpr>;
type SliceRcExpr = [RcExpr];
type FunctionImpl = dyn Fn(&VecRcExpr) -> Result<RcExpr, String>;
type FunctionImplList = HashMap<String, Rc<FunctionImpl>>;
type IdentifierValueGetter = dyn Fn() -> String;
type IdentifierValues<'a> = HashMap<String, Box<IdentifierValueGetter>>;

#[repr(C)]
#[derive(Clone)]
pub enum Expr {
    Str(String),
    Boolean(bool),
    Num(f64),
    Array(VecRcExpr),
    Identifier(String),
    FunctionCall(String, VecRcExpr),
    PreparedFunctionCall(String, VecRcExpr, Rc<FunctionImpl>),
    // BinaryOperator(RcExpr, RcExpr, AssocOp)
}

#[repr(C)]
#[derive(Debug)]
pub struct ExprAndIdentifiers {
    expr: RcExpr,
    identifiers_names: HashSet<String>,
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Str(x) => write!(f, "Str({:?})", x),
            Expr::Boolean(x) => write!(f, "Boolean({:?})", x),
            Expr::Num(x) => write!(f, "Num({:?})", x),
            Expr::Array(x) => write!(f, "Array({:?})", x),
            Expr::Identifier(x) => write!(f, "Identifier({:?})", x),
            Expr::FunctionCall(s, x) => write!(f, "FunctionCall({:?},{:?})", s, x),
            Expr::PreparedFunctionCall(s, x, _) => {
                write!(f, "PreparedFunctionCall({:?},{:?})", s, x)
            }
        }
    }
}

impl cmp::PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Expr::Str(x_a), Expr::Str(x_b)) => x_a == x_b,
            (Expr::Boolean(x_a), Expr::Boolean(x_b)) => x_a == x_b,
            (Expr::Num(x_a), Expr::Num(x_b)) => x_a == x_b,
            (Expr::Array(x_a), Expr::Array(x_b)) => x_a == x_b,
            (Expr::Identifier(x_a), Expr::Identifier(x_b)) => x_a == x_b,
            (Expr::FunctionCall(n_a, p_a), Expr::FunctionCall(n_b, p_b)) => {
                n_a == n_b && p_a == p_b
            }
            (Expr::PreparedFunctionCall(n_a, p_a, _), Expr::PreparedFunctionCall(n_b, p_b, _)) => {
                n_a == n_b && p_a == p_b
            }
            _ => false,
        }
    }
}

/// A nom parser has the following signature:
/// `Input -> IResult<Input, Output, Error>`, with `IResult` defined as:
/// `type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;`

/// spaces combinator
fn sp<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    let chars = " \t\r\n";
    take_while(move |c| chars.contains(c))(input)
}

/// string interior combinator
fn parse_str<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    escaped(alphanumeric1, '\\', one_of("\\\"rnt"))(input)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    alt((map(tag("false"), |_| false), map(tag("true"), |_| true)))(input)
}

/// full string combinator
fn string<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "string",
        preceded(char('\"'), cut(terminated(parse_str, char('\"')))),
    )(input)
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "array",
        preceded(
            char('['),
            cut(terminated(
                map(separated_list(preceded(sp, char(',')), value), |v| {
                    v.into_iter().map(Rc::new).collect()
                }),
                preceded(sp, char(']')),
            )),
        ),
    )(input)
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "identifier",
        preceded(
            opt(sp),
            preceded(
                opt(tag("@")),
                recognize(tuple((opt(tag("_")), alphanumeric0))),
            ),
        ),
    )(input)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "parameters",
        preceded(
            char('('),
            terminated(
                map(separated_list(preceded(sp, char(',')), value), |v| {
                    v.into_iter().map(Rc::new).collect()
                }),
                // map_opt(opt(separated_list(preceded(opt(sp), char(',')), value)), |opt| opt),
                preceded(opt(sp), char(')')),
            ),
        ),
    )(input)
}

fn function_call<'a, E: ParseError<&'a str>>(
    input: &'a str,
) -> IResult<&'a str, (&'a str, VecRcExpr), E> {
    pair(identifier, parameters)(input)
}

fn identifier_only<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    map(pair(identifier, not(parameters)), |(a, _b)| a)(input)
}

/// here, we apply the space parser before trying to parse a value
fn value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    preceded(
        sp,
        alt((
            map(double, Expr::Num),
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(function_call, |(f_name, params)| {
                Expr::FunctionCall(String::from(f_name), params)
            }),
            map(array, Expr::Array),
            map(identifier_only, |s| Expr::Identifier(s.to_string())),
        )),
    )(input)
}

fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(opt(sp), value, opt(sp))(input)
}

fn parse_expr(expression: &str) -> Result<Expr, String> {
    let expr = expr::<(&str, ErrorKind)>(expression);
    match expr {
        Ok(ok) => Ok(ok.1),
        Err(err_kind) => Err(format!("{:?}", err_kind)),
    }
}

fn prepare_expr_and_identifiers(expr: Expr, funcs: &FunctionImplList) -> ExprAndIdentifiers {
    let mut identifiers = HashSet::<String>::new();
    let expr = prepare_expr(Rc::new(expr), funcs, &mut identifiers);
    ExprAndIdentifiers {
        expr,
        identifiers_names: identifiers,
    }
}

fn prepare_expr_list(
    exprs: &SliceRcExpr,
    funcs: &FunctionImplList,
    identifiers: &mut HashSet<String>,
) -> VecRcExpr {
    exprs
        .iter()
        .map(|p| prepare_expr(p.clone(), funcs, identifiers))
        .collect()
}

fn prepare_expr(
    expr: RcExpr,
    funcs: &FunctionImplList,
    identifiers: &mut HashSet<String>,
) -> RcExpr {
    match expr.as_ref() {
        Expr::Identifier(name) => {
            identifiers.insert(name.clone());
            expr
        }
        Expr::FunctionCall(name, parameters) => match &funcs.get(name) {
            Some(fnc) => Rc::new(Expr::PreparedFunctionCall(
                name.clone(),
                prepare_expr_list(parameters, funcs, identifiers),
                Rc::clone(fnc),
            )),
            None => expr,
        },
        // Expr::FunctionCall(name, parameters) => {
        //     let parameters = prepare_expr_list(parameters, funcs, identifiers);
        //     match &funcs.get(name) {
        //         Some(fnc) => Rc::new(Expr::PreparedFunctionCall(
        //             name.clone(),
        //             parameters,
        //             Rc::clone(fnc),
        //         )),
        //         None => Rc::new(Expr::FunctionCall(name.clone(), parameters)),
        //     }
        // }
        Expr::Array(elements) => {
            Rc::new(Expr::Array(prepare_expr_list(elements, funcs, identifiers)))
        }
        _ => expr,
    }
}

fn exec_expr<'a>(expr: &'a RcExpr, values: &'a IdentifierValues) -> Result<RcExpr, String> {
    match expr.as_ref() {
        Expr::Str(_) => Ok(expr.clone()),
        Expr::Boolean(_) => Ok(expr.clone()),
        Expr::Num(_) => Ok(expr.clone()),
        Expr::Array(_) => Ok(expr.clone()),
        Expr::Identifier(name) => match &values.get(name) {
            Some(s) => Ok(Rc::new(Expr::Str(s()))),
            None => Err(format!(
                "Unable to find value for identifier named '{}'",
                name
            )),
        },
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(name, _parameters) => {
            Err(format!("Unable to find the function named '{}'", name))
        }
        Expr::PreparedFunctionCall(_, parameters, fnc) => {
            let call_result = fnc(&parameters)?;
            exec_expr(&call_result, values)
        }
    }
}

fn expr_to_string(expr: &Expr) -> String {
    match expr {
        Expr::Str(s) => s.to_string(),
        Expr::Boolean(b) => b.to_string(),
        Expr::Num(n) => n.to_string(),
        Expr::Array(_) => "Array".to_string(),
        Expr::Identifier(i) => format!("[{}]", i),
        // Expr::Identifier(name) => match &values.get(name) {
        //     Some(s) => s.to_string(),
        //     None => format!("Unable to find value for identifier named '{}'", name),
        // },
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(_, _) => "FunctionCall".to_string(),
        Expr::PreparedFunctionCall(_, _, _) => "PreparedFunctionCall".to_string(),
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;
    use test_case::test_case;

    macro_rules! rc_expr_str {
        ( $x:expr ) => {
            Rc::new(Expr::Str($x))
        };
    }
    macro_rules! rc_expr_num {
        ( $x:expr ) => {
            Rc::new(Expr::Num($x))
        };
    }

    #[test]
    fn parse_parameters() {
        // let p = parameters::<ParseError<&str>>("");
        // assert_eq!(p.unwrap(), ("",Vec::<Expr>::new()));
        // println()
    }

    #[test_case("true" => Expr::Boolean(true))]
    #[test_case("false" => Expr::Boolean(false))]
    fn parse_boolean(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case(stringify!("test") => "test")]
    #[test_case(stringify!("t") => "t")]
    #[test_case(stringify!("test\"doublequote") => "test\"doublequote")]
    #[test_case(stringify!("test\\slash") => "test\\slash")]
    #[test_case(stringify!("test\newline") => "test\newline")]
    #[test_case(stringify!("test\ttab") => "test\ttab")]
    #[test_case(stringify!("test\rreturn") => "test\rreturn")]
    fn parse_str(expression: &str) -> String {
        let result = parse_expr(expression);
        println!("{:?}", result);
        let expr = result.unwrap();
        if let Expr::Str(result) = expr {
            result
        } else {
            panic!("{:?}", expr)
        }
    }

    #[test_case("1" => Expr::Num(1_f64))]
    #[test_case("1.2" => Expr::Num(1.2_f64))]
    #[test_case("-0.42" => Expr::Num(-0.42_f64))]
    fn parse_num(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("id" => Expr::Identifier("id".to_string()))]
    #[test_case("@idarobase" => Expr::Identifier("idarobase".to_string()))]
    #[test_case("id_id" => Expr::Identifier("id_id".to_string()))]
    #[test_case("id42" => Expr::Identifier("id42".to_string()))]
    #[test_case("_id0" => Expr::Identifier("_id0".to_string()))]
    #[test_case("_id1" => Expr::Identifier("_id1".to_string()))]
    fn parse_identifier(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("[1,2]" => Expr::Array(vec![rc_expr_num!(1_f64), rc_expr_num!(2_f64)]))]
    fn parse_array(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test(1,2)" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1_f64), rc_expr_num!(2_f64)]))]
    #[test_case("test()" => Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))]
    #[test_case("test(aa)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Identifier("aa".to_string()))]))]
    fn parse_function_call(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test([\"value\", 42],2)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Array(vec![rc_expr_str!("value".to_string()), rc_expr_num!(42_f64)])), rc_expr_num!(2_f64)]))]
    fn parse_complexe_expressions(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case(stringify!("test") => Vec::<String>::new())]
    #[test_case("test" => vec!["test"])]
    #[test_case("[test2]" => vec!["test2"])]
    #[test_case("[test2, test3, test2, test3]" => vec!["test2", "test3"])]
    #[test_case("unknownFunc(test7)" => Vec::<String>::new())]
    #[test_case("[test2, test3, test3, knownFunc(test4, test5), test6, test5]" => vec!["test2", "test3", "test4", "test5", "test6"])]
    fn prepare_expr_and_identifiers_detection(expression: &str) -> Vec<String> {
        let expr = parse_expr(expression).unwrap();
        let mut funcs = FunctionImplList::new();
        funcs.insert(
            "knownFunc".to_string(),
            Rc::new(|_v: &VecRcExpr| Ok(rc_expr_num!(42_f64))),
        );
        let expr = prepare_expr_and_identifiers(expr, &funcs);
        println!("{:?}", expr);
        let mut result = expr
            .identifiers_names
            .iter()
            .cloned()
            .collect::<Vec<String>>();
        result.sort();
        result
    }

    #[test]
    fn execute_one_expression() {
        let mut funcs = FunctionImplList::new();
        funcs.insert(
            "first".to_string(),
            Rc::new(|v: &VecRcExpr| {
                v.first().map_or_else(
                    || Err("There was no first value.".to_string()),
                    |x| Ok(x.clone()),
                )
            }),
        );

        funcs.insert(
            "forty_two".to_string(),
            Rc::new(|_v: &VecRcExpr| Ok(rc_expr_num!(42_f64))),
        );
        funcs.insert(
            "forty_two_str".to_string(),
            Rc::new(|_v: &VecRcExpr| Ok(rc_expr_str!("42".to_string()))),
        );

        let mut values = IdentifierValues::new();
        values.insert("my".into(), Box::new(|| "value".to_string()));

        let expression = "first(first(first(my,2,3),2,3),2,3)";
        let result = parse_exec_expr(expression, &funcs, &values);
        assert_eq!(result, "value");
        println!("{:?}", result);
    }

    fn parse_exec_expr<'a>(
        expression: &'a str,
        funcs: &FunctionImplList,
        values: &IdentifierValues,
    ) -> String {
        let expr = parse_expr(expression).unwrap();
        let expr = prepare_expr_and_identifiers(expr, funcs);
        let result = exec_expr(&expr.expr, values).unwrap();
        expr_to_string(&result)
    }
}

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

use once_cell::sync::Lazy;

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

    let mut funcs: FunctionImplList = HashMap::new();

    funcs.insert(
        "true".to_string(),
        Rc::new(|_: &VecRcExpr| Ok(Rc::new(Expr::Boolean(true)))),
    );

    funcs.insert(
        "first".to_string(),
        Rc::new(|v: &VecRcExpr| {
            v.first().map_or_else(
                || Err("There was no first value.".to_string()),
                |x| Ok(x.clone()),
            )
        }),
    );

    let expr = prepare_expr_and_identifiers(expr, &funcs);
    Box::into_raw(Box::new(expr))
}

#[no_mangle]
extern "C" fn ffi_get_identifiers(ptr: *mut ExprAndIdentifiers) -> *mut c_char {
    let expr = unsafe {
        assert!(!ptr.is_null());
        &mut *ptr
    };

    let identifiers_separated = expr
        .identifiers_names
        .iter()
        .cloned()
        .collect::<Vec<String>>()
        .join("|");
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

#[no_mangle]
extern "C" fn ffi_exec_expr(
    ptr: *mut ExprAndIdentifiers,
    identifier_values: *const IdentifierKeyValue,
    identifier_values_len: usize,
) -> *mut c_char {
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
        values.insert(k, get_v);
    }

    let result = exec_expr(&expr.expr, &values).unwrap();
    let s_result = expr_to_string(&result);
    let c_str_result = CString::new(s_result).unwrap();
    c_str_result.into_raw()
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
