// #![cfg(feature = "alloc")]

// extern crate nom;
// extern crate jemallocator;

// #[global_allocator]
// static ALLOC: jemallocator::Jemalloc = jemallocator::Jemalloc;

use nom::{
  branch::alt,
  bytes::complete::{escaped, tag, take_while},
  character::complete::{alphanumeric1, alphanumeric0, alpha1, char, one_of},
  combinator::{map, opt, cut},
  error::{context, convert_error, ErrorKind, ParseError,VerboseError},
  multi::separated_list,
  number::complete::double,
  sequence::{delimited, preceded, separated_pair, terminated, tuple, pair},
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

#[derive(Debug, PartialEq)]
pub enum Expr {
  Str(String),
  Boolean(bool),
  Num(f64),
  Array(Vec<Expr>),
  Object(HashMap<String, Expr>),
  FunctionCall(String, Vec<Expr>),
  // BinaryOperator(Box<Expr>, Box<Expr>, AssocOp)
}



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
  alt((
      map(tag("false"), |_| false),
      map(tag("true"), |_| true)
  ))(input)
}

/// full string combinator
fn string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  context("string",
    preceded(
      char('\"'),
      cut(terminated(
          parse_str,
          char('\"')
  ))))(i)
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<Expr>, E> {
  context(
    "array",
    preceded(char('['),
    cut(terminated(
      separated_list(preceded(sp, char(',')), value),
      preceded(sp, char(']'))))
  ))(i)
}

/// key : value combinator
fn key_value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (&'a str, Expr), E> {
  separated_pair(preceded(sp, string), cut(preceded(sp, char(':'))), value)(i)
}

/// hash { key : value, ... } combinator 
fn hash<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, HashMap<String, Expr>, E> {
  context(
    "map",
    preceded(char('{'),
    cut(terminated(
      map(
        separated_list(preceded(sp, char(',')), key_value),
        |tuple_vec| {
          tuple_vec.into_iter().map(|(k, v)| (String::from(k), v)).collect()
        }),
      preceded(sp, char('}')),
    ))
  ))(i)
}

/// here, we apply the space parser before trying to parse a value
fn value<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
  preceded(
    sp,
    alt((
      map(double, Expr::Num),
      map(boolean, Expr::Boolean),
      map(string, |s| Expr::Str(String::from(s))),
      map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
      map(hash, Expr::Object),
      map(array, Expr::Array),
    )),
  )(i)
}

/// the root element of a JSON parser is either an object or an array
fn expr<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Expr, E> {
  delimited(
    opt(sp),
    value,
    opt(sp),
  )(i)
}

fn identifier<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
  context(
    "identifier",
    preceded(
      opt(sp),
      preceded(
        opt(tag("_")), 
        alphanumeric0
        )
      )
  )(i)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, Vec<Expr>, E> {
  context(
    "parameters",
    preceded(char('('),
    cut(terminated(
      separated_list(preceded(sp, char(',')), value),
      preceded(sp, char(')'))))
  ))(i)
}

fn function_call<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, (&'a str,  Vec<Expr>), E> {
  pair(identifier, parameters)(i)
}

// https://dev.to/living_syn/calling-rust-from-c-6hk

fn main() {

  let mut funcs : HashMap<String,  Box<dyn Fn(&Vec<Expr>) -> Result<&Expr, String>>>  = HashMap::new();
  
  funcs.insert(
    "test".to_string(),
    Box::new(| v:&Vec<Expr> | Ok(&Expr::Boolean(true)))
  );

  funcs.insert(
    "func2".to_string(),
    Box::new(| v:&Vec<Expr> | v.first().ok_or("".to_string()))
  );

  let expr =  expr::<(&str, ErrorKind)>("test(func2(42), \"a\", func2(rr(5), true))")
    .unwrap()
    .1;
  
  // for _ in 0..10_000_00 {
    let result = exec_expr(&expr, &funcs);
    print!("{:?}", result);  
  // }

}

//https://dev.to/luzero/building-crates-so-they-look-like-c-abi-libraries-1ibn
//

fn exec_expr<'a>(expr : &'a Expr , funcs : &HashMap<String,  Box<dyn Fn(&Vec<Expr>) -> Result<&Expr, String>>>) -> Result<&'a Expr, String>
{
  match expr {
    Expr::Str(_) => Ok(expr),
    Expr::Boolean(_) =>  Ok(expr),
    Expr::Num(_) => Ok(expr),
    Expr::Array(_) => Ok(expr),
    Expr::Object(_) => Ok(expr),
    // Expr::BinaryOperator(_, _, _) => Ok(expr),
    Expr::FunctionCall(name, parameters) => {
      match funcs.get(name) {
        Some(fnc) => {
          let call_result = fnc(parameters)?;
          exec_expr(call_result, funcs)
        },
        None => Err(format!("Unable to find the function named '{}'", name))
      }
    },
  }
}

