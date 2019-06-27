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

#[derive(Debug, PartialEq)]
pub enum Expr {
  Str(String),
  Boolean(bool),
  Num(f64),
  Array(Vec<Expr>),
  Object(HashMap<String, Expr>),
  FunctionCall(String, Vec<Expr>)
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
      map(hash, Expr::Object),
      map(array, Expr::Array),
      map(string, |s| Expr::Str(String::from(s))),
      map(double, Expr::Num),
      map(boolean, Expr::Boolean),
      map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
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

// fn function_call<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<(&'a str, (&'a str, Vec<Expr>)), E> {
//   pair(identifier, parameters)(i)


// //   Ok(("", vec![Expr::Boolean(true)]))
// }

fn main() {

  // let parser = separated_pair(tag("abc"), tag("|"), tag("efg"));
  
  // let parser = tuple::<(&str, ErrorKind)>((identifier, identifier));

  //  let application_inner = map(tuple((identifier, identifier)), |(head, tail)| {
  //     ""
  //   });
  // finally, we wrap it in an s-expression
  // s_exp(application_inner)(i);

  println!("{:?}", expr::<(&str, ErrorKind)>("test(42, \"a\", func2(5))"));


  // let data = "  { \"a\"\t: 42,
  // \"b\": [ \"x\", \"y\", 12 ] ,
  // \"c\": { \"hello\" : \"world\"
  // }
  // } ";

  // println!("will try to parse valid JSON data:\n\n**********\n{}\n**********\n", data);

  // // this will print:
  // // Ok(
  // //     (
  // //         "",
  // //         Object(
  // //             {
  // //                 "b": Array(
  // //                     [
  // //                         Str(
  // //                             "x",
  // //                         ),
  // //                         Str(
  // //                             "y",
  // //                         ),
  // //                         Num(
  // //                             12.0,
  // //                         ),
  // //                     ],
  // //                 ),
  // //                 "c": Object(
  // //                     {
  // //                         "hello": Str(
  // //                             "world",
  // //                         ),
  // //                     },
  // //                 ),
  // //                 "a": Num(
  // //                     42.0,
  // //                 ),
  // //             },
  // //         ),
  // //     ),
  // // )
  // println!(
  //   "parsing a valid file:\n{:#?}\n",
  //   root::<(&str, ErrorKind)>(data)
  // );

  // let data = "  { \"a\"\t: 42,
  // \"b\": [ \"x\", \"y\", 12 ] ,
  // \"c\": { 1\"hello\" : \"world\"
  // }
  // } ";

  // println!("will try to parse invalid JSON data:\n\n**********\n{}\n**********\n", data);

  // // here we use `(Input, ErrorKind)` as error type, which is used by default
  // // if you don't specify it. It contains the position of the error and some
  // // info on which parser encountered it.
  // // It is fast and small, but does not provide much context.
  // //
  // // This will print:
  // // basic errors - `root::<(&str, ErrorKind)>(data)`:
  // // Err(
  // //   Failure(
  // //       (
  // //           "1\"hello\" : \"world\"\n  }\n  } ",
  // //           Char,
  // //       ),
  // //   ),
  // // )
  // println!(
  //   "basic errors - `root::<(&str, ErrorKind)>(data)`:\n{:#?}\n",
  //   root::<(&str, ErrorKind)>(data)
  // );

  // // nom also provides `the `VerboseError<Input>` type, which will generate a sort
  // // of backtrace of the path through the parser, accumulating info on input positons
  // // and affected parsers.
  // //
  // // This will print:
  // //
  // // parsed verbose: Err(
  // //   Failure(
  // //       VerboseError {
  // //           errors: [
  // //               (
  // //                   "1\"hello\" : \"world\"\n  }\n  } ",
  // //                   Char(
  // //                       '}',
  // //                   ),
  // //               ),
  // //               (
  // //                   "{ 1\"hello\" : \"world\"\n  }\n  } ",
  // //                   Context(
  // //                       "map",
  // //                   ),
  // //               ),
  // //               (
  // //                   "{ \"a\"\t: 42,\n  \"b\": [ \"x\", \"y\", 12 ] ,\n  \"c\": { 1\"hello\" : \"world\"\n  }\n  } ",
  // //                   Context(
  // //                       "map",
  // //                   ),
  // //               ),
  // //           ],
  // //       },
  // //   ),
  // // )
  // println!("parsed verbose: {:#?}", root::<VerboseError<&str>>(data));

  // match root::<VerboseError<&str>>(data) {
  //   Err(Err::Error(e)) | Err(Err::Failure(e)) => {

  //     // here we use the `convert_error` function, to transform a `VerboseError<&str>`
  //     // into a printable trace.
  //     //
  //     // This will print:
  //     // verbose errors - `root::<VerboseError>(data)`:
  //     // 0: at line 2:
  //     //   "c": { 1"hello" : "world"
  //     //          ^
  //     // expected '}', found 1
  //     //
  //     // 1: at line 2, in map:
  //     //   "c": { 1"hello" : "world"
  //     //        ^
  //     //
  //     // 2: at line 0, in map:
  //     //   { "a" : 42,
  //     //   ^
  //     println!("verbose errors - `root::<VerboseError>(data)`:\n{}", convert_error(data, e));
  //   }
  //   _ => {},
  // }
}
