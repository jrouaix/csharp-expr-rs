use crate::expressions::*;

use nom::{
    branch::alt,
    bytes::complete::{escaped, is_a, is_not, tag, take_while, take_while1}, // escaped_transform
    character::complete::{alphanumeric0, alphanumeric1, anychar, char, one_of},
    combinator::{cut, map, map_opt, not, opt, recognize},
    error::{context, ParseError},
    multi::many1,
    multi::separated_list,
    number::complete::double,
    sequence::{delimited, pair, preceded, terminated, tuple},
    IResult,
};
use rust_decimal::prelude::FromPrimitive;
use std::rc::Rc;
use unescape::unescape;

/// A nom parser has the following signature:
/// `Input -> IResult<Input, Output, Error>`, with `IResult` defined as:
/// `type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;`

// fn not_space(s: &str) -> IResult<&str, &str> {
//     is_not(" \t\r\n")(s)
// }

/// spaces combinator
fn sp<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    // is_a(" \t\r\n")(input) // not working
    take_while(|c| " \t\r\n".contains(c))(input)
}

// /// string interior combinator
// fn str_content<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     // alt((tag("\"\""), escaped(alphanumeric1, '\\', one_of("\\\"rnt"))))(input)

//     // // WORKING
//     let white_spaces = alt((tag(" "), tag("\t"), tag("_"), tag("-")));
//     let punctuation = alt((tag("."), tag(","), tag(":"), tag("!"), tag("?"), tag("¿"), tag("%"))); // a lot more ! to debug

//     // let white_spaces = is_a("&é'(-è_çà@^`|([{~}])");
//     escaped(alt((alphanumeric1, white_spaces, punctuation)), '\\', one_of("\\\"rnt"))(input)

//     // TRY 1 => panics a lot
//     // escaped(anychar, '\\', one_of("\\\"rnt"))(input)
//     // TRY 2 => 100% CPU
//     // escaped(take_while(|c| c != '"'), '\\', one_of("\\\"rnt"))(input)
//     // TRY 3 => 100% CPU
//     // escaped(not(char('"')), '\\', one_of("\\\"rnt"))(input)
// }

// /// full string combinator
// fn stringU<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     context("string", preceded(char('\"'), cut(terminated(str_content, char('\"')))))(input)
// }

// string parser from here : https://github.com/Geal/nom/issues/1075

fn parse_str<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    escaped(
        take_while1(|c| c != '\\' && c != '"'),
        '\\',
        one_of("\"\\/bfnrtu"), // Note, this will not detect invalid unicode escapes.
    )(i)
}

fn string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "string",
        preceded(char('\"'), cut(terminated(map(opt(parse_str), |o| o.unwrap_or_default()), char('\"')))),
    )(i)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    alt((map(tag("false"), |_| false), map(tag("true"), |_| true)))(input)
}

/// null combinator
fn null<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (), E> {
    map(tag("null"), |_| ())(input)
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "array",
        preceded(
            char('['),
            cut(terminated(
                map(separated_list(preceded(sp, char(',')), value), |v| v.into_iter().map(Rc::new).collect()),
                preceded(sp, char(']')),
            )),
        ),
    )(input)
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "identifier",
        preceded(opt(sp), preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric0))))),
    )(input)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "parameters",
        preceded(
            char('('),
            terminated(
                map(separated_list(preceded(sp, char(',')), value), |v| v.into_iter().map(Rc::new).collect()),
                // map_opt(opt(separated_list(preceded(opt(sp), char(',')), value)), |opt| opt),
                preceded(opt(sp), char(')')),
            ),
        ),
    )(input)
}

fn function_call<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (&'a str, VecRcExpr), E> {
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
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            map(null, |_| Expr::Null),
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(array, Expr::Array),
            map(identifier_only, |s| Expr::Identifier(s.to_string())),
        )),
    )(input)
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(opt(sp), value, opt(sp))(input)
}
