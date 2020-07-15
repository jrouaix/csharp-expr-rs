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

fn binary_operator<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, AssocOp, E> {
    context(
        "binary_operator",
        delimited(
            sp,
            alt((
                map(tag("+"), |_| AssocOp::Add),
                map(tag("-"), |_| AssocOp::Subtract),
                map(tag("*"), |_| AssocOp::Multiply),
                map(tag("/"), |_| AssocOp::Divide),
                map(tag("%"), |_| AssocOp::Modulus),
                map(tag("&&"), |_| AssocOp::LAnd),
                map(tag("||"), |_| AssocOp::LOr),
                map(tag("=="), |_| AssocOp::Equal),
                map(tag("<="), |_| AssocOp::LessEqual),
                map(tag("<"), |_| AssocOp::Less),
                map(tag("!="), |_| AssocOp::NotEqual),
                map(tag(">="), |_| AssocOp::GreaterEqual),
                map(tag(">"), |_| AssocOp::Greater),
            )),
            sp,
        ),
    )(input)
}

fn binary_operation<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (Expr, Expr, AssocOp), E> {
    context(
        "binary_operation",
        delimited(opt(char('(')), map(tuple((non_binary_operation_value, binary_operator, value)), |x| (x.0, x.2, x.1)), opt(char(')'))),
    )(input)
}

// string parser from here : https://github.com/Geal/nom/issues/1075
fn parse_str<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    escaped(
        take_while1(|c| c != '\\' && c != '"'),
        '\\',
        one_of("\"\\/bfnrtu"), // Note, this will not detect invalid unicode escapes.
    )(i)
}

fn string<'a, E: ParseError<&'a str>>(i: &'a str) -> IResult<&'a str, &'a str, E> {
    context("string", preceded(char('\"'), cut(terminated(map(opt(parse_str), |o| o.unwrap_or_default()), char('\"')))))(i)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    alt((map(tag("false"), |_| false), map(tag("true"), |_| true)))(input)
}

/// null combinator
fn null<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (i, _) = tag("null")(input)?;
    Ok((i, Expr::Null))
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "array",
        preceded(
            char('['),
            cut(terminated(map(separated_list(preceded(sp, char(',')), value), |v| v.into_iter().map(Rc::new).collect()), preceded(sp, char(']')))),
        ),
    )(input)
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context("identifier", preceded(opt(sp), preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric1))))))(input)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context(
        "parameters",
        preceded(
            preceded(opt(sp), char('(')),
            terminated(map(separated_list(preceded(opt(sp), char(',')), value), |v| v.into_iter().map(Rc::new).collect()), preceded(opt(sp), char(')'))),
        ),
    )(input)
}

/// empty parameters
fn empty_parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context("empty_parameters", preceded(preceded(opt(sp), char('(')), terminated(map(opt(sp), |_| vec![]), preceded(opt(sp), char(')')))))(input)
}

fn function_call<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (&'a str, VecRcExpr), E> {
    pair(identifier, alt((parameters, empty_parameters)))(input)
}

fn identifier_only<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    map(pair(identifier, not(parameters)), |(a, _b)| a)(input)
}

/// here, we apply the space parser before trying to parse a value
fn value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    preceded(
        sp,
        alt((
            map(binary_operation, |(left, right, op)| Expr::BinaryOperator(Rc::new(left), Rc::new(right), op)),
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            null,
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(array, Expr::Array),
            map(identifier_only, |s| Expr::Identifier(s.to_string())),
        )),
    )(input)
}

/// here, we apply the space parser before trying to parse a value
fn non_binary_operation_value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    preceded(
        sp,
        alt((
            // map(binary_operation, |(left, right, op)| Expr::BinaryOperator(Rc::new(left), Rc::new(right), op)),
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            null,
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(array, Expr::Array),
            map(identifier_only, |s| Expr::Identifier(s.to_string())),
        )),
    )(input)
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(sp, value, sp)(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::ErrorKind;
    use rust_decimal_macros::*;
    use test_case::test_case;

    #[test_case("+", AssocOp::Add)]
    #[test_case("- ", AssocOp::Subtract)]
    #[test_case(" /", AssocOp::Divide)]
    #[test_case(" && ", AssocOp::LAnd)]
    fn binary_operator_test(text: &str, expected: AssocOp) {
        let result = binary_operator::<(&str, ErrorKind)>(text);
        assert_eq!(result, Ok(("", expected)));
    }

    #[test_case("(1 + 2)", (Expr::Num(dec!(1)), Expr::Num(dec!(2)), AssocOp::Add))]
    #[test_case("( 3 - 2)", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Subtract))]
    #[test_case("( 3 / 2)", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Divide))]
    #[test_case("(3|| 5)", (Expr::Num(dec!(3)), Expr::Num(dec!(5)), AssocOp::LOr))]
    #[test_case("5 * 5", (Expr::Num(dec!(5)), Expr::Num(dec!(5)), AssocOp::Multiply))]
    #[test_case(" 42 % \"2\"", (Expr::Num(dec!(42)), Expr::Str("2".to_string()), AssocOp::Modulus))]
    #[test_case("2 == 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Equal))]
    #[test_case("2 > 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Greater))]
    #[test_case("2 < 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Less))]
    #[test_case("2 >= 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::GreaterEqual))]
    #[test_case("2 <= 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::LessEqual))]
    #[test_case("true && false", (Expr::Boolean(true), Expr::Boolean(false), AssocOp::LAnd))]
    #[test_case("false || true", (Expr::Boolean(false), Expr::Boolean(true), AssocOp::LOr))]
    fn binary_operation_test(text: &str, expected: (Expr, Expr, AssocOp)) {
        let result = binary_operation::<(&str, ErrorKind)>(text);
        assert_eq!(result, Ok(("", expected)));
    }

    #[test]
    fn binary_operation_parenthesis_test() {
        let expected = Ok((
            "",
            Expr::BinaryOperator(
                RcExpr::new(Expr::Num(dec!(3))),
                RcExpr::new(Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(5))), RcExpr::new(Expr::Str("2".to_string())), AssocOp::Subtract)),
                AssocOp::Divide,
            ),
        ));
        assert_eq!(value::<(&str, ErrorKind)>("3 / (5-\"2\")"), expected);
        assert_eq!(value::<(&str, ErrorKind)>("3 / 5-\"2\""), expected);
        assert_eq!(value::<(&str, ErrorKind)>("(3 / 5-\"2\")"), expected);
    }
}
