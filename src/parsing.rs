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
        // delimited(opt(char('(')), map(tuple((non_binary_operation_value, binary_operator, value)), |x| (x.0, x.2, x.1)), opt(char(')'))),
        map(tuple((non_binary_operation_value, binary_operator, value)), |x| (x.0, x.2, x.1)),
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
    context("string", delimited(char('\"'), cut(map(opt(parse_str), |o| o.unwrap_or_default())), char('\"')))(i)
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
    context("parameters", delimited(char('['), comma_separated_values, char(']')))(input)
}

/// parameters between parenthesis
fn comma_separated_values<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context("comma_separated_values", map(separated_list(char(','), value), |v| v.into_iter().map(Rc::new).collect()))(input)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context("parameters", delimited(char('('), comma_separated_values, char(')')))(input)
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context("identifier", terminated(preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric1)))), sp))(input)
}

/// empty parameters
fn empty_parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    context("empty_parameters", map(tuple((char('('), sp, char(')'))), |_| vec![]))(input)
}

fn function_call<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (&'a str, VecRcExpr), E> {
    pair(identifier, alt((parameters, empty_parameters)))(input)
}

// fn identifier_only<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     map(pair(identifier, not(preceded(sp, char('(')))), |(a, _b)| a)(input)
// }

/// here, we apply the space parser before trying to parse a value
fn value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(
        sp,
        alt((
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(binary_operation, |(left, right, op)| Expr::BinaryOperator(Rc::new(left), Rc::new(right), op)),
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            null,
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(array, Expr::Array),
            map(identifier, |s| Expr::Identifier(s.to_string())),
        )),
        sp,
    )(input)
}

/// here, we apply the space parser before trying to parse a value
fn non_binary_operation_value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    delimited(
        sp,
        alt((
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            null,
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(array, Expr::Array),
            map(identifier, |s| Expr::Identifier(s.to_string())),
        )),
        sp,
    )(input)
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    value(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::ErrorKind;
    use rust_decimal_macros::*;
    use test_case::test_case;

    macro_rules! rc_expr_str {
        ( $x:expr ) => {
            Rc::new(Expr::Str($x.to_string()))
        };
    }
    macro_rules! rc_expr_num {
        ( $x:expr ) => {
            Rc::new(Expr::Num(dec!($x)))
        };
    }
    macro_rules! rc_expr_null {
        () => {
            Rc::new(Expr::Null)
        };
    }

    #[test_case("+", AssocOp::Add)]
    #[test_case("- ", AssocOp::Subtract)]
    #[test_case(" /", AssocOp::Divide)]
    #[test_case(" && ", AssocOp::LAnd)]
    fn binary_operator_test(text: &str, expected: AssocOp) {
        let result = binary_operator::<(&str, ErrorKind)>(text);
        assert_eq!(result, Ok(("", expected)));
    }

    #[test_case("1+2", (Expr::Num(dec!(1)), Expr::Num(dec!(2)), AssocOp::Add))]
    #[test_case(" 3- 2 ", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Subtract))]
    #[test_case(" 3 /2", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Divide))]
    #[test_case("3|| 5 ", (Expr::Num(dec!(3)), Expr::Num(dec!(5)), AssocOp::LOr))]
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

    #[test_case("test()", Expr::FunctionCall("test".to_string(), VecRcExpr::new()))]
    #[test_case(" toto () ", Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]
    #[test_case(" toto (toto()) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]))]
    // #[test_case("toto((null - null)) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::BinaryOperator( RcExpr::new(Expr::Null),RcExpr::new(Expr::Null), AssocOp::Subtract))]))]
    #[test_case("tata(null - null) ", Expr::FunctionCall("tata".to_string(), vec![RcExpr::new(Expr::BinaryOperator( RcExpr::new(Expr::Null),RcExpr::new(Expr::Null), AssocOp::Subtract))]))]
    fn parse_some_expr(text: &str, expected: Expr) {
        let result = parse_expr(text).unwrap();
        assert_eq!(result, expected);
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
        // assert_eq!(value::<(&str, ErrorKind)>("3 / (5-\"2\")"), expected);
        assert_eq!(value::<(&str, ErrorKind)>("3 / 5-\"2\""), expected);
        // assert_eq!(value::<(&str, ErrorKind)>("(3 / 5-\"2\")"), expected);
    }

    #[test_case("true" => Expr::Boolean(true))]
    #[test_case("false" => Expr::Boolean(false))]
    fn parse_boolean(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    // #[test_case("(1 + 2)" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(2), AssocOp::Add))]
    // #[test_case("(1 * 3)" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(3), AssocOp::Multiply))]
    #[test_case("1 + 2" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(2), AssocOp::Add))]
    #[test_case("1 * 3" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(3), AssocOp::Multiply))]
    fn parse_binary_operator(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test]
    fn parse_empty_string() {
        let expr = parse_expr("\"\"").unwrap();
        assert_eq!(expr, Expr::Str("".to_string()))
    }

    #[test]
    fn parse_string_with_doublequote() -> Result<(), String> {
        let expression = "\" \\\" \"";
        let expected = " \" ";
        let result = parse_expr(expression)?;
        println!("'{}' => '{}'", expression, result.to_string());
        assert_eq!(result, Expr::Str(expected.to_string()));
        Ok(())
    }

    #[test_case(stringify!("null") => "null")]
    #[test_case(stringify!("test") => "test")]
    #[test_case(stringify!("t") => "t")]
    #[test_case(stringify!("test\"doublequote") => "test\"doublequote")]
    #[test_case(stringify!("test\\slash") => "test\\slash")]
    #[test_case(stringify!("test\newline") => "test\newline")]
    #[test_case(stringify!("test\ttab") => "test\ttab")]
    #[test_case(stringify!("test\rreturn") => "test\rreturn")]
    #[test_case(stringify!("test escape") => "test escape")]
    #[test_case("\"test escape\"" => "test escape")]
    #[test_case("\"test\ttab\"" => "test\ttab")]
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

    #[test_case("1" => Expr::Num(dec!(1)))]
    #[test_case("1.2" => Expr::Num(dec!(1.2)))]
    #[test_case("-0.42" => Expr::Num(dec!(-0.42)))]
    fn parse_num(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("null" => Expr::Null)]
    fn parse_null(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("a" => Expr::Identifier("a".to_string()))]
    #[test_case("id" => Expr::Identifier("id".to_string()))]
    #[test_case(" hello " => Expr::Identifier("hello".to_string()))]
    #[test_case("@idarobase" => Expr::Identifier("idarobase".to_string()))]
    // #[test_case("id_id" => Expr::Identifier("id_id".to_string()))] // to debug
    #[test_case("id42" => Expr::Identifier("id42".to_string()))]
    #[test_case("_id0" => Expr::Identifier("_id0".to_string()))]
    #[test_case("_id1" => Expr::Identifier("_id1".to_string()))]
    fn parse_identifier(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("[1,2]" => Expr::Array(vec![rc_expr_num!(1), rc_expr_num!(2)]))]
    fn parse_array(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test(1,2)" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(2)]))]
    #[test_case("test ( 1 , 42 )" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(42)]))]
    #[test_case("test()" => Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))] // to debug
    #[test_case("test(test())" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))]))] // to debug
    #[test_case("test(aa)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Identifier("aa".to_string()))]))]
    #[test_case("Test(42)" => Expr::FunctionCall("Test".to_string(), vec![Rc::new(Expr::Num(dec!(42)))]))]
    fn parse_function_call(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test([\"value\", 42, null],2, \"null\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Array(vec![rc_expr_str!("value".to_string()), rc_expr_num!(42), rc_expr_null!()])), rc_expr_num!(2), rc_expr_str!("null".to_string())]))]
    #[test_case("hello" => Expr::Identifier("hello".to_string()))]
    #[test_case(" _hella " => Expr::Identifier("_hella".to_string()))]
    #[test_case(" helloworld " => Expr::Identifier("helloworld".to_string()))]
    #[test_case("test(\"value\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("value")]))]
    #[test_case("test(\"va lue\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")]))]
    #[test_case("test(\"va lue\") - 3" => Expr::BinaryOperator(RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), rc_expr_num!(3), AssocOp::Subtract))]
    #[test_case("42 / test(\"va lue\")" => Expr::BinaryOperator(rc_expr_num!(42), RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), AssocOp::Divide))]
    fn parse_complexe_expressions(expression: &'static str) -> Expr {
        let expr = expr::<(&str, ErrorKind)>(expression);
        match expr {
            Ok((rest, expr)) => match rest.len() {
                0 => expr,
                _ => {
                    dbg!(expr);
                    panic!(rest)
                }
            },
            Err(err_kind) => panic!(format!("{:?}", err_kind)),
        }
    }
}
