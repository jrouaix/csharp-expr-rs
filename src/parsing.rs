use crate::expressions::*;

use nom::{
    branch::alt,
    bytes::complete::{escaped, is_a, is_not, tag, take_while, take_while1}, // escaped_transform
    character::complete::{alphanumeric0, alphanumeric1, anychar, char, multispace0, one_of},
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

fn binary_operator<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, AssocOp, E> {
    // dbg!("binary_operator", input);
    context(
        "binary_operator",
        delimited(
            multispace0,
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
            multispace0,
        ),
    )(input)
}

// fn binary_operation<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (Expr, Expr, AssocOp), E> {
//     // dbg!("binary_operation", input);
//     context(
//         "binary_operation",
//         // delimited(opt(char('(')), map(tuple((non_binary_operation_value, binary_operator, value)), |x| (x.0, x.2, x.1)), opt(char(')'))),
//         map(tuple((value_no_ope, binary_operator, value)), |x| (x.0, x.2, x.1)),
//     )(input)
// }

// string parser from here : https://github.com/Geal/nom/issues/1075
fn parse_str<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    // dbg!("parse_str", input);
    escaped(
        take_while1(|c| c != '\\' && c != '"'),
        '\\',
        one_of("\"\\/bfnrtu"), // Note, this will not detect invalid unicode escapes.
    )(input)
}

fn string<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    // dbg!("string", input);
    context("string", delimited(char('\"'), cut(map(opt(parse_str), |o| o.unwrap_or_default())), char('\"')))(input)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    // dbg!("boolean", input);
    context("boolean", alt((map(tag("false"), |_| false), map(tag("true"), |_| true))))(input)
}

/// null combinator
fn null<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // dbg!("null", input);
    context("null", map(tag("null"), |_| Expr::Null))(input)
}

/// array combinator
fn array<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    // dbg!("array", input);
    context("array", delimited(char('['), comma_separated_values, char(']')))(input)
}

/// parameters between parenthesis
fn comma_separated_values<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    // dbg!("comma_separated_values", input);
    context("comma_separated_values", map(separated_list(char(','), value), |v| v.into_iter().map(Rc::new).collect()))(input)
}

/// parameters between parenthesis
fn parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    // dbg!("parameters", input);
    context("parameters", delimited(char('('), comma_separated_values, char(')')))(input)
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    // dbg!("identifier", input);
    context("identifier", terminated(preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric1)))), multispace0))(input)
}

/// empty parameters
fn empty_parameters<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, VecRcExpr, E> {
    // dbg!("empty_parameters", input);
    context("empty_parameters", map(tuple((char('('), multispace0, char(')'))), |_| vec![]))(input)
}

fn function_call<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, (&'a str, VecRcExpr), E> {
    // dbg!("function_call", input);
    context("function_call", pair(identifier, alt((parameters, empty_parameters))))(input)
}

// fn identifier_only<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     map(pair(identifier, not(preceded(sp, char('(')))), |(a, _b)| a)(input)
// }

// pub fn preceded2<I, O1, E: ParseError<I>, F, G>(inner: F) -> impl Fn(I) -> IResult<I, O1, E>
// where
//     F: Fn(I) -> IResult<I, O1, E>,
//     I: Clone,
// {
//     alt((inner, delimited(multispace0, delimited(char('('), inner, char(')')), multispace0)))
//     // move |input: I| {
//     //     let (input, _) = first(input)?;
//     //     second(input)
//     // }
// }

// fn optional_parenthesis<I: Clone, O, E: ParseError<I>, F>(f: F) -> impl Fn(I) -> IResult<I, Option<O>, E>
// where
//     F: Fn(I) -> IResult<I, O, E>,
// {
//     preceded(first: F, second: G)
//     move |input: I| alt((f, delimited(multispace0, delimited(char('('), f, char(')')), multispace0)))(input)
//     // move |input: I| {
//     //     let i = input.clone();
//     //     match f(input) {
//     //         Ok((i, o)) => Ok((i, Some(o))),
//     //         Err(Err::Error(_)) => Ok((i, None)),
//     //         Err(e) => Err(e),
//     //     }
//     // }
// }

fn binary_operations<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (i, first_operand) = value_no_ope(input)?;
    let (i, then) = many1(tuple((binary_operator, value_no_ope)))(i)?;
    let expr = then.into_iter().fold(first_operand, |acc, (op, val)| Expr::BinaryOperator(RcExpr::new(acc), RcExpr::new(val), op));
    Ok((i, expr))
}

fn value_no_ope_no_parenthesis<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // dbg!("value_no_ope_no_parenthesis", input);
    delimited(
        multispace0,
        alt((
            map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
            null,
            map(boolean, Expr::Boolean),
            map_opt(string, |s| unescape(s).map(Expr::Str)),
            map(function_call, |(f_name, params)| Expr::FunctionCall(String::from(f_name), params)),
            map(identifier, |s| Expr::Identifier(s.to_string())),
            map(array, Expr::Array),
        )),
        multispace0,
    )(input)
}

fn value_no_parenthesis<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // dbg!("value_no_parenthesis", input);
    alt((delimited(multispace0, binary_operations, multispace0), value_no_ope))(input)
}

fn value_no_ope<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // dbg!("non_binary_operation_value", input);
    alt((value_no_ope_no_parenthesis, delimited(multispace0, delimited(char('('), value_no_ope, char(')')), multispace0)))(input)
}

fn value<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    // dbg!("value", input);
    alt((value_no_parenthesis, delimited(multispace0, delimited(char('('), value, char(')')), multispace0)))(input)
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    value(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::ErrorKind;
    use rust_decimal_macros::*;
    use std::time::Instant;
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
    // #[test_case("(3)+(4)", (Expr::Num(dec!(3)), Expr::Num(dec!(4)), AssocOp::Add))]
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
    fn binary_operations_test(text: &str, expected: (Expr, Expr, AssocOp)) {
        let result = binary_operations::<(&str, ErrorKind)>(text);
        let (left, right, op) = expected;
        assert_eq!(result, Ok(("", Expr::BinaryOperator(RcExpr::new(left), RcExpr::new(right), op))));
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
                RcExpr::new(Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(3))), RcExpr::new(Expr::Num(dec!(5))), AssocOp::Divide)),
                RcExpr::new(Expr::Str("2".to_string())),
                AssocOp::Subtract,
            ),
        ));
        assert_eq!(value::<(&str, ErrorKind)>("3 / 5-\"2\""), expected);
        assert_eq!(value::<(&str, ErrorKind)>("(3 / 5-\"2\")"), expected);
        // assert_eq!(value::<(&str, ErrorKind)>("(3 / 5) -\"2\""), expected);
    }

    #[test_case("true" => Expr::Boolean(true))]
    #[test_case("false" => Expr::Boolean(false))]
    fn parse_boolean(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("1 + 2" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(2), AssocOp::Add))]
    #[test_case("(1 * 3)" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(3), AssocOp::Multiply))]
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

    #[test]
    fn parse_complex_str() {
        let result = parse_expr("\"te sΓé¼t\tt ab\"");
        assert_eq!(result, Ok(Expr::Str("te sΓé¼t\tt ab".to_string())));
    }

    #[test_case("1" => Expr::Num(dec!(1)))]
    #[test_case("1.2" => Expr::Num(dec!(1.2)))]
    #[test_case("-0.42" => Expr::Num(dec!(-0.42)))]
    #[test_case("(3.14)" => Expr::Num(dec!(3.14)))]
    #[test_case("(((42)))" => Expr::Num(dec!(42)))]
    fn parse_num(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("null" => Expr::Null)]
    fn parse_null(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("a" => Expr::Identifier("a".to_string()))]
    #[test_case("(b)" => Expr::Identifier("b".to_string()))]
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
    #[test_case("([3,4])" => Expr::Array(vec![rc_expr_num!(3), rc_expr_num!(4)]))]
    fn parse_array(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test(1,2)" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(2)]))]
    #[test_case("(test( ( 3 ), (4)))" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(3), rc_expr_num!(4)]))]
    #[test_case("test ( 1 , 42 )" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(42)]))]
    #[test_case("test()" => Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))] // to debug
    #[test_case("test((test()))" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))]))] // to debug
    #[test_case("test(aa)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Identifier("aa".to_string()))]))]
    #[test_case("Test(42)" => Expr::FunctionCall("Test".to_string(), vec![Rc::new(Expr::Num(dec!(42)))]))]
    fn parse_function_call(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test([\"value\", (42), null],2, \"null\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Array(vec![rc_expr_str!("value".to_string()), rc_expr_num!(42), rc_expr_null!()])), rc_expr_num!(2), rc_expr_str!("null".to_string())]))]
    #[test_case("hello" => Expr::Identifier("hello".to_string()))]
    #[test_case(" _hella " => Expr::Identifier("_hella".to_string()))]
    #[test_case(" helloworld " => Expr::Identifier("helloworld".to_string()))]
    #[test_case("test(\"value\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("value")]))]
    #[test_case("test(\"va lue\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")]))]
    #[test_case("test(\"va lue\") - 3" => Expr::BinaryOperator(RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), rc_expr_num!(3), AssocOp::Subtract))]
    #[test_case("42 / test(\"va lue\")" => Expr::BinaryOperator(rc_expr_num!(42), RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), AssocOp::Divide))]
    #[test_case("42 \r\n \t / func()" => Expr::BinaryOperator(rc_expr_num!(42), RcExpr::new( Expr::FunctionCall("func".to_string(), vec![])), AssocOp::Divide))]
    #[test_case("(43 \r\n \t / ( func() ) )" => Expr::BinaryOperator(rc_expr_num!(43), RcExpr::new( Expr::FunctionCall("func".to_string(), vec![])), AssocOp::Divide))]
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

    #[test]
    fn parse_insane_recursive_expressions() {
        for complexity in 1..10 {
            let mut expression = String::new();
            for i in 0..complexity {
                expression.push_str("Funk(true, 0, ");
                if i == complexity - 1 {
                    expression.push_str("42");
                }
            }
            for _ in 0..complexity {
                expression.push_str(")");
            }
            let now = Instant::now();
            let expr = expr::<(&str, ErrorKind)>(&expression);
            let (rest, _) = expr.unwrap();
            assert_eq!(rest.len(), 0);
            dbg!(complexity, &expression, now.elapsed());
        }
    }

    #[test]
    fn parse_insane_long_expressions() {
        for complexity in 1..100 {
            let mut expression = String::new();
            for i in 0..complexity {
                if i != 0 {
                    expression.push_str(" + ");
                }
                expression.push_str("Funk(true, 0, \"42\")");
            }
            let _now = Instant::now();
            let expr = expr::<(&str, ErrorKind)>(&expression);
            let (rest, _) = expr.unwrap();
            assert_eq!(rest.len(), 0);
            // dbg!(complexity, &expression, _now.elapsed());
        }
    }
}
