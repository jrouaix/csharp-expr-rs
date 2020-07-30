use crate::expressions::*;
use nom::error::ErrorKind;
use std::cell::RefCell;

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

enum Lex {
    ParenthesisOpen,
    ParenthesisClose,
    Comma,
    Identifier(String),
    Expr(crate::expressions::Expr),
    Op(crate::expressions::AssocOp),
}

/// A nom parser has the following signature:
/// `Input -> IResult<Input, Output, Error>`, with `IResult` defined as:
/// `type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;`

// string parser from here : https://github.com/Geal/nom/issues/1075
fn string<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    context(
        "string",
        delimited(
            char('\"'),
            cut(map(
                opt(escaped(
                    take_while1(|c| c != '\\' && c != '"'),
                    '\\',
                    one_of("\"\\/bfnrtu"), // Note, this will not detect invalid unicode escapes.
                )),
                |o| o.unwrap_or_default(),
            )),
            char('\"'),
        ),
    )(input)
}

/// boolean combinator
fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    context("boolean", alt((map(tag("false"), |_| false), map(tag("true"), |_| true))))(input)
}

/// null combinator
fn null<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = tag("null")(input)?;
    Ok((input, Expr::Null))
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric1))))(input)
}

// fn simple<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
//     let (input, _) = multispace0(input)?;
//     let (input, expr) = alt((
//         map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap())),
//         null,
//         map(boolean, Expr::Boolean),
//         map_opt(string, |s| unescape(s).map(Expr::Str)),
//     ))(input)?;
// }

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
                map(tag("<="), |_| AssocOp::LessEqual),
                map(tag("<"), |_| AssocOp::Less),
                map(tag(">="), |_| AssocOp::GreaterEqual),
                map(tag(">"), |_| AssocOp::Greater),
                map(tag("/"), |_| AssocOp::Divide),
                map(tag("=="), |_| AssocOp::Equal),
                map(tag("!="), |_| AssocOp::NotEqual),
                map(tag("%"), |_| AssocOp::Modulus),
                map(tag("&&"), |_| AssocOp::LAnd),
                map(tag("||"), |_| AssocOp::LOr),
            )),
            multispace0,
        ),
    )(input)
}

fn open_parenthesis<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lex, E> {
    let (input, _) = char('(')(input)?;
    Ok((input, Lex::ParenthesisOpen))
}
fn close_parenthesis<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lex, E> {
    let (input, _) = char(')')(input)?;
    Ok((input, Lex::ParenthesisClose))
}
fn comma<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lex, E> {
    let (input, _) = char(',')(input)?;
    Ok((input, Lex::Comma))
}

fn lexer<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lex, E> {
    alt((
        open_parenthesis,
        close_parenthesis,
        comma,
        map(binary_operator, |op| Lex::Op(op)),
        map(identifier, |id| Lex::Identifier(id.into())),
        map(null, |_| Lex::Expr(Expr::Null)),
        map(boolean, |b| Lex::Expr(Expr::Boolean(b))),
        map(double, |d| Lex::Expr(Expr::Num(FromPrimitive::from_f64(d).unwrap()))),
        map(string, |s| Lex::Expr(Expr::Str(s.into()))),
    ))(input)
}

#[derive(Debug)]
struct ParserMachine {
    parsers: Vec<Parser>,
}

impl ParserMachine {
    fn new() -> ParserMachine {
        ParserMachine {
            parsers: vec![ParserMachine::new_parser()],
        }
    }
    fn new_parser() -> Parser {
        Parser { state: ParsingState::Started }
    }

    fn current_parser<'a>(&'a mut self) -> &'a mut Parser {
        let last_position = self.parsers.len() - 1;
        self.parsers.get_mut(last_position).unwrap()
    }

    fn open_parenthesis(&mut self) {
        let current = self.current_parser();
        match &current.state {
            ParsingState::Identifier(s) => current.state = ParsingState::Function(s.clone(), RefCell::new(vec![]), false),
            _ => self.parsers.push(ParserMachine::new_parser()),
        }
    }

    fn identifier(&mut self, name: String) {
        let current = self.current_parser();
        match &current.state {
            ParsingState::Started => {
                current.state = ParsingState::Identifier(name);
            }
            _ => todo!(), // Unable to handle an identifier here
        }
    }

    fn comma(&mut self) {
        let current = self.current_parser();
        match &current.state {
            ParsingState::Function(s, p, false) => {
                current.state = ParsingState::Function(s.clone(), p.clone(), true);
            }
            _ => todo!(), // Unable to handle a comma ',' here
        }
    }

    fn expression(&mut self, expr: Expr) {
        let current = self.current_parser();
        match &current.state {
            ParsingState::Function(s, p, true) => {
                p.borrow_mut().push(RcExpr::new(expr));
                current.state = ParsingState::Function(s.clone(), p.clone(), true);
            }
            ParsingState::AwaitingNextOperand(e, op) => {
                current.state = ParsingState::Expr(Expr::BinaryOperator(RcExpr::new(e.clone()), RcExpr::new(expr), op.clone()));
            }
            ParsingState::Started => {
                current.state = ParsingState::Expr(expr);
            }
            _ => todo!(), // Unable to handle an expression here
        }
    }

    fn operator(&mut self, op: AssocOp) {
        let current = self.current_parser();
        match &current.state {
            ParsingState::Expr(e) => current.state = ParsingState::AwaitingNextOperand(e.clone(), op),
            _ => todo!(), // Unable to add an operator here
        };
    }

    fn close_parenthesis(&mut self) {
        let mut current = self.parsers.pop().unwrap();
        if let ParsingState::Function(s, p, _) = current.state {
            // let's be permisive on writing some more comma like func(1,2,3,)
            let parameters = p.clone().into_inner();
            current.state = ParsingState::Expr(Expr::FunctionCall(s.clone(), parameters));
            self.parsers.push(current);
            return;
        }

        let current = self.parsers.pop().unwrap();
        if let ParsingState::Expr(expr) = current.state {
            self.expression(expr.clone());
        }
    }

    fn finalize(mut self) -> Expr {
        if self.parsers.len() != 1 {
            todo!();
        }

        let result = self.parsers.pop().unwrap();

        match result.state {
            ParsingState::Expr(e) => e,
            _ => todo!(), // Missing something
        }
    }
}

#[derive(Debug)]
struct Parser {
    state: ParsingState,
}

#[derive(Debug)]
enum ParsingState {
    Started,
    Identifier(String),
    Expr(Expr),
    AwaitingNextOperand(Expr, AssocOp),
    Function(String, RefCell<VecRcExpr>, bool),
}

fn parser<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let mut machine = ParserMachine::new();

    let (input, _) = multispace0(input)?;
    let mut input = input;
    while input.len() != 0 {
        let (i, lex) = lexer(input)?;
        match lex {
            Lex::ParenthesisOpen => machine.open_parenthesis(),
            Lex::ParenthesisClose => machine.close_parenthesis(),
            Lex::Expr(e) => machine.expression(e),
            Lex::Op(op) => machine.operator(op),
            Lex::Comma => machine.comma(),
            Lex::Identifier(s) => machine.identifier(s),
        }
        let (i, _) = multispace0(i)?;
        input = i;
    }

    Ok((input, machine.finalize()))
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    parser(input)
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use nom::error::ErrorKind;
//     use rust_decimal_macros::*;
//     use std::time::Instant;
//     use test_case::test_case;

//     macro_rules! rc_expr_str {
//         ( $x:expr ) => {
//             Rc::new(Expr::Str($x.to_string()))
//         };
//     }
//     macro_rules! rc_expr_num {
//         ( $x:expr ) => {
//             Rc::new(Expr::Num(dec!($x)))
//         };
//     }
//     macro_rules! rc_expr_null {
//         () => {
//             Rc::new(Expr::Null)
//         };
//     }

//     #[test_case("+", AssocOp::Add)]
//     #[test_case("- ", AssocOp::Subtract)]
//     #[test_case(" /", AssocOp::Divide)]
//     #[test_case(" && ", AssocOp::LAnd)]
//     fn binary_operator_test(text: &str, expected: AssocOp) {
//         let result = binary_operator::<(&str, ErrorKind)>(text);
//         assert_eq!(result, Ok(("", expected)));
//     }

//     #[test_case("1+2", (Expr::Num(dec!(1)), Expr::Num(dec!(2)), AssocOp::Add))]
//     // #[test_case("(3)+(4)", (Expr::Num(dec!(3)), Expr::Num(dec!(4)), AssocOp::Add))]
//     #[test_case(" 3- 2 ", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Subtract))]
//     #[test_case(" 3 /2", (Expr::Num(dec!(3)), Expr::Num(dec!(2)), AssocOp::Divide))]
//     #[test_case("3|| 5 ", (Expr::Num(dec!(3)), Expr::Num(dec!(5)), AssocOp::LOr))]
//     #[test_case("5 * 5", (Expr::Num(dec!(5)), Expr::Num(dec!(5)), AssocOp::Multiply))]
//     #[test_case(" 42 % \"2\"", (Expr::Num(dec!(42)), Expr::Str("2".to_string()), AssocOp::Modulus))]
//     #[test_case("2 == 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Equal))]
//     #[test_case("2 > 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Greater))]
//     #[test_case("2 < 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::Less))]
//     #[test_case("2 >= 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::GreaterEqual))]
//     #[test_case("2 <= 2", (Expr::Num(dec!(2)), Expr::Num(dec!(2)), AssocOp::LessEqual))]
//     #[test_case("true && false", (Expr::Boolean(true), Expr::Boolean(false), AssocOp::LAnd))]
//     #[test_case("false || true", (Expr::Boolean(false), Expr::Boolean(true), AssocOp::LOr))]
//     fn binary_operations_test(text: &str, expected: (Expr, Expr, AssocOp)) {
//         let result = main_parser::<(&str, ErrorKind)>(text);
//         let (left, right, op) = expected;
//         assert_eq!(result, Ok(("", Expr::BinaryOperator(RcExpr::new(left), RcExpr::new(right), op))));
//     }

//     #[test_case("test()", Expr::FunctionCall("test".to_string(), VecRcExpr::new()))]
//     #[test_case(" toto () ", Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]
//     #[test_case(" toto (toto()) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]))]
//     // #[test_case("toto((null - null)) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::BinaryOperator( RcExpr::new(Expr::Null),RcExpr::new(Expr::Null), AssocOp::Subtract))]))]
//     #[test_case("tata(null - null) ", Expr::FunctionCall("tata".to_string(), vec![RcExpr::new(Expr::BinaryOperator( RcExpr::new(Expr::Null),RcExpr::new(Expr::Null), AssocOp::Subtract))]))]
//     fn parse_some_expr(text: &str, expected: Expr) {
//         let result = parse_expr(text).unwrap();
//         assert_eq!(result, expected);
//     }

//     #[test]
//     fn binary_operation_parenthesis_test() {
//         let expected = Ok((
//             "",
//             Expr::BinaryOperator(
//                 RcExpr::new(Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(3))), RcExpr::new(Expr::Num(dec!(5))), AssocOp::Divide)),
//                 RcExpr::new(Expr::Str("2".to_string())),
//                 AssocOp::Subtract,
//             ),
//         ));
//         assert_eq!(main_parser::<(&str, ErrorKind)>("3 / 5-\"2\""), expected);
//         assert_eq!(main_parser::<(&str, ErrorKind)>("(3) / (5) -(\"2\")"), expected);
//         // assert_eq!(main_parser::<(&str, ErrorKind)>("(3 / 5-\"2\")"), expected);
//     }

//     #[test_case("true" => Expr::Boolean(true))]
//     #[test_case("false" => Expr::Boolean(false))]
//     fn parse_boolean(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     #[test_case("1 + 2" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(2), AssocOp::Add))]
//     #[test_case("(4) + (2)" => Expr::BinaryOperator(rc_expr_num!(4), rc_expr_num!(2), AssocOp::Add))]
//     #[test_case("(1 * 3)" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(3), AssocOp::Multiply))]
//     fn parse_binary_operator(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     #[test]
//     fn parse_empty_string() {
//         let expr = parse_expr("\"\"").unwrap();
//         assert_eq!(expr, Expr::Str("".to_string()))
//     }

//     #[test]
//     fn parse_string_with_doublequote() -> Result<(), String> {
//         let expression = "\" \\\" \"";
//         let expected = " \" ";
//         let result = parse_expr(expression)?;
//         println!("'{}' => '{}'", expression, result.to_string());
//         assert_eq!(result, Expr::Str(expected.to_string()));
//         Ok(())
//     }

//     #[test]
//     fn parse_simple() {
//         assert_eq!(simple::<(&str, ErrorKind)>("true"), Ok(("", Expr::Boolean(true))));
//         assert_eq!(simple::<(&str, ErrorKind)>("2"), Ok(("", Expr::Num(dec!(2)))));
//         assert_eq!(simple::<(&str, ErrorKind)>("(true)"), Ok(("", Expr::Boolean(true))));
//         assert_eq!(simple::<(&str, ErrorKind)>("(-2)"), Ok(("", Expr::Num(dec!(-2)))));
//         assert_eq!(simple::<(&str, ErrorKind)>("true)"), Ok((")", Expr::Boolean(true))));
//         assert_eq!(simple::<(&str, ErrorKind)>("(true"), Err(nom::Err::Error(("", ErrorKind::Char))));
//         assert_eq!(simple::<(&str, ErrorKind)>("2 ,"), Ok((",", Expr::Num(dec!(2)))));
//         assert_eq!(simple::<(&str, ErrorKind)>("(2) ,"), Ok((" ,", Expr::Num(dec!(2)))));
//     }

//     #[test]
//     fn parse_identifier_or_function_call() {
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("true"), Ok(("", Expr::Identifier("true".into()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("(true)"), Ok(("", Expr::Identifier("true".into()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("( true )"), Ok(("", Expr::Identifier("true".into()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("( _id )"), Ok(("", Expr::Identifier("_id".into()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("( id ( ) )"), Ok(("", Expr::FunctionCall("id".into(), vec!()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("_id()"), Ok(("", Expr::FunctionCall("_id".into(), vec!()))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("_id()toto"), Ok(("toto", Expr::FunctionCall("_id".into(), vec!()))));
//         assert_eq!(
//             identifier_or_function_call::<(&str, ErrorKind)>("_id(1,2)"),
//             Ok(("", Expr::FunctionCall("_id".into(), vec![rc_expr_num!(1), rc_expr_num!(2)])))
//         );
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("_id( a , b"), Err(nom::Err::Error(("", ErrorKind::Char))));
//         assert_eq!(identifier_or_function_call::<(&str, ErrorKind)>("id("), Err(nom::Err::Error(("", ErrorKind::Char))));
//     }

//     #[test_case(stringify!("null") => "null")]
//     #[test_case(stringify!("test") => "test")]
//     #[test_case(stringify!("t") => "t")]
//     #[test_case(stringify!("test\"doublequote") => "test\"doublequote")]
//     #[test_case(stringify!("test\\slash") => "test\\slash")]
//     #[test_case(stringify!("test\newline") => "test\newline")]
//     #[test_case(stringify!("test\ttab") => "test\ttab")]
//     #[test_case(stringify!("test\rreturn") => "test\rreturn")]
//     #[test_case(stringify!("test escape") => "test escape")]
//     #[test_case("\"test escape\"" => "test escape")]
//     #[test_case("\"test\ttab\"" => "test\ttab")]
//     fn parse_str(expression: &str) -> String {
//         let result = parse_expr(expression);
//         println!("{:?}", result);
//         let expr = result.unwrap();
//         if let Expr::Str(result) = expr {
//             result
//         } else {
//             panic!("{:?}", expr)
//         }
//     }

//     #[test]
//     fn parse_complex_str() {
//         let result = parse_expr("\"te sΓé¼t\tt ab\"");
//         assert_eq!(result, Ok(Expr::Str("te sΓé¼t\tt ab".to_string())));
//     }

//     #[test_case("1" => Expr::Num(dec!(1)))]
//     #[test_case("1.2" => Expr::Num(dec!(1.2)))]
//     #[test_case("-0.42" => Expr::Num(dec!(-0.42)))]
//     #[test_case("(3.14)" => Expr::Num(dec!(3.14)))]
//     #[test_case("(((42)))" => Expr::Num(dec!(42)))]
//     fn parse_num(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     #[test_case("null" => Expr::Null)]
//     fn parse_null(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     #[test_case("a" => Expr::Identifier("a".to_string()))]
//     #[test_case("(b)" => Expr::Identifier("b".to_string()))]
//     #[test_case("id" => Expr::Identifier("id".to_string()))]
//     #[test_case(" hello " => Expr::Identifier("hello".to_string()))]
//     #[test_case("@idarobase" => Expr::Identifier("idarobase".to_string()))]
//     // #[test_case("id_id" => Expr::Identifier("id_id".to_string()))] // to debug
//     #[test_case("id42" => Expr::Identifier("id42".to_string()))]
//     #[test_case("_id0" => Expr::Identifier("_id0".to_string()))]
//     #[test_case("_id1" => Expr::Identifier("_id1".to_string()))]
//     fn parse_identifier(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     // #[test_case("[1,2]" => Expr::Array(vec![rc_expr_num!(1), rc_expr_num!(2)]))]
//     // #[test_case("([3,4])" => Expr::Array(vec![rc_expr_num!(3), rc_expr_num!(4)]))]
//     // fn parse_array(expression: &str) -> Expr {
//     //     parse_expr(expression).unwrap()
//     // }

//     #[test_case("test(1,2)" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(2)]))]
//     #[test_case("(test( ( 3 ), (4)))" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(3), rc_expr_num!(4)]))]
//     #[test_case("test ( 1 , 42 )" => Expr::FunctionCall("test".to_string(), vec![rc_expr_num!(1), rc_expr_num!(42)]))]
//     #[test_case("test()" => Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))] // to debug
//     #[test_case("test((test()))" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))]))] // to debug
//     #[test_case("test(aa)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Identifier("aa".to_string()))]))]
//     #[test_case("Test(42)" => Expr::FunctionCall("Test".to_string(), vec![Rc::new(Expr::Num(dec!(42)))]))]
//     fn parse_function_call(expression: &str) -> Expr {
//         parse_expr(expression).unwrap()
//     }

//     #[test_case("test([\"value\", (42), null],2, \"null\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Array(vec![rc_expr_str!("value".to_string()), rc_expr_num!(42), rc_expr_null!()])), rc_expr_num!(2), rc_expr_str!("null".to_string())]))]
//     #[test_case("hello" => Expr::Identifier("hello".to_string()))]
//     #[test_case(" _hella " => Expr::Identifier("_hella".to_string()))]
//     #[test_case(" helloworld " => Expr::Identifier("helloworld".to_string()))]
//     #[test_case("test(\"value\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("value")]))]
//     #[test_case("test(\"va lue\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")]))]
//     #[test_case("test(\"va lue\") - 3" => Expr::BinaryOperator(RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), rc_expr_num!(3), AssocOp::Subtract))]
//     #[test_case("42 / test(\"va lue\")" => Expr::BinaryOperator(rc_expr_num!(42), RcExpr::new( Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("va lue")])), AssocOp::Divide))]
//     #[test_case("42 \r\n \t / func()" => Expr::BinaryOperator(rc_expr_num!(42), RcExpr::new( Expr::FunctionCall("func".to_string(), vec![])), AssocOp::Divide))]
//     #[test_case("(43 \r\n \t / ( func() ) )" => Expr::BinaryOperator(rc_expr_num!(43), RcExpr::new( Expr::FunctionCall("func".to_string(), vec![])), AssocOp::Divide))]
//     fn parse_complexe_expressions(expression: &'static str) -> Expr {
//         let expr = expr::<(&str, ErrorKind)>(expression);
//         match expr {
//             Ok((rest, expr)) => match rest.len() {
//                 0 => expr,
//                 _ => {
//                     dbg!(expr);
//                     panic!(rest)
//                 }
//             },
//             Err(err_kind) => panic!(format!("{:?}", err_kind)),
//         }
//     }

//     #[test]
//     fn parse_insane_recursive_expressions() {
//         for complexity in 1..10 {
//             let mut expression = String::new();
//             for i in 0..complexity {
//                 expression.push_str("Funk(true, 0, ");
//                 if i == complexity - 1 {
//                     expression.push_str("42");
//                 }
//             }
//             for _ in 0..complexity {
//                 expression.push_str(")");
//             }
//             let now = Instant::now();
//             let expr = expr::<(&str, ErrorKind)>(&expression);
//             let (rest, _) = expr.unwrap();
//             assert_eq!(rest.len(), 0);
//             dbg!(complexity, &expression, now.elapsed());
//         }
//     }

//     #[test]
//     fn parse_insane_long_expressions() {
//         for complexity in 1..100 {
//             let mut expression = String::new();
//             for i in 0..complexity {
//                 if i != 0 {
//                     expression.push_str(" + ");
//                 }
//                 expression.push_str("Funk(true, 0, \"42\")");
//             }
//             let _now = Instant::now();
//             let expr = expr::<(&str, ErrorKind)>(&expression);
//             let (rest, _) = expr.unwrap();
//             assert_eq!(rest.len(), 0);
//             // dbg!(complexity, &expression, _now.elapsed());
//         }
//     }
// }
