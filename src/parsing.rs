use crate::expressions::*;

use nom::{
    branch::alt,
    bytes::complete::{escaped, tag, take_while1}, // escaped_transform
    character::complete::{alphanumeric1, char, multispace0, one_of},
    combinator::{map, opt, recognize},
    error::{context, ParseError},
    number::complete::double,
    sequence::{delimited, preceded, tuple},
    IResult,
};
use rust_decimal::prelude::FromPrimitive;
use std::cell::RefCell;
use unescape::unescape;

#[derive(Debug)]
enum Lex {
    ParenthesisOpen,
    ParenthesisClose,
    Comma,
    FunctionOpen(String),
    Expr(crate::expressions::Expr),
    Op(crate::expressions::AssocOp),
}

/// A nom parser has the following signature:
/// `Input -> IResult<Input, Output, Error>`, with `IResult` defined as:
/// `type IResult<I, O, E = (I, ErrorKind)> = Result<(I, O), Err<E>>;`

// string parser from here : https://github.com/Geal/nom/issues/1075
fn string<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    delimited(
        char('\"'),
        map(
            opt(escaped(
                take_while1(|c| c != '\\' && c != '"'),
                '\\',
                one_of("\\\""), // Note, this will not detect invalid unicode escapes.
            )),
            |o| o.unwrap_or_default(),
        ),
        char('\"'),
    )(input)
}

// // string parser from here : https://github.com/Geal/nom/issues/1075
// fn parse_str<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     // dbg!("parse_str", input);
//     escaped(
//         take_while1(|c| c != '\\' && c != '"'),
//         '\\',
//         one_of("\"\\/bfnrtu"), // Note, this will not detect invalid unicode escapes.
//     )(input)
// }

// fn string<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
//     // dbg!("string", input);
//     context("string", delimited(char('\"'), cut(map(opt(parse_str), |o| o.unwrap_or_default())), char('\"')))(input)
// }

fn boolean<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, bool, E> {
    context("boolean", alt((map(tag("false"), |_| false), map(tag("true"), |_| true))))(input)
}

fn null<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let (input, _) = tag("null")(input)?;
    Ok((input, Expr::Null))
}

fn identifier<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    preceded(opt(tag("@")), recognize(tuple((opt(tag("_")), alphanumeric1))))(input)
}

fn binary_operator<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, AssocOp, E> {
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
    ))(input)
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

fn open_function<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, &'a str, E> {
    let (input, name) = identifier(input)?;
    let (input, _) = multispace0(input)?;
    let (input, _) = open_parenthesis(input)?;
    Ok((input, name))
}

fn full_lexer<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Lex, E> {
    alt((
        open_parenthesis,
        close_parenthesis,
        comma,
        map(binary_operator, |op| Lex::Op(op)),
        map(string, |s| Lex::Expr(Expr::Str(unescape(s).unwrap()))),
        map(null, |_| Lex::Expr(Expr::Null)),
        map(boolean, |b| Lex::Expr(Expr::Boolean(b))),
        map(double, |d| Lex::Expr(Expr::Num(FromPrimitive::from_f64(d).unwrap()))),
        map(open_function, |id| Lex::FunctionOpen(id.into())),
        map(identifier, |id| Lex::Expr(Expr::Identifier(id.into()))),
    ))(input)
}

fn second_chance_lexer<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    map(double, |d| Expr::Num(FromPrimitive::from_f64(d).unwrap()))(input)
}

#[derive(Debug)]
struct ParserMachine {
    parsers: Vec<Parser>,
}

enum OperatorParseTryResult {
    Ok,
    ShouldBeANumber,
}

impl ParserMachine {
    fn new() -> ParserMachine {
        let mut machine = ParserMachine { parsers: vec![] };
        machine.push_parser();
        machine
    }

    fn push_parser(&mut self) {
        self.parsers.push(Parser { state: ParsingState::Started });
    }

    fn current_parser_state<'a>(&'a mut self) -> &'a ParsingState {
        let len = self.parsers.len();
        &(if len == 0 {
            self.push_parser();
            self.parsers.get_mut(0).unwrap()
        } else {
            let last_position = len - 1;
            self.parsers.get_mut(last_position).unwrap()
        })
        .state
    }

    fn current_parser_mut<'a>(&'a mut self) -> &'a mut Parser {
        let len = self.parsers.len();
        if len == 0 {
            self.push_parser();
            self.parsers.get_mut(0).unwrap()
        } else {
            let last_position = len - 1;
            self.parsers.get_mut(last_position).unwrap()
        }
    }

    fn current_parser_read<'a>(&'a mut self) -> &'a Parser {
        let len = self.parsers.len();
        if len == 0 {
            self.push_parser();
            self.parsers.get_mut(0).unwrap()
        } else {
            let last_position = len - 1;
            self.parsers.get_mut(last_position).unwrap()
        }
    }

    fn open_parenthesis(&mut self) {
        self.push_parser()
    }

    fn open_function(&mut self, name: String) {
        let current = self.current_parser_mut();

        let next_state = ParsingState::Function(name.clone(), RefCell::new(vec![]), false);
        if let ParsingState::Started = &current.state {
            current.state = next_state;
            // self.push_parser(); //???????????????????????????????????????????? TESTS!!!
            return;
        }

        if let ParsingState::Expr(_) = &current.state {
            dbg!(current);
            todo!("Unable to handle a function openning here")
        }

        self.push_parser();
        let current = self.current_parser_mut();
        current.state = next_state;
    }

    fn comma(&mut self) {
        let current = self.current_parser_mut();
        match &current.state {
            ParsingState::Function(s, p, false) => {
                current.state = ParsingState::Function(s.clone(), p.clone(), true);
            }
            _ => {
                dbg!(current);
                todo!("Unable to handle a comma ',' here")
            }
        }
    }

    fn expression(&mut self, expr: RcExpr) {
        let current = self.current_parser_mut();
        match &current.state {
            ParsingState::Function(s, p, has_comma) => {
                let parameters = p.clone().into_inner();
                if !has_comma && parameters.len() != 0 {
                    todo!("There should be a comma to separate arguments")
                }
                p.borrow_mut().push(expr);
                current.state = ParsingState::Function(s.clone(), p.clone(), false);
            }
            ParsingState::AwaitingNextOperand(e, op) => {
                current.state = ParsingState::Expr(RcExpr::new(Expr::BinaryOperator(e.clone(), expr, op.clone())));
                // todo!("Resolve current parser to Expr")
            }
            ParsingState::Started => {
                current.state = ParsingState::Expr(expr);
            }
            _ => {
                dbg!(current);
                todo!("Unable to handle an expression here")
            }
        }
    }

    fn operator(&mut self, op: AssocOp) -> OperatorParseTryResult {
        let current = self.current_parser_mut();
        let expr_to_add = match &current.state {
            ParsingState::Expr(e) => {
                current.state = ParsingState::AwaitingNextOperand(e.clone(), op);
                return OperatorParseTryResult::Ok;
            }
            ParsingState::Function(_, p, false) => {
                let mut parameters = p.borrow_mut();
                if parameters.len() == 0 {
                    return OperatorParseTryResult::ShouldBeANumber;
                } else {
                    let expr = parameters.pop().unwrap();
                    expr
                }
            }
            _ => return OperatorParseTryResult::ShouldBeANumber,
        };

        self.push_parser();
        self.expression(expr_to_add);
        self.operator(op);
        OperatorParseTryResult::Ok
    }

    fn close_parenthesis(&mut self) {
        let current = self.parsers.pop().unwrap();
        if let ParsingState::Function(s, p, _) = current.state {
            // let's be permisive on writing some more comma like func(1,2,3,)
            let parameters = p.clone().into_inner();
            self.expression(RcExpr::new(Expr::FunctionCall(s.clone(), parameters)));
            return;
        }

        // let current = self.parsers.pop().unwrap();
        if let ParsingState::Expr(expr) = current.state {
            self.expression(expr.clone());
            return;
        }

        dbg!(self);
        todo!("Unable to close any parenthesis here")
    }

    fn finalize(mut self) -> Expr {
        if self.parsers.len() == 0 {
            dbg!(&self);
            todo!("There should be at least one expression deep");
        }

        while self.parsers.len() != 1 {
            let parser = self.parsers.pop().unwrap();
            let expr = parser.finalize();
            self.expression(expr);
        }

        RcExpr::try_unwrap(self.parsers.pop().unwrap().finalize()).unwrap()
    }
}

#[derive(Debug)]
struct Parser {
    state: ParsingState,
}

#[derive(Debug)]
enum ParsingState {
    Started,
    // Identifier(String),
    Expr(RcExpr),
    AwaitingNextOperand(RcExpr, AssocOp),
    Function(String, RefCell<VecRcExpr>, bool),
}

impl Parser {
    fn finalize(self) -> RcExpr {
        match self.state {
            ParsingState::Expr(e) => e,
            ParsingState::Function(s, p, _) => {
                // let's be permisive on writing some more comma like func(1,2,3,)
                let parameters = p.clone().into_inner();
                RcExpr::new(Expr::FunctionCall(s.clone(), parameters))
            }
            _ => todo!("Cannot finalize parser in this state"),
        }
    }
}

fn parser<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    let mut machine = ParserMachine::new();

    let (input, _) = multispace0(input)?;
    let mut input = input;
    while input.len() != 0 {
        let (i, lex) = full_lexer(input)?;
        let mut i = i;
        match lex {
            Lex::ParenthesisOpen => machine.open_parenthesis(),
            Lex::ParenthesisClose => machine.close_parenthesis(),
            Lex::Expr(e) => machine.expression(RcExpr::new(e)),
            Lex::Op(op) => {
                if let OperatorParseTryResult::ShouldBeANumber = machine.operator(op) {
                    let (i2, expr) = second_chance_lexer(input)?;
                    machine.expression(RcExpr::new(expr));
                    i = i2;
                }
            }
            Lex::Comma => machine.comma(),
            Lex::FunctionOpen(s) => machine.open_function(s),
        }
        let (i, _) = multispace0(i)?;
        input = i;
    }

    Ok((input, machine.finalize()))
}

pub fn expr<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Expr, E> {
    parser(input)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nom::error::ErrorKind;
    use rust_decimal_macros::*;
    use std::rc::Rc;
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

    #[test_case("+", AssocOp::Add)]
    #[test_case("-", AssocOp::Subtract)]
    #[test_case("/", AssocOp::Divide)]
    #[test_case("&&", AssocOp::LAnd)]
    fn binary_operator_test(text: &str, expected: AssocOp) {
        let result = binary_operator::<(&str, ErrorKind)>(text);
        assert_eq!(result, Ok(("", expected)));
    }

    #[test_case(stringify!("null") => "null")]
    #[test_case(stringify!("test") => "test")]
    #[test_case(stringify!("t") => "t")]
    #[test_case("\"test escape\"" => "test escape")]
    #[test_case(stringify!("test escape") => "test escape")]
    #[test_case(stringify!("test\"doublequote") => "test\"doublequote")]
    #[test_case(stringify!("test\\slash") => "test\\slash")]
    #[test_case("\"test\nnewline\"" => "test\nnewline")]
    #[test_case("\"test\ttab\"" => "test\ttab")]
    #[test_case("\"test\rreturn\"" => "test\rreturn")]
    fn string_parser_tests(text: &str) -> String {
        let (i, result) = full_lexer::<(&str, ErrorKind)>(text).unwrap();
        if i.len() != 0 {
            dbg!(i, &result);
            assert_eq!(i.len(), 0);
        }
        if let Lex::Expr(Expr::Str(s)) = result {
            s.clone()
        } else {
            dbg!(&result);
            panic!("Should be a Lex::Expr(Expr::Str())");
        }
    }

    #[test_case("1+2")]
    fn parser_machine_test(expression: &str) {
        super_show(expression);
    }

    fn super_show(expression: &str) {
        let (input, lexed) = get_lexed::<(&str, ErrorKind)>(expression).unwrap();
        dbg!(&lexed);
        // assert_eq!(input.len(), 0);

        // let mut machine = ParserMachine::new();
        // for lex in lexed {
        //     dbg!(&lex);
        //     machine.lex(lex);
        //     dbg!(&machine);
        // }

        // machine.finalize();
    }

    fn get_lexed<'a, E: ParseError<&'a str>>(input: &'a str) -> IResult<&'a str, Vec<Lex>, E> {
        let mut lexed = vec![];
        let (input, _) = multispace0(input)?;
        let mut input = input;
        while input.len() != 0 {
            let (i, lex) = full_lexer(input)?;
            dbg!(&lex);
            lexed.push(lex);
            let (i, _) = multispace0(i)?;
            input = i;
        }
        Ok((input, lexed))
    }

    #[test_case("1+2", (Expr::Num(dec!(1)), Expr::Num(dec!(2)), AssocOp::Add))]
    #[test_case("(3)+(4)", (Expr::Num(dec!(3)), Expr::Num(dec!(4)), AssocOp::Add))]
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
        let result = parser::<(&str, ErrorKind)>(text);
        let (left, right, op) = expected;
        assert_eq!(result, Ok(("", Expr::BinaryOperator(RcExpr::new(left), RcExpr::new(right), op))));
    }

    #[test_case("test()", Expr::FunctionCall("test".to_string(), VecRcExpr::new()))]
    #[test_case(" toto () ", Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]
    #[test_case(" toto (toto()) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::FunctionCall("toto".to_string(), VecRcExpr::new()))]))]
    #[test_case("toto((null - null)) ", Expr::FunctionCall("toto".to_string(), vec![RcExpr::new(Expr::BinaryOperator( RcExpr::new(Expr::Null),RcExpr::new(Expr::Null), AssocOp::Subtract))]))]
    #[test_case("(null - null) ", Expr::BinaryOperator(RcExpr::new(Expr::Null), RcExpr::new(Expr::Null), AssocOp::Subtract))]
    #[test_case("2 - null ", Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(2))), RcExpr::new(Expr::Null), AssocOp::Subtract))]
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
        assert_eq!(parser::<(&str, ErrorKind)>("3 / 5-\"2\""), expected);
        assert_eq!(parser::<(&str, ErrorKind)>("(3) / (5) -(\"2\")"), expected);
        assert_eq!(parser::<(&str, ErrorKind)>("(3 / 5-\"2\")"), expected);
    }

    #[test_case("true" => Expr::Boolean(true))]
    #[test_case("false" => Expr::Boolean(false))]
    fn parse_boolean(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("1 + 2" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(2), AssocOp::Add))]
    #[test_case("(4) + (2)" => Expr::BinaryOperator(rc_expr_num!(4), rc_expr_num!(2), AssocOp::Add))]
    #[test_case("(1 * 3)" => Expr::BinaryOperator(rc_expr_num!(1), rc_expr_num!(3), AssocOp::Multiply))]
    fn parse_binary_operator(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test]
    fn parse_empty_string() {
        let expr = parse_expr("\"\"").unwrap();
        assert_eq!(expr, Expr::Str("".to_string()))
    }

    // #[test]
    // fn parse_string_with_doublequote() -> Result<(), String> {
    //     let expression = "\" \\\" \"";
    //     let expected = " \" ";
    //     let result = parse_expr(expression)?;
    //     println!("'{}' => '{}'", expression, result.to_string());
    //     assert_eq!(result, Expr::Str(expected.to_string()));
    //     Ok(())
    // }

    #[test]
    fn parse_simple() {
        assert_eq!(parser::<(&str, ErrorKind)>("true"), Ok(("", Expr::Boolean(true))));
        assert_eq!(parser::<(&str, ErrorKind)>("2"), Ok(("", Expr::Num(dec!(2)))));
        assert_eq!(parser::<(&str, ErrorKind)>("(true)"), Ok(("", Expr::Boolean(true))));
        assert_eq!(parser::<(&str, ErrorKind)>("(-2)"), Ok(("", Expr::Num(dec!(-2)))));
        // assert_eq!(parser::<(&str, ErrorKind)>("true)"), Ok((")", Expr::Boolean(true))));
        // assert_eq!(parser::<(&str, ErrorKind)>("(true"), Err(nom::Err::Error(("", ErrorKind::Char))));
        // assert_eq!(parser::<(&str, ErrorKind)>("2 ,"), Ok((",", Expr::Num(dec!(2)))));
        // assert_eq!(parser::<(&str, ErrorKind)>("(2) ,"), Ok((" ,", Expr::Num(dec!(2)))));
    }

    #[test]
    fn parse_identifier_or_function_call() {
        assert_eq!(parser::<(&str, ErrorKind)>("true"), Ok(("", Expr::Boolean(true))));
        assert_eq!(parser::<(&str, ErrorKind)>("(true)"), Ok(("", Expr::Boolean(true))));
        assert_eq!(parser::<(&str, ErrorKind)>("( true )"), Ok(("", Expr::Boolean(true))));
        assert_eq!(parser::<(&str, ErrorKind)>("( _id )"), Ok(("", Expr::Identifier("_id".into()))));
        assert_eq!(parser::<(&str, ErrorKind)>("( id ( ) )"), Ok(("", Expr::FunctionCall("id".into(), vec!()))));
        assert_eq!(parser::<(&str, ErrorKind)>("_id()"), Ok(("", Expr::FunctionCall("_id".into(), vec!()))));
        // assert_eq!(parser::<(&str, ErrorKind)>("_id()toto"), Ok(("toto", Expr::FunctionCall("_id".into(), vec!()))));
        assert_eq!(parser::<(&str, ErrorKind)>("_id(1,2)"), Ok(("", Expr::FunctionCall("_id".into(), vec![rc_expr_num!(1), rc_expr_num!(2)]))));
        // assert_eq!(parser::<(&str, ErrorKind)>("_id( a , b"), Err(nom::Err::Error(("", ErrorKind::Char))));
        // assert_eq!(parser::<(&str, ErrorKind)>("id("), Err(nom::Err::Error(("", ErrorKind::Char))));
    }

    #[test_case(stringify!("null") => "null")]
    #[test_case(stringify!("test") => "test")]
    #[test_case(stringify!("t") => "t")]
    #[test_case("\"test escape\"" => "test escape")]
    #[test_case("\"test\ttab\"" => "test\ttab")]
    #[test_case(stringify!("test escape") => "test escape")]
    // #[test_case(stringify!("test\"doublequote") => "test\"doublequote")]
    #[test_case(stringify!("test\\slash") => "test\\slash")]
    // #[test_case(stringify!("test\newline") => "test\newline")]
    // #[test_case(stringify!("test\ttab") => "test\ttab")]
    // #[test_case(stringify!("test\rreturn") => "test\rreturn")]
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
        let result = parse_expr("\" te sΓé¼t\tt ab ./\"");
        assert_eq!(result, Ok(Expr::Str(" te sΓé¼t\tt ab ./".to_string())));
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

    // #[test_case("[1,2]" => Expr::Array(vec![rc_expr_num!(1), rc_expr_num!(2)]))]
    // #[test_case("([3,4])" => Expr::Array(vec![rc_expr_num!(3), rc_expr_num!(4)]))]
    // fn parse_array(expression: &str) -> Expr {
    //     parse_expr(expression).unwrap()
    // }

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

    #[test_case("test(\"value\" , 2 , \"null\")" => Expr::FunctionCall("test".to_string(), vec![rc_expr_str!("value".to_string()), rc_expr_num!(2), rc_expr_str!("null".to_string())]))]
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
        for complexity in 1..100 {
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
            dbg!(complexity, &expression);
            let now = Instant::now();
            let expr = expr::<(&str, ErrorKind)>(&expression);
            let (rest, _) = expr.unwrap();
            assert_eq!(rest.len(), 0);
            dbg!(now.elapsed());
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
