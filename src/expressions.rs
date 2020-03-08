use crate::parsing::*;
use std::fmt::Display;

use nom::error::ErrorKind;
use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

pub type RcExpr = Rc<Expr>;
pub type VecRcExpr = Vec<RcExpr>;
pub type SliceRcExpr = [RcExpr];
pub type ExprFuncResult = Result<RcExpr, String>;
pub type FunctionImpl = dyn Fn(&VecRcExpr, &IdentifierValues) -> ExprFuncResult;
pub type FunctionImplList = HashMap<String, Rc<FunctionImpl>>;
pub type IdentifierValueGetter = dyn Fn() -> String;
pub type IdentifierValues = HashMap<String, Box<IdentifierValueGetter>>;

pub type ExprDecimal = f64;

#[repr(C)]
#[derive(Clone)]
pub enum Expr {
    Str(String),
    Boolean(bool),
    Num(ExprDecimal),
    Null,
    Array(VecRcExpr),
    Identifier(String),
    FunctionCall(String, VecRcExpr),
    PreparedFunctionCall(String, VecRcExpr, Rc<FunctionImpl>),
    // BinaryOperator(RcExpr, RcExpr, AssocOp)
}

#[repr(C)]
#[derive(Debug)]
pub struct ExprAndIdentifiers {
    pub expr: RcExpr,
    pub identifiers_names: HashSet<String>,
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Str(x) => write!(f, "Str({:?})", x),
            Expr::Boolean(x) => write!(f, "Boolean({:?})", x),
            Expr::Num(x) => write!(f, "Num({:?})", x),
            Expr::Null => write!(f, "Null"),
            Expr::Array(x) => write!(f, "Array({:?})", x),
            Expr::Identifier(x) => write!(f, "Identifier({:?})", x),
            Expr::FunctionCall(s, x) => write!(f, "FunctionCall({:?},{:?})", s, x),
            Expr::PreparedFunctionCall(s, x, _) => write!(f, "PreparedFunctionCall({:?},{:?})", s, x),
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
            (Expr::FunctionCall(n_a, p_a), Expr::FunctionCall(n_b, p_b)) => n_a == n_b && p_a == p_b,
            (Expr::PreparedFunctionCall(n_a, p_a, _), Expr::PreparedFunctionCall(n_b, p_b, _)) => n_a == n_b && p_a == p_b,
            (Expr::Null, Expr::Null) => true, // todo : should be false !? => implemented in the `f_are_equals` function
            _ => false,
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Str(s) => write!(f, "{}", s),
            Expr::Boolean(b) => write!(f, "{}", b),
            Expr::Num(n) => write!(f, "{}", n),
            Expr::Null => write!(f, ""),
            Expr::Array(_) => write!(f, "Array"),
            Expr::Identifier(i) => write!(f, "[{}]", i),
            Expr::FunctionCall(_, _) => write!(f, "FunctionCall"),
            Expr::PreparedFunctionCall(_, _, _) => write!(f, "PreparedFunctionCall"),
        }
    }
}

impl Expr {
    pub fn is_final(&self) -> bool {
        match self {
            Expr::Str(_) => true,
            Expr::Boolean(b) => true,
            Expr::Num(_) => true,
            Expr::Null => true,
            Expr::Array(_) => false,
            Expr::Identifier(_) => false,
            Expr::FunctionCall(_, _) => false,
            Expr::PreparedFunctionCall(_, _, _) => false,
        }
    }
}

pub fn parse_expr(expression: &str) -> Result<Expr, String> {
    let expr = expr::<(&str, ErrorKind)>(expression);
    match expr {
        Ok(ok) => Ok(ok.1),
        Err(err_kind) => Err(format!("{:?}", err_kind)),
    }
}

pub fn prepare_expr_and_identifiers(expr: Expr, funcs: &FunctionImplList) -> ExprAndIdentifiers {
    let mut identifiers = HashSet::<String>::new();
    let expr = prepare_expr(Rc::new(expr), funcs, &mut identifiers);
    ExprAndIdentifiers {
        expr,
        identifiers_names: identifiers,
    }
}

pub fn prepare_expr_list(exprs: &SliceRcExpr, funcs: &FunctionImplList, identifiers: &mut HashSet<String>) -> VecRcExpr {
    exprs.iter().map(|p| prepare_expr(p.clone(), funcs, identifiers)).collect()
}

pub fn prepare_expr(expr: RcExpr, funcs: &FunctionImplList, identifiers: &mut HashSet<String>) -> RcExpr {
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
        Expr::Array(elements) => Rc::new(Expr::Array(prepare_expr_list(elements, funcs, identifiers))),
        _ => expr,
    }
}

pub fn exec_expr<'a>(expr: &'a RcExpr, values: &'a IdentifierValues) -> Result<RcExpr, String> {
    match expr.as_ref() {
        Expr::Str(_) => Ok(expr.clone()),
        Expr::Boolean(b) => Ok(Rc::new(Expr::Boolean(*b))),
        Expr::Num(f) => Ok(Rc::new(Expr::Num(*f))),
        Expr::Null => Ok(Rc::new(Expr::Null)),
        Expr::Array(_) => Ok(expr.clone()),
        Expr::Identifier(name) => match &values.get(name) {
            Some(s) => Ok(Rc::new(Expr::Str(s()))),
            None => Err(format!("Unable to find value for identifier named '{}'", name)),
        },
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(name, _parameters) => Err(format!("Unable to find the function named '{}'", name)),
        Expr::PreparedFunctionCall(_, parameters, fnc) => {
            let call_result = fnc(&parameters, &values)?;
            exec_expr(&call_result, values)
        }
    }
}

#[cfg(test)]
mod tests {
    // Note this useful idiom: importing names from outer (for mod tests) scope.
    use super::*;
    use crate::functions::*;
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
    macro_rules! rc_expr_null {
        () => {
            Rc::new(Expr::Null)
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

    #[test]
    fn parse_empty_string() { // to debug
                              // let expr = parse_expr("\"\"").unwrap();
                              // assert_eq!(expr, Expr::Str("\"\"".to_string()))
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

    #[test_case("1" => Expr::Num(1_f64))]
    #[test_case("1.2" => Expr::Num(1.2_f64))]
    #[test_case("-0.42" => Expr::Num(-0.42_f64))]
    fn parse_num(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("null" => Expr::Null)]
    fn parse_null(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("id" => Expr::Identifier("id".to_string()))]
    #[test_case("@idarobase" => Expr::Identifier("idarobase".to_string()))]
    // #[test_case("id_id" => Expr::Identifier("id_id".to_string()))] // to debug
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
    // #[test_case("test()" => Expr::FunctionCall("test".to_string(), Vec::<RcExpr>::new()))] // to debug
    #[test_case("test(aa)" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Identifier("aa".to_string()))]))]
    fn parse_function_call(expression: &str) -> Expr {
        parse_expr(expression).unwrap()
    }

    #[test_case("test([\"value\", 42, null],2, \"null\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Array(vec![rc_expr_str!("value".to_string()), rc_expr_num!(42_f64), rc_expr_null!()])), rc_expr_num!(2_f64), rc_expr_str!("null".to_string())]))]
    #[test_case("test(\"value\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Str("value".to_string()))]))]
    #[test_case("test(\"va lue\")" => Expr::FunctionCall("test".to_string(), vec![Rc::new(Expr::Str("va lue".to_string()))]))]
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
            Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(rc_expr_num!(42_f64))),
        );
        let expr = prepare_expr_and_identifiers(expr, &funcs);
        println!("{:?}", expr);
        let mut result = expr.identifiers_names.iter().cloned().collect::<Vec<String>>();
        result.sort();
        result
    }

    #[test]
    fn execute_one_expression() {
        let mut funcs = FunctionImplList::new();
        funcs.insert(
            "first".to_string(),
            Rc::new(|v: &VecRcExpr, _: &IdentifierValues| v.first().map_or_else(|| Err("There was no first value.".to_string()), |x| Ok(x.clone()))),
        );

        funcs.insert(
            "forty_two".to_string(),
            Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(rc_expr_num!(42_f64))),
        );
        funcs.insert(
            "forty_two_str".to_string(),
            Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(rc_expr_str!("42".to_string()))),
        );

        let mut values = IdentifierValues::new();
        values.insert("my".into(), Box::new(|| "value".to_string()));

        let expression = "first(first(first(my,2,3),2,3),2,3)";
        let result = parse_exec_expr(expression, &funcs, &values);
        assert_eq!(result, "value");
        println!("{:?}", result);
    }

    // #[test_case("Exact(null, \"\")" => "true")] // to debug
    #[test_case("Exact(null, Concat(null, null))" => "true")]
    #[test_case(stringify!("test") => "test")]
    #[test_case("IsNull(null)" => "true")]
    #[test_case("IsNull(IsBlank(null))" => "false")]
    #[test_case("AreEquals(IsBlank(null), IsNull(null))" => "true")]
    #[test_case("AreEquals(IsBlank(42), IsNull(null))" => "false")]
    #[test_case("In(null, null)" => "false")]
    #[test_case("In(true, false, 42, false)" => "false")]
    #[test_case("In(true, 42, true, false)" => "true")]
    #[test_case("In(\"ok\", 42, true, \"ok\")" => "true")]
    #[test_case("In(42, 42, true, \"ok\")" => "true")]
    #[test_case("Concat(42, 42, true, \"ok\")" => "4242trueok")]
    #[test_case("Concatenate(null, \"42\", true, \"ok\", In(42, 3.14))" => "42trueokfalse")]
    #[test_case("Exact(null, Concat(null, null, null))" => "true")]
    #[test_case("Find(\"hello\", \"hello\")" => "1")]
    #[test_case("Find(\"world\", \"helloworld\")" => "6")]
    #[test_case("Find(\"not found\", \"helloworld\")" => "0")]
    #[test_case("Find(\"world\", \"Hello world\")" => "7")]
    #[test_case("Find(\"AAA\", \"AAA\")" => "1")]
    #[test_case("Find(\" BBB\", \" BBB\")" => "1")]
    #[test_case("Find(\"\\\"\", \"co\\\"co\")" => "3")]
    #[test_case("Find(\"\\t\", \"bo\\tbo\")" => "3")]
    #[test_case("Find(\"AbcD\", \"aBCd\")" => "1")]
    #[test_case("Find(\"C\", \"CCC\", 1)" => "1")]
    #[test_case("Find(\"C\", \"CCC\", 0)" => "1")]
    #[test_case("Find(\"C\", \"CCC\", 2)" => "2")]
    #[test_case("Find(\"C\", \"CCC\", 3)" => "3")]
    #[test_case("Substitute(\"abcEFG\", \"aBC\", \"A\")" => "AEFG")]
    #[test_case("Substitute(\"abcEFG\", \"CCC\", 3)" => "abcEFG")]
    #[test_case("Substitute(\"abababa\", \"a\", null)" => "bbb")]
    #[test_case("Substitute(\"abababa\", \"a\", \"0O\")" => "0Ob0Ob0Ob0O")]
    #[test_case("Fixed(2)" => "2.00")]
    #[test_case("Fixed(2, 2)" => "2.00")]
    #[test_case("Fixed(3.1416, 2)" => "3.14")]
    #[test_case("Fixed(3.1416, 3)" => "3.142")]
    #[test_case("Fixed(3.1416, 5)" => "3.14160")]
    #[test_case("Fixed(31416, 0, true)" => "31416")]
    #[test_case("Fixed(31416, 0, false)" => "31,416")]
    #[test_case("Fixed(31415926.5359, 3, false)" => "31,415,926.536")]
    #[test_case("Fixed(0.42, 3, false)" => "0.420")]
    #[test_case("Left(\"Left\", 2)" => "Le")]
    #[test_case("Left(\"Left\", -2)" => "")]
    #[test_case("Left(\"Left\", 42)" => "Left")]
    #[test_case("Right(\"Right\", 3)" => "ght")]
    #[test_case("Right(\"Right\", -2)" => "")]
    #[test_case("FirstWord(\"once\")" => "once")]
    #[test_case("FirstWord(\"once upon\")" => "once")]
    #[test_case("FirstWord(\"a!time\")" => "a")]
    #[test_case("FirstWord(\"w.at\")" => "w")]
    #[test_case("FirstWord(\"you\tou\")" => "you")]
    #[test_case("FirstSentence(\"once upon. a time\")" => "once upon")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 0)" => "a")]
    #[test_case("Split(\"azbzczdze\", \"z\", 0)" => "a")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 2)" => "c")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 42)" => "")]
    #[test_case("Mid(\"abcdefghij\", 1, 2)" => "ab")]
    #[test_case("Mid(\"abcdefghij\", 2, 2)" => "bc")]
    #[test_case("Mid(\"abcdefghij\", 2, 3)" => "bcd")]
    #[test_case("Mid(\"abcdefghij\", -2, 3)" => "abc")]
    #[test_case("Mid(\"abcdefghij\", 0, 0)" => "")]
    #[test_case("Mid(\"abcdefghij\", 4, 42)" => "defghij")]
    #[test_case("Mid(\"abcdefghij\", 4, \"7\")" => "defghij")]
    #[test_case("Mid(\"abcdefghij\", -42, 42)" => "abcdefghij")]
    #[test_case("Mid(\"abcdefghij\", \"1\", 10)" => "abcdefghij")]
    #[test_case("Concat(Mid(Left(\"abcdefghij\", 3), \"2\", 1), NumberValue(\"3\"))" => "b3")]
    #[test_case("NumberValue(\"2\")" => "2")]
    #[test_case("NumberValue(\"2.3\")" => "2.3")]
    #[test_case("NumberValue(\"2z4\", \"z.\")" => "2.4")]
    #[test_case("Text(\"toto\")" => "toto")]
    fn execute_some_real_world_expression(expression: &str) -> String {
        let funcs = get_functions();
        parse_exec_expr(expression, &funcs, &IdentifierValues::new())
    }

    fn parse_exec_expr<'a>(expression: &'a str, funcs: &FunctionImplList, values: &IdentifierValues) -> String {
        let expr = parse_expr(expression).unwrap();
        let expr = prepare_expr_and_identifiers(expr, funcs);
        let result = exec_expr(&expr.expr, values).unwrap();
        result.to_string()
    }
}
