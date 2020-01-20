use crate::parsing::*;

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
    pub expr: RcExpr,
    pub identifiers_names: HashSet<String>,
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

impl ToString for Expr {
    fn to_string(&self) -> String {
        match self {
            Expr::Str(s) => s.to_string(),
            Expr::Boolean(b) => b.to_string(),
            Expr::Num(n) => n.to_string(),
            Expr::Array(_) => "Array".to_string(),
            Expr::Identifier(i) => format!("[{}]", i),
            Expr::FunctionCall(_, _) => "FunctionCall".to_string(),
            Expr::PreparedFunctionCall(_, _, _) => "PreparedFunctionCall".to_string(),
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

pub fn prepare_expr_list(
    exprs: &SliceRcExpr,
    funcs: &FunctionImplList,
    identifiers: &mut HashSet<String>,
) -> VecRcExpr {
    exprs
        .iter()
        .map(|p| prepare_expr(p.clone(), funcs, identifiers))
        .collect()
}

pub fn prepare_expr(
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

pub fn exec_expr<'a>(expr: &'a RcExpr, values: &'a IdentifierValues) -> Result<RcExpr, String> {
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
            let call_result = fnc(&parameters, &values)?;
            exec_expr(&call_result, values)
        }
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
            Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(rc_expr_num!(42_f64))),
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
            Rc::new(|v: &VecRcExpr, _: &IdentifierValues| {
                v.first().map_or_else(
                    || Err("There was no first value.".to_string()),
                    |x| Ok(x.clone()),
                )
            }),
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

    fn parse_exec_expr<'a>(
        expression: &'a str,
        funcs: &FunctionImplList,
        values: &IdentifierValues,
    ) -> String {
        let expr = parse_expr(expression).unwrap();
        let expr = prepare_expr_and_identifiers(expr, funcs);
        let result = exec_expr(&expr.expr, values).unwrap();
        result.to_string()
    }
}
