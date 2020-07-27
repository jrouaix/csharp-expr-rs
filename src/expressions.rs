use crate::parsing::*;
use std::fmt::Display;

use chrono::prelude::*;
use chrono::Duration;
use nom::error::ErrorKind;
use rust_decimal::prelude::*;
use std::cmp;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::ops::Add;
use std::ops::AddAssign;
use std::rc::Rc;
use unicase::UniCase;

pub type RcExpr = Rc<Expr>;
pub type VecRcExpr = Vec<RcExpr>;
pub type SliceRcExpr = [RcExpr];
pub type ExprFuncResult = Result<ExprResult, String>;
pub type FunctionImpl = dyn Fn(&VecRcExpr, &IdentifierValues) -> ExprFuncResult;
pub type FunctionImplList = HashMap<UniCase<String>, (FunctionDeterminism, Rc<FunctionImpl>)>;
pub type IdentifierValueGetter = dyn Fn() -> String;
pub type IdentifierValues = HashMap<UniCase<String>, Box<IdentifierValueGetter>>;
pub type ExprDecimal = Decimal;

pub trait BinaryOperatorsImpl: Fn(RcExpr, RcExpr, AssocOp, &IdentifierValues) -> ExprFuncResult {}
impl<T> BinaryOperatorsImpl for T where T: Fn(RcExpr, RcExpr, AssocOp, &IdentifierValues) -> ExprFuncResult {}
pub type BinaryOperatorsImplRc = Rc<dyn BinaryOperatorsImpl>;

#[repr(C)]
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum FunctionDeterminism {
    Deterministic,
    NonDeterministic,
}

impl Default for FunctionDeterminism {
    fn default() -> Self {
        FunctionDeterminism::Deterministic
    }
}

impl Add for FunctionDeterminism {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        match (self, other) {
            (FunctionDeterminism::Deterministic, FunctionDeterminism::Deterministic) => FunctionDeterminism::Deterministic,
            _ => FunctionDeterminism::NonDeterministic,
        }
    }
}

impl AddAssign for FunctionDeterminism {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

// got this list from rust : https://docs.microsoft.com/en-us/dotnet/csharp/language-reference/operators/arithmetic-operators
#[derive(PartialEq, Copy, Clone)]
pub enum AssocOp {
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulus,
    LAnd,
    LOr,
    Equal,
    Less,
    LessEqual,
    NotEqual,
    Greater,
    GreaterEqual,
}

impl fmt::Display for AssocOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            AssocOp::Add => write!(f, "+"),
            AssocOp::Subtract => write!(f, "-"),
            AssocOp::Multiply => write!(f, "*"),
            AssocOp::Divide => write!(f, "/"),
            AssocOp::Modulus => write!(f, "%"),
            AssocOp::LAnd => write!(f, "&&"),
            AssocOp::LOr => write!(f, "||"),
            AssocOp::Equal => write!(f, "=="),
            AssocOp::Less => write!(f, "<"),
            AssocOp::LessEqual => write!(f, "<="),
            AssocOp::NotEqual => write!(f, "!="),
            AssocOp::Greater => write!(f, ">"),
            AssocOp::GreaterEqual => write!(f, ">="),
        }
    }
}

impl fmt::Debug for AssocOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        self::Display::fmt(self, f)
    }
}

#[repr(C)]
#[derive(Clone)]
pub enum Expr {
    Str(String),                                                                  // "text"
    Boolean(bool),                                                                // true | false
    Num(ExprDecimal),                                                             // 123.45
    Null,                                                                         // null
    Array(VecRcExpr),                                                             // [null, 42, "text"]
    Identifier(String),                                                           // varToto
    FunctionCall(String, VecRcExpr),                                              // func(42, "text")
    PreparedFunctionCall(String, VecRcExpr, Rc<FunctionImpl>),                    // func(42, "text") + *func()
    BinaryOperator(RcExpr, RcExpr, AssocOp),                                      // 32 + 10
    PreparedBinaryOperator(RcExpr, RcExpr, AssocOp, Rc<dyn BinaryOperatorsImpl>), // 32 + 10 + *operators()
}

#[derive(Clone, Debug)]
pub enum ExprResult {
    Str(String),
    Boolean(bool),
    Num(ExprDecimal),
    Date(NaiveDateTime),
    TimeSpan(Duration),
    Null,

    NonExecuted(RcExpr),
}

#[repr(C)]
#[derive(Debug)]
pub struct ExprAndIdentifiers {
    pub expr: RcExpr,
    pub identifiers_names: HashSet<String>,
    pub determinism: FunctionDeterminism,
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
            Expr::BinaryOperator(l, r, o) => write!(f, "{:?} {:?} {:?}", l, o, r),
            Expr::PreparedBinaryOperator(l, r, o, _) => write!(f, "{:?} {:?} {:?}", l, o, r),
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
            (Expr::BinaryOperator(left_a, right_a, op_a), Expr::BinaryOperator(left_b, right_b, op_b)) => left_a == left_b && right_a == right_b && op_a == op_b,
            (Expr::PreparedBinaryOperator(left_a, right_a, op_a, _), Expr::PreparedBinaryOperator(left_b, right_b, op_b, _)) => left_a == left_b && right_a == right_b && op_a == op_b,
            (Expr::FunctionCall(n_a, p_a), Expr::FunctionCall(n_b, p_b)) => n_a == n_b && p_a == p_b,
            (Expr::PreparedFunctionCall(n_a, p_a, _), Expr::PreparedFunctionCall(n_b, p_b, _)) => n_a == n_b && p_a == p_b,
            (Expr::Null, Expr::Null) => true,
            _ => false,
        }
    }
}

impl cmp::PartialEq for ExprResult {
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ExprResult::Str(x_a), ExprResult::Str(x_b)) => x_a == x_b,
            (ExprResult::Boolean(x_a), ExprResult::Boolean(x_b)) => x_a == x_b,
            (ExprResult::Num(x_a), ExprResult::Num(x_b)) => x_a == x_b,
            (ExprResult::Date(x_a), ExprResult::Date(x_b)) => x_a == x_b,
            (ExprResult::TimeSpan(x_a), ExprResult::TimeSpan(x_b)) => x_a == x_b,
            (ExprResult::Null, ExprResult::Null) => true, // should be false ? => implemented in the `f_are_equals` function
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
            Expr::Identifier(i) => write!(f, "@{}", i),
            Expr::FunctionCall(_, _) => write!(f, "FunctionCall"),
            Expr::PreparedFunctionCall(_, _, _) => write!(f, "PreparedFunctionCall"),
            Expr::BinaryOperator(l, r, o) => write!(f, "{} {} {}", l, o, r),
            Expr::PreparedBinaryOperator(l, r, o, _) => write!(f, "{} {} {}", l, o, r),
        }
    }
}

const SECONDS_IN_MIN: i64 = 60;
const SECONDS_IN_HOURS: i64 = SECONDS_IN_MIN * 60;
const SECONDS_IN_DAYS: i64 = SECONDS_IN_HOURS * 24;

impl Display for ExprResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExprResult::Str(s) => write!(f, "{}", s),
            ExprResult::Boolean(b) => write!(f, "{}", b),
            ExprResult::Num(n) => write!(f, "{}", n),
            ExprResult::Date(d) => write!(f, "{:02}/{:02}/{:02} {:02}:{:02}:{:02}", d.month(), d.day(), d.year(), d.hour(), d.minute(), d.second()),
            ExprResult::TimeSpan(d) => {
                let sign = if *d < Duration::zero() { "-" } else { "" };
                let mut secs = d.num_seconds().abs();
                let days = secs / SECONDS_IN_DAYS;
                secs = secs - days * SECONDS_IN_DAYS;
                let hours = secs / SECONDS_IN_HOURS;
                secs = secs - hours * SECONDS_IN_HOURS;
                let mins = secs / SECONDS_IN_MIN;
                secs = secs - mins * SECONDS_IN_MIN;
                if days > 0 {
                    write!(f, "{}{}.{:02}:{:02}:{:02}", sign, days, hours, mins, secs)
                } else {
                    write!(f, "{}{:02}:{:02}:{:02}", sign, hours, mins, secs)
                }
            }
            ExprResult::Null => write!(f, ""),
            ExprResult::NonExecuted(rc_expr) => write!(f, "{:?}", rc_expr),
        }
    }
}

impl ExprResult {
    pub fn is_final(&self) -> bool {
        match self {
            ExprResult::NonExecuted(_) => false,
            _ => true,
        }
    }
}

pub fn parse_expr(expression: &str) -> Result<Expr, String> {
    let expr = expr::<(&str, ErrorKind)>(expression);
    match expr {
        Ok((rest, expr)) => match rest.len() {
            0 => Ok(expr),
            _ => Err(format!("Unable to parse the rest of the expression '{:?}'", rest)),
        },
        Err(err_kind) => Err(format!("{:?}", err_kind)),
    }
}

pub fn prepare_expr_and_identifiers(expr: Expr, funcs: &FunctionImplList, operators: BinaryOperatorsImplRc) -> ExprAndIdentifiers {
    let mut identifiers = HashSet::<String>::new();
    let (determinism, expr) = prepare_expr(Rc::new(expr), funcs, &mut identifiers, operators);
    ExprAndIdentifiers {
        expr,
        identifiers_names: identifiers,
        determinism,
    }
}

pub fn prepare_expr_list(exprs: &SliceRcExpr, funcs: &FunctionImplList, identifiers: &mut HashSet<String>, operators: BinaryOperatorsImplRc) -> (FunctionDeterminism, VecRcExpr) {
    let mut list = VecRcExpr::with_capacity(exprs.len());
    let mut total_determinist = FunctionDeterminism::default();
    for p in exprs.iter() {
        let (determinism, prepared) = prepare_expr(Rc::clone(p), funcs, identifiers, Rc::clone(&operators));
        list.push(prepared);
        total_determinist += determinism;
    }
    (total_determinist, list)
}

pub fn prepare_expr(expr: RcExpr, funcs: &FunctionImplList, identifiers: &mut HashSet<String>, operators: BinaryOperatorsImplRc) -> (FunctionDeterminism, RcExpr) {
    match expr.as_ref() {
        Expr::Identifier(name) => {
            identifiers.insert(name.clone());
            (FunctionDeterminism::Deterministic, expr)
        }
        Expr::FunctionCall(name, parameters) => match &funcs.get(&UniCase::new(name.into())) {
            Some(fnc) => {
                let (params_determinism, prepared_list) = prepare_expr_list(parameters, funcs, identifiers, operators);
                (fnc.0 + params_determinism, Rc::new(Expr::PreparedFunctionCall(name.clone(), prepared_list, Rc::clone(&fnc.1))))
            }
            None => (FunctionDeterminism::default(), expr),
        },
        Expr::BinaryOperator(left, right, op) => {
            let left_prepared = prepare_expr(Rc::clone(left), funcs, identifiers, Rc::clone(&operators));
            let right_prepared = prepare_expr(Rc::clone(right), funcs, identifiers, Rc::clone(&operators));
            (
                (left_prepared.0 + right_prepared.0),
                RcExpr::new(Expr::PreparedBinaryOperator(left_prepared.1, right_prepared.1, *op, Rc::clone(&operators))),
            )
        }
        Expr::Array(elements) => {
            let (determinism, prepared_list) = prepare_expr_list(elements, funcs, identifiers, operators);
            (determinism, Rc::new(Expr::Array(prepared_list)))
        }
        Expr::Str(_) => (FunctionDeterminism::Deterministic, expr),
        Expr::Boolean(_) => (FunctionDeterminism::Deterministic, expr),
        Expr::Num(_) => (FunctionDeterminism::Deterministic, expr),
        Expr::Null => (FunctionDeterminism::Deterministic, expr),
        Expr::PreparedFunctionCall(_, _, _) => unreachable!(),
        Expr::PreparedBinaryOperator(_, _, _, _) => unreachable!(),
    }
}

pub fn exec_expr<'a>(expr: &'a RcExpr, values: &'a IdentifierValues) -> Result<ExprResult, String> {
    match expr.as_ref() {
        Expr::Str(s) => Ok(ExprResult::Str(s.clone())),
        Expr::Boolean(b) => Ok(ExprResult::Boolean(*b)),
        Expr::Num(f) => Ok(ExprResult::Num(*f)),
        Expr::Null => Ok(ExprResult::Null),
        Expr::Array(_) => Ok(ExprResult::NonExecuted(expr.clone())),
        Expr::Identifier(name) => match &values.get(&UniCase::new(name.into())) {
            Some(s) => Ok(ExprResult::Str(s())),
            None => Err(format!("Unable to find value for identifier named '{}'", name)),
        },
        // Expr::BinaryOperator(_, _, _) => Ok(expr),
        Expr::FunctionCall(name, _parameters) => Err(format!("Unable to find the function named '{}'", name)),
        Expr::PreparedFunctionCall(_, parameters, fnc) => {
            let call_result = fnc(&parameters, &values)?;
            if let ExprResult::NonExecuted(expr) = call_result {
                exec_expr(&expr, values)
            } else {
                Ok(call_result)
            }
        }
        Expr::BinaryOperator(_, _, _) => Err(format!("No operators implementation")),
        Expr::PreparedBinaryOperator(left, right, op, op_impl) => op_impl(Rc::clone(left), Rc::clone(right), *op, values),
    }
}

#[cfg(test)]
mod tests {
    use super::FunctionDeterminism::*;
    use super::*;
    use crate::functions::*;
    use rust_decimal_macros::*;
    use test_case::test_case;

    macro_rules! rc_expr_str {
        ( $x:expr ) => {
            Rc::new(Expr::Str($x.to_string()))
        };
    }
    macro_rules! exprresult_str {
        ( $x:expr ) => {
            ExprResult::Str($x)
        };
    }
    macro_rules! rc_expr_num {
        ( $x:expr ) => {
            Rc::new(Expr::Num(dec!($x)))
        };
    }
    macro_rules! exprresult_num {
        ( $x:expr ) => {
            ExprResult::Num($x)
        };
    }
    macro_rules! rc_expr_null {
        () => {
            Rc::new(Expr::Null)
        };
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
            UniCase::new("knownFunc".to_string()),
            (FunctionDeterminism::Deterministic, Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(exprresult_num!(dec!(42))))),
        );
        let expr = prepare_expr_and_identifiers(expr, &funcs, Rc::new(null_op));
        println!("{:?}", expr);
        let mut result = expr.identifiers_names.iter().cloned().collect::<Vec<String>>();
        result.sort();
        result
    }

    #[test]
    fn execute_one_expression() {
        let mut funcs = FunctionImplList::new();
        funcs.insert(
            UniCase::new("first".to_string()),
            (
                FunctionDeterminism::Deterministic,
                Rc::new(|v: &VecRcExpr, _: &IdentifierValues| v.first().map_or_else(|| Err("There was no first value.".to_string()), |x| Ok(ExprResult::NonExecuted(x.clone())))),
            ),
        );

        funcs.insert(
            UniCase::new("forty_two".to_string()),
            (FunctionDeterminism::Deterministic, Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(exprresult_num!(dec!(42))))),
        );
        funcs.insert(
            UniCase::new("forty_two_str".to_string()),
            (FunctionDeterminism::Deterministic, Rc::new(|_v: &VecRcExpr, _: &IdentifierValues| Ok(exprresult_str!("42".to_string())))),
        );

        let mut values = IdentifierValues::new();
        values.insert("my".into(), Box::new(|| "value".to_string()));

        let expression = "first(fiRst(FIRST(my,2,3),2,3),2,3)";
        let result = parse_exec_expr(expression, &funcs, &values, Rc::new(null_op));
        assert_eq!(result, "value");

        let expression = "fiRst(my,2,3) - 1";
        let result = parse_exec_expr(expression, &funcs, &values, Rc::new(null_op));
        assert_eq!(result, "");
    }

    #[test_case("true && false" => "false")]
    #[test_case("false || true" => "true")]
    #[test_case("3" => "3")]
    #[test_case("1+2" => "3")]
    #[test_case("1-1" => "0")]
    #[test_case("1 == 1" => "true")]
    #[test_case("1 != 1" => "false")]
    #[test_case("1/2" => "0.5")]
    #[test_case("1-2/2" => "-0.5")]
    #[test_case("1-(3/3)" => "0")]
    #[test_case("1>42" => "false")]
    #[test_case("2 >= 2" => "true")]
    #[test_case("5>=2" => "true")]
    #[test_case("7<2" => "false")]
    #[test_case("9<=9" => "true")]
    #[test_case("42%3" => "0")]
    #[test_case("43 % 3" => "1")]
    #[test_case("NumberValue(\"3\")% 2" => "1")]
    #[test_case("3 % 2" => "1")]
    #[test_case("Exact(null, \"\")" => "true")]
    #[test_case("null" => "")]
    #[test_case("eXaCt(null, Concat(null, null))" => "true")]
    #[test_case("Exact(\"null\", \"null\")" => "true")]
    #[test_case(stringify!("test") => "test")]
    #[test_case("IIF(ISNULL(\"2345876\"), \"\", \"M\")" => "M")]
    #[test_case("IIF(ISNULL(76), \"\", \"M\")" => "M")]
    #[test_case("IsNull(null)" => "true")]
    #[test_case("IsNull(2)" => "false")]
    #[test_case("IsNull(\" \t \")" => "true")]
    #[test_case("isnull([])" => "false")]
    #[test_case("isnull([test])" => "false")]
    #[test_case("IsNull(IsBlank(null))" => "false")]
    #[test_case("AreEquals(IsBlank(null), IsNull(null))" => "true")]
    #[test_case("AreEquals(IsBlank(42), IsNull(null))" => "false")]
    #[test_case("In(null, null)" => "false")]
    #[test_case("In(true, false, 42, false)" => "false")]
    #[test_case("In(true, 42, true, false)" => "true")]
    #[test_case("In(\"ok\", 42, true, \"ok\")" => "true")]
    #[test_case("In(42, 42, true, \"ok\")" => "true")]
    #[test_case("Like(42, 42)" => "true" )]
    // #[test_case("ISLIKE(\"https://www.matelas.com/195-sur-matelas.html#/2-dimensions-140x190\", \"#\")" => "true" )] // to debug
    #[test_case("Like(4242, \"4_42\")" => "true" )]
    #[test_case("Like(424, \"4_4%\")" => "true" )]
    #[test_case("Like(4242, \"%_42\")" => "true" )]
    #[test_case("Like(\"hooo%hooo_hoooo\", \"h%o%%h%o__%\")" => "true" )]
    #[test_case("InLike(42, 42)" => "true" )]
    #[test_case("InLike(42, 43, 42)" => "true" )]
    #[test_case("InLike(42, 43, 66)" => "false" )]
    #[test_case("InLike(\"event_ally%nt\", \"nope\", \"Eventually Consistant\")" => "true")]
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
    #[test_case("Find(\"Alpha\", \"Alphabet\")" => "1")]
    #[test_case("Substitute(\"abcEFG\", \"aBC\", \"A\")" => "AEFG")]
    #[test_case("Substitute(\"abcEFG\", \"CCC\", 3)" => "abcEFG")]
    #[test_case("Substitute(\"abababa\", \"a\", null)" => "bbb")]
    #[test_case("Substitute(\"abababa\", \"a\", \"0O\")" => "0Ob0Ob0Ob0O")]
    #[test_case("Fixed(2)" => "2.00")]
    #[test_case("Fixed(2, 2)" => "2.00")]
    #[test_case("Fixed(3.1416, 2)" => "3.14")]
    #[test_case("Fixed(3.1416, 3)" => "3.142")]
    #[test_case("Fixed(3.1416, 5)" => "3.14160")]
    #[test_case("Fixed(31415926.5359, 0, true)" => "31415927")]
    #[test_case("Fixed(31415926.5359, 0, false)" => "31,415,927")]
    #[test_case("Fixed(31415926.5359, 1, true)" => "31415926.5")]
    #[test_case("Fixed(31415926.5359, 1, false)" => "31,415,926.5")]
    #[test_case("Fixed(31415926.5359, 2, true)" => "31415926.54")]
    #[test_case("Fixed(31415926.5359, 2, false)" => "31,415,926.54")]
    #[test_case("Fixed(31415926.5359, 3, true)" => "31415926.536")]
    #[test_case("Fixed(31415926.5359, 3, false)" => "31,415,926.536")]
    #[test_case("Fixed(31415926.5359, 4, true)" => "31415926.5359")]
    #[test_case("Fixed(31415926.5359, 4, false)" => "31,415,926.5359")]
    #[test_case("Fixed(31415926.5359, 5, true)" => "31415926.53590")]
    #[test_case("Fixed(31415926.5359, 5, false)" => "31,415,926.53590")]
    #[test_case("Fixed(31416, 0, false)" => "31,416")]
    #[test_case("Fixed(31416, 0)" => "31416")]
    #[test_case("Fixed(0.42, 3, false)" => "0.420")]
    #[test_case("Left(\"Left\", 2)" => "Le")]
    #[test_case("Left(\"Left\", -2)" => "")]
    #[test_case("Left(\"Left\", 42)" => "Left")]
    #[test_case("Right(\"Right\", 3)" => "ght")]
    #[test_case("Right(\"Right\", -2)" => "")]
    #[test_case("Mid(\"Mid\", 1, 1)" => "M")]
    #[test_case("Mid(\"Mid\", 0, 2)" => "Mi")]
    #[test_case("Mid(\"Mid\", 3, 15)" => "d")]
    #[test_case("Mid(\"bcatag\", 2, 3)" => "cat")]
    #[test_case("Mid(\"bcatag\", 6, 3)" => "g")]
    #[test_case("Mid(\"bcatag\", 7, 3)" => "")]
    #[test_case("Len(null)" => "0")]
    #[test_case("Len(\" \")" => "1")]
    #[test_case("Len(\"12\")" => "2")]
    #[test_case("Len(3.14)" => "4")]
    #[test_case("Lower(3.14)" => "3.14")]
    #[test_case("Lower(\"A\")" => "a")]
    #[test_case("Lower(\"aBc\")" => "abc")]
    #[test_case("Upper(3.14)" => "3.14")]
    #[test_case("Upper(\"a\")" => "A")]
    #[test_case("Upper(\"AbC\")" => "ABC")]
    #[test_case("Trim(\"AbC\")" => "AbC")]
    #[test_case("Trim(\"   \t AbCd\")" => "AbCd")]
    #[test_case("Trim(\"   \t AbCd  eE  \t \")" => "AbCd  eE")]
    #[test_case("FirstWord(\"once\")" => "once")]
    #[test_case("FirstWord(\"once upon\")" => "once")]
    #[test_case("FirstWord(\"a!time\")" => "a")]
    #[test_case("FirstWord(\"w.at\")" => "w")]
    #[test_case("FirstWord(\"you\tou\")" => "you")]
    #[test_case("FirstSentence(\"once upon. a time\")" => "once upon.")]
    #[test_case("FirstSentence(\"toto\")" => "toto")]
    #[test_case("FirstSentence(\"toto. Wat ?\")" => "toto.")]
    #[test_case("FirstSentence(\"Wat ? toto.\")" => "Wat ?")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 0)" => "a")]
    #[test_case("Split(\"azbzczdze\", \"z\", 0)" => "a")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 2)" => "c")]
    #[test_case("Split(\"a,b,c,d,e\", \",\", 42)" => "")]
    #[test_case("Split(\"1,2,3,4,5,6,7\", \",\", 90)" => "")]
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
    #[test_case("Capitalize(\"\")" => "")]
    #[test_case("Capitalize(\"toto\")" => "Toto")]
    #[test_case("Capitalize(\" once Upon a Time. in ? america ? Already upper case  ... y ! i    i . \")" => " Once Upon a Time. In ? America ? Already upper case  ... Y ! I    i . ")]
    #[test_case("StartsWith(\"toto\", \"t\")" => "true")]
    #[test_case("StartsWith(null, \"t\")" => "false")]
    #[test_case("StartsWith(\"toto\", null)" => "true")]
    #[test_case("StartsWith(\"toto\", \"tota\")" => "false")]
    #[test_case("StartsWith(\"toto\", \"totoa\")" => "false")]
    #[test_case("StartsWith(\"abc\", \"aBC\")" => "true")]
    #[test_case("EndsWith(\"toto\", \"o\")" => "true")]
    #[test_case("EndsWith(null, \"t\")" => "false")]
    #[test_case("EndsWith(\"toto\", null)" => "true")]
    #[test_case("EndsWith(\"toto\", \"aoto\")" => "false")]
    #[test_case("EndsWith(\"toto\", \"atoto\")" => "false")]
    #[test_case("EndsWith(\"abc\", \"aBC\")" => "true")]
    #[test_case("ReplaceEquals(\"aBc\", null, \"aaa\", NumberValue(\"BREAK\"), \"abc\", 42, NumberValue(\"BREAK\"), NumberValue(\"BREAK\"))" => "42")]
    #[test_case("ReplaceLike(\"aBc\", null, \"aaa\", NumberValue(\"BREAK\"), \"%c\", 42, NumberValue(\"BREAK\"), NumberValue(\"BREAK\"))" => "42")]
    #[test_case("And(\"TrUe\", \"1\", 1, true, true)" => "true")]
    #[test_case("And(\"true\", 0, true, NumberValue(\"BREAK\"))" => "false")]
    #[test_case("Or(true, NumberValue(\"BREAK\"))" => "true")]
    #[test_case("Or(false, 0, \"anything\", Sum(2, -1), NumberValue(\"BREAK\"))" => "true")]
    #[test_case("Not(false)" => "true")]
    #[test_case("Not(1)" => "false")]
    #[test_case("Not(\"not\")" => "true")]
    #[test_case("Xor(true, true)" => "false")]
    #[test_case("Xor(true, false)" => "true")]
    #[test_case("Xor(false, true)" => "true")]
    #[test_case("Xor(false, false)" => "false")]
    #[test_case("Iif(true, 42, NumberValue(\"BREAK\"))" => "42")]
    #[test_case("Iif(false, NumberValue(\"BREAK\"), 42)" => "42")]
    // #[test_case("IIF(NUMBERVALUE(\"\") >= NUMBERVALUE(150), 0, 6.9)" => "6.9")]
    // #[test_case("IIF(NUMBERVALUE(\"\") < NUMBERVALUE(1), \"Hors Stock\", \"En stock\")" => "En stock")]
    #[test_case("Abs(2)" => "2")]
    #[test_case("Abs(-32)" => "32")]
    #[test_case("Abs(-0)" => "0")]
    #[test_case("Product(2, 3, 0)" => "0")]
    #[test_case("Product(1, 2, 3)" => "6")]
    #[test_case("Product(1, 2, 3, \"-1\")" => "-6")]
    #[test_case("Divide(2, 1)" => "2")]
    #[test_case("Divide(3, -2)" => "-1.5")]
    #[test_case("Subtract(3, 2)" => "1")]
    #[test_case("Subtract(-3, 5)" => "-8")]
    #[test_case("Modulo(3, 2)" => "1")]
    #[test_case("Mod(-5, 2)" => "-1")]
    #[test_case("Mod(-21, 4)" => "-1")]
    #[test_case("Mod(7.5, -3)" => "1.5")]
    #[test_case("Round(3.1416, -1)" => "3")]
    #[test_case("Round(3.1416, 0)" => "3")]
    #[test_case("Round(3.1416, 1)" => "3.1")]
    #[test_case("Round(3.1416, 2)" => "3.14")]
    #[test_case("Round(3.1416, 3)" => "3.142")]
    #[test_case("Round ( 3.1416, 4 )" => "3.1416")]
    #[test_case("Round(\"3.1416\", 5)" => "3.1416")]
    #[test_case("69.9 / NUMBERVALUE(1.2)" => "58.25")]
    #[test_case("NUMBERVALUE(69.9) / NUMBERVALUE(1.2)" => "58.25")]
    #[test_case("ROUND(NUMBERVALUE(69.9) / NUMBERVALUE(1.2), 2)" => "58.25")]
    #[test_case("GreaterThan(2, 3)" => "false")]
    #[test_case("Gt(3, 3)" => "false")]
    #[test_case("Gt(3, -1)" => "true")]
    #[test_case("LowerThan(2, 5)" => "true")]
    #[test_case("Lt(3, 3)" => "false")]
    #[test_case("Lt(3, -1)" => "false")]
    #[test_case("GreaterThanOrEqual(2, 3)" => "false")]
    #[test_case("Gtoe(3, 3)" => "true")]
    #[test_case("Gtoe(3, -1)" => "true")]
    #[test_case("LowerThanOrEqual(2, 5)" => "true")]
    #[test_case("Ltoe(3, 3)" => "true")]
    #[test_case("Ltoe(3, -1)" => "false")]
    #[test_case("Date(\"1996-12-19T16:39:57-08:00\")" => "12/20/1996 00:39:57")]
    #[test_case("Date(\"1996-12-07T16:39:57Z\")" => "12/07/1996 16:39:57")]
    #[test_case("Date(\"1996-12-07 16:39:57\")" => "12/07/1996 16:39:57")]
    #[test_case("Date(\" 1996/12/07 16:39:58 \")" => "12/07/1996 16:39:58")]
    #[test_case("Date(\"1996-12-07\")" => "12/07/1996 00:00:00")]
    #[test_case("Year(\"1996-12-19T16:39:57-08:00\")" => "1996")]
    #[test_case("Month(\"1996-12-19T16:39:57-08:00\")" => "12")]
    #[test_case("Day(\"1996-12-19T16:39:57-08:00\")" => "20")]
    #[test_case("Day(\"1996-12-07T16:39:57Z\")" => "7")]
    #[test_case("DateDiff(\"1996-12-07T16:39:58Z\", \"1996-12-07T16:39:57Z\")" => "00:00:01")]
    #[test_case("DateDiff(\"1996-12-07T16:39:57Z\", \"1996-12-02T16:40:52Z\")" => "4.23:59:05")]
    #[test_case("DateDiff(\"1996-12-07T16:39:57Z\", \"1996-12-09T16:39:57Z\")" => "-2.00:00:00")]
    #[test_case("DateAddHours(Date(\"1996-12-19T16:39:57-08:00\"), -8)" => "12/19/1996 16:39:57")]
    #[test_case("DateAddHours(\"1996-12-19T16:39:57-08:00\", -8.5)" => "12/19/1996 16:09:57")]
    #[test_case("DateAddDays(\"1996-12-19T16:39:57-08:00\", 1.5)" => "12/21/1996 12:39:57")]
    #[test_case("DateAddDays(\"1996-12-19T16:39:57-08:00\", -1.5)" => "12/18/1996 12:39:57")]
    #[test_case("DateAddMonths(\"1996-12-19T16:39:57-08:00\", 16)" => "04/20/1998 00:39:57")]
    #[test_case("DateAddMonths(\"1996-12-19T16:39:57-08:00\", -5)" => "07/20/1996 00:39:57")]
    #[test_case("DateAddMonths(\"1996-12-19T16:39:57-08:00\", -15)" => "09/20/1995 00:39:57")]
    #[test_case("LocalDate(\"1996-12-19T16:39:57Z\", \"Romance Standard Time\")" => "12/19/1996 17:39:57")]
    #[test_case("LocalDate(\"1996-07-23T16:39:57Z\", \"Romance Standard Time\")" => "07/23/1996 18:39:57")]
    #[test_case("DateFormat(\"1996-12-19T16:39:57Z\")" => "1996-12-19 16:39:57.000")]
    #[test_case("DateFormat(\"1996-12-19T16:39:57.123Z\")" => "1996-12-19 16:39:57.123")]
    #[test_case("DateFormat(\"2021-12-19T16:39:57.123Z\", \"yyyy-MMM-mm\")" => "2021-Dec-39")]
    #[test_case("DateFormat(\"2021-12-19T16:39:57.123Z\", \"yyyy-MMMM-dd\")" => "2021-December-19")]
    #[test_case("DateFormat(\"2021-12-19T16:39:57.123Z\", \"h:m:s\")" => " 4:39:57")]
    #[test_case("DateFormat(\"2021-12-19T16:39:57.123Z\", \"H:m:s\")" => "16:39:57")]
    #[test_case("SUBSTITUTE(null, \"\", \"hop\")" => "hop")]
    #[test_case("SUBSTITUTE(\"\", \"\", \"hip\")" => "hip")]
    #[test_case("SUBSTITUTE(\"ha\", \"\", \"hip\")" => "ha")]
    #[test_case("SUBSTITUTE(\"\", \"ho\", \"hip\")" => "")]
    #[test_case("IIF(AreEquals(NUMBERVALUE(LEN(\"123456789012\")), NUMBERVALUE(12)), CONCATENATE(\"123456789012\", \"0\"), \"nope\")" => "1234567890120")]
    #[test_case("IIF(NUMBERVALUE(LEN(\"123456789012\")) == NUMBERVALUE(12), CONCATENATE(\"123456789012\", \"0\"), \"nope\")" => "1234567890120")]
    #[test_case("Date(\"2020-07-14 13:00:00.000\")" => "07/14/2020 13:00:00")]
    #[test_case("Date(\"2020-07-14 13:00:00\")" => "07/14/2020 13:00:00")]
    #[test_case("Date(\"2020-07-14 08:18\")" =>  "07/14/2020 08:18:00")]
    #[test_case("DateFormat(LocalDate(\"2020-03-04\"), \"yyyy-MM-dd HH\")" =>  "2020-03-04 01")]
    // #[test_case("NowSpecificTimeZone(\"Saratov Standard Time\")" => "16:39:57")]
    // #[test_case("Today()" => "---")]
    // #[test_case("Time()" => "---")]
    fn execute_some_real_world_expression(expression: &str) -> String {
        let funcs = get_functions();
        let op = f_operators;
        parse_exec_expr(expression, &funcs, &IdentifierValues::new(), Rc::new(op))
    }

    #[test]
    fn non_ascii_test() {
        let expr = "Substitute(\"ta mère !\", \"mère !\", \"frêre ?\")";
        assert_eq!(parse_exec_expr_with_defaults(expr), "ta frêre ?");
    }

    fn parse_exec_expr_with_defaults<'a>(expression: &'a str) -> String {
        parse_exec_expr(expression, &get_functions(), &IdentifierValues::new(), Rc::new(f_operators))
    }

    fn parse_exec_expr<'a>(expression: &'a str, funcs: &FunctionImplList, values: &IdentifierValues, operators: BinaryOperatorsImplRc) -> String {
        let expr = parse_expr(expression).unwrap();
        let expr = prepare_expr_and_identifiers(expr, funcs, operators);
        let result = exec_expr(&expr.expr, values).unwrap();
        result.to_string()
    }

    #[test]
    fn deterministic_operations() {
        assert_eq!(Deterministic + Deterministic, Deterministic);
        assert_eq!(NonDeterministic + Deterministic, NonDeterministic);
        assert_eq!(Deterministic + NonDeterministic, NonDeterministic);
        assert_eq!(NonDeterministic + NonDeterministic, NonDeterministic);
        let mut d = FunctionDeterminism::default();
        assert_eq!(d, Deterministic);
        d += Deterministic;
        assert_eq!(d, Deterministic);
        d += NonDeterministic;
        assert_eq!(d, NonDeterministic);
        d += NonDeterministic;
        assert_eq!(d, NonDeterministic);
        d += Deterministic;
        assert_eq!(d, NonDeterministic);
        d += Deterministic;
        assert_eq!(d, NonDeterministic);
    }

    #[test_case("Substitute(\"ta mere !\", \"mere !\", \"frere ?\")" => true)]
    #[test_case("Substitute(\"ta mere !\", \"mere !\", Now(42))" => false)]
    #[test_case("Time(42)" => false)]
    #[test_case("Upper(Today(42))" => false)]
    #[test_case("Upper(\"\")" => true)]
    #[test_case("Upper(Sum(2, 4))" => true)]
    #[test_case("Upper(Sum(2, now(42)))" => false)]
    #[test_case("Upper(Unkkkkkknown(2, now(42)))" => true)] // this one will always fail before calling now(), so it's determinist
    #[test_case("now(42)" => false)]
    #[test_case("1 + now(42)" => false)]
    #[test_case("LocalDate(\"2019-08-06\")" => true)]
    #[test_case("DateFormat(LocalDate(\"2023-09-19\"), \"yyyy-MM-dd HH:mm:ss\")" => true)]
    #[test_case("Upper(\"\") + 2" => true)]
    fn deterministic_or_not(expression: &str) -> bool {
        let expr = parse_expr(expression).unwrap();
        let expr = prepare_expr_and_identifiers(expr, &get_functions(), Rc::new(null_op));
        expr.determinism == Deterministic
    }

    #[test]
    fn partial_eq_test() {
        assert_eq!(AssocOp::Multiply, AssocOp::Multiply);
        assert_eq!(Expr::Num(dec!(1)), Expr::Num(dec!(1)));
        assert_eq!(
            Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(3))), RcExpr::new(Expr::Num(dec!(5))), AssocOp::Divide),
            Expr::BinaryOperator(RcExpr::new(Expr::Num(dec!(3))), RcExpr::new(Expr::Num(dec!(5))), AssocOp::Divide)
        );
    }

    fn null_op(l: RcExpr, r: RcExpr, op: AssocOp, _: &IdentifierValues) -> ExprFuncResult {
        dbg!(l, op, r, "RETURNS Null (null_op)");
        Ok(ExprResult::Null)
    }
}
