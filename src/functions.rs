use crate::expressions::*;
use std::rc::Rc;

fn ok_result(expr: Expr) -> ExprFuncResult {
    Ok(Rc::new(expr))
}

// fn is_null(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
//     let len = params.len();
//     if len == 0 {
//         return ok_result(Expr::Boolean(true));
//     }
//     if len == 1 {
//         return expr_is_null(params.get(0).unwrap(), values);
//     }

//     todo!("limit parameters attribute");
//     // {

//     // }else

//     // Ok(Rc::new(Expr::Boolean(true)))
// }

// fn expr_is_null(expr: &Expr, values: &IdentifierValues) -> ExprFuncResult {
//     match expr {
//         Expr::Str(s) => ok_result(Expr::Boolean(s.is_empty())),
//         Expr::Boolean(b) => ok_result(Expr::Boolean(false)),
//         Expr::Num(n) => ok_result(Expr::Boolean(false)),
//         Expr::Array(_) => "Array".to_string(),
//         Expr::Identifier(i) => format!("[{}]", i),
//         // Expr::Identifier(name) => match &values.get(name) {
//         //     Some(s) => s.to_string(),
//         //     None => format!("Unable to find value for identifier named '{}'", name),
//         // },
//         // Expr::BinaryOperator(_, _, _) => Ok(expr),
//         Expr::FunctionCall(_, _) => "FunctionCall".to_string(),
//         Expr::PreparedFunctionCall(_, _, _) => "PreparedFunctionCall".to_string(),
//     }
// }
