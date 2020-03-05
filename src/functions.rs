use crate::expressions::*;
use std::rc::Rc;

fn ok_result(expr: Expr) -> ExprFuncResult {
    Ok(Rc::new(expr))
}

fn error_result(error: String) -> ExprFuncResult {
    Err(error)
}

fn is_null(params: &VecRcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let len = params.len();
    if len == 0 {
        return Ok(true);
    }
    if len == 1 {
        return expr_is_null(params.get(0).unwrap(), values);
    }
    Err("is_null only takes 0 or 1 parameter".to_string())
}

fn expr_is_null(expr: &RcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let res = exec_expr(expr, values)?;
    if let Expr::Null = *res {
        Ok(true)
    } else {
        Ok(false)
    }
}

fn expr_are_equals(left: &Expr, right: &Expr) -> bool {
    if let Expr::Null = *left {
        return false;
    }

    if let Expr::Null = *right {
        return false;
    }

    left == right
}

fn expr_to_string(expr: &RcExpr, values: &IdentifierValues) -> Result<String, String> {
    let res = exec_expr(expr, values)?;
    if res.is_final() {
        Ok(res.to_string())
    } else {
        Err("Can't change this expression to string".to_string())
    }
}

fn expr_to_num(expr: &RcExpr, values: &IdentifierValues, decimal_separator: Option<char>) -> Result<ExprDecimal, String> {
    let res = exec_expr(expr, values)?;
    if let Expr::Num(n) = *res {
        Ok(n)
    } else {
        let mut s = expr_to_string(expr, values)?;
        if let Some(c) = decimal_separator {
            s = s.replace(c, ".")
        }
        let n: ExprDecimal = s.parse().or_else(|_| Err(format!("Can't parse value {} to decimal", s)))?;
        Ok(n)
    }
}

fn assert_exact_params_count(params: &VecRcExpr, count: usize, f_name: &str) -> Result<(), String> {
    if params.len() == count {
        Ok(())
    } else {
        Err(format!("Function {} should have exactly {} parameters", f_name, count).to_string())
    }
}

fn assert_max_params_count(params: &VecRcExpr, count: usize, f_name: &str) -> Result<(), String> {
    if params.len() <= count {
        Ok(())
    } else {
        Err(format!("Function {} should have no more than {} parameters", f_name, count).to_string())
    }
}

fn assert_min_params_count(params: &VecRcExpr, count: usize, f_name: &str) -> Result<(), String> {
    if params.len() >= count {
        Ok(())
    } else {
        Err(format!("Function {} should have {} parameters or more", f_name, count).to_string())
    }
}

pub fn get_functions() -> FunctionImplList {
    let mut funcs = FunctionImplList::new();
    funcs.insert("IsNull".to_string(), Rc::new(f_is_null));
    funcs.insert("IsBlank".to_string(), Rc::new(f_is_null));
    funcs.insert("AreEquals".to_string(), Rc::new(f_are_equals));
    funcs.insert("In".to_string(), Rc::new(f_in));
    funcs.insert("InLike".to_string(), Rc::new(f_in_like));
    funcs.insert("FirstNotNull".to_string(), Rc::new(f_first_not_null));
    funcs.insert("FirstNotEmpty".to_string(), Rc::new(f_first_not_null));
    funcs.insert("Concatenate".to_string(), Rc::new(f_concat));
    funcs.insert("Concat".to_string(), Rc::new(f_concat));
    funcs
}

// #region Category names

// private const string MiscCatName = "Misc";
// private const string StringsCatName = "Strings";
// private const string LogicalCatName = "Logical";
// private const string MathCatName = "Math";
// private const string DateCatName = "DateTime";

// #endregion

/**********************************/
/*          Miscellaneous         */
/**********************************/

// IsNull, IsBlank
fn f_is_null(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let res = is_null(params, values)?;
    ok_result(Expr::Boolean(res))
}

// AreEquals
fn f_are_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "AreEquals")?;
    let left = exec_expr(params.get(0).unwrap(), values)?;
    let right = exec_expr(params.get(1).unwrap(), values)?;
    let res = expr_are_equals(&left, &right);
    ok_result(Expr::Boolean(res))
}

// In
fn f_in(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "In")?;
    let search = exec_expr(params.get(0).unwrap(), values)?;
    for p in params.iter().skip(1) {
        let p_result = exec_expr(p, values)?;
        if expr_are_equals(&search, &p_result) {
            return ok_result(Expr::Boolean(true));
        }
    }
    return ok_result(Expr::Boolean(false));
}

// InLike
fn f_in_like(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "In")?;
    let search = exec_expr(params.get(0).unwrap(), values)?;
    for p in params.iter().skip(1) {
        let p_result = exec_expr(p, values)?;
        todo!("SQL like");
        // if expr_like(&search, &p_result) {
        //     return ok_result(Expr::Boolean(true));
        // }
    }
    return ok_result(Expr::Boolean(false));
}

// FirstNotNull, FirstNotEmpty
fn f_first_not_null(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    for p in params.iter() {
        let p_result = exec_expr(p, values)?;
        match *p_result {
            Expr::Null => {}
            _ => return Ok(p_result),
        }
    }
    ok_result(Expr::Null)
}

/**********************************/
/*          Strings               */
/**********************************/

// Concatenate, Concat
fn f_concat(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = String::new();
    for p in params.iter() {
        let s = expr_to_string(p, values)?;
        result.push_str(&s[..]);
    }
    ok_result(Expr::Str(result))
}
