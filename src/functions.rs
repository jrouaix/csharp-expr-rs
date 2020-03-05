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
        Err("Can't change this Expression to string".to_string())
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
pub fn f_is_null(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let res = is_null(params, values)?;
    Ok(Rc::new(Expr::Boolean(res)))
}

// AreEquals
pub fn f_are_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "AreEquals")?;
    let left = exec_expr(params.get(0).unwrap(), values)?;
    let right = exec_expr(params.get(1).unwrap(), values)?;
    let res = expr_are_equals(&left, &right);
    Ok(Rc::new(Expr::Boolean(res)))
}

// In
pub fn f_in(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "In")?;
    let search = exec_expr(params.get(0).unwrap(), values)?;
    for p in params.iter().skip(1) {
        let p_result = exec_expr(p, values)?;
        if expr_are_equals(&search, &p_result) {
            return Ok(Rc::new(Expr::Boolean(true)));
        }
    }
    return Ok(Rc::new(Expr::Boolean(false)));
}

// [ExpressionFunction(MiscCatName)]
// public static Result In(object value, params object[] possibleValues) => new Result(() => // => new Result(() => possibleValues.Any(v => ObjectIsEqualToResult(v, value)));
//     {
//         if (Result.IsObjError(value)) return value;

//         foreach (var test in possibleValues)
//         {
//             if (Result.IsObjError(test)) return test;

//             var equal = ObjectIsEqualToResult(test, value);

//             if (Result.IsObjError(equal)) return equal;

//             if (BoolValue(equal)) return true;
//         }

//         return false;
//     });

// [ExpressionFunction(MiscCatName)]
// public static Result InLike(object value, params object[] possibleLikeValues) => new Result(() => //  => new Result(() => possibleLikeValues.Any(v => ObjectIsLikeResult(value, v)));
//     {
//         if (Result.IsObjError(value)) return value;

//         foreach (var test in possibleLikeValues)
//         {
//             if (Result.IsObjError(test)) return test;

//             var like = ObjectIsLikeResult(value, test);

//             if (Result.IsObjError(like)) return like;

//             if (BoolValue(like)) return true;
//         }

//         return false;
//     });

// [ExpressionFunction(MiscCatName, "FirstNotEmpty")]
// public static Result FirstNotNull(params object[] values) => new Result(() =>
//     {
//         foreach (var v in values)
//         {
//             if (Result.IsObjError(v)) return v;

//             var isnull = ObjectIsNullResult(v);

//             if (Result.IsObjError(isnull)) return isnull;

//             if (!BoolValue(isnull)) return v;
//         }

//         return null;
//     });

// #endregion
