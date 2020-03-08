use crate::expressions::*;
use num_format::{Locale, ToFormattedString};
use regex::RegexBuilder;
use std::rc::Rc;

fn ok_result(expr: Expr) -> ExprFuncResult {
    Ok(Rc::new(expr))
}

fn error_result(error: String) -> ExprFuncResult {
    Err(error)
}

fn exec_vec_is_null(params: &VecRcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let len = params.len();
    if len == 0 {
        return Ok(true);
    }
    if len == 1 {
        return exec_expr_is_null(params.get(0).unwrap(), values);
    }
    Err("is_null only takes 0 or 1 parameter".to_string())
}

fn exec_expr_is_null(expr: &RcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let res = exec_expr(expr, values)?;
    Ok(if let Expr::Null = *res { true } else { false })
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

fn exec_expr_to_string(expr: &RcExpr, values: &IdentifierValues) -> Result<String, String> {
    let res = exec_expr(expr, values)?;
    if res.is_final() {
        Ok(res.to_string())
    } else {
        Err("Can't change this expression to string".to_string())
    }
}

fn exec_expr_to_num(expr: &RcExpr, values: &IdentifierValues, decimal_separator: Option<char>) -> Result<ExprDecimal, String> {
    let res = exec_expr(expr, values)?;
    if let Expr::Num(n) = *res {
        Ok(n)
    } else {
        let mut s = exec_expr_to_string(expr, values)?;
        if let Some(c) = decimal_separator {
            s = s.replace(c, ".")
        }
        let n: ExprDecimal = s.parse().or_else(|_| Err(format!("'{}' is not a number", s)))?;
        Ok(n)
    }
}

fn exec_expr_to_int(expr: &RcExpr, values: &IdentifierValues) -> Result<isize, String> {
    let res = exec_expr(expr, values)?;
    match &*res {
        Expr::Num(n) => Ok(*n as isize),
        Expr::Str(s) => Ok(s.parse::<isize>().or_else(|_| Err(format!("'{}' is not a number", s)))?),
        expr => Err(format!("'{}' is not a number", expr)),
    }
}

fn exec_expr_to_bool(expr: &RcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let res = exec_expr(expr, values)?;
    match &*res {
        Expr::Boolean(b) => Ok(*b),
        expr => Err(format!("'{}' is not a boolean", expr)),
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
    funcs.insert("Exact".to_string(), Rc::new(f_exact));
    funcs.insert("Find".to_string(), Rc::new(f_find));
    funcs.insert("Fixed".to_string(), Rc::new(f_fixed));
    funcs.insert("Left".to_string(), Rc::new(f_left));
    funcs.insert("Right".to_string(), Rc::new(f_right));
    funcs.insert("Mid".to_string(), Rc::new(f_mid));
    funcs.insert("Len".to_string(), Rc::new(f_len));
    funcs.insert("Lower".to_string(), Rc::new(f_lower));
    funcs.insert("Upper".to_string(), Rc::new(f_upper));
    funcs.insert("FirstWord".to_string(), Rc::new(f_first_word));
    funcs.insert("FirstSentence".to_string(), Rc::new(f_first_sentence));
    funcs.insert("Capitalize".to_string(), Rc::new(f_capitalize));
    funcs.insert("Split".to_string(), Rc::new(f_split));
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
    let res = exec_vec_is_null(params, values)?;
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
    assert_min_params_count(params, 2, "InLike")?;
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
        let s = exec_expr_to_string(p, values)?;
        result.push_str(&s[..]);
    }
    ok_result(Expr::Str(result))
}

// Exact
fn f_exact(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Exact")?;
    let left = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let right = exec_expr_to_string(params.get(1).unwrap(), values)?;
    ok_result(Expr::Boolean(left == right))
}

// Find
fn f_find(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "Find")?;
    assert_max_params_count(params, 3, "Find")?;
    let start_num: usize = match params.get(2) {
        None => 0,
        Some(epxr) => (exec_expr_to_int(epxr, values)? - 1).max(0) as usize,
    };

    let find_text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let find_text = regex::escape(&find_text[..]);
    let regex = RegexBuilder::new(&find_text[..])
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("{}", e))?;

    let within_text = exec_expr_to_string(params.get(1).unwrap(), values)?;
    println!("{}", find_text);
    let position = match regex.find_at(&within_text[..], start_num) {
        None => 0,                // 0 for not found
        Some(m) => m.start() + 1, // because it's a Excel function and 1 based enumeration
    };
    ok_result(Expr::Num(position as ExprDecimal))
}

// Fixed
fn f_fixed(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 1, "Fixed")?;
    assert_max_params_count(params, 3, "Fixed")?;

    let number = exec_expr_to_num(params.get(0).unwrap(), values, None)?;

    let decimals = match params.get(1) {
        None => 2,
        Some(epxr) => exec_expr_to_int(epxr, values)?.max(0) as usize,
    };
    let no_commas = match params.get(2) {
        None => true,
        Some(epxr) => exec_expr_to_bool(epxr, values)?,
    };

    let result = if no_commas {
        format!("{num:.prec$}", num = number, prec = decimals)
    } else {
        let int = (number.trunc() as isize).to_formatted_string(&Locale::en);
        let fract = format!("{num:.prec$}", num = number.fract(), prec = decimals);
        let fract: Vec<&str> = fract.split(".").collect();
        let result = match fract.get(1) {
            Some(s) => format!("{}.{}", int, s),
            None => int,
        };
        result
    };
    ok_result(Expr::Str(result))
}

// Left
fn f_left(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Left")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let size = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        ok_result(Expr::Str("".to_string()))
    } else if size >= s.len() {
        ok_result(Expr::Str(s))
    } else {
        ok_result(Expr::Str(format!("{}", &s[..size])))
    }
}

// Right
fn f_right(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Right")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let size = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        ok_result(Expr::Str("".to_string()))
    } else if size >= s.len() {
        ok_result(Expr::Str(s))
    } else {
        ok_result(Expr::Str(format!("{}", &s[s.len() - size..])))
    }
}

// Mid
fn f_mid(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Mid")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let false_position = exec_expr_to_int(params.get(1).unwrap(), values)?.max(1).min(s.len() as isize);
    let position = (false_position - 1) as usize;
    let size = exec_expr_to_int(params.get(2).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        ok_result(Expr::Str("".to_string()))
    } else if position == 0 && size >= s.len() {
        ok_result(Expr::Str(s))
    } else {
        let end = (position + size).min(s.len());
        ok_result(Expr::Str(format!("{}", &s[position..end])))
    }
}

fn single_string_func<F: FnOnce(String) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_exact_params_count(params, 1, f_name)?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    func(s)
}

// Len
fn f_len(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Len", |s| ok_result(Expr::Num(s.len() as ExprDecimal)))
}

// Lower
fn f_lower(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Lower", |s| ok_result(Expr::Str(s.to_lowercase())))
}

// Upper
fn f_upper(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Upper", |s| ok_result(Expr::Str(s.to_uppercase())))
}

fn is_punctuation(c: char) -> bool {
    c == '.' || c == ',' || c == '!' || c == '?' || c == '¿'
}
fn is_space(c: char) -> bool {
    c == ' ' || c == '\t' || c == '\r' || c == '\n'
}
fn is_sentence_punctuation(c: char) -> bool {
    c == '.' || c == '!' || c == '?'
}

// FirstWord
fn f_first_word(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "FirstWord", |s| {
        let position = s.chars().position(|c| is_space(c) || is_punctuation(c));
        match position {
            None => ok_result(Expr::Str(s)),
            Some(i) => ok_result(Expr::Str(format!("{}", &s[..i]))),
        }
    })
}

// FirstSentence
fn f_first_sentence(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "FirstSentence", |s| {
        let position = s.chars().position(|c| is_sentence_punctuation(c));
        match position {
            None => ok_result(Expr::Str(s)),
            Some(i) => ok_result(Expr::Str(format!("{}", &s[..i]))),
        }
    })
}

// Capitalize
fn f_capitalize(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Capitalize", |s| {
        todo!();
    })
}

// Split
fn f_split(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Split")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let separator = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let index = exec_expr_to_int(params.get(2).unwrap(), values)?.max(0) as usize;
    let parts: Vec<&str> = s.split(&separator[..]).collect();
    let result = match parts.get(index) {
        None => Expr::Null,
        Some(p) => Expr::Str(p.to_string()),
    };
    ok_result(result)
}
