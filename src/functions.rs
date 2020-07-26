use crate::expressions::*;
use chrono::{prelude::*, Duration, TimeZone};
use chrono_tz::Tz;
use num_format::{Locale, ToFormattedString};
use regex::{Regex, RegexBuilder};
use rust_decimal::prelude::*;
use rust_decimal_macros::*;
use std::collections::HashMap;
use std::rc::Rc;
use unicase::UniCase;

fn exec_vec_is_null(params: &VecRcExpr, values: &IdentifierValues) -> Result<bool, String> {
    match params.len() {
        0 => Ok(true),
        1 => exec_expr_is_null(params.get(0).unwrap(), values),
        _ => Err("is_null only takes 0 or 1 parameter".to_string()),
    }
}

fn exec_expr_is_null(expr: &RcExpr, values: &IdentifierValues) -> Result<bool, String> {
    let res = exec_expr(expr, values)?;
    Ok(expr_result_is_null(&res))
}

fn expr_result_is_null(result: &ExprResult) -> bool {
    match result {
        ExprResult::Null => true,
        ExprResult::Str(s) => s.len() == 0 || s.chars().all(|c| is_space(c)),
        _ => false,
    }
}

fn results_are_equals(left: &ExprResult, right: &ExprResult) -> bool {
    match (left, right) {
        (ExprResult::Null, _) => false,
        (_, ExprResult::Null) => false,
        _ => left == right,
    }
}

fn result_to_string(expr: &ExprResult) -> Result<String, String> {
    if expr.is_final() {
        Ok(expr.to_string())
    } else {
        Err("Can't change this expression to string".to_string())
    }
}

fn exec_expr_to_string(expr: &RcExpr, values: &IdentifierValues) -> Result<String, String> {
    let res = exec_expr(expr, values)?;
    result_to_string(&res)
}

fn exec_expr_to_num(expr: &RcExpr, values: &IdentifierValues, decimal_separator: Option<char>) -> Result<ExprDecimal, String> {
    let res = exec_expr(expr, values)?;
    if let ExprResult::Num(n) = res {
        Ok(n)
    } else {
        let mut s = exec_expr_to_string(expr, values)?;
        // if s.len() == 0 {
        //     return Ok(dec!(0));
        // }
        if let Some(c) = decimal_separator {
            s = s.replace(c, ".")
        }
        let n: ExprDecimal = s.parse().or_else(|_| Err(format!("The value '{}' is not a number.", s)))?;
        Ok(n)
    }
}

fn exec_expr_to_float(expr: &RcExpr, values: &IdentifierValues, decimal_separator: Option<char>) -> Result<f64, String> {
    let num = exec_expr_to_num(expr, values, decimal_separator)?;
    num.to_f64().ok_or_else(|| "Error casting value to float.".to_string())
}

// fn exec_expr_to_int(expr: &RcExpr, values: &IdentifierValues, decimal_separator: Option<char>) -> Result<i64, String> {
//     let num = exec_expr_to_num(expr, values, decimal_separator)?;
//     num.to_i64().ok_or_else(|| "Error casting value to integer".to_string())
// }

fn exec_expr_to_int(expr: &RcExpr, values: &IdentifierValues) -> Result<isize, String> {
    let res = exec_expr(expr, values)?;
    match &res {
        ExprResult::Num(n) => Ok(n.to_isize().ok_or_else(|| "Error casting value to integer".to_string())?),
        ExprResult::Str(s) => Ok(s.parse::<isize>().or_else(|_| Err(format!("The value '{}' is not a integer.", s)))?),
        expr => Err(format!("The value '{}' is not a number, nor a string.", expr)),
    }
}

fn exec_expr_to_bool(expr: &RcExpr, values: &IdentifierValues) -> Result<bool, String> {
    lazy_static! {
        static ref TRUE_STRING: Regex = RegexBuilder::new("^\\s*(true|1)\\s*$").case_insensitive(true).build().unwrap();
    }
    let res = exec_expr(expr, values)?;
    match &res {
        ExprResult::Boolean(b) => Ok(*b),
        ExprResult::Num(n) => Ok(*n == dec!(1)),
        ExprResult::Str(s) => Ok(TRUE_STRING.is_match(&*s)),
        _ => Ok(false),
    }
}

fn exec_expr_to_date_no_defaults(expr: &RcExpr, values: &IdentifierValues) -> Result<NaiveDateTime, String> {
    exec_expr_to_date(expr, values, false, false, false, false, false, false)
}

fn exec_expr_to_date(
    expr: &RcExpr,
    values: &IdentifierValues,
    default_year: bool,
    default_month: bool,
    default_day: bool,
    default_hour: bool,
    default_minute: bool,
    default_second: bool,
) -> Result<NaiveDateTime, String> {
    let res = exec_expr(expr, values)?;
    let mut date_time = match &res {
        ExprResult::Date(d) => *d,
        e => {
            let text = result_to_string(&e)?.trim().to_string();
            // text.parse::<DateTime<Utc>>().map_err(|e| format!("{}", e))?.naive_utc()
            match text.parse::<DateTime<Utc>>() {
                Ok(dt) => return Ok(dt.naive_utc()),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match DateTime::parse_from_rfc2822(&text) {
                Ok(dt) => return Ok(dt.naive_utc()),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match text.parse::<NaiveDateTime>() {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y-%m-%d %H:%M:%S") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y/%m/%d %H:%M:%S") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y-%m-%d %H:%M:%S%.f") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y/%m/%d %H:%M:%S%.f") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y-%m-%d %H:%M") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    dbg!(&text, err);
                }
            }
            match NaiveDateTime::parse_from_str(&text, "%Y/%m/%d %H:%M") {
                Ok(dt) => return Ok(dt),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            match text.parse::<NaiveDate>() {
                Ok(dt) => return Ok(dt.and_hms(0, 0, 0)),
                Err(err) => {
                    //dbg!(&text, err);
                }
            }
            Err(format!("The value '{}' is not a date.", text))?
        }
    };

    if default_year {
        date_time = date_time.with_year(1).unwrap();
    }
    if default_month {
        date_time = date_time.with_month(1).unwrap();
    }
    if default_day {
        date_time = date_time.with_day(1).unwrap();
    }
    if default_hour {
        date_time = date_time.with_hour(1).unwrap();
    }
    if default_minute {
        date_time = date_time.with_minute(1).unwrap();
    }
    if default_second {
        date_time = date_time.with_second(1).unwrap();
    }
    Ok(date_time)
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

fn assert_between_params_count(params: &VecRcExpr, count_min: usize, count_max: usize, f_name: &str) -> Result<(), String> {
    let len = params.len();
    if len < count_min || len > count_max {
        Err(format!("Function {} should have between {} and {} parameters", f_name, count_min, count_max).to_string())
    } else {
        Ok(())
    }
}

/**********************************/
/*          Regex helpers         */
/**********************************/

fn make_case_insensitive_search_regex(search_pattern: &str) -> Result<Regex, String> {
    let search_pattern = regex::escape(&search_pattern);
    let regex = RegexBuilder::new(&search_pattern).case_insensitive(true).build().map_err(|e| format!("{}", e))?;
    Ok(regex)
}

fn make_case_insensitive_equals_regex(search_pattern: &str) -> Result<Regex, String> {
    let search_pattern = regex::escape(&search_pattern);
    let search_pattern = format!("^{}$", search_pattern);
    let regex = RegexBuilder::new(&search_pattern).case_insensitive(true).build().map_err(|e| format!("{}", e))?;
    Ok(regex)
}

fn like_pattern_to_regex_pattern(like_pattern: &str) -> String {
    let mut result = String::new();
    result.push('^');

    const ANY_MANY: &str = ".*";
    const ANY_ONE: &str = ".{1}";

    let mut previous_char = Option::<char>::default();
    for c in like_pattern.chars() {
        match (previous_char, c) {
            (None, '%') | (None, '_') => {
                previous_char = Some(c);
            }
            (None, _) => {
                result.push(c);
                previous_char = Some(c);
            }
            (Some('%'), '%') | (Some('_'), '_') => {
                result.push(c);
                previous_char = None;
            }
            (Some('%'), _) => {
                result.push_str(ANY_MANY);
                if c != '%' && c != '_' {
                    result.push(c);
                }
                previous_char = Some(c);
            }
            (Some('_'), _) => {
                result.push_str(ANY_ONE);
                if c != '%' && c != '_' {
                    result.push(c);
                }
                previous_char = Some(c);
            }
            (Some(_), '%') | (Some(_), '_') => {
                previous_char = Some(c);
            }
            (Some(_), _) => {
                result.push(c);
                previous_char = Some(c);
            }
        }
        // dbg!("{} {} => {}", c, previous_char.unwrap_or(' '), &result);
    }

    match previous_char {
        None => {}
        Some('%') => result.push_str(ANY_MANY),
        Some('_') => result.push_str(ANY_ONE),
        _ => {}
    }

    result.push('$');
    result
}

fn make_case_insensitive_like_regex(search_pattern: &str) -> Result<Regex, String> {
    let search_pattern = regex::escape(&search_pattern);
    let regex_pattern = like_pattern_to_regex_pattern(&search_pattern);
    let regex = RegexBuilder::new(&regex_pattern).case_insensitive(true).build().map_err(|e| format!("{}", e))?;
    Ok(regex)
}

/**********************************/
/*          Functions list        */
/**********************************/

pub fn get_functions() -> FunctionImplList {
    let mut funcs = FunctionImplList::new();
    funcs.insert(UniCase::new("IsNull".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_is_null)));
    funcs.insert(UniCase::new("IsBlank".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_is_null)));
    funcs.insert(UniCase::new("AreEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_are_equals)));
    funcs.insert(UniCase::new("In".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_in)));
    funcs.insert(UniCase::new("InLike".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_in_like)));
    funcs.insert(UniCase::new("IsLike".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_is_like)));
    funcs.insert(UniCase::new("Like".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_is_like)));
    funcs.insert(UniCase::new("FirstNotNull".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_first_not_null)));
    funcs.insert(UniCase::new("FirstNotEmpty".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_first_not_null)));
    funcs.insert(UniCase::new("Concatenate".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_concat)));
    funcs.insert(UniCase::new("Concat".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_concat)));
    funcs.insert(UniCase::new("Exact".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_exact)));
    funcs.insert(UniCase::new("Find".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_find)));
    funcs.insert(UniCase::new("Substitute".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_substitute)));
    funcs.insert(UniCase::new("Fixed".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_fixed)));
    funcs.insert(UniCase::new("Left".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_left)));
    funcs.insert(UniCase::new("Right".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_right)));
    funcs.insert(UniCase::new("Mid".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_mid)));
    funcs.insert(UniCase::new("Len".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_len)));
    funcs.insert(UniCase::new("Lower".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_lower)));
    funcs.insert(UniCase::new("Upper".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_upper)));
    funcs.insert(UniCase::new("Trim".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_trim)));
    funcs.insert(UniCase::new("FirstWord".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_first_word)));
    funcs.insert(UniCase::new("FirstSentence".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_first_sentence)));
    funcs.insert(UniCase::new("Capitalize".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_capitalize)));
    funcs.insert(UniCase::new("Split".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_split)));
    funcs.insert(UniCase::new("NumberValue".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_number_value)));
    funcs.insert(UniCase::new("Text".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_text)));
    funcs.insert(UniCase::new("StartsWith".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_starts_with)));
    funcs.insert(UniCase::new("EndsWith".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_ends_with)));
    funcs.insert(UniCase::new("ReplaceEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_replace_equals)));
    funcs.insert(UniCase::new("ReplaceLike".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_replace_like)));
    funcs.insert(UniCase::new("And".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_and)));
    funcs.insert(UniCase::new("Or".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_or)));
    funcs.insert(UniCase::new("Not".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_not)));
    funcs.insert(UniCase::new("Xor".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_xor)));
    funcs.insert(UniCase::new("Iif".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_iif)));
    funcs.insert(UniCase::new("If".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_iif)));
    funcs.insert(UniCase::new("Abs".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_abs)));
    funcs.insert(UniCase::new("Product".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_product)));
    funcs.insert(UniCase::new("Sum".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_sum)));
    funcs.insert(UniCase::new("Divide".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_divide)));
    funcs.insert(UniCase::new("Subtract".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_subtract)));
    funcs.insert(UniCase::new("Mod".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_mod)));
    funcs.insert(UniCase::new("Modulo".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_mod)));
    funcs.insert(UniCase::new("Round".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_round)));
    funcs.insert(UniCase::new("GreaterThan".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_greater_than)));
    funcs.insert(UniCase::new("Gt".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_greater_than)));
    funcs.insert(UniCase::new("LowerThan".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_lower_than)));
    funcs.insert(UniCase::new("Lt".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_lower_than)));
    funcs.insert(UniCase::new("GreaterThanOrEqual".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_greater_than_or_equal)));
    funcs.insert(UniCase::new("Gtoe".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_greater_than_or_equal)));
    funcs.insert(UniCase::new("LowerThanOrEqual".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_lower_than_or_equal)));
    funcs.insert(UniCase::new("Ltoe".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_lower_than_or_equal)));
    funcs.insert(UniCase::new("Date".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date)));
    funcs.insert(UniCase::new("Now".to_string()), (FunctionDeterminism::NonDeterministic, Rc::new(f_now)));
    funcs.insert(UniCase::new("Year".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_year)));
    funcs.insert(UniCase::new("Month".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_month)));
    funcs.insert(UniCase::new("Day".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_day)));
    funcs.insert(UniCase::new("DateDiff".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_diff)));
    funcs.insert(UniCase::new("DateDiffHours".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_diff_hours)));
    funcs.insert(UniCase::new("DateDiffDays".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_diff_days)));
    funcs.insert(UniCase::new("DateDiffMonths".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_diff_months)));
    funcs.insert(UniCase::new("DateEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_equals)));
    funcs.insert(UniCase::new("DateNotEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_not_equals)));
    funcs.insert(UniCase::new("DateLower".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_lower)));
    funcs.insert(UniCase::new("DateLowerOrEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_lower_or_equals)));
    funcs.insert(UniCase::new("DateGreater".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_greater)));
    funcs.insert(UniCase::new("DateGreaterOrEquals".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_greater_or_equals)));
    funcs.insert(UniCase::new("DateAddHours".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_add_hours)));
    funcs.insert(UniCase::new("DateAddDays".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_add_days)));
    funcs.insert(UniCase::new("DateAddMonths".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_add_months)));
    funcs.insert(UniCase::new("DateAddYears".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_add_years)));
    funcs.insert(UniCase::new("LocalDate".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_local_date)));
    funcs.insert(UniCase::new("DateFormat".to_string()), (FunctionDeterminism::Deterministic, Rc::new(f_date_format)));
    funcs.insert(UniCase::new("NowSpecificTimeZone".to_string()), (FunctionDeterminism::NonDeterministic, Rc::new(f_now_specific_timezone)));
    funcs.insert(UniCase::new("Today".to_string()), (FunctionDeterminism::NonDeterministic, Rc::new(f_today)));
    funcs.insert(UniCase::new("Time".to_string()), (FunctionDeterminism::NonDeterministic, Rc::new(f_time)));
    funcs
}

pub fn f_operators(left: RcExpr, right: RcExpr, op: AssocOp, values: &IdentifierValues) -> ExprFuncResult {
    match (op, left, right) {
        (AssocOp::Add, l, r) => f_sum(&vec![l, r], values),
        (AssocOp::Divide, l, r) => f_divide(&vec![l, r], values),
        (AssocOp::Equal, l, r) => f_are_equals(&vec![l, r], values),
        (AssocOp::Greater, l, r) => f_greater_than(&vec![l, r], values),
        (AssocOp::GreaterEqual, l, r) => f_greater_than_or_equal(&vec![l, r], values),
        (AssocOp::LAnd, l, r) => f_and(&vec![l, r], values),
        (AssocOp::Less, l, r) => f_lower_than(&vec![l, r], values),
        (AssocOp::LessEqual, l, r) => f_lower_than_or_equal(&vec![l, r], values),
        (AssocOp::LOr, l, r) => f_or(&vec![l, r], values),
        (AssocOp::Modulus, l, r) => f_mod(&vec![l, r], values),
        (AssocOp::Multiply, l, r) => f_product(&vec![l, r], values),
        (AssocOp::NotEqual, l, r) => f_are_not_equals(&vec![l, r], values),
        (AssocOp::Subtract, l, r) => f_subtract(&vec![l, r], values),
    }
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
    Ok(ExprResult::Boolean(res))
}

// AreEquals
fn f_are_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "AreEquals")?;
    let left = exec_expr(params.get(0).unwrap(), values)?;
    let right = exec_expr(params.get(1).unwrap(), values)?;
    let res = results_are_equals(&left, &right);
    Ok(ExprResult::Boolean(res))
}

// AreNotEquals
fn f_are_not_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "AreNotEquals")?;
    let left = exec_expr(params.get(0).unwrap(), values)?;
    let right = exec_expr(params.get(1).unwrap(), values)?;
    let res = results_are_equals(&left, &right);
    Ok(ExprResult::Boolean(!res))
}

// In
fn f_in(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "In")?;
    let search = exec_expr(params.get(0).unwrap(), values)?;
    for p in params.iter().skip(1) {
        let p_result = exec_expr(p, values)?;
        if results_are_equals(&search, &p_result) {
            return Ok(ExprResult::Boolean(true));
        }
    }
    return Ok(ExprResult::Boolean(false));
}

// InLike
fn f_in_like(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 2, "InLike")?;
    let search = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let regex = make_case_insensitive_like_regex(&search)?;
    for p in params.iter().skip(1) {
        let text = exec_expr_to_string(p, values)?;
        if regex.is_match(&text) {
            return Ok(ExprResult::Boolean(true));
        }
    }
    Ok(ExprResult::Boolean(false))
}

// IsLike, Like
fn f_is_like(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "IsLike")?;
    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let search = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let regex = make_case_insensitive_like_regex(&search)?;
    Ok(ExprResult::Boolean(regex.is_match(&text)))
}

fn f_first_not_null(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    for p in params.iter() {
        let p_result = exec_expr(p, values)?;
        if !expr_result_is_null(&p_result) {
            return Ok(p_result);
        }
    }
    Ok(ExprResult::Null)
}

/**********************************/
/*          Strings               */
/**********************************/

// Concatenate, Concat
fn f_concat(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = String::new();
    for p in params.iter() {
        let s = exec_expr_to_string(p, values)?;
        result.push_str(&s);
    }
    Ok(ExprResult::Str(result))
}

// Exact
fn f_exact(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Exact")?;
    let left = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let right = exec_expr_to_string(params.get(1).unwrap(), values)?;
    Ok(ExprResult::Boolean(left == right))
}

// Find
fn f_find(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 2, 3, "Find")?;
    let start_num: usize = match params.get(2) {
        None => 0,
        Some(epxr) => (exec_expr_to_int(epxr, values)? - 1).max(0) as usize,
    };

    let find_text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let regex = make_case_insensitive_search_regex(&find_text)?;

    let within_text = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let position = match regex.find_at(&within_text, start_num) {
        None => 0,                // 0 for not found
        Some(m) => m.start() + 1, // because it's a Excel function and 1 based enumeration
    };
    Ok(ExprResult::Num(ExprDecimal::from(position)))
}

// Substitute
fn f_substitute(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Substitute")?;

    let within_text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let find_text = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let replace_text = exec_expr_to_string(params.get(2).unwrap(), values)?;

    let regex = make_case_insensitive_search_regex(&find_text)?;
    let replaced = regex.replace_all(&within_text, move |_c: &regex::Captures| replace_text.clone());

    Ok(ExprResult::Str(replaced.into()))
}

// Fixed
fn f_fixed(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 1, 3, "Fixed")?;

    let number = exec_expr_to_num(params.get(0).unwrap(), values, None)?;

    let decimals = match params.get(1) {
        None => 2,
        Some(epxr) => exec_expr_to_int(epxr, values)?.max(0) as u32,
    };

    let number = number.round_dp_with_strategy(decimals, RoundingStrategy::RoundHalfDown);

    let no_commas = match params.get(2) {
        None => true,
        Some(epxr) => exec_expr_to_bool(epxr, values)?,
    };

    let result = if no_commas {
        format!("{num:.prec$}", num = number, prec = decimals as usize)
    } else {
        let int = number.trunc().to_isize().ok_or_else(|| "integer cast error".to_string())?.to_formatted_string(&Locale::en);
        let fract = format!("{num:.prec$}", num = number.fract(), prec = decimals as usize);
        let fract: Vec<&str> = fract.split(".").collect();
        let result = match fract.get(1) {
            Some(s) => format!("{}.{}", int, s),
            None => int,
        };
        result
    };
    Ok(ExprResult::Str(result))
}

// Left
fn f_left(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Left")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let size = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        Ok(ExprResult::Str("".to_string()))
    } else if size >= s.len() {
        Ok(ExprResult::Str(s))
    } else {
        Ok(ExprResult::Str(format!("{}", &s[..size])))
    }
}

// Right
fn f_right(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Right")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let size = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        Ok(ExprResult::Str("".to_string()))
    } else if size >= s.len() {
        Ok(ExprResult::Str(s))
    } else {
        Ok(ExprResult::Str(format!("{}", &s[s.len() - size..])))
    }
}

// Mid
fn f_mid(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Mid")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let false_position = exec_expr_to_int(params.get(1).unwrap(), values)?.max(1);
    let position = (false_position - 1) as usize;
    if position >= s.len() {
        return Ok(ExprResult::Str("".to_string()));
    }
    let size = exec_expr_to_int(params.get(2).unwrap(), values)?.max(0) as usize;
    if size == 0 {
        Ok(ExprResult::Str("".to_string()))
    } else if position == 0 && size >= s.len() {
        Ok(ExprResult::Str(s))
    } else {
        let end = (position + size).min(s.len());
        Ok(ExprResult::Str(format!("{}", &s[position..end])))
    }
}

fn single_string_func<F: FnOnce(String) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_exact_params_count(params, 1, f_name)?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    func(s)
}

// Len
fn f_len(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Len", |s| Ok(ExprResult::Num(ExprDecimal::from(s.len()))))
}

// Lower
fn f_lower(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Lower", |s| Ok(ExprResult::Str(s.to_lowercase())))
}

// Upper
fn f_upper(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Upper", |s| Ok(ExprResult::Str(s.to_uppercase())))
}

// Trim
fn f_trim(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Trim", |s| Ok(ExprResult::Str(s.trim().to_string())))
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
            None => Ok(ExprResult::Str(s)),
            Some(i) => Ok(ExprResult::Str(format!("{}", &s[..i]))),
        }
    })
}

// Text
fn f_text(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Text", |s| Ok(ExprResult::Str(s)))
}

// FirstSentence
fn f_first_sentence(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "FirstSentence", |s| {
        let position = s.chars().position(|c| is_sentence_punctuation(c));
        match position {
            None => Ok(ExprResult::Str(s)),
            Some(i) => Ok(ExprResult::Str(format!("{}", &s[..i + 1]))),
        }
    })
}

// Capitalize
fn f_capitalize(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Capitalize", |s| {
        let (_, result) = s.chars().into_iter().fold((true, String::with_capacity(s.capacity())), |state, c| {
            let (should_capitalize, mut s) = state;
            match (should_capitalize, is_sentence_punctuation(c), is_space(c)) {
                (false, end_sentence, _) => {
                    s.push(c);
                    (should_capitalize || end_sentence, s)
                }
                (true, _, true) => {
                    s.push(c);
                    (should_capitalize, s)
                }
                (true, _, false) => {
                    for u in c.to_uppercase() {
                        s.push(u);
                    }
                    (false, s)
                }
            }
        });

        Ok(ExprResult::Str(result))
    })
}

// Split
fn f_split(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Split")?;
    let s = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let separator = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let index = exec_expr_to_int(params.get(2).unwrap(), values)?.max(0) as usize;
    let parts: Vec<&str> = s.split(&separator).collect();
    let result = match parts.get(index) {
        None => ExprResult::Null,
        Some(p) => ExprResult::Str(p.to_string()),
    };
    Ok(result)
}

// NumberValue
fn f_number_value(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 1, 2, "NumberValue")?;
    let separator = match params.get(1) {
        None => None,
        Some(expr) => exec_expr_to_string(expr, values)?.chars().next(),
    };

    let number = exec_expr_to_num(params.get(0).unwrap(), values, separator)?;
    Ok(ExprResult::Num(number))
}

// StartsWith
fn f_starts_with(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "StartsWith")?;
    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let search = exec_expr_to_string(params.get(1).unwrap(), values)?;

    let mut t_iter = text.chars().into_iter();
    let mut s_iter = search.chars().into_iter();

    loop {
        let t = t_iter.next();
        let s = s_iter.next();
        match (s, t) {
            (None, None) => return Ok(ExprResult::Boolean(true)),
            (None, Some(_)) => return Ok(ExprResult::Boolean(true)),
            (Some(_), None) => return Ok(ExprResult::Boolean(false)),
            (Some(vs), Some(vt)) => {
                if !vs.to_lowercase().eq(vt.to_lowercase()) {
                    return Ok(ExprResult::Boolean(false));
                }
            }
        }
    }
    unreachable!();
}

// EndsWith
fn f_ends_with(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "EndsWith")?;
    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let search = exec_expr_to_string(params.get(1).unwrap(), values)?;

    let mut t_iter = text.chars().rev().into_iter();
    let mut s_iter = search.chars().rev().into_iter();

    loop {
        let t = t_iter.next();
        let s = s_iter.next();
        match (s, t) {
            (None, None) => return Ok(ExprResult::Boolean(true)),
            (None, Some(_)) => return Ok(ExprResult::Boolean(true)),
            (Some(_), None) => return Ok(ExprResult::Boolean(false)),
            (Some(vs), Some(vt)) => {
                if !vs.to_lowercase().eq(vt.to_lowercase()) {
                    return Ok(ExprResult::Boolean(false));
                }
            }
        }
    }
    unreachable!();
}

// ReplaceEquals
fn f_replace_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 4, "ReplaceEquals")?;
    if params.len() % 2 == 1 {
        return Err("Remplacement key/value parameters must come 2 by 2".to_string());
    }

    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let mut p_iter = params.iter().skip(2);
    loop {
        match (p_iter.next(), p_iter.next()) {
            (Some(pattern_expr), Some(replacement_expr)) => {
                let pattern = exec_expr_to_string(pattern_expr, values)?;
                let regex = make_case_insensitive_equals_regex(&pattern)?;

                if regex.is_match(&text) {
                    let replacement = exec_expr(replacement_expr, values);
                    return replacement;
                }
            }
            _ => break,
        }
    }

    let default = exec_expr(params.get(1).unwrap(), values);
    default
}

// ReplaceLike
fn f_replace_like(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 4, "ReplaceLike")?;
    if params.len() % 2 == 1 {
        return Err("Remplacement key/value parameters must come 2 by 2".to_string());
    }

    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let mut p_iter = params.iter().skip(2);
    loop {
        match (p_iter.next(), p_iter.next()) {
            (Some(pattern_expr), Some(replacement_expr)) => {
                let pattern = exec_expr_to_string(pattern_expr, values)?;
                let regex = make_case_insensitive_like_regex(&pattern)?;

                if regex.is_match(&text) {
                    let replacement = exec_expr(replacement_expr, values);
                    return replacement;
                }
            }
            _ => break,
        }
    }

    let default = exec_expr(params.get(1).unwrap(), values);
    default
}

/**********************************/
/*          Logical               */
/**********************************/

// And
fn f_and(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    for expr in params {
        let b = exec_expr_to_bool(expr, values)?;
        if !b {
            return Ok(ExprResult::Boolean(false));
        }
    }
    Ok(ExprResult::Boolean(true))
}

// Or
fn f_or(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    for expr in params {
        let b = exec_expr_to_bool(expr, values)?;
        if b {
            return Ok(ExprResult::Boolean(true));
        }
    }
    Ok(ExprResult::Boolean(false))
}

// Not
fn f_not(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 1, "Not")?;
    Ok(ExprResult::Boolean(!exec_expr_to_bool(params.get(0).unwrap(), values)?))
}

// Xor
fn f_xor(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Xor")?;
    let p0 = exec_expr_to_bool(params.get(0).unwrap(), values)?;
    let p1 = exec_expr_to_bool(params.get(1).unwrap(), values)?;
    Ok(ExprResult::Boolean(p0 ^ p1))
}

// Iif, If
fn f_iif(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Iif")?;
    let test = exec_expr_to_bool(params.get(0).unwrap(), values)?;
    exec_expr(params.get(if test { 1 } else { 2 }).unwrap(), values)
}

/**********************************/
/*          Math                  */
/**********************************/

// Abs
fn f_abs(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 1, "Abs")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    Ok(ExprResult::Num(num.abs()))
}

// Product
fn f_product(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = ExprDecimal::from(1);
    for expr in params.iter() {
        let i = exec_expr_to_num(expr, values, None)?;
        let intermediate_result = result;
        result = std::panic::catch_unwind(|| intermediate_result * i).map_err(|_| format!("Couldn't multiply {} by {} : overflow", result, i).to_string())?;
    }
    Ok(ExprResult::Num(result))
}

// Sum
fn f_sum(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = ExprDecimal::from(0);
    for expr in params.iter() {
        let i = exec_expr_to_num(expr, values, None)?;
        let intermediate_result = result;
        result = std::panic::catch_unwind(|| intermediate_result + i).map_err(|_| format!("Couldn't add {} to {} : overflow", i, result).to_string())?;
    }
    Ok(ExprResult::Num(result))
}

// Divide
fn f_divide(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Divide")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let divisor = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num / divisor).map_err(|_| format!("Couldn't divide {} by {}", num, divisor).to_string())?;
    Ok(ExprResult::Num(result))
}

// Subtract
fn f_subtract(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Subtract")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let sub = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num - sub).map_err(|_| format!("Couldn't remove {} from {}", sub, num).to_string())?;
    Ok(ExprResult::Num(result))
}

// Mod, Modulo
fn f_mod(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Mod")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let divisor = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num % divisor).map_err(|_| format!("Couldn't module {} by {}", num, divisor).to_string())?;
    Ok(ExprResult::Num(result))
}

// Round
fn f_round(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Round")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let digits = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as u32;
    let mult_div = ExprDecimal::from((10 as u32).pow(digits));
    let result = std::panic::catch_unwind(|| (num * mult_div).round() / mult_div).map_err(|_| format!("Couldn't round {} to {} digits", num, digits).to_string())?;
    Ok(ExprResult::Num(result))
}

fn simple_operator<F: FnOnce(ExprDecimal, ExprDecimal) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_exact_params_count(params, 2, f_name)?;
    let num_a = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let num_b = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    func(num_a, num_b)
}

// GreaterThan, Gt
fn f_greater_than(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "GreaterThan", |a, b| Ok(ExprResult::Boolean(a > b)))
}

// LowerThan, Lt
fn f_lower_than(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "LowerThan", |a, b| Ok(ExprResult::Boolean(a < b)))
}

// GreaterThanOrEqual, Gtoe
fn f_greater_than_or_equal(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "GreaterThanOrEqual", |a, b| Ok(ExprResult::Boolean(a >= b)))
}

// LowerThanOrEqual, Ltoe
fn f_lower_than_or_equal(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "LowerThanOrEqual", |a, b| Ok(ExprResult::Boolean(a <= b)))
}

/**********************************/
/*          DateTime              */
/**********************************/

// Now
fn f_now(params: &VecRcExpr, _values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 0, "Now")?;
    Ok(ExprResult::Date(Utc::now().naive_utc()))
}

// Today
fn f_today(params: &VecRcExpr, _values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 0, "Today")?;
    let date = NaiveDateTime::new(Utc::now().date().naive_utc(), NaiveTime::from_hms(0, 0, 0));
    Ok(ExprResult::Date(date))
}

// Time
fn f_time(params: &VecRcExpr, _values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 0, "Time")?;
    let duration = Utc::now().time().signed_duration_since(NaiveTime::from_hms(0, 0, 0));
    Ok(ExprResult::TimeSpan(duration))
}

// NowSpecificTimeZone
fn f_now_specific_timezone(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 0, 1, "NowSpecificTimeZone")?;

    let now = Utc::now().naive_utc();

    match params.get(0) {
        None => Ok(ExprResult::Date(now)),
        Some(expr) => {
            let time_zone_name = exec_expr_to_string(expr, values)?;
            naive_datetime_to_timezone(&now, &time_zone_name)
        }
    }
}

fn single_date_func<F: FnOnce(NaiveDateTime) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_exact_params_count(params, 1, f_name)?;
    let date = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    func(date)
}

// Date
fn f_date(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Date", |d| Ok(ExprResult::Date(d)))
}

// Year
fn f_year(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Year", |d| Ok(ExprResult::Num(ExprDecimal::from(d.year()))))
}

// Month
fn f_month(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Month", |d| Ok(ExprResult::Num(ExprDecimal::from(d.month()))))
}

// Day
fn f_day(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Day", |d| Ok(ExprResult::Num(ExprDecimal::from(d.day()))))
}

fn two_dates_func_no_defaults<F: FnOnce(NaiveDateTime, NaiveDateTime) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_exact_params_count(params, 2, f_name)?;
    let date_left = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let date_right = exec_expr_to_date_no_defaults(params.get(1).unwrap(), values)?;
    func(date_left, date_right)
}

fn two_dates_func<F: FnOnce(NaiveDateTime, NaiveDateTime) -> ExprFuncResult>(params: &VecRcExpr, values: &IdentifierValues, f_name: &str, func: F) -> ExprFuncResult {
    assert_between_params_count(params, 2, 8, f_name)?;

    let default_year = params.get(2).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;
    let default_month = params.get(3).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;
    let default_day = params.get(4).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;
    let default_hour = params.get(5).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;
    let default_minute = params.get(6).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;
    let default_second = params.get(7).map_or(Ok(false), |expr| exec_expr_to_bool(expr, values))?;

    let date_left = exec_expr_to_date(params.get(0).unwrap(), values, default_year, default_month, default_day, default_hour, default_minute, default_second)?;
    let date_right = exec_expr_to_date(params.get(1).unwrap(), values, default_year, default_month, default_day, default_hour, default_minute, default_second)?;
    func(date_left, date_right)
}

// DateDiff
fn f_date_diff(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func_no_defaults(params, values, "DateDiff", |d1, d2| Ok(ExprResult::TimeSpan(d1 - d2)))
}

pub const SECONDS_IN_MIN: i64 = 60;
pub const SECONDS_IN_HOURS: i64 = SECONDS_IN_MIN * 60;
pub const SECONDS_IN_DAYS: i64 = SECONDS_IN_HOURS * 24;
// pub const SECONDS_IN_MONTHS_size: f64 = SECONDS_IN_DAYS as f64 * 30.5_f64;

//DateDiffHours
fn f_date_diff_hours(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func_no_defaults(params, values, "DateDiffHours", |d1, d2| {
        let hours = ((d1 - d2).num_seconds() / SECONDS_IN_HOURS).abs();
        Ok(ExprResult::Num(ExprDecimal::from(hours)))
    })
}

// DateDiffDays
fn f_date_diff_days(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func_no_defaults(params, values, "DateDiffDays", |d1, d2| {
        let days = ((d1 - d2).num_seconds() / SECONDS_IN_DAYS).abs();
        Ok(ExprResult::Num(ExprDecimal::from(days)))
    })
}

// DateDiffMonths
fn f_date_diff_months(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func_no_defaults(params, values, "DateDiffMonths", |d1, d2| {
        let months = ((d1.month() as i32 - d2.month() as i32) + 12 * (d1.year() - d2.year())).abs();
        Ok(ExprResult::Num(ExprDecimal::from(months)))
    })
}

// DateEquals
fn f_date_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateEquals", |d1, d2| Ok(ExprResult::Boolean(d1 == d2)))
}

// DateNotEquals
fn f_date_not_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateNotEquals", |d1, d2| Ok(ExprResult::Boolean(d1 != d2)))
}

// DateLower
fn f_date_lower(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateLower", |d1, d2| Ok(ExprResult::Boolean(d1 < d2)))
}

// DateLowerOrEquals
fn f_date_lower_or_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateLowerOrEquals", |d1, d2| Ok(ExprResult::Boolean(d1 <= d2)))
}

// DateGreater
fn f_date_greater(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateGreater", |d1, d2| Ok(ExprResult::Boolean(d1 > d2)))
}

// DateGreaterOrEquals
fn f_date_greater_or_equals(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateGreaterOrEquals", |d1, d2| Ok(ExprResult::Boolean(d1 >= d2)))
}

// DateAddHours
fn f_date_add_hours(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddHours")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let hours = exec_expr_to_float(params.get(1).unwrap(), values, None)?;
    let date_time = date_time + Duration::seconds((hours * SECONDS_IN_HOURS as f64) as i64);
    Ok(ExprResult::Date(date_time))
}

// DateAddDays
fn f_date_add_days(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddDays")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let days = exec_expr_to_float(params.get(1).unwrap(), values, None)?;
    let date_time = date_time + Duration::seconds((days * SECONDS_IN_DAYS as f64) as i64);
    Ok(ExprResult::Date(date_time))
}

// DateAddMonths
fn f_date_add_months(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddMonths")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;

    let months = exec_expr_to_int(params.get(1).unwrap(), values)?;
    let month0 = date_time.month0() as i32 + (months as i32);
    let mut years_to_add = month0 / 12;
    let mut new_month0 = month0 % 12;
    if new_month0 < 0 {
        new_month0 = new_month0 + 12;
        years_to_add = years_to_add - 1;
    }

    let mut new_date_time = date_time
        .with_year(date_time.year() + years_to_add)
        .ok_or(format!("Couldn't add {} years to the date {}", years_to_add, date_time))?;

    new_date_time = new_date_time
        .with_month0(new_month0 as u32)
        .ok_or(format!("Couldn't set {} as month to the date {}", new_month0 + 1, new_date_time))?;

    Ok(ExprResult::Date(new_date_time))
}

// DateAddYears
fn f_date_add_years(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddYears")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let years = exec_expr_to_int(params.get(1).unwrap(), values)? as i32;

    let new_date_time = date_time.with_year(date_time.year() + years).ok_or(format!("Couldn't add {} years to the date {}", years, date_time))?;

    Ok(ExprResult::Date(new_date_time))
}

// LocalDate
fn f_local_date(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 1, 2, "LocalDate")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let time_zone_name = params.get(1).map_or(Ok("Romance Standard Time".into()), |expr| exec_expr_to_string(expr, values))?;
    naive_datetime_to_timezone(&date_time, &time_zone_name)
}

// DateFormat
fn f_date_format(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_between_params_count(params, 1, 2, "DateFormat")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let format = params.get(1).map_or(Ok("yyyy-MM-dd HH:mm:ss.fff".into()), |expr| exec_expr_to_string(expr, values))?;

    let format = dotnet_format_to_strptime_format(&format);
    let result = date_time.format(&format);

    Ok(ExprResult::Str(result.to_string()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;

    #[test_case("yyyy-MM-dd HH:mm:ss.fff" => "%Y-%m-%d %H:%M:%S.%3f")]
    fn test_dotnet_format_to_strptime_format(dotnet_format: &str) -> String {
        dotnet_format_to_strptime_format(dotnet_format)
    }

    #[test_case("abcd" => "^abcd$")]
    #[test_case("a_cd" => "^a.{1}cd$")]
    #[test_case("ab%d" => "^ab.*d$")]
    #[test_case("ab%%cd" => "^ab%cd$")]
    #[test_case("_abc" => "^.{1}abc$")]
    #[test_case("%abc" => "^.*abc$")]
    #[test_case("def_" => "^def.{1}$")]
    #[test_case("def%" => "^def.*$")]
    #[test_case("_O__%%___%%%O%" => "^.{1}O_%_.{1}%.*O.*$")]
    fn test_like_pattern_to_regex_pattern(like_pattern: &str) -> String {
        like_pattern_to_regex_pattern(like_pattern)
    }
}

fn dotnet_format_to_strptime_format(dotnet_format: &str) -> String {
    lazy_static! {
        static ref REPLACEMENTS: [(Regex, &'static str); 46] = [
            (Regex::new("dddd").unwrap(), "%A"),
            (Regex::new("ddd").unwrap(), "%a"),
            (Regex::new("dd").unwrap(), "%DAY"),
            (Regex::new("d").unwrap(), "%e"),
            (Regex::new("%DAY").unwrap(), "%d"),
            // Ok it's scrappy but (?<!%)d => Error
            // look-around, including look-ahead and look-behind, is not supported
            (Regex::new("fffffff").unwrap(), "%7f"),
            (Regex::new("ffffff").unwrap(), "%6f"),
            (Regex::new("fffff").unwrap(), "%5f"),
            (Regex::new("ffff").unwrap(), "%4f"),
            (Regex::new("fff").unwrap(), "%3f"),
            (Regex::new("ff").unwrap(), "%2f"),
            // (Regex::new("f").unwrap(), "%1f"), // Not supporting this one, no one uses it anyway
            (Regex::new("FFFFFFF").unwrap(), "%7f"),
            (Regex::new("FFFFFF").unwrap(), "%6f"),
            (Regex::new("FFFFF").unwrap(), "%5f"),
            (Regex::new("FFFF").unwrap(), "%4f"),
            (Regex::new("FFF").unwrap(), "%3f"),
            (Regex::new("FF").unwrap(), "%2f"),
            (Regex::new("F").unwrap(), "%1f"),
            (Regex::new("hh").unwrap(), "%I"),
            (Regex::new("h").unwrap(), "%l"),
            (Regex::new("HH").unwrap(), "%_OURS"),
            (Regex::new("H").unwrap(), "%k"),
            (Regex::new("%_OURS").unwrap(), "%H"),
            (Regex::new("mm").unwrap(), "%_INUTE"),  // same, kind of unsupported
            (Regex::new("m").unwrap(), "%_INUTE"),   // same, kind of unsupported
            (Regex::new("MMMM").unwrap(), "%B"),
            (Regex::new("MMM").unwrap(), "%b"),
            (Regex::new("MM").unwrap(), "%m"),
            (Regex::new("M").unwrap(), "%m"),
            (Regex::new("%_INUTE").unwrap(), "%M"),
            (Regex::new("%_INUTE").unwrap(), "%M"),
            (Regex::new("ss").unwrap(), "%S"),
            (Regex::new("s").unwrap(), "%S"),
            (Regex::new("tt").unwrap(), "%P"),
            (Regex::new("t").unwrap(), "%P"),
            (Regex::new("yyyyy").unwrap(), "%Y"),
            (Regex::new("yyyy").unwrap(), "%Y"),
            (Regex::new("yyy").unwrap(), "%Y"),
            (Regex::new("yy").unwrap(), "%YEAR"),
            (Regex::new("y").unwrap(), "%y"),
            (Regex::new("%YEAR").unwrap(), "%y"),
            (Regex::new("zzz").unwrap(), "%:_one"),
            (Regex::new("zz").unwrap(), "%_one"),
            (Regex::new("z").unwrap(), "%z"),
            (Regex::new("%_one").unwrap(), "%z"),
            (Regex::new("%:_one").unwrap(), "%:z"),
        ];
    }

    let result = REPLACEMENTS.iter().fold(dotnet_format.to_string(), |acc, replacer| {
        // let res = replacer.0.replace(&acc, replacer.1).to_string();
        // println!("{}", res);
        // res
        replacer.0.replace(&acc, replacer.1).to_string()
    });

    result
}

// Could be replaced by ? https://github.com/chronotope/chrono-tz/
fn get_utc_offset(time_zone_name: &str) -> Result<&'static Tz, String> {
    lazy_static! {
        static ref TIME_ZONES: HashMap<&'static str, Tz> = {
            let mut m = HashMap::new();
            m.insert("Dateline Standard Time", chrono_tz::Etc::GMTPlus12);
            m.insert("UTC-11", chrono_tz::Etc::GMTPlus11);
            m.insert("Aleutian Standard Time", chrono_tz::America::Adak);
            m.insert("Hawaiian Standard Time", chrono_tz::Pacific::Honolulu);
            m.insert("Marquesas Standard Time", chrono_tz::Pacific::Marquesas);
            m.insert("Alaskan Standard Time", chrono_tz::America::Anchorage);
            m.insert("UTC-09", chrono_tz::Etc::GMTPlus9);
            m.insert("Pacific Standard Time (Mexico)", chrono_tz::America::Tijuana);
            m.insert("UTC-08", chrono_tz::Etc::GMTPlus8);
            m.insert("Pacific Standard Time", chrono_tz::America::Los_Angeles);
            m.insert("US Mountain Standard Time", chrono_tz::America::Phoenix);
            m.insert("Mountain Standard Time (Mexico)", chrono_tz::America::Chihuahua);
            m.insert("Mountain Standard Time", chrono_tz::America::Denver);
            m.insert("Central America Standard Time", chrono_tz::America::Guatemala);
            m.insert("Central Standard Time", chrono_tz::America::Chicago);
            m.insert("Easter Island Standard Time", chrono_tz::Pacific::Easter);
            m.insert("Central Standard Time (Mexico)", chrono_tz::America::Mexico_City);
            m.insert("Canada Central Standard Time", chrono_tz::America::Regina);
            m.insert("SA Pacific Standard Time", chrono_tz::America::Bogota);
            m.insert("Eastern Standard Time (Mexico)", chrono_tz::America::Cancun);
            m.insert("Eastern Standard Time", chrono_tz::America::New_York);
            m.insert("Haiti Standard Time", chrono_tz::America::PortauPrince);
            m.insert("Cuba Standard Time", chrono_tz::America::Havana);
            m.insert("US Eastern Standard Time", chrono_tz::America::Indiana::Indianapolis);
            m.insert("Turks And Caicos Standard Time", chrono_tz::America::Grand_Turk);
            m.insert("Paraguay Standard Time", chrono_tz::America::Asuncion);
            m.insert("Atlantic Standard Time", chrono_tz::America::Halifax);
            m.insert("Venezuela Standard Time", chrono_tz::America::Caracas);
            m.insert("Central Brazilian Standard Time", chrono_tz::America::Cuiaba);
            m.insert("SA Western Standard Time", chrono_tz::America::La_Paz);
            m.insert("Pacific SA Standard Time", chrono_tz::America::Santiago);
            m.insert("Newfoundland Standard Time", chrono_tz::America::St_Johns);
            m.insert("Tocantins Standard Time", chrono_tz::America::Araguaina);
            m.insert("E. South America Standard Time", chrono_tz::America::Sao_Paulo);
            m.insert("SA Eastern Standard Time", chrono_tz::America::Cayenne);
            m.insert("Argentina Standard Time", chrono_tz::America::Argentina::Buenos_Aires);
            m.insert("Greenland Standard Time", chrono_tz::America::Godthab);
            m.insert("Montevideo Standard Time", chrono_tz::America::Montevideo);
            m.insert("Magallanes Standard Time", chrono_tz::America::Punta_Arenas);
            m.insert("Saint Pierre Standard Time", chrono_tz::America::Miquelon);
            m.insert("Bahia Standard Time", chrono_tz::America::Bahia);
            m.insert("UTC-02", chrono_tz::Etc::GMTPlus2);
            m.insert("Mid-Atlantic Standard Time", chrono_tz::Etc::GMTPlus2);
            m.insert("Azores Standard Time", chrono_tz::Atlantic::Azores);
            m.insert("Cape Verde Standard Time", chrono_tz::Atlantic::Cape_Verde);
            m.insert("UTC", chrono_tz::Etc::UTC);
            m.insert("GMT Standard Time", chrono_tz::Europe::London);
            m.insert("Greenwich Standard Time", chrono_tz::Atlantic::Reykjavik);
            m.insert("Sao Tome Standard Time", chrono_tz::Africa::Sao_Tome);
            m.insert("Morocco Standard Time", chrono_tz::Africa::Casablanca);
            m.insert("W. Europe Standard Time", chrono_tz::Europe::Berlin);
            m.insert("Central Europe Standard Time", chrono_tz::Europe::Budapest);
            m.insert("Romance Standard Time", chrono_tz::Europe::Paris);
            m.insert("Central European Standard Time", chrono_tz::Europe::Warsaw);
            m.insert("W. Central Africa Standard Time", chrono_tz::Africa::Lagos);
            m.insert("Jordan Standard Time", chrono_tz::Asia::Amman);
            m.insert("GTB Standard Time", chrono_tz::Europe::Bucharest);
            m.insert("Middle East Standard Time", chrono_tz::Asia::Beirut);
            m.insert("Egypt Standard Time", chrono_tz::Africa::Cairo);
            m.insert("E. Europe Standard Time", chrono_tz::Europe::Chisinau);
            m.insert("Syria Standard Time", chrono_tz::Asia::Damascus);
            m.insert("West Bank Standard Time", chrono_tz::Asia::Hebron);
            m.insert("South Africa Standard Time", chrono_tz::Africa::Johannesburg);
            m.insert("FLE Standard Time", chrono_tz::Europe::Kiev);
            m.insert("Israel Standard Time", chrono_tz::Asia::Jerusalem);
            m.insert("Kaliningrad Standard Time", chrono_tz::Europe::Kaliningrad);
            m.insert("Sudan Standard Time", chrono_tz::Africa::Khartoum);
            m.insert("Libya Standard Time", chrono_tz::Africa::Tripoli);
            m.insert("Namibia Standard Time", chrono_tz::Africa::Windhoek);
            m.insert("Arabic Standard Time", chrono_tz::Asia::Baghdad);
            m.insert("Turkey Standard Time", chrono_tz::Europe::Istanbul);
            m.insert("Arab Standard Time", chrono_tz::Asia::Riyadh);
            m.insert("Belarus Standard Time", chrono_tz::Europe::Minsk);
            m.insert("Russian Standard Time", chrono_tz::Europe::Moscow);
            m.insert("E. Africa Standard Time", chrono_tz::Africa::Nairobi);
            m.insert("Iran Standard Time", chrono_tz::Asia::Tehran);
            m.insert("Arabian Standard Time", chrono_tz::Asia::Dubai);
            m.insert("Astrakhan Standard Time", chrono_tz::Europe::Astrakhan);
            m.insert("Azerbaijan Standard Time", chrono_tz::Asia::Baku);
            m.insert("Russia Time Zone 3", chrono_tz::Europe::Samara);
            m.insert("Mauritius Standard Time", chrono_tz::Indian::Mauritius);
            m.insert("Saratov Standard Time", chrono_tz::Europe::Saratov);
            m.insert("Georgian Standard Time", chrono_tz::Asia::Tbilisi);
            m.insert("Volgograd Standard Time", chrono_tz::Europe::Volgograd);
            m.insert("Caucasus Standard Time", chrono_tz::Asia::Yerevan);
            m.insert("Afghanistan Standard Time", chrono_tz::Asia::Kabul);
            m.insert("West Asia Standard Time", chrono_tz::Asia::Tashkent);
            m.insert("Ekaterinburg Standard Time", chrono_tz::Asia::Yekaterinburg);
            m.insert("Pakistan Standard Time", chrono_tz::Asia::Karachi);
            m.insert("Qyzylorda Standard Time", chrono_tz::Asia::Qyzylorda);
            m.insert("India Standard Time", chrono_tz::Asia::Kolkata);
            m.insert("Sri Lanka Standard Time", chrono_tz::Asia::Colombo);
            m.insert("Nepal Standard Time", chrono_tz::Asia::Kathmandu);
            m.insert("Central Asia Standard Time", chrono_tz::Asia::Almaty);
            m.insert("Bangladesh Standard Time", chrono_tz::Asia::Dhaka);
            m.insert("Omsk Standard Time", chrono_tz::Asia::Omsk);
            m.insert("Myanmar Standard Time", chrono_tz::Asia::Yangon);
            m.insert("SE Asia Standard Time", chrono_tz::Asia::Bangkok);
            m.insert("Altai Standard Time", chrono_tz::Asia::Barnaul);
            m.insert("W. Mongolia Standard Time", chrono_tz::Asia::Hovd);
            m.insert("North Asia Standard Time", chrono_tz::Asia::Krasnoyarsk);
            m.insert("N. Central Asia Standard Time", chrono_tz::Asia::Novosibirsk);
            m.insert("Tomsk Standard Time", chrono_tz::Asia::Tomsk);
            m.insert("China Standard Time", chrono_tz::Asia::Shanghai);
            m.insert("North Asia East Standard Time", chrono_tz::Asia::Irkutsk);
            m.insert("Singapore Standard Time", chrono_tz::Asia::Singapore);
            m.insert("W. Australia Standard Time", chrono_tz::Australia::Perth);
            m.insert("Taipei Standard Time", chrono_tz::Asia::Taipei);
            m.insert("Ulaanbaatar Standard Time", chrono_tz::Asia::Ulaanbaatar);
            m.insert("Aus Central W. Standard Time", chrono_tz::Australia::Eucla);
            m.insert("Transbaikal Standard Time", chrono_tz::Asia::Chita);
            m.insert("Tokyo Standard Time", chrono_tz::Asia::Tokyo);
            m.insert("North Korea Standard Time", chrono_tz::Asia::Pyongyang);
            m.insert("Korea Standard Time", chrono_tz::Asia::Seoul);
            m.insert("Yakutsk Standard Time", chrono_tz::Asia::Yakutsk);
            m.insert("Cen. Australia Standard Time", chrono_tz::Australia::Adelaide);
            m.insert("AUS Central Standard Time", chrono_tz::Australia::Darwin);
            m.insert("E. Australia Standard Time", chrono_tz::Australia::Brisbane);
            m.insert("AUS Eastern Standard Time", chrono_tz::Australia::Sydney);
            m.insert("West Pacific Standard Time", chrono_tz::Pacific::Port_Moresby);
            m.insert("Tasmania Standard Time", chrono_tz::Australia::Hobart);
            m.insert("Vladivostok Standard Time", chrono_tz::Asia::Vladivostok);
            m.insert("Lord Howe Standard Time", chrono_tz::Australia::Lord_Howe);
            m.insert("Bougainville Standard Time", chrono_tz::Pacific::Bougainville);
            m.insert("Russia Time Zone 10", chrono_tz::Asia::Srednekolymsk);
            m.insert("Magadan Standard Time", chrono_tz::Asia::Magadan);
            m.insert("Norfolk Standard Time", chrono_tz::Pacific::Norfolk);
            m.insert("Sakhalin Standard Time", chrono_tz::Asia::Sakhalin);
            m.insert("Central Pacific Standard Time", chrono_tz::Pacific::Guadalcanal);
            m.insert("Russia Time Zone 11", chrono_tz::Asia::Kamchatka);
            m.insert("New Zealand Standard Time", chrono_tz::Pacific::Auckland);
            m.insert("UTC+12", chrono_tz::Etc::GMTMinus12);
            m.insert("Fiji Standard Time", chrono_tz::Pacific::Fiji);
            m.insert("Kamchatka Standard Time", chrono_tz::Asia::Kamchatka);
            m.insert("Chatham Islands Standard Time", chrono_tz::Pacific::Chatham);
            m.insert("UTC+13", chrono_tz::Etc::GMTMinus13);
            m.insert("Tonga Standard Time", chrono_tz::Pacific::Tongatapu);
            m.insert("Samoa Standard Time", chrono_tz::Pacific::Apia);
            m.insert("Line Islands Standard Time", chrono_tz::Pacific::Kiritimati);
            m
        };
    };

    if let Some(time_zone) = TIME_ZONES.get(time_zone_name) {
        Ok(time_zone)
    } else {
        Err(format!("Unable to find a time zone named '{}'", time_zone_name))
    }
}

fn naive_datetime_to_timezone(datetime: &NaiveDateTime, time_zone_name: &str) -> ExprFuncResult {
    let timezone = get_utc_offset(time_zone_name)?;
    let local = timezone.from_utc_datetime(datetime);
    dbg!(datetime, timezone, local);
    Ok(ExprResult::Date(local.naive_local()))
}
