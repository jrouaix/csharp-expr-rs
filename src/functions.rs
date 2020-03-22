use crate::expressions::*;
use chrono::{prelude::*, Duration};
use num_format::{Locale, ToFormattedString};
use regex::{Regex, RegexBuilder};
use std::rc::Rc;

fn ok_result(expr: Expr) -> ExprFuncResult {
    Ok(Rc::new(expr))
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

fn expr_to_string(expr: &Expr) -> Result<String, String> {
    if expr.is_final() {
        Ok(expr.to_string())
    } else {
        Err("Can't change this expression to string".to_string())
    }
}

fn exec_expr_to_string(expr: &RcExpr, values: &IdentifierValues) -> Result<String, String> {
    let res = exec_expr(expr, values)?;
    expr_to_string(&res)
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
    lazy_static! {
        static ref TRUE_STRING: Regex = RegexBuilder::new("^\\s*(true|1)\\s*$").case_insensitive(true).build().unwrap();
    }
    let res = exec_expr(expr, values)?;
    match &*res {
        Expr::Boolean(b) => Ok(*b),
        Expr::Num(n) => Ok(*n == 1 as ExprDecimal),
        Expr::Str(s) => Ok(TRUE_STRING.is_match(&*s)),
        _ => Err(format!("'{}' is not a boolean", expr)),
    }
}

fn exec_expr_to_date_no_defaults(expr: &RcExpr, values: &IdentifierValues) -> Result<DateTime<Utc>, String> {
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
) -> Result<DateTime<Utc>, String> {
    let res = exec_expr(expr, values)?;
    let mut date_time = match &*res {
        Expr::Date(d) => *d,
        e => {
            let text = expr_to_string(&e)?;
            text.parse::<DateTime<Utc>>().map_err(|e| format!("{}", e))?
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

/*

/// <summary>
   /// return the date from value
   /// </summary>
   private static Result ObjectToDateResult(
       object text,
       bool defaultYear = false,
       bool defaultMonth = false,
       bool defaultDay = false,
       bool defaultHour = false,
       bool defaultMinute = false,
       bool defaultSecond = false)
   {
       return new Result(() =>
       {
           if (Result.IsObjError(text)) return text;
           if (text is DateTime) return text;

           var stringValue = ObjectToString(text);

           DateTime date;
           if (DateTime.TryParse(stringValue, CultureInfo.InvariantCulture, DateTimeStyles.AssumeUniversal | DateTimeStyles.AdjustToUniversal, out date))
           {
               date = new DateTime(
               defaultYear ? 1 : date.Year,
               defaultMonth ? 1 : date.Month,
               defaultDay ? 1 : date.Day,
               defaultHour ? 1 : date.Hour,
               defaultMinute ? 1 : date.Minute,
               defaultSecond ? 1 : date.Second,
               DateTimeKind.Utc);

               return date;
           };

           return new Error($"The value '{stringValue}' is not a date.");
       });
   }
   */

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

/**********************************/
/*          Regex helpers         */
/**********************************/

fn make_case_insensitive_search_regex(search_pattern: &str) -> Result<Regex, String> {
    let search_pattern = regex::escape(&search_pattern);
    let regex = RegexBuilder::new(&search_pattern)
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("{}", e))?;
    Ok(regex)
}

fn make_case_insensitive_equals_regex(search_pattern: &str) -> Result<Regex, String> {
    let search_pattern = regex::escape(&search_pattern);
    let search_pattern = format!("^{}$", search_pattern);
    let regex = RegexBuilder::new(&search_pattern)
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("{}", e))?;
    Ok(regex)
}

#[cfg(test)]
mod tests {
    use super::*;
    use test_case::test_case;
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
        // println!("{} {} => {}", c, previous_char.unwrap_or(' '), result);
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
    let regex = RegexBuilder::new(&regex_pattern)
        .case_insensitive(true)
        .build()
        .map_err(|e| format!("{}", e))?;
    Ok(regex)
}

/**********************************/
/*          Functions list        */
/**********************************/

pub fn get_functions() -> FunctionImplList {
    let mut funcs = FunctionImplList::new();
    funcs.insert("IsNull".to_string(), Rc::new(f_is_null));
    funcs.insert("IsBlank".to_string(), Rc::new(f_is_null));
    funcs.insert("AreEquals".to_string(), Rc::new(f_are_equals));
    funcs.insert("In".to_string(), Rc::new(f_in));
    funcs.insert("InLike".to_string(), Rc::new(f_in_like));
    funcs.insert("IsLike".to_string(), Rc::new(f_is_like));
    funcs.insert("Like".to_string(), Rc::new(f_is_like));
    funcs.insert("FirstNotNull".to_string(), Rc::new(f_first_not_null));
    funcs.insert("FirstNotEmpty".to_string(), Rc::new(f_first_not_null));
    funcs.insert("Concatenate".to_string(), Rc::new(f_concat));
    funcs.insert("Concat".to_string(), Rc::new(f_concat));
    funcs.insert("Exact".to_string(), Rc::new(f_exact));
    funcs.insert("Find".to_string(), Rc::new(f_find));
    funcs.insert("Substitute".to_string(), Rc::new(f_substitute));
    funcs.insert("Fixed".to_string(), Rc::new(f_fixed));
    funcs.insert("Left".to_string(), Rc::new(f_left));
    funcs.insert("Right".to_string(), Rc::new(f_right));
    funcs.insert("Mid".to_string(), Rc::new(f_mid));
    funcs.insert("Len".to_string(), Rc::new(f_len));
    funcs.insert("Lower".to_string(), Rc::new(f_lower));
    funcs.insert("Upper".to_string(), Rc::new(f_upper));
    funcs.insert("Trim".to_string(), Rc::new(f_trim));
    funcs.insert("FirstWord".to_string(), Rc::new(f_first_word));
    funcs.insert("FirstSentence".to_string(), Rc::new(f_first_sentence));
    funcs.insert("Capitalize".to_string(), Rc::new(f_capitalize));
    funcs.insert("Split".to_string(), Rc::new(f_split));
    funcs.insert("NumberValue".to_string(), Rc::new(f_number_value));
    funcs.insert("Text".to_string(), Rc::new(f_text));
    funcs.insert("StartsWith".to_string(), Rc::new(f_starts_with));
    funcs.insert("EndsWith".to_string(), Rc::new(f_ends_with));
    funcs.insert("ReplaceEquals".to_string(), Rc::new(f_replace_equals));
    funcs.insert("ReplaceLike".to_string(), Rc::new(f_replace_like));
    funcs.insert("And".to_string(), Rc::new(f_and));
    funcs.insert("Or".to_string(), Rc::new(f_or));
    funcs.insert("Not".to_string(), Rc::new(f_not));
    funcs.insert("Xor".to_string(), Rc::new(f_xor));
    funcs.insert("Iif".to_string(), Rc::new(f_iif));
    funcs.insert("If".to_string(), Rc::new(f_iif));
    funcs.insert("Abs".to_string(), Rc::new(f_abs));
    funcs.insert("Product".to_string(), Rc::new(f_product));
    funcs.insert("Sum".to_string(), Rc::new(f_sum));
    funcs.insert("Divide".to_string(), Rc::new(f_divide));
    funcs.insert("Subtract".to_string(), Rc::new(f_subtract));
    funcs.insert("Mod".to_string(), Rc::new(f_mod));
    funcs.insert("Modulo".to_string(), Rc::new(f_mod));
    funcs.insert("Round".to_string(), Rc::new(f_round));
    funcs.insert("GreaterThan".to_string(), Rc::new(f_greater_than));
    funcs.insert("Gt".to_string(), Rc::new(f_greater_than));
    funcs.insert("LowerThan".to_string(), Rc::new(f_lower_than));
    funcs.insert("Lt".to_string(), Rc::new(f_lower_than));
    funcs.insert("GreaterThanOrEqual".to_string(), Rc::new(f_greater_than_or_equal));
    funcs.insert("Gtoe".to_string(), Rc::new(f_greater_than_or_equal));
    funcs.insert("LowerThanOrEqual".to_string(), Rc::new(f_lower_than_or_equal));
    funcs.insert("Ltoe".to_string(), Rc::new(f_lower_than_or_equal));
    funcs.insert("Date".to_string(), Rc::new(f_date));
    funcs.insert("Now".to_string(), Rc::new(f_now));
    funcs.insert("Year".to_string(), Rc::new(f_year));
    funcs.insert("Month".to_string(), Rc::new(f_month));
    funcs.insert("Day".to_string(), Rc::new(f_day));
    funcs.insert("DateDiff".to_string(), Rc::new(f_date_diff));
    funcs.insert("DateDiffHours".to_string(), Rc::new(f_date_diff_hours));
    funcs.insert("DateDiffDays".to_string(), Rc::new(f_date_diff_days));
    funcs.insert("DateDiffMonths".to_string(), Rc::new(f_date_diff_months));
    funcs.insert("DateAddHours".to_string(), Rc::new(f_date_add_hours));
    funcs.insert("DateAddDays".to_string(), Rc::new(f_date_add_days));
    funcs.insert("DateAddMonths".to_string(), Rc::new(f_date_add_months));
    funcs.insert("DateAddYears".to_string(), Rc::new(f_date_add_years));
    funcs.insert("LocalDate".to_string(), Rc::new(f_local_date));
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
    let search = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let regex = make_case_insensitive_like_regex(&search)?;
    for p in params.iter().skip(1) {
        let text = exec_expr_to_string(p, values)?;
        if regex.is_match(&text) {
            return ok_result(Expr::Boolean(true));
        }
    }
    ok_result(Expr::Boolean(false))
}

// IsLike, Like
fn f_is_like(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "IsLike")?;
    let text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let search = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let regex = make_case_insensitive_like_regex(&search)?;
    ok_result(Expr::Boolean(regex.is_match(&text)))
}

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
        result.push_str(&s);
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
    let regex = make_case_insensitive_search_regex(&find_text)?;

    let within_text = exec_expr_to_string(params.get(1).unwrap(), values)?;
    println!("{}", find_text);
    let position = match regex.find_at(&within_text, start_num) {
        None => 0,                // 0 for not found
        Some(m) => m.start() + 1, // because it's a Excel function and 1 based enumeration
    };
    ok_result(Expr::Num(position as ExprDecimal))
}

// Substitute
fn f_substitute(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 3, "Substitute")?;

    let within_text = exec_expr_to_string(params.get(0).unwrap(), values)?;
    let find_text = exec_expr_to_string(params.get(1).unwrap(), values)?;
    let replace_text = exec_expr_to_string(params.get(2).unwrap(), values)?;

    let regex = make_case_insensitive_search_regex(&find_text)?;
    let replaced = regex.replace_all(&within_text, move |_c: &regex::Captures| replace_text.clone());

    ok_result(Expr::Str(replaced.into()))
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

// Trim
fn f_trim(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Trim", |s| ok_result(Expr::Str(s.trim().to_string())))
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

// Text
fn f_text(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_string_func(params, values, "Text", |s| ok_result(Expr::Str(s)))
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
    let parts: Vec<&str> = s.split(&separator).collect();
    let result = match parts.get(index) {
        None => Expr::Null,
        Some(p) => Expr::Str(p.to_string()),
    };
    ok_result(result)
}

// NumberValue
fn f_number_value(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_min_params_count(params, 1, "NumberValue")?;
    assert_max_params_count(params, 2, "NumberValue")?;
    let separator = match params.get(1) {
        None => None,
        Some(expr) => exec_expr_to_string(expr, values)?.chars().next(),
    };
    let number = exec_expr_to_num(params.get(0).unwrap(), values, separator)?;
    ok_result(Expr::Num(number))
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
        println!("{:?} {:?}", t, s);
        match (s, t) {
            (None, None) => return ok_result(Expr::Boolean(true)),
            (None, Some(_)) => return ok_result(Expr::Boolean(true)),
            (Some(_), None) => return ok_result(Expr::Boolean(false)),
            (Some(vs), Some(vt)) => {
                if !vs.to_lowercase().eq(vt.to_lowercase()) {
                    return ok_result(Expr::Boolean(false));
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
        println!("{:?} {:?}", t, s);
        match (s, t) {
            (None, None) => return ok_result(Expr::Boolean(true)),
            (None, Some(_)) => return ok_result(Expr::Boolean(true)),
            (Some(_), None) => return ok_result(Expr::Boolean(false)),
            (Some(vs), Some(vt)) => {
                if !vs.to_lowercase().eq(vt.to_lowercase()) {
                    return ok_result(Expr::Boolean(false));
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
            return ok_result(Expr::Boolean(false));
        }
    }
    ok_result(Expr::Boolean(true))
}

// Or
fn f_or(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    for expr in params {
        let b = exec_expr_to_bool(expr, values)?;
        if b {
            return ok_result(Expr::Boolean(true));
        }
    }
    ok_result(Expr::Boolean(false))
}

// Not
fn f_not(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 1, "Not")?;
    ok_result(Expr::Boolean(!exec_expr_to_bool(params.get(0).unwrap(), values)?))
}

// Xor
fn f_xor(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Xor")?;
    let p0 = exec_expr_to_bool(params.get(0).unwrap(), values)?;
    let p1 = exec_expr_to_bool(params.get(1).unwrap(), values)?;
    ok_result(Expr::Boolean(p0 ^ p1))
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
    ok_result(Expr::Num(num.abs()))
}

// Product
fn f_product(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = 1 as ExprDecimal;
    for expr in params.iter() {
        let i = exec_expr_to_num(expr, values, None)?;
        let intermediate_result = result;
        result = std::panic::catch_unwind(|| intermediate_result * i)
            .map_err(|_| format!("Couldn't multiply {} by {} : overflow", result, i).to_string())?;
    }
    ok_result(Expr::Num(result))
}

// Sum
fn f_sum(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    let mut result = 0 as ExprDecimal;
    for expr in params.iter() {
        let i = exec_expr_to_num(expr, values, None)?;
        let intermediate_result = result;
        result =
            std::panic::catch_unwind(|| intermediate_result + i).map_err(|_| format!("Couldn't add {} to {} : overflow", i, result).to_string())?;
    }
    ok_result(Expr::Num(result))
}

// Divide
fn f_divide(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Divide")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let divisor = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num / divisor).map_err(|_| format!("Couldn't divide {} by {}", num, divisor).to_string())?;
    ok_result(Expr::Num(result))
}

// Subtract
fn f_subtract(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Subtract")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let sub = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num - sub).map_err(|_| format!("Couldn't remove {} from {}", sub, num).to_string())?;
    ok_result(Expr::Num(result))
}

// Mod, Modulo
fn f_mod(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Mod")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let divisor = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let result = std::panic::catch_unwind(|| num % divisor).map_err(|_| format!("Couldn't module {} by {}", num, divisor).to_string())?;
    ok_result(Expr::Num(result))
}

// Round
fn f_round(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "Round")?;
    let num = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let digits = exec_expr_to_int(params.get(1).unwrap(), values)?.max(0) as u32;
    let mult_div = (10 as u32).pow(digits) as ExprDecimal;
    let result = std::panic::catch_unwind(|| (num * mult_div).round() / mult_div)
        .map_err(|_| format!("Couldn't round {} to {} digits", num, digits).to_string())?;
    ok_result(Expr::Num(result))
}

fn simple_operator<F: FnOnce(ExprDecimal, ExprDecimal) -> ExprFuncResult>(
    params: &VecRcExpr,
    values: &IdentifierValues,
    f_name: &str,
    func: F,
) -> ExprFuncResult {
    assert_exact_params_count(params, 2, f_name)?;
    let num_a = exec_expr_to_num(params.get(0).unwrap(), values, None)?;
    let num_b = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    func(num_a, num_b)
}

// GreaterThan, Gt
fn f_greater_than(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "GreaterThan", |a, b| ok_result(Expr::Boolean(a > b)))
}

// LowerThan, Lt
fn f_lower_than(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "LowerThan", |a, b| ok_result(Expr::Boolean(a < b)))
}

// GreaterThanOrEqual, Gtoe
fn f_greater_than_or_equal(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "GreaterThanOrEqual", |a, b| ok_result(Expr::Boolean(a >= b)))
}

// LowerThanOrEqual, Ltoe
fn f_lower_than_or_equal(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    simple_operator(params, values, "LowerThanOrEqual", |a, b| ok_result(Expr::Boolean(a <= b)))
}

/**********************************/
/*          DateTime              */
/**********************************/

// Now
fn f_now(params: &VecRcExpr, _values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 0, "Now")?;
    ok_result(Expr::Date(Utc::now()))
}

fn single_date_func<F: FnOnce(DateTime<Utc>) -> ExprFuncResult>(
    params: &VecRcExpr,
    values: &IdentifierValues,
    f_name: &str,
    func: F,
) -> ExprFuncResult {
    assert_exact_params_count(params, 1, f_name)?;
    let date = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    func(date)
}

// Date
fn f_date(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Date", |d| ok_result(Expr::Date(d)))
}

// Year
fn f_year(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Year", |d| ok_result(Expr::Num(d.year() as ExprDecimal)))
}

// Month
fn f_month(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Month", |d| ok_result(Expr::Num(d.month() as ExprDecimal)))
}

// Day
fn f_day(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    single_date_func(params, values, "Day", |d| ok_result(Expr::Num(d.day() as ExprDecimal)))
}

fn two_dates_func<F: FnOnce(DateTime<Utc>, DateTime<Utc>) -> ExprFuncResult>(
    params: &VecRcExpr,
    values: &IdentifierValues,
    f_name: &str,
    func: F,
) -> ExprFuncResult {
    assert_exact_params_count(params, 2, f_name)?;
    let date_left = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let date_right = exec_expr_to_date_no_defaults(params.get(1).unwrap(), values)?;
    func(date_left, date_right)
}

// DateDiff
fn f_date_diff(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateDiff", |d1, d2| ok_result(Expr::TimeSpan(d1 - d2)))
}

const SECONDS_IN_HOURS: ExprDecimal = 60 as ExprDecimal * 60 as ExprDecimal;
const SECONDS_IN_DAYS: ExprDecimal = SECONDS_IN_HOURS * 24 as ExprDecimal;
const SECONDS_IN_MONTHS: ExprDecimal = SECONDS_IN_DAYS * 30.5 as ExprDecimal;

//DateDiffHours
fn f_date_diff_hours(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateDiffHours", |d1, d2| {
        ok_result(Expr::Num((d1 - d2).num_seconds() as ExprDecimal / SECONDS_IN_HOURS))
    })
}

// DateDiffDays
fn f_date_diff_days(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateDiffDays", |d1, d2| {
        ok_result(Expr::Num((d1 - d2).num_seconds() as ExprDecimal / SECONDS_IN_DAYS))
    })
}

// DateDiffMonths
fn f_date_diff_months(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    two_dates_func(params, values, "DateDiffMonths", |d1, d2| {
        ok_result(Expr::Num((d1 - d2).num_seconds() as ExprDecimal / SECONDS_IN_MONTHS))
    })
}

// DateAddHours
fn f_date_add_hours(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddHours")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let hours = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let date_time = date_time + Duration::seconds((hours * SECONDS_IN_HOURS) as i64);
    ok_result(Expr::Date(date_time))
}

// DateAddDays
fn f_date_add_days(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddDays")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let days = exec_expr_to_num(params.get(1).unwrap(), values, None)?;
    let date_time = date_time + Duration::seconds((days * SECONDS_IN_DAYS) as i64);
    ok_result(Expr::Date(date_time))
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

    new_date_time =
        new_date_time
            .with_month0(new_month0 as u32)
            .ok_or(format!("Couldn't set {} as month to the date {}", new_month0 + 1, new_date_time))?;

    ok_result(Expr::Date(new_date_time))
}

// DateAddYears
fn f_date_add_years(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 2, "DateAddYears")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    let years = exec_expr_to_int(params.get(1).unwrap(), values)? as i32;

    let new_date_time = date_time
        .with_year(date_time.year() + years)
        .ok_or(format!("Couldn't add {} years to the date {}", years, date_time))?;

    ok_result(Expr::Date(new_date_time))
}

// LocalDate
fn f_local_date(params: &VecRcExpr, values: &IdentifierValues) -> ExprFuncResult {
    assert_exact_params_count(params, 1, "LocalDate")?;
    let date_time = exec_expr_to_date_no_defaults(params.get(0).unwrap(), values)?;
    todo!();
    ok_result(Expr::Date(date_time))
}
