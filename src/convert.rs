/// Converts a word to its corresponding real number representation.
/// If the word starts with a '-', it is treated as a negative number.
/// Otherwise, it is treated as a decimal number.
///
/// # Arguments
///
/// * `word` - The word to convert.
///
/// # Returns
///
/// The string representation of the converted real number.
fn convert_normal(word: &str) -> String {
    if word.starts_with('-') {
        format!("(- {})", convert_normal(&word[1..]))
    } else {
        format!("{}.0", word)
    }
}

/// Converts a word to its corresponding real number representation,
/// taking into account scientific notation.
///
/// # Arguments
///
/// * `word` - The word to convert.
///
/// # Returns
///
/// The string representation of the converted real number.
pub fn convert_to_real(word: &str) -> String {
    for (i, c) in word.chars().enumerate() {
        if c == 'E' || c == 'e' {
            let (left, right) = word.split_at(i);
            let p = right.trim_start_matches(c).parse::<i32>().unwrap();
            if p == 0 {
                return format!("{}.0", left);
            }
            if p > 0 {
                return format!("(* {} 1{}.0)", convert_normal(left), "0".repeat(p as usize));
            }
            return format!(
                "(/ {} 1{}.0)",
                convert_normal(left),
                "0".repeat((p * -1) as usize)
            );
        }
        if c == '/' {
            let (left, right) = word.split_at(i);
            return format!(
                "(/ {} {})",
                convert_normal(left),
                convert_normal(right.trim_start_matches(c))
            );
        }
    }
    convert_normal(word)
}

/// Converts a sense string to its corresponding real number representation.
///
/// # Arguments
///
/// * `sense` - The sense string to convert.
///
/// # Returns
///
/// The string representation of the converted sense.
pub fn convert_sense_to_real(sense: &str) -> &str {
    match sense {
        "L" => "(- 1.0)",
        "G" => "1.0",
        "E" => "0.0",
        _ => "0.0",
    }
}

/// Converts a sense string to its corresponding sign representation.
///
/// # Arguments
///
/// * `sense` - The sense string to convert.
///
/// # Returns
///
/// The string representation of the converted sign.
pub fn convert_sense_to_sign(sense: &str) -> &str {
    match sense {
        "L" => "<=",
        "G" => ">=",
        "E" => "=",
        _ => "=",
    }
}
