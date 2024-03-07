fn convert_normal(word: &str) -> String {
    format!("{}.0", word)
}

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

pub fn convert_sense_to_real(sense: &str) -> &str {
    match sense {
        "L" => "-1.0",
        "G" => "1.0",
        "E" => "0.0",
        _ => "0.0",
    }
}

pub fn convert_sense_to_sign(sense: &str) -> &str {
    match sense {
        "L" => "<=",
        "G" => ">=",
        "E" => "=",
        _ => "=",
    }
}
