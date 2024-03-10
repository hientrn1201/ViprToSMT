use std::{
    fs::File,
    io::{self, BufRead, BufReader, Write},
};

pub fn normalize(filename: &str) -> io::Result<()> {
    let file = File::open(&filename)?;
    let reader = BufReader::new(file);
    let outfile = filename.trim_end_matches(".smt2").to_string() + "_norm.smt2";

    let mut fout = File::create(&outfile)?;

    for line in reader.lines() {
        let line = line.expect("Failed to read line");
        let mut words = line.split_whitespace();

        while let Some(word) = words.next() {
            if word.len() > 1
                && word.chars().nth(0).unwrap() == '-'
                && word.chars().nth(1).unwrap().is_ascii_digit()
            {
                fout.write_all(b"(- ")
                    .expect("Failed to write to output file");
                fout.write_all(word[1..].as_bytes())
                    .expect("Failed to write to output file");
                fout.write_all(b")")
                    .expect("Failed to write to output file");
            } else {
                fout.write_all(word.as_bytes())
                    .expect("Failed to write to output file");
            }
            fout.write_all(b" ")
                .expect("Failed to write to output file");
        }

        fout.write_all(b"\n")
            .expect("Failed to write to output file");

        if line.starts_with("(exit)") {
            break;
        }
    }
    Ok(())
}
