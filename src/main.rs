mod cons_helper;
mod convert;

use cons_helper::{clean_up_cons, dom_cons, handle_last_cons, parse_cons};
use convert::{convert_sense_to_sign, convert_to_real};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, Read, Write};
use std::process::exit;

#[derive(Debug)]
struct Relation {
    sense: String,
    terms: HashSet<usize>,
}

fn main() -> io::Result<()> {
    println!("Enter a name:");
    let mut file_path = String::new();

    io::stdin()
        .read_line(&mut file_path)
        .expect("failed to readline");

    let filename = file_path.trim();

    let file = File::open(filename)?;
    let mut reader = io::BufReader::new(file);
    let outfile = filename.trim_end_matches(".vipr").to_string() + "_vipr.smt2";

    let mut fout = File::create(&outfile)?;
    writeln!(&mut fout, "(set-info :smt-lib-version 2.6)")?;
    writeln!(&mut fout, "(set-logic ALL)")?;
    writeln!(
        &mut fout,
        "(set-info :sourse |Transformed from an VIPR format problem|)"
    )?;
    writeln!(&mut fout, "; --- END HEADER ---")?;
    writeln!(&mut fout)?;

    writeln!(&mut fout, "(declare-fun xfalse () Bool)")?;
    writeln!(&mut fout, "(assert (not xfalse))")?;
    writeln!(&mut fout, "(declare-fun xtrue () Bool)")?;
    writeln!(&mut fout, "(assert xtrue)")?;

    let mut variables = Vec::new();
    let mut constraints = HashMap::new();
    let mut obj_func: Relation = Relation {
        sense: "".to_string(),
        terms: HashSet::new(),
    };
    let mut num_cons = 0;
    let mut num_bcons = 0;

    let mut infease = false;
    let mut lb = "";
    let mut ub = "";
    let mut list_sols = Vec::new();
    let mut asm_set = HashSet::new();

    // map con_ind to delete previous cons
    let mut delete_cons = HashMap::<usize, Vec<usize>>::new();

    // map con_ind to used asm
    let mut used_asm = HashMap::<usize, HashSet<usize>>::new();

    // Read the entire file content into a string
    let mut content = String::new();
    reader.read_to_string(&mut content)?;

    // Split the content by whitespace and newlines
    let contents: Vec<&str> = content
        .lines()
        .filter(|&line| {
            !line.trim().starts_with('%')
                && !line.trim().is_empty()
                && !line.trim().starts_with("VER")
        })
        .flat_map(|line| line.split_whitespace())
        .collect();

    // Iterate over numbers and print them
    let mut content_iter = contents.into_iter();
    while let Some(string) = content_iter.next() {
        match string {
            "VAR" => {
                let num_vars = content_iter.next().unwrap().parse::<usize>().unwrap();
                for _ in 0..num_vars {
                    let var_name = content_iter.next().unwrap();
                    variables.push("Real");
                }
            }
            "INT" => {
                let num_ints = content_iter.next().unwrap().parse::<usize>().unwrap();
                for _ in 0..num_ints {
                    let int_index = content_iter.next().unwrap().parse::<usize>().unwrap();
                    variables[int_index] = "Int";
                }
                for (i, var_type) in variables.iter().enumerate() {
                    writeln!(&mut fout, "(declare-fun x{} () {})", i, var_type)?;
                    writeln!(&mut fout, "(declare-fun is_intx{} () Bool)", i)?;
                    if *var_type == "Int" {
                        writeln!(&mut fout, "(assert is_intx{})", i)?;
                    } else {
                        writeln!(&mut fout, "(assert (not (is_intx{})))", i)?;
                    }
                }
            }
            "OBJ" => {
                let objsense = content_iter.next().unwrap();
                let num_objterms = content_iter.next().unwrap().parse::<usize>().unwrap();
                obj_func.sense = objsense.to_string();
                for _ in 0..num_objterms {
                    let var_index = content_iter.next().unwrap().parse::<usize>().unwrap();
                    let var_coeff = convert_to_real(content_iter.next().unwrap());
                    obj_func.terms.insert(var_index);
                    writeln!(&mut fout, "(declare-fun obj{} () Real)", var_index)?;
                    writeln!(&mut fout, "(assert (= obj{} {}))", var_index, var_coeff)?;
                }
            }
            "CON" => {
                num_cons = content_iter.next().unwrap().parse::<usize>().unwrap();
                num_bcons = content_iter.next().unwrap().parse::<usize>().unwrap();
                for i in 0..num_cons {
                    parse_cons(&mut content_iter, &mut constraints, &fout, i, &obj_func)?;
                }
            }
            "RTP" => {
                let s = content_iter.next().unwrap();
                if s == "infeas" {
                    infease = true;
                } else {
                    infease = false;
                    lb = content_iter.next().unwrap();
                    ub = content_iter.next().unwrap();
                    if (obj_func.sense == "min" && lb == "-inf")
                        || (obj_func.sense == "max" && ub == "inf")
                    {
                        println!("error in rtp");
                        exit(0);
                    }
                }
            }
            "SOL" => {
                let num_sol = content_iter.next().unwrap().parse::<usize>().unwrap();
                if (num_sol == 0 && infease == false) || (num_sol > 0 && infease == true) {
                    println!("error in sol");
                    exit(0);
                }
                for sol_ind in 0..num_sol {
                    content_iter.next(); // skip name
                    let mut ind_set = HashSet::new();
                    let num_vars = content_iter.next().unwrap().parse::<usize>().unwrap();
                    for _ in 0..num_vars {
                        let ind = content_iter.next().unwrap().parse::<usize>().unwrap();
                        let val = convert_to_real(content_iter.next().unwrap());
                        ind_set.insert(ind);
                        writeln!(&mut fout, "(declare-fun sol{}x{} () Real)", sol_ind, ind)?;
                        writeln!(&mut fout, "(assert (= sol{}x{} {}))", sol_ind, ind, val)?;
                    }

                    list_sols.push(ind_set.clone());
                    // assert constraints
                    for (cons_ind, cons) in constraints.iter() {
                        writeln!(
                            &mut fout,
                            "(assert ({} (+ {} 0.0 0.0) crhs{}))",
                            convert_sense_to_sign(&cons.sense),
                            cons.terms
                                .iter()
                                .filter(|ind| ind_set.contains(ind))
                                .map(|ind| format!(
                                    "(* c{}x{} sol{}x{})",
                                    cons_ind, ind, sol_ind, ind
                                ))
                                .collect::<Vec<String>>()
                                .join(" "),
                            cons_ind
                        )?;
                    }
                }
                // assert objective function,
                // make sure at least one solution is above the lower bound if max problem and vice versa
                writeln!(
                    &mut fout,
                    "(assert (or {} xfalse))",
                    list_sols
                        .iter()
                        .enumerate()
                        .map(|(ind_sol, ind_set)| {
                            format!(
                                "({} (+ {} 0.0 0.0) {})",
                                if obj_func.sense == "min" { "<=" } else { ">=" },
                                obj_func
                                    .terms
                                    .iter()
                                    .filter(|obj_ind| ind_set.contains(obj_ind))
                                    .map(|obj_ind| format!(
                                        "(* obj{} sol{}x{})",
                                        obj_ind, ind_sol, obj_ind
                                    ))
                                    .collect::<Vec<String>>()
                                    .join(" "),
                                if obj_func.sense == "min" {
                                    convert_to_real(ub)
                                } else {
                                    convert_to_real(lb)
                                },
                            )
                        })
                        .collect::<Vec<String>>()
                        .join(" ")
                )?;
            }
            "DER" => {
                let num_der = content_iter.next().unwrap().parse::<usize>().unwrap();
                let cons_len = constraints.len();
                for der_ind in (0 + cons_len)..(num_der + cons_len) {
                    parse_cons(
                        &mut content_iter,
                        &mut constraints,
                        &fout,
                        der_ind,
                        &obj_func,
                    )?;
                    if der_ind == num_der + cons_len - 1 {
                        handle_last_cons(
                            &constraints.get(&der_ind).unwrap().terms,
                            &obj_func.terms,
                            &der_ind,
                            obj_func.sense.clone(),
                            infease,
                            &mut fout,
                            lb,
                            ub,
                        )?;
                    }
                    content_iter.next();
                    let reason = content_iter.next().unwrap();
                    match reason {
                        "asm" => {
                            used_asm.insert(der_ind, HashSet::from([der_ind]));
                            asm_set.insert(der_ind);
                            content_iter.next();
                            content_iter.next();
                            clean_up_cons(&delete_cons, &der_ind, &mut constraints)?;
                        }
                        "lin" | "rnd" => {
                            let mut rea_coe = HashSet::<usize>::new();
                            let mut used_cons = HashMap::<usize, String>::new();
                            let mut coe_map = HashMap::<usize, HashSet<usize>>::new();
                            let num_used_cons =
                                content_iter.next().unwrap().parse::<usize>().unwrap();
                            let mut new_used_asm_set = HashSet::new();
                            for _ in 0..num_used_cons {
                                let used_con_ind =
                                    content_iter.next().unwrap().parse::<usize>().unwrap();

                                let used_con_coeff = convert_to_real(content_iter.next().unwrap());

                                if let Some(used_asm_ind) = used_asm.get(&used_con_ind) {
                                    for used_asm_ind in used_asm_ind {
                                        new_used_asm_set.insert(*used_asm_ind);
                                    }
                                }
                                for used_con_term in
                                    constraints.get(&used_con_ind).unwrap().terms.iter()
                                {
                                    coe_map.insert(*used_con_term, HashSet::new());
                                }
                                writeln!(
                                    &mut fout,
                                    "(assert (< {}.0 {}.0))",
                                    used_con_ind, der_ind
                                )?;
                                used_cons.insert(used_con_ind, used_con_coeff);
                            }
                            used_asm.insert(der_ind, new_used_asm_set);

                            for (used_con_ind, _) in used_cons.iter() {
                                for used_con_term in
                                    constraints.get(used_con_ind).unwrap().terms.iter()
                                {
                                    coe_map
                                        .entry(*used_con_term)
                                        .or_insert(HashSet::new())
                                        .insert(*used_con_ind);
                                }
                            }

                            for (used_con_term, used_con_set) in coe_map.iter() {
                                rea_coe.insert(*used_con_term);
                                if used_con_set.len() <= 0 {
                                    println!("error in lin or rnd");
                                    exit(0);
                                }
                                writeln!(
                                    &mut fout,
                                    "(declare-fun r{}x{} () Real)",
                                    der_ind, used_con_term
                                )?;
                                writeln!(
                                    &mut fout,
                                    "(assert (= r{}x{} (+ {} 0.0 0.0)))",
                                    der_ind,
                                    used_con_term,
                                    used_con_set
                                        .iter()
                                        .map(|used_con_ind| format!(
                                            "(* {} c{}x{})",
                                            used_cons.get(used_con_ind).unwrap(),
                                            used_con_ind,
                                            used_con_term
                                        ))
                                        .collect::<Vec<String>>()
                                        .join(" ")
                                )?;
                                if reason == "rnd" {
                                    writeln!(
                                        &mut fout,
                                        "(declare-fun rndr{}x{} () Int)",
                                        der_ind, used_con_term
                                    )?;
                                    writeln!(
                                        &mut fout,
                                        "(assert (ite is_intx{} (= (to real rndr{}x{}) r{}x{}) (= r{}x{} 0.0)))",
                                        used_con_term, der_ind, used_con_term, der_ind, used_con_term, der_ind, used_con_term
                                    )?;
                                }
                            }

                            for (var, sign) in [("cleq", "<="), ("cgeq", ">="), ("ceq", "=")].iter()
                            {
                                writeln!(&mut fout, "(declare-fun {}{} () Bool)", var, der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (= {}{} (and ({} {}))))",
                                    var,
                                    der_ind,
                                    sign,
                                    used_cons
                                        .iter()
                                        .map(|(ind, coeff)| format!(
                                            "({} (* {} cs{}) 0.0)",
                                            sign, coeff, ind
                                        ))
                                        .collect::<Vec<String>>()
                                        .join(" ")
                                )?;
                            }
                            writeln!(&mut fout, "(declare-fun rs{} () Real)", der_ind)?;

                            writeln!(&mut fout, "(declare-fun beta{} () Real)", der_ind)?;
                            writeln!(
                                &mut fout,
                                "(assert (= beta{} (+ {} 0.0 0.0)))",
                                der_ind,
                                used_cons
                                    .iter()
                                    .map(|(used_ind, used_coeff)| format!(
                                        "(* {} crhs{})",
                                        used_coeff, used_ind
                                    ))
                                    .collect::<Vec<String>>()
                                    .join(" ")
                            )?;
                            if reason == "rnd" {
                                writeln!(
                                    &mut fout,
                                    "(assert (or (= rs{} -1.0) (= rs{} 1.0)))",
                                    der_ind, der_ind
                                )?;
                                writeln!(&mut fout, "(declare-fun rndbeta{} () Int)", der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (ite (= rs{} -1.0) (and (<= (to real rndbeta{}) beta{}) (> (to real (+ rndbeta{} 1)) beta{})) (and (>= (to real rndbeta{}) beta{}) (< (to real (- rndbeta{} 1)) beta{}))))",
                                    der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind
                                )?;
                                writeln!(&mut fout, "(declare-fun brndbeta{} () Real)", der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (= brndbeta{} (to real rndbeta{})))",
                                    der_ind, der_ind
                                )?;
                            }
                            let beta = if reason == "rnd" { "brndbeta" } else { "beta" };
                            // assert dominance of constraints
                            dom_cons(
                                &rea_coe,
                                format!("rs{}", der_ind),
                                format!("{}{}", beta, der_ind),
                                format!("r{}x", der_ind),
                                &constraints.get(&der_ind).unwrap().terms,
                                format!("cs{}", der_ind),
                                format!("crhs{}", der_ind),
                                format!("c{}x", der_ind),
                                &fout,
                            )?;

                            content_iter.next();
                            let last_used = content_iter.next().unwrap().parse::<usize>().unwrap();
                            delete_cons
                                .entry(last_used)
                                .or_insert(Vec::new())
                                .push(der_ind);
                            clean_up_cons(&delete_cons, &der_ind, &mut constraints)?;
                        }
                        "uns" => {
                            let i1 = content_iter.next().unwrap().parse::<usize>().unwrap();
                            let l1 = content_iter.next().unwrap().parse::<usize>().unwrap();
                            let i2 = content_iter.next().unwrap().parse::<usize>().unwrap();
                            let l2 = content_iter.next().unwrap().parse::<usize>().unwrap();
                            if !asm_set.contains(&l1) || !asm_set.contains(&l2) {
                                println!("error in uns");
                                exit(0);
                            }
                            let mut new_used_asm_set = HashSet::new();
                            for k in used_asm[&i1].iter() {
                                if *k != l1 {
                                    new_used_asm_set.insert(*k);
                                }
                            }
                            for k in used_asm[&i2].iter() {
                                if *k != l2 {
                                    new_used_asm_set.insert(*k);
                                }
                            }
                            used_asm.insert(der_ind, new_used_asm_set);
                            for i in [i1, l1, i2, l2].iter() {
                                writeln!(&mut fout, "(assert ({}.0 < {}.0))", i, der_ind)?;
                            }
                            dom_cons(
                                &constraints.get(&i2).unwrap().terms,
                                format!("cs{}", i1),
                                format!("crhs{}", i1),
                                format!("c{}x", i1),
                                &constraints.get(&der_ind).unwrap().terms,
                                format!("cs{}", der_ind),
                                format!("crhs{}", der_ind),
                                format!("c{}x", der_ind),
                                &fout,
                            )?;
                            dom_cons(
                                &constraints.get(&i2).unwrap().terms,
                                format!("cs{}", i2),
                                format!("crhs{}", i2),
                                format!("c{}x", i2),
                                &constraints.get(&der_ind).unwrap().terms,
                                format!("cs{}", der_ind),
                                format!("crhs{}", der_ind),
                                format!("c{}x", der_ind),
                                &fout,
                            )?;
                            for j in &constraints.get(&l1).unwrap().terms {
                                if !constraints.get(&l2).unwrap().terms.contains(&j) {
                                    writeln!(&mut fout, "(assert (= c{}x{} 0.0))", l1, j)?;
                                } else {
                                    writeln!(
                                        &mut fout,
                                        "(assert (= c{}x{} c{}x{}))",
                                        l1, j, l2, j
                                    )?;
                                    writeln!(
                                        &mut fout,
                                        "(declare-fun rndr{}x{} () Int)",
                                        der_ind, j
                                    )?;
                                }
                                writeln!(&mut fout, "(assert (ite is_intx{} (= (to_real rndr{}x{} ) c{}x{}) (= c{}x{} 0.0)))", j, der_ind, j, l1, j, l1, j)?;
                            }
                            for j in &constraints.get(&l2).unwrap().terms {
                                if !constraints.get(&l1).unwrap().terms.contains(&j) {
                                    writeln!(&mut fout, "(assert (= c{}x{} 0.0))", l2, j)?;
                                }
                            }
                            writeln!(&mut fout, "(declare-fun rndbeta{} () Int)", der_ind)?;
                            writeln!(&mut fout, "(assert (or (and (= cs{} -1.0) (= cs{} 1.0) (= (to_real rndbeta{}) crhs{}) (= (+ crhs{} 1.0) crhs{})) (and (= cs{} -1.0) (= cs{} 1.0) (= (to_real rndbeta{}) crhs{}) (= (+ crhs{} 1.0) crhs{}))))", l1, l2, der_ind, l1, l1, l2, l2, l1, der_ind, l2, l2, l1)?;

                            content_iter.next();
                            let last_used = content_iter.next().unwrap().parse::<i32>().unwrap();
                            if last_used >= 0 {
                                delete_cons
                                    .entry(last_used as usize)
                                    .or_insert(Vec::new())
                                    .push(der_ind);
                                clean_up_cons(&delete_cons, &der_ind, &mut constraints)?;
                            }
                        }
                        _ => {
                            println!("error in der");
                            exit(0);
                        }
                    }
                }
            }
            _ => {
                continue;
            }
        }
    }
    writeln!(&mut fout, "(check-sat)")?;
    writeln!(&mut fout, "(exit)")?;

    Ok(())
}
