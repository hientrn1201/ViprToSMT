mod cons_helper;
mod convert;
mod execute_ext_cmd;
mod write_file_helper;

use clap::Parser;
use cons_helper::{add_dep, clean_up_cons, dom_cons, handle_last_cons, parse_cons};
use convert::{convert_sense_to_sign, convert_to_real};
use execute_ext_cmd::check;
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, Read, Write};
use std::process::exit;
use std::time::Instant;
use write_file_helper::{fout_close, fout_open};

#[derive(Parser, Debug, Default)]
#[clap(
    author = "Hien Tran",
    version,
    about = "Convert VIPR file to SMT2 file"
)]
struct Args {
    /// VIPR file (path included) to be converted
    #[clap(short, long)]
    filename: String,

    /// Maximum derived constraints per check size
    #[clap(short, long, default_value_t = usize::MAX)]
    max_block_size: usize,

    /// Software used to check
    #[clap(short, long)]
    software: String,    
}

#[derive(Debug)]
pub struct Relation {
    sense: String,
    terms: HashMap<usize, String>,
    rhs: String,
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    let filename = args.filename.trim();

    let file = File::open(filename)?;
    let mut reader = io::BufReader::new(file);
    let outfile = filename.trim_end_matches(".vipr").to_string() + "_vipr.smt2";

    let mut fout: File;

    let mut variables = Vec::new();
    let mut constraints = HashMap::new();
    let mut obj_func: Relation = Relation {
        sense: "".to_string(),
        terms: HashMap::new(),
        rhs: "".to_string(),
    };

    let mut infease = false;
    let mut lb = "";
    let mut ub = "";
    let mut list_sols = Vec::<HashMap<usize, String>>::new();
    let mut asm_set = HashSet::new();

    // map con_ind to delete previous cons
    let mut delete_cons = HashMap::<usize, Vec<usize>>::new();

    // map con_ind to used asm
    let mut used_asm = HashMap::<usize, HashSet<usize>>::new();

    // used constraints index set for the current block of derived constraints
    let mut used_dep = HashSet::<usize>::new();

    // used intx index set for the current block of derived constraints
    let mut used_intx = HashSet::<usize>::new();

    // flag to check if the objective function has been used in the the current block of derived constraints
    let mut is_used_obj = false;

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

    let mut cur_block_size = 0;

    let max_block_size = args.max_block_size;

    let software = args.software;

    let mut count = 0;

    let start = Instant::now();

    let mut content_iter = contents.into_iter();

    while let Some(string) = content_iter.next() {
        match string {
            // process VAR & INT section to get the type of variables
            "VAR" => {
                let num_vars = content_iter.next().unwrap().parse::<usize>().unwrap();
                for _ in 0..num_vars {
                    content_iter.next();
                    variables.push("Real");
                }
            }
            "INT" => {
                let num_ints = content_iter.next().unwrap().parse::<usize>().unwrap();
                for _ in 0..num_ints {
                    let int_index = content_iter.next().unwrap().parse::<usize>().unwrap();
                    variables[int_index] = "Int";
                }
            }

            // process OBJ section to get the objective function
            "OBJ" => {
                let objsense = content_iter.next().unwrap();
                let num_objterms = content_iter.next().unwrap().parse::<usize>().unwrap();
                obj_func.sense = objsense.to_string();
                for _ in 0..num_objterms {
                    let var_index = content_iter.next().unwrap().parse::<usize>().unwrap();
                    let var_coeff = convert_to_real(content_iter.next().unwrap());
                    obj_func.terms.insert(var_index, var_coeff);
                }
            }

            // process CON section to get the constraints
            // store constraints in a hashmap "constraints" with the index as the key
            "CON" => {
                let num_cons = content_iter.next().unwrap().parse::<usize>().unwrap();
                content_iter.next();
                // num_bcons = content_iter.next().unwrap().parse::<usize>().unwrap();
                for i in 0..num_cons {
                    parse_cons(&mut content_iter, &mut constraints, i, &obj_func)?;
                }
            }

            // process RTP section to get the lower and upper bounds of the objective function
            // and check if the problem is infeasible
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
                        eprintln!("error in rtp");
                        exit(0);
                    }
                }
            }

            // process SOL section to get the solutions if any
            "SOL" => {
                let num_sol = content_iter.next().unwrap().parse::<usize>().unwrap();
                if (num_sol == 0 && infease == false) || (num_sol > 0 && infease == true) {
                    eprintln!("error in sol");
                    exit(0);
                }

                for sol_ind in 0..num_sol {
                    fout = fout_open(&outfile)?;
                    for (con_ind, con) in constraints.iter() {
                        writeln!(&mut fout, "(declare-fun crhs{} () Real)", con_ind)?;
                        writeln!(&mut fout, "(assert (= crhs{} {}))", con_ind, con.rhs)?;
                        for (var_ind, var_coef) in con.terms.iter() {
                            writeln!(&mut fout, "(declare-fun c{}x{} () Real)", con_ind, var_ind)?;
                            writeln!(
                                &mut fout,
                                "(assert (= c{}x{} {}))",
                                con_ind, var_ind, var_coef
                            )?;
                        }
                    }
                    for (var_ind, var_type) in variables.iter().enumerate() {
                        writeln!(&mut fout, "(declare-fun x{} () {})", var_ind, var_type)?;
                        writeln!(&mut fout, "(declare-fun is_intx{} () Bool)", var_ind)?;
                        if *var_type == "Int" {
                            writeln!(&mut fout, "(assert is_intx{})", var_ind)?;
                        } else {
                            writeln!(&mut fout, "(assert (not is_intx{}))", var_ind)?;
                        }
                    }
                    content_iter.next(); // skip name
                    let mut ind_set = HashMap::new();
                    let num_vars = content_iter.next().unwrap().parse::<usize>().unwrap();
                    for _ in 0..num_vars {
                        let ind = content_iter.next().unwrap().parse::<usize>().unwrap();
                        let val = convert_to_real(content_iter.next().unwrap());
                        writeln!(&mut fout, "(declare-fun sol{}x{} () Real)", sol_ind, ind)?;
                        writeln!(&mut fout, "(assert (= sol{}x{} {}))", sol_ind, ind, val)?;
                        ind_set.insert(ind, val);
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
                                .filter(|(ind, _)| ind_set.contains_key(ind))
                                .map(|(ind, _)| format!(
                                    "(* c{}x{} sol{}x{})",
                                    cons_ind, ind, sol_ind, ind
                                ))
                                .collect::<Vec<String>>()
                                .join(" "),
                            cons_ind
                        )?;
                    }
                    fout_close(&fout)?;
                    check(&outfile, count, &software)?;
                    count += 1;
                }
                // assert objective function,
                // make sure at least one solution is above the lower bound if max problem and vice versa
                if !infease {
                    fout = fout_open(&outfile)?;
                    for (obj_ind, obj_coef) in obj_func.terms.iter() {
                        writeln!(&mut fout, "(declare-fun obj{} () Real)", obj_ind)?;
                        writeln!(&mut fout, "(assert (= obj{} {}))", obj_ind, obj_coef)?;
                    }

                    for (sol_ind, sol) in list_sols.iter().enumerate() {
                        for (sol_var_ind, sol_var_coef) in sol.iter() {
                            writeln!(
                                &mut fout,
                                "(declare-fun sol{}x{} () Real)",
                                sol_ind, sol_var_ind
                            )?;
                            writeln!(
                                &mut fout,
                                "(assert (= sol{}x{} {}))",
                                sol_ind, sol_var_ind, sol_var_coef
                            )?;
                        }
                    }

                    writeln!(
                        &mut fout,
                        "(assert (or {} xtrue))",
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
                                        .filter(|(obj_ind, _)| ind_set.contains_key(obj_ind))
                                        .map(|(obj_ind, _)| format!(
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
                    fout_close(&fout)?;
                    check(&outfile, count, &software)?;
                    count += 1;
                }
            }

            // process DER section to get the derived constraints based on batch processing
            "DER" => {
                fout = fout_open(&outfile)?;
                let num_der = content_iter.next().unwrap().parse::<usize>().unwrap();
                let cons_len = constraints.len();
                for der_ind in (0 + cons_len)..(num_der + cons_len) {
                    parse_cons(&mut content_iter, &mut constraints, der_ind, &obj_func)?;
                    used_dep.insert(der_ind);
                    add_dep(der_ind, &constraints, &fout)?;
                    if der_ind == num_der + cons_len - 1 {
                        handle_last_cons(
                            &constraints
                                .get(&der_ind)
                                .unwrap()
                                .terms
                                .keys()
                                .cloned()
                                .collect(),
                            &obj_func.terms,
                            &der_ind,
                            obj_func.sense.clone(),
                            infease,
                            &mut fout,
                            lb,
                            ub,
                            &mut is_used_obj,
                        )?;
                    }

                    content_iter.next();
                    let reason = content_iter.next().unwrap();
                    match reason {
                        // if the reason is asm, add the constraint to the used_asm set
                        // and clean up the constraints that are no longer needed
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

                                if !used_dep.contains(&used_con_ind) {
                                    add_dep(used_con_ind, &constraints, &fout)?;
                                    used_dep.insert(used_con_ind);
                                }

                                if let Some(used_asm_ind) = used_asm.get(&used_con_ind) {
                                    for used_asm_ind in used_asm_ind {
                                        new_used_asm_set.insert(*used_asm_ind);
                                    }
                                }
                                for (used_con_term, _) in
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
                            for (used_con_term, _) in coe_map.iter() {
                                if !used_intx.contains(&used_con_term) {
                                    used_intx.insert(*used_con_term);
                                    writeln!(
                                        &mut fout,
                                        "(declare-fun is_intx{} () Bool)",
                                        used_con_term
                                    )?;
                                    if variables[*used_con_term] == "Int" {
                                        writeln!(&mut fout, "(assert is_intx{})", used_con_term)?;
                                    } else {
                                        writeln!(
                                            &mut fout,
                                            "(assert (not is_intx{}))",
                                            used_con_term
                                        )?;
                                    }
                                }
                            }

                            for (used_con_ind, _) in used_cons.iter() {
                                for (used_con_term, _) in
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
                                    eprintln!("error in lin or rnd");
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
                                        "(assert (ite is_intx{} (= (to_real rndr{}x{}) r{}x{}) (= r{}x{} 0.0)))",
                                        used_con_term, der_ind, used_con_term, der_ind, used_con_term, der_ind, used_con_term
                                    )?;
                                }
                            }

                            for (var, sign) in [("cleq", "<="), ("cgeq", ">="), ("ceq", "=")].iter()
                            {
                                writeln!(&mut fout, "(declare-fun {}{} () Bool)", var, der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (= {}{} (and {})))",
                                    var,
                                    der_ind,
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
                            writeln!(
                                &mut fout,
                                "(assert (ite ceq{} (= rs{} 0.0) (ite cleq{} (= rs{} (- 1.0)) (ite cgeq{} (= rs{} 1.0) xfalse))))",
                                der_ind, der_ind, der_ind, der_ind, der_ind, der_ind
                            )?;
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
                                    "(assert (or (= rs{} (- 1.0)) (= rs{} 1.0)))",
                                    der_ind, der_ind
                                )?;
                                writeln!(&mut fout, "(declare-fun rndbeta{} () Int)", der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (ite (= rs{} (- 1.0)) (and (<= (to_real rndbeta{}) beta{}) (> (to_real (+ rndbeta{} 1)) beta{})) (and (>= (to_real rndbeta{}) beta{}) (< (to_real (- rndbeta{} 1)) beta{}))))",
                                    der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind, der_ind
                                )?;
                                writeln!(&mut fout, "(declare-fun brndbeta{} () Real)", der_ind)?;
                                writeln!(
                                    &mut fout,
                                    "(assert (= brndbeta{} (to_real rndbeta{})))",
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
                                &constraints
                                    .get(&der_ind)
                                    .unwrap()
                                    .terms
                                    .keys()
                                    .cloned()
                                    .collect(),
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
                                eprintln!("error in uns");
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
                                if !used_dep.contains(i) {
                                    add_dep(*i, &constraints, &fout)?;
                                    used_dep.insert(*i);
                                }
                                writeln!(&mut fout, "(assert (< {}.0 {}.0))", i, der_ind)?;
                            }
                            dom_cons(
                                &constraints
                                    .get(&i1)
                                    .unwrap()
                                    .terms
                                    .keys()
                                    .cloned()
                                    .collect(),
                                format!("cs{}", i1),
                                format!("crhs{}", i1),
                                format!("c{}x", i1),
                                &constraints
                                    .get(&der_ind)
                                    .unwrap()
                                    .terms
                                    .keys()
                                    .cloned()
                                    .collect(),
                                format!("cs{}", der_ind),
                                format!("crhs{}", der_ind),
                                format!("c{}x", der_ind),
                                &fout,
                            )?;
                            dom_cons(
                                &constraints
                                    .get(&i2)
                                    .unwrap()
                                    .terms
                                    .keys()
                                    .cloned()
                                    .collect(),
                                format!("cs{}", i2),
                                format!("crhs{}", i2),
                                format!("c{}x", i2),
                                &constraints
                                    .get(&der_ind)
                                    .unwrap()
                                    .terms
                                    .keys()
                                    .cloned()
                                    .collect(),
                                format!("cs{}", der_ind),
                                format!("crhs{}", der_ind),
                                format!("c{}x", der_ind),
                                &fout,
                            )?;
                            for (j, _) in &constraints.get(&l1).unwrap().terms {
                                if !constraints.get(&l2).unwrap().terms.contains_key(&j) {
                                    writeln!(&mut fout, "(assert (= c{}x{} 0.0))", l1, j)?;
                                } else {
                                    if !used_intx.contains(&j) {
                                        used_intx.insert(*j);
                                        writeln!(&mut fout, "(declare-fun is_intx{} () Bool)", j)?;
                                        if variables[*j] == "Int" {
                                            writeln!(&mut fout, "(assert is_intx{})", j)?;
                                        } else {
                                            writeln!(&mut fout, "(assert (not is_intx{}))", j)?;
                                        }
                                    }

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
                            for j in constraints.get(&l2).unwrap().terms.keys() {
                                if !constraints.get(&l1).unwrap().terms.contains_key(&j) {
                                    writeln!(&mut fout, "(assert (= c{}x{} 0.0))", l2, j)?;
                                }
                            }
                            writeln!(&mut fout, "(declare-fun rndbeta{} () Int)", der_ind)?;
                            writeln!(&mut fout, "(assert (or (and (= cs{} (- 1.0)) (= cs{} 1.0) (= (to_real rndbeta{}) crhs{}) (= (+ crhs{} 1.0) crhs{})) (and (= cs{} (- 1.0)) (= cs{} 1.0) (= (to_real rndbeta{}) crhs{}) (= (+ crhs{} 1.0) crhs{}))))", l1, l2, der_ind, l1, l1, l2, l2, l1, der_ind, l2, l2, l1)?;

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
                            eprintln!("error in der");
                            exit(0);
                        }
                    }
                    cur_block_size += 1;
                    if cur_block_size == max_block_size {
                        fout_close(&fout)?;
                        check(&outfile, count, &software)?;
                        count += 1;
                        fout = fout_open(&outfile)?;
                        cur_block_size = 0;
                        is_used_obj = false;
                        used_dep.clear();
                        used_intx.clear();
                    }
                }
            }
            _ => {
                continue;
            }
        }
    }

    fout = File::options().write(true).append(true).open(&outfile)?;
    fout_close(&fout)?;
    check(&outfile, count, &software)?;
    println!("{} is valid.", filename);
    println!("Time elapsed: {:?}s", start.elapsed().as_secs_f64());
    Ok(())
}
