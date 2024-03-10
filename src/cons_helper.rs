use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, Write};

use crate::convert::{convert_sense_to_real, convert_to_real};
use crate::Relation;

pub fn clean_up_cons(
    delete_cons: &HashMap<usize, Vec<usize>>,
    index: &usize,
    constraints: &mut HashMap<usize, Relation>,
) -> io::Result<()> {
    if index < &0 {
        return Ok(());
    }
    if let Some(cons_to_delete) = delete_cons.get(index) {
        for cons_ind in cons_to_delete {
            constraints.remove(cons_ind);
        }
    }
    Ok(())
}

pub fn handle_last_cons(
    terms: &HashSet<usize>,
    objcoe: &HashSet<usize>,
    i: &usize,
    objsense: String,
    infease: bool,
    mut fout: &File,
    lb: &str,
    ub: &str,
) -> io::Result<()> {
    if !infease {
        if objsense == "min" {
            dom_cons(
                terms,
                format!("cs{}", i),
                format!("crhs{}", i),
                format!("c{}x", i),
                objcoe,
                "1.0".to_string(),
                convert_to_real(lb),
                "obj".to_string(),
                fout,
            )?;
            Ok(())
        } else {
            dom_cons(
                terms,
                format!("cs{}", i),
                format!("crhs{}", i),
                format!("c{}x", i),
                objcoe,
                "-1.0".to_string(),
                convert_to_real(ub),
                "obj".to_string(),
                fout,
            )?;
            Ok(())
        }
    } else {
        write!(&mut fout, "(assert (and")?;
        for k in terms {
            write!(&mut fout, " (= c{}x{} 0.0)", i, k)?;
        }
        write!(&mut fout, " (=> (= cs{} -1.0) (< crhs{} 0.0))", i, i)?;
        write!(&mut fout, " (=> (= cs{} 1.0) (> crhs{} 0.0))", i, i)?;
        write!(&mut fout, " (=> (= cs{} 0.0) (not (= crhs{} 0.0)))))", i, i)?;
        writeln!(&mut fout)?;
        Ok(())
    }
    // we may need more things, if obsurdity dominate the bound in feasible circumstance(if exist solution then fine.)
}

pub fn dom_cons(
    a1: &HashSet<usize>,
    sense1: String,
    b1: String,
    pre1: String,
    a2: &HashSet<usize>,
    sense2: String,
    b2: String,
    pre2: String,
    mut fout: &File,
) -> io::Result<()> {
    write!(&mut fout, "(assert (or (and")?;
    for k in a1 {
        write!(&mut fout, " (= {}{} 0.0)", pre1, k)?;
    }
    write!(&mut fout, " (=> (= {} -1.0) (< {} 0.0))", sense1, b1)?;
    write!(&mut fout, " (=> (= {} 1.0) (> {} 0.0))", sense1, b1)?;
    write!(&mut fout, " (=> (= {} 0.0) (not (= {} 0.0))))", sense1, b1)?;
    write!(&mut fout, " (and")?;
    for k in a1 {
        if !a2.contains(&k) {
            write!(&mut fout, " (= {}{} 0.0)", pre1, k)?;
        }
    }
    for k in a2 {
        if !a1.contains(&k) {
            write!(&mut fout, " (= {}{} 0.0)", pre2, k)?;
        }
    }
    for k in a1 {
        if a2.contains(&k) {
            write!(&mut fout, " (= {}{} {}{})", pre1, k, pre2, k)?;
        }
    }
    write!(&mut fout, " (or")?;
    write!(
        &mut fout,
        " (and (= {} {}) (= {} 0.0) (= {} 0.0))",
        b1, b2, sense1, sense2
    )?;
    write!(
        &mut fout,
        " (and (<= {} {}) (= {} -1.0) (<= {} 0.0))",
        b1, b2, sense2, sense1
    )?;
    write!(
        &mut fout,
        " (and (>= {} {}) (= {} 1.0) (>= {} 0.0))))))",
        b1, b2, sense2, sense1
    )?;
    writeln!(&mut fout)?;
    Ok(())
}

pub fn parse_cons(
    content_iter: &mut std::vec::IntoIter<&str>,
    constraints: &mut HashMap<usize, Relation>,
    mut fout: &File,
    i: usize,
    obj_func: &Relation,
) -> io::Result<()> {
    content_iter.next();
    writeln!(&mut fout, "(declare-fun cs{} () Real)", i)?;
    let sense = content_iter.next().unwrap();
    let sense_real = convert_sense_to_real(sense);
    writeln!(&mut fout, "(assert (= cs{} {}))", i, sense_real)?;

    let rhs = convert_to_real(content_iter.next().unwrap());
    writeln!(&mut fout, "(declare-fun crhs{} () Real)", i)?;
    writeln!(&mut fout, "(assert (= crhs{} {}))", i, rhs)?;
    let mut cons = Relation {
        sense: sense.to_string(),
        terms: HashSet::new(),
    };
    let num_terms = content_iter.next().unwrap();
    if num_terms == "OBJ" {
        for ind in obj_func.terms.iter() {
            writeln!(&mut fout, "(declare-fun c{}x{} () Real)", i, ind)?;
            writeln!(&mut fout, "(assert (= c{}x{} obj{}))", i, ind, ind)?;
        }
        cons.terms = obj_func.terms.clone();
    } else {
        let num_terms = num_terms.parse::<usize>().unwrap();
        for _ in 0..num_terms {
            let var_index = content_iter.next().unwrap().parse::<usize>().unwrap();
            let var_coeff = convert_to_real(content_iter.next().unwrap());
            writeln!(&mut fout, "(declare-fun c{}x{} () Real)", i, var_index)?;
            writeln!(&mut fout, "(assert (= c{}x{} {}))", i, var_index, var_coeff)?;
            cons.terms.insert(var_index);
        }
    }
    constraints.insert(i, cons);
    Ok(())
}
