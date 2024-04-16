use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, Write};

use crate::convert::{convert_sense_to_real, convert_to_real};
use crate::Relation;

/// Cleans up constraints based on the given `delete_cons` map and `index`.
/// Removes constraints from the `constraints` map if their index is present in `delete_cons`.
///
/// # Arguments
///
/// * `delete_cons` - A map containing indices of constraints to be deleted.
/// * `index` - The index of the constraint to be checked for deletion.
/// * `constraints` - A mutable reference to the map of constraints.
///
/// # Returns
///
/// Returns an `io::Result` indicating whether the operation was successful or not.
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

/// Handles the last constraint based on the given parameters.
/// Writes the corresponding SMT-LIB code to the given file.
///
/// # Arguments
///
/// * `terms` - A set of term indices.
/// * `objcoe` - A map containing objective coefficients.
/// * `i` - The index of the constraint.
/// * `objsense` - The objective sense ("min" or "max").
/// * `infease` - A boolean indicating whether the constraint is infeasible.
/// * `fout` - A mutable reference to the output file.
/// * `lb` - The lower bound as a string.
/// * `ub` - The upper bound as a string.
/// * `is_used_obj` - A mutable reference to a boolean indicating whether the objective has been used.
///
/// # Returns
///
/// Returns an `io::Result` indicating whether the operation was successful or not.
pub fn handle_last_cons(
    terms: &HashSet<usize>,
    objcoe: &HashMap<usize, String>,
    i: &usize,
    objsense: String,
    infease: bool,
    mut fout: &File,
    lb: &str,
    ub: &str,
    is_used_obj: &mut bool,
) -> io::Result<()> {
    if !infease {
        if !*is_used_obj {
            for (ind, coef) in objcoe.iter() {
                writeln!(&mut fout, "(declare-fun obj{} () Real)", ind)?;
                writeln!(&mut fout, "(assert (= obj{} {}))", ind, coef)?;
            }
            *is_used_obj = true;
        }
        let obj_key = objcoe.keys().cloned().collect::<HashSet<usize>>();
        if objsense == "min" {
            dom_cons(
                terms,
                format!("cs{}", i),
                format!("crhs{}", i),
                format!("c{}x", i),
                &obj_key, // Clone the elements before collecting them into a new HashSet
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
                &obj_key,
                "(- 1.0)".to_string(),
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
        write!(&mut fout, " (=> (= cs{} (- 1.0)) (< crhs{} 0.0))", i, i)?;
        write!(&mut fout, " (=> (= cs{} 1.0) (> crhs{} 0.0))", i, i)?;
        write!(&mut fout, " (=> (= cs{} 0.0) (not (= crhs{} 0.0)))))", i, i)?;
        writeln!(&mut fout)?;
        Ok(())
    }
    // we may need more things, if obsurdity dominate the bound in feasible circumstance(if exist solution then fine.)
}

/// Generates SMT-LIB code for a dominance constraint based on the given parameters.
/// Writes the code to the given file.
///
/// # Arguments
///
/// * `a1` - A set of term indices for the first constraint.
/// * `sense1` - The sense of the first constraint.
/// * `b1` - The right-hand side of the first constraint as a string.
/// * `pre1` - The prefix for the first constraint's variables.
/// * `a2` - A set of term indices for the second constraint.
/// * `sense2` - The sense of the second constraint.
/// * `b2` - The right-hand side of the second constraint as a string.
/// * `pre2` - The prefix for the second constraint's variables.
/// * `fout` - A mutable reference to the output file.
///
/// # Returns
///
/// Returns an `io::Result` indicating whether the operation was successful or not.
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
    write!(&mut fout, " (=> (= {} (- 1.0)) (< {} 0.0))", sense1, b1)?;
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
        " (and (<= {} {}) (= {} (- 1.0)) (<= {} 0.0))",
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

/// Parses a constraint from the content iterator and adds it to the `constraints` map.
///
/// # Arguments
///
/// * `content_iter` - A mutable reference to the content iterator.
/// * `constraints` - A mutable reference to the map of constraints.
/// * `i` - The index of the constraint.
/// * `obj_func` - The objective function as a `Relation` object.
///
/// # Returns
///
/// Returns an `io::Result` indicating whether the operation was successful or not.
pub fn parse_cons(
    content_iter: &mut std::vec::IntoIter<&str>,
    constraints: &mut HashMap<usize, Relation>,
    i: usize,
    obj_func: &Relation,
) -> io::Result<()> {
    content_iter.next();
    let sense = content_iter.next().unwrap();

    let rhs = convert_to_real(content_iter.next().unwrap());
    let mut cons = Relation {
        sense: sense.to_string(),
        terms: HashMap::new(),
        rhs,
    };
    let num_terms = content_iter.next().unwrap();
    if num_terms == "OBJ" {
        cons.terms = obj_func.terms.clone();
    } else {
        let num_terms = num_terms.parse::<usize>().unwrap();
        for _ in 0..num_terms {
            let var_index = content_iter.next().unwrap().parse::<usize>().unwrap();
            let var_coeff = convert_to_real(content_iter.next().unwrap());
            cons.terms.insert(var_index, var_coeff);
        }
    }
    constraints.insert(i, cons);
    Ok(())
}

/// Adds declarations and assertions for a constraint to the output file.
///
/// # Arguments
///
/// * `i` - The index of the constraint.
/// * `constraints` - A reference to the map of constraints.
/// * `fout` - A mutable reference to the output file.
///
/// # Returns
///
/// Returns an `io::Result` indicating whether the operation was successful or not.
pub fn add_dep(
    i: usize,
    constraints: &HashMap<usize, Relation>,
    mut fout: &File,
) -> io::Result<()> {
    writeln!(&mut fout, "(declare-fun cs{} () Real)", i)?;
    writeln!(
        &mut fout,
        "(assert (= cs{} {}))",
        i,
        convert_sense_to_real(&constraints.get(&i).unwrap().sense)
    )?;
    writeln!(&mut fout, "(declare-fun crhs{} () Real)", i)?;
    writeln!(
        &mut fout,
        "(assert (= crhs{} {}))",
        i,
        constraints.get(&i).unwrap().rhs
    )?;
    for (ind, coef) in constraints.get(&i).unwrap().terms.iter() {
        writeln!(&mut fout, "(declare-fun c{}x{} () Real)", i, ind)?;
        writeln!(&mut fout, "(assert (= c{}x{} {}))", i, ind, coef)?;
    }

    Ok(())
}
