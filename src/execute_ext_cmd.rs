use std::{io, process::Command};

/// Represents the result of a satisfiability check.
const SAT: &str = "sat";

/// Performs a satisfiability check using the CVC5 SMT solver.
///
/// This function executes the CVC5 SMT solver on the given file and checks if the output indicates
/// satisfiability. If the output is not "sat", it returns an error.
///
/// # Arguments
///
/// * `filename` - A string slice representing the name of the file to be checked.
/// * `count` - An integer specifying the count.
///
/// # Returns
///
/// * `io::Result<()>` - A result indicating success or failure. If successful, it returns `Ok(())`.
///
/// # Errors
///
/// Returns an error under the following conditions:
///
/// * If the output from CVC5 is unexpected.
/// * If there's an error removing the file after checking.
pub fn check(filename: &str, count: usize) -> io::Result<()> {
    let output = execute_cmd("cvc5", vec![filename]);
    match output {
        Ok(output) => {
            if output.trim() != SAT {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "Unexpected output from cvc5",
                ));
            }

            let remove_output = execute_cmd("rm", vec!["-f", filename]);
            match remove_output {
                Ok(_) => Ok(()),
                Err(err) => Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("Failed to remove file: {}", err),
                )),
            }
        }
        Err(err) => Err(err),
    }
}

/// Executes a command and returns its output as a string.
///
/// This function takes the name of the program to execute and a vector of arguments,
/// executes the command, and returns the standard output as a string.
///
/// # Arguments
///
/// * `program` - A string slice representing the name of the program to execute.
/// * `args` - A vector of string slices representing the arguments to pass to the program.
///
/// # Returns
///
/// * `io::Result<String>` - A result indicating success or failure. If successful, it returns the
///                          standard output of the executed command as a string.
///
/// # Errors
///
/// Returns an error if the command fails to execute or if its status is not successful.
///
/// # Example
///
/// ```
/// use std::io;
/// use smt_solver::execute_cmd;
///
/// fn main() -> io::Result<()> {
///     let output = execute_cmd("ls", vec!["-l"])?;
///     println!("Output: {}", output);
///     Ok(())
/// }
/// ```
fn execute_cmd(program: &str, args: Vec<&str>) -> io::Result<String> {
    let output = Command::new(program)
        .args(args)
        .output()
        .expect("failed to execute process");

    if !output.status.success() {
        return Err(io::Error::new(
            io::ErrorKind::Other,
            format!("Command failed with {:?}", output.status.code().unwrap()),
        ));
    }
    let stdout = String::from_utf8(output.stdout).unwrap();
    Ok(stdout)
}
