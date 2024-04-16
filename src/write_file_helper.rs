use std::{
    fs::File,
    io::{self, Write},
};

/// Opens a file for writing and initializes it with SMT-LIBv2 headers.
///
/// # Arguments
///
/// * `filename` - A string slice that holds the name of the file to be created.
///
/// # Returns
///
/// * `io::Result<File>` - A result indicating success or failure. If successful, it returns a File
///                        instance representing the opened file.
pub fn fout_open(filename: &str) -> io::Result<File> {
    let mut fout = File::create(filename)?;
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
    Ok(fout)
}

/// Closes the given file by writing SMT-LIBv2 exit commands.
///
/// # Arguments
///
/// * `fout` - A mutable reference to a File instance that needs to be closed.
///
/// # Returns
///
/// * `io::Result<()>` - A result indicating success or failure.
pub fn fout_close(mut fout: &File) -> io::Result<()> {
    writeln!(&mut fout, "(check-sat)")?;
    writeln!(&mut fout, "(exit)")?;
    Ok(())
}
