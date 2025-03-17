// Copyright 2022-2024 The Regents of the University of California
// released under BSD 3-Clause License
// author: Kevin Laeufer <laeufer@berkeley.edu>
//
// Code to interface with yosys by calling it as a process. Derived from this python implementation:
// https://github.com/ekiwi/rtl-repair/blob/main/benchmarks/yosys.py

use std::fs;
use std::path::{Path, PathBuf};
use thiserror::Error;
use tempfile;

#[derive(Error, Debug)]
pub enum YosysError {
    #[error("failed to find yosys, make sure it is on your path!")]
    YosysNotFound,
    #[error("failed to execute command: `{0}`\n{1}\n{2}")]
    FailedToExecuteCommand(String, String, String),
    #[error("no output generated: {0}")]
    OutputMissing(String),
    #[error("failed to perform i/o: {0}")]
    IoError(#[from] std::io::Error),
}

pub struct YosysEnv {
    working_dir: PathBuf,
    script_out: Option<PathBuf>,
}

impl Default for YosysEnv {
    fn default() -> Self {
        let working_dir = std::env::current_dir().unwrap();
        Self {
            working_dir,
            script_out: None,
        }
    }
}

impl YosysEnv {
    pub fn with_temp_dir() -> Result<Self> {
        let dir = tempfile::TempDir::new()?;
        Ok(Self {
            working_dir: dir.into_path(),
            ..Default::default()
        })
    }

    pub fn working_dir(&self) -> &Path {
        self.working_dir.as_path()
    }
}

#[derive(Default, Debug)]
pub struct ProjectConf {
    sources: Vec<PathBuf>,
    top: Option<String>,
    include_path: Option<PathBuf>,
}

impl ProjectConf {
    pub fn with_source(source: PathBuf) -> Self {
        let sources = vec![source];
        Self {
            sources,
            ..Default::default()
        }
    }
}

pub type Result<T> = std::result::Result<T, YosysError>;

pub fn run_yosys<C>(env: &YosysEnv, commands: &[C]) -> Result<String>
where
    C: AsRef<str>,
{
    let cmd_str: String = join(commands.iter(), " ; ");

    if let Some(script_out) = &env.script_out {
        todo!("implement script out");
    }

    let mut cmd = std::process::Command::new("yosys");
    cmd.arg("-p").arg(&cmd_str).current_dir(&env.working_dir);

    let res = cmd.output().unwrap();
    let out = String::from_utf8_lossy(&res.stdout).to_string();
    if res.status.success() {
        Ok(out)
    } else {
        let err = String::from_utf8_lossy(&res.stderr).to_string();
        Err(YosysError::FailedToExecuteCommand(
            format!("{cmd:?}"),
            out,
            err,
        ))
    }
}

const MINIMAL_BTOR_CONVERSION: &[&str] = &[
    "proc -noopt",
    "async2sync", // required for designs with async reset
    "flatten",
    "dffunmap",
];

fn read_sources(project: &ProjectConf) -> Vec<String> {
    // canonicalize file paths since yosys might use a different output directory
    let sources = project
        .sources
        .iter()
        .map(|s| fs::canonicalize(s.as_path()).unwrap());

    let mut out: Vec<_> = if let Some(include) = &project.include_path {
        let ii = include.to_string_lossy().to_string();
        sources
            .map(|s| format!("read_verilog -sv -I{ii} {}", s.to_string_lossy()))
            .collect()
    } else {
        sources
            .map(|s| format!("read_verilog -sv {}", s.to_string_lossy()))
            .collect()
    };
    if let Some(top) = &project.top {
        out.push(format!("hierarchy -top {}", top));
    }
    out
}

pub fn yosys_to_btor(
    env: &YosysEnv,
    project: &ProjectConf,
    btor_name: Option<&Path>,
) -> Result<PathBuf> {
    // auto-generate a btor_name if it was not given
    let btor_name = match (btor_name, &project.top) {
        (Some(name), _) => name.to_path_buf(),
        (None, Some(top)) => PathBuf::from(format!("{top}.btor")),
        _ => {
            let with_btor = project.sources.first().unwrap().with_extension("btor");
            let name = with_btor.file_name().unwrap().to_string_lossy();
            PathBuf::from(name.as_ref())
        }
    };

    let mut cmd = read_sources(project);
    cmd.extend(MINIMAL_BTOR_CONVERSION.iter().map(|s| s.to_string()));
    cmd.push(format!("write_btor -x {}", btor_name.to_string_lossy()));
    run_yosys(env, &cmd)?;
    let btor_full = if btor_name.is_absolute() {
        fs::canonicalize(btor_name).unwrap()
    } else {
        fs::canonicalize(PathBuf::from_iter([
            env.working_dir.as_path(),
            btor_name.as_path(),
        ]))
        .unwrap()
    };
    if btor_full.exists() {
        Ok(btor_full)
    } else {
        Err(YosysError::OutputMissing(
            btor_full.to_string_lossy().to_string(),
        ))
    }
}

/// Crashes the program if yosys is not found.
pub fn require_yosys() -> Result<()> {
    match std::process::Command::new("yosys").arg("-version").output() {
        Ok(res) => {
            let txt = String::from_utf8(res.stdout).unwrap();
            if txt.starts_with("Yosys") {
                Ok(())
            } else {
                Err(YosysError::YosysNotFound)
            }
        }
        Err(_) => Err(YosysError::YosysNotFound),
    }
}

#[inline]
fn join<T, S, I>(value: T, separator: S) -> String
where
    S: AsRef<str>,
    T: ExactSizeIterator<Item = I>,
    I: AsRef<str>,
{
    let mut out = String::new();
    let last_id = value.len() - 1;
    for (ii, v) in value.enumerate() {
        out.push_str(v.as_ref());
        if ii < last_id {
            out.push_str(separator.as_ref());
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_require_yosys() {
        require_yosys().expect("failed");
    }

    #[test]
    fn test_run_yosys_load_existing_verilog_file() {
        // read existing file
        let cmds = ["read_verilog inputs/add_mul_and.v"];
        let res = run_yosys(&YosysEnv::default(), &cmds).unwrap();
        assert!(res.contains("Successfully finished Verilog frontend"));
    }

    #[test]
    fn test_run_yosys_fail() {
        // run_yosys should signal a failure when yosys fails
        let cmds = ["read_verilog inputs/does_not_exist.v"];
        let res = run_yosys(&YosysEnv::default(), &cmds);
        assert!(res.is_err());
    }

    #[test]
    fn test_yosys_to_btor() {
        let env = YosysEnv::with_temp_dir().unwrap();
        let inp = PathBuf::from("inputs/add_mul_and.v");
        let proj = ProjectConf {
            sources: vec![inp],
            ..Default::default()
        };
        let btor_file =
            yosys_to_btor(&env, &proj, Some(&PathBuf::from("add_mul_and_2.btor"))).unwrap();
        assert!(btor_file
            .to_string_lossy()
            .to_string()
            .ends_with("add_mul_and_2.btor"));
        let btor = fs::read_to_string(btor_file).unwrap();
        assert!(btor.contains("input 1 d"))
    }

    #[test]
    fn test_yosys_to_btor_auto_name() {
        let env = YosysEnv::with_temp_dir().unwrap();
        let inp = PathBuf::from("inputs/add_mul_and.v");
        let proj = ProjectConf {
            sources: vec![inp],
            ..Default::default()
        };
        let btor_file = yosys_to_btor(&env, &proj, None).unwrap();
        // derived from sources
        assert!(btor_file
            .to_string_lossy()
            .to_string()
            .ends_with("add_mul_and.btor"));
    }
}