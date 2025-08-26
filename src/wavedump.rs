// Copyright 2025 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use crate::ir::{SymbolId, SymbolTable};
use fst_writer::{FstFileType, FstInfo};
use std::path::Path;
use thiserror::Error;

/// Wavedump output file.
pub struct Wavedump {}

#[derive(Error, Debug)]
pub enum WavedumpError {
    #[error("fst write error: {0}")]
    FstError(#[from] fst_writer::FstWriteError),
}

pub type Result<T> = std::result::Result<T, WavedumpError>;

impl Wavedump {
    pub fn create_fst(filename: impl AsRef<Path>, st: &SymbolTable, dut: SymbolId) -> Result<Self> {
        let info = FstInfo {
            start_time: 0,
            timescale_exponent: 0,
            version: "Protocols interpreter".to_string(),
            date: "".to_string(),
            file_type: FstFileType::Verilog,
        };
        let header = fst_writer::open_fst(filename, &info)?;

        // generate signal declarations for DUT
    }
}
