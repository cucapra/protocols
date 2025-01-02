// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use codespan_reporting::diagnostic::{Diagnostic as CodespanDiagnostic, Label as CodespanLabel};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term::{self, Config, DisplayStyle, TermColor};

use crate::ir::*;

pub struct DiagnosticHandler {
    files: SimpleFiles<String, String>,
}

impl DiagnosticHandler {
    pub fn new() -> Self {
        self {
            files: SimpleFiles::new(),
        }
    }

    pub fn add_file(&mut self, name: String, content: String) -> usize {
        self.files.add(name, content)
    }
}

