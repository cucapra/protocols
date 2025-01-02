// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use codespan_reporting::diagnostic::{Diagnostic as CodespanDiagnostic, Label as CodespanLabel};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};

use crate::ir::*;

pub struct DiagnosticHandler {
    files: SimpleFiles<String, String>,
}

impl DiagnosticHandler {
    pub fn new() -> Self {
        Self {
            files: SimpleFiles::new(),
        }
    }

    pub fn add_file(&mut self, name: String, content: String) -> usize {
        self.files.add(name, content)
    }

    pub fn emit_diagnostic(&self, tr: &Transaction, expr_id: ExprId, message: &str, severity: codespan_reporting::diagnostic::Severity) {
        if let Some((line, col)) = tr.get_md(expr_id) {
            let label = CodespanLabel::primary(0, line..(line)) 
                .with_message(message);
        

            let diagnostic = CodespanDiagnostic::new(severity).with_message(format!("Error in statement ID: {:?}", expr_id)).with_labels(vec![label]);

            let writer = term::termcolor::StandardStream::stderr(term::termcolor::ColorChoice::Auto);
            
            let config = term::Config {
                display_style: term::DisplayStyle::Rich,
                ..term::Config::default()
            };

            term::emit(&mut writer.lock(), &config, &self.files, &diagnostic).unwrap();

        } else {
            eprintln!("Could not find metadata for statement id: {:?}", expr_id);
        }
    }
}



#[cfg(test)]
mod tests {
    use super::*;
    use baa::BitVecValue;

    #[test]
    fn test_emit_diagnostic() {
        let mut handler = DiagnosticHandler::new();

        let file_id = handler.add_file(
            "test_file".to_string(),
            "a=1;\nassert_eq!(x, 20);\n".to_string(),
        );

        let mut symbols = SymbolTable::default();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));

        let mut tr = Transaction::new("test_transaction".to_string());
        let one_expr = tr.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        tr.s(Stmt::Assign(a, one_expr));

        tr.add_md(one_expr, 2, 5);

        handler.emit_diagnostic(
            &tr,
            one_expr,
            "Mismatched types in assertion",
            codespan_reporting::diagnostic::Severity::Error,
        );
    }
}