// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nikil.shyamsunder@gmail.com>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{collections::HashSet, io::Write};

use codespan_reporting::diagnostic::{
    Diagnostic as CodespanDiagnostic, Label as CodespanLabel, LabelStyle, Severity,
};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{Buffer, Color, ColorSpec, WriteColor};

use crate::ir::*;

/// Track Errors
#[derive(Hash, Eq, PartialEq, Debug)]
pub enum ErrorKey {
    ExprKey(ExprId),
    StmtKey(StmtId),
}

/// Severity of diagnostic
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Level {
    Error,
    Warning,
}

/// A label representing a part of the source code
#[derive(Debug, Clone, PartialEq, Eq)]
struct Label {
    message: Option<String>,
    range: (usize, usize),
}

impl Label {
    fn to_codespan_label(&self, fileid: usize) -> CodespanLabel<usize> {
        CodespanLabel::new(LabelStyle::Primary, fileid, self.range.0..self.range.1)
            .with_message(self.message.clone().unwrap_or_default())
        // error msg
    }
}

/// Diagnostic of a particular part of source code
struct Diagnostic {
    title: String,
    message: String,
    level: Level,
    location: Option<(usize, Label)>,
}

impl Diagnostic {
    pub fn emit(&self, buffer: &mut Buffer, files: &SimpleFiles<String, String>) {
        if let Some((fileid, label)) = &self.location {
            let severity = match self.level {
                Level::Error => Severity::Error,
                Level::Warning => Severity::Warning,
            };

            let diagnostic = CodespanDiagnostic::new(severity)
                .with_message(&self.message) // Severity: (msg)
                .with_labels(vec![label.to_codespan_label(*fileid)]);

            let config = term::Config::default(); // Change config depending on how error needs to be produced
            term::emit(buffer, &config, files, &diagnostic).expect("Failed to write diagnostic");
        } else {
            let color = match self.level {
                Level::Error => Color::Red,
                Level::Warning => Color::Yellow,
            };

            buffer
                .set_color(ColorSpec::new().set_bold(true).set_fg(Some(color)))
                .expect("Failed to set color");
            writeln!(buffer, "{}", self.title).expect("Failed to write title");

            buffer
                .set_color(&ColorSpec::new())
                .expect("Failed to reset color");
        }
    }
}

pub struct DiagnosticHandler {
    files: SimpleFiles<String, String>,
    reported_errs: HashSet<ErrorKey>,
    error_string: String,
}

impl DiagnosticHandler {
    pub fn new() -> Self {
        Self {
            files: SimpleFiles::new(),
            reported_errs: HashSet::new(),
            error_string: String::new(),
        }
    }

    pub fn add_file(&mut self, name: String, content: String) -> usize {
        self.files.add(name, content)
    }

    pub fn error_string(&self) -> &str {
        &self.error_string
    }

    pub fn emit_diagnostic_expr(
        &mut self,
        tr: &Transaction,
        expr_id: &ExprId,
        message: &str,
        level: Level,
    ) {
        // need to check errors to avoid recursive duplication of error message
        if !self.reported_errs.insert(ErrorKey::ExprKey(*expr_id)) {
            return;
        }
        let buffer = &mut Buffer::ansi();
        if let Some((start, end, fileid)) = tr.get_expr_loc(*expr_id) {
            let label = Label {
                message: Some(message.to_string()),
                range: (start, end),
            };

            let diagnostic = Diagnostic {
                title: format!("{:?} in file {}", level, fileid),
                message: message.to_string(),
                level,
                location: Some((fileid, label)),
            };

            diagnostic.emit(buffer, &self.files);

            let error_msg = String::from_utf8_lossy(buffer.as_slice());
            self.error_string.push_str(&error_msg);
            print!("{}", error_msg);
        }
    }

    pub fn emit_diagnostic_stmt(
        &mut self,
        tr: &Transaction,
        stmt_id: &StmtId,
        message: &str,
        level: Level,
    ) {
        // need to check errors to avoid recursive duplication of error message
        if !self.reported_errs.insert(ErrorKey::StmtKey(*stmt_id)) {
            return;
        }
        let buffer = &mut Buffer::ansi();
        if let Some((start, end, fileid)) = tr.get_stmt_loc(*stmt_id) {
            let label = Label {
                message: Some(message.to_string()),
                range: (start, end),
            };

            let diagnostic = Diagnostic {
                title: format!("{:?} in file {}", level, fileid),
                message: message.to_string(),
                level,
                location: Some((fileid, label)),
            };

            diagnostic.emit(buffer, &self.files);

            let error_msg = String::from_utf8_lossy(buffer.as_slice());
            self.error_string.push_str(&error_msg);
            print!("{}", error_msg);
        }
    }
}

#[cfg(test)]
mod tests {
    use baa::BitVecValue;
    use insta::Settings;
    use std::path::Path;
    use strip_ansi_escapes::strip_str;

    use crate::{serialize::tests::create_calyx_go_done_transaction, typecheck::*};

    use super::*;

    #[test]
    fn test_emit_diagnostic() {
        let mut symbols = SymbolTable::default();
        let a = symbols.add_without_parent("a".to_string(), Type::BitVec(32));
        let b = symbols.add_without_parent("b".to_string(), Type::BitVec(32));

        let mut tr = Transaction::new("test_transaction".to_string());
        let one_expr = tr.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        let zero_expr = tr.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        tr.s(Stmt::Assign(a, one_expr));
        tr.s(Stmt::Assign(b, zero_expr));

        let mut handler = DiagnosticHandler::new();
        let file_id = handler.add_file(
            "main.calyx".to_string(),
            "12345678\nassert_eq!(x, 20);\n".to_string(),
        );

        tr.add_expr_loc(one_expr, 9, 11, file_id);
        tr.add_expr_loc(zero_expr, 12, 15, file_id);

        handler.emit_diagnostic_expr(&tr, &one_expr, "Random Warning", Level::Warning);
        handler.emit_diagnostic_expr(&tr, &zero_expr, "Random Error", Level::Error);

        let content = strip_str(handler.error_string());

        let mut settings = Settings::clone_current();
        settings.set_snapshot_path(Path::new("../tests/snapshots"));
        settings.bind(|| {
            insta::assert_snapshot!(content);
        });
    }

    #[test]
    fn serialize_calyx_go_done_transaction() {
        let mut handler = DiagnosticHandler::new();
        let (calyx_go_done, symbols) = create_calyx_go_done_transaction(&mut handler);
        type_check(&calyx_go_done, &symbols, &mut handler);
    }
}
