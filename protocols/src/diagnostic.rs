// Copyright 2024 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Francis Pham <fdp25@cornell.edu>

use std::{collections::HashSet, io::Write};

use baa::BitVecValue;
use clap::ColorChoice;
use codespan_reporting::diagnostic::{
    Diagnostic as CodespanDiagnostic, Label as CodespanLabel, LabelStyle, Severity,
};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{Buffer, Color, ColorSpec, WriteColor};
use pest::iterators::Pair;
use pest::RuleType;

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
    /// Whether colored outputs should be enabled in the diagnostic
    _color_choice: ColorChoice,
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
    /// `color_choice` indicates whether to emit error messages w/ ANSI colors
    color_choice: ColorChoice,
}

impl Default for DiagnosticHandler {
    /// Default `DiagnosticHandler` does not emit colored error messages
    fn default() -> Self {
        Self::new(ColorChoice::Never)
    }
}

impl DiagnosticHandler {
    pub fn new(color_choice: ColorChoice) -> Self {
        Self {
            files: SimpleFiles::new(),
            reported_errs: HashSet::new(),
            error_string: String::new(),
            color_choice,
        }
    }

    /// Creates a buffer for error diagnostics
    /// (different buffers are created based on whether we want colors or not)
    fn create_buffer(&self) -> Buffer {
        if self.color_choice == ColorChoice::Never {
            Buffer::no_color()
        } else {
            Buffer::ansi()
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
        let mut buffer = self.create_buffer();
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
                _color_choice: self.color_choice,
            };

            diagnostic.emit(&mut buffer, &self.files);

            let error_msg = String::from_utf8_lossy(buffer.as_slice());
            self.error_string.push_str(&error_msg);
            print!("{}", error_msg);
        }
    }

    /// Note: we make this function parametric over any type `R`
    /// that implements Pest's `RuleType` trait
    /// so that we can call this function from different parsers
    pub fn emit_diagnostic_parsing<R: RuleType>(
        &mut self,
        message: &str,
        fileid: usize,
        pair: &Pair<'_, R>,
        level: Level,
    ) {
        let start = pair.as_span().start();
        let end = pair.as_span().end();
        let buffer = &mut self.create_buffer();
        let label = Label {
            message: Some(message.to_string()),
            range: (start, end),
        };

        let diagnostic = Diagnostic {
            title: format!("{:?} in file {}", level, fileid),
            message: message.to_string(),
            level,
            location: Some((fileid, label)),
            _color_choice: self.color_choice,
        };

        diagnostic.emit(buffer, &self.files);
        let error_msg = String::from_utf8_lossy(buffer.as_slice());
        self.error_string.push_str(&error_msg);
        print!("{}", String::from_utf8_lossy(buffer.as_slice()));
    }

    pub fn emit_diagnostic_lexing(
        &mut self,
        message: &str,
        fileid: usize,
        start: usize,
        end: usize,
        level: Level,
    ) {
        let buffer = &mut self.create_buffer();
        let label = Label {
            message: Some(message.to_string()),
            range: (start, end),
        };

        let diagnostic = Diagnostic {
            title: format!("{:?} in file {}", level, fileid),
            message: message.to_string(),
            level,
            location: Some((fileid, label)),
            _color_choice: self.color_choice,
        };

        diagnostic.emit(buffer, &self.files);
        let error_msg = String::from_utf8_lossy(buffer.as_slice());
        self.error_string.push_str(&error_msg);
        print!("{}", error_msg);
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
        let buffer = &mut self.create_buffer();
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
                _color_choice: self.color_choice,
            };

            diagnostic.emit(buffer, &self.files);

            let error_msg = String::from_utf8_lossy(buffer.as_slice());
            self.error_string.push_str(&error_msg);
            print!("{}", error_msg);
        }
    }

    pub fn emit_diagnostic_assertion(
        &mut self,
        tr: &Transaction,
        expr1_id: &ExprId,
        expr2_id: &ExprId,
        eval1: &BitVecValue,
        eval2: &BitVecValue,
    ) {
        let buffer = &mut self.create_buffer();

        if let (Some((start1, end1, fileid1)), Some((start2, end2, fileid2))) =
            (tr.get_expr_loc(*expr1_id), tr.get_expr_loc(*expr2_id))
        {
            assert!(
                fileid1 == fileid2,
                "Expressions must be in the same file for assertion error"
            );
            let diagnostic = Diagnostic {
                title: format!("Error in file {}", fileid1),
                message: "The two expressions did not evaluate to the same value".to_string(),
                level: Level::Error,
                location: Some((
                    fileid1,
                    Label {
                        message: Some(format!("LHS Value: {:?}, RHS Value: {:?}", eval1, eval2)),
                        range: (start1.min(start2), end1.max(end2)),
                    },
                )),
                _color_choice: self.color_choice,
            };

            diagnostic.emit(buffer, &self.files);

            let error_msg = String::from_utf8_lossy(buffer.as_slice());
            self.error_string.push_str(&error_msg);
            print!("{}", error_msg);
        }
    }

    pub fn emit_general_message(&mut self, message: &str, level: Level) {
        let buffer = &mut self.create_buffer();
        let diagnostic = Diagnostic {
            title: format!("{:?}", level),
            message: message.to_string(),
            level,
            location: None,
            _color_choice: self.color_choice,
        };

        diagnostic.emit(buffer, &self.files);

        let error_msg = String::from_utf8_lossy(buffer.as_slice());
        self.error_string.push_str(&error_msg);
        print!("{}", error_msg);
    }
}

#[cfg(test)]
mod tests {
    use baa::BitVecValue;
    use insta::Settings;
    use std::path::Path;
    use strip_ansi_escapes::strip_str;

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

        let mut handler = DiagnosticHandler::new(ColorChoice::Never);
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
}
