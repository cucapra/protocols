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
enum ErrorKey {
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
}

impl DiagnosticHandler {
    pub fn new() -> Self {
        Self {
            files: SimpleFiles::new(),
            reported_errs: HashSet::new(),
        }
    }

    pub fn add_file(&mut self, name: String, content: String) -> usize {
        self.files.add(name, content)
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

            print!("{}", String::from_utf8_lossy(buffer.as_slice()));
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

            print!("{}", String::from_utf8_lossy(buffer.as_slice()));
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::typecheck::*;

    use super::*;
    use baa::BitVecValue;

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
    }

    #[test]
    fn serialize_calyx_go_down_transaction() {
        // Manually create the expected result of parsing `calyx_go_down`.
        // Note that the order in which things are created will be different in the parser.

        // 1) declare symbols
        let mut symbols = SymbolTable::default();
        let mut handler: DiagnosticHandler = DiagnosticHandler::new();
        let ii = symbols.add_without_parent("ii".to_string(), Type::BitVec(32));
        let oo = symbols.add_without_parent("oo".to_string(), Type::BitVec(32));
        assert_eq!(symbols["oo"], symbols[oo]);

        // declare Calyx struct
        let dut_struct = symbols.add_struct(
            "Calyx".to_string(),
            vec![
                Field::new("ii".to_string(), Dir::In, Type::BitVec(32)),
                Field::new("go".to_string(), Dir::In, Type::BitVec(1)),
                Field::new("done".to_string(), Dir::Out, Type::BitVec(1)),
                Field::new("oo".to_string(), Dir::Out, Type::BitVec(32)),
            ],
        );

        let dut = symbols.add_without_parent("dut".to_string(), Type::Struct(dut_struct));
        let dut_ii = symbols.add_with_parent("ii".to_string(), dut);
        let dut_go = symbols.add_with_parent("go".to_string(), dut);
        let dut_done = symbols.add_with_parent("done".to_string(), dut);
        let dut_oo = symbols.add_with_parent("oo".to_string(), dut);
        assert_eq!(symbols["dut.oo"], symbols[dut_oo]);
        assert_eq!(symbols["oo"], symbols[oo]);

        // create fileid and read file
        let input =
            std::fs::read_to_string("tests/calyx_go_doneStruct.prot").expect("failed to load");
        let calyx_fileid = handler.add_file("calyx_go_done.prot".to_string(), input);

        // 2) create transaction
        let mut calyx_go_done = Transaction::new("calyx_go_done".to_string());
        calyx_go_done.args = vec![Arg::new(ii, Dir::In), Arg::new(oo, Dir::Out)];
        calyx_go_done.type_args = vec![dut];

        // 3) create expressions
        let ii_expr = calyx_go_done.e(Expr::Sym(ii));
        calyx_go_done.add_expr_loc(ii_expr, 153, 155, calyx_fileid);
        let dut_oo_expr = calyx_go_done.e(Expr::Sym(dut_oo));
        calyx_go_done.add_expr_loc(dut_oo_expr, 260, 266, calyx_fileid);
        let one_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(1, 1)));
        calyx_go_done.add_expr_loc(one_expr, 170, 171, calyx_fileid);
        let zero_expr = calyx_go_done.e(Expr::Const(BitVecValue::from_u64(0, 1)));
        calyx_go_done.add_expr_loc(zero_expr, 232, 233, calyx_fileid);
        let dut_done_expr = calyx_go_done.e(Expr::Sym(dut_done));
        calyx_go_done.add_expr_loc(dut_done_expr, 184, 192, calyx_fileid);
        let cond_expr = calyx_go_done.e(Expr::Equal(dut_done_expr, one_expr));
        calyx_go_done.add_expr_loc(cond_expr, 183, 198, calyx_fileid);
        let not_expr = calyx_go_done.e(Expr::Not(cond_expr));
        calyx_go_done.add_expr_loc(not_expr, 182, 198, calyx_fileid);

        // 4) create statements
        let while_body = vec![calyx_go_done.s(Stmt::Step)];
        let wbody = calyx_go_done.s(Stmt::Block(while_body));

        let dut_ii_assign = calyx_go_done.s(Stmt::Assign(dut_ii, ii_expr));
        calyx_go_done.add_stmt_loc(dut_ii_assign, 143, 157, calyx_fileid);
        let dut_go_assign = calyx_go_done.s(Stmt::Assign(dut_go, one_expr));
        calyx_go_done.add_stmt_loc(dut_go_assign, 160, 172, calyx_fileid);
        let dut_while = calyx_go_done.s(Stmt::While(not_expr, wbody));
        calyx_go_done.add_stmt_loc(dut_while, 175, 219, calyx_fileid);
        let dut_go_reassign = calyx_go_done.s(Stmt::Assign(dut_go, zero_expr));
        calyx_go_done.add_stmt_loc(dut_go_reassign, 222, 234, calyx_fileid);
        let dut_ii_dontcare = calyx_go_done.s(Stmt::Assign(dut_ii, calyx_go_done.expr_dont_care()));
        calyx_go_done.add_stmt_loc(dut_ii_dontcare, 238, 250, calyx_fileid);
        let oo_assign = calyx_go_done.s(Stmt::Assign(oo, dut_oo_expr));
        calyx_go_done.add_stmt_loc(oo_assign, 254, 268, calyx_fileid);
        let body = vec![
            dut_ii_assign,
            dut_go_assign,
            dut_while,
            dut_go_reassign,
            dut_ii_dontcare,
            oo_assign,
        ];
        calyx_go_done.body = calyx_go_done.s(Stmt::Block(body));
        type_check(&calyx_go_done, &symbols, &mut handler);
    }
}
