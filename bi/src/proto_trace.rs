// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Protocol Traces and Error Reporting

use baa::BitVecValue;
use protocols::ir::StmtId;

pub type ProtoTrace = Vec<ProtoCall>;

#[derive(Debug, Clone)]
pub struct ProtoCall {
    pub name: String,
    pub start: u32,
    pub end: u32,
    pub args: Vec<Option<BitVecValue>>,
}

#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
pub struct TraceId(u32);

#[derive(Debug, Clone)]
struct TraceEntry {
    value: ProtoCall,
    prev: Option<u32>,
}

#[derive(Debug, Default)]
pub struct Traces {
    entries: Vec<TraceEntry>,
    tails: Vec<Option<u32>>,
}

impl Traces {
    pub fn append(&mut self, trace: TraceId, value: ProtoCall) {
        let entry_id = self.entries.len() as u32;
        let prev = self.tails.get(trace.0 as usize).cloned().flatten();
        self.entries.push(TraceEntry { value, prev });
        self.tails[trace.0 as usize] = Some(entry_id);
    }

    pub fn fork(&mut self, trace: TraceId) -> TraceId {
        let new_id = TraceId(self.tails.len() as u32);
        self.tails.push(self.tails[trace.0 as usize]);
        new_id
    }

    pub fn empty(&mut self) -> TraceId {
        let new_id = TraceId(self.tails.len() as u32);
        self.tails.push(None);
        new_id
    }

    pub fn remove(&mut self, trace: TraceId) {
        // TODO: remove any orphaned entries (GC!)
        self.tails[trace.0 as usize] = None;
    }

    pub fn get_trace(&self, trace: TraceId) -> ProtoTrace {
        if let Some(t) = self.tails[trace.0 as usize] {
            self.get_trace_from_tail(t)
        } else {
            vec![]
        }
    }

    fn get_trace_from_tail(&self, tail: u32) -> ProtoTrace {
        let mut out = vec![];
        let mut t = Some(tail);
        while let Some(entry_id) = t {
            let entry = &self.entries[entry_id as usize];
            out.push(entry.value.clone());
            t = entry.prev;
        }
        out.reverse();
        out
    }

    pub fn unique_traces(&self) -> Vec<ProtoTrace> {
        let mut tails: Vec<_> = self.tails.iter().cloned().flatten().collect();
        tails.sort();
        tails.dedup();
        tails
            .into_iter()
            .map(|t| self.get_trace_from_tail(t))
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Failure {
    // TODO: include more information for assignments vs assert_eq
    pub step: u32,
    pub proto_id: usize,
    pub thread_name: String,
    pub stmt: StmtId,
    pub a: BitVecValue,
    pub b: BitVecValue,
}
