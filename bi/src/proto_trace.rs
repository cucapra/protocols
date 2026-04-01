// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

//! # Protocol Traces and Error Reporting

use baa::BitVecValue;
use protocols::ir::StmtId;

/// A `ProtoTrace` (protocol trace) is just a type alias for a list
/// of `ProtoCall`s (protocol calls)
pub type ProtoTrace = Vec<ProtoCall>;

/// Type representing a call to a protocol (e.g. `add(1, 2, 3)`)
#[derive(Debug, Clone)]
pub struct ProtoCall {
    pub name: String,
    pub start: u32,
    pub end: Option<u32>,
    pub args: Vec<Option<BitVecValue>>,
}

/// `TraceId` is an index into the `Traces.tails`
#[derive(Debug, Copy, Clone, PartialOrd, PartialEq)]
pub struct TraceId(u32);

/// A `TraceEntry` is a linked-list node
#[derive(Debug, Clone)]
struct TraceEntry {
    /// The actual protocol invocation
    value: ProtoCall,

    /// The previous `TraceEntry`'s index in `Traces.entries`
    /// (if one exists)
    prev: Option<u32>,
}

/// `Traces` represents all successfully completed transactions (across
/// all explored execution paths)
#[derive(Debug, Default)]
pub struct Traces {
    /// Flat array containing all `TraceEntry` nodes that have been created
    entries: Vec<TraceEntry>,

    /// For `TraceId(i)`, `tails[i]` contains the index in `entries` of the
    /// most recent `TraceEntry` created for `TraceId(i)`
    tails: Vec<Option<u32>>,
}

impl Traces {
    /// Appends a `ProtoCall` to the end of the `trace`
    /// (identified by its `TraceId`)
    pub fn append(&mut self, trace: TraceId, value: ProtoCall) {
        let entry_id = self.entries.len() as u32;
        let prev = self.tails.get(trace.0 as usize).cloned().flatten();
        self.entries.push(TraceEntry { value, prev });
        self.tails[trace.0 as usize] = Some(entry_id);
    }

    /// Updates the `Traces` struct when a new protocol is `fork`-ed.
    /// The argument `TraceId` is for the parent, while the forked-off child's
    /// `TraceId` is returned.
    /// This function creates a new `TraceId` for the child, and copies the
    /// parent's `tails` pointer to the child (this means that the parent
    /// & the child share all `TraceEntry`s prior to the fork, without
    /// needing to clone every single `TraceEntry` struct).
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

    /// Discards the trace corresponding to a failed thread
    /// (identified by its `TraceId`). Under the hood, this just
    /// sets `tails[trace_id] = None`, which prevents the trace from
    /// being accessible via `Traces::get_trace` (which retrieves all
    /// transactions starting from `tails[trace_id]`).
    pub fn remove(&mut self, trace: TraceId) {
        // TODO: remove any orphaned entries (GC!)
        self.tails[trace.0 as usize] = None;
    }

    /// Retrieves all transactions corresponding to a `TraceId`
    /// by starting `tails[trace_id]` and walking backwards through  
    /// each `TraceEntry`'s `prev` pointer
    pub fn get_trace(&self, trace: TraceId) -> ProtoTrace {
        if let Some(t) = self.tails[trace.0 as usize] {
            self.get_trace_from_tail(t)
        } else {
            vec![]
        }
    }

    /// Helper function for `get_trace`
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

    /// Extracts all unique protocol traces
    pub fn unique_traces(&self) -> Vec<ProtoTrace> {
        let mut tails: Vec<_> = self.tails.iter().cloned().flatten().collect();
        tails.sort();
        tails.dedup();

        // We visit all traces and count the usage in order to ensure that no trace
        // returned is a prefix of another returned trace.
        let mut uses = vec![0; self.entries.len()];
        let mut todo = tails.clone();
        while let Some(entry_id) = todo.pop() {
            uses[entry_id as usize] += 1;
            if let Some(prev) = self.entries[entry_id as usize].prev {
                todo.push(prev);
            }
        }

        // filter out any tails that are used more than once since that implies that they are
        // the tail of a prefix trace
        debug_assert!(
            !tails.iter().any(|&t| uses[t as usize] == 0),
            "all tails should be used at least once"
        );
        tails.retain(|&t| uses[t as usize] == 1);

        tails
            .into_iter()
            .map(|t| self.get_trace_from_tail(t))
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Failure {
    // TODO: include more information for assignments vs assert_eq
    pub thread_local_step: u32,
    pub proto_id: usize,
    pub thread_name: String,
    pub stmt: StmtId,
    pub a: BitVecValue,
    pub b: BitVecValue,
}
