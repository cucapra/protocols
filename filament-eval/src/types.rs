// Copyright 2026 Cornell University
// released under MIT License
// author: Ernest Ng <eyn5@cornell.edu>

use std::fmt;

use protocols::ir::{Dir, Field, Type};
use serde::Deserialize;

/// A Filament event variable
#[derive(Debug, Deserialize, Clone, PartialEq)]
pub struct Event {
    /// The name of the event
    pub name: String,

    /// The delay associated with the event
    pub delay: u32,
}

/// Tuple struct so that we can implement `Display` for `Vec<Event>`
/// Rust doesn't allow us to do `impl Display for Vec<Event>` directly due to
/// the orphan rule (neither `Display` nor `Vec` are defined in this crate).
pub struct Events(pub Vec<Event>);

/// A raw Filament parameter (the fields of this struct exactly match
/// what is in the Filament interface JSON)
#[derive(Debug, Deserialize)]
#[allow(dead_code)]
pub struct RawParameter {
    name: String,
    width: u32,
    event: String,
    start: u32,
    end: u32,
}

impl RawParameter {
    /// Converts a `RawParameter` into a Protocols `Field` based on the
    /// supplied direction `dir`
    pub fn into_field(self, dir: Dir) -> Field {
        Field {
            name: self.name,
            dir,
            tpe: Type::BitVec(self.width),
        }
    }
}

/* -------------------------------------------------------------------------- */
/*                            Trait implementations                           */
/* -------------------------------------------------------------------------- */

impl fmt::Display for Event {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "<{}: {}>", self.name, self.delay)
    }
}

impl fmt::Display for Events {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let event_strs: Vec<String> = self.0.iter().map(|e| e.to_string()).collect();
        write!(f, "[{}]", event_strs.join(", "))
    }
}
