// Copyright 2024-2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

//! Shared value representation.

use baa::BitVecOps;
use baa::BitVecValue;

/// A concrete value of any type.
#[derive(Debug, Clone)]
pub struct Value(ValueKind);

#[derive(Debug, Clone)]
enum ValueKind {
    Scalar(BitVecValue),
    Seq(Vec<BitVecValue>),
}

impl TryFrom<Value> for BitVecValue {
    type Error = ();
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value(ValueKind::Scalar(v)) => Ok(v),
            _ => Err(()),
        }
    }
}

impl<'a> TryFrom<&'a Value> for &'a BitVecValue {
    type Error = ();
    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match value {
            Value(ValueKind::Scalar(v)) => Ok(v),
            _ => Err(()),
        }
    }
}

impl From<BitVecValue> for Value {
    fn from(value: BitVecValue) -> Self {
        Value(ValueKind::Scalar(value))
    }
}

impl TryFrom<Value> for Vec<BitVecValue> {
    type Error = ();
    fn try_from(value: Value) -> Result<Self, Self::Error> {
        match value {
            Value(ValueKind::Seq(v)) => Ok(v),
            _ => Err(()),
        }
    }
}

impl From<Vec<BitVecValue>> for Value {
    fn from(value: Vec<BitVecValue>) -> Self {
        Value(ValueKind::Seq(value))
    }
}

impl<'a> TryFrom<&'a Value> for &'a [BitVecValue] {
    type Error = ();
    fn try_from(value: &'a Value) -> Result<Self, Self::Error> {
        match value {
            Value(ValueKind::Seq(v)) => Ok(v.as_slice()),
            _ => Err(()),
        }
    }
}

impl Value {
    pub fn to_hex_str(&self) -> String {
        match &self.0 {
            ValueKind::Scalar(bv) => bv.to_hex_str(),
            ValueKind::Seq(values) => {
                let values: Vec<_> = values.iter().map(|v| v.to_hex_str()).collect();
                format!("[{}]", values.join(", "))
            }
        }
    }

    pub fn to_dec_str(&self) -> String {
        match &self.0 {
            ValueKind::Scalar(bv) => bv.to_dec_str(),
            ValueKind::Seq(values) => {
                let values: Vec<_> = values.iter().map(|v| v.to_dec_str()).collect();
                format!("[{}]", values.join(", "))
            }
        }
    }
}
