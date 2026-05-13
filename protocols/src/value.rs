// Copyright 2024-2026 Cornell University
// released under MIT License
// author: Nikil Shyamunder <nvs26@cornell.edu>
// author: Kevin Laeufer <laeufer@cornell.edu>
// author: Ernest Ng <eyn5@cornell.edu>

//! Shared value representation.

use baa::{BitVecOps, BitVecValue, WidthInt};

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

/// A bit-vector value that may have some unknown bits.
#[derive(Debug, Clone)]
pub struct SymBitVecValue {
    value: BitVecValue,
    known: BitVecValue,
}

impl From<BitVecValue> for SymBitVecValue {
    fn from(value: BitVecValue) -> Self {
        let known = BitVecValue::ones(value.width());
        Self { value, known }
    }
}

impl TryFrom<SymBitVecValue> for BitVecValue {
    type Error = ();

    fn try_from(value: SymBitVecValue) -> Result<Self, Self::Error> {
        if value.known.is_all_ones() {
            Ok(value.value)
        } else {
            Err(())
        }
    }
}

impl SymBitVecValue {
    pub fn unknown(width: WidthInt) -> Self {
        Self {
            value: BitVecValue::zero(width),
            known: BitVecValue::zero(width),
        }
    }

    pub fn width(&self) -> u32 {
        debug_assert_eq!(self.value.width(), self.known.width());
        self.value.width()
    }
}

#[derive(Debug, Clone)]
pub struct SymSeqValue {
    entries: Vec<SymBitVecValue>,
    /// indicates that there is a constraint that enforces the length to be exactly what
    /// the current `entries.len()` is
    len_is_known: bool,
}

impl From<Vec<BitVecValue>> for SymSeqValue {
    fn from(value: Vec<BitVecValue>) -> Self {
        let entries = value.into_iter().map(|e| e.into()).collect();
        Self {
            entries,
            len_is_known: true,
        }
    }
}

impl TryFrom<SymSeqValue> for Vec<BitVecValue> {
    type Error = ();

    fn try_from(value: SymSeqValue) -> Result<Self, Self::Error> {
        if value.len_is_known {
            value.entries.into_iter().map(|e| e.try_into()).collect()
        } else {
            Err(())
        }
    }
}

#[derive(Debug, Clone)]
pub struct SymValue(SymValueKind);

#[derive(Debug, Clone)]
enum SymValueKind {
    Scalar(SymBitVecValue),
    Seq(SymSeqValue),
}

impl From<Value> for SymValue {
    fn from(value: Value) -> Self {
        match value.0 {
            ValueKind::Scalar(v) => Self(SymValueKind::Scalar(v.into())),
            ValueKind::Seq(v) => Self(SymValueKind::Seq(v.into())),
        }
    }
}
