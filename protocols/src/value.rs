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
    pub fn new(value: BitVecValue, known: BitVecValue) -> Self {
        debug_assert_eq!(value.width(), known.width());
        Self { value, known }
    }

    pub fn unknown(width: u32) -> Self {
        Self {
            value: BitVecValue::zero(width),
            known: BitVecValue::zero(width),
        }
    }

    pub fn width(&self) -> u32 {
        debug_assert_eq!(self.value.width(), self.known.width());
        self.value.width()
    }

    pub fn to_string(&self, display_hex: bool) -> String {
        if self.known.is_all_ones() {
            if display_hex {
                format!("0x{}", self.value.to_hex_str())
            } else {
                self.value.to_dec_str()
            }
        } else if self.known.is_zero() {
            // TODO: do we actually want to keep this behavior?
            "X".to_string()
        } else if self.width().is_multiple_of(4) {
            // we first try to output as hex
            let hex_known = self.known.to_hex_str();
            if hex_known.chars().all(|c| matches!(c, '0' | 'f')) {
                let hex_value = self.value.to_hex_str();
                debug_assert_eq!(hex_known.chars().count(), hex_value.chars().count());
                "0x".chars()
                    .chain(hex_value.chars().zip(hex_known.chars()).map(|(v, k)| {
                        if k == 'f' {
                            v
                        } else {
                            debug_assert_eq!(k, '0');
                            'x' // unknown
                        }
                    }))
                    .collect()
            } else {
                self.to_bit_string()
            }
        } else {
            self.to_bit_string()
        }
    }

    fn to_bit_string(&self) -> String {
        "0b".chars()
            .chain((0..self.width()).rev().map(|ii| {
                match (self.known.is_bit_set(ii), self.value.is_bit_set(ii)) {
                    (true, true) => '1',
                    (true, false) => '0',
                    (false, _) => 'x',
                }
            }))
            .collect()
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
        Self::new(entries, true)
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

impl SymSeqValue {
    pub fn new(entries: Vec<SymBitVecValue>, len_is_known: bool) -> Self {
        if let Some(f) = entries.first() {
            let width = f.width();
            debug_assert!(entries.iter().all(|e| e.width() == width));
        }
        Self {
            entries,
            len_is_known,
        }
    }

    pub fn to_string(&self, _display_hex: bool) -> String {
        todo!()
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

impl SymValue {
    pub fn new_scalar(value: BitVecValue, known: BitVecValue) -> Self {
        let s = SymBitVecValue::new(value, known);
        Self(SymValueKind::Scalar(s))
    }

    pub fn new_seq(entries: Vec<SymBitVecValue>, len_is_known: bool) -> Self {
        let s = SymSeqValue::new(entries, len_is_known);
        Self(SymValueKind::Seq(s))
    }

    pub fn to_string(&self, display_hex: bool) -> String {
        match &self.0 {
            SymValueKind::Scalar(v) => v.to_string(display_hex),
            SymValueKind::Seq(v) => v.to_string(display_hex),
        }
    }
}
