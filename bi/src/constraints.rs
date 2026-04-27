// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecMutOps, BitVecOps, BitVecValue, WidthInt};
use protocols::ir::{Arg, SymbolTable, Type};
use protocols::serialize::serialize_type;

#[derive(Debug, Clone)]
pub enum ArgValue {
    Seq(SeqValue),
    Data(DataValue),
}

impl ArgValue {
    pub fn unknown(sym: &SymbolTable, arg: &Arg) -> Self {
        match sym[arg.symbol()].tpe() {
            // model undigned int ad u64
            Type::UnsignedInt => Self::Data(DataValue::unknown(64)),
            Type::BitVec(w) => Self::Data(DataValue::unknown(w)),
            Type::Seq(seq_id) => {
                if let Type::BitVec(w) = sym[seq_id].tpe() {
                    Self::Seq(SeqValue::unknown(w, sym[seq_id].min_len()))
                } else {
                    todo!(
                        "Only [u..] is supported. Not: {}",
                        serialize_type(sym, sym[seq_id].tpe())
                    )
                }
            }
            Type::Struct(_) => unreachable!("args cannot be structs"),
            Type::Unknown => unreachable!("arg types are always known"),
        }
    }

    pub fn get_known(&self) -> Option<BitVecValue> {
        match self {
            ArgValue::Data(d) => d.get_known(),
            ArgValue::Seq(_) => todo!("seq value get known"),
        }
    }

    pub fn as_seq_mut(&mut self) -> Option<&mut SeqValue> {
        if let Self::Seq(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_seq(&self) -> Option<&SeqValue> {
        if let Self::Seq(v) = self {
            Some(v)
        } else {
            None
        }
    }

    pub fn as_scalar_mut(&mut self) -> Option<&mut DataValue> {
        if let Self::Data(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub struct DataValue {
    value: BitVecValue,
    known: BitVecValue,
}

impl DataValue {
    fn unknown(width: WidthInt) -> Self {
        Self {
            value: BitVecValue::zero(width),
            known: BitVecValue::zero(width),
        }
    }

    pub fn get_known(&self) -> Option<BitVecValue> {
        if self.known.is_all_ones() {
            Some(self.value.clone())
        } else {
            None
        }
    }

    #[allow(dead_code)]
    fn bit_is_known(&self, bit: WidthInt) -> bool {
        self.known.is_bit_set(bit)
    }

    #[allow(dead_code)]
    fn define_bit(&mut self, bit: WidthInt, value: u8) {
        debug_assert!(!self.bit_is_known(bit));
        debug_assert!(bit < self.value.width());
        if value != 0 {
            self.value.set_bit(bit);
        }
        self.known.set_bit(bit);
    }

    pub fn define_value(&mut self, value: BitVecValue) {
        debug_assert_eq!(self.value.width(), value.width());
        self.value = value;
        self.known = BitVecValue::ones(self.value.width());
    }
}

#[derive(Debug, Clone)]
pub struct SeqValue {
    width: WidthInt,
    /// indicates that there is a constraint that enforces the length to be exactly what
    /// the current `values.len()` is
    len_is_known: bool,
    values: Vec<DataValue>,
}

impl SeqValue {
    fn unknown(width: WidthInt, min_len: u64) -> Self {
        Self {
            width,
            len_is_known: false,
            values: vec![DataValue::unknown(width); min_len as usize],
        }
    }

    pub fn get_known_len(&self) -> Option<u64> {
        if self.len_is_known {
            Some(self.values.len() as u64)
        } else {
            None
        }
    }

    pub fn get_known(&self, index: u64) -> Option<BitVecValue> {
        self.values[index as usize].get_known()
    }

    pub fn define_value(&mut self, index: u64, value: BitVecValue) {
        self.values[index as usize].define_value(value);
    }

    pub fn freeze_len(&mut self) {
        debug_assert!(!self.len_is_known);
        self.len_is_known = true;
    }

    pub fn increment_unknown_len(&mut self) {
        debug_assert!(!self.len_is_known);
        self.values.push(DataValue::unknown(self.width));
    }

    pub fn min_len(&self) -> u64 {
        self.values.len() as u64
    }
}
