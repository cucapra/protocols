// Copyright 2026 Cornell University
// released under MIT License
// author: Kevin Laeufer <laeufer@cornell.edu>

use baa::{BitVecMutOps, BitVecOps, BitVecValue, WidthInt};
use protocols::ir::{Arg, SymbolTable, Type};

#[derive(Debug, Clone)]
pub enum ArgValue {
    Data(DataValue),
    Repeat(RepeatValue),
}

impl ArgValue {
    pub fn unknown(sym: &SymbolTable, arg: &Arg) -> Self {
        match sym[arg.symbol()].tpe() {
            Type::UnsignedInt => Self::Repeat(RepeatValue::default()),
            Type::BitVec(w) => Self::Data(DataValue::unknown(w)),
            Type::Seq(_) => todo!("handle seq constraints"),
            Type::Struct(_) => unreachable!("args cannot be structs"),
            Type::Unknown => unreachable!("arg types are always known"),
        }
    }

    pub fn get_known(&self) -> Option<BitVecValue> {
        match self {
            ArgValue::Data(d) => d.get_known(),
            ArgValue::Repeat(RepeatValue::Exactly(v, _)) => {
                Some(BitVecValue::from_u64(*v as u64, 32))
            }
            ArgValue::Repeat(RepeatValue::AtLeast(_)) => None,
        }
    }

    pub fn as_repeat(&mut self) -> Option<&mut RepeatValue> {
        if let Self::Repeat(v) = self {
            Some(v)
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
pub enum RepeatValue {
    AtLeast(u32),
    Exactly(u32, u32),
}

impl Default for RepeatValue {
    fn default() -> Self {
        Self::AtLeast(0)
    }
}

impl RepeatValue {
    pub fn current_value(&self) -> u32 {
        match self {
            RepeatValue::AtLeast(v) => *v,
            RepeatValue::Exactly(_, v) => *v,
        }
    }

    pub fn increment_current_value(&mut self) {
        match self {
            RepeatValue::AtLeast(v) => *v += 1,
            RepeatValue::Exactly(b, v) => {
                if *v + 1 == *b {
                    *v = 0;
                } else {
                    *v += 1;
                }
                debug_assert!(*v < *b, "{} < {}", *v, *b);
            }
        }
    }

    pub fn num_iters(&self) -> Option<u32> {
        match self {
            RepeatValue::AtLeast(_) => None,
            RepeatValue::Exactly(b, _) => Some(*b),
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

    fn get_known(&self) -> Option<BitVecValue> {
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
