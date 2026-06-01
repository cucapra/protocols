use std::ops::Index;

use cranelift_entity::{PrimaryMap, entity_impl};
use rustc_hash::FxHashMap;

use crate::frontend::serialize::serialize_type;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Arg {
    symbol: SymbolId,
}

impl Arg {
    pub fn symbol(&self) -> SymbolId {
        self.symbol
    }

    pub fn new(symbol: SymbolId) -> Self {
        Self { symbol }
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum Dir {
    In,
    Out,
}

/// Implementing the `Not` trait allows us to use the unary negation operator
/// on the `Dir` type, e.g. `!In = Out`
impl std::ops::Not for Dir {
    type Output = Dir;

    fn not(self) -> Self::Output {
        match self {
            Dir::In => Dir::Out,
            Dir::Out => Dir::In,
        }
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum SymbolKind {
    Dut,
    InPort,
    OutPort,
    Arg(u16),
    LoopVar,
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SeqId(u32);
entity_impl!(SeqId, "seq");

/// A silly little bit of indirection to work around the fact that we do not have TypeId.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Seq(Type, u64);

impl Seq {
    pub fn tpe(&self) -> Type {
        self.0
    }
    pub fn min_len(&self) -> u64 {
        self.1
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct StructId(u32);
entity_impl!(StructId, "struct");

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Struct {
    name: String,
    pins: Vec<Field>,
}

impl Struct {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn pins(&self) -> &Vec<Field> {
        &self.pins
    }

    /// Retrieves the names of all the fields of a `Struct` that
    /// have a given `direction` (either `Dir::In` or `Dir::Out`),
    /// returning an `Iterator` of field name `String`s.
    /// (Note: the names returned here are *not* fully-qualified -- instead
    /// it is the caller's responsibility to qualify the field names
    /// by the name of the struct *instance*. We do not do this in this
    /// method as we only have access to the name of the *struct type*
    /// here, as opposed to the name of the *struct instance*.)
    pub fn get_fields_by_direction(&self, direction: Dir) -> impl Iterator<Item = String> {
        self.pins.iter().filter_map(move |field| {
            if field.dir == direction {
                Some(field.name.clone())
            } else {
                None
            }
        })
    }
}

/// Datatype representing a `Field` in a `Struct`, contains:
/// - The name of the field
/// - The direction (`In` or `Out`)
/// - The `Type` of the field
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Field {
    name: String,
    dir: Dir,
    tpe: Type,
}

impl Field {
    pub fn new(name: String, dir: Dir, tpe: Type) -> Self {
        Self { name, dir, tpe }
    }

    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn dir(&self) -> Dir {
        self.dir
    }

    pub fn tpe(&self) -> Type {
        self.tpe
    }

    /// Computes the bitwidth of a `Field`. Note: this function panics
    /// if the `Type` of a `Field` is *not* a `BitVec`.
    pub fn bitwidth(&self) -> u32 {
        self.tpe.bitwidth()
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
pub enum Type {
    /// Non-negative integer with no upper bound.
    UnsignedInt,
    BitVec(u32),
    Struct(StructId),
    Seq(SeqId),
    /// Type taken on when we do not know the actual type yet
    Unknown,
}

impl Type {
    /// Checks whether two types are *equivalent*,
    /// i.e. if two bit-vector types have the same length,
    /// or if two `struct`s have the same `StructId`.
    /// NB: this function returns `false` if either type is `Unknown`,
    /// or if any of the aforementioned cases don't hold.
    pub fn is_equivalent(&self, other: &Type) -> bool {
        match (self, other) {
            (Type::BitVec(vec1), Type::BitVec(vec2)) => vec1 == vec2,
            (Type::Struct(id1), Type::Struct(id2)) => id1 == id2,
            // TODO: type inferencing to infer unknown == LHS
            (Type::Unknown, _) | (_, Type::Unknown) => false,
            _ => false,
        }
    }

    /// Computes the bitwidth of a `Type`. Note: this function panics
    /// if the `Type` is *not* a `BitVec`.
    pub fn bitwidth(&self) -> u32 {
        match self {
            Type::BitVec(width) => *width,
            Type::Struct(_) => panic!("Unable to compute bitwidth for a struct type"),
            Type::Seq(_) => panic!("Unable to compute bitwidth for a `[..]`, seq type"),
            Type::UnsignedInt => panic!("Unable to compute bitwidth for a uint"),
            Type::Unknown => panic!("Unable to compute bitwidth for Type::Unknown"),
        }
    }
}

#[derive(Clone, Copy, Hash, PartialEq, Eq, Default)]
pub struct SymbolId(u32);
entity_impl!(SymbolId, "symbol");

#[derive(Debug, Clone, Eq, PartialEq, Default)]
pub struct SymbolTable {
    entries: PrimaryMap<SymbolId, SymbolTableEntry>,
    by_name_sym: FxHashMap<String, SymbolId>,
    structs: PrimaryMap<StructId, Struct>,
    seq: PrimaryMap<SeqId, Seq>,
    by_name_struct: FxHashMap<String, StructId>,
}

/// Pretty-printer for `SymbolTable`s
impl std::fmt::Display for SymbolTable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "SymbolTable {{")?;

        // Display symbol table entries
        writeln!(f, "  Symbols:")?;
        for (symbol_id, entry) in self.entries.iter() {
            let type_str = serialize_type(self, entry.tpe());

            let parent_str = match entry.parent {
                Some(parent_id) => format!(
                    " [parent: symbol{} \"{}\"]",
                    parent_id.0, self[parent_id].name
                ),
                None => "".to_string(),
            };

            writeln!(
                f,
                "    symbol{} \"{}\": {}{}",
                symbol_id.0,
                entry.full_name(self),
                type_str,
                parent_str
            )?;
        }

        // Display structs
        if !self.structs.is_empty() {
            writeln!(f)?;
            writeln!(f, "  Structs:")?;
            for (struct_id, struct_def) in self.structs.iter() {
                writeln!(f, "    struct{} \"{}\" {{", struct_id.0, struct_def.name)?;
                for field in &struct_def.pins {
                    let type_str = serialize_type(self, field.tpe());
                    writeln!(f, "      {:?} {}: {}", field.dir, field.name, type_str)?;
                }
                writeln!(f, "    }}")?;
            }
        }

        write!(f, "}}")
    }
}

impl SymbolTable {
    pub fn add_without_parent(&mut self, name: String, tpe: Type, kind: SymbolKind) -> SymbolId {
        assert!(
            !name.contains('.'),
            "hierarchical names need to be handled externally"
        );
        let entry = SymbolTableEntry {
            name,
            tpe,
            kind,
            parent: None,
        };
        let lookup_name = entry.full_name(self);

        assert!(
            !self.by_name_sym.contains_key(&lookup_name),
            "we already have an entry for {lookup_name}!",
        );

        let id = self.entries.push(entry);
        self.by_name_sym.insert(lookup_name, id);
        id
    }

    /// Takes a string and returns the corresponding `SymbolId` (if one exists)
    pub fn symbol_id_from_name(&self, name: &str) -> Option<SymbolId> {
        self.by_name_sym.get(name).copied()
    }

    /// Takes a `SymbolId` and returns the corresponding (qualified) full name
    pub fn full_name_from_symbol_id(&self, symbol_id: &SymbolId) -> String {
        self[symbol_id].full_name(self)
    }

    pub fn update_type(&mut self, symbol_id: SymbolId, tpe: Type) {
        let entry = self.entries.get_mut(symbol_id).unwrap();
        debug_assert_eq!(entry.tpe, Type::Unknown, "Not unknown: {:?}", entry.tpe);
        entry.tpe = tpe;
    }

    pub fn add_with_parent(&mut self, name: String, parent: SymbolId) -> SymbolId {
        assert!(
            !name.contains('.'),
            "hierarchical names need to be handled externally"
        );

        let existing_pin = if let Type::Struct(structid) = self.entries[parent].tpe() {
            let fields = self.structs[structid].pins();
            fields.iter().find(|field| field.name == name)
        } else {
            None
        };

        let tpe = match existing_pin {
            Some(pin) => pin.tpe(),
            None => todo!("deal with parent not being a struct"),
        };

        let kind = match existing_pin.map(|p| p.dir) {
            Some(Dir::In) => SymbolKind::InPort,
            Some(Dir::Out) => SymbolKind::OutPort,
            None => todo!("deal with parent not being a struct"),
        };

        let entry = SymbolTableEntry {
            name,
            tpe,
            kind,
            parent: Some(parent),
        };
        let lookup_name = entry.full_name(self);

        assert!(
            !self.by_name_sym.contains_key(&lookup_name),
            "we already have an entry for {lookup_name}!",
        );

        let id = self.entries.push(entry);
        self.by_name_sym.insert(lookup_name, id);
        id
    }

    pub fn add_seq(&mut self, inner: Type, min_size: u64) -> SeqId {
        self.seq.push(Seq(inner, min_size))
    }

    pub fn add_struct(&mut self, name: String, pins: Vec<Field>) -> StructId {
        let s = Struct {
            name: name.to_string(),
            pins,
        };
        let id = self.structs.push(s);

        self.by_name_struct.insert(name, id);
        id
    }

    pub fn struct_id_from_name(&mut self, name: &str) -> Option<StructId> {
        self.by_name_struct.get(name).copied()
    }

    pub fn struct_ids(&self) -> Vec<StructId> {
        self.structs.keys().collect()
    }

    pub fn get_children(&self, parent_name: &SymbolId) -> Vec<SymbolId> {
        let mut children = vec![];
        for (id, entry) in self.entries.iter() {
            if entry.parent() == Some(*parent_name) {
                children.push(id);
            }
        }
        children
    }
}

impl Index<&str> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &str) -> &Self::Output {
        let index = self.by_name_sym[index];
        &self.entries[index]
    }
}

impl Index<SymbolId> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: SymbolId) -> &Self::Output {
        &self.entries[index]
    }
}

impl Index<&SymbolId> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &SymbolId) -> &Self::Output {
        &self.entries[*index]
    }
}

impl Index<StructId> for SymbolTable {
    type Output = Struct;

    fn index(&self, index: StructId) -> &Self::Output {
        &self.structs[index]
    }
}

impl Index<&StructId> for SymbolTable {
    type Output = Struct;

    fn index(&self, index: &StructId) -> &Self::Output {
        &self.structs[*index]
    }
}

impl Index<SeqId> for SymbolTable {
    type Output = Seq;

    fn index(&self, index: SeqId) -> &Self::Output {
        &self.seq[index]
    }
}

impl Index<&SeqId> for SymbolTable {
    type Output = Seq;

    fn index(&self, index: &SeqId) -> &Self::Output {
        &self.seq[*index]
    }
}

impl Index<Arg> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: Arg) -> &Self::Output {
        &self.entries[index.symbol]
    }
}

impl Index<&Arg> for SymbolTable {
    type Output = SymbolTableEntry;

    fn index(&self, index: &Arg) -> &Self::Output {
        &self.entries[index.symbol]
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SymbolTableEntry {
    name: String,
    tpe: Type,
    kind: SymbolKind,
    /// Used to compute the fully qualified name.
    parent: Option<SymbolId>,
}

impl SymbolTableEntry {
    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn tpe(&self) -> Type {
        self.tpe
    }

    /// Retrieves the `SymbolID` of the parent symbol
    /// (e.g. if the current entry refers to the field of a struct,
    /// then this method returns the parent struct)
    pub fn parent(&self) -> Option<SymbolId> {
        self.parent
    }

    /// full hierarchical name
    pub fn full_name(&self, symbols: &SymbolTable) -> String {
        let mut name = self.name.clone();
        let mut parent = self.parent;
        while let Some(p) = parent {
            let parent_entry = &symbols[p];
            name = format!("{}.{name}", parent_entry.name);
            parent = parent_entry.parent;
        }
        name
    }

    pub fn is_port(&self) -> bool {
        matches!(self.kind, SymbolKind::InPort | SymbolKind::OutPort)
    }
    pub fn is_in_port(&self) -> bool {
        matches!(self.kind, SymbolKind::InPort)
    }
    pub fn is_out_port(&self) -> bool {
        matches!(self.kind, SymbolKind::InPort)
    }
    pub fn as_arg_index(&self) -> Option<usize> {
        if let SymbolKind::Arg(index) = self.kind {
            Some(index as usize)
        } else {
            None
        }
    }

    pub fn is_arg(&self) -> bool {
        self.as_arg_index().is_some()
    }
    pub fn is_loop_var(&self) -> bool {
        matches!(self.kind, SymbolKind::LoopVar)
    }
}
