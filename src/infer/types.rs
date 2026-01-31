use crate::infer::types::struct_type::{MemberName, StructId};

pub(crate) mod struct_type;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyVar(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    Var(TyVar, Vec<TyConstr>),
    Int,
    Float,
    Bool,
    Fn(FnTy),
    Struct(StructId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FnTy {
    pub(crate) args: Vec<Ty>,
    pub(crate) ret: Box<Ty>,
}

// scheme means type scheme
// this realizes generics (parametric polymorphism)
#[derive(Debug, Clone)]
pub struct Scheme {
    pub(crate) vars: Vec<TyVar>,
    pub(crate) typ: Ty,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TyConstr {
    HasMember(MemberName),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SymId {
    Fn(FnId),
    Struct(StructId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct FnId(usize);

impl FnId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}
