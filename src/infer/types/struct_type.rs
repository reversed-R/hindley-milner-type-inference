use std::{collections::HashMap, fmt::Display};

use crate::infer::types::Ty;

#[derive(Debug, Clone)]
pub struct StructTy {
    pub(crate) members: HashMap<MemberName, Ty>,
    pub(crate) vars: Vec<Ty>, // generics
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct MemberName(pub(crate) String);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct StructId(usize);

impl StructId {
    pub fn new(id: usize) -> Self {
        Self(id)
    }
}

impl Display for StructId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<crate::ast::MemberName> for MemberName {
    fn from(value: crate::ast::MemberName) -> Self {
        Self(value.0)
    }
}
