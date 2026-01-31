use std::fmt::Display;

use crate::ast::{AbsId, MemberName};

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Int,
    Float,
    Bool,
    Fn(FnType),
    Defined(AbsId),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnType {
    pub(crate) args: Vec<Type>,
    pub(crate) ret: Box<Type>,
    // pub(crate) genargs: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct StructType {
    pub(crate) members: Vec<(MemberName, Type)>,
    // pub(crate) genargs: Vec<String>,
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Bool => write!(f, "Bool"),
            Self::Fn(ftyp) => write!(f, "{ftyp}"),
            Self::Defined(id) => write!(f, "{id}"),
        }
    }
}

impl Display for FnType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
            *self.ret
        )
    }
}

impl Display for StructType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "{{")?;
        for (m, typ) in &self.members {
            writeln!(f, "  {}: {typ},", m.0)?;
        }
        writeln!(f, "}}")
    }
}
