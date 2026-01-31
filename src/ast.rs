use std::fmt::Display;

use crate::ast::types::{FnType, StructType};

pub(crate) mod types;

pub(crate) struct Ast {
    pub(crate) fns: Vec<(AbsId, FnType)>,
    pub(crate) structs: Vec<(AbsId, StructType)>,
    pub(crate) stmts: Vec<Stmt>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct AbsId {
    quals: Vec<String>,
    id: String,
}

pub(crate) enum Stmt {
    VarDecl(VarDecl),
}

pub(crate) struct VarDecl {
    pub(crate) name: VarName,
    pub(crate) val: Expr,
}

pub(crate) enum Expr {
    Literal(Literal),
    Variable(VarName),
    Lambda(LambdaExpr),
    Call(CallExpr),
    MemberAccess(MemberAccessExpr),
    MethodCall(MethodCallExpr),
}

pub(crate) enum Literal {
    Integer(u64),
    Float(f64),
    Bool(bool),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct VarName(pub(crate) String);

pub(crate) struct LambdaExpr {
    pub(crate) args: Vec<VarName>,
    pub(crate) ret: Box<Expr>,
}

pub(crate) struct CallExpr {
    pub(crate) f: Callee,
    pub(crate) args: Vec<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Callee {
    Fn(AbsId),
    Var(VarName),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct MemberName(pub(crate) String);

pub(crate) struct MemberAccessExpr {
    pub(crate) left: Box<Expr>,
    pub(crate) member: MemberName,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct MethodName(pub(crate) String);

pub(crate) struct MethodCallExpr {
    pub(crate) method: MethodName,
    pub(crate) left: Box<Expr>,
    pub(crate) args: Vec<Expr>,
}

impl AbsId {
    pub(crate) fn new(quals: Vec<String>, id: String) -> Self {
        Self { quals, id }
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (id, s) in &self.structs {
            writeln!(f, "struct {id} {s}")?;
        }

        for (id, fntyp) in &self.fns {
            writeln!(f, "fn {id}{fntyp} {{ ... }}")?;
        }

        writeln!(f)?;
        writeln!(f, "fn target() {{")?;
        for stmt in &self.stmts {
            writeln!(f, "  {stmt}")?;
        }
        writeln!(f, "}}")?;

        Ok(())
    }
}

impl Display for AbsId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.quals.is_empty() {
            write!(f, "{}", self.id)
        } else {
            write!(
                f,
                "{}::{}",
                self.quals
                    .iter()
                    .map(|a| a.to_string())
                    .collect::<Vec<_>>()
                    .join("::"),
                self.id
            )
        }
    }
}

impl Display for Stmt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::VarDecl(v) => write!(f, "let {} = {};", v.name, v.val),
        }
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(l) => write!(f, "{l}"),
            Self::Variable(v) => write!(f, "{v}"),
            Self::Lambda(l) => write!(f, "{l}"),
            Self::Call(c) => write!(f, "{c}"),
            Self::MemberAccess(m) => write!(f, "{m}"),
            Self::MethodCall(c) => write!(f, "{c}"),
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(v) => write!(f, "{v}"),
            Self::Float(v) => write!(f, "{v}"),
            Self::Bool(v) => write!(f, "{v}"),
        }
    }
}

impl Display for VarName {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Display for LambdaExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "({}) -> {}",
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
            self.ret
        )
    }
}

impl Display for CallExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.f,
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
        )
    }
}

impl Display for Callee {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Fn(id) => write!(f, "{id}"),
            Self::Var(v) => write!(f, "{v}"),
        }
    }
}

impl Display for MemberAccessExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}.{}", self.left, self.member.0)
    }
}

impl Display for MethodCallExpr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}({})",
            self.left,
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
        )
    }
}
