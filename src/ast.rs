use std::fmt::Display;

use log::info;

pub(crate) struct Ast {
    pub(crate) stmts: Vec<Stmt>,
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
    pub(crate) f: VarName,
    pub(crate) args: Vec<Expr>,
}

impl Ast {
    pub(crate) fn print(&self) {
        info!("{self}");
    }
}

impl Display for Ast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for stmt in &self.stmts {
            writeln!(f, "{stmt}")?;
        }

        Ok(())
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
