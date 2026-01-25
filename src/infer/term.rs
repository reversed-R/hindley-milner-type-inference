use std::fmt::Display;

// 構文上に現れる型推論のあらゆる対象を表す`項`
//
// これの拡張によって構文上の要素の拡張ができそう
// 例えば
// - メンバアクセス
// - メソッド適用
// など
#[derive(Debug, Clone)]
pub(crate) enum Term {
    Var(TypVar),          // `x`
    Literal(TermLiteral), // `1`
    Eq(TermEq),           // `x` = `expr`
    Apply(TermApply),     // `f`(`x`, `y`)
    Fn(TermFn),           // fn `f`(`x`: t1, `y`: t2) -> t3
}

// 型変数 t を表すと同時に、
// 構文中のすべての項に一意なidとして割り当てられるため、
// これをidにして項の型の実体にアクセスできる
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct TypVar(pub(crate) usize);

#[derive(Debug, Clone)]
pub(crate) enum TermLiteral {
    Integer(u64),
    Float(f64),
    Bool(bool),
}

// when
// x: t1, y: t2
//
// ```
//  x = y;
// ```
// means
// t1 = t2
#[derive(Debug, Clone)]
pub(crate) struct TermEq {
    pub(crate) t1: TypVar,
    pub(crate) t2: TypVar,
}

#[derive(Debug, Clone)]
pub(crate) struct TermApply {
    pub(crate) f: TypVar,
    pub(crate) args: Vec<TypVar>,
}

#[derive(Debug, Clone)]
pub(crate) struct TermFn {
    pub(crate) args: Vec<TypVar>,
    pub(crate) ret: TypVar,
}

impl Display for Term {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Literal(l) => write!(f, "{l}"),
            Self::Eq(e) => write!(f, "{e}"),
            Self::Var(v) => write!(f, "{v}"),
            Self::Fn(func) => write!(f, "{func}"),
            Self::Apply(app) => write!(f, "{app}"),
        }
    }
}

impl Display for TypVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

impl Display for TermLiteral {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Integer(v) => write!(f, "Integer({v})"),
            Self::Float(v) => write!(f, "Float({v})"),
            Self::Bool(v) => write!(f, "Bool({v})"),
        }
    }
}

impl Display for TermEq {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} == {}", self.t1, self.t2)
    }
}

impl Display for TermFn {
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

impl Display for TermApply {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}( {} )",
            self.f,
            self.args
                .iter()
                .map(|a| a.to_string())
                .collect::<Vec<_>>()
                .join(","),
        )
    }
}
