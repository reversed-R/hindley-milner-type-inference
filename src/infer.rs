use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

use crate::ast::{Ast, Expr, Literal, Stmt, VarName};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TyVar(pub usize);

#[derive(Debug, Clone, PartialEq)]
pub enum Ty {
    Var(TyVar),
    Int,
    Float,
    Bool,
    Fn(FnTy),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnTy {
    pub(crate) args: Vec<Ty>,
    pub(crate) ret: Box<Ty>,
}

// scheme means type scheme
// this realizes generics (parametric polymorphism)
#[derive(Debug, Clone)]
pub struct Scheme {
    vars: Vec<TyVar>,
    typ: Ty,
}

#[derive(Debug, Default, Clone)]
pub struct TyEnv {
    map: HashMap<VarName, Scheme>,
}

#[derive(Debug)]
pub struct Infer {
    next_tv: usize,
    substitutions: HashMap<TyVar, Ty>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TyError {
    VariableNotFound(VarName),
    VariableConflicted(VarName),

    TypeVariableNotCallable(TyVar),
    FnArgLenMismatched(FnTy, FnTy),
    TypeConfliced(Ty, Ty),
    OccursCheckFailed(TyVar, Ty),
}

type TyResult<T> = Result<T, TyError>;

impl Infer {
    pub fn new() -> Self {
        Self {
            next_tv: 0,
            substitutions: HashMap::new(),
        }
    }

    fn fresh(&mut self) -> Ty {
        let v = TyVar(self.next_tv);
        self.next_tv += 1;
        Ty::Var(v)
    }

    fn apply(&self, t: Ty) -> Ty {
        match t {
            Ty::Var(v) => {
                if let Some(t2) = self.substitutions.get(&v) {
                    self.apply(t2.clone())
                } else {
                    Ty::Var(v)
                }
            }
            Ty::Fn(f) => Ty::Fn(FnTy {
                args: f.args.into_iter().map(|a| self.apply(a)).collect(),
                ret: Box::new(self.apply(*f.ret)),
            }),
            x => x,
        }
    }

    fn unify(&mut self, t1: Ty, t2: Ty) -> TyResult<()> {
        let t1 = self.apply(t1);
        let t2 = self.apply(t2);

        // FIXME: inefficient clone to return Err
        match (t1.clone(), t2.clone()) {
            (Ty::Var(v), t) | (t, Ty::Var(v)) => {
                let t = self.apply(t);
                if t == Ty::Var(v.clone()) {
                    Ok(())
                } else if occurs(&v, &t) {
                    Err(TyError::OccursCheckFailed(v, t))
                } else {
                    self.substitutions.insert(v, t);

                    Ok(())
                }
            }
            (Ty::Int, Ty::Int) | (Ty::Float, Ty::Float) | (Ty::Bool, Ty::Bool) => Ok(()),

            (Ty::Fn(f1), Ty::Fn(f2)) => {
                if f1.args.len() != f2.args.len() {
                    Err(TyError::FnArgLenMismatched(f1, f2))
                } else {
                    for (a1, a2) in f1.args.into_iter().zip(f2.args.into_iter()) {
                        self.unify(a1, a2)?;
                    }

                    self.unify(*f1.ret, *f2.ret)?;

                    Ok(())
                }
            }
            _ => Err(TyError::TypeConfliced(t1, t2)),
        }
    }

    fn ftv(t: &Ty) -> HashSet<TyVar> {
        match t {
            Ty::Var(v) => [v.clone()].into(),
            Ty::Fn(f) => {
                let mut s = HashSet::new();
                for a in &f.args {
                    s.extend(Self::ftv(a));
                }
                s.extend(Self::ftv(&f.ret));
                s
            }
            _ => HashSet::new(),
        }
    }

    fn ftv_scheme(s: &Scheme) -> HashSet<TyVar> {
        let mut ftv = Self::ftv(&s.typ);
        for v in &s.vars {
            ftv.remove(v);
        }
        ftv
    }

    fn ftv_env(env: &TyEnv) -> HashSet<TyVar> {
        env.map.values().flat_map(Self::ftv_scheme).collect()
    }

    fn generalize(&self, env: &TyEnv, t: Ty) -> Scheme {
        let ftv_t = Self::ftv(&t);
        let ftv_env = Self::ftv_env(env);

        let vars = ftv_t.difference(&ftv_env).cloned().collect::<Vec<_>>();

        Scheme { vars, typ: t }
    }

    fn instantiate(&mut self, s: &Scheme) -> Ty {
        let mut m = HashMap::new();

        for v in &s.vars {
            m.insert(v.clone(), self.fresh());
        }

        fn go(t: &Ty, m: &HashMap<TyVar, Ty>) -> Ty {
            match t {
                Ty::Var(v) => m.get(v).cloned().unwrap_or(Ty::Var(v.clone())),
                Ty::Fn(f) => Ty::Fn(FnTy {
                    args: f.args.iter().map(|a| go(a, m)).collect(),
                    ret: Box::new(go(&f.ret, m)),
                }),
                x => x.clone(),
            }
        }

        go(&s.typ, &m)
    }

    fn infer_expr(&mut self, env: &mut TyEnv, expr: &Expr) -> TyResult<Ty> {
        match expr {
            Expr::Literal(Literal::Integer(_)) => Ok(Ty::Int),
            Expr::Literal(Literal::Float(_)) => Ok(Ty::Float),
            Expr::Literal(Literal::Bool(_)) => Ok(Ty::Bool),

            Expr::Variable(v) => {
                let scheme = env.map.get(v).expect("unbound variable");
                Ok(self.instantiate(scheme))
            }

            Expr::Lambda(l) => {
                let mut local_env = env.clone();

                let args: Vec<Ty> = l
                    .args
                    .iter()
                    .map(|a| {
                        let tv = self.fresh();
                        local_env.map.insert(
                            a.clone(),
                            Scheme {
                                vars: vec![],
                                typ: tv.clone(),
                            },
                        );
                        tv
                    })
                    .collect();

                let body = self.infer_expr(&mut local_env, &l.ret)?;

                Ok(Ty::Fn(FnTy {
                    args,
                    ret: Box::new(body),
                }))
            }

            Expr::Call(c) => {
                let f = self.infer_expr(env, &Expr::Variable(c.f.clone()))?;
                let args = c
                    .args
                    .iter()
                    .map(|a| self.infer_expr(env, a))
                    .collect::<Result<_, _>>()?;

                let ret = self.fresh();
                self.unify(
                    f,
                    Ty::Fn(FnTy {
                        args,
                        ret: Box::new(ret.clone()),
                    }),
                )?;

                Ok(ret)
            }
        }
    }
}

fn occurs(v: &TyVar, t: &Ty) -> bool {
    match t {
        Ty::Var(v2) => v == v2,
        Ty::Fn(f) => f.args.iter().any(|a| occurs(v, a)) || occurs(v, &f.ret),
        _ => false,
    }
}

#[derive(Debug)]
pub struct InferedTys {
    pub schemes: HashMap<VarName, Scheme>,
    pub tys: HashMap<VarName, Ty>,
}

pub fn infer_ast(ast: &Ast) -> TyResult<InferedTys> {
    let mut infer = Infer::new();
    let mut env = TyEnv::default();
    let mut tys = HashMap::new();

    for stmt in &ast.stmts {
        match stmt {
            Stmt::VarDecl(v) => {
                let t = infer.infer_expr(&mut env, &v.val)?;
                let t = infer.apply(t);
                let scheme = infer.generalize(&env, t.clone());
                env.map.insert(v.name.clone(), scheme);
                tys.insert(v.name.clone(), t);
            }
        }
    }

    Ok(InferedTys {
        schemes: env.map,
        tys,
    })
}

impl InferedTys {
    // for test
    pub fn can_apply(&self, var: &VarName, f: FnTy) -> TyResult<()> {
        let mut infer = Infer::new();
        let f_scheme = self
            .schemes
            .get(var)
            .ok_or(TyError::VariableNotFound(var.clone()))?;

        let t = infer.instantiate(f_scheme);
        infer.unify(t.clone(), Ty::Fn(f))
    }
}

impl Display for TyVar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "t{}", self.0)
    }
}

impl Display for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Var(v) => write!(f, "{v}"),
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Bool => write!(f, "Bool"),
            Self::Fn(func) => write!(f, "{func}"),
        }
    }
}

impl Display for FnTy {
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

impl Display for Scheme {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for v in &self.vars {
            write!(f, "∀{v}")?;
        }

        if !self.vars.is_empty() {
            write!(f, ". ")?;
        }

        write!(f, "{}", self.typ)
    }
}

impl Display for InferedTys {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (v, s) in &self.schemes {
            writeln!(f, "{v}: {s}")?;
        }

        Ok(())
    }
}
