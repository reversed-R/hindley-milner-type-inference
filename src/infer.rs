use std::{collections::HashMap, fmt::Display};

mod builder;
pub(crate) mod types;

use crate::{
    ast::{AbsId, Ast, Callee, Expr, Literal, MemberName, MethodName, Stmt, VarName},
    infer::{
        builder::TyBuilder,
        types::{
            FnId, FnTy, Scheme, SymId, Ty, TyVar,
            struct_type::{StructId, StructTy},
        },
    },
};

#[derive(Debug, Clone)]
pub struct TyEnv {
    schemes: HashMap<VarName, Scheme>,
    structs: HashMap<StructId, StructTy>,
    fns: HashMap<FnId, FnTy>,
    syms: HashMap<AbsId, SymId>,
    method_impls: HashMap<Ty, HashMap<MethodName, FnTy>>,
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

    SymbolNotFound(AbsId),
    StructMemberConfliced(AbsId, MemberName),
    MethodConfliced(Ty, MethodName),
    SymbolNotAType(AbsId),

    TypeVariableNotCallable(TyVar),
    FnArgLenMismatched(FnTy, FnTy),
    TypeConfliced(Ty, Ty),
    OccursCheckFailed(TyVar, Ty),
    MemberNotFound(Ty, MemberName),
    MethodNotImpled(Ty, MethodName),
    InsufficientContext,
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
        Ty::Var(v, vec![])
    }

    fn apply(&self, t: Ty) -> Ty {
        match t {
            Ty::Var(v, c) => {
                if let Some(t2) = self.substitutions.get(&v) {
                    self.apply(t2.clone())
                } else {
                    Ty::Var(v, c)
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
            (Ty::Var(v, c), t) | (t, Ty::Var(v, c)) => {
                let t = self.apply(t);
                if t == Ty::Var(v.clone(), c.clone()) {
                    // TODO: constraintsも含んで正しく等価計算をする関数を定義
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

    // fn ftv(t: &Ty) -> HashSet<TyVar> {
    //     match t {
    //         Ty::Var(v) => [v.clone()].into(),
    //         Ty::Fn(f) => {
    //             let mut s = HashSet::new();
    //             for a in &f.args {
    //                 s.extend(Self::ftv(a));
    //             }
    //             s.extend(Self::ftv(&f.ret));
    //             s
    //         }
    //         _ => HashSet::new(),
    //     }
    // }
    //
    // fn ftv_scheme(s: &Scheme) -> HashSet<TyVar> {
    //     let mut ftv = Self::ftv(&s.typ);
    //     for v in &s.vars {
    //         ftv.remove(v);
    //     }
    //     ftv
    // }
    //
    // fn ftv_env(env: &TyEnv) -> HashSet<TyVar> {
    //     env.schemes.values().flat_map(Self::ftv_scheme).collect()
    // }

    fn instantiate(&mut self, s: &Scheme) -> Ty {
        let mut m = HashMap::new();

        for v in &s.vars {
            m.insert(v.clone(), self.fresh());
        }

        fn go(t: &Ty, m: &HashMap<TyVar, Ty>) -> Ty {
            match t {
                // WARN: really?
                Ty::Var(v, _) => m.get(v).cloned().unwrap_or(Ty::Var(v.clone(), vec![])),
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
                let scheme = env
                    .schemes
                    .get(v)
                    .ok_or(TyError::VariableNotFound(v.clone()))?;
                Ok(self.instantiate(scheme))
            }

            Expr::Lambda(l) => {
                let mut local_env = env.clone();

                let args: Vec<Ty> = l
                    .args
                    .iter()
                    .map(|a| {
                        let tv = self.fresh();
                        local_env.schemes.insert(
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

            Expr::Call(c) => match &c.f {
                Callee::Fn(id) => {
                    let f = if let Some(SymId::Fn(id)) = env.syms.get(id) {
                        env.fns.get(id).expect("not found").clone()
                    } else {
                        return Err(TyError::SymbolNotFound(id.clone()));
                    };
                    let callee_ret = (*f.ret).clone();

                    let args = c
                        .args
                        .iter()
                        .map(|a| self.infer_expr(env, a))
                        .collect::<Result<_, _>>()?;
                    let ret = self.fresh();

                    self.unify(
                        Ty::Fn(f),
                        Ty::Fn(FnTy {
                            args,
                            ret: Box::new(ret),
                        }),
                    )?;

                    Ok(callee_ret)
                }
                Callee::Var(v) => {
                    let f = self.infer_expr(env, &Expr::Variable(v.clone()))?;

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
            },

            Expr::MemberAccess(m) => {
                let left = self.infer_expr(env, &m.left)?;

                match left.clone() {
                    Ty::Int | Ty::Float | Ty::Bool | Ty::Fn(_) => {
                        Err(TyError::MemberNotFound(left, m.member.clone()))
                    }
                    Ty::Var(_, _) => Err(TyError::InsufficientContext),
                    Ty::Struct(s) => env
                        .structs
                        .get(&s)
                        .unwrap()
                        .members
                        .get(&m.member.clone().into())
                        .ok_or(TyError::MemberNotFound(left, m.member.clone()))
                        .cloned(),
                }
            }

            Expr::MethodCall(m) => {
                let left = self.infer_expr(env, &m.left)?;

                match left.clone() {
                    Ty::Var(_, _) => Err(TyError::InsufficientContext),
                    // NOTE: leftの具体の型が判明するならmethodをimplしているかどうか判定できる
                    Ty::Int | Ty::Float | Ty::Bool | Ty::Fn(_) | Ty::Struct(_) => {
                        let f = env
                            .method_impls
                            .get(&left)
                            .unwrap()
                            .get(&m.method)
                            .ok_or(TyError::MethodNotImpled(left, m.method.clone()))
                            .cloned()?;

                        let args = m
                            .args
                            .iter()
                            .map(|a| self.infer_expr(env, a))
                            .collect::<Result<_, _>>()?;

                        let ret = (*f.ret).clone();

                        let tv = self.fresh();
                        self.unify(
                            Ty::Fn(f),
                            Ty::Fn(FnTy {
                                args,
                                ret: Box::new(tv),
                            }),
                        )?;

                        Ok(ret)
                    }
                }
            }
        }
    }
}

fn occurs(v: &TyVar, t: &Ty) -> bool {
    match t {
        Ty::Var(v2, _) => v == v2,
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
    let mut env = TyEnv::new(ast)?;
    let mut tys = HashMap::new();

    for stmt in &ast.stmts {
        match stmt {
            Stmt::VarDecl(v) => {
                let t = infer.infer_expr(&mut env, &v.val)?;
                let t = infer.apply(t);
                env.schemes.insert(
                    v.name.clone(),
                    Scheme {
                        vars: vec![], // 単一の型を割り当てるため、量化しない
                        typ: t.clone(),
                    },
                );
                tys.insert(v.name.clone(), t);
            }
        }
    }

    Ok(InferedTys {
        schemes: env.schemes,
        tys,
    })
}

impl TyEnv {
    fn new(ast: &Ast) -> TyResult<Self> {
        let mut builder = TyBuilder::new(ast);

        for (id, s) in &ast.structs {
            builder.build_and_store_struct_ty(id.clone(), s.clone())?;
        }

        for (id, f) in &ast.fns {
            builder.build_and_store_fn_ty(id.clone(), f.clone())?;
        }

        for (typ, methods) in &ast.method_impls {
            for (method, ftyp) in methods {
                builder.build_and_store_method(typ.clone(), method.clone(), ftyp.clone())?;
            }
        }

        Ok(Self {
            schemes: HashMap::new(),
            structs: builder.structs,
            fns: builder.fns,
            syms: builder.syms,
            method_impls: builder.method_impls,
        })
    }
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
            Self::Var(v, _) => write!(f, "{v}"),
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Bool => write!(f, "Bool"),
            Self::Fn(func) => write!(f, "{func}"),
            Self::Struct(id) => write!(f, "struct {id}"),
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
