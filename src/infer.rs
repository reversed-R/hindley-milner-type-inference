use log::{debug, info};
use rand::seq::IndexedRandom;
use std::{
    collections::{HashMap, HashSet},
    fmt::Display,
};

pub(crate) mod init;
mod term;
mod union_find;

use crate::{
    ast::VarName,
    infer::{
        init::{ScopeId, VariablePool},
        term::{Term, TermLiteral, TypVar},
        union_find::UnionFind,
    },
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Typ {
    Int,
    Float,
    Bool,
    Fn(FnTyp), // Defined(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct FnTyp {
    pub(crate) args: Vec<Typ>,
    pub(crate) ret: Box<Typ>,
}

/// TypEnv represents environment for type inference.
///
/// NOTE: `variables` do not means type variables but variables in the original language AST.
#[derive(Debug)]
pub struct TypEnv {
    substitutions: HashMap<TypVar, Typ>,
    constraints: HashMap<TypVar, Term>,
    variables: VariablePool,
    unifications: HashMap<TypVar, TypVar>,
}

#[derive(Debug, Clone)]
pub enum TypeError {
    VariableNotFound(VarName),
    VariableConflicted(VarName),

    TypeVariableNotCallable(TypVar),
    FnArgLenMismatched(TypVar, TypVar),
    TypeConfliced(TypVar, Typ, Typ),
}

#[derive(Debug)]
pub struct InferedTypes {
    pub(crate) variables: HashMap<(VarName, ScopeId), Typ>,
}

impl TypEnv {
    pub fn infer(mut self) -> Result<InferedTypes, TypeError> {
        let mut rng = rand::rng();

        // randでランダムにconstraintsを取得している
        // が、それって本当?という感がある。
        while let Some(&&t) = self.constraints.keys().collect::<Vec<_>>().choose(&mut rng) {
            let c = self.constraints.get(&t).unwrap().clone();
            debug!("{t} == {c}");

            match c {
                Term::Eq(e) => {
                    // 等価な2つの型変数はunifiyし、
                    // 制約を取り除いた状態にする
                    self.unify(&[(e.t1, e.t2)]);
                    self.constraints.remove(&t);
                }
                Term::Var(v) => {
                    // Varの参照する型変数vについて型変数tと同一でないならば
                    //   型変数tをvでunifyし、
                    //   Varを取り除いた状態にする
                    if t != v {
                        self.unify(&[(t, v)]);
                        self.constraints.remove(&t);
                    }
                }
                Term::Fn(f) => {
                    // Fnの引数や戻り値の型変数が
                    // - すべてsubstitutionを持っているならば
                    //   - substituteする
                    // - そうでないならば、constraintsに含んだままにする
                    let mut all_substituted = true;
                    for a in &f.args {
                        if let Some(typ) = self.get_substitution(a) {
                            self.substitute(*a, typ.clone())?;
                        } else {
                            all_substituted = false;
                        }
                    }
                    if let Some(typ) = self.get_substitution(&f.ret) {
                        self.substitute(f.ret, typ.clone())?;
                    } else {
                        all_substituted = false;
                    }

                    if all_substituted {
                        let args = f
                            .args
                            .iter()
                            .map(|a| self.get_substitution(a).cloned())
                            .collect::<Option<Vec<_>>>()
                            .unwrap();
                        let ret = self.get_substitution(&f.ret).unwrap();
                        self.substitute(
                            t,
                            Typ::Fn(FnTyp {
                                args,
                                ret: Box::new(ret.clone()),
                            }),
                        )?;
                    }
                }
                Term::Apply(app) => {
                    // Applyの関数fを取得し、
                    // 関数であり、引数の長さが一致していることを確認
                    // ApplyとFnの引数の型変数の対応でunifiy
                    if let Some(term) = self.constraints.get(&app.f) {
                        match term {
                            Term::Fn(f) => {
                                if f.args.len() != app.args.len() {
                                    return Err(TypeError::FnArgLenMismatched(t, app.f));
                                } else {
                                    let reps = f
                                        .args
                                        .iter()
                                        .zip(app.args.iter())
                                        .map(|(x, y)| (*x, *y))
                                        .collect::<Vec<_>>();

                                    self.unify(&reps);

                                    // 引数の型変数にsubstitutionがあればしておく
                                    for a in &app.args {
                                        if let Some(typ) = self.get_substitution(a) {
                                            self.substitute(t, typ.clone())?;
                                        }
                                    }
                                }
                            }
                            Term::Eq(_) | Term::Var(_) | Term::Apply(_) => {
                                // nothing to do
                            }
                            Term::Literal(_) => {
                                return Err(TypeError::TypeVariableNotCallable(app.f));
                            }
                        }
                    } else if let Some(Typ::Fn(f)) = self.get_substitution(&app.f).cloned() {
                        // fがsubstitutionを持っている場合、
                        // 引数の型変数はfの引数の型変数の型でそれぞれsubstitutionされ、
                        // App全体の型変数はfの戻り値の型変数の型でsubstitutionされる
                        if f.args.len() != app.args.len() {
                            return Err(TypeError::FnArgLenMismatched(t, app.f));
                        } else {
                            for (t, typ) in app.args.iter().zip(f.args.iter()) {
                                self.substitute(*t, typ.clone())?;
                            }

                            self.substitute(t, *f.ret)?;
                        }
                    } else {
                        // NOTE: TypEnvの初期化時に変数の存在チェックはしているため、
                        // ただのNoneになることはない。
                        // つまり、ここに来るのはTermがFn以外だったときのみ。
                        return Err(TypeError::TypeVariableNotCallable(app.f));
                    }
                }
                Term::Literal(l) => match l {
                    // 簡単のためリテラルは直ちに型が付くとする
                    TermLiteral::Integer(_) => {
                        // 本当はIntegerはIntかUintかLongかくらいの推論はさせたい
                        self.substitute(t, Typ::Int)?;
                    }
                    TermLiteral::Float(_) => {
                        self.substitute(t, Typ::Float)?;
                    }
                    TermLiteral::Bool(_) => {
                        self.substitute(t, Typ::Bool)?;
                    }
                },
            }
        }

        let mut variables = HashMap::new();
        for (sid, vars) in &self.variables.scopes {
            for (v, t) in vars {
                variables.insert(
                    (v.clone(), sid.clone()),
                    self.get_substitution(t).unwrap().clone(),
                );
            }
        }

        Ok(InferedTypes { variables })
    }

    // 制約の集合constraintsのうち、
    // 型変数oldから型変数newへの置換の組
    // (old: TypVar, new: TypVar)
    // の列 reps によって
    // 複数の型変数を一括でunifyする
    fn unify(&mut self, reps: &[(TypVar, TypVar)]) {
        debug!(
            "unifiy: [{}]",
            reps.iter()
                .filter(|(old, new)| old != new)
                .map(|(old, new)| format!("{old} => {new}"))
                .collect::<Vec<_>>()
                .join(",")
        );

        // 置換の組の列 reps から
        // 置換のHashMap norm(normalizer)を計算
        let norm = self.build_normalizer(reps);

        if norm.is_empty() {
            return;
        }

        for c in self.constraints.values_mut() {
            match c {
                Term::Fn(f) => {
                    for a in f.args.iter_mut() {
                        if let Some(new) = norm.get(a) {
                            *a = *new;
                        }
                    }

                    if let Some(new) = norm.get(&f.ret) {
                        f.ret = *new;
                    }
                }
                Term::Apply(app) => {
                    if let Some(new) = norm.get(&app.f) {
                        app.f = *new;
                    }

                    for a in app.args.iter_mut() {
                        if let Some(new) = norm.get(a) {
                            *a = *new;
                        }
                    }
                }
                Term::Eq(e) => {
                    if let Some(new) = norm.get(&e.t1) {
                        e.t1 = *new;
                    }
                    if let Some(new) = norm.get(&e.t2) {
                        e.t2 = *new;
                    }
                }
                Term::Var(v) => {
                    if let Some(new) = norm.get(v) {
                        *v = *new;
                    }
                }
                Term::Literal(_) => {}
            }
        }

        // 型変数dstが型変数srcにunifyされたことを記録
        // 最後に結果を復元する際に使用
        self.unifications = norm;
    }

    fn substitute(&mut self, tv: TypVar, typ: Typ) -> Result<(), TypeError> {
        // constraintsから除去し、
        // substitutionsに追加する
        self.constraints.remove(&tv);
        if let Some(existence_typ) = self.substitutions.get(&tv) {
            if &typ != existence_typ {
                Err(TypeError::TypeConfliced(tv, existence_typ.clone(), typ))
            } else {
                Ok(())
            }
        } else {
            debug!("substitute: {tv} = {typ}");
            self.substitutions.insert(tv, typ);

            Ok(())
        }
    }

    // reps: (old: TypVar, new: TypVar) の置換の組の集まり
    fn build_normalizer(&mut self, reps: &[(TypVar, TypVar)]) -> HashMap<TypVar, TypVar> {
        let mut uf = UnionFind::new();

        // すべて union
        for (x, y) in &self.unifications {
            uf.union(*x, *y);
        }
        for &(old, new) in reps {
            uf.union(old, new);
        }

        // 登場するすべての 型変数 を集める
        let mut ts = HashSet::new();
        for (x, y) in &self.unifications {
            ts.insert(*x);
            ts.insert(*y);
        }
        for &(old, new) in reps {
            ts.insert(old);
            ts.insert(new);
        }

        // 各 TypVar -> 代表 TypVar
        let mut normalizer = HashMap::new();
        for t in ts {
            let root = uf.find(t);
            normalizer.insert(t, root);
        }

        normalizer
    }

    fn get_substitution(&self, t: &TypVar) -> Option<&Typ> {
        self.substitutions
            .get(self.unifications.get(t).unwrap_or(t))
    }
}

impl InferedTypes {
    pub fn print(&self) {
        for ((v, sid), typ) in &self.variables {
            info!("{v} ({sid}): {typ}");
        }
    }
}

impl Display for Typ {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int => write!(f, "Int"),
            Self::Float => write!(f, "Float"),
            Self::Bool => write!(f, "Bool"),
            Self::Fn(func) => write!(f, "{func}"),
        }
    }
}

impl Display for FnTyp {
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
