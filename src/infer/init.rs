use std::{
    collections::{HashMap, hash_map::Entry},
    fmt::Display,
};

use crate::{
    ast::{Ast, Expr, Literal, Stmt, VarName},
    infer::{
        TypEnv, TypeError,
        term::{Term, TermApply, TermEq, TermFn, TermLiteral, TypVar},
    },
};

struct TypVarGenerator {
    id: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ScopeId {
    rank: usize,
    idx: usize,
}

#[derive(Debug)]
pub(super) struct VariablePool {
    pub(crate) scopes: HashMap<ScopeId, HashMap<VarName, TypVar>>,
    each_rank_scope_idxs: Vec<usize>,
    current_scope: ScopeId,
}

impl ScopeId {
    pub(crate) fn new(rank: usize, idx: usize) -> Self {
        Self { rank, idx }
    }
}

impl VariablePool {
    fn new() -> Self {
        let mut scopes = HashMap::new();
        let root = ScopeId { rank: 0, idx: 0 };
        scopes.insert(root.clone(), HashMap::<VarName, TypVar>::new());

        Self {
            scopes,
            each_rank_scope_idxs: vec![0],
            current_scope: root,
        }
    }

    // 現在のスコープに変数名vの変数を挿入
    // - 現在のスコープに同じ変数名がなければ型変数を得る
    // - 現在のスコープに同じ変数名があればエラー
    fn insert(&mut self, v: VarName, tv: TypVar) -> Result<(), TypeError> {
        // println!("insert: {v:?}, {tv:?}");
        // println!("current_scope: {:?}", self.current_scope);

        match self
            .scopes
            .get_mut(&self.current_scope)
            .unwrap()
            .entry(v.clone())
        {
            Entry::Vacant(e) => {
                e.insert(tv);

                Ok(())
            }
            Entry::Occupied(_) => Err(TypeError::VariableConflicted(v)),
        }
    }

    fn get(&self, v: &VarName) -> Option<TypVar> {
        // println!("get: {v:?}");

        let mut sid = self.current_scope.clone();

        loop {
            if let Some(tv) = self.scopes.get(&sid).unwrap().get(v) {
                return Some(*tv);
            }

            if let Some(parent) = self.get_parent_scope_id(&sid) {
                sid = parent;
            } else {
                return None;
            }
        }
    }

    fn get_parent_scope_id(&self, sid: &ScopeId) -> Option<ScopeId> {
        if sid.rank == 0 {
            None
        } else {
            Some(ScopeId {
                rank: sid.rank - 1,
                idx: self.each_rank_scope_idxs[sid.rank - 1],
            })
        }
    }

    fn enter_scope(&mut self) {
        // println!("enter scope");
        let next_rank = self.current_scope.rank + 1;
        let next_idx;
        if let Some(e) = self.each_rank_scope_idxs.get_mut(next_rank) {
            *e += 1;
            next_idx = *e;
        } else {
            self.each_rank_scope_idxs.push(0);
            next_idx = 0;
        }

        let next_sid = ScopeId {
            rank: next_rank,
            idx: next_idx,
        };

        self.scopes.insert(next_sid.clone(), HashMap::new());
        // println!("next_sid: {next_sid:?}");
        self.current_scope = next_sid;
    }

    fn exit_scope(&mut self) {
        // println!("exit scope");
        if self.current_scope.rank == 0 {
            panic!("compiler bug: variable stack underflowed");
        } else {
            let parent_rank = self.current_scope.rank - 1;
            let parent_idx = self.each_rank_scope_idxs[parent_rank];

            // println!("sid: {parent_rank}:{parent_idx}");
            self.current_scope = ScopeId {
                rank: parent_rank,
                idx: parent_idx,
            };
        }
    }
}

impl TypVarGenerator {
    fn new() -> Self {
        Self { id: 0 }
    }

    fn generate(&mut self) -> TypVar {
        let id = self.id;
        self.id += 1;

        TypVar(id)
    }
}

impl TypEnv {
    pub fn new(ast: Ast) -> Result<Self, TypeError> {
        let mut typvar = TypVarGenerator::new();
        let mut variables = VariablePool::new();
        let mut constraints = HashMap::new();

        for stmt in &ast.stmts {
            match stmt {
                Stmt::VarDecl(v) => {
                    let src = register_expr_to_env(
                        &v.val,
                        &mut typvar,
                        &mut variables,
                        &mut constraints,
                    )?;

                    // register variable into map
                    let dst = typvar.generate();
                    constraints.insert(dst, Term::Eq(TermEq { t1: dst, t2: src }));

                    // register variable into map
                    variables.insert(v.name.clone(), dst)?;
                }
            }
        }

        Ok(Self {
            constraints,
            substitutions: HashMap::new(),
            variables,
            unifications: HashMap::new(),
        })
    }
}

fn register_expr_to_env(
    expr: &Expr,
    typvar: &mut TypVarGenerator,
    variables: &mut VariablePool,
    constraints: &mut HashMap<TypVar, Term>,
) -> Result<TypVar, TypeError> {
    match expr {
        Expr::Literal(l) => match l {
            Literal::Integer(i) => {
                let tv = typvar.generate();
                constraints.insert(tv, Term::Literal(TermLiteral::Integer(*i)));

                Ok(tv)
            }
            Literal::Float(f) => {
                let tv = typvar.generate();
                constraints.insert(tv, Term::Literal(TermLiteral::Float(*f)));

                Ok(tv)
            }
            Literal::Bool(b) => {
                let tv = typvar.generate();
                constraints.insert(tv, Term::Literal(TermLiteral::Bool(*b)));

                Ok(tv)
            }
        },
        Expr::Variable(v) => {
            // NOTE: 変数の存在チェックが、型変数がすでに定義されているかで行える
            // We can check existence of local variable
            // by checking whether type variable has been already defined or not.
            if let Some(tv) = variables.get(v) {
                Ok(tv)
            } else {
                Err(TypeError::VariableNotFound(v.clone()))
            }
        }
        Expr::Lambda(l) => {
            variables.enter_scope();

            let args = l
                .args
                .iter()
                .map(|a| {
                    let tv = typvar.generate();
                    variables.insert(a.clone(), tv)?;

                    Ok(tv)
                })
                .collect::<Result<_, _>>()?;
            let ret = register_expr_to_env(&l.ret, typvar, variables, constraints)?;

            variables.exit_scope();

            let tv = typvar.generate();
            constraints.insert(tv, Term::Fn(TermFn { args, ret }));

            Ok(tv)
        }
        Expr::Call(c) => {
            let args = c
                .args
                .iter()
                .map(|e| register_expr_to_env(e, typvar, variables, constraints))
                .collect::<Result<_, _>>()?;

            let tv = typvar.generate();
            constraints.insert(
                tv,
                Term::Apply(TermApply {
                    f: variables
                        .get(&c.f)
                        .ok_or(TypeError::VariableNotFound(c.f.clone()))?,
                    args,
                }),
            );

            Ok(tv)
        }
    }
}

impl Display for ScopeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.rank, self.idx)
    }
}
