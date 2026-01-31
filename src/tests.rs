use std::sync::Once;

use log::debug;

use crate::{
    ast::{
        AbsId, Ast, CallExpr, Callee, Expr, LambdaExpr, Literal, MemberAccessExpr, MemberName,
        Stmt, VarDecl, VarName,
        types::{FnType, StructType, Type},
    },
    infer::{
        infer_ast,
        types::{FnTy, Ty},
    },
};

static INIT: Once = Once::new();

fn init_logger() {
    INIT.call_once(|| {
        env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("debug"))
            .is_test(true)
            .init();
    });
}

#[test]
fn test1() {
    init_logger();
    // ```
    // let f = (x) -> x;
    // let x = 1;
    // let y = f(x);
    // ```
    let ast = Ast {
        structs: vec![],
        fns: vec![],
        stmts: vec![
            Stmt::VarDecl(VarDecl {
                name: VarName("f".to_string()),
                val: Expr::Lambda(LambdaExpr {
                    args: vec![VarName("x".to_string())],
                    ret: Box::new(Expr::Variable(VarName("x".to_string()))),
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("x".to_string()),
                val: Expr::Literal(Literal::Integer(1)),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("y".to_string()),
                val: Expr::Call(CallExpr {
                    f: Callee::Var(VarName("f".to_string())),
                    args: vec![Expr::Variable(VarName("x".to_string()))],
                }),
            }),
        ],
    };

    debug!("\n{ast}");

    let res = infer_ast(&ast).unwrap();

    debug!("\n{res}");

    assert_eq!(res.tys.get(&VarName("x".to_string())), Some(&Ty::Int));
    assert_eq!(res.tys.get(&VarName("y".to_string())), Some(&Ty::Int));
    assert_eq!(
        Ok(()),
        res.can_apply(
            &VarName("f".to_string()),
            FnTy {
                args: vec![Ty::Int],
                ret: Box::new(Ty::Int)
            }
        )
    );
}

#[test]
fn test2() {
    init_logger();
    // ```
    // let f = (x) -> x;
    // let x = 1.0;
    // let y = f(x);
    // let g = (x, y) -> x;
    // let z = g(x, y);
    // ```
    let ast = Ast {
        structs: vec![],
        fns: vec![],
        stmts: vec![
            Stmt::VarDecl(VarDecl {
                name: VarName("f".to_string()),
                val: Expr::Lambda(LambdaExpr {
                    args: vec![VarName("x".to_string())],
                    ret: Box::new(Expr::Variable(VarName("x".to_string()))),
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("x".to_string()),
                val: Expr::Literal(Literal::Float(1.0)),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("y".to_string()),
                val: Expr::Call(CallExpr {
                    f: Callee::Var(VarName("f".to_string())),
                    args: vec![Expr::Variable(VarName("x".to_string()))],
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("g".to_string()),
                val: Expr::Lambda(LambdaExpr {
                    args: vec![VarName("x".to_string()), VarName("y".to_string())],
                    ret: Box::new(Expr::Variable(VarName("x".to_string()))),
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("z".to_string()),
                val: Expr::Call(CallExpr {
                    f: Callee::Var(VarName("g".to_string())),
                    args: vec![
                        Expr::Variable(VarName("x".to_string())),
                        Expr::Variable(VarName("y".to_string())),
                    ],
                }),
            }),
        ],
    };

    debug!("\n{ast}");

    let res = infer_ast(&ast).unwrap();

    debug!("\n{res}");

    assert_eq!(res.tys.get(&VarName("x".to_string())), Some(&Ty::Float));
    assert_eq!(res.tys.get(&VarName("y".to_string())), Some(&Ty::Float));
    assert_eq!(res.tys.get(&VarName("z".to_string())), Some(&Ty::Float));
    assert_eq!(
        Ok(()),
        res.can_apply(
            &VarName("f".to_string()),
            FnTy {
                args: vec![Ty::Float],
                ret: Box::new(Ty::Float)
            }
        )
    );
    assert_eq!(
        Ok(()),
        res.can_apply(
            &VarName("g".to_string()),
            FnTy {
                args: vec![Ty::Float, Ty::Float],
                ret: Box::new(Ty::Float)
            }
        )
    );
}

#[test]
fn test3() {
    init_logger();
    // ```
    // struct S {
    //   m: Int,
    //   n: Bool,
    // }
    //
    // fn s_new() -> S {
    //   S {
    //     m: 0,
    //     n: false,
    //   }
    // }
    //
    // let f = (x) -> x;
    // let x = s_new().m;
    // let y = f(x);
    // ```
    let ast = Ast {
        structs: vec![(
            AbsId::new(vec![], "S".to_string()),
            StructType {
                members: vec![
                    (MemberName("m".to_string()), Type::Int),
                    (MemberName("n".to_string()), Type::Bool),
                ],
            },
        )],
        fns: vec![(
            AbsId::new(vec![], "s_new".to_string()),
            FnType {
                args: vec![],
                ret: Box::new(Type::Defined(AbsId::new(vec![], "S".to_string()))),
            },
        )],
        stmts: vec![
            Stmt::VarDecl(VarDecl {
                name: VarName("f".to_string()),
                val: Expr::Lambda(LambdaExpr {
                    args: vec![VarName("x".to_string())],
                    ret: Box::new(Expr::Variable(VarName("x".to_string()))),
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("x".to_string()),
                val: Expr::MemberAccess(MemberAccessExpr {
                    left: Box::new(Expr::Call(CallExpr {
                        f: Callee::Fn(AbsId::new(vec![], "s_new".to_string())),
                        args: vec![],
                    })),
                    member: MemberName("n".to_string()),
                }),
            }),
            Stmt::VarDecl(VarDecl {
                name: VarName("y".to_string()),
                val: Expr::Call(CallExpr {
                    f: Callee::Var(VarName("f".to_string())),
                    args: vec![Expr::Variable(VarName("x".to_string()))],
                }),
            }),
        ],
    };

    debug!("\n{ast}");

    let res = infer_ast(&ast).unwrap();

    debug!("\n{res}");

    assert_eq!(res.tys.get(&VarName("x".to_string())), Some(&Ty::Bool));
    assert_eq!(res.tys.get(&VarName("y".to_string())), Some(&Ty::Bool));
    assert_eq!(
        Ok(()),
        res.can_apply(
            &VarName("f".to_string()),
            FnTy {
                args: vec![Ty::Bool],
                ret: Box::new(Ty::Bool)
            }
        )
    );
}
