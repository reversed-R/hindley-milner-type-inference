use log::debug;

use crate::{
    ast::{Ast, CallExpr, Expr, LambdaExpr, Literal, Stmt, VarDecl, VarName},
    infer::{FnTy, Ty, infer_ast},
};

#[test]
fn test1() {
    env_logger::init();
    // ```
    // let f = (x) -> x;
    // let x = 1;
    // let y = f(x);
    // ```
    let ast = Ast {
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
                    f: VarName("f".to_string()),
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
    // ```
    // let f = (x) -> x;
    // let x = 1.0;
    // let y = f(x);
    // let g = (x, y) -> x;
    // let z = g(x, y);
    // ```
    let ast = Ast {
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
                    f: VarName("f".to_string()),
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
                    f: VarName("g".to_string()),
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
