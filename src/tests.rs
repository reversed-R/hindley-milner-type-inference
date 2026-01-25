use log::{debug, info};

use crate::{
    ast::{Ast, CallExpr, Expr, LambdaExpr, Literal, Stmt, VarDecl, VarName},
    infer::{FnTyp, Typ, TypEnv, init::ScopeId},
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

    info!("target syntax tree:");
    ast.print();
    debug!("----");

    let env = TypEnv::new(ast).unwrap();

    let res = env.infer().unwrap();

    debug!("----");
    info!("type inference succeeded!");
    info!("results:");
    res.print();

    assert_eq!(
        res.variables
            .get(&(VarName("f".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Fn(FnTyp {
            args: vec![Typ::Int],
            ret: Box::new(Typ::Int)
        }))
    );
    assert_eq!(
        res.variables
            .get(&(VarName("x".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Int)
    );
    assert_eq!(
        res.variables
            .get(&(VarName("y".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Int)
    );
    assert_eq!(
        res.variables
            .get(&(VarName("x".to_string()), ScopeId::new(1, 0))),
        Some(&Typ::Int)
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

    let env = TypEnv::new(ast).unwrap();
    let res = env.infer().unwrap();

    assert_eq!(
        res.variables
            .get(&(VarName("f".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Fn(FnTyp {
            args: vec![Typ::Float],
            ret: Box::new(Typ::Float)
        }))
    );
    assert_eq!(
        res.variables
            .get(&(VarName("x".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Float)
    );
    assert_eq!(
        res.variables
            .get(&(VarName("y".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Float)
    );
    assert_eq!(
        res.variables
            .get(&(VarName("g".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Fn(FnTyp {
            args: vec![Typ::Float, Typ::Float],
            ret: Box::new(Typ::Float)
        }))
    );
    assert_eq!(
        res.variables
            .get(&(VarName("z".to_string()), ScopeId::new(0, 0))),
        Some(&Typ::Float)
    );
}
