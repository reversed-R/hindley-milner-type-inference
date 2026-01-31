use std::collections::{HashMap, hash_map::Entry};

use crate::{
    ast::{
        AbsId, Ast,
        types::{FnType, StructType, Type},
    },
    infer::{
        TyError, TyResult,
        types::{
            FnId, FnTy, SymId, Ty,
            struct_type::{StructId, StructTy},
        },
    },
};

pub(super) struct TyBuilder<'ast> {
    next_sid: usize,
    next_fid: usize,
    pub(super) ast: &'ast Ast,
    pub(super) syms: HashMap<AbsId, SymId>,
    pub(super) structs: HashMap<StructId, StructTy>,
    pub(super) fns: HashMap<FnId, FnTy>,
}

impl<'ast> TyBuilder<'ast> {
    pub(super) fn new(ast: &'ast Ast) -> Self {
        Self {
            next_sid: 0,
            next_fid: 0,
            ast,
            syms: HashMap::new(),
            structs: HashMap::new(),
            fns: HashMap::new(),
        }
    }

    fn new_struct_id(&mut self) -> StructId {
        let id = self.next_sid;
        self.next_sid += 1;

        StructId::new(id)
    }

    fn new_fn_id(&mut self) -> FnId {
        let id = self.next_sid;
        self.next_sid += 1;

        FnId::new(id)
    }

    fn build_ty(&mut self, typ: Type) -> TyResult<Ty> {
        match typ {
            Type::Int => Ok(Ty::Int),
            Type::Float => Ok(Ty::Float),
            Type::Bool => Ok(Ty::Bool),
            Type::Fn(f) => Ok(Ty::Fn(self.build_fn_ty(f)?)),
            Type::Defined(id) => {
                let sym = self
                    .syms
                    .get(&id)
                    .ok_or(TyError::SymbolNotFound(id.clone()))?;

                match sym {
                    SymId::Fn(_) => Err(TyError::SymbolNotAType(id)),
                    SymId::Struct(sid) => Ok(Ty::Struct(*sid)),
                }
            }
        }
    }

    fn build_fn_ty(&mut self, typ: FnType) -> TyResult<FnTy> {
        Ok(FnTy {
            args: typ
                .args
                .into_iter()
                .map(|a| self.build_ty(a))
                .collect::<TyResult<_>>()?,
            ret: Box::new(self.build_ty(*typ.ret)?),
        })
    }

    fn build_struct_ty(&mut self, id: AbsId, typ: StructType) -> TyResult<StructTy> {
        let mut members = HashMap::new();
        for (m, ty) in typ.members {
            match members.entry(m.clone().into()) {
                Entry::Vacant(e) => {
                    e.insert(self.build_ty(ty)?);
                }
                Entry::Occupied(_) => return Err(TyError::StructMemberConfliced(id, m)),
            }
        }

        Ok(StructTy {
            members,
            vars: vec![],
        })
    }

    pub(crate) fn build_and_store_fn_ty(&mut self, id: AbsId, ftyp: FnType) -> TyResult<()> {
        let fty = self.build_fn_ty(ftyp)?;
        let fid = self.new_fn_id();

        self.syms.insert(id, SymId::Fn(fid));
        self.fns.insert(fid, fty);

        Ok(())
    }

    pub(crate) fn build_and_store_struct_ty(
        &mut self,
        id: AbsId,
        styp: StructType,
    ) -> TyResult<()> {
        let sty = self.build_struct_ty(id.clone(), styp)?;
        let sid = self.new_struct_id();

        self.syms.insert(id, SymId::Struct(sid));
        self.structs.insert(sid, sty);

        Ok(())
    }
}
