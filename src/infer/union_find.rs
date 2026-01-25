use std::collections::HashMap;

use crate::infer::term::TypVar;

pub(crate) struct UnionFind {
    parent: HashMap<TypVar, TypVar>,
}

impl UnionFind {
    pub fn new() -> Self {
        Self {
            parent: HashMap::new(),
        }
    }

    pub fn find(&mut self, x: TypVar) -> TypVar {
        let p = *self.parent.get(&x).unwrap_or(&x);
        if p == x {
            x
        } else {
            let root = self.find(p);
            self.parent.insert(x, root); // パス圧縮
            root
        }
    }

    pub fn union(&mut self, old: TypVar, new: TypVar) {
        let rold = self.find(old);
        let rnew = self.find(new);

        if rold == rnew {
            return;
        }

        self.parent.insert(rold, rnew);
    }
}
