use std::vec::Vec;
use std::cell::Cell;

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
pub struct Set(usize);

#[derive(Debug, Clone)]
pub struct UnionFind {
    parent: Vec<Cell<Set>>,
    rank: Vec<usize>
}

impl UnionFind {
    pub fn new() -> Self {
        UnionFind {
            parent: Vec::new(),
            rank: Vec::new()
        }
    }

    pub fn with_capacity(num_variables: usize) -> Self {
        UnionFind {
            parent: Vec::with_capacity(num_variables),
            rank: Vec::with_capacity(num_variables)
        }
    }

    pub fn new_var(&mut self) -> Set {
        let v = Set(self.parent.len());
        self.parent.push(Cell::new(v));
        self.rank.push(0);
        v
    }

    pub fn union(&mut self, x: Set, y: Set) {
        let x_root = self.find(x);
        let y_root = self.find(y);

        if x_root == y_root {
            return;
        }

        let (designated_parent, designated_child) = if self.rank[x_root.0] < self.rank[y_root.0] {
            (y_root, x_root)
        } else {
            (x_root, y_root)
        };

        self.parent[designated_child.0].set(designated_parent);
        if self.rank[designated_parent.0] == self.rank[designated_child.0] {
            self.rank[designated_parent.0] += 1;
        }
    }

    pub fn find(&self, x: Set) -> Set {
        let mut cur = x;
        while self.parent[x.0].get() != cur {
            let next = self.parent[cur.0].get();
            self.parent[x.0].set(self.parent[next.0].get());
            cur = next;
        }
        cur
    }
}

