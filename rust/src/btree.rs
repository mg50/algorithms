use std::vec;
use std::mem;
use std::fmt::Display;
use std::fmt;

pub struct BTree<K,V> {
    order: usize,
    root: BTreeNode<K,V>
}

struct BTreeNode<K, V> {
    order: usize,
    entries: Vec<Entry<K, V>>,
    children: Vec<BTreeNode<K, V>>
}

enum InsertionResult<K,V> {
    Success,
    Split(BTreeNode<K,V>, Entry<K,V>, BTreeNode<K,V>)
}

struct Entry<K, V> {
    key: K,
    value: V
}

impl <K:Display, V: Display> Display for Entry<K,V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "<{},{}>", self.key, self.value)
    }
}

impl <K: Display, V: Display> Display for BTreeNode<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {

        write!(f, "{}", self.stringify(1))
    }
}

impl <K: Display, V: Display> BTreeNode<K, V> {
    fn stringify(&self, num_spaces: i32) -> String {
        let entries: Vec<_> = self.entries
            .iter()
            .map(|ref entry| format!("({},{})", entry.key, entry.value))
            .collect();


        let spaces: Vec<_> = (1..num_spaces)
            .map(|x| format!("  "))
            .collect();

        let children: Vec<_> = self.children
            .iter()
            .map(|child| child.stringify(num_spaces + 1))
            .collect();

        format!("{}[{}]\n{}", spaces.join(""), entries.join(","), children.join(""))
    }
}

impl <K: Display, V: Display> Display for BTree<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.root)
    }
}


impl <K: Ord, V: Display> BTree<K,V> {
    pub fn new(order: usize) -> BTree<K,V> {
        BTree{order: order, root: BTreeNode::new(order)}
    }

    pub fn search(&self, key: K) -> Option<&V> {
        self.root.search(key)
    }

    pub fn insert(&mut self, key: K, val: V) {
        match self.root.insert(key, val) {
            InsertionResult::Success => {}
            InsertionResult::Split(left,mid,right) => {
                self.root.entries = vec![mid];
                self.root.children = vec![left,right];
            }
        }
    }
}

impl <K: Ord, V: Display> BTreeNode<K, V> {
    fn new(order: usize) -> BTreeNode<K, V> {
        let entries = Vec::with_capacity(order - 1);
        let children = Vec::with_capacity(order);
        BTreeNode{order: order, entries: entries, children: children}
    }

    fn search(&self, key: K) -> Option<&V> {
        match self.insert_index(&key) {
            (idx, true) => Some(&self.entries[idx].value),
            (idx, false) => {
                if self.is_leaf() { None }
                else { self.children[idx].search(key) }
            }
        }
    }

    fn insert(&mut self, key: K, val: V) -> InsertionResult<K, V> {
        match self.insert_index(&key) {
            (idx, true) => {
                self.entries[idx].value = val;
                InsertionResult::Success
            },
            (idx, false) => {
                // full leaf
                if self.is_full() && self.is_leaf() {
                    let entry = Entry{key: key, value: val};
                    self.entries.insert(idx, entry);
                    let (left, mid, right) = self.split_overfull_node();
                    InsertionResult::Split(left, mid, right)
                }
                // leaf with space left
                else if self.is_leaf() {
                    let entry = Entry{key: key, value: val};
                    self.entries.insert(idx, entry);
                    InsertionResult::Success
                }
                // non-leaf
                else {
                    match self.children[idx].insert(key, val) {
                        InsertionResult::Success => InsertionResult::Success,
                        InsertionResult::Split(left, mid, right) => {
                            let full = self.is_full();

                            self.entries.insert(idx, mid);
                            self.children[idx] = left;
                            self.children.insert(idx+1, right);

                            if full {
                                let (left, mid, right) = self.split_overfull_node();
                                InsertionResult::Split(left, mid, right)
                            } else {
                                InsertionResult::Success
                            }
                        }
                    }
                }
            }
        }
    }

    fn insert_index(&self, key: &K) -> (usize, bool) {
        let mut idx = 0;
        for entry in self.entries.iter() {
            if *key == entry.key { return (idx, true) };
            if *key < entry.key { break };
            idx += 1;
        }
        (idx, false)
    }

    fn split_overfull_node(&mut self) -> (BTreeNode<K,V>, Entry<K,V>, BTreeNode<K,V>) {
        let mut entries = Vec::new();
        mem::swap(&mut entries, &mut self.entries);

        let mut children = Vec::new();
        mem::swap(&mut children, &mut self.children);

        let splitIdx = self.order / 2;

        let mut left_entries = Vec::with_capacity(self.order - 1);

        // this is maybe O(n^2)?
        for idx in (0..splitIdx).rev() {
            left_entries.push(entries.remove(0));
        }

        let middle_entry = entries.remove(0);

        let mut left_children;

        if children.len() == 0 {
            left_children = Vec::with_capacity(0);
        } else {
            left_children = Vec::with_capacity(self.order);
            for idx in (0..(splitIdx+1)).rev() {
                left_children.push(children.remove(0));
            }
        }

        let left_node = BTreeNode{order: self.order,
                                  entries: left_entries,
                                  children: left_children};

        let right_node = BTreeNode{order: self.order,
                                   entries: entries,
                                   children: children};

        (left_node, middle_entry, right_node)
    }

    fn is_full(&self) -> bool {
        self.entries.len() >= self.order - 1
    }

    fn is_leaf(&self) -> bool {
        self.children.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use super::BTree;

    #[test]
    fn btree_test() {
        let mut tree: BTree<i32, i32> = BTree::new(3);
        for idx in 1..21 {
            tree.insert(idx, idx)
        }
        println!("{}", tree);
    }
}
