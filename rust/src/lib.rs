use std::mem;
mod btree;
mod rbtree;

struct Tree<K, V> {
    root: Option<Node<K, V>>
}

struct Node<K, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K,V>>>,
    right: Option<Box<Node<K,V>>>
}

impl <K: Ord, V> Tree<K, V> {
    fn new() -> Self {
        Tree{root: None}
    }

    fn insert(&mut self, key: K, val: V) {
        match self.root {
            None => self.root = Some(Node::new(key, val)),
            Some(ref mut node) => node.insert(key, val)
        }
    }

    fn find(&self, key: K) -> Option<&V> {
        match self.root {
            None => None,
            Some(ref node) => node.find(key)
        }
    }

    fn delete(&mut self, key: K) {
        let mut delete_root = false;

        match self.root {
            None => {}
            Some(ref mut node) => delete_root = node.delete(key)
        }

        if delete_root { self.root = None }
    }

    fn length(&self) -> u32 {
        match self.root {
            None => 0,
            Some(ref node) => node.length()
        }
    }
}

impl <K: Ord, V> Node<K,V> {
    fn new(key: K, val: V) -> Self {
        Node{key: key, value: val, left: None, right: None}
    }

    fn find(&self, key: K) -> Option<&V> {
        if key < self.key {
            match self.left {
                None => None,
                Some(ref left) => left.find(key)
            }
        } else if key == self.key {
            Some(&self.value)
        } else {
            match self.right {
                None => None,
                Some(ref right) => right.find(key)
            }
        }
    }

    fn length(&self) -> u32 {
        let left = match self.left {
            None => 0,
            Some(ref node) => node.length()
        };

        let right = match self.right {
            None => 0,
            Some(ref node) => node.length()
        };

        1 + left + right
    }

    fn insert(&mut self, key: K, val: V) {
        if self.key == key {
            self.value = val;
            return
        }

        let node = if key < self.key { &mut self.left } else { &mut self.right };
        match *node {
            None => *node = Some(Box::new(Node::new(key, val))),
            Some(ref mut child) => child.insert(key, val)
        }
    }

    fn delete(&mut self, key: K) -> bool {
        if key == self.key {
            return self.delete_self();
        }

        let mut delete_child = false;
        let child = if key < self.key { &mut self.left } else { &mut self.right };
        match child {
            &mut None => {},
            &mut Some(ref mut child_node) => delete_child = child_node.delete(key)
        }

        if delete_child { *child = None }

        false
    }

    fn delete_self(&mut self) -> bool {
        let mut delete_left = false;
        let mut has_two_children = false;

        match (&mut self.left, &mut self.right) {
            (&mut None, &mut None) => return true,
            (&mut Some(_), &mut None) => delete_left = true,
            (&mut None, &mut Some(_)) => {},
            (&mut Some(ref mut left), _) => has_two_children = true
        }

        if has_two_children {
            match self.delete_max_left() {
                None => {},
                Some((k, v)) => {
                    self.key = k;
                    self.value = v;
                }
            }
        }
        else { self.replace_with_child(delete_left) }

        false
    }

    fn replace_with_child(&mut self, use_left_child: bool) {
        let mut swap_val = None;
        {
            let child = if use_left_child { &mut self.left } else { &mut self.right };
            mem::swap(&mut swap_val, child);
        }
        match swap_val {
            None => {},
            Some(child_node) => {
                let n = *child_node;
                self.key = n.key;
                self.value = n.value;
                self.left = n.left;
                self.right = n.right
            }
        }
    }

    fn delete_max_left(&mut self) -> Option<(K, V)> {
        match self.left {
            None => None,
            Some(ref mut left) => left.delete_rightest()
        }
    }

    fn delete_rightest(&mut self) -> Option<(K, V)> {
        let result = self.delete_right_unless_grandparent();
        match result {
            None => {
                match self.right {
                    None => None,
                    Some(ref mut right) => right.delete_rightest()
                }
            },
            _ => result
        }
    }

    fn delete_right_unless_grandparent(&mut self) -> Option<(K, V)> {
        match self.right {
            None => return None,
            Some(ref child) => {
                match child.right {
                    Some(ref grandchild) => return None,
                    None => {}
                }
            }
        };

        let mut deleted = None;
        mem::swap(&mut self.right, &mut deleted);
        match deleted {
            None => None,
            Some(node) => {
                let n = *node;
                Some((n.key, n.value))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let mut tree: ::Tree<u32, u32> = ::Tree::new();
        assert_eq!(tree.length(), 0);

        tree.insert(0, 0);
        tree.insert(1, 2);
        tree.insert(3, 4);

        assert_eq!(tree.length(), 3);
        assert_eq!(tree.find(0), Some(&0));
        assert_eq!(tree.find(1), Some(&2));
        assert_eq!(tree.find(3), Some(&4));
        assert_eq!(tree.find(4), None);

        tree.delete(3);
        assert_eq!(tree.length(), 2);
    }
}
