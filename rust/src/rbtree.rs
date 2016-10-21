use std::cmp;
use std::mem;

struct RBTree<K, V> {
    root: Option<Node<K, V>>,
    length: u32
}

struct Node<K, V> {
    color: Color,
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>
}

enum InsertionResult {
    SuccessInsert,
    SuccessUpdate,
    RepaintedRed,
    RotateMe(Dir),
    RedInvariantBroken
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum Color { Red, Black }

#[derive(PartialEq, Eq, Clone, Copy)]
enum Dir { Left, Right }

impl <K: Ord, V> RBTree<K, V> {
    fn new() -> RBTree<K, V> {
        RBTree{root: None, length: 0}
    }

    fn find(&self, key: K) -> Option<&V> {
        match self.root {
            None => None,
            Some(ref root) => root.find(key)
        }
    }

    fn insert(&mut self, key: K, value: V) {
        let (rotation_result, length_delta) = match self.root {
            Some(ref mut root) => {
                match root.insert(key, value) {
                    InsertionResult::RotateMe(dir) => (Some(dir), 1),
                    InsertionResult::SuccessUpdate => (None, 0),
                    _ => (None, 1)
                }
            },
            None => {
                let node = Node::new(key, value, Color::Black);
                self.root = Some(node);
                (None, 1)
            }
        };

        rotation_result.map(|dir| self.rotate_root(dir));
        self.root.as_mut().map(|root| root.color = Color::Black);
        self.length += length_delta;
    }

    fn rotate_root(&mut self, dir: Dir) {
        let mut tmp_root = None;
        mem::swap(&mut tmp_root, &mut self.root);
        match tmp_root {
            Some(node) => {
                let mut rotated = node.rotate(dir);
                mem::swap(&mut self.root, &mut Some(rotated));
            },
            None => {}
        }
    }

    fn len(&self) -> u32 {
        self.length
    }
}

impl <K: Ord, V> Node<K, V> {
    fn new(key: K, value: V, color: Color) -> Node<K,V> {
        Node{key: key, value: value, left: None, right: None, color: color}
    }

    fn find(&self, key: K) -> Option<&V> {
        if key == self.key { Some(&self.value) }
        else {
            let child = if key < self.key { &self.left } else { &self.right };
            match child {
                &None => None,
                &Some(ref c) => c.find(key)
            }
        }
    }

    fn insert(&mut self, key: K, value: V) -> InsertionResult {
        if key == self.key {
            self.value = value;
            return InsertionResult::SuccessUpdate
        }

        let dir = if key < self.key { Dir::Left } else { Dir::Right };

        let result = {
            let child = if dir == Dir::Left { &mut self.left } else { &mut self.right };
            match child {
                &mut None => {
                    let mut node = Node::new(key, value, Color::Red);
                    mem::swap(child, &mut Some(Box::new(node)));

                    return if self.color == Color::Black { InsertionResult::SuccessInsert }
                    else { InsertionResult::RedInvariantBroken }
                },

                &mut Some(ref mut child_node) => child_node.insert(key, value)
            }
        };

        self.handle_insertion_result(dir, result)
    }

    fn handle_insertion_result(&mut self, dir_inserted: Dir, result: InsertionResult) -> InsertionResult {
        match result {
            InsertionResult::RedInvariantBroken => {
                if self.both_children_colored(Color::Red) {
                    self.handle_both_children_red_case()
                } else {
                    self.normalize_child(dir_inserted);
                    self.color = Color::Red;
                    self.paint_child_color(dir_inserted, Color::Black);
                    InsertionResult::RotateMe(dir_inserted)
                }
            },
            InsertionResult::RotateMe(dir_to_rotate) =>
                self.handle_rotation_case(dir_inserted, dir_to_rotate),
            InsertionResult::RepaintedRed => {
                if self.color == Color::Black { InsertionResult::SuccessInsert }
                else { InsertionResult::RedInvariantBroken }
            },
            result => result
        }
    }

    fn handle_both_children_red_case(&mut self) -> InsertionResult {
        self.paint_child_color(Dir::Left, Color::Black);
        self.paint_child_color(Dir::Right, Color::Black);
        self.color = Color::Red;
        InsertionResult::RepaintedRed
    }

    fn handle_rotation_case(&mut self, dir_inserted: Dir, dir_to_rotate: Dir) -> InsertionResult {
        let rotated = {
            let child_ref =
                if dir_inserted == Dir::Left { &mut self.left } else { &mut self.right };
            let child = *mem::replace(child_ref, None).unwrap();
            child.rotate(dir_to_rotate)
        };
        let result = Some(Box::new(rotated));

        if dir_inserted == Dir::Left { self.left = result }
        else { self.right = result };
        InsertionResult::SuccessInsert
    }

    fn normalize_child(&mut self, dir: Dir) {
        let mut container = None;
        let current_child = if dir == Dir::Left { &mut self.left } else { &mut self.right };
        mem::swap(&mut container, current_child);

        let mut new_child = {
            let node = *container.unwrap();
            let other_dir = dir.other();
            if node.child_has_color(other_dir, Color::Red) {
                node.rotate(other_dir)
            }
            else { node }
        };
        mem::swap(current_child, &mut Some(Box::new(new_child)))
    }

    // will blow up if the relevant child is None
    fn rotate(mut self, dir: Dir) -> Node<K, V> {
        let mut new_parent_option = None;
        self.swap_child(&mut new_parent_option, dir);

        let mut new_parent = *new_parent_option.unwrap();
        if dir == Dir::Left {
            mem::swap(&mut new_parent.right, &mut self.left);
            new_parent.right = Some(Box::new(self));
        } else {
            mem::swap(&mut new_parent.left, &mut self.right);
            new_parent.left = Some(Box::new(self));
        }

        new_parent
    }

    fn swap_child(&mut self, new_child: &mut Option<Box<Node<K,V>>>, dir: Dir) {
        let child = if dir == Dir::Left { &mut self.left } else { &mut self.right };
        mem::swap(new_child, child);
    }

    fn child_has_color(&self, dir: Dir, color: Color) -> bool {
        let child = if dir == Dir::Left { &self.left } else { &self.right };
        match child {
            &None => color == Color::Black,
            &Some(ref node) => node.color == color
        }
    }

    fn paint_child_color(&mut self, dir: Dir, color: Color) {
        let child = if dir == Dir::Left { &mut self.left } else { &mut self.right };
        match child {
            &mut None => {},
            &mut Some(ref mut node) => node.color = color
        }
    }

    fn both_children_colored(&self, color: Color) -> bool {
        self.child_has_color(Dir::Left, color) &&
            self.child_has_color(Dir::Right, color)
    }
}

impl Dir {
    fn other(self) -> Dir {
        if self == Dir::Left { Dir::Right } else { Dir::Left }
    }
}


#[cfg(test)]
mod tests {
    use super::RBTree;
    use super::Node;
    use super::Color;

    #[test]
    fn rbtree_test() {
        let mut tree: RBTree<u32, u32> = RBTree::new();

        let num_nodes = 1000;

        for i in 0..num_nodes {
            tree.insert(i, i+1);
        }

        for i in 0..num_nodes {
            assert_eq!(i+1, *tree.find(i).unwrap());
        }

        assert_eq!(num_nodes, tree.len());
        tree.insert(0, 5);
        assert_eq!(num_nodes, tree.len());

        let root = &tree.root.unwrap();
        check_invariant(root);
    }


    fn check_invariant(node: &Node<u32, u32>) -> u32 {
        let left_count = match node.left {
            None => 0,
            Some(ref child) => check_invariant(child)
        };
        let right_count = match node.right {
            None => 0,
            Some(ref child) => check_invariant(child)
        };

        if left_count != right_count { panic!("invariant not satisfied {} {}", left_count, right_count) }

        let my_count = if node.color == Color::Black { 1 } else { 0 };
        my_count + left_count
    }

}
