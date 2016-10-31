#![allow(dead_code)]

use std::rc::Rc;
use std::cmp::PartialEq;

/// The color of the node in our red-black Tree.
#[derive(Debug, Clone)]
pub enum Color {
    Black,
    Red,
}

#[derive(Debug, PartialEq, Clone)]
pub struct RbTree<T: PartialEq + PartialOrd> {
    len: usize,
    tree: Rc<Tree<T>>,
}

type Node<T> = Rc<Tree<T>>;

/// The tree structure for our red-black tree.
#[derive(Debug, Clone)]
pub enum Tree<T: PartialEq + PartialOrd> {
    /// An empty leaf node
    E,
    /// A node with a value that points to a left and right node in our `Tree`
    T(Color, Node<T>, Rc<T>, Node<T>),
}

impl<T: PartialEq + PartialOrd> RbTree<T> {
    /// Creates a new, empty, red-black tree.
    pub fn new() -> RbTree<T> {
        RbTree {
            tree: Rc::new(Tree::E),
            len: 0
        }
    }

    /// Inserts an item into a new copy of the existing `Tree`.
    ///
    /// # Examples
    /// ```
    /// use coll::persistent::RbTree;
    /// let tree_one = RbTree::new();
    /// let tree_two = tree_one.insert(1);
    /// let tree_three = tree_two.insert(2);
    /// assert!(tree_one != tree_two);
    /// assert!(tree_two != tree_three);
    /// assert!(tree_three != tree_one);
    /// ```
    pub fn insert(&self, item: T) -> RbTree<T> {
        let tree = self.tree.insert(item);
        RbTree { tree: Rc::new(tree), len: self.len + 1 }
    }

    /// Gets the length of the current tree.
    ///
    /// # Examples
    /// ```
    /// use coll::persistent::RbTree;
    /// let tree = RbTree::new().insert(4).insert(2).insert(3).insert(1);
    /// assert_eq!(tree.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Checks the tree for the presence of a given `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use coll::persistent::RbTree;
    /// let tree = RbTree::new().insert(1).insert(2).insert(3);
    /// assert!(tree.contains(1));
    /// assert!(tree.contains(2));
    /// assert!(tree.contains(3));
    /// assert_eq!(tree.contains(4), false);
    /// ```
    pub fn contains(&self, item: T) -> bool where T: PartialEq + PartialOrd {
        self.tree.contains(item)
    }
    
    /// Returns `true` if the collection is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use coll::persistent::RbTree;
    /// let tree: RbTree<i32> = RbTree::new();
    /// assert!(tree.is_empty());
    ///
    /// let tree = tree.insert(1);
    /// assert!(tree.is_empty() == false);
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T: PartialEq + PartialOrd> Tree<T> {
    fn new() -> Self {
        Tree::E
    }

    fn new_with_value(value: T) -> Self {
        Tree::T(Color::Red,
                  Rc::new(Tree::E),
                  Rc::new(value),
                  Rc::new(Tree::E))
    }

    fn balance(self) -> Self {
        if let Tree::T(Color::Black, ref l, ref x, ref r) = self {

            if let &Tree::T(Color::Red, ref l2, ref x2, ref r2) = l.as_ref() {

                // Black (Red (Red (l3, x3, r3), x2, r2), x, r)
                if let &Tree::T(Color::Red, ref l3, ref x3, ref r3) = l2.as_ref() {
                    let left = Rc::new(Tree::T(Color::Black, l3.clone(), x3.clone(), r3.clone()));
                    let right = Rc::new(Tree::T(Color::Black, r2.clone(), x.clone(), r.clone()));
                    return Tree::T(Color::Red, left, x2.clone(), right);
                }

                // Black (Red (l2, x2, Red (l3, x3, r3)), x, r)
                if let &Tree::T(Color::Red, ref l3, ref x3, ref r3) = r2.as_ref() {
                    let left = Rc::new(Tree::T(Color::Black, l2.clone(), x2.clone(), l3.clone()));
                    let right = Rc::new(Tree::T(Color::Black, r3.clone(), x.clone(), r.clone()));
                    return Tree::T(Color::Red, left, x3.clone(), right);
                }

            }

            if let &Tree::T(Color::Red, ref l2, ref x2, ref r2) = r.as_ref() {

                // Black (l, x, (Red (Red (l3, x3, r3), x2, r2)))
                if let &Tree::T(Color::Red, ref l3, ref x3, ref r3) = l2.as_ref() {
                    let left = Rc::new(Tree::T(Color::Black, l.clone(), x.clone(), l3.clone()));
                    let right = Rc::new(Tree::T(Color::Black, r3.clone(), x2.clone(), r2.clone()));
                    return Tree::T(Color::Red, left, x3.clone(), right);
                }

                // Black (l, x, (Red (l2, x2, Red (l3, x3, r3))))
                if let &Tree::T(Color::Red, ref l3, ref x3, ref r3) = r2.as_ref() {
                    let left = Rc::new(Tree::T(Color::Black, l.clone(), x.clone(), l2.clone()));
                    let right = Rc::new(Tree::T(Color::Black, l3.clone(), x3.clone(), r3.clone()));
                    return Tree::T(Color::Red, left, x2.clone(), right);
                }
            }
        }

        return self;
    }

    fn contains(&self, x: T) -> bool where T: PartialEq + PartialOrd {
        match self {
            &Tree::T(_, ref left, ref y, ref right) => {
                if x < **y {
                    left.contains(x)
                } else if x > **y {
                    right.contains(x)
                } else {
                    true
                }
            }
            &Tree::E => false,
        }
    }

    pub fn insert(&self, x: T) -> Self where T: PartialOrd {
        fn ins<T: PartialOrd>(t: &Tree<T>, x: T) -> Tree<T> {
            let empty = Rc::new(Tree::E);

            match t {
                &Tree::E => Tree::T(Color::Red, empty.clone(), Rc::new(x), empty.clone()),

                &Tree::T(ref color, ref l, ref y, ref r) if x < **y => {
                    let left = Rc::new(ins(l, x));
                    let result = Tree::T(color.clone(), left, y.clone(), r.clone());
                    result.balance()
                }

                &Tree::T(ref color, ref l, ref y, ref r) if x > **y => {
                    let right = Rc::new(ins(r, x));
                    let result = Tree::T(color.clone(), l.clone(), y.clone(), right);
                    result.balance()
                }

                &Tree::T(ref color, ref l, ref _y, ref r) => {
                    Tree::T(color.clone(), l.clone(), Rc::new(x), r.clone())
                }
            }
        }

        if let Tree::T(_, left, y, right) = ins(self, x) {
            Tree::T(Color::Black, left, y, right)
        } else {
            unreachable!()
        }
    }
}

impl PartialEq for Color {
    fn eq(&self, other: &Color) -> bool {
        match (self, other) {
            (&Color::Black, &Color::Black) |
            (&Color::Red, &Color::Red) => true,

            (&Color::Black, &Color::Red) |
            (&Color::Red, &Color::Black) => false,
        }
    }
}

impl<T> PartialEq<Tree<T>> for Tree<T>
    where T: PartialEq + PartialOrd
{
    fn eq(&self, other: &Tree<T>) -> bool {
        match (self, other) {
            (&Tree::E, &Tree::E) => true,
            (&Tree::E, _) | (_, &Tree::E) => false,

            (&Tree::T(ref c1, ref l1, ref e1, ref r1),
             &Tree::T(ref c2, ref l2, ref e2, ref r2)) => {
                c1 == c2 && l1 == l2 && e1 == e2 && r1 == r2
            }
        }
    }
}

#[test]
fn two_empty_trees_are_equal() {
    let left: &Tree<i32> = &Tree::new();
    let right: &Tree<i32> = &Tree::new();
    assert_eq!(left, right);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_1() {
    let empty = Rc::new(Tree::E);

    let y1 = Rc::new(Tree::new_with_value('y'));
    let x1 = Rc::new(Tree::T(Color::Red, empty.clone(), Rc::new('x'), y1));
    let z1 = Tree::T(Color::Black, x1, Rc::new('z'), empty.clone());

    let x2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = Tree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = z1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_2() {
    let empty = Rc::new(Tree::E);

    let x1 = Rc::new(Tree::new_with_value('x'));
    let y1 = Rc::new(Tree::T(Color::Red, x1, Rc::new('y'), empty.clone()));
    let z1 = Tree::T(Color::Black, y1, Rc::new('z'), empty.clone());

    let x2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = Tree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = z1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_gives_the_correct_tree_3() {
    let empty = Rc::new(Tree::E);

    let z1 = Rc::new(Tree::new_with_value('z'));
    let y1 = Rc::new(Tree::T(Color::Red, empty.clone(), Rc::new('y'), z1));
    let x1 = Tree::T(Color::Black, empty.clone(), Rc::new('x'), y1);

    let x2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = Tree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = x1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_4() {
    let empty = Rc::new(Tree::E);

    let y1 = Rc::new(Tree::new_with_value('y'));
    let z1 = Rc::new(Tree::T(Color::Red, y1, Rc::new('z'), empty.clone()));
    let x1 = Tree::T(Color::Black, empty.clone(), Rc::new('x'), z1);

    let x2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = Tree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = x1.balance();
    assert_eq!(result, expected);
}

#[test]
fn insert_three_items_gives_the_expected_tree() {
    let empty = Rc::new(Tree::E);

    let tree = Tree::new().insert('x').insert('y').insert('z');

    let x = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = Tree::T(Color::Black, x, Rc::new('y'), z);

    assert_eq!(tree, expected);
}


#[test]
fn insert_two_items_gives_the_expected_tree() {
    let empty = Rc::new(Tree::E);

    let tree = Tree::new().insert('x').insert('y');

    let y = Rc::new(Tree::T(Color::Red, empty.clone(), Rc::new('y'), empty.clone()));
    let expected = Tree::T(Color::Black, empty.clone(), Rc::new('x'), y);

    assert_eq!(tree, expected);
}

#[test]
fn insert_a_single_item_gives_the_expected_tree() {
    let tree = Tree::new().insert('x');

    let empty = Rc::new(Tree::E);
    let expected = Tree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone());

    assert_eq!(tree, expected);
}

#[test]
fn insert_with_7_items_builds_the_correct_tree() {
    let empty = Rc::new(Tree::E);

    let tree = Tree::new().insert(1).insert(2).insert(3)
                            .insert(4).insert(5).insert(6)
                            .insert(7);

    let one = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new(1), empty.clone()));
    let three = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new(3), empty.clone()));
    let two = Rc::new(Tree::T(Color::Black, one, Rc::new(2), three));
    let five = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new(5), empty.clone()));
    let seven = Rc::new(Tree::T(Color::Black, empty.clone(), Rc::new(7), empty.clone()));
    let six = Rc::new(Tree::T(Color::Black, five, Rc::new(6), seven));
    let expected = Tree::T(Color::Black, two, Rc::new(4), six);

    assert_eq!(tree, expected);
}

#[test]
fn insert_doesnt_allow_duplicates() {
    let tree_one = Tree::new().insert(1).insert(1).insert(1).insert(1).insert(1);
    let tree_two = Tree::new().insert(1);

    assert_eq!(tree_one, tree_two);
}

#[test]
fn contains_finds_all_elements() {
    let tree = Tree::new().insert(1).insert(2).insert(3).insert(4).insert(5).insert(6).insert(7);

    assert!(tree.contains(1));
    assert!(tree.contains(2));
    assert!(tree.contains(3));
    assert!(tree.contains(4));
    assert!(tree.contains(5));
    assert!(tree.contains(6));
    assert!(tree.contains(7));
}