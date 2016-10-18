#![allow(dead_code)]

use std::rc::Rc;
use std::cmp::PartialEq;

/// The color of the node in our red-black RbTree.
#[derive(Debug, Clone)]
pub enum Color {
    Black,
    Red,
}

type Node<T> = Rc<RbTree<T>>;

/// The tree structure for our red-black tree.
#[derive(Debug, Clone)]
pub enum RbTree<T>
    where T: PartialEq + PartialOrd
{
    /// An empty leaf node
    E,
    /// A node with a value that points to a left and right node in our `RbTree`
    T(Color, Node<T>, Rc<T>, Node<T>),
}

impl<T> RbTree<T>
    where T: PartialEq + PartialOrd
{
    /// Constructs an empty `RbTree<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use coll::persistent::RbTree;
    /// let t: RbTree<i32> = RbTree::new();
    /// ```
    pub fn new() -> Self {
        RbTree::E
    }

    fn new_with_value(value: T) -> Self {
        RbTree::T(Color::Red,
                  Rc::new(RbTree::E),
                  Rc::new(value),
                  Rc::new(RbTree::E))
    }

    fn balance(self) -> Self {
        if let RbTree::T(Color::Black, ref l, ref x, ref r) = self {

            if let &RbTree::T(Color::Red, ref l2, ref x2, ref r2) = l.clone().as_ref() {

                // Black (Red (Red, _), _)
                if let &RbTree::T(Color::Red, ref l3, ref x3, ref r3) = l2.clone().as_ref() {
                    let left = Rc::new(RbTree::T(Color::Black, l3.clone(), x3.clone(), r3.clone()));
                    let right = Rc::new(RbTree::T(Color::Black, r2.clone(), x.clone(), r.clone()));
                    return RbTree::T(Color::Red, left, x2.clone(), right);
                }

                // Black (Red (_, Red), _)
                if let &RbTree::T(Color::Red, ref l3, ref x3, ref r3) = r2.clone().as_ref() {
                    let left = Rc::new(RbTree::T(Color::Black, l2.clone(), x2.clone(), l3.clone()));
                    let right = Rc::new(RbTree::T(Color::Black, r3.clone(), x.clone(), r.clone()));
                    return RbTree::T(Color::Red, left, x3.clone(), right);
                }

            }

            if let &RbTree::T(Color::Red, ref l2, ref x2, ref r2) = r.clone().as_ref() {

                // Black (l, x, (Red (Red, _)))
                if let &RbTree::T(Color::Red, ref l3, ref x3, ref r3) = l2.clone().as_ref() {
                    let left = Rc::new(RbTree::T(Color::Black, l.clone(), x.clone(), l3.clone()));
                    let right = Rc::new(RbTree::T(Color::Black, r3.clone(), x2.clone(), r2.clone()));
                    return RbTree::T(Color::Red, left, x3.clone(), right);
                }

                // Black (l, x, (Red (r2, x2, Red (l3, x3, r3))))
                if let &RbTree::T(Color::Red, ref l3, ref x3, ref r3) = r2.clone().as_ref() {
                    let left = Rc::new(RbTree::T(Color::Black, l.clone(), x.clone(), l3.clone()));
                    let right = Rc::new(RbTree::T(Color::Black, l2.clone(), x3.clone(), r3.clone()));
                    return RbTree::T(Color::Red, left, x2.clone(), right);
                }
            }
        }

        return self;
    }

    /// Checks the tree for the presence of a given `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use coll::persistent::RbTree;
    /// let tree: RbTree<i32> = RbTree::new().insert(1).insert(2).insert(3);
    /// assert!(tree.contains(1));
    /// assert!(tree.contains(2));
    /// assert!(tree.contains(3));
    /// assert_eq!(tree.contains(4), false);
    /// ```
    pub fn contains(&self, x: T) -> bool
        where T: PartialEq + PartialOrd
    {
        match self {
            &RbTree::T(_, ref left, ref y, ref right) => {
                if x < **y {
                    left.contains(x)
                } else if x > **y {
                    right.contains(x)
                } else {
                    true
                }
            }
            _ => false,
        }
    }

    /// Inserts an item into a new copy of the existing `RbTree`.
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
    pub fn insert(&self, x: T) -> Self
        where T: PartialOrd
    {
        fn ins<T>(t: &RbTree<T>, x: T) -> RbTree<T>
            where T: PartialOrd
        {
            let empty = Rc::new(RbTree::E);

            match t {
                &RbTree::E => RbTree::T(Color::Red, empty.clone(), Rc::new(x), empty.clone()),

                &RbTree::T(ref color, ref l, ref y, ref r) if x < **y => {
                    let left = Rc::new(ins(l, x));
                    let result = RbTree::T(color.clone(), left, y.clone(), r.clone());
                    result.balance()
                }

                &RbTree::T(ref color, ref l, ref y, ref r) if x > **y => {
                    let right = Rc::new(ins(r, x));
                    let result = RbTree::T(color.clone(), l.clone(), y.clone(), right);
                    result.balance()
                }

                &RbTree::T(ref color, ref l, ref _y, ref r) => {
                    RbTree::T(color.clone(), l.clone(), Rc::new(x), r.clone())
                }
            }
        }

        if let RbTree::T(_, left, y, right) = ins(self, x) {
            RbTree::T(Color::Black, left, y, right)
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

impl<T> PartialEq<RbTree<T>> for RbTree<T>
    where T: PartialEq + PartialOrd
{
    fn eq(&self, other: &RbTree<T>) -> bool {
        match (self, other) {
            (&RbTree::E, &RbTree::E) => true,
            (&RbTree::E, _) | (_, &RbTree::E) => false,

            (&RbTree::T(ref c1, ref l1, ref e1, ref r1),
             &RbTree::T(ref c2, ref l2, ref e2, ref r2)) => {
                c1 == c2 && l1 == l2 && e1 == e2 && r1 == r2
            }
        }
    }
}

#[test]
fn two_empty_trees_are_equal() {
    let left: &RbTree<i32> = &RbTree::new();
    let right: &RbTree<i32> = &RbTree::new();
    assert_eq!(left, right);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_1() {
    let empty = Rc::new(RbTree::E);

    let y1 = Rc::new(RbTree::new_with_value('y'));
    let x1 = Rc::new(RbTree::T(Color::Red, empty.clone(), Rc::new('x'), y1));
    let z1 = RbTree::T(Color::Black, x1, Rc::new('z'), empty.clone());

    let x2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = RbTree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = z1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_2() {
    let empty = Rc::new(RbTree::E);

    let x1 = Rc::new(RbTree::new_with_value('x'));
    let y1 = Rc::new(RbTree::T(Color::Red, x1, Rc::new('y'), empty.clone()));
    let z1 = RbTree::T(Color::Black, y1, Rc::new('z'), empty.clone());

    let x2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = RbTree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = z1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_gives_the_correct_tree_3() {
    let empty = Rc::new(RbTree::E);

    let z1 = Rc::new(RbTree::new_with_value('z'));
    let y1 = Rc::new(RbTree::T(Color::Red, empty.clone(), Rc::new('y'), z1));
    let x1 = RbTree::T(Color::Black, empty.clone(), Rc::new('x'), y1);

    let x2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = RbTree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = x1.balance();
    assert_eq!(result, expected);
}

#[test]
fn balancing_three_nodes_produces_the_correct_tree_4() {
    let empty = Rc::new(RbTree::E);

    let y1 = Rc::new(RbTree::new_with_value('y'));
    let z1 = Rc::new(RbTree::T(Color::Red, y1, Rc::new('z'), empty.clone()));
    let x1 = RbTree::T(Color::Black, empty.clone(), Rc::new('x'), z1);

    let x2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z2 = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = RbTree::T(Color::Red, x2, Rc::new('y'), z2);

    let result = x1.balance();
    assert_eq!(result, expected);
}

#[test]
fn insert_three_items_gives_the_expected_tree() {
    let empty = Rc::new(RbTree::E);

    let tree = RbTree::new().insert('x').insert('y').insert('z');

    let x = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone()));
    let z = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new('z'), empty.clone()));
    let expected = RbTree::T(Color::Black, x, Rc::new('y'), z);

    assert_eq!(tree, expected);
}


#[test]
fn insert_two_items_gives_the_expected_tree() {
    let empty = Rc::new(RbTree::E);

    let tree = RbTree::new().insert('x').insert('y');

    let y = Rc::new(RbTree::T(Color::Red, empty.clone(), Rc::new('y'), empty.clone()));
    let expected = RbTree::T(Color::Black, empty.clone(), Rc::new('x'), y);

    assert_eq!(tree, expected);
}

#[test]
fn insert_a_single_item_gives_the_expected_tree() {
    let tree = RbTree::new().insert('x');

    let empty = Rc::new(RbTree::E);
    let expected = RbTree::T(Color::Black, empty.clone(), Rc::new('x'), empty.clone());

    assert_eq!(tree, expected);
}

#[test]
fn insert_with_7_items_builds_the_correct_tree() {
    let empty = Rc::new(RbTree::E);

    let tree = RbTree::new().insert(1).insert(2).insert(3)
                            .insert(4).insert(5).insert(6)
                            .insert(7);

    let one = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new(1), empty.clone()));
    let five = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new(5), empty.clone()));
    let two = Rc::new(RbTree::T(Color::Black, one, Rc::new(2), five));
    let three = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new(3), empty.clone()));
    let seven = Rc::new(RbTree::T(Color::Black, empty.clone(), Rc::new(7), empty.clone()));
    let six = Rc::new(RbTree::T(Color::Black, three, Rc::new(6), seven));
    let expected = RbTree::T(Color::Black, two, Rc::new(4), six);

    assert_eq!(tree, expected);
}

#[test]
fn insert_doesnt_allow_duplicates() {
    let tree_one = RbTree::new().insert(1).insert(1).insert(1).insert(1).insert(1);
    let tree_two = RbTree::new().insert(1);

    assert_eq!(tree_one, tree_two);
}

#[test]
fn contains_finds_all_elements() {
    let tree = RbTree::new().insert(1).insert(2).insert(3).insert(4).insert(5);
    let contains_all = tree.contains(1) && tree.contains(2) && tree.contains(3) &&
                       tree.contains(4) && tree.contains(5);

    assert!(contains_all);
}