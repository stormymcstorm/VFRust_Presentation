extern crate prusti_contracts;
use prusti_contracts::*;

pub enum BST {
  Node {
    value: i32,
    left: Box<BST>,
    right: Box<BST>,
  },
  Empty,
}

impl BST {
  pub fn new() -> BST {
    BST::Empty
  }

  #[ensures(match result {
    BST::Empty => false,

    BST::Node {value, ..} => val == value
  })]
  fn create_node(val: i32) -> BST {
    BST::Node {
      value: val,
      left: Box::new(BST::Empty),
      right: Box::new(BST::Empty)
    }
  }
  
  #[pure]
  #[ensures(matches!(*self, BST::Empty) == result)]
  pub fn is_empty(&self) -> bool {
    match self {
      BST::Empty => true,
      _ => false,
    }
  }

  #[pure]
  #[ensures(match *self {
    BST::Empty => result == 0,
    
    BST::Node{ref left, ref right, ..} => result == 1 + left.len() + right.len(),
  })]
  pub fn len(&self) -> usize {
    match self {
      BST::Empty => 0,

      BST::Node{value, left, right} => 1 + left.len() + right.len(),
    }
  }

  #[ensures(! self.is_empty())]
  #[ensures(self.contains(val))]
  #[ensures(old(self.contains(val)) ==> self.len() == old(self.len()))]
  // #[ensures(old(! self.contains(val)) ==> self.len() == 1 + old(self.len()))]
  #[ensures(old(matches!(*self, BST::Empty)) ==> self.len() == 1 + old(self.len()))]
  pub fn insert(&mut self, val: i32) {
    match self {
      BST::Empty => *self = BST::create_node(val),

      BST::Node {
        ref value,
        ref mut left,
        ref mut right,
      } => if val == *value {
        return
      } else if val < *value {
        left.insert(val);
      } else {
        right.insert(val);
      },
    }
  }

  #[pure]
  // #[ensures(match *self {
  //   BST::Empty => false,

  //   BST::Node{ref value, ref left, ref right} => val == *value || left.contains(val) || right.contains(val)
  // })]
  fn contains(&self, val: i32) -> bool {
    match self {
      BST::Empty => false,

      BST::Node {
        ref value,
        ref left,
        ref right,
      } => if val == *value {
        true
      } else if val <= *value {
        left.contains(val)
      } else {
        right.contains(val)
      }
    }
  }
}