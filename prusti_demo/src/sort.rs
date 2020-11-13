extern crate prusti_contracts;
use prusti_contracts::*;

pub struct VecWrapper(Vec<i32>);

impl VecWrapper {

  #[trusted]
  #[ensures(result.len() == 0)]
  pub fn new() -> Self {
    VecWrapper(Vec::new())
  }

  #[trusted]
  #[pure]
  #[requires(0 <= index && index < self.len())]
  pub fn lookup(&self, index: usize) -> i32 {
    self.0[index]
  }

  #[trusted]
  #[pure]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  #[pure]
  #[trusted]
  #[requires(0 <= a && a < self.len())]
  #[requires(0 <= b && b < self.len())]
  #[after_expiry(self.len() == old(self.len()))]
  #[after_expiry(self.lookup(a) == old(self.lookup(b)))]
  #[after_expiry(self.lookup(b) == old(self.lookup(a)))]
  pub fn swap(&mut self, a: usize, b: usize) {
    self.0.swap(a, b);
  }
}

#[ensures(list.len() == old(list.len()))]
// #[ensures(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < list.len()) ==>
//             list.lookup(k1) <= list.lookup(k2)))]
pub fn insertion_sort(list: &mut VecWrapper) {
  let mut i = 1;

  while i < list.len() {
    body_invariant!(i >= 1);
    body_invariant!(i < list.len());
    body_invariant!(list.len() == old(list.len()));
    // body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < k2 && k2 < i) ==>
    //   list.lookup(k1) <= list.lookup(k2)));
    // body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < i && i <= k2 && k2 < list.len()) ==>
    //   list.lookup(k1) <= list.lookup(k2)));

    let mut j = i;

    while j > 0 && list.lookup(j) < list.lookup(j - 1){
      body_invariant!(j <= i);
      body_invariant!(j >= 1);
      body_invariant!(j < list.len());
      // body_invariant!(forall(|k1: usize, k2: usize| (0 <= k1 && k1 < list.len() 
      //   && k1 < k2 && k2 < list.len()) ==>
      //   list.lookup(k1) <= list.lookup(k2)));

      list.swap(j, j - 1);
      
      j -= 1;

      body_invariant!(list.len() == old(list.len()));
      body_invariant!(j >= 0);
      body_invariant!(j <= list.len());
    }

    i += 1;
  }
}