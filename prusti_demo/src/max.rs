extern crate prusti_contracts;
use prusti_contracts::*;


#[pure]
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
fn max(a: i32, b: i32) -> i32 {
  if a < b {
    b
  } else {
    a
  }
}
