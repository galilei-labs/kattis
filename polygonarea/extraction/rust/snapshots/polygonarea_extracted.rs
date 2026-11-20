#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = Int63;

// Rocq: Polygonarea.polygonarea_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Polygonarea.polygonarea_implem.area_loop
// Variant: uncurried
pub fn area_loop_1(x: Array<Int63>, y: Array<Int63>, m: Int63, i: Int63, acc: Int63) -> Int63 {
  area_loop(x, y, m, i, acc, ())
}

// Rocq: Polygonarea.polygonarea_implem.area_loop (local: area_loop)
// Variant: uncurried, lifted
pub fn area_loop(x: Array<Int63>, y: Array<Int63>, m: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x.get_cloned(i);
      let tmp_3 = y.get_cloned(i + int63!(1));
      let tmp_4 = acc + tmp_2 * tmp_3;
      let tmp_5 = x.get_cloned(i + int63!(1));
      let tmp_6 = y.get_cloned(i);
      area_loop(x, y, m, tmp_1, tmp_4 - tmp_5 * tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      acc
    },
  }
}

// Rocq: Polygonarea.polygonarea_implem.signed_area2_impl
// Variant: uncurried
pub fn signed_area2_impl(x: Array<Int63>, y: Array<Int63>) -> Int63 {
  let tmp = x.length();
  let m = tmp - int63!(1);
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let s = area_loop_1(x_clone, y_clone, m, int63!(0), int63!(0));
  let tmp_1 = x.get_cloned(m);
  let tmp_2 = y.get_cloned(int63!(0));
  let tmp_3 = s + tmp_1 * tmp_2;
  let tmp_4 = x.get_cloned(int63!(0));
  std::mem::drop(x);
  let tmp_5 = y.get_cloned(m);
  std::mem::drop(y);
  tmp_3 - tmp_4 * tmp_5
}
