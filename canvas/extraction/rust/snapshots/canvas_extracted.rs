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

pub type uint = Int63;

// Rocq: Canvas.canvas_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Canvas.canvas_implem.sift
// Variant: uncurried
pub fn sift_1(h: Array<Int63>, sz: Int63, i: Int63) -> Array<Int63> {
  sift(h, sz, i, ())
}

// Rocq: Canvas.canvas_implem.sift (local: sift)
// Variant: uncurried, lifted
pub fn sift(h: Array<Int63>, sz: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let x = h.get_cloned(i);
  let l = int63!(2) * i + int63!(1);
  if l < sz {
    let yl = h.get_cloned(l);
    let r = l + int63!(1);
    let tmp = r < sz;
    let tmp_1 = h.get_cloned(r);
    let tmp_2 = tmp_1 < yl;
    if andb(tmp, tmp_2) {
      let yr = h.get_cloned(r);
      let tmp_3 = andb(yr < x, i < r);
      match bdec(tmp_3) {
        sumbool::left => {
          sift(h.set(i, yr).set(r, x), sz, r, ())
        },
        sumbool::right => {
          h
        },
      }
    } else {
      let tmp_4 = andb(yl < x, i < l);
      match bdec(tmp_4) {
        sumbool::left => {
          sift(h.set(i, yl).set(l, x), sz, l, ())
        },
        sumbool::right => {
          h
        },
      }
    }
  } else {
    h
  }
}

// Rocq: Canvas.canvas_implem.build
// Variant: uncurried
pub fn build_1(h: Array<Int63>, sz: Int63, k: Int63) -> Array<Int63> {
  build(h, sz, k, ())
}

// Rocq: Canvas.canvas_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(h: Array<Int63>, sz: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      build(sift_1(h, sz, k - int63!(1)), sz, k - int63!(1), ())
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Canvas.canvas_implem.huff
// Variant: uncurried
pub fn huff_1(h: Array<Int63>, sz: Int63, acc: Int63) -> Int63 {
  huff(h, sz, acc, ())
}

// Rocq: Canvas.canvas_implem.huff (local: huff)
// Variant: uncurried, lifted
pub fn huff(h: Array<Int63>, sz: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = int63!(1) < sz;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = h.get_cloned(int63!(0));
      let sz1 = sz - int63!(1);
      let tmp_1 = h.get_cloned(sz1);
      let h1 = sift_1(h.set(int63!(0), tmp_1), sz1, int63!(0));
      let b_1 = h1.get_cloned(int63!(0));
      let h2 = sift_1(h1.set(int63!(0), a_1 + b_1), sz1, int63!(0));
      huff(h2, sz1, acc + (a_1 + b_1), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      acc
    },
  }
}

// Rocq: Canvas.canvas_implem.canvas_impl
pub fn canvas_impl(x: Array<Int63>) -> Int63 {
  let sz = x.length();
  let x_ref = &x;
  let tmp = x_ref.copy();
  std::mem::drop(x);
  let tmp_1 = sz / int63!(2);
  let h = build_1(tmp, sz, tmp_1);
  huff_1(h, sz, int63!(0))
}
