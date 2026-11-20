#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint as b;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

// Rocq: Magicsequence.magicsequence_implem.mask
pub fn mask() -> Int63 {
  int63!(65535)
}

// Rocq: Magicsequence.magicsequence_implem.K
pub fn K() -> Int63 {
  int63!(65536)
}

// Rocq: Magicsequence.magicsequence_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Magicsequence.magicsequence_implem.gen_loop
// Variant: uncurried
pub fn gen_loop_1(a_1: Int63, b_1: Int63, c: Int63, n: Int63, i: Int63, t: Int63, m: Int63, arr: Array<Int63>, lo: Array<Int63>, hi: Array<Int63>) -> (((Array<Int63>, Int63), Array<Int63>), Array<Int63>) {
  gen_loop(a_1, b_1, c, n, i, t, m, arr, lo, hi, ())
}

// Rocq: Magicsequence.magicsequence_implem.gen_loop (local: gen_loop)
// Variant: uncurried, lifted
pub fn gen_loop(a_1: Int63, b_1: Int63, c: Int63, n: Int63, i: Int63, t: Int63, m: Int63, arr: Array<Int63>, lo: Array<Int63>, hi: Array<Int63>, _H: ()) -> (((Array<Int63>, Int63), Array<Int63>), Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let dl = t & __rocq_global_60;
      let dh = t >> int63!(16) & __rocq_global_60;
      let kl = lo.get_cloned(dl);
      let kh = hi.get_cloned(dh);
      let tmp_1 = i + int63!(1);
      let tmp_2 = (t * b_1 + a_1) % c;
      let tmp_3 = if m < t {
        t
      } else {
        m
      };
      gen_loop(a_1, b_1, c, n, tmp_1, tmp_2, tmp_3, arr.set(i, t), lo.set(dl, kl + int63!(1)), hi.set(dh, kh + int63!(1)), ())
    },
    sumbool::right => {
      (((arr, m), lo), hi)
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(e: Int63, acc: Int63, cnt: Array<Int63>) -> Array<Int63> {
  prefix_loop(e, acc, cnt, ())
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(e: Int63, acc: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = e < __rocq_global_223;
  match bdec(tmp) {
    sumbool::left => {
      let k = cnt.get_cloned(e);
      prefix_loop(e + int63!(1), acc + k, cnt.set(e, acc), ())
    },
    sumbool::right => {
      cnt
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(s: Int63, n: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  place_loop(s, n, src, i, cnt, dst, ())
}

// Rocq: Magicsequence.magicsequence_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(s: Int63, n: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let e = src.get_cloned(i);
      let d = e >> s & __rocq_global_60;
      let p = cnt.get_cloned(d);
      place_loop(s, n, src, i + int63!(1), cnt.set(d, p + int63!(1)), dst.set(p, e), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      std::mem::drop(cnt);
      dst
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.pass
// Variant: uncurried
pub fn pass(s: Int63, n: Int63, src: Array<Int63>, cnt: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  let cnt_1 = prefix_loop_1(int63!(0), int63!(0), cnt);
  place_loop_1(s, n, src, int63!(0), cnt_1, dst)
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop
// Variant: uncurried
pub fn hash_loop_1(x: Int63, y: Int63, n: Int63, i: Int63, v: Int63, r: Array<Int63>) -> Int63 {
  hash_loop(x, y, n, i, v, r, ())
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop (local: hash_loop)
// Variant: uncurried, lifted
pub fn hash_loop(x: Int63, y: Int63, n: Int63, i: Int63, v: Int63, r: Array<Int63>, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = v * x;
      let tmp_3 = r.get_cloned(i);
      let tmp_4 = (tmp_2 + tmp_3) % y;
      hash_loop(x, y, n, tmp_1, tmp_4, r, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      v
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.magic_impl
// Variant: uncurried
pub fn magic_impl(n: Int63, a_1: Int63, b_1: Int63, c: Int63, x: Int63, y: Int63) -> Int63 {
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = gen_loop_1(a_1, b_1, c, n, int63!(0), a_1, int63!(0), tmp, Array::<Int63>::make(__rocq_global_223, int63!(0)), Array::<Int63>::make(__rocq_global_223, int63!(0)));
  match tmp_1 {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          match v61 {
            (v66, v68) => {
              let m = &v66;
              let tmp_2 = Array::<Int63>::make(n, int63!(0));
              let m_clone = Clone::clone(m);
              let r1 = pass(int63!(0), n, m_clone, v63, tmp_2);
              let tmp_3 = __rocq_global_223;
              let r = if v68 < tmp_3 {
                std::mem::drop(v66);
                std::mem::drop(v58);
                r1
              } else {
                pass(int63!(16), n, r1, v58, v66)
              };
              hash_loop_1(x, y, n, int63!(0), int63!(0), r)
            },
          }
        },
      }
    },
  }
}
const __rocq_global_60: Int63 = int63!(65535);
const __rocq_global_223: Int63 = int63!(65536);