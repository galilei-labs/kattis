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

pub type char63 = Int63;

pub type uint = Int63;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Suffixsorting.suffixsorting_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Suffixsorting.suffixsorting_implem.init_rank
// Variant: uncurried
pub fn init_rank_1(x: rocq_string::RocqString, n: Int63, i: Int63, r: Array<Int63>) -> Array<Int63> {
  init_rank(x, n, i, r, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.init_rank (local: init_rank)
// Variant: uncurried, lifted
pub fn init_rank(x: rocq_string::RocqString, n: Int63, i: Int63, r: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let x_clone = Clone::clone(&x);
      let tmp_2 = get(x_clone, i);
      init_rank(x, n, tmp_1, r.set(i, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      r
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.init_id
// Variant: uncurried
pub fn init_id_1(n: Int63, i: Int63, sa: Array<Int63>) -> Array<Int63> {
  init_id(n, i, sa, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.init_id (local: init_id)
// Variant: uncurried, lifted
pub fn init_id(n: Int63, i: Int63, sa: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      init_id(n, i + int63!(1), sa.set(i, i), ())
    },
    sumbool::right => {
      sa
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.cbound
pub fn cbound(n: Int63) -> Int63 {
  if n < int63!(256) {
    int63!(257)
  } else {
    n + int63!(1)
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(r: Array<Int63>, n: Int63, k: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>) -> Array<Int63> {
  count_loop(r, n, k, src, i, cnt, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(r: Array<Int63>, n: Int63, k: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let x = src.get_cloned(i);
      let tmp_1 = x + k;
      let v = if tmp_1 < n {
        let tmp_2 = x + k;
        r.get_cloned(tmp_2)
      } else {
        int63!(0)
      };
      let tmp_3 = i + int63!(1);
      let tmp_4 = cnt.get_cloned(v);
      count_loop(r, n, k, src, tmp_3, cnt.set(v, tmp_4 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(src);
      cnt
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(B: Int63, v: Int63, acc: Int63, cnt: Array<Int63>) -> Array<Int63> {
  prefix_loop(B, v, acc, cnt, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(B: Int63, v: Int63, acc: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = v < B;
  match bdec(tmp) {
    sumbool::left => {
      let c = cnt.get_cloned(v);
      prefix_loop(B, v + int63!(1), acc + c, cnt.set(v, acc), ())
    },
    sumbool::right => {
      cnt
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(r: Array<Int63>, n: Int63, k: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  place_loop(r, n, k, src, i, cnt, dst, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(r: Array<Int63>, n: Int63, k: Int63, src: Array<Int63>, i: Int63, cnt: Array<Int63>, dst: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let x = src.get_cloned(i);
      let tmp_1 = x + k;
      let v = if tmp_1 < n {
        let tmp_2 = x + k;
        r.get_cloned(tmp_2)
      } else {
        int63!(0)
      };
      let p = cnt.get_cloned(v);
      place_loop(r, n, k, src, i + int63!(1), cnt.set(v, p + int63!(1)), dst.set(p, x), ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(src);
      std::mem::drop(cnt);
      dst
    },
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.csort
// Variant: uncurried
pub fn csort(r: Array<Int63>, n: Int63, k: Int63, src: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  let B = cbound(n);
  let tmp = Array::<Int63>::make(B, int63!(0));
  let r_clone = Clone::clone(&r);
  let src_clone = Clone::clone(&src);
  let c0 = count_loop_1(r_clone, n, k, src_clone, int63!(0), tmp);
  let c1 = prefix_loop_1(B, int63!(0), int63!(0), c0);
  place_loop_1(r, n, k, src, int63!(0), c1, dst)
}

// Rocq: Suffixsorting.suffixsorting_implem.skey
// Variant: uncurried
pub fn skey(r: Array<Int63>, n: Int63, k: Int63, x: Int63) -> Int63 {
  let tmp = x + k;
  if tmp < n {
    let tmp_1 = r.get_cloned(x + k);
    std::mem::drop(r);
    tmp_1
  } else {
    std::mem::drop(r);
    int63!(0)
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.rank_loop
// Variant: uncurried
pub fn rank_loop_1(r: Array<Int63>, n: Int63, k: Int63, sa: Array<Int63>, t: Int63, cur: Int63, nr: Array<Int63>) -> (Array<Int63>, Int63) {
  rank_loop(r, n, k, sa, t, cur, nr, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.rank_loop (local: rank_loop)
// Variant: uncurried, lifted
pub fn rank_loop(r: Array<Int63>, n: Int63, k: Int63, sa: Array<Int63>, t: Int63, cur: Int63, nr: Array<Int63>, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = t < n;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = sa.get_cloned(t - int63!(1));
      let b_1 = sa.get_cloned(t);
      let tmp_1 = r.get_cloned(a_1);
      let tmp_2 = r.get_cloned(b_1);
      let tmp_3 = if tmp_1 == tmp_2 {
        let r_clone = Clone::clone(&r);
        let tmp_4 = skey(r_clone, n, k, a_1);
        let r_clone_1 = Clone::clone(&r);
        tmp_4 == skey(r_clone_1, n, k, b_1)
      } else {
        false
      };
      let c = if tmp_3 {
        cur
      } else {
        cur + int63!(1)
      };
      let tmp_5 = t + int63!(1);
      let tmp_6 = nr.set(b_1, c);
      rank_loop(r, n, k, sa, tmp_5, c, tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(sa);
      (nr, cur)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
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

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Suffixsorting.suffixsorting_implem.rounds
// Variant: uncurried
pub fn rounds_1(n: Int63, k: Int63, r: Array<Int63>, nr: Array<Int63>, sa: Array<Int63>, tmp: Array<Int63>) -> Array<Int63> {
  rounds(n, k, r, nr, sa, tmp, ())
}

// Rocq: Suffixsorting.suffixsorting_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(n: Int63, k: Int63, r: Array<Int63>, nr: Array<Int63>, sa: Array<Int63>, tmp: Array<Int63>, _H: ()) -> Array<Int63> {
  let r_clone = Clone::clone(&r);
  let sa_clone = Clone::clone(&sa);
  let tmp1 = csort(r_clone, n, k, sa_clone, tmp);
  let r_clone_1 = Clone::clone(&r);
  let tmp1_clone = Clone::clone(&tmp1);
  let sa1 = csort(r_clone_1, n, int63!(0), tmp1_clone, sa);
  let tmp_1 = sa1.get_cloned(int63!(0));
  let tmp_2 = nr.set(tmp_1, int63!(1));
  let r_clone_2 = Clone::clone(&r);
  let sa1_clone = Clone::clone(&sa1);
  let q = rank_loop_1(r_clone_2, n, k, sa1_clone, int63!(1), int63!(1), tmp_2);
  let q_clone = Clone::clone(&q);
  let tmp_3 = snd::<Array<Int63>, Int63>(q_clone);
  if tmp_3 == n {
    std::mem::drop(q);
    std::mem::drop(tmp1);
    std::mem::drop(r);
    sa1
  } else {
    let tmp_4 = k + k;
    let tmp_5 = andb(k < tmp_4, k + k < n);
    match bdec(tmp_5) {
      sumbool::left => {
        rounds(n, k + k, fst::<Array<Int63>, Int63>(q), r, sa1, tmp1, ())
      },
      sumbool::right => {
        std::mem::drop(q);
        std::mem::drop(tmp1);
        std::mem::drop(r);
        sa1
      },
    }
  }
}

// Rocq: Suffixsorting.suffixsorting_implem.suffix_array_impl
pub fn suffix_array_impl(x: rocq_string::RocqString) -> Array<Int63> {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let tmp = Array::<Int63>::make(n, int63!(0));
  let r = init_rank_1(x, n, int63!(0), tmp);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let sa = init_id_1(n, int63!(0), tmp_1);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  rounds_1(n, int63!(1), r, tmp_2, sa, tmp_3)
}
