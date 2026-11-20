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

pub type char63 = Int63;

pub type uint = Int63;

// Rocq: Zapis.zapis_implem.MOD
pub fn MOD() -> Int63 {
  int63!(100000)
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Zapis.zapis_implem.bdec
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Zapis.zapis_implem.okp
// Variant: uncurried
pub fn okp(a_1: Int63, b_1: Int63, o: Int63, c: Int63) -> bool {
  andb(orb(a_1 == o, a_1 == int63!(63)), orb(b_1 == c, b_1 == int63!(63)))
}

// Rocq: Zapis.zapis_implem.pcode
// Variant: uncurried
pub fn pcode(a_1: Int63, b_1: Int63) -> Int63 {
  let tmp = int63!(40);
  let tmp_1 = int63!(41);
  let tmp_2 = if okp(a_1, b_1, tmp, tmp_1) {
    int63!(1)
  } else {
    int63!(0)
  };
  let tmp_3 = int63!(91);
  let tmp_4 = int63!(93);
  let tmp_5 = if okp(a_1, b_1, tmp_3, tmp_4) {
    int63!(1)
  } else {
    int63!(0)
  };
  let tmp_6 = tmp_2 + tmp_5;
  let tmp_7 = int63!(123);
  let tmp_8 = int63!(125);
  let tmp_9 = if okp(a_1, b_1, tmp_7, tmp_8) {
    int63!(1)
  } else {
    int63!(0)
  };
  tmp_6 + tmp_9
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Zapis.zapis_implem.ixi
// Variant: uncurried
pub fn ixi(W: Int63, a_1: Int63, b_1: Int63) -> Int63 {
  int63!(2) * (a_1 * W + b_1)
}

// Rocq: Zapis.zapis_implem.capm
pub fn capm(v: Int63) -> Int63 {
  if v < __rocq_global_216 {
    v
  } else {
    __rocq_global_216
  }
}

// Rocq: Zapis.zapis_implem.inner
// Variant: uncurried
pub fn inner_1(x: rocq_string::RocqString, tb: Array<Int63>, W: Int63, ci: Int63, ii: Int63, j: Int63, kk: Int63, t: Int63, r: Int63, c: Int63) -> (Int63, Int63) {
  inner(x, tb, W, ci, ii, j, kk, t, r, c, ())
}

// Rocq: Zapis.zapis_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(x: rocq_string::RocqString, tb: Array<Int63>, W: Int63, ci: Int63, ii: Int63, j: Int63, kk: Int63, t: Int63, r: Int63, c: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = int63!(0) < t;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let p = pcode(ci, get(x_clone, kk));
      let ia = ixi(W, ii + int63!(1), kk);
      let ib = ixi(W, kk + int63!(1), j);
      let ra = tb.get_cloned(ia);
      let ca = tb.get_cloned(ia + int63!(1));
      let rb = tb.get_cloned(ib);
      let cb = tb.get_cloned(ib + int63!(1));
      let tmp_1 = kk + int63!(2);
      let tmp_2 = t - int63!(1);
      let tmp_3 = (r + p * ra % __rocq_global_216 * rb) % __rocq_global_216;
      let tmp_4 = capm(p * ca);
      let tmp_5 = capm(tmp_4 * cb);
      inner(x, tb, W, ci, ii, j, tmp_1, tmp_2, tmp_3, capm(c + tmp_5), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(tb);
      (r, c)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Zapis.zapis_implem.middle
// Variant: uncurried
pub fn middle_1(x: rocq_string::RocqString, W: Int63, h: Int63, L: Int63, m: Int63, ii: Int63, tb: Array<Int63>) -> Array<Int63> {
  middle(x, W, h, L, m, ii, tb, ())
}

// Rocq: Zapis.zapis_implem.middle (local: middle)
// Variant: uncurried, lifted
pub fn middle(x: rocq_string::RocqString, W: Int63, h: Int63, L: Int63, m: Int63, ii: Int63, tb: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = ii < m;
  match bdec(tmp) {
    sumbool::left => {
      let j = ii + L;
      let tmp_1 = int63!(0);
      let b0 = if h == tmp_1 {
        int63!(1)
      } else {
        int63!(0)
      };
      let x_clone = Clone::clone(&x);
      let tmp_2 = get(x_clone, ii);
      let tmp_3 = ii + int63!(1);
      let x_clone_1 = Clone::clone(&x);
      let tb_clone = Clone::clone(&tb);
      let rc = inner_1(x_clone_1, tb_clone, W, tmp_2, ii, j, tmp_3, h, b0, b0);
      let p = ixi(W, ii, j);
      let tmp_4 = ii + int63!(1);
      let rc_clone = Clone::clone(&rc);
      middle(x, W, h, L, m, tmp_4, tb.set(p, fst::<Int63, Int63>(rc_clone)).set(p + int63!(1), snd::<Int63, Int63>(rc)), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tb
    },
  }
}

// Rocq: Zapis.zapis_implem.outer
// Variant: uncurried
pub fn outer_1(x: rocq_string::RocqString, n: Int63, W: Int63, hm: Int63, h: Int63, tb: Array<Int63>) -> Array<Int63> {
  outer(x, n, W, hm, h, tb, ())
}

// Rocq: Zapis.zapis_implem.outer (local: outer)
// Variant: uncurried, lifted
pub fn outer(x: rocq_string::RocqString, n: Int63, W: Int63, hm: Int63, h: Int63, tb: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = h < hm;
  match bdec(tmp) {
    sumbool::left => {
      let L = int63!(2) * h;
      let tmp_1 = h + int63!(1);
      let tmp_2 = n - L + int63!(1);
      let x_clone = Clone::clone(&x);
      let tmp_3 = middle_1(x_clone, W, h, L, tmp_2, int63!(0), tb);
      outer(x, n, W, hm, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tb
    },
  }
}

// Rocq: Zapis.zapis_implem.zapis_impl
pub fn zapis_impl(x: rocq_string::RocqString) -> (Int63, bool) {
  let x_clone = Clone::clone(&x);
  let n = length(x_clone);
  let W = n + int63!(1);
  let tmp = n / int63!(2) + int63!(1);
  let tmp_1 = W * W;
  let tb = outer_1(x, n, W, tmp, int63!(0), Array::<Int63>::make(int63!(2) * tmp_1, int63!(0)));
  let p = ixi(W, int63!(0), n);
  let tmp_2 = tb.get_cloned(p);
  let tmp_3 = __rocq_global_216;
  let tmp_4 = tb.get_cloned(p + int63!(1));
  std::mem::drop(tb);
  (tmp_2, tmp_3 <= tmp_4)
}
const __rocq_global_216: Int63 = int63!(100000);