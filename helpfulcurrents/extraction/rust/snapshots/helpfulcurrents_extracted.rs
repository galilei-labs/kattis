#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

pub type char63 = Int63;

// Rocq: Helpfulcurrents.helpfulcurrents_implem.P
pub fn P() -> Int63 {
  int63!(1000003)
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.bdec
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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.addm
// Variant: uncurried
pub fn addm(a_1: Int63, b_1: Int63) -> Int63 {
  let s = a_1 + b_1;
  if s < __rocq_global_93 {
    s
  } else {
    s - __rocq_global_93
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.orf
// Variant: uncurried
pub fn orf(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 == int63!(0) {
    b_1
  } else {
    a_1
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass1
// Variant: uncurried
pub fn pass1_1(s: rocq_string::RocqString, sb: rocq_string::RocqString, Ym: Int63, Xm: Int63, xim: Int63, y: Int63, x: Int63, wv: Int63, wf: Int63, cv: Array<Int63>, cf: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  pass1(s, sb, Ym, Xm, xim, y, x, wv, wf, cv, cf, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass1 (local: pass1)
// Variant: uncurried, lifted
pub fn pass1(s: rocq_string::RocqString, sb: rocq_string::RocqString, Ym: Int63, Xm: Int63, xim: Int63, y: Int63, x: Int63, wv: Int63, wf: Int63, cv: Array<Int63>, cf: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = x < Xm;
  match bdec(tmp) {
    sumbool::left => {
      let s_clone = Clone::clone(&s);
      let c = get(s_clone, x);
      let st = andb(y + int63!(1) == Ym, x == xim);
      let sv = if st {
        int63!(1)
      } else {
        int63!(0)
      };
      let tmp_1 = y + int63!(1) < Ym;
      let sb_clone = Clone::clone(&sb);
      let tmp_2 = andb(tmp_1, negb(get(sb_clone, x) == int63!(64)));
      let north = andb(tmp_2, negb(c == int63!(35)));
      let nv = if north {
        cv.get_cloned(x)
      } else {
        int63!(0)
      };
      let nf = if north {
        cf.get_cloned(x)
      } else {
        int63!(0)
      };
      let tmp_3 = addm(sv, nv);
      let av = addm(tmp_3, wv);
      let tmp_4 = orf(sv, nf);
      let af = orf(tmp_4, wf);
      let w = c == int63!(62);
      let tmp_5 = x + int63!(1);
      let tmp_6 = if w {
        av
      } else {
        int63!(0)
      };
      let tmp_7 = if w {
        af
      } else {
        int63!(0)
      };
      pass1(s, sb, Ym, Xm, xim, y, tmp_5, tmp_6, tmp_7, cv.set(x, av), cf.set(x, af), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      std::mem::drop(sb);
      (cv, cf)
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2
// Variant: uncurried
pub fn pass2_1(s: rocq_string::RocqString, x: Int63, ev: Int63, ef: Int63, cv: Array<Int63>, cf: Array<Int63>, av: Int63, af: Int63) -> ((Array<Int63>, Array<Int63>), (Int63, Int63)) {
  pass2(s, x, ev, ef, cv, cf, av, af, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2 (local: pass2)
// Variant: uncurried, lifted
pub fn pass2(s: rocq_string::RocqString, x: Int63, ev: Int63, ef: Int63, cv: Array<Int63>, cf: Array<Int63>, av: Int63, af: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), (Int63, Int63)) {
  let tmp = int63!(0) < x;
  match bdec(tmp) {
    sumbool::left => {
      let x_ = x - int63!(1);
      let s_clone = Clone::clone(&s);
      let c = get(s_clone, x_);
      let tmp_1 = cv.get_cloned(x_);
      let bv = addm(tmp_1, ev);
      let tmp_2 = cf.get_cloned(x_);
      let bf = orf(tmp_2, ef);
      let e = c == int63!(60);
      let k = c == int63!(64);
      let tmp_3 = if e {
        bv
      } else {
        int63!(0)
      };
      let tmp_4 = if e {
        bf
      } else {
        int63!(0)
      };
      let tmp_5 = cv.set(x_, bv);
      let tmp_6 = cf.set(x_, bf);
      let tmp_7 = if k {
        bv
      } else {
        av
      };
      let tmp_8 = if k {
        bf
      } else {
        af
      };
      pass2(s, x_, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      ((cv, cf), (av, af))
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

// Rocq: Helpfulcurrents.helpfulcurrents_implem.pass2r
// Variant: uncurried
pub fn pass2r(s: rocq_string::RocqString, Xm: Int63, r1: (Array<Int63>, Array<Int63>), av: Int63, af: Int63) -> ((Array<Int63>, Array<Int63>), (Int63, Int63)) {
  let r1_clone = Clone::clone(&r1);
  pass2_1(s, Xm, int63!(0), int63!(0), fst::<Array<Int63>, Array<Int63>>(r1_clone), snd::<Array<Int63>, Array<Int63>>(r1), av, af)
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows
// Variant: uncurried
pub fn rows_1(m: Array<rocq_string::RocqString>, Ym: Int63, Xm: Int63, xim: Int63, k: Int63, cv: Array<Int63>, cf: Array<Int63>, av: Int63, af: Int63) -> (Int63, Int63) {
  rows(m, Ym, Xm, xim, k, cv, cf, av, af, ())
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.rows (local: rows)
// Variant: uncurried, lifted
pub fn rows(m: Array<rocq_string::RocqString>, Ym: Int63, Xm: Int63, xim: Int63, k: Int63, cv: Array<Int63>, cf: Array<Int63>, av: Int63, af: Int63, _H: ()) -> (Int63, Int63) {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let y = k - int63!(1);
      let m_ref = &m;
      let s = m_ref.get_cloned(y);
      let m_ref_1 = &m;
      let tmp_1 = m_ref_1.get_cloned(k);
      let s_clone = Clone::clone(&s);
      let r1 = pass1_1(s_clone, tmp_1, Ym, Xm, xim, y, int63!(0), int63!(0), int63!(0), cv, cf);
      let r2 = pass2r(s, Xm, r1, av, af);
      let r2_clone = Clone::clone(&r2);
      let tmp_2 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), (Int63, Int63)>(r2_clone));
      let r2_clone_1 = Clone::clone(&r2);
      let tmp_3 = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), (Int63, Int63)>(r2_clone_1));
      let r2_clone_2 = Clone::clone(&r2);
      rows(m, Ym, Xm, xim, y, tmp_2, tmp_3, fst::<Int63, Int63>(snd::<(Array<Int63>, Array<Int63>), (Int63, Int63)>(r2_clone_2)), snd::<Int63, Int63>(snd::<(Array<Int63>, Array<Int63>), (Int63, Int63)>(r2)), ())
    },
    sumbool::right => {
      std::mem::drop(m);
      std::mem::drop(cv);
      std::mem::drop(cf);
      (av, af)
    },
  }
}

// Rocq: Helpfulcurrents.helpfulcurrents_implem.helpfulcurrents_impl
// Variant: uncurried
pub fn helpfulcurrents_impl(Ym: Int63, Xm: Int63, xim: Int63, m: Array<rocq_string::RocqString>) -> Rc<option<Int63>> {
  let tmp = Array::<Int63>::make(Xm, int63!(0));
  let tmp_1 = Array::<Int63>::make(Xm, int63!(0));
  let r = rows_1(m, Ym, Xm, xim, Ym, tmp, tmp_1, int63!(0), int63!(0));
  let r_clone = Clone::clone(&r);
  let tmp_2 = snd::<Int63, Int63>(r_clone);
  if tmp_2 == int63!(0) {
    std::mem::drop(r);
    Rc::new(option::<Int63>::None)
  } else {
    Rc::new(option::<Int63>::Some(fst::<Int63, Int63>(r)))
  }
}
const __rocq_global_93: Int63 = int63!(1000003);