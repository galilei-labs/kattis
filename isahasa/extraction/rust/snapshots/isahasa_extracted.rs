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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub struct ht {
  pub hkeys: Array<rocq_string::RocqString>,
  pub hnxt: Array<Int63>,
  pub hhead: Array<Int63>,
  pub hcnt: Int63,
}

impl Clone for ht {
  fn clone(&self) -> Self {
    match self {
      ht { hkeys: __field0, hnxt: __field1, hhead: __field2, hcnt: __field3 } => ht { hkeys: Clone::clone(__field0), hnxt: Clone::clone(__field1), hhead: Clone::clone(__field2), hcnt: Clone::clone(__field3) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum relkind {
  IsA,
  HasA,
}

pub type pstr = rocq_string::RocqString;

pub type char63 = Int63;

// Rocq: Isahasa.isahasa_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Isahasa.isahasa_implem.hloop
// Variant: uncurried
pub fn hloop_1(s: rocq_string::RocqString, len: Int63, i: Int63, h: Int63) -> Int63 {
  hloop(s, len, i, h, ())
}

// Rocq: Isahasa.isahasa_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(s: rocq_string::RocqString, len: Int63, i: Int63, h: Int63, _H: ()) -> Int63 {
  let tmp = i < len;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = h * int63!(31);
      let s_clone = Clone::clone(&s);
      hloop(s, len, tmp_1, tmp_2 + get(s_clone, i), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      h
    },
  }
}

// Rocq: Isahasa.isahasa_implem.hash
pub fn hash(s: rocq_string::RocqString) -> Int63 {
  let s_clone = Clone::clone(&s);
  let len = length(s_clone);
  hloop_1(s, len, int63!(0), int63!(0)) & int63!(1023)
}

// Rocq: Isahasa.isahasa_implem.hhead
pub fn hhead(h: Rc<ht>) -> Array<Int63> {
  let h_hhead_clone = Clone::clone(&h.hhead);
  std::mem::drop(h);
  h_hhead_clone
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> std::cmp::Ordering {
  let tmp = v0.compare(&v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Isahasa.isahasa_implem.walk
// Variant: uncurried
pub fn walk_1(s: rocq_string::RocqString, keys: Array<rocq_string::RocqString>, nxt: Array<Int63>, p: Int63) -> Int63 {
  walk(s, keys, nxt, p, ())
}

// Rocq: Isahasa.isahasa_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(s: rocq_string::RocqString, keys: Array<rocq_string::RocqString>, nxt: Array<Int63>, p: Int63, _H: ()) -> Int63 {
  let tmp = p == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(s);
      std::mem::drop(keys);
      std::mem::drop(nxt);
      int63!(0)
    },
    sumbool::right => {
      let tmp_1 = p - int63!(1);
      let keys_ref = &keys;
      let tmp_2 = keys_ref.get_cloned(tmp_1);
      let s_clone = Clone::clone(&s);
      match compare(tmp_2, s_clone) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(s);
          std::mem::drop(nxt);
          std::mem::drop(keys);
          p
        },
        std::cmp::Ordering::Less => {
          let q = nxt.get_cloned(p - int63!(1));
          let tmp_3 = q < p;
          match bdec(tmp_3) {
            sumbool::left => {
              walk(s, keys, nxt, q, ())
            },
            sumbool::right => {
              std::mem::drop(s);
              std::mem::drop(nxt);
              std::mem::drop(keys);
              int63!(0)
            },
          }
        },
        std::cmp::Ordering::Greater => {
          let q = nxt.get_cloned(p - int63!(1));
          let tmp_4 = q < p;
          match bdec(tmp_4) {
            sumbool::left => {
              walk(s, keys, nxt, q, ())
            },
            sumbool::right => {
              std::mem::drop(s);
              std::mem::drop(nxt);
              std::mem::drop(keys);
              int63!(0)
            },
          }
        },
      }
    },
  }
}

// Rocq: Isahasa.isahasa_implem.hkeys
pub fn hkeys(h: Rc<ht>) -> Array<rocq_string::RocqString> {
  let h_hkeys_clone = Clone::clone(&h.hkeys);
  std::mem::drop(h);
  h_hkeys_clone
}

// Rocq: Isahasa.isahasa_implem.hnxt
pub fn hnxt(h: Rc<ht>) -> Array<Int63> {
  let h_hnxt_clone = Clone::clone(&h.hnxt);
  std::mem::drop(h);
  h_hnxt_clone
}

// Rocq: Isahasa.isahasa_implem.hcnt
// Variant: borrowed
pub fn hcnt(h: &Rc<ht>) -> Int63 {
  let tmp = h;
  Clone::clone(&tmp.hcnt)
}

// Rocq: Isahasa.isahasa_implem.intern
// Variant: uncurried
pub fn intern(st: Rc<ht>, s: rocq_string::RocqString) -> (Rc<ht>, Int63) {
  let s_clone = Clone::clone(&s);
  let b_1 = hash(s_clone);
  let st_clone = Rc::clone(&st);
  let tmp = hhead(st_clone);
  let hb = tmp.get_cloned(b_1);
  let st_clone_1 = Rc::clone(&st);
  let tmp_1 = hkeys(st_clone_1);
  let st_clone_2 = Rc::clone(&st);
  let tmp_2 = hnxt(st_clone_2);
  let s_clone_1 = Clone::clone(&s);
  let p = walk_1(s_clone_1, tmp_1, tmp_2, hb);
  if p == int63!(0) {
    std::mem::drop(tmp);
    let c = hcnt(&st);
    let st_clone_3 = Rc::clone(&st);
    let tmp_3 = hkeys(st_clone_3).set(c, s);
    let st_clone_4 = Rc::clone(&st);
    (Rc::new(ht { hkeys: tmp_3, hnxt: hnxt(st_clone_4).set(c, hb), hhead: hhead(st).set(b_1, c + int63!(1)), hcnt: c + int63!(1) }), c)
  } else {
    std::mem::drop(s);
    std::mem::drop(tmp);
    (st, p - int63!(1))
  }
}

// Rocq: Isahasa.isahasa_implem.iloop
// Variant: uncurried
pub fn iloop_1(xsrc: Array<rocq_string::RocqString>, xdst: Array<rocq_string::RocqString>, n: Int63, i: Int63, st: Rc<ht>, ia: Array<Int63>, ib: Array<Int63>) -> ((Rc<ht>, Array<Int63>), Array<Int63>) {
  iloop(xsrc, xdst, n, i, st, ia, ib, ())
}

// Rocq: Isahasa.isahasa_implem.iloop (local: iloop)
// Variant: uncurried, lifted
pub fn iloop(xsrc: Array<rocq_string::RocqString>, xdst: Array<rocq_string::RocqString>, n: Int63, i: Int63, st: Rc<ht>, ia: Array<Int63>, ib: Array<Int63>, _H: ()) -> ((Rc<ht>, Array<Int63>), Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let xsrc_ref = &xsrc;
      let tmp_1 = xsrc_ref.get_cloned(i);
      let tmp_2 = intern(st, tmp_1);
      match tmp_2 {
        (v30, v32) => {
          let xdst_ref = &xdst;
          let tmp_3 = xdst_ref.get_cloned(i);
          let tmp_4 = intern(v30, tmp_3);
          match tmp_4 {
            (v45, v47) => {
              iloop(xsrc, xdst, n, i + int63!(1), v45, ia.set(i, v32), ib.set(i, v47), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xsrc);
      std::mem::drop(xdst);
      ((st, ia), ib)
    },
  }
}

// Rocq: Isahasa.isahasa_implem.setbit
// Variant: uncurried
pub fn setbit(T: Array<Int63>, W: Int63, u: Int63, v: Int63) -> Array<Int63> {
  let i = u * W + v / int63!(63);
  let tmp = T.get_cloned(i);
  T.set(i, tmp | int63!(1) << v % int63!(63))
}

// Rocq: Isahasa.isahasa_implem.eloop
// Variant: uncurried
pub fn eloop_1(xrs: Array<relkind>, ia: Array<Int63>, ib: Array<Int63>, k: Int63, W: Int63, n: Int63, l: Int63, T: Array<Int63>) -> Array<Int63> {
  eloop(xrs, ia, ib, k, W, n, l, T, ())
}

// Rocq: Isahasa.isahasa_implem.eloop (local: eloop)
// Variant: uncurried, lifted
pub fn eloop(xrs: Array<relkind>, ia: Array<Int63>, ib: Array<Int63>, k: Int63, W: Int63, n: Int63, l: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = l < n;
  match bdec(tmp) {
    sumbool::left => {
      let a_1 = ia.get_cloned(l);
      let b_1 = ib.get_cloned(l);
      let tmp_1 = xrs.get_cloned(l);
      let T_ = match tmp_1 {
        relkind::IsA => {
          let tmp_2 = setbit(T, W, a_1, b_1);
          setbit(tmp_2, W, a_1 + k, b_1 + k)
        },
        relkind::HasA => {
          let tmp_3 = setbit(T, W, a_1, b_1 + k);
          setbit(tmp_3, W, a_1 + k, b_1 + k)
        },
      };
      eloop(xrs, ia, ib, k, W, n, l + int63!(1), T_, ())
    },
    sumbool::right => {
      std::mem::drop(xrs);
      std::mem::drop(ia);
      std::mem::drop(ib);
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.getbit
// Variant: uncurried
pub fn getbit(T: Array<Int63>, W: Int63, u: Int63, v: Int63) -> bool {
  let tmp = T.get_cloned(u * W + v / int63!(63));
  std::mem::drop(T);
  tmp >> v % int63!(63) & int63!(1) == int63!(1)
}

// Rocq: Isahasa.isahasa_implem.rowor
// Variant: uncurried
pub fn rowor_1(T: Array<Int63>, W: Int63, u: Int63, w: Int63, j: Int63) -> Array<Int63> {
  rowor(T, W, u, w, j, ())
}

// Rocq: Isahasa.isahasa_implem.rowor (local: rowor)
// Variant: uncurried, lifted
pub fn rowor(T: Array<Int63>, W: Int63, u: Int63, w: Int63, j: Int63, _H: ()) -> Array<Int63> {
  let tmp = j < W;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = u * W + j;
      let tmp_2 = T.get_cloned(u * W + j);
      let tmp_3 = T.get_cloned(w * W + j);
      rowor(T.set(tmp_1, tmp_2 | tmp_3), W, u, w, j + int63!(1), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fw_inner
// Variant: uncurried
pub fn fw_inner_1(T: Array<Int63>, N: Int63, W: Int63, w: Int63, u: Int63) -> Array<Int63> {
  fw_inner(T, N, W, w, u, ())
}

// Rocq: Isahasa.isahasa_implem.fw_inner (local: fw_inner)
// Variant: uncurried, lifted
pub fn fw_inner(T: Array<Int63>, N: Int63, W: Int63, w: Int63, u: Int63, _H: ()) -> Array<Int63> {
  let tmp = u < N;
  match bdec(tmp) {
    sumbool::left => {
      let T_clone = Clone::clone(&T);
      let tmp_1 = if getbit(T_clone, W, u, w) {
        rowor_1(T, W, u, w, int63!(0))
      } else {
        T
      };
      fw_inner(tmp_1, N, W, w, u + int63!(1), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fw_outer
// Variant: uncurried
pub fn fw_outer_1(T: Array<Int63>, N: Int63, W: Int63, w: Int63) -> Array<Int63> {
  fw_outer(T, N, W, w, ())
}

// Rocq: Isahasa.isahasa_implem.fw_outer (local: fw_outer)
// Variant: uncurried, lifted
pub fn fw_outer(T: Array<Int63>, N: Int63, W: Int63, w: Int63, _H: ()) -> Array<Int63> {
  let tmp = w < N;
  match bdec(tmp) {
    sumbool::left => {
      fw_outer(fw_inner_1(T, N, W, w, int63!(0)), N, W, w + int63!(1), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fill
// Variant: uncurried
pub fn fill_1(f: Rc<dyn Fn(Int63) -> bool>, m: Int63, j: Int63, out: Array<bool>) -> Array<bool> {
  fill(f, m, j, out, ())
}

// Rocq: Isahasa.isahasa_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(f: Rc<dyn Fn(Int63) -> bool>, m: Int63, j: Int63, out: Array<bool>, _H: ()) -> Array<bool> {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63) -> bool> = &f;
      let tmp_2 = f_ref(j);
      fill(f, m, tmp_1, out.set(j, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(f);
      out
    },
  }
}

// Rocq: Isahasa.isahasa_implem.lookup
// Variant: uncurried
pub fn lookup(st: Rc<ht>, s: rocq_string::RocqString) -> Int63 {
  let st_clone = Rc::clone(&st);
  let tmp = hhead(st_clone);
  let s_clone = Clone::clone(&s);
  let p = tmp.get_cloned(hash(s_clone));
  std::mem::drop(tmp);
  let st_clone_1 = Rc::clone(&st);
  walk_1(s, hkeys(st_clone_1), hnxt(st), p)
}

// Rocq: Isahasa.isahasa_implem.answer
// Variant: uncurried
pub fn answer(st: Rc<ht>, T: Array<Int63>, W: Int63, k: Int63, s1: rocq_string::RocqString, s2: rocq_string::RocqString, r: relkind) -> bool {
  let st_clone = Rc::clone(&st);
  let a_1 = lookup(st_clone, s1);
  let b_1 = lookup(st, s2);
  if a_1 == int63!(0) {
    std::mem::drop(T);
    false
  } else {
    if b_1 == int63!(0) {
      std::mem::drop(T);
      false
    } else {
      match r {
        relkind::IsA => {
          if a_1 == b_1 {
            std::mem::drop(T);
            true
          } else {
            getbit(T, W, a_1 - int63!(1), b_1 - int63!(1))
          }
        },
        relkind::HasA => {
          getbit(T, W, a_1 - int63!(1), b_1 - int63!(1) + k)
        },
      }
    }
  }
}

// Rocq: Isahasa.isahasa_implem.isahasa_impl
// Variant: uncurried
pub fn isahasa_impl(xsrc: Array<rocq_string::RocqString>, xrs: Array<relkind>, xdst: Array<rocq_string::RocqString>, xqsrc: Array<rocq_string::RocqString>, xqrs: Array<relkind>, xqdst: Array<rocq_string::RocqString>) -> Array<bool> {
  let n = xsrc.length();
  let cap = n + n;
  let tmp = rocq_string::StringPayload::from_static(b"");
  let st0 = Rc::new(ht { hkeys: Array::<rocq_string::RocqString>::make(cap, rocq_string::RocqString::from_payload(tmp)), hnxt: Array::<Int63>::make(cap, int63!(0)), hhead: Array::<Int63>::make(int63!(1024), int63!(0)), hcnt: int63!(0) });
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let tmp_3 = iloop_1(xsrc, xdst, n, int63!(0), st0, tmp_1, tmp_2);
  match tmp_3 {
    (v83, v85) => {
      match v83 {
        (v88, v90) => {
          let ia = &v88;
          let k = hcnt(ia);
          let N = k + k;
          let W = (N + int63!(62)) / int63!(63);
          let tmp_4 = N * W;
          let T0 = eloop_1(xrs, v90, v85, k, W, n, int63!(0), Array::<Int63>::make(tmp_4, int63!(0)));
          let T = fw_outer_1(T0, N, W, int63!(0));
          let m = xqsrc.length();
          let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
            let __anf_capture_181 = xqsrc;
            let __anf_capture_187 = v88;
            let __anf_capture_191 = W;
            let __anf_capture_193 = k;
            move |j: Int63| -> bool {
              let xqsrc = &__anf_capture_181;
              let xqdst = &xqdst;
              let xqrs = &xqrs;
              let ia = &__anf_capture_187;
              let T = &T;
              let W = &__anf_capture_191;
              let k = &__anf_capture_193;
              let tmp_5 = xqsrc.get_cloned(j);
              let tmp_6 = xqdst.get_cloned(j);
              let tmp_7 = xqrs.get_cloned(j);
              let ia_clone = Rc::clone(ia);
              let T_clone = Clone::clone(T);
              let W_clone = Clone::clone(W);
              let k_clone = Clone::clone(k);
              answer(ia_clone, T_clone, W_clone, k_clone, tmp_5, tmp_6, tmp_7)
            }
          });
          let tmp_8 = Array::<bool>::make(m, false);
          fill_1(callback, m, int63!(0), tmp_8)
        },
      }
    },
  }
}
