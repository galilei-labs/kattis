#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub struct ht {
  pub hkeys: Rc<Array<Rc<rocq_string::RocqString>>>,
  pub hnxt: Rc<Array<u64>>,
  pub hhead: Rc<Array<u64>>,
  pub hcnt: u64,
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

pub type pstr = Rc<rocq_string::RocqString>;

pub type char63 = u64;

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Isahasa.isahasa_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Isahasa.isahasa_implem.hloop
// Variant: uncurried
pub fn hloop_1(s: Rc<rocq_string::RocqString>, len: u64, i: u64, h: u64) -> u64 {
  hloop(s, len, i, h, ())
}

// Rocq: Isahasa.isahasa_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(s: Rc<rocq_string::RocqString>, len: u64, i: u64, h: u64, _H: ()) -> u64 {
  let tmp = ltb(i, len);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = mul(h, 31u64);
      let s_clone = Rc::clone(&s);
      hloop(s, len, tmp_1, add(tmp_2, get(s_clone, i)), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      h
    },
  }
}

// Rocq: Isahasa.isahasa_implem.hash
pub fn hash(s: Rc<rocq_string::RocqString>) -> u64 {
  let s_clone = Rc::clone(&s);
  let len = length(s_clone);
  land(hloop_1(s, len, 0u64, 0u64), 1023u64)
}

// Rocq: Isahasa.isahasa_implem.hhead
pub fn hhead(h: Rc<ht>) -> Rc<Array<u64>> {
  let h_hhead_clone = Rc::clone(&h.hhead);
  std::mem::drop(h);
  h_hhead_clone
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let tmp = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Isahasa.isahasa_implem.walk
// Variant: uncurried
pub fn walk_1(s: Rc<rocq_string::RocqString>, keys: Rc<Array<Rc<rocq_string::RocqString>>>, nxt: Rc<Array<u64>>, p: u64) -> u64 {
  walk(s, keys, nxt, p, ())
}

// Rocq: Isahasa.isahasa_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(s: Rc<rocq_string::RocqString>, keys: Rc<Array<Rc<rocq_string::RocqString>>>, nxt: Rc<Array<u64>>, p: u64, _H: ()) -> u64 {
  let tmp = eqb(p, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(s);
      std::mem::drop(keys);
      std::mem::drop(nxt);
      0u64
    },
    sumbool::right => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&keys, sub(p, 1u64));
      let s_clone = Rc::clone(&s);
      match compare(tmp_1, s_clone) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(s);
          std::mem::drop(nxt);
          std::mem::drop(keys);
          p
        },
        std::cmp::Ordering::Less => {
          let q = rocq_array::get::<u64>(&nxt, sub(p, 1u64));
          let tmp_2 = ltb(q, p);
          match bdec(tmp_2) {
            sumbool::left => {
              walk(s, keys, nxt, q, ())
            },
            sumbool::right => {
              std::mem::drop(s);
              std::mem::drop(nxt);
              std::mem::drop(keys);
              0u64
            },
          }
        },
        std::cmp::Ordering::Greater => {
          let q = rocq_array::get::<u64>(&nxt, sub(p, 1u64));
          let tmp_3 = ltb(q, p);
          match bdec(tmp_3) {
            sumbool::left => {
              walk(s, keys, nxt, q, ())
            },
            sumbool::right => {
              std::mem::drop(s);
              std::mem::drop(nxt);
              std::mem::drop(keys);
              0u64
            },
          }
        },
      }
    },
  }
}

// Rocq: Isahasa.isahasa_implem.hkeys
pub fn hkeys(h: Rc<ht>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let h_hkeys_clone = Rc::clone(&h.hkeys);
  std::mem::drop(h);
  h_hkeys_clone
}

// Rocq: Isahasa.isahasa_implem.hnxt
pub fn hnxt(h: Rc<ht>) -> Rc<Array<u64>> {
  let h_hnxt_clone = Rc::clone(&h.hnxt);
  std::mem::drop(h);
  h_hnxt_clone
}

// Rocq: Isahasa.isahasa_implem.hcnt
// Variant: borrowed
pub fn hcnt(h: &Rc<ht>) -> u64 {
  let tmp = h;
  Clone::clone(&tmp.hcnt)
}

// Rocq: Isahasa.isahasa_implem.intern
// Variant: uncurried
pub fn intern(st: Rc<ht>, s: Rc<rocq_string::RocqString>) -> (Rc<ht>, u64) {
  let s_clone = Rc::clone(&s);
  let b = hash(s_clone);
  let st_clone = Rc::clone(&st);
  let tmp = hhead(st_clone);
  let hb = rocq_array::get::<u64>(&tmp, b);
  let st_clone_1 = Rc::clone(&st);
  let tmp_1 = hkeys(st_clone_1);
  let st_clone_2 = Rc::clone(&st);
  let tmp_2 = hnxt(st_clone_2);
  let s_clone_1 = Rc::clone(&s);
  let p = walk_1(s_clone_1, tmp_1, tmp_2, hb);
  if eqb(p, 0u64) {
    std::mem::drop(tmp);
    let c = hcnt(&st);
    let st_clone_3 = Rc::clone(&st);
    let tmp_3 = hkeys(st_clone_3);
    let tmp_4 = rocq_array::set::<Rc<rocq_string::RocqString>>(tmp_3, c, s);
    let st_clone_4 = Rc::clone(&st);
    let tmp_5 = hnxt(st_clone_4);
    let tmp_6 = rocq_array::set::<u64>(tmp_5, c, hb);
    let tmp_7 = hhead(st);
    let tmp_8 = rocq_array::set::<u64>(tmp_7, b, add(c, 1u64));
    (Rc::new(ht { hkeys: tmp_4, hnxt: tmp_6, hhead: tmp_8, hcnt: add(c, 1u64) }), c)
  } else {
    std::mem::drop(s);
    std::mem::drop(tmp);
    (st, sub(p, 1u64))
  }
}

// Rocq: Isahasa.isahasa_implem.iloop
// Variant: uncurried
pub fn iloop_1(xsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xdst: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, st: Rc<ht>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>) -> ((Rc<ht>, Rc<Array<u64>>), Rc<Array<u64>>) {
  iloop(xsrc, xdst, n, i, st, ia, ib, ())
}

// Rocq: Isahasa.isahasa_implem.iloop (local: iloop)
// Variant: uncurried, lifted
pub fn iloop(xsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xdst: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, st: Rc<ht>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, _H: ()) -> ((Rc<ht>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xsrc, i);
      let tmp_2 = intern(st, tmp_1);
      match tmp_2 {
        (v30, v32) => {
          let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xdst, i);
          let tmp_4 = intern(v30, tmp_3);
          match tmp_4 {
            (v45, v47) => {
              let tmp_5 = add(i, 1u64);
              let tmp_6 = rocq_array::set::<u64>(ia, i, v32);
              let tmp_7 = rocq_array::set::<u64>(ib, i, v47);
              iloop(xsrc, xdst, n, tmp_5, v45, tmp_6, tmp_7, ())
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lor
// Variant: uncurried
pub fn lor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lor(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Isahasa.isahasa_implem.setbit
// Variant: uncurried
pub fn setbit(T: Rc<Array<u64>>, W: u64, u: u64, v: u64) -> Rc<Array<u64>> {
  let i = add(mul(u, W), div(v, 63u64));
  let tmp = rocq_array::get::<u64>(&T, i);
  rocq_array::set::<u64>(T, i, lor(tmp, lsl(1u64, mod_(v, 63u64))))
}

// Rocq: Isahasa.isahasa_implem.eloop
// Variant: uncurried
pub fn eloop_1(xrs: Rc<Array<relkind>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, k: u64, W: u64, n: u64, l: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  eloop(xrs, ia, ib, k, W, n, l, T, ())
}

// Rocq: Isahasa.isahasa_implem.eloop (local: eloop)
// Variant: uncurried, lifted
pub fn eloop(xrs: Rc<Array<relkind>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, k: u64, W: u64, n: u64, l: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(l, n);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&ia, l);
      let b = rocq_array::get::<u64>(&ib, l);
      let tmp_1 = rocq_array::get::<relkind>(&xrs, l);
      let T_ = match tmp_1 {
        relkind::IsA => {
          let tmp_2 = setbit(T, W, a, b);
          setbit(tmp_2, W, add(a, k), add(b, k))
        },
        relkind::HasA => {
          let tmp_3 = setbit(T, W, a, add(b, k));
          setbit(tmp_3, W, add(a, k), add(b, k))
        },
      };
      eloop(xrs, ia, ib, k, W, n, add(l, 1u64), T_, ())
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
pub fn getbit(T: Rc<Array<u64>>, W: u64, u: u64, v: u64) -> bool {
  let tmp = rocq_array::get::<u64>(&T, add(mul(u, W), div(v, 63u64)));
  std::mem::drop(T);
  eqb(land(lsr(tmp, mod_(v, 63u64)), 1u64), 1u64)
}

// Rocq: Isahasa.isahasa_implem.rowor
// Variant: uncurried
pub fn rowor_1(T: Rc<Array<u64>>, W: u64, u: u64, w: u64, j: u64) -> Rc<Array<u64>> {
  rowor(T, W, u, w, j, ())
}

// Rocq: Isahasa.isahasa_implem.rowor (local: rowor)
// Variant: uncurried, lifted
pub fn rowor(T: Rc<Array<u64>>, W: u64, u: u64, w: u64, j: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, W);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(mul(u, W), j);
      let tmp_2 = rocq_array::get::<u64>(&T, add(mul(u, W), j));
      let tmp_3 = rocq_array::get::<u64>(&T, add(mul(w, W), j));
      let tmp_4 = rocq_array::set::<u64>(T, tmp_1, lor(tmp_2, tmp_3));
      rowor(tmp_4, W, u, w, add(j, 1u64), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fw_inner
// Variant: uncurried
pub fn fw_inner_1(T: Rc<Array<u64>>, N: u64, W: u64, w: u64, u: u64) -> Rc<Array<u64>> {
  fw_inner(T, N, W, w, u, ())
}

// Rocq: Isahasa.isahasa_implem.fw_inner (local: fw_inner)
// Variant: uncurried, lifted
pub fn fw_inner(T: Rc<Array<u64>>, N: u64, W: u64, w: u64, u: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(u, N);
  match bdec(tmp) {
    sumbool::left => {
      let T_clone = Rc::clone(&T);
      let tmp_1 = if getbit(T_clone, W, u, w) {
        rowor_1(T, W, u, w, 0u64)
      } else {
        T
      };
      fw_inner(tmp_1, N, W, w, add(u, 1u64), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fw_outer
// Variant: uncurried
pub fn fw_outer_1(T: Rc<Array<u64>>, N: u64, W: u64, w: u64) -> Rc<Array<u64>> {
  fw_outer(T, N, W, w, ())
}

// Rocq: Isahasa.isahasa_implem.fw_outer (local: fw_outer)
// Variant: uncurried, lifted
pub fn fw_outer(T: Rc<Array<u64>>, N: u64, W: u64, w: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(w, N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = fw_inner_1(T, N, W, w, 0u64);
      fw_outer(tmp_1, N, W, add(w, 1u64), ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Isahasa.isahasa_implem.fill
// Variant: uncurried
pub fn fill_1(f: Rc<dyn Fn(u64) -> bool>, m: u64, j: u64, out: Rc<Array<bool>>) -> Rc<Array<bool>> {
  fill(f, m, j, out, ())
}

// Rocq: Isahasa.isahasa_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(f: Rc<dyn Fn(u64) -> bool>, m: u64, j: u64, out: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let f_ref: &Rc<dyn Fn(u64) -> bool> = &f;
      let tmp_2 = f_ref(j);
      let tmp_3 = rocq_array::set::<bool>(out, j, tmp_2);
      fill(f, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      out
    },
  }
}

// Rocq: Isahasa.isahasa_implem.lookup
// Variant: uncurried
pub fn lookup(st: Rc<ht>, s: Rc<rocq_string::RocqString>) -> u64 {
  let st_clone = Rc::clone(&st);
  let tmp = hhead(st_clone);
  let s_clone = Rc::clone(&s);
  let p = rocq_array::get::<u64>(&tmp, hash(s_clone));
  std::mem::drop(tmp);
  let st_clone_1 = Rc::clone(&st);
  let tmp_1 = hkeys(st_clone_1);
  let tmp_2 = hnxt(st);
  walk_1(s, tmp_1, tmp_2, p)
}

// Rocq: Isahasa.isahasa_implem.answer
// Variant: uncurried
pub fn answer(st: Rc<ht>, T: Rc<Array<u64>>, W: u64, k: u64, s1: Rc<rocq_string::RocqString>, s2: Rc<rocq_string::RocqString>, r: relkind) -> bool {
  let st_clone = Rc::clone(&st);
  let a = lookup(st_clone, s1);
  let b = lookup(st, s2);
  if eqb(a, 0u64) {
    std::mem::drop(T);
    false
  } else {
    if eqb(b, 0u64) {
      std::mem::drop(T);
      false
    } else {
      match r {
        relkind::IsA => {
          if eqb(a, b) {
            std::mem::drop(T);
            true
          } else {
            getbit(T, W, sub(a, 1u64), sub(b, 1u64))
          }
        },
        relkind::HasA => {
          getbit(T, W, sub(a, 1u64), add(sub(b, 1u64), k))
        },
      }
    }
  }
}

// Rocq: Isahasa.isahasa_implem.isahasa_impl
// Variant: uncurried
pub fn isahasa_impl(xsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xrs: Rc<Array<relkind>>, xdst: Rc<Array<Rc<rocq_string::RocqString>>>, xqsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xqrs: Rc<Array<relkind>>, xqdst: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>> {
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&xsrc);
  let cap = add(n, n);
  let tmp = rocq_string::RocqString::from_bytes(vec![]);
  let tmp_1 = Rc::new(tmp);
  let tmp_2 = rocq_array::make::<Rc<rocq_string::RocqString>>(cap, tmp_1);
  let tmp_3 = rocq_array::make::<u64>(cap, 0u64);
  let tmp_4 = rocq_array::make::<u64>(1024u64, 0u64);
  let st0 = Rc::new(ht { hkeys: tmp_2, hnxt: tmp_3, hhead: tmp_4, hcnt: 0u64 });
  let tmp_5 = rocq_array::make::<u64>(n, 0u64);
  let tmp_6 = rocq_array::make::<u64>(n, 0u64);
  let tmp_7 = iloop_1(xsrc, xdst, n, 0u64, st0, tmp_5, tmp_6);
  match tmp_7 {
    (v84, v86) => {
      match v84 {
        (v89, v91) => {
          let ia = &v89;
          let k = hcnt(ia);
          let N = add(k, k);
          let W = div(add(N, 62u64), 63u64);
          let tmp_8 = rocq_array::make::<u64>(mul(N, W), 0u64);
          let T0 = eloop_1(xrs, v91, v86, k, W, n, 0u64, tmp_8);
          let T = fw_outer_1(T0, N, W, 0u64);
          let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&xqsrc);
          let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
            let __anf_capture_182 = xqsrc;
            let __anf_capture_188 = v89;
            let __anf_capture_192 = W;
            let __anf_capture_194 = k;
            move |j: u64| -> bool {
              let xqsrc = &__anf_capture_182;
              let xqdst = &xqdst;
              let xqrs = &xqrs;
              let ia = &__anf_capture_188;
              let T = &T;
              let W = &__anf_capture_192;
              let k = &__anf_capture_194;
              let tmp_9 = rocq_array::get::<Rc<rocq_string::RocqString>>(xqsrc, j);
              let tmp_10 = rocq_array::get::<Rc<rocq_string::RocqString>>(xqdst, j);
              let tmp_11 = rocq_array::get::<relkind>(xqrs, j);
              let ia_clone = Rc::clone(ia);
              let T_clone = Rc::clone(T);
              let W_clone = Clone::clone(W);
              let k_clone = Clone::clone(k);
              answer(ia_clone, T_clone, W_clone, k_clone, tmp_9, tmp_10, tmp_11)
            }
          });
          let tmp_12 = rocq_array::make::<bool>(m, false);
          fill_1(callback, m, 0u64, tmp_12)
        },
      }
    },
  }
}

mod __rocq_reuse {
//! Empty allocation ownership for OwnedANF reset and exact-type rebuilding.
use std::mem::MaybeUninit;
use std::rc::Rc;

/// Move-only and opaque: storage has no initialized `T` and cannot be inspected.
pub struct Token<T> {
    _storage: Option<Rc<MaybeUninit<T>>>,
}

/// Consume an owner. The caller supplies the IR-approved shallow field copy;
/// This may use a compiler-generated structural Clone implementation, but does
/// not authorize arbitrary host clone behavior merely because T implements Clone.
#[inline]
pub fn reset<T>(mut owner: Rc<T>, duplicate: impl FnOnce(&T) -> T) -> (T, Token<T>) {
    if let Some(payload) = Rc::get_mut(&mut owner) {
        // SAFETY: get_mut establishes exclusive access (including no Weak
        // owners). T and MaybeUninit<T> have identical size/alignment, so their
        // Rc allocation layouts agree. After read, no potentially panicking
        // user code runs before ownership becomes Rc<MaybeUninit<T>>. There is
        // exactly one from_raw for into_raw, and the original Rc<T> is consumed.
        // The token never reads or drops the moved T; dropping it only frees
        // the allocation. The payload returned here owns T's fields once.
        unsafe {
            let value = std::ptr::read(payload);
            let raw = Rc::into_raw(owner).cast::<MaybeUninit<T>>();
            let storage = Rc::from_raw(raw);
            (value, Token { _storage: Some(storage) })
        }
    } else {
        let value = duplicate(&owner);
        drop(owner);
        (value, Token { _storage: None })
    }
}

/// Consume reserved storage and a fully evaluated payload. Empty tokens allocate.
#[inline]
pub fn rebuild<T>(token: Token<T>, payload: T) -> Rc<T> {
    match token._storage {
        None => Rc::new(payload),
        Some(mut storage) => {
            // The opaque, non-Clone token owns the only strong reference and
            // has no weak references. Check before initializing, so a panic
            // cannot leave an initialized T hidden inside MaybeUninit<T>.
            Rc::get_mut(&mut storage).expect("exclusive reuse token").write(payload);
            // SAFETY: the payload is now fully initialized; no panicking code
            // lies between initialization and this ownership conversion. The
            // reset conversion established identical allocation layouts.
            unsafe { Rc::from_raw(Rc::into_raw(storage).cast::<T>()) }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    struct Probe(Rc<Cell<usize>>);
    impl Drop for Probe {
        fn drop(&mut self) { self.0.set(self.0.get() + 1); }
    }

    #[test]
    fn rebuilding_preserves_address_and_drops_only_new_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner);
        let (old, token) = reset(owner, |_| panic!("unique"));
        drop(old);
        assert_eq!(drops.get(), 1);
        let new = rebuild(token, Probe(drops.clone()));
        assert_eq!(Rc::as_ptr(&new), address);
        assert_eq!(drops.get(), 1);
        drop(new);
        assert_eq!(drops.get(), 2);
    }

    #[test]
    fn empty_token_allocates_and_preserves_old_alias() {
        let old = Rc::new(7);
        let alias = old.clone();
        let (_, token) = reset(old, |x| *x);
        let new = rebuild(token, 19);
        assert_eq!(*alias, 7);
        assert_eq!(*new, 19);
        assert!(!Rc::ptr_eq(&alias, &new));
    }

    #[test]
    fn unique_token_drop_does_not_drop_payload() {
        let drops = Rc::new(Cell::new(0));
        let owner = Rc::new(Probe(drops.clone()));
        let address = Rc::as_ptr(&owner).cast::<MaybeUninit<Probe>>();
        let (payload, token) = reset(owner, |_| panic!("unique path duplicated"));
        assert_eq!(Rc::as_ptr(token._storage.as_ref().unwrap()), address);
        drop(token);
        assert_eq!(drops.get(), 0);
        drop(payload);
        assert_eq!(drops.get(), 1);
    }

    #[test]
    fn shared_fallback_preserves_aliases() {
        let field = Rc::new(7);
        let owner = Rc::new((field.clone(), 9));
        let alias = owner.clone();
        let (payload, token) = reset(owner, |x| (x.0.clone(), x.1));
        assert!(token._storage.is_none());
        assert!(Rc::ptr_eq(&payload.0, &alias.0));
        assert_eq!(Rc::strong_count(&field), 3);
        drop(token);
        drop(payload);
        assert_eq!(alias.1, 9);
        drop(alias);
        assert_eq!(Rc::strong_count(&field), 1);
    }

    #[test]
    fn weak_pointer_forces_fallback() {
        let owner = Rc::new(17);
        let weak = Rc::downgrade(&owner);
        let (payload, token) = reset(owner, |x| *x);
        assert_eq!(payload, 17);
        assert!(token._storage.is_none());
        assert!(weak.upgrade().is_none());
    }

    #[test]
    fn panicking_fallback_releases_consumed_handle() {
        let owner = Rc::new(17);
        let alias = owner.clone();
        let result = std::panic::catch_unwind(|| reset(owner, |_| panic!("copy failed")));
        assert!(result.is_err());
        assert_eq!(Rc::strong_count(&alias), 1);
        assert_eq!(*alias, 17);
    }

    #[test]
    fn zero_sized_payload() {
        let (payload, token) = reset(Rc::new(()), |_| panic!("unique"));
        drop(token);
        assert_eq!(payload, ());
    }
}

}
