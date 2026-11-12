// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Isahasa.isahasa_implem.isahasa
// Variant: uncurried
pub fn isahasa() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>> = isahasa_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> = Rc::new(v0);
  v1
}

// Rocq: Isahasa.isahasa_implem.isahasa
pub fn isahasa_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>> = isahasa_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.make
// Variant: uncurried
pub fn make(v0: u64, v1: u64) -> Rc<rocq_string::RocqString> {
  let v8 = rocq_string::make(v0, v1);
  v8
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
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Isahasa.isahasa_implem.hloop
// Variant: uncurried
pub fn hloop_1(s: Rc<rocq_string::RocqString>, len: u64, i: u64, h: u64) -> u64 {
  hloop(s, len, i, h, ())
}

// Rocq: Isahasa.isahasa_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(s: Rc<rocq_string::RocqString>, len: u64, i: u64, h: u64, _H: ()) -> u64 {
  let v12 = ltb(i, len);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v32 = mul(h, 31u64);
      let v36 = Rc::clone(&s);
      hloop(s, len, v23, add(v32, get(v36, i)), ())
    },
    sumbool::right => {
      std::mem::drop(s);
      h
    },
  }
}

// Rocq: Isahasa.isahasa_implem.hash
pub fn hash(s: Rc<rocq_string::RocqString>) -> u64 {
  let v4 = Rc::clone(&s);
  let len = length(v4);
  land(hloop_1(s, len, 0u64, 0u64), 1023u64)
}

// Rocq: Isahasa.isahasa_implem.hhead
pub fn hhead(h: Rc<ht>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&h).hhead));
  std::mem::drop(h);
  v3
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let v4 = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  v4
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
  let v14 = eqb(p, 0u64);
  match bdec(v14) {
    sumbool::left => {
      std::mem::drop(s);
      std::mem::drop(keys);
      std::mem::drop(nxt);
      0u64
    },
    sumbool::right => {
      let v30 = sub(p, 1u64);
      let v31 = &keys;
      let v35 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v31, v30);
      let v39 = Rc::clone(&s);
      match compare(v35, v39) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(s);
          std::mem::drop(nxt);
          std::mem::drop(keys);
          p
        },
        std::cmp::Ordering::Less => {
          let v51 = sub(p, 1u64);
          let v52 = &nxt;
          let q = rocq_array::get::<u64>(&v52, v51);
          let v63 = ltb(q, p);
          match bdec(v63) {
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
          let v97 = sub(p, 1u64);
          let v98 = &nxt;
          let q = rocq_array::get::<u64>(&v98, v97);
          let v109 = ltb(q, p);
          match bdec(v109) {
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
  let v3 = Rc::clone((&(&**&h).hkeys));
  std::mem::drop(h);
  v3
}

// Rocq: Isahasa.isahasa_implem.hnxt
pub fn hnxt(h: Rc<ht>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&h).hnxt));
  std::mem::drop(h);
  v3
}

// Rocq: Isahasa.isahasa_implem.hcnt
// Variant: borrowed
pub fn hcnt(h: &Rc<ht>) -> u64 {
  let v1 = h;
  Clone::clone((&(&**v1).hcnt))
}

// Rocq: Isahasa.isahasa_implem.intern
// Variant: uncurried
pub fn intern(st: Rc<ht>, s: Rc<rocq_string::RocqString>) -> (Rc<ht>, u64) {
  let v5 = Rc::clone(&s);
  let b = hash(v5);
  let v10 = Rc::clone(&st);
  let v11 = hhead(v10);
  let v12 = &v11;
  let hb = rocq_array::get::<u64>(&v12, b);
  let v20 = Rc::clone(&st);
  let v21 = hkeys(v20);
  let v25 = Rc::clone(&st);
  let v26 = hnxt(v25);
  let v29 = Rc::clone(&s);
  let p = walk_1(v29, v21, v26, hb);
  match eqb(p, 0u64) {
    true => {
      std::mem::drop(v11);
      let c = hcnt(&st);
      let v53 = Rc::clone(&st);
      let v55 = hkeys(v53);
      let v61 = rocq_array::set::<Rc<rocq_string::RocqString>>(v55, c, s);
      let v65 = Rc::clone(&st);
      let v67 = hnxt(v65);
      let v73 = rocq_array::set::<u64>(v67, c, hb);
      let v77 = hhead(st);
      let v92 = rocq_array::set::<u64>(v77, b, add(c, 1u64));
      (Rc::new(ht { hkeys: v61, hnxt: v73, hhead: v92, hcnt: add(c, 1u64) }), c)
    },
    false => {
      std::mem::drop(s);
      std::mem::drop(v11);
      (st, sub(p, 1u64))
    },
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
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v20 = &xsrc;
      let v23 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v20, i);
      let v28 = intern(st, v23);
      match v28 {
        (v30, v32) => {
          let v35 = &xdst;
          let v38 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v35, i);
          let v43 = intern(v30, v38);
          match v43 {
            (v45, v47) => {
              let v56 = add(i, 1u64);
              let v63 = rocq_array::set::<u64>(ia, i, v32);
              let v70 = rocq_array::set::<u64>(ib, i, v47);
              iloop(xsrc, xdst, n, v56, v45, v63, v70, ())
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
  let v25 = &T;
  let v28 = rocq_array::get::<u64>(&v25, i);
  rocq_array::set::<u64>(T, i, lor(v28, lsl(1u64, mod_(v, 63u64))))
}

// Rocq: Isahasa.isahasa_implem.eloop
// Variant: uncurried
pub fn eloop_1(xrs: Rc<Array<relkind>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, k: u64, W: u64, n: u64, l: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  eloop(xrs, ia, ib, k, W, n, l, T, ())
}

// Rocq: Isahasa.isahasa_implem.eloop (local: eloop)
// Variant: uncurried, lifted
pub fn eloop(xrs: Rc<Array<relkind>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, k: u64, W: u64, n: u64, l: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(l, n);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &ia;
      let a = rocq_array::get::<u64>(&v20, l);
      let v24 = &ib;
      let b = rocq_array::get::<u64>(&v24, l);
      let v28 = &xrs;
      let v31 = rocq_array::get::<relkind>(&v28, l);
      let T_ = match v31 {
        relkind::IsA => {
          let v43 = setbit(T, W, a, b);
          setbit(v43, W, add(a, k), add(b, k))
        },
        relkind::HasA => {
          let v83 = setbit(T, W, a, add(b, k));
          setbit(v83, W, add(a, k), add(b, k))
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
  let v26 = add(mul(u, W), div(v, 63u64));
  let v27 = &T;
  let v30 = rocq_array::get::<u64>(&v27, v26);
  std::mem::drop(T);
  eqb(land(lsr(v30, mod_(v, 63u64)), 1u64), 1u64)
}

// Rocq: Isahasa.isahasa_implem.rowor
// Variant: uncurried
pub fn rowor_1(T: Rc<Array<u64>>, W: u64, u: u64, w: u64, j: u64) -> Rc<Array<u64>> {
  rowor(T, W, u, w, j, ())
}

// Rocq: Isahasa.isahasa_implem.rowor (local: rowor)
// Variant: uncurried, lifted
pub fn rowor(T: Rc<Array<u64>>, W: u64, u: u64, w: u64, j: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(j, W);
  match bdec(v13) {
    sumbool::left => {
      let v28 = add(mul(u, W), j);
      let v41 = add(mul(u, W), j);
      let v42 = &T;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      let v57 = add(mul(w, W), j);
      let v58 = &T;
      let v61 = rocq_array::get::<u64>(&v58, v57);
      let v73 = rocq_array::set::<u64>(T, v28, lor(v45, v61));
      rowor(v73, W, u, w, add(j, 1u64), ())
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
  let v13 = ltb(u, N);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&T);
      let v28 = match getbit(v20, W, u, w) {
        true => {
          rowor_1(T, W, u, w, 0u64)
        },
        false => {
          T
        },
      };
      fw_inner(v28, N, W, w, add(u, 1u64), ())
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
  let v12 = ltb(w, N);
  match bdec(v12) {
    sumbool::left => {
      let v29 = fw_inner_1(T, N, W, w, 0u64);
      fw_outer(v29, N, W, add(w, 1u64), ())
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
  let v12 = ltb(j, m);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(j, 1u64);
      let v24: &Rc<dyn Fn(u64) -> bool> = &f;
      let v27 = v24(j);
      let v34 = rocq_array::set::<bool>(out, j, v27);
      fill(f, m, v23, v34, ())
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
  let v5 = Rc::clone(&st);
  let v6 = hhead(v5);
  let v10 = Rc::clone(&s);
  let v11 = hash(v10);
  let v12 = &v6;
  let p = rocq_array::get::<u64>(&v12, v11);
  std::mem::drop(v6);
  let v20 = Rc::clone(&st);
  let v21 = hkeys(v20);
  let v25 = hnxt(st);
  walk_1(s, v21, v25, p)
}

// Rocq: Isahasa.isahasa_implem.answer
// Variant: uncurried
pub fn answer(st: Rc<ht>, T: Rc<Array<u64>>, W: u64, k: u64, s1: Rc<rocq_string::RocqString>, s2: Rc<rocq_string::RocqString>, r: relkind) -> bool {
  let v10 = Rc::clone(&st);
  let a = lookup(v10, s1);
  let b = lookup(st, s2);
  match eqb(a, 0u64) {
    true => {
      std::mem::drop(T);
      false
    },
    false => {
      match eqb(b, 0u64) {
        true => {
          std::mem::drop(T);
          false
        },
        false => {
          match r {
            relkind::IsA => {
              match eqb(a, b) {
                true => {
                  std::mem::drop(T);
                  true
                },
                false => {
                  getbit(T, W, sub(a, 1u64), sub(b, 1u64))
                },
              }
            },
            relkind::HasA => {
              getbit(T, W, sub(a, 1u64), add(sub(b, 1u64), k))
            },
          }
        },
      }
    },
  }
}

// Rocq: Isahasa.isahasa_implem.isahasa_impl
// Variant: uncurried
pub fn isahasa_impl(xsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xrs: Rc<Array<relkind>>, xdst: Rc<Array<Rc<rocq_string::RocqString>>>, xqsrc: Rc<Array<Rc<rocq_string::RocqString>>>, xqrs: Rc<Array<relkind>>, xqdst: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>> {
  let v6 = &xsrc;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v6);
  let cap = add(n, n);
  let v23 = make(0u64, 0u64);
  let v28 = rocq_array::make::<Rc<rocq_string::RocqString>>(cap, v23);
  let v35 = rocq_array::make::<u64>(cap, 0u64);
  let v44 = rocq_array::make::<u64>(1024u64, 0u64);
  let st0 = Rc::new(ht { hkeys: v28, hnxt: v35, hhead: v44, hcnt: 0u64 });
  let v67 = rocq_array::make::<u64>(n, 0u64);
  let v74 = rocq_array::make::<u64>(n, 0u64);
  let v89 = iloop_1(xsrc, xdst, n, 0u64, st0, v67, v74);
  match v89 {
    (v91, v93) => {
      match v91 {
        (v96, v98) => {
          let ia = &v96;
          let k = hcnt(ia);
          let N = add(k, k);
          let W = div(add(N, 62u64), 63u64);
          let v141 = rocq_array::make::<u64>(mul(N, W), 0u64);
          let T0 = eloop_1(xrs, v98, v93, k, W, n, 0u64, v141);
          let T = fw_outer_1(T0, N, W, 0u64);
          let v171 = &xqsrc;
          let m = rocq_array::length::<Rc<rocq_string::RocqString>>(&v171);
          let v188 = {
            let __anf_capture_189 = xqsrc;
            let __anf_capture_195 = v96;
            let __anf_capture_199 = W;
            let __anf_capture_201 = k;
            move |j: u64| -> bool {
              let xqsrc = &__anf_capture_189;
              let xqdst = &xqdst;
              let xqrs = &xqrs;
              let ia = &__anf_capture_195;
              let T = &T;
              let W = &__anf_capture_199;
              let k = &__anf_capture_201;
              let v207 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xqsrc, j);
              let v210 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xqdst, j);
              let v213 = rocq_array::get::<relkind>(&xqrs, j);
              let v215 = Rc::clone(ia);
              let v217 = Rc::clone(T);
              let v219 = Clone::clone(W);
              let v221 = Clone::clone(k);
              answer(v215, v217, v219, v221, v207, v210, v213)
            }
          };
          let v231: Rc<dyn Fn(u64) -> bool> = Rc::new(v188);
          let v241 = rocq_array::make::<bool>(m, false);
          fill_1(v231, m, 0u64, v241)
        },
      }
    },
  }
}

// Rocq: Isahasa.isahasa_implem.isahasa_impl
pub fn isahasa_impl_curried(xsrc: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>> {
  let v3 = {
    move |xrs: Rc<Array<relkind>>| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>> {
      let xsrc = &xsrc;
      let v8 = Rc::clone(xsrc);
      let v11 = {
        move |xdst: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>> {
          let xsrc = &v8;
          let xrs = &xrs;
          let v18 = Rc::clone(xsrc);
          let v20 = Rc::clone(xrs);
          let v23 = {
            move |xqsrc: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>> {
              let xsrc = &v18;
              let xrs = &v20;
              let xdst = &xdst;
              let v32 = Rc::clone(xsrc);
              let v34 = Rc::clone(xrs);
              let v36 = Rc::clone(xdst);
              let v39 = {
                move |xqrs: Rc<Array<relkind>>| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> {
                  let xsrc = &v32;
                  let xrs = &v34;
                  let xdst = &v36;
                  let xqsrc = &xqsrc;
                  let v50 = Rc::clone(xsrc);
                  let v52 = Rc::clone(xrs);
                  let v54 = Rc::clone(xdst);
                  let v56 = Rc::clone(xqsrc);
                  let v59 = {
                    move |xqdst: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<Array<bool>> {
                      let v73 = Rc::clone(&v50);
                      let v75 = Rc::clone(&v52);
                      let v77 = Rc::clone(&v54);
                      let v79 = Rc::clone(&v56);
                      let v81 = Rc::clone(&xqrs);
                      isahasa_impl(v73, v75, v77, v79, v81, xqdst)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>> = Rc::new(v3);
  v103
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> = __rocq_global_1019.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1019: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<relkind>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>> = isahasa(); }
std::thread_local! { static __rocq_global_1022: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<relkind>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<bool>>>>>>>> = isahasa_curried(); }