#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

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

pub type char63 = u64;

// Rocq: Doublets.doublets_implem.M_word
pub fn M_word() -> u64 {
  65536u64
}

// Rocq: Doublets.doublets_implem.M_key
pub fn M_key() -> u64 {
  1048576u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Doublets.doublets_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Doublets.doublets_implem.hloop
// Variant: uncurried
pub fn hloop_1(x: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64, h: u64) -> u64 {
  hloop(x, p, len, j, h, ())
}

// Rocq: Doublets.doublets_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(x: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64, h: u64, _H: ()) -> u64 {
  let tmp = ltb(j, len);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = mul(h, 31u64);
      let tmp_3 = if eqb(j, p) {
        1u64
      } else {
        let x_clone = Rc::clone(&x);
        add(get(x_clone, j), 2u64)
      };
      hloop(x, p, len, tmp_1, add(tmp_2, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      h
    },
  }
}

// Rocq: Doublets.doublets_implem.khash
// Variant: uncurried
pub fn khash(m: u64, x: Rc<rocq_string::RocqString>, p: u64) -> u64 {
  let x_clone = Rc::clone(&x);
  let len = length(x_clone);
  mod_(hloop_1(x, p, len, 0u64, 7u64), m)
}

// Rocq: Doublets.doublets_implem.wbuild
// Variant: uncurried
pub fn wbuild_1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  wbuild(xd, n, i, wl, wb, wn, ())
}

// Rocq: Doublets.doublets_implem.wbuild (local: wbuild)
// Variant: uncurried, lifted
pub fn wbuild(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&xd, i);
      let w_clone = Rc::clone(&w);
      let tmp_1 = length(w_clone);
      let w_clone_1 = Rc::clone(&w);
      let h = khash(__rocq_global_196, w_clone_1, tmp_1);
      let old = rocq_array::get::<u64>(&wb, h);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::set::<u64>(wl, i, length(w));
      let tmp_4 = rocq_array::set::<u64>(wb, h, add(i, 1u64));
      let tmp_5 = rocq_array::set::<u64>(wn, i, old);
      wbuild(xd, n, tmp_2, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(xd);
      ((wl, wb), wn)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Doublets.doublets_implem.find
// Variant: uncurried
pub fn find_1(nx: Rc<Array<u64>>, test: Rc<dyn Fn(u64) -> bool>, ptr: u64) -> u64 {
  find(nx, test, ptr, ())
}

// Rocq: Doublets.doublets_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(nx: Rc<Array<u64>>, test: Rc<dyn Fn(u64) -> bool>, ptr: u64, _H: ()) -> u64 {
  if eqb(ptr, 0u64) {
    std::mem::drop(nx);
    std::mem::drop(test);
    0u64
  } else {
    let tmp = sub(ptr, 1u64);
    let test_ref: &Rc<dyn Fn(u64) -> bool> = &test;
    let tmp_1 = test_ref(tmp);
    if tmp_1 {
      std::mem::drop(nx);
      std::mem::drop(test);
      ptr
    } else {
      let tmp_2 = rocq_array::get::<u64>(&nx, sub(ptr, 1u64));
      let tmp_3 = ltb(tmp_2, ptr);
      match bdec(tmp_3) {
        sumbool::left => {
          let tmp_4 = rocq_array::get::<u64>(&nx, sub(ptr, 1u64));
          find(nx, test, tmp_4, ())
        },
        sumbool::right => {
          std::mem::drop(nx);
          std::mem::drop(test);
          0u64
        },
      }
    }
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

// Rocq: Doublets.doublets_implem.kloop
// Variant: uncurried
pub fn kloop_1(x: Rc<rocq_string::RocqString>, y: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64) -> bool {
  kloop(x, y, p, len, j, ())
}

// Rocq: Doublets.doublets_implem.kloop (local: kloop)
// Variant: uncurried, lifted
pub fn kloop(x: Rc<rocq_string::RocqString>, y: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64, _H: ()) -> bool {
  let tmp = ltb(j, len);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = eqb(j, p);
      let x_clone = Rc::clone(&x);
      let tmp_2 = get(x_clone, j);
      let y_clone = Rc::clone(&y);
      let tmp_3 = eqb(tmp_2, get(y_clone, j));
      if orb(tmp_1, tmp_3) {
        kloop(x, y, p, len, add(j, 1u64), ())
      } else {
        std::mem::drop(x);
        std::mem::drop(y);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      true
    },
  }
}

// Rocq: Doublets.doublets_implem.keq
// Variant: uncurried
pub fn keq(x: Rc<rocq_string::RocqString>, y: Rc<rocq_string::RocqString>, p: u64) -> bool {
  let x_clone = Rc::clone(&x);
  let len = length(x_clone);
  let y_clone = Rc::clone(&y);
  let tmp = length(y_clone);
  if eqb(len, tmp) {
    kloop_1(x, y, p, len, 0u64)
  } else {
    std::mem::drop(x);
    std::mem::drop(y);
    false
  }
}

// Rocq: Doublets.doublets_implem.ktest
// Variant: borrowed, uncurried
pub fn ktest(xd: &Rc<Array<Rc<rocq_string::RocqString>>>, w: &Rc<rocq_string::RocqString>, p: u64, y: u64) -> bool {
  let p_1 = p;
  let y_1 = y;
  let tmp = eqb(mod_(y_1, 16u64), p_1);
  let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(xd, lsr(y_1, 4u64));
  let w_clone = Rc::clone(w);
  andb(tmp, keq(tmp_1, w_clone, p_1))
}

// Rocq: Doublets.doublets_implem.build
// Variant: uncurried
pub fn build_1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, N16: u64, e: u64, cls: Rc<Array<u64>>, bk: Rc<Array<u64>>, bn: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  build(xd, N16, e, cls, bk, bn, hd, cn, ())
}

// Rocq: Doublets.doublets_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xd: Rc<Array<Rc<rocq_string::RocqString>>>, N16: u64, e: u64, cls: Rc<Array<u64>>, bk: Rc<Array<u64>>, bn: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(e, N16);
  match bdec(tmp) {
    sumbool::left => {
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&xd, lsr(e, 4u64));
      let p = mod_(e, 16u64);
      let w_clone = Rc::clone(&w);
      let tmp_1 = length(w_clone);
      if ltb(p, tmp_1) {
        let w_clone_1 = Rc::clone(&w);
        let h = khash(__rocq_global_276, w_clone_1, p);
        let old = rocq_array::get::<u64>(&bk, h);
        let xd_clone = Rc::clone(&xd);
        let w_clone_2 = Rc::clone(&w);
        let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
          let __anf_capture_80 = p;
          move |v82: u64| -> bool {
            let xd = &xd_clone;
            let w = &w_clone_2;
            let tmp_2 = Clone::clone(&__anf_capture_80);
            ktest(xd, w, tmp_2, v82)
          }
        });
        let bn_clone = Rc::clone(&bn);
        let r = find_1(bn_clone, callback, old);
        let tmp_3 = 0u64;
        let c = if eqb(r, tmp_3) {
          std::mem::drop(w);
          e
        } else {
          std::mem::drop(w);
          let tmp_4 = sub(r, 1u64);
          rocq_array::get::<u64>(&cls, tmp_4)
        };
        let oldc = rocq_array::get::<u64>(&hd, c);
        let tmp_5 = add(e, 1u64);
        let tmp_6 = rocq_array::set::<u64>(cls, e, c);
        let tmp_7 = rocq_array::set::<u64>(bk, h, add(e, 1u64));
        let tmp_8 = rocq_array::set::<u64>(bn, e, old);
        let tmp_9 = rocq_array::set::<u64>(hd, c, add(e, 1u64));
        let tmp_10 = rocq_array::set::<u64>(cn, e, oldc);
        build(xd, N16, tmp_5, tmp_6, tmp_7, tmp_8, tmp_9, tmp_10, ())
      } else {
        std::mem::drop(w);
        build(xd, N16, add(e, 1u64), cls, bk, bn, hd, cn, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xd);
      std::mem::drop(bk);
      std::mem::drop(bn);
      ((cls, hd), cn)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let tmp = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Doublets.doublets_implem.wtest
// Variant: borrowed, uncurried
pub fn wtest(xd: &Rc<Array<Rc<rocq_string::RocqString>>>, q: &Rc<rocq_string::RocqString>, y: u64) -> bool {
  let y_1 = y;
  let tmp = rocq_array::get::<Rc<rocq_string::RocqString>>(xd, y_1);
  let q_clone = Rc::clone(q);
  match compare(tmp, q_clone) {
    std::cmp::Ordering::Equal => {
      true
    },
    std::cmp::Ordering::Less => {
      false
    },
    std::cmp::Ordering::Greater => {
      false
    },
  }
}

// Rocq: Doublets.doublets_implem.lookup
// Variant: uncurried
pub fn lookup(xd: Rc<Array<Rc<rocq_string::RocqString>>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, q: Rc<rocq_string::RocqString>) -> u64 {
  let q_clone = Rc::clone(&q);
  let tmp = length(q_clone);
  let q_clone_1 = Rc::clone(&q);
  let h = khash(__rocq_global_196, q_clone_1, tmp);
  let ptr = rocq_array::get::<u64>(&wb, h);
  std::mem::drop(wb);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_31 = q;
    move |v33: u64| -> bool {
      wtest(&xd, &__anf_capture_31, v33)
    }
  });
  find_1(wn, callback, ptr)
}

// Rocq: Doublets.doublets_implem.sT
pub fn sT(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> u64 {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v14);
                  std::mem::drop(v4);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v9
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sQ
pub fn sQ(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> Rc<Array<u64>> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v4);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v14
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sM
pub fn sM(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> Rc<Array<u64>> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              match v12 {
                (v17, v19) => {
                  std::mem::drop(v14);
                  std::mem::drop(v17);
                  std::mem::drop(v19);
                  v4
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.sD
pub fn sD(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> Rc<Array<u64>> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              std::mem::drop(v4);
              let a0 = &v12;
              std::mem::drop(v14);
              let a0_0_clone = Rc::clone(&a0.0);
              std::mem::drop(v12);
              a0_0_clone
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.mkb
// Variant: uncurried
pub fn mkb(D: Rc<Array<u64>>, P: Rc<Array<u64>>, Q: Rc<Array<u64>>, T: u64, M: Rc<Array<u64>>) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  ((((D, P), Q), T), M)
}

// Rocq: Doublets.doublets_implem.sP
pub fn sP(s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> Rc<Array<u64>> {
  match s {
    (v2, v4) => {
      match v2 {
        (v7, _v9) => {
          match v7 {
            (v12, v14) => {
              std::mem::drop(v4);
              let a0 = &v12;
              std::mem::drop(v14);
              let a0_1_clone = Rc::clone(&a0.1);
              std::mem::drop(v12);
              a0_1_clone
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.cwalk
// Variant: uncurried
pub fn cwalk_1(cn: Rc<Array<u64>>, u: u64, du: u64, ptr: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  cwalk(cn, u, du, ptr, s, ())
}

// Rocq: Doublets.doublets_implem.cwalk (local: cwalk)
// Variant: uncurried, lifted
pub fn cwalk(cn: Rc<Array<u64>>, u: u64, du: u64, ptr: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>), _H: ()) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  if eqb(ptr, 0u64) {
    std::mem::drop(cn);
    s
  } else {
    let e = sub(ptr, 1u64);
    let v = lsr(e, 4u64);
    let s_clone = Clone::clone(&s);
    let tmp = sD(s_clone);
    let tmp_1 = rocq_array::get::<u64>(&tmp, v);
    let tmp_2 = 0u64;
    let s_ = if eqb(tmp_1, tmp_2) {
      let s_clone_1 = Clone::clone(&s);
      let tmp_3 = sD(s_clone_1);
      let tmp_4 = rocq_array::set::<u64>(tmp_3, v, add(du, 1u64));
      let s_clone_2 = Clone::clone(&s);
      let tmp_5 = sP(s_clone_2);
      let tmp_6 = rocq_array::set::<u64>(tmp_5, v, u);
      let s_clone_3 = Clone::clone(&s);
      let tmp_7 = sQ(s_clone_3);
      let s_clone_4 = Clone::clone(&s);
      let tmp_8 = rocq_array::set::<u64>(tmp_7, sT(s_clone_4), v);
      let s_clone_5 = Clone::clone(&s);
      let tmp_9 = add(sT(s_clone_5), 1u64);
      let tmp_10 = sM(s);
      mkb(tmp_4, tmp_6, tmp_8, tmp_9, tmp_10)
    } else {
      s
    };
    let tmp_11 = rocq_array::get::<u64>(&cn, e);
    let tmp_12 = ltb(tmp_11, ptr);
    match bdec(tmp_12) {
      sumbool::left => {
        std::mem::drop(tmp);
        let tmp_13 = rocq_array::get::<u64>(&cn, e);
        cwalk(cn, u, du, tmp_13, s_, ())
      },
      sumbool::right => {
        std::mem::drop(cn);
        std::mem::drop(tmp);
        s_
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.ploop
// Variant: uncurried
pub fn ploop_1(cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, u: u64, du: u64, base: u64, len: u64, p: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  ploop(cls, hd, cn, u, du, base, len, p, s, ())
}

// Rocq: Doublets.doublets_implem.ploop (local: ploop)
// Variant: uncurried, lifted
pub fn ploop(cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, u: u64, du: u64, base: u64, len: u64, p: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>), _H: ()) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  let tmp = ltb(p, len);
  match bdec(tmp) {
    sumbool::left => {
      let c = rocq_array::get::<u64>(&cls, add(base, p));
      let s_clone = Clone::clone(&s);
      let tmp_1 = sM(s_clone);
      let tmp_2 = rocq_array::get::<u64>(&tmp_1, c);
      if eqb(tmp_2, 0u64) {
        std::mem::drop(tmp_1);
        let tmp_3 = rocq_array::get::<u64>(&hd, c);
        let cn_clone = Rc::clone(&cn);
        let s1 = cwalk_1(cn_clone, u, du, tmp_3, s);
        let tmp_4 = add(p, 1u64);
        let s1_clone = Clone::clone(&s1);
        let tmp_5 = sD(s1_clone);
        let s1_clone_1 = Clone::clone(&s1);
        let tmp_6 = sP(s1_clone_1);
        let s1_clone_2 = Clone::clone(&s1);
        let tmp_7 = sQ(s1_clone_2);
        let s1_clone_3 = Clone::clone(&s1);
        let tmp_8 = sT(s1_clone_3);
        let tmp_9 = sM(s1);
        let tmp_10 = rocq_array::set::<u64>(tmp_9, c, 1u64);
        ploop(cls, hd, cn, u, du, base, len, tmp_4, mkb(tmp_5, tmp_6, tmp_7, tmp_8, tmp_10), ())
      } else {
        std::mem::drop(tmp_1);
        ploop(cls, hd, cn, u, du, base, len, add(p, 1u64), s, ())
      }
    },
    sumbool::right => {
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      s
    },
  }
}

// Rocq: Doublets.doublets_implem.bfs
// Variant: uncurried
pub fn bfs_1(cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, n: u64, qh: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>)) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  bfs(cls, hd, cn, wl, n, qh, s, ())
}

// Rocq: Doublets.doublets_implem.bfs (local: bfs)
// Variant: uncurried, lifted
pub fn bfs(cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, n: u64, qh: u64, s: ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>), _H: ()) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  let tmp = ltb(qh, n);
  match bdec(tmp) {
    sumbool::left => {
      let s_clone = Clone::clone(&s);
      let tmp_1 = sT(s_clone);
      if ltb(qh, tmp_1) {
        let s_clone_1 = Clone::clone(&s);
        let tmp_2 = sQ(s_clone_1);
        let u = rocq_array::get::<u64>(&tmp_2, qh);
        std::mem::drop(tmp_2);
        let len = rocq_array::get::<u64>(&wl, u);
        let s_clone_2 = Clone::clone(&s);
        let tmp_3 = sD(s_clone_2);
        let tmp_4 = rocq_array::get::<u64>(&tmp_3, u);
        std::mem::drop(tmp_3);
        let tmp_5 = mul(u, 16u64);
        let cls_clone = Rc::clone(&cls);
        let hd_clone = Rc::clone(&hd);
        let cn_clone = Rc::clone(&cn);
        let s_ = ploop_1(cls_clone, hd_clone, cn_clone, u, tmp_4, tmp_5, len, 0u64, s);
        bfs(cls, hd, cn, wl, n, add(qh, 1u64), s_, ())
      } else {
        std::mem::drop(cls);
        std::mem::drop(hd);
        std::mem::drop(cn);
        std::mem::drop(wl);
        s
      }
    },
    sumbool::right => {
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      std::mem::drop(wl);
      s
    },
  }
}

// Rocq: Doublets.doublets_implem.bfs_from
// Variant: uncurried
pub fn bfs_from(cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, n: u64, N16: u64, s0: u64) -> ((((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64), Rc<Array<u64>>) {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::set::<u64>(tmp, s0, 1u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let tmp_4 = rocq_array::set::<u64>(tmp_3, 0u64, s0);
  let tmp_5 = rocq_array::make::<u64>(N16, 0u64);
  bfs_1(cls, hd, cn, wl, n, 0u64, mkb(tmp_1, tmp_2, tmp_4, 1u64, tmp_5))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Doublets.doublets_implem.recon
// Variant: uncurried
pub fn recon_1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, D: Rc<Array<u64>>, P: Rc<Array<u64>>, v: u64, out: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  recon(xd, D, P, v, out, ())
}

// Rocq: Doublets.doublets_implem.recon (local: recon)
// Variant: uncurried, lifted
pub fn recon(xd: Rc<Array<Rc<rocq_string::RocqString>>>, D: Rc<Array<u64>>, P: Rc<Array<u64>>, v: u64, out: Rc<Array<Rc<rocq_string::RocqString>>>, _H: ()) -> Rc<Array<Rc<rocq_string::RocqString>>> {
  let tmp = rocq_array::get::<u64>(&D, v);
  let tmp_1 = sub(tmp, 1u64);
  let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xd, v);
  let out_ = rocq_array::set::<Rc<rocq_string::RocqString>>(out, tmp_1, tmp_2);
  let tmp_3 = rocq_array::get::<u64>(&D, v);
  if leb(tmp_3, 1u64) {
    std::mem::drop(P);
    std::mem::drop(xd);
    std::mem::drop(D);
    out_
  } else {
    let tmp_4 = rocq_array::get::<u64>(&P, v);
    let tmp_5 = rocq_array::get::<u64>(&D, tmp_4);
    let tmp_6 = rocq_array::get::<u64>(&D, v);
    let tmp_7 = ltb(tmp_5, tmp_6);
    match bdec(tmp_7) {
      sumbool::left => {
        let tmp_8 = rocq_array::get::<u64>(&P, v);
        recon(xd, D, P, tmp_8, out_, ())
      },
      sumbool::right => {
        std::mem::drop(P);
        std::mem::drop(xd);
        std::mem::drop(D);
        out_
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.answer2
// Variant: uncurried
pub fn answer2(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, s0: u64, tgt: Rc<rocq_string::RocqString>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let xd_clone = Rc::clone(&xd);
  let rt = lookup(xd_clone, wb, wn, tgt);
  if eqb(rt, 0u64) {
    std::mem::drop(xd);
    std::mem::drop(cls);
    std::mem::drop(hd);
    std::mem::drop(cn);
    std::mem::drop(wl);
    Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
  } else {
    let t = sub(rt, 1u64);
    let st = bfs_from(cls, hd, cn, wl, n, N16, s0);
    let st_clone = Clone::clone(&st);
    let tmp = sD(st_clone);
    let dt = rocq_array::get::<u64>(&tmp, t);
    if eqb(dt, 0u64) {
      std::mem::drop(st);
      std::mem::drop(xd);
      std::mem::drop(tmp);
      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
    } else {
      std::mem::drop(tmp);
      let st_clone_1 = Clone::clone(&st);
      let tmp_1 = sD(st_clone_1);
      let tmp_2 = sP(st);
      let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xd, t);
      let tmp_4 = rocq_array::make::<Rc<rocq_string::RocqString>>(dt, tmp_3);
      let tmp_5 = recon_1(xd, tmp_1, tmp_2, t, tmp_4);
      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(tmp_5))
    }
  }
}

// Rocq: Doublets.doublets_implem.answer1
// Variant: uncurried
pub fn answer1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, src: Rc<rocq_string::RocqString>, tgt: Rc<rocq_string::RocqString>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let xd_clone = Rc::clone(&xd);
  let wb_clone = Rc::clone(&wb);
  let wn_clone = Rc::clone(&wn);
  let src_clone = Rc::clone(&src);
  let rs = lookup(xd_clone, wb_clone, wn_clone, src_clone);
  if eqb(rs, 0u64) {
    std::mem::drop(xd);
    std::mem::drop(cls);
    std::mem::drop(hd);
    std::mem::drop(cn);
    std::mem::drop(wl);
    std::mem::drop(wb);
    std::mem::drop(wn);
    std::mem::drop(src);
    std::mem::drop(tgt);
    Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
  } else {
    let s0 = sub(rs, 1u64);
    let tgt_clone = Rc::clone(&tgt);
    match compare(src, tgt_clone) {
      std::cmp::Ordering::Equal => {
        std::mem::drop(cls);
        std::mem::drop(hd);
        std::mem::drop(cn);
        std::mem::drop(wl);
        std::mem::drop(wb);
        std::mem::drop(wn);
        std::mem::drop(tgt);
        let tmp = 1u64;
        let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xd, s0);
        std::mem::drop(xd);
        let tmp_2 = rocq_array::make::<Rc<rocq_string::RocqString>>(tmp, tmp_1);
        Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(tmp_2))
      },
      std::cmp::Ordering::Less => {
        answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
      },
      std::cmp::Ordering::Greater => {
        answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
      },
    }
  }
}

// Rocq: Doublets.doublets_implem.qloop
// Variant: uncurried
pub fn qloop_1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, xs: Rc<Array<Rc<rocq_string::RocqString>>>, xt: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, nq: u64, q: u64, out: Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>> {
  qloop(xd, xs, xt, n, N16, cls, hd, cn, wl, wb, wn, nq, q, out, ())
}

// Rocq: Doublets.doublets_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(xd: Rc<Array<Rc<rocq_string::RocqString>>>, xs: Rc<Array<Rc<rocq_string::RocqString>>>, xt: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, nq: u64, q: u64, out: Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>, _H: ()) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>> {
  let tmp = ltb(q, nq);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(q, 1u64);
      let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xs, q);
      let tmp_3 = rocq_array::get::<Rc<rocq_string::RocqString>>(&xt, q);
      let xd_clone = Rc::clone(&xd);
      let cls_clone = Rc::clone(&cls);
      let hd_clone = Rc::clone(&hd);
      let cn_clone = Rc::clone(&cn);
      let wl_clone = Rc::clone(&wl);
      let wb_clone = Rc::clone(&wb);
      let wn_clone = Rc::clone(&wn);
      let tmp_4 = rocq_array::set::<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>(out, q, answer1(xd_clone, n, N16, cls_clone, hd_clone, cn_clone, wl_clone, wb_clone, wn_clone, tmp_2, tmp_3));
      qloop(xd, xs, xt, n, N16, cls, hd, cn, wl, wb, wn, nq, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(xd);
      std::mem::drop(xs);
      std::mem::drop(xt);
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      std::mem::drop(wl);
      std::mem::drop(wb);
      std::mem::drop(wn);
      out
    },
  }
}

// Rocq: Doublets.doublets_implem.doublets_impl
// Variant: uncurried
pub fn doublets_impl(xd: Rc<Array<Rc<rocq_string::RocqString>>>, xs: Rc<Array<Rc<rocq_string::RocqString>>>, xt: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>> {
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&xd);
  let N16 = mul(n, 16u64);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(__rocq_global_196, 0u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let xd_clone = Rc::clone(&xd);
  let tmp_3 = wbuild_1(xd_clone, n, 0u64, tmp, tmp_1, tmp_2);
  match tmp_3 {
    (v53, v55) => {
      match v53 {
        (v58, v60) => {
          let tmp_4 = rocq_array::make::<u64>(N16, 0u64);
          let tmp_5 = rocq_array::make::<u64>(__rocq_global_276, 0u64);
          let tmp_6 = rocq_array::make::<u64>(N16, 0u64);
          let tmp_7 = rocq_array::make::<u64>(N16, 0u64);
          let tmp_8 = rocq_array::make::<u64>(N16, 0u64);
          let xd_clone_1 = Rc::clone(&xd);
          let tmp_9 = build_1(xd_clone_1, N16, 0u64, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8);
          match tmp_9 {
            (v120, v122) => {
              match v120 {
                (v125, v127) => {
                  let nq = rocq_array::length::<Rc<rocq_string::RocqString>>(&xs);
                  let tmp_10 = rocq_array::make::<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>(nq, Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None));
                  qloop_1(xd, xs, xt, n, N16, v125, v127, v122, v58, v60, v55, nq, 0u64, tmp_10)
                },
              }
            },
          }
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
const __rocq_global_196: u64 = 65536u64;
const __rocq_global_276: u64 = 1048576u64;