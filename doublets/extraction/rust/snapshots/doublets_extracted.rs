// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Doublets.doublets_implem.doublets
// Variant: uncurried
pub fn doublets() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>> = doublets_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Doublets.doublets_implem.doublets
pub fn doublets_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>> = doublets_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>>> = Rc::new(v0);
  v1
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
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Doublets.doublets_implem.hloop
// Variant: uncurried
pub fn hloop_1(x: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64, h: u64) -> u64 {
  hloop(x, p, len, j, h, ())
}

// Rocq: Doublets.doublets_implem.hloop (local: hloop)
// Variant: uncurried, lifted
pub fn hloop(x: Rc<rocq_string::RocqString>, p: u64, len: u64, j: u64, h: u64, _H: ()) -> u64 {
  let v13 = ltb(j, len);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(j, 1u64);
      let v33 = mul(h, 31u64);
      let v40 = match eqb(j, p) {
        true => {
          1u64
        },
        false => {
          let v49 = Rc::clone(&x);
          add(get(v49, j), 2u64)
        },
      };
      hloop(x, p, len, v24, add(v33, v40), ())
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
  let v6 = Rc::clone(&x);
  let len = length(v6);
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
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &xd;
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&v18, i);
      let v27 = Rc::clone(&w);
      let v28 = length(v27);
      let v33 = Rc::clone(&w);
      let h = khash(__rocq_global_196, v33, v28);
      let v37 = &wb;
      let old = rocq_array::get::<u64>(&v37, h);
      let v48 = add(i, 1u64);
      let v59 = rocq_array::set::<u64>(wl, i, length(w));
      let v74 = rocq_array::set::<u64>(wb, h, add(i, 1u64));
      let v81 = rocq_array::set::<u64>(wn, i, old);
      wbuild(xd, n, v48, v59, v74, v81, ())
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
  match eqb(ptr, 0u64) {
    true => {
      std::mem::drop(nx);
      std::mem::drop(test);
      0u64
    },
    false => {
      let v24 = sub(ptr, 1u64);
      let v25: &Rc<dyn Fn(u64) -> bool> = &test;
      let v28 = v25(v24);
      match v28 {
        true => {
          std::mem::drop(nx);
          std::mem::drop(test);
          ptr
        },
        false => {
          let v41 = sub(ptr, 1u64);
          let v42 = &nx;
          let v46 = rocq_array::get::<u64>(&v42, v41);
          let v51 = ltb(v46, ptr);
          match bdec(v51) {
            sumbool::left => {
              let v62 = sub(ptr, 1u64);
              let v63 = &nx;
              let v66 = rocq_array::get::<u64>(&v63, v62);
              find(nx, test, v66, ())
            },
            sumbool::right => {
              std::mem::drop(nx);
              std::mem::drop(test);
              0u64
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
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
  let v13 = ltb(j, len);
  match bdec(v13) {
    sumbool::left => {
      let v23 = eqb(j, p);
      let v28 = Rc::clone(&x);
      let v31 = get(v28, j);
      let v35 = Rc::clone(&y);
      let v43 = eqb(v31, get(v35, j));
      match orb(v23, v43) {
        true => {
          kloop(x, y, p, len, add(j, 1u64), ())
        },
        false => {
          std::mem::drop(x);
          std::mem::drop(y);
          false
        },
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
  let v6 = Rc::clone(&x);
  let len = length(v6);
  let v12 = Rc::clone(&y);
  let v13 = length(v12);
  match eqb(len, v13) {
    true => {
      kloop_1(x, y, p, len, 0u64)
    },
    false => {
      std::mem::drop(x);
      std::mem::drop(y);
      false
    },
  }
}

// Rocq: Doublets.doublets_implem.ktest
// Variant: borrowed, uncurried
pub fn ktest(xd: &Rc<Array<Rc<rocq_string::RocqString>>>, w: &Rc<rocq_string::RocqString>, p: u64, y: u64) -> bool {
  let p_1 = p;
  let y_1 = y;
  let v20 = eqb(mod_(y_1, 16u64), p_1);
  let v29 = lsr(y_1, 4u64);
  let v30 = xd;
  let v34 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v30, v29);
  let v38 = Rc::clone(w);
  andb(v20, keq(v34, v38, p_1))
}

// Rocq: Doublets.doublets_implem.build
// Variant: uncurried
pub fn build_1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, N16: u64, e: u64, cls: Rc<Array<u64>>, bk: Rc<Array<u64>>, bn: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  build(xd, N16, e, cls, bk, bn, hd, cn, ())
}

// Rocq: Doublets.doublets_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(xd: Rc<Array<Rc<rocq_string::RocqString>>>, N16: u64, e: u64, cls: Rc<Array<u64>>, bk: Rc<Array<u64>>, bn: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let v16 = ltb(e, N16);
  match bdec(v16) {
    sumbool::left => {
      let v27 = lsr(e, 4u64);
      let v28 = &xd;
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&v28, v27);
      let p = mod_(e, 16u64);
      let v44 = Rc::clone(&w);
      let v45 = length(v44);
      match ltb(p, v45) {
        true => {
          let v58 = Rc::clone(&w);
          let h = khash(__rocq_global_276, v58, p);
          let v62 = &bk;
          let old = rocq_array::get::<u64>(&v62, h);
          let v69 = Rc::clone(&xd);
          let v72 = Rc::clone(&w);
          let v75 = {
            let __anf_capture_80 = p;
            move |v82: u64| -> bool {
              let xd = &v69;
              let w = &v72;
              let v84 = Clone::clone(&__anf_capture_80);
              ktest(xd, w, v84, v82)
            }
          };
          let v93: Rc<dyn Fn(u64) -> bool> = Rc::new(v75);
          let v97 = Rc::clone(&bn);
          let r = find_1(v97, v93, old);
          let v105 = 0u64;
          let c = match eqb(r, v105) {
            true => {
              std::mem::drop(w);
              e
            },
            false => {
              std::mem::drop(w);
              let v121 = sub(r, 1u64);
              let v122 = &cls;
              rocq_array::get::<u64>(&v122, v121)
            },
          };
          let v129 = &hd;
          let oldc = rocq_array::get::<u64>(&v129, c);
          let v140 = add(e, 1u64);
          let v147 = rocq_array::set::<u64>(cls, e, c);
          let v162 = rocq_array::set::<u64>(bk, h, add(e, 1u64));
          let v169 = rocq_array::set::<u64>(bn, e, old);
          let v184 = rocq_array::set::<u64>(hd, c, add(e, 1u64));
          let v191 = rocq_array::set::<u64>(cn, e, oldc);
          build(xd, N16, v140, v147, v162, v169, v184, v191, ())
        },
        false => {
          std::mem::drop(w);
          build(xd, N16, add(e, 1u64), cls, bk, bn, hd, cn, ())
        },
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
  let v4 = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  v4
}

// Rocq: Doublets.doublets_implem.wtest
// Variant: borrowed, uncurried
pub fn wtest(xd: &Rc<Array<Rc<rocq_string::RocqString>>>, q: &Rc<rocq_string::RocqString>, y: u64) -> bool {
  let y_1 = y;
  let v5 = xd;
  let v9 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v5, y_1);
  let v13 = Rc::clone(q);
  match compare(v9, v13) {
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
  let v9 = Rc::clone(&q);
  let v10 = length(v9);
  let v15 = Rc::clone(&q);
  let h = khash(__rocq_global_196, v15, v10);
  let v19 = &wb;
  let ptr = rocq_array::get::<u64>(&v19, h);
  std::mem::drop(wb);
  let v28 = {
    let __anf_capture_31 = q;
    move |v33: u64| -> bool {
      wtest(&xd, &__anf_capture_31, v33)
    }
  };
  let v42: Rc<dyn Fn(u64) -> bool> = Rc::new(v28);
  find_1(wn, v42, ptr)
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
              let v18 = Rc::clone((&(a0).0));
              std::mem::drop(v12);
              v18
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
              let v18 = Rc::clone((&(a0).1));
              std::mem::drop(v12);
              v18
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
  match eqb(ptr, 0u64) {
    true => {
      std::mem::drop(cn);
      s
    },
    false => {
      let e = sub(ptr, 1u64);
      let v = lsr(e, 4u64);
      let v36 = Clone::clone(&s);
      let v38 = sD(v36);
      let v39 = &v38;
      let v42 = rocq_array::get::<u64>(&v39, v);
      let v44 = 0u64;
      let s_ = match eqb(v42, v44) {
        true => {
          let v54 = Clone::clone(&s);
          let v56 = sD(v54);
          let v71 = rocq_array::set::<u64>(v56, v, add(du, 1u64));
          let v74 = Clone::clone(&s);
          let v77 = sP(v74);
          let v83 = rocq_array::set::<u64>(v77, v, u);
          let v86 = Clone::clone(&s);
          let v88 = sQ(v86);
          let v91 = Clone::clone(&s);
          let v100 = rocq_array::set::<u64>(v88, sT(v91), v);
          let v104 = Clone::clone(&s);
          let v113 = add(sT(v104), 1u64);
          let v117 = sM(s);
          mkb(v71, v83, v100, v113, v117)
        },
        false => {
          s
        },
      };
      let v136 = &cn;
      let v140 = rocq_array::get::<u64>(&v136, e);
      let v145 = ltb(v140, ptr);
      match bdec(v145) {
        sumbool::left => {
          std::mem::drop(v38);
          let v149 = &cn;
          let v152 = rocq_array::get::<u64>(&v149, e);
          cwalk(cn, u, du, v152, s_, ())
        },
        sumbool::right => {
          std::mem::drop(cn);
          std::mem::drop(v38);
          s_
        },
      }
    },
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
  let v17 = ltb(p, len);
  match bdec(v17) {
    sumbool::left => {
      let v26 = add(base, p);
      let v27 = &cls;
      let c = rocq_array::get::<u64>(&v27, v26);
      let v34 = Clone::clone(&s);
      let v36 = sM(v34);
      let v37 = &v36;
      let v40 = rocq_array::get::<u64>(&v37, c);
      match eqb(v40, 0u64) {
        true => {
          std::mem::drop(v36);
          let v50 = &hd;
          let v53 = rocq_array::get::<u64>(&v50, c);
          let v56 = Rc::clone(&cn);
          let s1 = cwalk_1(v56, u, du, v53, s);
          let v73 = add(p, 1u64);
          let v77 = Clone::clone(&s1);
          let v79 = sD(v77);
          let v82 = Clone::clone(&s1);
          let v84 = sP(v82);
          let v87 = Clone::clone(&s1);
          let v89 = sQ(v87);
          let v92 = Clone::clone(&s1);
          let v94 = sT(v92);
          let v98 = sM(s1);
          let v107 = rocq_array::set::<u64>(v98, c, 1u64);
          ploop(cls, hd, cn, u, du, base, len, v73, mkb(v79, v84, v89, v94, v107), ())
        },
        false => {
          std::mem::drop(v36);
          ploop(cls, hd, cn, u, du, base, len, add(p, 1u64), s, ())
        },
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
  let v15 = ltb(qh, n);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Clone::clone(&s);
      let v24 = sT(v22);
      match ltb(qh, v24) {
        true => {
          let v33 = Clone::clone(&s);
          let v35 = sQ(v33);
          let v36 = &v35;
          let u = rocq_array::get::<u64>(&v36, qh);
          std::mem::drop(v35);
          let v40 = &wl;
          let len = rocq_array::get::<u64>(&v40, u);
          let v47 = Clone::clone(&s);
          let v49 = sD(v47);
          let v50 = &v49;
          let v53 = rocq_array::get::<u64>(&v50, u);
          std::mem::drop(v49);
          let v61 = mul(u, 16u64);
          let v66 = Rc::clone(&cls);
          let v69 = Rc::clone(&hd);
          let v72 = Rc::clone(&cn);
          let s_ = ploop_1(v66, v69, v72, u, v53, v61, len, 0u64, s);
          bfs(cls, hd, cn, wl, n, add(qh, 1u64), s_, ())
        },
        false => {
          std::mem::drop(cls);
          std::mem::drop(hd);
          std::mem::drop(cn);
          std::mem::drop(wl);
          s
        },
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
  let v17 = rocq_array::make::<u64>(n, 0u64);
  let v26 = rocq_array::set::<u64>(v17, s0, 1u64);
  let v33 = rocq_array::make::<u64>(n, 0u64);
  let v40 = rocq_array::make::<u64>(n, 0u64);
  let v49 = rocq_array::set::<u64>(v40, 0u64, s0);
  let v58 = rocq_array::make::<u64>(N16, 0u64);
  bfs_1(cls, hd, cn, wl, n, 0u64, mkb(v26, v33, v49, 1u64, v58))
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
  let v7 = &D;
  let v10 = rocq_array::get::<u64>(&v7, v);
  let v17 = sub(v10, 1u64);
  let v18 = &xd;
  let v21 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v18, v);
  let out_ = rocq_array::set::<Rc<rocq_string::RocqString>>(out, v17, v21);
  let v30 = &D;
  let v33 = rocq_array::get::<u64>(&v30, v);
  match leb(v33, 1u64) {
    true => {
      std::mem::drop(P);
      std::mem::drop(xd);
      std::mem::drop(D);
      out_
    },
    false => {
      let v46 = &P;
      let v49 = rocq_array::get::<u64>(&v46, v);
      let v50 = &D;
      let v53 = rocq_array::get::<u64>(&v50, v49);
      let v54 = &D;
      let v57 = rocq_array::get::<u64>(&v54, v);
      let v63 = ltb(v53, v57);
      match bdec(v63) {
        sumbool::left => {
          let v67 = &P;
          let v70 = rocq_array::get::<u64>(&v67, v);
          recon(xd, D, P, v70, out_, ())
        },
        sumbool::right => {
          std::mem::drop(P);
          std::mem::drop(xd);
          std::mem::drop(D);
          out_
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.answer2
// Variant: uncurried
pub fn answer2(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, s0: u64, tgt: Rc<rocq_string::RocqString>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let v14 = Rc::clone(&xd);
  let rt = lookup(v14, wb, wn, tgt);
  match eqb(rt, 0u64) {
    true => {
      std::mem::drop(xd);
      std::mem::drop(cls);
      std::mem::drop(hd);
      std::mem::drop(cn);
      std::mem::drop(wl);
      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
    },
    false => {
      let t = sub(rt, 1u64);
      let st = bfs_from(cls, hd, cn, wl, n, N16, s0);
      let v62 = Clone::clone(&st);
      let v64 = sD(v62);
      let v65 = &v64;
      let dt = rocq_array::get::<u64>(&v65, t);
      match eqb(dt, 0u64) {
        true => {
          std::mem::drop(st);
          std::mem::drop(xd);
          std::mem::drop(v64);
          Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
        },
        false => {
          std::mem::drop(v64);
          let v86 = Clone::clone(&st);
          let v88 = sD(v86);
          let v92 = sP(st);
          let v93 = &xd;
          let v96 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v93, t);
          let v101 = rocq_array::make::<Rc<rocq_string::RocqString>>(dt, v96);
          let v113 = recon_1(xd, v88, v92, t, v101);
          Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(v113))
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.answer1
// Variant: uncurried
pub fn answer1(xd: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, N16: u64, cls: Rc<Array<u64>>, hd: Rc<Array<u64>>, cn: Rc<Array<u64>>, wl: Rc<Array<u64>>, wb: Rc<Array<u64>>, wn: Rc<Array<u64>>, src: Rc<rocq_string::RocqString>, tgt: Rc<rocq_string::RocqString>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let v14 = Rc::clone(&xd);
  let v17 = Rc::clone(&wb);
  let v20 = Rc::clone(&wn);
  let v23 = Rc::clone(&src);
  let rs = lookup(v14, v17, v20, v23);
  match eqb(rs, 0u64) {
    true => {
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
    },
    false => {
      let s0 = sub(rs, 1u64);
      let v52 = Rc::clone(&tgt);
      match compare(src, v52) {
        std::cmp::Ordering::Equal => {
          std::mem::drop(cls);
          std::mem::drop(hd);
          std::mem::drop(cn);
          std::mem::drop(wl);
          std::mem::drop(wb);
          std::mem::drop(wn);
          std::mem::drop(tgt);
          let v56 = 1u64;
          let v57 = &xd;
          let v60 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v57, s0);
          std::mem::drop(xd);
          let v66 = rocq_array::make::<Rc<rocq_string::RocqString>>(v56, v60);
          Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(v66))
        },
        std::cmp::Ordering::Less => {
          answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
        },
        std::cmp::Ordering::Greater => {
          answer2(xd, n, N16, cls, hd, cn, wl, wb, wn, s0, tgt)
        },
      }
    },
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
  let v22 = ltb(q, nq);
  match bdec(v22) {
    sumbool::left => {
      let v33 = add(q, 1u64);
      let v35 = &xs;
      let v38 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v35, q);
      let v39 = &xt;
      let v42 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v39, q);
      let v45 = Rc::clone(&xd);
      let v52 = Rc::clone(&cls);
      let v55 = Rc::clone(&hd);
      let v58 = Rc::clone(&cn);
      let v61 = Rc::clone(&wl);
      let v64 = Rc::clone(&wb);
      let v67 = Rc::clone(&wn);
      let v79 = rocq_array::set::<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>(out, q, answer1(v45, n, N16, v52, v55, v58, v61, v64, v67, v38, v42));
      qloop(xd, xs, xt, n, N16, cls, hd, cn, wl, wb, wn, nq, v33, v79, ())
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
  let v3 = &xd;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v3);
  let N16 = mul(n, 16u64);
  let v22 = rocq_array::make::<u64>(n, 0u64);
  let v30 = rocq_array::make::<u64>(__rocq_global_196, 0u64);
  let v37 = rocq_array::make::<u64>(n, 0u64);
  let v40 = Rc::clone(&xd);
  let v51 = wbuild_1(v40, n, 0u64, v22, v30, v37);
  match v51 {
    (v53, v55) => {
      match v53 {
        (v58, v60) => {
          let v71 = rocq_array::make::<u64>(N16, 0u64);
          let v79 = rocq_array::make::<u64>(__rocq_global_276, 0u64);
          let v86 = rocq_array::make::<u64>(N16, 0u64);
          let v93 = rocq_array::make::<u64>(N16, 0u64);
          let v100 = rocq_array::make::<u64>(N16, 0u64);
          let v103 = Rc::clone(&xd);
          let v118 = build_1(v103, N16, 0u64, v71, v79, v86, v93, v100);
          match v118 {
            (v120, v122) => {
              match v120 {
                (v125, v127) => {
                  let v129 = &xs;
                  let nq = rocq_array::length::<Rc<rocq_string::RocqString>>(&v129);
                  let v141 = rocq_array::make::<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>(nq, Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None));
                  qloop_1(xd, xs, xt, n, N16, v125, v127, v122, v58, v60, v55, nq, 0u64, v141)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Doublets.doublets_implem.doublets_impl
pub fn doublets_impl_curried(xd: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>> {
  let v3 = {
    move |xs: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> {
      let xd = &xd;
      let v8 = Rc::clone(xd);
      let v11 = {
        move |xt: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&xs);
          doublets_impl(v19, v21, xt)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> = __rocq_global_1429.with(Clone::clone);
  v0
}
const __rocq_global_196: u64 = 65536u64;
const __rocq_global_276: u64 = 1048576u64;
std::thread_local! { static __rocq_global_1429: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>> = doublets(); }
std::thread_local! { static __rocq_global_1432: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>>>>>> = doublets_curried(); }