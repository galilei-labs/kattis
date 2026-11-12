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

pub type uint = u64;

// Rocq: Indoorienteering.indoorienteering_implem.hmul
pub fn hmul() -> u64 {
  7046029254386353131u64
}

// Rocq: Indoorienteering.indoorienteering_implem.indoorienteering
// Variant: uncurried
pub fn indoorienteering() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool> {
  let v0: fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool = indoor_owned;
  let v1: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool> = Rc::new(v0);
  v1
}

// Rocq: Indoorienteering.indoorienteering_implem.indoorienteering
pub fn indoorienteering_curried() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(u64) -> bool>> {
  let v0: fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(u64) -> bool> = indoor_curried_owned;
  let v1: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(u64) -> bool>> = Rc::new(v0);
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

// Rocq: Indoorienteering.indoorienteering_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Indoorienteering.indoorienteering_implem.fill
// Variant: uncurried
pub fn fill_1(x: Rc<Array<Rc<Array<u64>>>>, n: u64, N: u64, i: u64, D: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill(x, n, N, i, D, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(x: Rc<Array<Rc<Array<u64>>>>, n: u64, N: u64, i: u64, D: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, N);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(i, 1u64);
      let v30 = div(i, n);
      let v33 = Rc::clone(&x);
      let v37 = rocq_array::get::<Rc<Array<u64>>>(&v33, v30);
      std::mem::drop(v33);
      let v43 = mod_(i, n);
      let v44 = &v37;
      let v47 = rocq_array::get::<u64>(&v44, v43);
      std::mem::drop(v37);
      let v54 = rocq_array::set::<u64>(D, i, v47);
      fill(x, n, N, v24, v54, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      D
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Indoorienteering.indoorienteering_implem.logcap
pub fn logcap(n: u64) -> u64 {
  match leb(n, 8u64) {
    true => {
      7u64
    },
    false => {
      match eqb(n, 9u64) {
        true => {
          9u64
        },
        false => {
          match eqb(n, 10u64) {
            true => {
              11u64
            },
            false => {
              match eqb(n, 11u64) {
                true => {
                  13u64
                },
                false => {
                  match eqb(n, 12u64) {
                    true => {
                      15u64
                    },
                    false => {
                      match eqb(n, 13u64) {
                        true => {
                          17u64
                        },
                        false => {
                          20u64
                        },
                      }
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor
// Variant: uncurried
pub fn lxor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lxor(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
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

// Rocq: Indoorienteering.indoorienteering_implem.find
// Variant: uncurried
pub fn find_1(t: Rc<Array<u64>>, k: u64, i: u64) -> u64 {
  find(t, k, i, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(t: Rc<Array<u64>>, k: u64, i: u64, _H: ()) -> u64 {
  let v6 = &t;
  let v7 = rocq_array::length::<u64>(&v6);
  let v13 = ltb(i, v7);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &t;
      let x = rocq_array::get::<u64>(&v17, i);
      let v29 = eqb(x, 0u64);
      let v35 = eqb(x, k);
      match orb(v29, v35) {
        true => {
          std::mem::drop(t);
          i
        },
        false => {
          find(t, k, add(i, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      i
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.hidx
// Variant: uncurried
pub fn hidx(sh: u64, k: u64) -> u64 {
  lsr(mul(k, __rocq_global_342), sh)
}

// Rocq: Indoorienteering.indoorienteering_implem.find0
// Variant: uncurried
pub fn find0(sh: u64, t: Rc<Array<u64>>, k: u64) -> u64 {
  let v9 = hidx(sh, k);
  find_1(t, k, v9)
}

// Rocq: Indoorienteering.indoorienteering_implem.insert
// Variant: uncurried
pub fn insert(sh: u64, t: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, bool) {
  let v8 = Rc::clone(&t);
  let j = find0(sh, v8, k);
  let v13 = &t;
  let v14 = rocq_array::length::<u64>(&v13);
  match ltb(j, v14) {
    true => {
      let v22 = &t;
      let v25 = rocq_array::get::<u64>(&v22, j);
      match eqb(v25, 0u64) {
        true => {
          let v40 = rocq_array::set::<u64>(t, j, k);
          (v40, true)
        },
        false => {
          (t, true)
        },
      }
    },
    false => {
      (t, false)
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.lookup
// Variant: uncurried
pub fn lookup(sh: u64, t: Rc<Array<u64>>, k: u64) -> bool {
  let v8 = Rc::clone(&t);
  let j = find0(sh, v8, k);
  let v14 = &t;
  let v15 = rocq_array::length::<u64>(&v14);
  let v20 = ltb(j, v15);
  let v22 = &t;
  let v25 = rocq_array::get::<u64>(&v22, j);
  std::mem::drop(t);
  andb(v20, eqb(v25, k))
}

// Rocq: Indoorienteering.indoorienteering_implem.key
// Variant: uncurried
pub fn key(S: u64, l: u64) -> u64 {
  let v16 = add(lsl(S, 50u64), l);
  add(v16, 1u64)
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs
// Variant: uncurried
pub fn pdfs_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, base2: u64, sh: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64) -> bool {
  pdfs(n, a, D, L, base2, sh, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs (local: pdfs)
// Variant: uncurried, lifted
pub fn pdfs(n: u64, a: u64, D: Rc<Array<u64>>, L: u64, base2: u64, sh: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64, _H: ()) -> bool {
  let v22 = eqb(r, 0u64);
  match bdec(v22) {
    sumbool::left => {
      let v38 = add(mul(c, n), a);
      let v39 = &D;
      let v42 = rocq_array::get::<u64>(&v39, v38);
      let l = add(len, v42);
      match leb(l, L) {
        true => {
          std::mem::drop(D);
          lookup(sh, t, key(lxor(base2, free), sub(L, l)))
        },
        false => {
          std::mem::drop(t);
          std::mem::drop(D);
          false
        },
      }
    },
    sumbool::right => {
      let v97 = ltb(v, n);
      match bdec(v97) {
        sumbool::left => {
          let bv = lsl(1u64, v);
          let v115 = land(free, bv);
          match eqb(v115, 0u64) {
            true => {
              pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
            },
            false => {
              let v176 = add(mul(c, n), v);
              let v177 = &D;
              let v180 = rocq_array::get::<u64>(&v177, v176);
              let l = add(len, v180);
              match leb(l, L) {
                true => {
                  let v198 = lxor(free, bv);
                  let v206 = sub(r, 1u64);
                  let v218 = Rc::clone(&D);
                  let v227 = Rc::clone(&t);
                  match pdfs(n, a, v218, L, base2, sh, v227, v, v198, l, v206, 0u64, ()) {
                    true => {
                      std::mem::drop(t);
                      std::mem::drop(D);
                      true
                    },
                    false => {
                      pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
                    },
                  }
                },
                false => {
                  pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
                },
              }
            },
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          std::mem::drop(t);
          false
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Indoorienteering.indoorienteering_implem.leafins
// Variant: uncurried
pub fn leafins(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, m: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, t: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, bool) {
  let v19 = insert(sh, t, k);
  match v19 {
    (v21, v23) => {
      let b = &v21;
      match v23 {
        true => {
          std::mem::drop(D);
          (v21, false)
        },
        false => {
          let v55 = Rc::clone(b);
          match pdfs_1(D, n, L, a, base2, sh, v55, m, fr2, 0u64, k2, 0u64) {
            true => {
              (v21, true)
            },
            false => {
              std::mem::drop(v21);
              let v86 = rocq_array::make::<u64>(size, 0u64);
              let v96 = fst::<Rc<Array<u64>>, bool>(insert(sh, v86, k));
              (v96, false)
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.idfs
// Variant: uncurried
pub fn idfs_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, m: u64, fp: u64, need: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64) -> (Rc<Array<u64>>, bool) {
  idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.idfs (local: idfs)
// Variant: uncurried, lifted
pub fn idfs(n: u64, m: u64, D: Rc<Array<u64>>, L: u64, fp: u64, a: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, need: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64, _H: ()) -> (Rc<Array<u64>>, bool) {
  let v28 = eqb(r, 0u64);
  match bdec(v28) {
    sumbool::left => {
      let v44 = add(mul(c, n), m);
      let v45 = &D;
      let v48 = rocq_array::get::<u64>(&v45, v44);
      let l = add(len, v48);
      match leb(l, L) {
        true => {
          leafins(D, n, L, a, m, fr2, base2, k2, sh, size, t, key(lxor(fp, free), l))
        },
        false => {
          std::mem::drop(D);
          (t, false)
        },
      }
    },
    sumbool::right => {
      let v121 = ltb(v, n);
      match bdec(v121) {
        sumbool::left => {
          let bv = lsl(1u64, v);
          let v139 = land(free, bv);
          match eqb(v139, 0u64) {
            true => {
              idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
            },
            false => {
              let v208 = eqb(r, 1u64);
              let v232 = negb(eqb(land(need, lxor(free, bv)), 0u64));
              match andb(v208, v232) {
                true => {
                  idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
                },
                false => {
                  let v303 = add(mul(c, n), v);
                  let v304 = &D;
                  let v307 = rocq_array::get::<u64>(&v304, v303);
                  let l = add(len, v307);
                  match leb(l, L) {
                    true => {
                      let v325 = lxor(free, bv);
                      let v333 = sub(r, 1u64);
                      let v345 = Rc::clone(&D);
                      let v378 = idfs(n, m, v345, L, fp, a, fr2, base2, k2, sh, size, need, t, v, v325, l, v333, 0u64, ());
                      match v378 {
                        (v380, v382) => {
                          match v382 {
                            true => {
                              std::mem::drop(D);
                              (v380, true)
                            },
                            false => {
                              idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, v380, c, free, len, r, add(v, 1u64), ())
                            },
                          }
                        },
                      }
                    },
                    false => {
                      idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
                    },
                  }
                },
              }
            },
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          (t, false)
        },
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.search_m
// Variant: uncurried
pub fn search_m(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64) -> bool {
  let fp = lxor(sub(lsl(1u64, a), 1u64), lsl(1u64, m));
  let v55 = eqb(land(n, 1u64), 0u64);
  let v63 = leb(4u64, n);
  let need = match andb(v55, v63) {
    true => {
      let v72 = 1u64;
      let v75 = 0u64;
      let v81 = match eqb(m, v75) {
        true => {
          1u64
        },
        false => {
          0u64
        },
      };
      lsl(v72, v81)
    },
    false => {
      0u64
    },
  };
  let fr2 = lxor(fp, need);
  let v116 = rocq_array::make::<u64>(size, 0u64);
  let v123 = Rc::clone(&D);
  let v158 = idfs_1(v123, n, L, a, m, fp, need, fr2, need, k2, sh, size, v116, a, fp, 0u64, k1, 0u64);
  match v158 {
    (v160, v162) => {
      match v162 {
        true => {
          std::mem::drop(D);
          std::mem::drop(v160);
          true
        },
        false => {
          pdfs_1(D, n, L, a, need, sh, v160, m, fr2, 0u64, k2, 0u64)
        },
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop
// Variant: uncurried
pub fn mloop_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64) -> bool {
  mloop(D, n, L, a, k1, k2, sh, size, m, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64, _H: ()) -> bool {
  let v17 = ltb(m, a);
  match bdec(v17) {
    sumbool::left => {
      let v24 = Rc::clone(&D);
      match search_m(v24, n, L, a, k1, k2, sh, size, m) {
        true => {
          std::mem::drop(D);
          true
        },
        false => {
          mloop(D, n, L, a, k1, k2, sh, size, add(m, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(D);
      false
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.indoor
// Variant: uncurried
pub fn indoor_owned(x: Rc<Array<Rc<Array<u64>>>>, L: u64) -> bool {
  let v2 = &x;
  let n = rocq_array::length::<Rc<Array<u64>>>(&v2);
  let N = mul(n, n);
  let v19 = rocq_array::make::<u64>(N, 0u64);
  let D = fill_1(x, n, N, 0u64, v19);
  let a = sub(n, 1u64);
  let k1 = div(sub(n, 2u64), 2u64);
  let v64 = sub(n, 2u64);
  let k2 = sub(v64, k1);
  let b = logcap(n);
  mloop_1(D, n, L, a, k1, k2, sub(63u64, b), add(lsl(1u64, b), 256u64), 0u64)
}

// Rocq: Indoorienteering.indoorienteering_implem.indoor
// Variant: borrowed, uncurried
pub fn indoor(x: &Rc<Array<Rc<Array<u64>>>>, L: u64) -> bool {
  let L_1 = L;
  let v3 = x;
  let n = rocq_array::length::<Rc<Array<u64>>>(&v3);
  let N = mul(n, n);
  let v20 = rocq_array::make::<u64>(N, 0u64);
  let v23 = Rc::clone(x);
  let D = fill_1(v23, n, N, 0u64, v20);
  let a = sub(n, 1u64);
  let k1 = div(sub(n, 2u64), 2u64);
  let v66 = sub(n, 2u64);
  let k2 = sub(v66, k1);
  let b = logcap(n);
  mloop_1(D, n, L_1, a, k1, k2, sub(63u64, b), add(lsl(1u64, b), 256u64), 0u64)
}

// Rocq: Indoorienteering.indoorienteering_implem.indoor
pub fn indoor_curried_owned(x: Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(u64) -> bool> {
  let v3 = {
    move |L: u64| -> bool {
      indoor(&x, L)
    }
  };
  let v14: Rc<dyn Fn(u64) -> bool> = Rc::new(v3);
  v14
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool> = __rocq_global_1038.with(Clone::clone);
  v0
}
const __rocq_global_342: u64 = 7046029254386353131u64;
std::thread_local! { static __rocq_global_1038: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>, u64) -> bool> = indoorienteering(); }
std::thread_local! { static __rocq_global_1041: Rc<dyn Fn(Rc<Array<Rc<Array<u64>>>>) -> Rc<dyn Fn(u64) -> bool>> = indoorienteering_curried(); }