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

// Rocq: Water.water_implem.big
pub fn big() -> u64 {
  4611686018427387903u64
}

// Rocq: Water.water_implem.budget
pub fn budget() -> u64 {
  1099511627776u64
}

// Rocq: Water.water_implem.water
// Variant: uncurried
pub fn water() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = water_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Water.water_implem.water
pub fn water_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>> = water_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>>> = Rc::new(v0);
  v1
}

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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Water.water_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Water.water_implem.add_pipe
// Variant: uncurried
pub fn add_pipe(m: u64, r: Rc<Array<u64>>, a: u64, b: u64, c: u64) -> Rc<Array<u64>> {
  let i1 = add(mul(a, m), b);
  let v18 = &r;
  let v22 = rocq_array::get::<u64>(&v18, i1);
  let r1 = rocq_array::set::<u64>(r, i1, add(v22, c));
  let i2 = add(mul(b, m), a);
  let v47 = &r1;
  let v51 = rocq_array::get::<u64>(&v47, i2);
  rocq_array::set::<u64>(r1, i2, add(v51, c))
}

// Rocq: Water.water_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, m: u64, p: u64, j: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(pa, pb, pc, m, p, j, r, ())
}

// Rocq: Water.water_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, m: u64, p: u64, j: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(j, p);
  match bdec(v15) {
    sumbool::left => {
      let v26 = add(j, 1u64);
      let v28 = &pa;
      let v31 = rocq_array::get::<u64>(&v28, j);
      let v32 = &pb;
      let v35 = rocq_array::get::<u64>(&v32, j);
      let v36 = &pc;
      let v39 = rocq_array::get::<u64>(&v36, j);
      let v50 = add_pipe(m, r, v31, v35, v39);
      init_loop(pa, pb, pc, m, p, v26, v50, ())
    },
    sumbool::right => {
      std::mem::drop(pa);
      std::mem::drop(pb);
      std::mem::drop(pc);
      r
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

// Rocq: Water.water_implem.scan
// Variant: uncurried
pub fn scan_1(r: Rc<Array<u64>>, m: u64, u: u64, bu: u64, v: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  scan(r, m, u, bu, v, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(r: Rc<Array<u64>>, m: u64, u: u64, bu: u64, v: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  let v17 = ltb(v, m);
  match bdec(v17) {
    sumbool::left => {
      let v32 = add(mul(u, m), v);
      let v33 = &r;
      let x = rocq_array::get::<u64>(&v33, v32);
      let v39 = &par;
      let v42 = rocq_array::get::<u64>(&v39, v);
      let v49 = eqb(v42, 0u64);
      let v57 = ltb(0u64, x);
      match andb(v49, v57) {
        true => {
          let v71 = add(v, 1u64);
          let v78 = rocq_array::set::<u64>(par, v, u);
          let v85 = match ltb(bu, x) {
            true => {
              bu
            },
            false => {
              x
            },
          };
          let v97 = rocq_array::set::<u64>(bott, v, v85);
          let v104 = rocq_array::set::<u64>(q, tail, v);
          scan(r, m, u, bu, v71, v78, v97, v104, add(tail, 1u64), ())
        },
        false => {
          scan(r, m, u, bu, add(v, 1u64), par, bott, q, tail, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      (((par, bott), q), tail)
    },
  }
}

// Rocq: Water.water_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(r: Rc<Array<u64>>, m: u64, head: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  bfs_loop(r, m, head, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(r: Rc<Array<u64>>, m: u64, head: u64, par: Rc<Array<u64>>, bott: Rc<Array<u64>>, q: Rc<Array<u64>>, tail: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v15 = ltb(head, m);
  match bdec(v15) {
    sumbool::left => {
      let v25 = ltb(head, tail);
      let v28 = 2u64;
      let v29 = &par;
      let v32 = rocq_array::get::<u64>(&v29, v28);
      let v39 = eqb(v32, 0u64);
      match andb(v25, v39) {
        true => {
          let v46 = &q;
          let u = rocq_array::get::<u64>(&v46, head);
          let v51 = &bott;
          let v54 = rocq_array::get::<u64>(&v51, u);
          let v59 = Rc::clone(&r);
          let v76 = scan_1(v59, m, u, v54, 1u64, par, bott, q, tail);
          match v76 {
            (v78, v80) => {
              match v78 {
                (v83, v85) => {
                  match v83 {
                    (v88, v90) => {
                      bfs_loop(r, m, add(head, 1u64), v88, v90, v85, v80, ())
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          std::mem::drop(r);
          std::mem::drop(q);
          (par, bott)
        },
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(q);
      (par, bott)
    },
  }
}

// Rocq: Water.water_implem.bfs
// Variant: uncurried
pub fn bfs(r: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v11 = rocq_array::make::<u64>(m, 0u64);
  let v22 = rocq_array::set::<u64>(v11, 1u64, 1u64);
  let v29 = rocq_array::make::<u64>(m, 0u64);
  let v39 = rocq_array::set::<u64>(v29, 1u64, __rocq_global_376);
  let v46 = rocq_array::make::<u64>(m, 0u64);
  let v57 = rocq_array::set::<u64>(v46, 0u64, 1u64);
  bfs_loop_1(r, m, 0u64, v22, v39, v57, 1u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Water.water_implem.walk
// Variant: uncurried
pub fn walk_1(par: Rc<Array<u64>>, m: u64, d: u64, r: Rc<Array<u64>>, cur: u64, i: u64) -> Rc<Array<u64>> {
  walk(par, m, d, r, cur, i, ())
}

// Rocq: Water.water_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(par: Rc<Array<u64>>, m: u64, d: u64, r: Rc<Array<u64>>, cur: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, m);
  match bdec(v14) {
    sumbool::left => {
      match eqb(cur, 1u64) {
        true => {
          std::mem::drop(par);
          r
        },
        false => {
          let v29 = &par;
          let u = rocq_array::get::<u64>(&v29, cur);
          let i1 = add(mul(u, m), cur);
          let v46 = &r;
          let v50 = rocq_array::get::<u64>(&v46, i1);
          let r1 = rocq_array::set::<u64>(r, i1, sub(v50, d));
          let i2 = add(mul(cur, m), u);
          let v75 = &r1;
          let v79 = rocq_array::get::<u64>(&v75, i2);
          let r2 = rocq_array::set::<u64>(r1, i2, add(v79, d));
          walk(par, m, d, r2, u, add(i, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(par);
      r
    },
  }
}

// Rocq: Water.water_implem.augment
// Variant: uncurried
pub fn augment_1(m: u64, B: u64, r: Rc<Array<u64>>, val: u64, i: u64) -> (Rc<Array<u64>>, u64) {
  augment(m, B, r, val, i, ())
}

// Rocq: Water.water_implem.augment (local: augment)
// Variant: uncurried, lifted
pub fn augment(m: u64, B: u64, r: Rc<Array<u64>>, val: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v13 = ltb(i, B);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&r);
      let v23 = bfs(v20, m);
      match v23 {
        (v25, v27) => {
          let bott = &v25;
          let par = &v27;
          let v33 = 2u64;
          let v36 = rocq_array::get::<u64>(&bott, v33);
          match eqb(v36, 0u64) {
            true => {
              std::mem::drop(v25);
              std::mem::drop(v27);
              (r, val)
            },
            false => {
              let v54 = 2u64;
              let d = rocq_array::get::<u64>(&par, v54);
              std::mem::drop(v27);
              let v75 = walk_1(v25, m, d, r, 2u64, 0u64);
              augment(m, B, v75, add(val, d), add(i, 1u64), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      (r, val)
    },
  }
}

// Rocq: Water.water_implem.imp_loop
// Variant: uncurried
pub fn imp_loop_1(ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>, m: u64, k: u64, t: u64, r: Rc<Array<u64>>, val: u64, out: Rc<Array<u64>>) -> Rc<Array<u64>> {
  imp_loop(ia, ib, ic, m, k, t, r, val, out, ())
}

// Rocq: Water.water_implem.imp_loop (local: imp_loop)
// Variant: uncurried, lifted
pub fn imp_loop(ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>, m: u64, k: u64, t: u64, r: Rc<Array<u64>>, val: u64, out: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = ltb(t, k);
  match bdec(v17) {
    sumbool::left => {
      let v22 = &ia;
      let v25 = rocq_array::get::<u64>(&v22, t);
      let v26 = &ib;
      let v29 = rocq_array::get::<u64>(&v26, t);
      let v30 = &ic;
      let v33 = rocq_array::get::<u64>(&v30, t);
      let r1 = add_pipe(m, r, v25, v29, v33);
      let v59 = augment_1(m, __rocq_global_569, r1, val, 0u64);
      match v59 {
        (v61, v63) => {
          let v72 = add(t, 1u64);
          let v87 = rocq_array::set::<u64>(out, add(t, 1u64), v63);
          imp_loop(ia, ib, ic, m, k, v72, v61, v63, v87, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ia);
      std::mem::drop(ib);
      std::mem::drop(ic);
      std::mem::drop(r);
      out
    },
  }
}

// Rocq: Water.water_implem.water_impl
// Variant: uncurried
pub fn water_impl(n: u64, pa: Rc<Array<u64>>, pb: Rc<Array<u64>>, pc: Rc<Array<u64>>, ia: Rc<Array<u64>>, ib: Rc<Array<u64>>, ic: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let m = add(n, 1u64);
  let v15 = &pa;
  let p = rocq_array::length::<u64>(&v15);
  let v32 = rocq_array::make::<u64>(mul(m, m), 0u64);
  let r = init_loop_1(pa, pb, pc, m, p, 0u64, v32);
  let v64 = augment_1(m, __rocq_global_569, r, 0u64, 0u64);
  match v64 {
    (v66, v68) => {
      let v70 = &ia;
      let k = rocq_array::length::<u64>(&v70);
      let v89 = rocq_array::make::<u64>(add(k, 1u64), 0u64);
      let v98 = rocq_array::set::<u64>(v89, 0u64, v68);
      imp_loop_1(ia, ib, ic, m, k, 0u64, v66, v68, v98)
    },
  }
}

// Rocq: Water.water_implem.water_impl
pub fn water_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>> {
  let v3 = {
    move |pa: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |pb: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>> {
          let n = &v8;
          let pa = &pa;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(pa);
          let v23 = {
            move |pc: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> {
              let n = &v18;
              let pa = &v20;
              let pb = &pb;
              let v32 = Clone::clone(n);
              let v34 = Rc::clone(pa);
              let v36 = Rc::clone(pb);
              let v39 = {
                move |ia: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
                  let n = &v32;
                  let pa = &v34;
                  let pb = &v36;
                  let pc = &pc;
                  let v50 = Clone::clone(n);
                  let v52 = Rc::clone(pa);
                  let v54 = Rc::clone(pb);
                  let v56 = Rc::clone(pc);
                  let v59 = {
                    move |ib: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
                      let n = &v50;
                      let pa = &v52;
                      let pb = &v54;
                      let pc = &v56;
                      let ia = &ia;
                      let v72 = Clone::clone(n);
                      let v74 = Rc::clone(pa);
                      let v76 = Rc::clone(pb);
                      let v78 = Rc::clone(pc);
                      let v80 = Rc::clone(ia);
                      let v83 = {
                        move |ic: Rc<Array<u64>>| -> Rc<Array<u64>> {
                          let v99 = Clone::clone(&v72);
                          let v101 = Rc::clone(&v74);
                          let v103 = Rc::clone(&v76);
                          let v105 = Rc::clone(&v78);
                          let v107 = Rc::clone(&v80);
                          let v109 = Rc::clone(&ib);
                          water_impl(v99, v101, v103, v105, v107, v109, ic)
                        }
                      };
                      let v115: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v83);
                      v115
                    }
                  };
                  let v119: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v59);
                  v119
                }
              };
              let v123: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = Rc::new(v39);
              v123
            }
          };
          let v127: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>> = Rc::new(v23);
          v127
        }
      };
      let v131: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>> = Rc::new(v11);
      v131
    }
  };
  let v135: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>> = Rc::new(v3);
  v135
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_716.with(Clone::clone);
  v0
}
const __rocq_global_376: u64 = 4611686018427387903u64;
const __rocq_global_569: u64 = 1099511627776u64;
std::thread_local! { static __rocq_global_716: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = water(); }
std::thread_local! { static __rocq_global_719: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>>>>>> = water_curried(); }