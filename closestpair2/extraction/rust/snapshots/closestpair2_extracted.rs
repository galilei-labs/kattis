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

pub type sint = u64;

pub type uint = u64;

pub type res = ((u64, u64), u64);

// Rocq: Closestpair2.closestpair2_implem.INF
pub fn INF() -> u64 {
  4611686018427387904u64
}

// Rocq: Closestpair2.closestpair2_implem.closestpair
// Variant: uncurried
pub fn closestpair() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64)> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64) = closestpair_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64)> = Rc::new(v0);
  v1
}

// Rocq: Closestpair2.closestpair2_implem.closestpair
pub fn closestpair_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> = closestpair_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)>> = Rc::new(v0);
  v1
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.splits
// Variant: uncurried
pub fn splits(lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)))
}

// Rocq: Closestpair2.closestpair2_implem.bdec
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

// Rocq: Closestpair2.closestpair2_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let v9 = sub(hi, lo);
  add(lo, div(v9, 2u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(key: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop(key, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(key: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(k, hi);
  match bdec(v16) {
    sumbool::left => {
      match ltb(i, mid) {
        true => {
          match leb(hi, j) {
            true => {
              let v41 = add(i, 1u64);
              let v49 = add(k, 1u64);
              let v50 = &src;
              let v53 = rocq_array::get::<u64>(&v50, i);
              let v60 = rocq_array::set::<u64>(dst, k, v53);
              merge_loop(key, src, mid, hi, v41, j, v49, v60, ())
            },
            false => {
              let v86 = &src;
              let v89 = rocq_array::get::<u64>(&v86, i);
              let v90 = &key;
              let v93 = rocq_array::get::<u64>(&v90, v89);
              let v94 = &src;
              let v97 = rocq_array::get::<u64>(&v94, j);
              let v98 = &key;
              let v101 = rocq_array::get::<u64>(&v98, v97);
              match lesb(v93, v101) {
                true => {
                  let v115 = add(i, 1u64);
                  let v123 = add(k, 1u64);
                  let v124 = &src;
                  let v127 = rocq_array::get::<u64>(&v124, i);
                  let v134 = rocq_array::set::<u64>(dst, k, v127);
                  merge_loop(key, src, mid, hi, v115, j, v123, v134, ())
                },
                false => {
                  let v166 = add(j, 1u64);
                  let v174 = add(k, 1u64);
                  let v175 = &src;
                  let v178 = rocq_array::get::<u64>(&v175, j);
                  let v185 = rocq_array::set::<u64>(dst, k, v178);
                  merge_loop(key, src, mid, hi, i, v166, v174, v185, ())
                },
              }
            },
          }
        },
        false => {
          let v223 = add(j, 1u64);
          let v231 = add(k, 1u64);
          let v232 = &src;
          let v235 = rocq_array::get::<u64>(&v232, j);
          let v242 = rocq_array::set::<u64>(dst, k, v235);
          merge_loop(key, src, mid, hi, i, v223, v231, v242, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(key);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.merge
// Variant: uncurried
pub fn merge(key: Rc<Array<u64>>, src: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop_1(key, src, mid, hi, lo, mid, lo, dst)
}

// Rocq: Closestpair2.closestpair2_implem.msort
// Variant: uncurried
pub fn msort_1(xs: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(xs, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(xs: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = splits(lo, hi);
  match bdec(v13) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let v28 = Rc::clone(&xs);
      let v39 = msort(v28, lo, mid, oth, tgt, ());
      match &v39 {
        (t1, o1) => {
          let v47 = ();
          let v51 = Rc::clone(&xs);
          let v57 = Rc::clone(t1);
          let v58 = Rc::clone(o1);
          std::mem::drop(v39);
          let v62 = msort(v51, mid, hi, v57, v58, v47);
          match v62 {
            (v64, v66) => {
              let t2 = &v64;
              let v73 = Rc::clone(t2);
              let v83 = merge(xs, v73, lo, mid, hi, v66);
              (v83, v64)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      let v104 = rocq_array::set::<u64>(tgt, lo, lo);
      (v104, oth)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Closestpair2.closestpair2_implem.bd
pub fn bd(r: ((u64, u64), u64)) -> u64 {
  snd::<(u64, u64), u64>(r)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.near
// Variant: uncurried
pub fn near(xs: Rc<Array<u64>>, xm: u64, b: u64, v: u64) -> bool {
  let v5 = &xs;
  let v8 = rocq_array::get::<u64>(&v5, v);
  std::mem::drop(xs);
  let dx = sub(v8, xm);
  ltb(mul(dx, dx), b)
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop
// Variant: uncurried
pub fn strip_loop_1(xs: Rc<Array<u64>>, xm: u64, b: u64, t: Rc<Array<u64>>, hi: u64, k: u64, c: u64, o: Rc<Array<u64>>) -> (Rc<Array<u64>>, u64) {
  strip_loop(xs, xm, b, t, hi, k, c, o, ())
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop (local: strip_loop)
// Variant: uncurried, lifted
pub fn strip_loop(xs: Rc<Array<u64>>, xm: u64, b: u64, t: Rc<Array<u64>>, hi: u64, k: u64, c: u64, o: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v16 = ltb(k, hi);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &t;
      let v = rocq_array::get::<u64>(&v20, k);
      let v27 = Rc::clone(&xs);
      match near(v27, xm, b, v) {
        true => {
          let v43 = add(k, 1u64);
          let v51 = add(c, 1u64);
          let v58 = rocq_array::set::<u64>(o, c, v);
          strip_loop(xs, xm, b, t, hi, v43, v51, v58, ())
        },
        false => {
          strip_loop(xs, xm, b, t, hi, add(k, 1u64), c, o, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(t);
      (o, c)
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.d2
// Variant: uncurried
pub fn d2(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, a: u64, b: u64) -> u64 {
  let v5 = &xs;
  let v8 = rocq_array::get::<u64>(&v5, a);
  let v9 = &xs;
  let v12 = rocq_array::get::<u64>(&v9, b);
  std::mem::drop(xs);
  let dx = sub(v8, v12);
  let v19 = &ys;
  let v22 = rocq_array::get::<u64>(&v19, a);
  let v23 = &ys;
  let v26 = rocq_array::get::<u64>(&v23, b);
  std::mem::drop(ys);
  let dy = sub(v22, v26);
  add(mul(dx, dx), mul(dy, dy))
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop
// Variant: uncurried
pub fn inner_loop_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, t: u64, r: ((u64, u64), u64)) -> ((u64, u64), u64) {
  inner_loop(xs, ys, T, e, s, t, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop (local: inner_loop)
// Variant: uncurried, lifted
pub fn inner_loop(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, t: u64, r: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let v15 = ltb(t, e);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &T;
      let a = rocq_array::get::<u64>(&v19, s);
      let v23 = &T;
      let b = rocq_array::get::<u64>(&v23, t);
      let v28 = &ys;
      let v31 = rocq_array::get::<u64>(&v28, b);
      let v32 = &ys;
      let v35 = rocq_array::get::<u64>(&v32, a);
      let dy = sub(v31, v35);
      let v47 = mul(dy, dy);
      let v50 = Clone::clone(&r);
      let v52 = bd(v50);
      match ltb(v47, v52) {
        true => {
          let v62 = Rc::clone(&xs);
          let v65 = Rc::clone(&ys);
          let d = d2(v62, v65, a, b);
          let v78 = add(t, 1u64);
          let v82 = Clone::clone(&r);
          let v84 = bd(v82);
          let v90 = match ltb(d, v84) {
            true => {
              std::mem::drop(r);
              ((a, b), d)
            },
            false => {
              r
            },
          };
          inner_loop(xs, ys, T, e, s, v78, v90, ())
        },
        false => {
          std::mem::drop(xs);
          std::mem::drop(T);
          std::mem::drop(ys);
          r
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop
// Variant: uncurried
pub fn outer_loop_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, r: ((u64, u64), u64)) -> ((u64, u64), u64) {
  outer_loop(xs, ys, T, e, s, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop (local: outer_loop)
// Variant: uncurried, lifted
pub fn outer_loop(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, r: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let v14 = ltb(s, e);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(s, 1u64);
      let v34 = add(s, 1u64);
      let v37 = Rc::clone(&xs);
      let v40 = Rc::clone(&ys);
      let v43 = Rc::clone(&T);
      let v52 = inner_loop_1(v37, v40, v43, e, s, v34, r);
      outer_loop(xs, ys, T, e, v25, v52, ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.solve
// Variant: uncurried
pub fn solve_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, P: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), ((u64, u64), u64)) {
  solve(xs, ys, P, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.solve (local: solve)
// Variant: uncurried, lifted
pub fn solve(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, P: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), ((u64, u64), u64)) {
  let v15 = splits(lo, hi);
  match bdec(v15) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let v30 = Rc::clone(&xs);
      let v33 = Rc::clone(&ys);
      let v36 = Rc::clone(&P);
      let v47 = solve(v30, v33, v36, lo, mid, oth, tgt, ());
      match v47 {
        (v49, v51) => {
          let p = &v51;
          match v49 {
            (v55, v57) => {
              let v64 = Rc::clone(&xs);
              let v67 = Rc::clone(&ys);
              let v70 = Rc::clone(&P);
              let v81 = solve(v64, v67, v70, mid, hi, v55, v57, ());
              match v81 {
                (v83, v85) => {
                  let p_1 = &v85;
                  match v83 {
                    (v89, v91) => {
                      let t2 = &v89;
                      let v97 = Rc::clone(&ys);
                      let v99 = Rc::clone(t2);
                      let t3 = merge(v97, v99, lo, mid, hi, v91);
                      let v111 = Clone::clone(p_1);
                      let v113 = bd(v111);
                      let v115 = Clone::clone(p);
                      let v117 = bd(v115);
                      let r0 = match ltb(v113, v117) {
                        true => {
                          std::mem::drop(v51);
                          v85
                        },
                        false => {
                          std::mem::drop(v85);
                          v51
                        },
                      };
                      let v130 = &P;
                      let v133 = rocq_array::get::<u64>(&v130, mid);
                      std::mem::drop(P);
                      let v134 = &xs;
                      let v137 = rocq_array::get::<u64>(&v134, v133);
                      let v140 = Clone::clone(&r0);
                      let v142 = bd(v140);
                      let v145 = Rc::clone(&xs);
                      let v152 = Rc::clone(&t3);
                      let v159 = Rc::clone(t2);
                      std::mem::drop(v89);
                      let v161 = strip_loop_1(v145, v137, v142, v152, hi, lo, lo, v159);
                      match v161 {
                        (v163, v165) => {
                          let e = &v163;
                          let v171 = Rc::clone(e);
                          ((t3, v171), outer_loop_1(xs, ys, v163, v165, lo, r0))
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
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      let v211 = &P;
      let v214 = rocq_array::get::<u64>(&v211, lo);
      std::mem::drop(P);
      let v222 = rocq_array::set::<u64>(tgt, lo, v214);
      ((v222, oth), ((0u64, 0u64), __rocq_global_643))
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Closestpair2.closestpair2_implem.closestpair_impl
// Variant: uncurried
pub fn closestpair_impl(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>) -> (u64, u64) {
  let v2 = &xs;
  let n = rocq_array::length::<u64>(&v2);
  let v13 = rocq_array::make::<u64>(n, 0u64);
  let v20 = rocq_array::make::<u64>(n, 0u64);
  let v23 = Rc::clone(&xs);
  let v32 = msort_1(v23, 0u64, n, v13, v20);
  match &v32 {
    (A, P) => {
      let v41 = 0u64;
      let v48 = rocq_array::make::<u64>(n, 0u64);
      let v54 = Rc::clone(A);
      let v59 = Rc::clone(P);
      std::mem::drop(v32);
      let v63 = solve_1(xs, ys, v54, v41, n, v59, v48);
      match v63 {
        (v65, v67) => {
          std::mem::drop(v65);
          fst::<(u64, u64), u64>(v67)
        },
      }
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.closestpair_impl
pub fn closestpair_impl_curried(xs: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> {
  let v3 = {
    move |ys: Rc<Array<u64>>| -> (u64, u64) {
      let v9 = Rc::clone(&xs);
      closestpair_impl(v9, ys)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64)> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64)> = __rocq_global_785.with(Clone::clone);
  v0
}
const __rocq_global_643: u64 = 4611686018427387904u64;
std::thread_local! { static __rocq_global_785: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, u64)> = closestpair(); }
std::thread_local! { static __rocq_global_788: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)>> = closestpair_curried(); }