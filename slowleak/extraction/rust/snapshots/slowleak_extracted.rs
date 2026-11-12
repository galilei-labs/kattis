// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

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

pub type uint = u64;

// Rocq: Slowleak.slowleak_implem.INF
pub fn INF() -> u64 {
  2305843009213693952u64
}

// Rocq: Slowleak.slowleak_implem.slowleak
// Variant: uncurried
pub fn slowleak() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> {
  let v0: fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>> = slowleak_impl;
  let v1: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Slowleak.slowleak_implem.slowleak
pub fn slowleak_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> = slowleak_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> = Rc::new(v0);
  v1
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

// Rocq: Slowleak.slowleak_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.diag_loop
// Variant: uncurried
pub fn diag_loop_1(n: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  diag_loop(n, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.diag_loop (local: diag_loop)
// Variant: uncurried, lifted
pub fn diag_loop(n: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v43 = rocq_array::set::<u64>(T, add(mul(i, n), i), 0u64);
      diag_loop(n, v22, v43, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.setmin
// Variant: uncurried
pub fn setmin(T: Rc<Array<u64>>, p: u64, s: u64) -> Rc<Array<u64>> {
  let v4 = &T;
  let v7 = rocq_array::get::<u64>(&v4, p);
  match ltb(s, v7) {
    true => {
      rocq_array::set::<u64>(T, p, s)
    },
    false => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.edge_loop
// Variant: uncurried
pub fn edge_loop_1(n: u64, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>, m: u64, e: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  edge_loop(n, xi, xj, xk, m, e, T, ())
}

// Rocq: Slowleak.slowleak_implem.edge_loop (local: edge_loop)
// Variant: uncurried, lifted
pub fn edge_loop(n: u64, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>, m: u64, e: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(e, m);
  match bdec(v15) {
    sumbool::left => {
      let v20 = &xi;
      let v23 = rocq_array::get::<u64>(&v20, e);
      let u = sub(v23, 1u64);
      let v32 = &xj;
      let v35 = rocq_array::get::<u64>(&v32, e);
      let v = sub(v35, 1u64);
      let v43 = &xk;
      let k = rocq_array::get::<u64>(&v43, e);
      let v54 = add(e, 1u64);
      let v75 = setmin(T, add(mul(u, n), v), k);
      let v94 = setmin(v75, add(mul(v, n), u), k);
      edge_loop(n, xi, xj, xk, m, v54, v94, ())
    },
    sumbool::right => {
      std::mem::drop(xi);
      std::mem::drop(xj);
      std::mem::drop(xk);
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_j
// Variant: uncurried
pub fn fw_j_1(n: u64, rowi: u64, rowk: u64, aik: u64, j: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_j(n, rowi, rowk, aik, j, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_j (local: fw_j)
// Variant: uncurried, lifted
pub fn fw_j(n: u64, rowi: u64, rowk: u64, aik: u64, j: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(j, n);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(j, 1u64);
      let v32 = add(rowi, j);
      let v39 = add(rowk, j);
      let v40 = &T;
      let v43 = rocq_array::get::<u64>(&v40, v39);
      let v55 = setmin(T, v32, add(aik, v43));
      fw_j(n, rowi, rowk, aik, v25, v55, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_i
// Variant: uncurried
pub fn fw_i_1(n: u64, k: u64, rowk: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_i(n, k, rowk, i, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_i (local: fw_i)
// Variant: uncurried, lifted
pub fn fw_i(n: u64, k: u64, rowk: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let rowi = mul(i, n);
      let v30 = add(i, 1u64);
      let v37 = add(rowi, k);
      let v38 = &T;
      let v41 = rocq_array::get::<u64>(&v38, v37);
      let v56 = fw_j_1(n, rowi, rowk, v41, 0u64, T);
      fw_i(n, k, rowk, v30, v56, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.fw_k
// Variant: uncurried
pub fn fw_k_1(n: u64, k: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fw_k(n, k, T, ())
}

// Rocq: Slowleak.slowleak_implem.fw_k (local: fw_k)
// Variant: uncurried, lifted
pub fn fw_k(n: u64, k: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(k, n);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(k, 1u64);
      let v29 = mul(k, n);
      let v42 = fw_i_1(n, k, v29, 0u64, T);
      fw_k(n, v22, v42, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Slowleak.slowleak_implem.vx_loop
// Variant: uncurried
pub fn vx_loop_1(xs: Rc<Array<u64>>, t: u64, i: u64, V: Rc<Array<u64>>) -> Rc<Array<u64>> {
  vx_loop(xs, t, i, V, ())
}

// Rocq: Slowleak.slowleak_implem.vx_loop (local: vx_loop)
// Variant: uncurried, lifted
pub fn vx_loop(xs: Rc<Array<u64>>, t: u64, i: u64, V: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, t);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v31 = add(i, 1u64);
      let v33 = &xs;
      let v36 = rocq_array::get::<u64>(&v33, i);
      let v50 = rocq_array::set::<u64>(V, v31, sub(v36, 1u64));
      vx_loop(xs, t, v23, v50, ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      V
    },
  }
}

// Rocq: Slowleak.slowleak_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(M: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, i: u64, b: u64, bv: u64) -> u64 {
  sel_loop(M, vis, dist, i, b, bv, ())
}

// Rocq: Slowleak.slowleak_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(M: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, i: u64, b: u64, bv: u64, _H: ()) -> u64 {
  let v14 = ltb(i, M);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &vis;
      let v21 = rocq_array::get::<bool>(&v18, i);
      match v21 {
        true => {
          sel_loop(M, vis, dist, add(i, 1u64), b, bv, ())
        },
        false => {
          let v51 = &dist;
          let di = rocq_array::get::<u64>(&v51, i);
          match ltb(di, bv) {
            true => {
              sel_loop(M, vis, dist, add(i, 1u64), i, di, ())
            },
            false => {
              sel_loop(M, vis, dist, add(i, 1u64), b, bv, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(vis);
      std::mem::drop(dist);
      b
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Slowleak.slowleak_implem.rel_loop
// Variant: uncurried
pub fn rel_loop_1(M: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, vis: Rc<Array<bool>>, d: u64, ru: u64, du: u64, b: u64, dist: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rel_loop(M, V, T, vis, d, ru, du, b, dist, ())
}

// Rocq: Slowleak.slowleak_implem.rel_loop (local: rel_loop)
// Variant: uncurried, lifted
pub fn rel_loop(M: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, vis: Rc<Array<bool>>, d: u64, ru: u64, du: u64, b: u64, dist: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = ltb(b, M);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &vis;
      let v24 = rocq_array::get::<bool>(&v21, b);
      let dist_ = match v24 {
        true => {
          dist
        },
        false => {
          let v29 = &V;
          let v32 = rocq_array::get::<u64>(&v29, b);
          let v37 = add(ru, v32);
          let v38 = &T;
          let w = rocq_array::get::<u64>(&v38, v37);
          match leb(w, d) {
            true => {
              setmin(dist, b, add(du, w))
            },
            false => {
              dist
            },
          }
        },
      };
      rel_loop(M, V, T, vis, d, ru, du, add(b, 1u64), dist_, ())
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      dist
    },
  }
}

// Rocq: Slowleak.slowleak_implem.dij_loop
// Variant: uncurried
pub fn dij_loop_1(n: u64, M: u64, tgt: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, d: u64, r: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>) -> Rc<option<u64>> {
  dij_loop(n, M, tgt, V, T, d, r, vis, dist, ())
}

// Rocq: Slowleak.slowleak_implem.dij_loop (local: dij_loop)
// Variant: uncurried, lifted
pub fn dij_loop(n: u64, M: u64, tgt: u64, V: Rc<Array<u64>>, T: Rc<Array<u64>>, d: u64, r: u64, vis: Rc<Array<bool>>, dist: Rc<Array<u64>>, _H: ()) -> Rc<option<u64>> {
  let v19 = ltb(0u64, r);
  match bdec(v19) {
    sumbool::left => {
      let v31 = Rc::clone(&vis);
      let v34 = Rc::clone(&dist);
      let u = sel_loop_1(M, v31, v34, 0u64, M, __rocq_global_110);
      match eqb(u, M) {
        true => {
          std::mem::drop(V);
          std::mem::drop(T);
          std::mem::drop(vis);
          std::mem::drop(dist);
          Rc::new(option::<u64>::None)
        },
        false => {
          match eqb(u, tgt) {
            true => {
              std::mem::drop(V);
              std::mem::drop(T);
              std::mem::drop(vis);
              let v61 = &dist;
              let v64 = rocq_array::get::<u64>(&v61, u);
              std::mem::drop(dist);
              Rc::new(option::<u64>::Some(v64))
            },
            false => {
              let vis_ = rocq_array::set::<bool>(vis, u, true);
              let v83 = &V;
              let v87 = rocq_array::get::<u64>(&v83, u);
              let v91 = mul(v87, n);
              let v92 = &dist;
              let v95 = rocq_array::get::<u64>(&v92, u);
              let v102 = Rc::clone(&V);
              let v105 = Rc::clone(&T);
              let v108 = Rc::clone(&vis_);
              let dist_ = rel_loop_1(M, v102, v105, v108, d, v91, v95, 0u64, dist);
              dij_loop(n, M, tgt, V, T, d, sub(r, 1u64), vis_, dist_, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(T);
      std::mem::drop(vis);
      std::mem::drop(dist);
      Rc::new(option::<u64>::None)
    },
  }
}

// Rocq: Slowleak.slowleak_implem.slowleak_impl
// Variant: uncurried
pub fn slowleak_impl(x: u64, y: u64, xs: Rc<Array<u64>>, xi: Rc<Array<u64>>, xj: Rc<Array<u64>>, xk: Rc<Array<u64>>) -> Rc<option<u64>> {
  let v20 = rocq_array::make::<u64>(mul(x, x), __rocq_global_110);
  let T0 = diag_loop_1(x, 0u64, v20);
  let v28 = &xi;
  let m = rocq_array::length::<u64>(&v28);
  let T1 = edge_loop_1(x, xi, xj, xk, m, 0u64, T0);
  let T = fw_k_1(x, 0u64, T1);
  let v58 = &xs;
  let t = rocq_array::length::<u64>(&v58);
  let M = add(t, 2u64);
  let v77 = rocq_array::make::<u64>(M, 0u64);
  let v100 = rocq_array::set::<u64>(v77, add(t, 1u64), sub(x, 1u64));
  let V = vx_loop_1(xs, t, 0u64, v100);
  let v118 = add(t, 1u64);
  let v125 = rocq_array::make::<bool>(M, false);
  let v131 = rocq_array::make::<u64>(M, __rocq_global_110);
  let v142 = rocq_array::set::<u64>(v131, 0u64, 0u64);
  dij_loop_1(x, M, v118, V, T, y, M, v125, v142)
}

// Rocq: Slowleak.slowleak_implem.slowleak_impl
pub fn slowleak_impl_curried(x: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> {
  let v3 = {
    move |y: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>> {
      let x = &x;
      let v8 = Clone::clone(x);
      let v11 = {
        move |xs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>> {
          let x = &v8;
          let y = &y;
          let v18 = Clone::clone(x);
          let v20 = Clone::clone(y);
          let v23 = {
            move |xi: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>> {
              let x = &v18;
              let y = &v20;
              let xs = &xs;
              let v32 = Clone::clone(x);
              let v34 = Clone::clone(y);
              let v36 = Rc::clone(xs);
              let v39 = {
                move |xj: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>> {
                  let x = &v32;
                  let y = &v34;
                  let xs = &v36;
                  let xi = &xi;
                  let v50 = Clone::clone(x);
                  let v52 = Clone::clone(y);
                  let v54 = Rc::clone(xs);
                  let v56 = Rc::clone(xi);
                  let v59 = {
                    move |xk: Rc<Array<u64>>| -> Rc<option<u64>> {
                      let v73 = Clone::clone(&v50);
                      let v75 = Clone::clone(&v52);
                      let v77 = Rc::clone(&v54);
                      let v79 = Rc::clone(&v56);
                      let v81 = Rc::clone(&xj);
                      slowleak_impl(v73, v75, v77, v79, v81, xk)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> {
  let v0: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = __rocq_global_783.with(Clone::clone);
  v0
}
const __rocq_global_110: u64 = 2305843009213693952u64;
std::thread_local! { static __rocq_global_783: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<u64>>> = slowleak(); }
std::thread_local! { static __rocq_global_786: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<u64>>>>>>>> = slowleak_curried(); }