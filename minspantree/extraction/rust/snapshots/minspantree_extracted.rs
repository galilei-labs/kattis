// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

pub type sint = u64;

// Rocq: Minspantree.minspantree_implem.mst
// Variant: uncurried
pub fn mst() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>> = mst_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> = Rc::new(v0);
  v1
}

// Rocq: Minspantree.minspantree_implem.mst
pub fn mst_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>> = mst_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>>> = Rc::new(v0);
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

// Rocq: Minspantree.minspantree_implem.bdec
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

// Rocq: Minspantree.minspantree_implem.find
// Variant: uncurried
pub fn find_1(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64) -> u64 {
  find(par, rk, v, ())
}

// Rocq: Minspantree.minspantree_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64, _H: ()) -> u64 {
  let v4 = &par;
  let u = rocq_array::get::<u64>(&v4, v);
  match eqb(u, v) {
    true => {
      std::mem::drop(rk);
      std::mem::drop(par);
      v
    },
    false => {
      let v19 = &rk;
      let v22 = rocq_array::get::<u64>(&v19, v);
      let v23 = &rk;
      let v26 = rocq_array::get::<u64>(&v23, u);
      let v32 = ltb(v22, v26);
      match bdec(v32) {
        sumbool::left => {
          find(par, rk, u, ())
        },
        sumbool::right => {
          std::mem::drop(rk);
          std::mem::drop(par);
          v
        },
      }
    },
  }
}

// Rocq: Minspantree.minspantree_implem.findr
// Variant: uncurried
pub fn findr(par: Rc<Array<u64>>, rk: Rc<Array<u64>>, v: u64) -> u64 {
  find_1(par, rk, v)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Minspantree.minspantree_implem.scan
// Variant: uncurried
pub fn scan_1(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, ord: Rc<Array<u64>>, m: u64, q: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<u64>>, cnt: u64, cost: u64) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  scan(n, us, vs, ws, ord, m, q, par, rk, out, cnt, cost, ())
}

// Rocq: Minspantree.minspantree_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, ord: Rc<Array<u64>>, m: u64, q: u64, par: Rc<Array<u64>>, rk: Rc<Array<u64>>, out: Rc<Array<u64>>, cnt: u64, cost: u64, _H: ()) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  let v20 = ltb(q, m);
  match bdec(v20) {
    sumbool::left => {
      let v24 = &ord;
      let e = rocq_array::get::<u64>(&v24, q);
      let v29 = &us;
      let v32 = rocq_array::get::<u64>(&v29, e);
      let v35 = Rc::clone(&par);
      let v38 = Rc::clone(&rk);
      let a = findr(v35, v38, v32);
      let v43 = &vs;
      let v46 = rocq_array::get::<u64>(&v43, e);
      let v49 = Rc::clone(&par);
      let v52 = Rc::clone(&rk);
      let b = findr(v49, v52, v46);
      match eqb(a, b) {
        true => {
          scan(n, us, vs, ws, ord, m, add(q, 1u64), par, rk, out, cnt, cost, ())
        },
        false => {
          let v103 = &rk;
          let ra = rocq_array::get::<u64>(&v103, a);
          let v107 = &rk;
          let rb = rocq_array::get::<u64>(&v107, b);
          match ltb(ra, rb) {
            true => {
              let v125 = add(q, 1u64);
              let v132 = rocq_array::set::<u64>(par, a, b);
              let v139 = rocq_array::set::<u64>(out, cnt, e);
              let v147 = add(cnt, 1u64);
              let v149 = &ws;
              let v152 = rocq_array::get::<u64>(&v149, e);
              scan(n, us, vs, ws, ord, m, v125, v132, rk, v139, v147, add(cost, v152), ())
            },
            false => {
              match ltb(rb, ra) {
                true => {
                  let v204 = add(q, 1u64);
                  let v211 = rocq_array::set::<u64>(par, b, a);
                  let v218 = rocq_array::set::<u64>(out, cnt, e);
                  let v226 = add(cnt, 1u64);
                  let v228 = &ws;
                  let v231 = rocq_array::get::<u64>(&v228, e);
                  scan(n, us, vs, ws, ord, m, v204, v211, rk, v218, v226, add(cost, v231), ())
                },
                false => {
                  let v276 = add(q, 1u64);
                  let v283 = rocq_array::set::<u64>(par, a, b);
                  let v298 = rocq_array::set::<u64>(rk, b, add(rb, 1u64));
                  let v305 = rocq_array::set::<u64>(out, cnt, e);
                  let v313 = add(cnt, 1u64);
                  let v315 = &ws;
                  let v318 = rocq_array::get::<u64>(&v315, e);
                  scan(n, us, vs, ws, ord, m, v276, v283, v298, v305, v313, add(cost, v318), ())
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      let v373 = sub(n, 1u64);
      match eqb(cnt, v373) {
        true => {
          std::mem::drop(us);
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(ord);
          std::mem::drop(par);
          std::mem::drop(rk);
          Rc::new(option::<(u64, Rc<Array<u64>>)>::Some((cost, out)))
        },
        false => {
          std::mem::drop(us);
          std::mem::drop(vs);
          std::mem::drop(ws);
          std::mem::drop(ord);
          std::mem::drop(par);
          std::mem::drop(rk);
          std::mem::drop(out);
          Rc::new(option::<(u64, Rc<Array<u64>>)>::None)
        },
      }
    },
  }
}

// Rocq: Minspantree.minspantree_implem.step_end
// Variant: uncurried
pub fn step_end(m: u64, w: u64, x: u64) -> u64 {
  let v9 = sub(m, x);
  match ltb(w, v9) {
    true => {
      add(x, w)
    },
    false => {
      m
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Minspantree.minspantree_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, iend: u64, jend: u64, kend: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop(ws, src, iend, jend, kend, i, j, k, dst, ())
}

// Rocq: Minspantree.minspantree_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, iend: u64, jend: u64, kend: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = ltb(k, kend);
  match bdec(v17) {
    sumbool::left => {
      let v27 = match ltb(i, iend) {
        true => {
          match ltb(j, jend) {
            true => {
              let v36 = &src;
              let v39 = rocq_array::get::<u64>(&v36, i);
              let v40 = &ws;
              let v43 = rocq_array::get::<u64>(&v40, v39);
              let v44 = &src;
              let v47 = rocq_array::get::<u64>(&v44, j);
              let v48 = &ws;
              let v51 = rocq_array::get::<u64>(&v48, v47);
              lesb(v43, v51)
            },
            false => {
              true
            },
          }
        },
        false => {
          false
        },
      };
      match v27 {
        true => {
          let v79 = add(i, 1u64);
          let v87 = add(k, 1u64);
          let v88 = &src;
          let v91 = rocq_array::get::<u64>(&v88, i);
          let v98 = rocq_array::set::<u64>(dst, k, v91);
          merge_loop(ws, src, iend, jend, kend, v79, j, v87, v98, ())
        },
        false => {
          let v132 = add(j, 1u64);
          let v140 = add(k, 1u64);
          let v141 = &src;
          let v144 = rocq_array::get::<u64>(&v141, j);
          let v151 = rocq_array::set::<u64>(dst, k, v144);
          merge_loop(ws, src, iend, jend, kend, i, v132, v140, v151, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.pass_loop
// Variant: uncurried
pub fn pass_loop_1(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pass_loop(ws, src, m, w, lo, dst, ())
}

// Rocq: Minspantree.minspantree_implem.pass_loop (local: pass_loop)
// Variant: uncurried, lifted
pub fn pass_loop(ws: Rc<Array<u64>>, src: Rc<Array<u64>>, m: u64, w: u64, lo: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(lo, m);
  match bdec(v14) {
    sumbool::left => {
      let mid = step_end(m, w, lo);
      let hi = step_end(m, w, mid);
      let v41 = ltb(lo, hi);
      match bdec(v41) {
        sumbool::left => {
          let v48 = Rc::clone(&ws);
          let v51 = Rc::clone(&src);
          let v66 = merge_loop_1(v48, v51, mid, hi, hi, lo, mid, lo, dst);
          pass_loop(ws, src, m, w, hi, v66, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(src);
          dst
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Minspantree.minspantree_implem.sort_loop
// Variant: uncurried
pub fn sort_loop_1(ws: Rc<Array<u64>>, m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sort_loop(ws, m, w, src, dst, ())
}

// Rocq: Minspantree.minspantree_implem.sort_loop (local: sort_loop)
// Variant: uncurried, lifted
pub fn sort_loop(ws: Rc<Array<u64>>, m: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(w, m);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(w, w);
      let v30 = ltb(w, v24);
      match bdec(v30) {
        sumbool::left => {
          let v39 = add(w, w);
          let v45 = Rc::clone(&ws);
          let v48 = Rc::clone(&src);
          let v57 = pass_loop_1(v45, v48, m, w, 0u64, dst);
          sort_loop(ws, m, v39, v57, src, ())
        },
        sumbool::right => {
          std::mem::drop(ws);
          std::mem::drop(dst);
          src
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ws);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(m: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota_loop(m, i, a, ())
}

// Rocq: Minspantree.minspantree_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(m: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, m);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v29 = rocq_array::set::<u64>(a, i, i);
      iota_loop(m, v22, v29, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Minspantree.minspantree_implem.iota
pub fn iota(m: u64) -> Rc<Array<u64>> {
  let v10 = rocq_array::make::<u64>(m, 0u64);
  iota_loop_1(m, 0u64, v10)
}

// Rocq: Minspantree.minspantree_implem.sort_edges
// Variant: uncurried
pub fn sort_edges(ws: Rc<Array<u64>>, m: u64) -> Rc<Array<u64>> {
  let v8 = iota(m);
  let v15 = rocq_array::make::<u64>(m, 0u64);
  sort_loop_1(ws, m, 1u64, v8, v15)
}

// Rocq: Minspantree.minspantree_implem.mst_impl
// Variant: uncurried
pub fn mst_impl(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>> {
  let v4 = &us;
  let m = rocq_array::length::<u64>(&v4);
  let v10 = Rc::clone(&ws);
  let v13 = sort_edges(v10, m);
  let v19 = iota(n);
  let v26 = rocq_array::make::<u64>(n, 0u64);
  let v41 = rocq_array::make::<u64>(sub(n, 1u64), 0u64);
  scan_1(n, us, vs, ws, v13, m, 0u64, v19, v26, v41, 0u64, 0u64)
}

// Rocq: Minspantree.minspantree_implem.mst_impl
pub fn mst_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>> {
  let v3 = {
    move |us: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |vs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> {
          let n = &v8;
          let us = &us;
          let v18 = Clone::clone(n);
          let v20 = Rc::clone(us);
          let v23 = {
            move |ws: Rc<Array<u64>>| -> Rc<option<(u64, Rc<Array<u64>>)>> {
              let v33 = Clone::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&vs);
              mst_impl(v33, v35, v37, ws)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> = __rocq_global_641.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_641: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>> = mst(); }
std::thread_local! { static __rocq_global_644: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<option<(u64, Rc<Array<u64>>)>>>>>> = mst_curried(); }