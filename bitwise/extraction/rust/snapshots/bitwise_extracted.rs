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

// Rocq: Bitwise.bitwise_implem.best_and
// Variant: uncurried
pub fn best_and() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, Rc<Array<u64>>) -> u64 = best_and_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Bitwise.bitwise_implem.best_and
pub fn best_and_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> = best_and_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v0);
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

// Rocq: Bitwise.bitwise_implem.bdec
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

// Rocq: Bitwise.bitwise_implem.init_ptr
// Variant: uncurried
pub fn init_ptr_1(m: u64, x: u64, P: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_ptr(m, x, P, ())
}

// Rocq: Bitwise.bitwise_implem.init_ptr (local: init_ptr)
// Variant: uncurried, lifted
pub fn init_ptr(m: u64, x: u64, P: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(x, m);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(x, 1u64);
      let v30 = add(x, 1u64);
      let v37 = rocq_array::set::<u64>(P, x, v30);
      init_ptr(m, v22, v37, ())
    },
    sumbool::right => {
      P
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Bitwise.bitwise_implem.hasbit
// Variant: uncurried
pub fn hasbit(v: u64, b: u64) -> bool {
  eqb(land(lsr(v, b), 1u64), 1u64)
}

// Rocq: Bitwise.bitwise_implem.cell
// Variant: uncurried
pub fn cell(a: Rc<Array<u64>>, n: u64, x: u64) -> u64 {
  match ltb(x, n) {
    true => {
      let v10 = &a;
      let v13 = rocq_array::get::<u64>(&v10, x);
      std::mem::drop(a);
      v13
    },
    false => {
      let v21 = sub(x, n);
      let v22 = &a;
      let v25 = rocq_array::get::<u64>(&v22, v21);
      std::mem::drop(a);
      v25
    },
  }
}

// Rocq: Bitwise.bitwise_implem.scan
// Variant: uncurried
pub fn scan_1(a: Rc<Array<u64>>, P: Rc<Array<u64>>, n: u64, b: u64, i: u64, nb: u64, Q: Rc<Array<u64>>) -> Rc<Array<u64>> {
  scan(a, P, n, b, i, nb, Q, ())
}

// Rocq: Bitwise.bitwise_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(a: Rc<Array<u64>>, P: Rc<Array<u64>>, n: u64, b: u64, i: u64, nb: u64, Q: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = ltb(0u64, i);
  match bdec(v17) {
    sumbool::left => {
      let x = sub(i, 1u64);
      let v33 = Rc::clone(&a);
      let v39 = cell(v33, n, x);
      let nb_ = match hasbit(v39, b) {
        true => {
          i
        },
        false => {
          nb
        },
      };
      let v50 = &P;
      let p = rocq_array::get::<u64>(&v50, x);
      let v60 = match ltb(p, nb_) {
        true => {
          nb_
        },
        false => {
          p
        },
      };
      let v72 = rocq_array::set::<u64>(Q, x, v60);
      scan(a, P, n, b, x, nb_, v72, ())
    },
    sumbool::right => {
      std::mem::drop(a);
      std::mem::drop(P);
      Q
    },
  }
}

// Rocq: Bitwise.bitwise_implem.newptr
// Variant: uncurried
pub fn newptr(a: Rc<Array<u64>>, P: Rc<Array<u64>>, Q: Rc<Array<u64>>, n: u64, b: u64) -> Rc<Array<u64>> {
  let n2 = mul(2u64, n);
  let v21 = add(n2, 1u64);
  let v29 = add(n2, 1u64);
  let v36 = rocq_array::set::<u64>(Q, n2, v29);
  let v59 = rocq_array::set::<u64>(v36, add(n2, 1u64), add(n2, 1u64));
  scan_1(a, P, n, b, n2, v21, v59)
}

// Rocq: Bitwise.bitwise_implem.init
// Variant: uncurried
pub fn init_1(L: u64, j: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  init(L, j, V, S, ())
}

// Rocq: Bitwise.bitwise_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(L: u64, j: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v12 = ltb(j, L);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(j, 1u64);
      let v30 = rocq_array::set::<u64>(V, j, j);
      let v37 = rocq_array::set::<u64>(S, j, j);
      init(L, v23, v30, v37, ())
    },
    sumbool::right => {
      (V, S)
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

// Rocq: Bitwise.bitwise_implem.dedup
// Variant: uncurried
pub fn dedup_1(Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, w: u64, i: u64, w_: u64, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
  dedup(Q, V, S, w, i, w_, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.dedup (local: dedup)
// Variant: uncurried, lifted
pub fn dedup(Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, w: u64, i: u64, w_: u64, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>, _H: ()) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
  let v16 = ltb(i, w);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &V;
      let v23 = rocq_array::get::<u64>(&v20, i);
      let v24 = &Q;
      let v = rocq_array::get::<u64>(&v24, v23);
      let v28 = &S;
      let s = rocq_array::get::<u64>(&v28, i);
      let v40 = ltb(0u64, w_);
      let v49 = sub(w_, 1u64);
      let v50 = &V_;
      let v54 = rocq_array::get::<u64>(&v50, v49);
      let v58 = eqb(v54, v);
      match andb(v40, v58) {
        true => {
          let v72 = add(i, 1u64);
          let v87 = rocq_array::set::<u64>(S_, sub(w_, 1u64), s);
          dedup(Q, V, S, w, v72, w_, V_, v87, ())
        },
        false => {
          let v119 = add(i, 1u64);
          let v127 = add(w_, 1u64);
          let v134 = rocq_array::set::<u64>(V_, w_, v);
          let v141 = rocq_array::set::<u64>(S_, w_, s);
          dedup(Q, V, S, w, v119, v127, v134, v141, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(Q);
      std::mem::drop(V);
      std::mem::drop(S);
      ((w_, V_), S_)
    },
  }
}

// Rocq: Bitwise.bitwise_implem.levels
// Variant: uncurried
pub fn levels_1(Q: Rc<Array<u64>>, t: u64, w: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>) -> ((((u64, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  levels(Q, t, w, V, S, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.levels (local: levels)
// Variant: uncurried, lifted
pub fn levels(Q: Rc<Array<u64>>, t: u64, w: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>, _H: ()) -> ((((u64, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let v17 = ltb(0u64, t);
  match bdec(v17) {
    sumbool::left => {
      let v28 = Rc::clone(&Q);
      let v31 = Rc::clone(&V);
      let v34 = Rc::clone(&S);
      let v45 = dedup_1(v28, v31, v34, w, 0u64, 0u64, V_, S_);
      match v45 {
        (v47, v49) => {
          match v47 {
            (v52, v54) => {
              levels(Q, sub(t, 1u64), v52, v54, v49, V, S, ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(Q);
      ((((w, V), S), V_), S_)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Bitwise.bitwise_implem.check
// Variant: uncurried
pub fn check_1(V: Rc<Array<u64>>, S: Rc<Array<u64>>, n: u64, w: u64, j: u64) -> bool {
  check(V, S, n, w, j, ())
}

// Rocq: Bitwise.bitwise_implem.check (local: check)
// Variant: uncurried, lifted
pub fn check(V: Rc<Array<u64>>, S: Rc<Array<u64>>, n: u64, w: u64, j: u64, _H: ()) -> bool {
  let v13 = ltb(j, w);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &V;
      let v21 = rocq_array::get::<u64>(&v18, j);
      let v23 = &S;
      let v27 = rocq_array::get::<u64>(&v23, j);
      let v31 = add(v27, n);
      match leb(v21, v31) {
        true => {
          std::mem::drop(V);
          std::mem::drop(S);
          true
        },
        false => {
          check(V, S, n, w, add(j, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(V);
      std::mem::drop(S);
      false
    },
  }
}

// Rocq: Bitwise.bitwise_implem.test
// Variant: uncurried
pub fn test(Q: Rc<Array<u64>>, n: u64, k: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>) -> ((((bool, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let v8 = 0u64;
  let v9 = &Q;
  let f0 = rocq_array::get::<u64>(&v9, v8);
  let v22 = sub(n, 1u64);
  let v28 = match ltb(f0, v22) {
    true => {
      f0
    },
    false => {
      sub(n, 1u64)
    },
  };
  let L1 = add(v28, 1u64);
  let v60 = init_1(L1, 0u64, V, S);
  match &v60 {
    (S1, V1) => {
      let v75 = Rc::clone(S1);
      let v76 = Rc::clone(V1);
      std::mem::drop(v60);
      let v82 = levels_1(Q, k, L1, v75, v76, V_, S_);
      match v82 {
        (v84, v86) => {
          match v84 {
            (v89, v91) => {
              match v89 {
                (v94, v96) => {
                  let p1 = &v96;
                  match v94 {
                    (v100, v102) => {
                      let w = &v102;
                      let v109 = Rc::clone(w);
                      let v111 = Rc::clone(p1);
                      ((((check_1(v109, v111, n, v100, 0u64), v102), v96), v91), v86)
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

// Rocq: Bitwise.bitwise_implem.bits
// Variant: uncurried
pub fn bits_1(a: Rc<Array<u64>>, n: u64, k: u64, b: u64, ans: u64, P: Rc<Array<u64>>, Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>) -> u64 {
  bits(a, n, k, b, ans, P, Q, V, S, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.bits (local: bits)
// Variant: uncurried, lifted
pub fn bits(a: Rc<Array<u64>>, n: u64, k: u64, b: u64, ans: u64, P: Rc<Array<u64>>, Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>, _H: ()) -> u64 {
  let v21 = ltb(0u64, b);
  match bdec(v21) {
    sumbool::left => {
      let j = sub(b, 1u64);
      let v36 = Rc::clone(&a);
      let v39 = Rc::clone(&P);
      let Q1 = newptr(v36, v39, Q, n, j);
      let v50 = Rc::clone(&Q1);
      let v63 = test(v50, n, k, V, S, V_, S_);
      match v63 {
        (v65, v67) => {
          match v65 {
            (v70, v72) => {
              match v70 {
                (v75, v77) => {
                  match v75 {
                    (v80, v82) => {
                      match v80 {
                        true => {
                          let v93 = lsl(1u64, j);
                          bits(a, n, k, j, lor(ans, v93), Q1, P, v82, v77, v72, v67, ())
                        },
                        false => {
                          bits(a, n, k, j, ans, P, Q1, v82, v77, v72, v67, ())
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
      std::mem::drop(a);
      std::mem::drop(P);
      std::mem::drop(Q);
      std::mem::drop(V);
      std::mem::drop(S);
      std::mem::drop(V_);
      std::mem::drop(S_);
      ans
    },
  }
}

// Rocq: Bitwise.bitwise_implem.best_and_impl
// Variant: uncurried
pub fn best_and_impl(k: u64, a: Rc<Array<u64>>) -> u64 {
  let v2 = &a;
  let n = rocq_array::length::<u64>(&v2);
  let n2 = mul(2u64, n);
  let v20 = add(n2, 1u64);
  let v37 = rocq_array::make::<u64>(add(n2, 2u64), 0u64);
  let P0 = init_ptr_1(v20, 0u64, v37);
  let P = rocq_array::set::<u64>(P0, add(n2, 1u64), add(n2, 1u64));
  let v87 = rocq_array::make::<u64>(add(n2, 2u64), 0u64);
  let v94 = rocq_array::make::<u64>(n, 0u64);
  let v101 = rocq_array::make::<u64>(n, 0u64);
  let v108 = rocq_array::make::<u64>(n, 0u64);
  let v115 = rocq_array::make::<u64>(n, 0u64);
  bits_1(a, n, k, 30u64, 0u64, P, v87, v94, v101, v108, v115)
}

// Rocq: Bitwise.bitwise_implem.best_and_impl
pub fn best_and_impl_curried(k: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v3 = {
    move |a: Rc<Array<u64>>| -> u64 {
      let v9 = Clone::clone(&k);
      best_and_impl(v9, a)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = __rocq_global_859.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_859: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = best_and(); }
std::thread_local! { static __rocq_global_862: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = best_and_curried(); }