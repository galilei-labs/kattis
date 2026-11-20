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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(x, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(x, 1u64);
      let tmp_2 = add(x, 1u64);
      let tmp_3 = rocq_array::set::<u64>(P, x, tmp_2);
      init_ptr(m, tmp_1, tmp_3, ())
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
  if ltb(x, n) {
    let tmp = rocq_array::get::<u64>(&a, x);
    std::mem::drop(a);
    tmp
  } else {
    let tmp_1 = rocq_array::get::<u64>(&a, sub(x, n));
    std::mem::drop(a);
    tmp_1
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
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let x = sub(i, 1u64);
      let a_clone = Rc::clone(&a);
      let tmp_1 = cell(a_clone, n, x);
      let nb_ = if hasbit(tmp_1, b) {
        i
      } else {
        nb
      };
      let p = rocq_array::get::<u64>(&P, x);
      let tmp_2 = if ltb(p, nb_) {
        nb_
      } else {
        p
      };
      let tmp_3 = rocq_array::set::<u64>(Q, x, tmp_2);
      scan(a, P, n, b, x, nb_, tmp_3, ())
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
  let tmp = add(n2, 1u64);
  let tmp_1 = add(n2, 1u64);
  let tmp_2 = rocq_array::set::<u64>(Q, n2, tmp_1);
  let tmp_3 = rocq_array::set::<u64>(tmp_2, add(n2, 1u64), add(n2, 1u64));
  scan_1(a, P, n, b, n2, tmp, tmp_3)
}

// Rocq: Bitwise.bitwise_implem.init
// Variant: uncurried
pub fn init_1(L: u64, j: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  init(L, j, V, S, ())
}

// Rocq: Bitwise.bitwise_implem.init (local: init)
// Variant: uncurried, lifted
pub fn init(L: u64, j: u64, V: Rc<Array<u64>>, S: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(j, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::set::<u64>(V, j, j);
      let tmp_3 = rocq_array::set::<u64>(S, j, j);
      init(L, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      (V, S)
    },
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

// Rocq: Bitwise.bitwise_implem.dedup
// Variant: uncurried
pub fn dedup_1(Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, w: u64, i: u64, w_: u64, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
  dedup(Q, V, S, w, i, w_, V_, S_, ())
}

// Rocq: Bitwise.bitwise_implem.dedup (local: dedup)
// Variant: uncurried, lifted
pub fn dedup(Q: Rc<Array<u64>>, V: Rc<Array<u64>>, S: Rc<Array<u64>>, w: u64, i: u64, w_: u64, V_: Rc<Array<u64>>, S_: Rc<Array<u64>>, _H: ()) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(i, w);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&V, i);
      let v = rocq_array::get::<u64>(&Q, tmp_1);
      let s = rocq_array::get::<u64>(&S, i);
      let tmp_2 = ltb(0u64, w_);
      let tmp_3 = rocq_array::get::<u64>(&V_, sub(w_, 1u64));
      let tmp_4 = eqb(tmp_3, v);
      if andb(tmp_2, tmp_4) {
        let tmp_5 = add(i, 1u64);
        let tmp_6 = rocq_array::set::<u64>(S_, sub(w_, 1u64), s);
        dedup(Q, V, S, w, tmp_5, w_, V_, tmp_6, ())
      } else {
        let tmp_7 = add(i, 1u64);
        let tmp_8 = add(w_, 1u64);
        let tmp_9 = rocq_array::set::<u64>(V_, w_, v);
        let tmp_10 = rocq_array::set::<u64>(S_, w_, s);
        dedup(Q, V, S, w, tmp_7, tmp_8, tmp_9, tmp_10, ())
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
  let tmp = ltb(0u64, t);
  match bdec(tmp) {
    sumbool::left => {
      let Q_clone = Rc::clone(&Q);
      let V_clone = Rc::clone(&V);
      let S_clone = Rc::clone(&S);
      let tmp_1 = dedup_1(Q_clone, V_clone, S_clone, w, 0u64, 0u64, V_, S_);
      match tmp_1 {
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
  let tmp = ltb(j, w);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&V, j);
      let tmp_2 = rocq_array::get::<u64>(&S, j);
      let tmp_3 = add(tmp_2, n);
      if leb(tmp_1, tmp_3) {
        std::mem::drop(V);
        std::mem::drop(S);
        true
      } else {
        check(V, S, n, w, add(j, 1u64), ())
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
  let f0 = rocq_array::get::<u64>(&Q, 0u64);
  let tmp = sub(n, 1u64);
  let tmp_1 = if ltb(f0, tmp) {
    f0
  } else {
    sub(n, 1u64)
  };
  let L1 = add(tmp_1, 1u64);
  let tmp_2 = init_1(L1, 0u64, V, S);
  match &tmp_2 {
    (S1, V1) => {
      let S1_clone = Rc::clone(S1);
      let V1_clone = Rc::clone(V1);
      std::mem::drop(tmp_2);
      let tmp_3 = levels_1(Q, k, L1, S1_clone, V1_clone, V_, S_);
      match tmp_3 {
        (v84, v86) => {
          match v84 {
            (v89, v91) => {
              match v89 {
                (v94, v96) => {
                  let p1 = &v96;
                  match v94 {
                    (v100, v102) => {
                      let w = &v102;
                      let w_clone = Rc::clone(w);
                      let p1_clone = Rc::clone(p1);
                      ((((check_1(w_clone, p1_clone, n, v100, 0u64), v102), v96), v91), v86)
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
  let tmp = ltb(0u64, b);
  match bdec(tmp) {
    sumbool::left => {
      let j = sub(b, 1u64);
      let a_clone = Rc::clone(&a);
      let P_clone = Rc::clone(&P);
      let Q1 = newptr(a_clone, P_clone, Q, n, j);
      let Q1_clone = Rc::clone(&Q1);
      let tmp_1 = test(Q1_clone, n, k, V, S, V_, S_);
      match tmp_1 {
        (v65, v67) => {
          match v65 {
            (v70, v72) => {
              match v70 {
                (v75, v77) => {
                  match v75 {
                    (v80, v82) => {
                      if v80 {
                        let tmp_2 = lsl(1u64, j);
                        bits(a, n, k, j, lor(ans, tmp_2), Q1, P, v82, v77, v72, v67, ())
                      } else {
                        bits(a, n, k, j, ans, P, Q1, v82, v77, v72, v67, ())
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
  let n = rocq_array::length::<u64>(&a);
  let n2 = mul(2u64, n);
  let tmp = add(n2, 1u64);
  let tmp_1 = rocq_array::make::<u64>(add(n2, 2u64), 0u64);
  let P0 = init_ptr_1(tmp, 0u64, tmp_1);
  let P = rocq_array::set::<u64>(P0, add(n2, 1u64), add(n2, 1u64));
  let tmp_2 = rocq_array::make::<u64>(add(n2, 2u64), 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let tmp_4 = rocq_array::make::<u64>(n, 0u64);
  let tmp_5 = rocq_array::make::<u64>(n, 0u64);
  let tmp_6 = rocq_array::make::<u64>(n, 0u64);
  bits_1(a, n, k, 30u64, 0u64, P, tmp_2, tmp_3, tmp_4, tmp_5, tmp_6)
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
