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

// Rocq: Ultraquicksort.ultraquicksort_implem.inversions
pub fn inversions() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>) -> u64 = inversions_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Ultraquicksort.ultraquicksort_implem.bdec
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

// Rocq: Ultraquicksort.ultraquicksort_implem.merge
// Variant: uncurried
pub fn merge_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, c: u64) -> (Rc<Array<u64>>, u64) {
  merge(src, dst, mid, hi, i, j, k, c, ())
}

// Rocq: Ultraquicksort.ultraquicksort_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, c: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v16 = ltb(i, mid);
  match bdec(v16) {
    sumbool::left => {
      let v27 = ltb(j, hi);
      match bdec(v27) {
        sumbool::left => {
          let v31 = &src;
          let x = rocq_array::get::<u64>(&v31, i);
          let v35 = &src;
          let y = rocq_array::get::<u64>(&v35, j);
          match ltb(y, x) {
            true => {
              let v52 = rocq_array::set::<u64>(dst, k, y);
              let v60 = add(j, 1u64);
              let v68 = add(k, 1u64);
              let v75 = sub(mid, i);
              merge(src, v52, mid, hi, i, v60, v68, add(c, v75), ())
            },
            false => {
              let v111 = rocq_array::set::<u64>(dst, k, x);
              merge(src, v111, mid, hi, add(i, 1u64), j, add(k, 1u64), c, ())
            },
          }
        },
        sumbool::right => {
          let v155 = &src;
          let v158 = rocq_array::get::<u64>(&v155, i);
          let v165 = rocq_array::set::<u64>(dst, k, v158);
          merge(src, v165, mid, hi, add(i, 1u64), j, add(k, 1u64), c, ())
        },
      }
    },
    sumbool::right => {
      let v216 = ltb(j, hi);
      match bdec(v216) {
        sumbool::left => {
          let v220 = &src;
          let v223 = rocq_array::get::<u64>(&v220, j);
          let v230 = rocq_array::set::<u64>(dst, k, v223);
          merge(src, v230, mid, hi, i, add(j, 1u64), add(k, 1u64), c, ())
        },
        sumbool::right => {
          std::mem::drop(src);
          (dst, c)
        },
      }
    },
  }
}

// Rocq: Ultraquicksort.ultraquicksort_implem.msort
// Variant: uncurried
pub fn msort_1(b: bool, lo: u64, hi: u64, w: Rc<Array<u64>>, s: Rc<Array<u64>>, c: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  msort(b, lo, hi, w, s, c, ())
}

// Rocq: Ultraquicksort.ultraquicksort_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(b: bool, lo: u64, hi: u64, w: Rc<Array<u64>>, s: Rc<Array<u64>>, c: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let v22 = ltb(1u64, sub(hi, lo));
  match bdec(v22) {
    sumbool::left => {
      let v33 = sub(hi, lo);
      let mid = add(lo, div(v33, 2u64));
      let v67 = msort(negb(b), lo, mid, w, s, c, ());
      match v67 {
        (v69, v71) => {
          match v69 {
            (v74, v76) => {
              let v99 = msort(negb(b), mid, hi, v74, v76, v71, ());
              match v99 {
                (v101, v103) => {
                  match v101 {
                    (v106, v108) => {
                      let s2 = &v106;
                      let w2 = &v108;
                      match b {
                        true => {
                          let v115 = Rc::clone(w2);
                          let v130 = merge_1(v115, v106, mid, hi, lo, mid, lo, v103);
                          match v130 {
                            (v132, v134) => {
                              ((v132, v108), v134)
                            },
                          }
                        },
                        false => {
                          let v155 = Rc::clone(s2);
                          let v170 = merge_1(v155, v108, mid, hi, lo, mid, lo, v103);
                          match v170 {
                            (v172, v174) => {
                              ((v106, v172), v174)
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
    },
    sumbool::right => {
      match b {
        true => {
          ((w, s), c)
        },
        false => {
          let v223 = &w;
          let v226 = rocq_array::get::<u64>(&v223, lo);
          let v233 = rocq_array::set::<u64>(s, lo, v226);
          ((w, v233), c)
        },
      }
    },
  }
}

// Rocq: Ultraquicksort.ultraquicksort_implem.inversions_impl
pub fn inversions_impl(a: Rc<Array<u64>>) -> u64 {
  let v1 = &a;
  let n = rocq_array::length::<u64>(&v1);
  let v8 = 0u64;
  let v9 = &a;
  let v10 = rocq_array::copy::<u64>(&v9);
  std::mem::drop(a);
  let v17 = rocq_array::make::<u64>(n, 0u64);
  snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(msort_1(true, v8, n, v10, v17, 0u64))
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = __rocq_global_317.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_317: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = inversions(); }