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

// Rocq: Median.median_implem.seed0
pub fn seed0() -> u64 {
  88172645463325252u64
}

// Rocq: Median.median_implem.median
pub fn median() -> Rc<dyn Fn(Rc<Array<u64>>) -> f64> {
  let v0: fn(Rc<Array<u64>>) -> f64 = median_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> f64> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
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

// Rocq: Median.median_implem.bdec
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

// Rocq: Median.median_implem.lcg
pub fn lcg(s: u64) -> u64 {
  add(mul(s, 6364136223846793005u64), 1442695040888963407u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
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

// Rocq: Median.median_implem.tst
// Variant: uncurried
pub fn tst(strict: bool, x: u64, v: u64) -> bool {
  match strict {
    true => {
      ltb(v, x)
    },
    false => {
      leb(v, x)
    },
  }
}

// Rocq: Median.median_implem.swap_with
// Variant: uncurried
pub fn swap_with(y: Rc<Array<u64>>, i: u64, j: u64, v: u64) -> Rc<Array<u64>> {
  let v4 = &y;
  let w = rocq_array::get::<u64>(&v4, i);
  let v15 = rocq_array::set::<u64>(y, i, v);
  rocq_array::set::<u64>(v15, j, w)
}

// Rocq: Median.median_implem.part
// Variant: uncurried
pub fn part_1(strict: bool, x: u64, hi: u64, y: Rc<Array<u64>>, i: u64, j: u64) -> (Rc<Array<u64>>, u64) {
  part(strict, x, hi, y, i, j, ())
}

// Rocq: Median.median_implem.part (local: part)
// Variant: uncurried, lifted
pub fn part(strict: bool, x: u64, hi: u64, y: Rc<Array<u64>>, i: u64, j: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v14 = ltb(j, hi);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &y;
      let v = rocq_array::get::<u64>(&v18, j);
      match tst(strict, x, v) {
        true => {
          let v40 = swap_with(y, i, j, v);
          part(strict, x, hi, v40, add(i, 1u64), add(j, 1u64), ())
        },
        false => {
          part(strict, x, hi, y, i, add(j, 1u64), ())
        },
      }
    },
    sumbool::right => {
      (y, i)
    },
  }
}

// Rocq: Median.median_implem.sel
// Variant: uncurried
pub fn sel_1(k: u64, y: Rc<Array<u64>>, lo: u64, hi: u64, seed: u64) -> Rc<Array<u64>> {
  sel(k, y, lo, hi, seed, ())
}

// Rocq: Median.median_implem.sel (local: sel)
// Variant: uncurried, lifted
pub fn sel(k: u64, y: Rc<Array<u64>>, lo: u64, hi: u64, seed: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(lo, hi);
  match bdec(v13) {
    sumbool::left => {
      let s = lcg(seed);
      let v30 = lsr(s, 17u64);
      let v36 = sub(hi, lo);
      let v46 = add(lo, mod_(v30, v36));
      let v47 = &y;
      let x = rocq_array::get::<u64>(&v47, v46);
      let v66 = part_1(true, x, hi, y, lo, lo);
      match v66 {
        (v68, v70) => {
          let v87 = part_1(false, x, hi, v68, v70, v70);
          match v87 {
            (v89, v91) => {
              match ltb(k, v70) {
                true => {
                  let v107 = ltb(v70, hi);
                  match bdec(v107) {
                    sumbool::left => {
                      sel(k, v89, lo, v70, s, ())
                    },
                    sumbool::right => {
                      v89
                    },
                  }
                },
                false => {
                  match ltb(k, v91) {
                    true => {
                      v89
                    },
                    false => {
                      let v150 = ltb(lo, v91);
                      match bdec(v150) {
                        sumbool::left => {
                          sel(k, v89, v91, hi, s, ())
                        },
                        sumbool::right => {
                          v89
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
      y
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Median.median_implem.maxl
// Variant: uncurried
pub fn maxl_1(y: Rc<Array<u64>>, k: u64, j: u64, acc: u64) -> u64 {
  maxl(y, k, j, acc, ())
}

// Rocq: Median.median_implem.maxl (local: maxl)
// Variant: uncurried, lifted
pub fn maxl(y: Rc<Array<u64>>, k: u64, j: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(j, k);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &y;
      let v = rocq_array::get::<u64>(&v16, j);
      let v27 = add(j, 1u64);
      let v34 = match ltb(acc, v) {
        true => {
          v
        },
        false => {
          acc
        },
      };
      maxl(y, k, v27, v34, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      acc
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Median.median_implem.median_impl
pub fn median_impl(x: Rc<Array<u64>>) -> f64 {
  let v1 = &x;
  let n = rocq_array::length::<u64>(&v1);
  let k = div(n, 2u64);
  let v12 = &x;
  let v13 = rocq_array::copy::<u64>(&v12);
  let y = sel_1(k, v13, 0u64, n, __rocq_global_343);
  let v28 = &y;
  let u = rocq_array::get::<u64>(&v28, k);
  let v40 = mod_(n, 2u64);
  match eqb(v40, 1u64) {
    true => {
      std::mem::drop(x);
      std::mem::drop(y);
      of_uint63(u)
    },
    false => {
      std::mem::drop(x);
      let v59 = 0u64;
      let v60 = &y;
      let v63 = rocq_array::get::<u64>(&v60, v59);
      let w = maxl_1(y, k, 1u64, v63);
      div_1(of_uint63(add(w, u)), of_uint63(2u64))
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> f64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> f64> = __rocq_global_449.with(Clone::clone);
  v0
}
const __rocq_global_343: u64 = 88172645463325252u64;
std::thread_local! { static __rocq_global_449: Rc<dyn Fn(Rc<Array<u64>>) -> f64> = median(); }