// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Derangementrotations.derangementrotations_implem.derangement_rotations
// Variant: uncurried
pub fn derangement_rotations() -> Rc<dyn Fn(u64, u64) -> u64> {
  let v0: fn(u64, u64) -> u64 = derangement_rotations_impl;
  let v1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Derangementrotations.derangementrotations_implem.derangement_rotations
pub fn derangement_rotations_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> u64> = derangement_rotations_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = Rc::new(v0);
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

// Rocq: Derangementrotations.derangementrotations_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Derangementrotations.derangementrotations_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(p: u64, base: u64, e: u64, acc: u64) -> u64 {
  pow_loop(p, base, e, acc, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(p: u64, base: u64, e: u64, acc: u64, _H: ()) -> u64 {
  let v14 = eqb(e, 0u64);
  match bdec(v14) {
    sumbool::left => {
      acc
    },
    sumbool::right => {
      let v31 = mod_(mul(base, base), p);
      let v39 = div(e, 2u64);
      let v48 = mod_(e, 2u64);
      let v50 = 0u64;
      let v56 = match eqb(v48, v50) {
        true => {
          acc
        },
        false => {
          mod_(mul(acc, base), p)
        },
      };
      pow_loop(p, v31, v39, v56, ())
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.pow2mod
// Variant: uncurried
pub fn pow2mod(p: u64, g: u64) -> u64 {
  pow_loop_1(p, 2u64, g, 1u64)
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a: u64, b: u64) -> u64 {
  gcd_loop(a, b, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a: u64, b: u64, _H: ()) -> u64 {
  let v12 = eqb(b, 0u64);
  match bdec(v12) {
    sumbool::left => {
      a
    },
    sumbool::right => {
      let v23 = mod_(a, b);
      gcd_loop(b, v23, ())
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.gcd63
// Variant: uncurried
pub fn gcd63(a: u64, b: u64) -> u64 {
  gcd_loop_1(a, b)
}

// Rocq: Derangementrotations.derangementrotations_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(n: u64, m: u64, p: u64, d: u64, acc: u64) -> u64 {
  sum_loop(n, m, p, d, acc, ())
}

// Rocq: Derangementrotations.derangementrotations_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(n: u64, m: u64, p: u64, d: u64, acc: u64, _H: ()) -> u64 {
  let v13 = ltb(d, m);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(d, 1u64);
      let v34 = sub(m, d);
      let v66 = mod_(sub(add(pow2mod(p, gcd63(d, n)), p), 2u64), p);
      let v76 = mod_(mul(v34, v66), p);
      let v86 = mod_(add(acc, v76), p);
      sum_loop(n, m, p, v24, v86, ())
    },
    sumbool::right => {
      acc
    },
  }
}

// Rocq: Derangementrotations.derangementrotations_implem.derangement_rotations_impl
// Variant: uncurried
pub fn derangement_rotations_impl(n: u64, p: u64) -> u64 {
  let v10 = sub(n, 1u64);
  sum_loop_1(n, v10, p, 1u64, 0u64)
}

// Rocq: Derangementrotations.derangementrotations_implem.derangement_rotations_impl
pub fn derangement_rotations_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> u64> {
  let v3 = {
    move |p: u64| -> u64 {
      let v9 = Clone::clone(&n);
      derangement_rotations_impl(v9, p)
    }
  };
  let v15: Rc<dyn Fn(u64) -> u64> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, u64) -> u64> {
  let v0: Rc<dyn Fn(u64, u64) -> u64> = __rocq_global_307.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_307: Rc<dyn Fn(u64, u64) -> u64> = derangement_rotations(); }
std::thread_local! { static __rocq_global_310: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = derangement_rotations_curried(); }