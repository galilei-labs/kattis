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

// Rocq: Primepower.primepower_implem.M
pub fn M() -> u64 {
  1000000007u64
}

// Rocq: Primepower.primepower_implem.primepower
// Variant: uncurried
pub fn primepower() -> Rc<dyn Fn(u64, u64, u64) -> u64> {
  let v0: fn(u64, u64, u64) -> u64 = primepower_impl;
  let v1: Rc<dyn Fn(u64, u64, u64) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Primepower.primepower_implem.primepower
pub fn primepower_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = primepower_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.is_zero
pub fn is_zero(i: u64) -> bool {
  eqb(i, 0u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.Uint63Axioms.is_even
pub fn is_even(i: u64) -> bool {
  is_zero(land(i, 1u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
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

// Rocq: Primepower.primepower_implem.bdec
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

// Rocq: Primepower.primepower_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(b: u64, e: u64, acc: u64) -> u64 {
  pow_loop(b, e, acc, ())
}

// Rocq: Primepower.primepower_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(b: u64, e: u64, acc: u64, _H: ()) -> u64 {
  let v13 = ltb(0u64, e);
  match bdec(v13) {
    sumbool::left => {
      let v29 = mod_(mul(b, b), __rocq_global_104);
      let v37 = lsr(e, 1u64);
      let v42 = match is_even(e) {
        true => {
          acc
        },
        false => {
          mod_(mul(acc, b), __rocq_global_104)
        },
      };
      pow_loop(v29, v37, v42, ())
    },
    sumbool::right => {
      acc
    },
  }
}

// Rocq: Primepower.primepower_implem.powmod
// Variant: uncurried
pub fn powmod(b: u64, e: u64) -> u64 {
  pow_loop_1(mod_(b, __rocq_global_104), e, 1u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Primepower.primepower_implem.prod_loop
// Variant: uncurried
pub fn prod_loop_1(s: Rc<Array<u64>>, E: u64, L: u64, p: u64, acc: u64) -> u64 {
  prod_loop(s, E, L, p, acc, ())
}

// Rocq: Primepower.primepower_implem.prod_loop (local: prod_loop)
// Variant: uncurried, lifted
pub fn prod_loop(s: Rc<Array<u64>>, E: u64, L: u64, p: u64, acc: u64, _H: ()) -> u64 {
  let v7 = &s;
  let v10 = rocq_array::get::<u64>(&v7, p);
  let v12 = 0u64;
  let acc_ = match eqb(v10, v12) {
    true => {
      acc
    },
    false => {
      mod_(mul(powmod(p, E), acc), __rocq_global_104)
    },
  };
  let v50 = ltb(L, p);
  match bdec(v50) {
    sumbool::left => {
      prod_loop(s, E, L, sub(p, 1u64), acc_, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc_
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Primepower.primepower_implem.cross_loop
// Variant: uncurried
pub fn cross_loop_1(i: u64, R: u64, j: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cross_loop(i, R, j, s, ())
}

// Rocq: Primepower.primepower_implem.cross_loop (local: cross_loop)
// Variant: uncurried, lifted
pub fn cross_loop(i: u64, R: u64, j: u64, s: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = leb(j, R);
  match bdec(v12) {
    sumbool::left => {
      let j_ = add(j, i);
      let v29 = ltb(j, j_);
      match bdec(v29) {
        sumbool::left => {
          let v41 = rocq_array::set::<u64>(s, j, 0u64);
          cross_loop(i, R, j_, v41, ())
        },
        sumbool::right => {
          rocq_array::set::<u64>(s, j, 0u64)
        },
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Primepower.primepower_implem.sieve_loop
// Variant: uncurried
pub fn sieve_loop_1(R: u64, i: u64, s: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sieve_loop(R, i, s, ())
}

// Rocq: Primepower.primepower_implem.sieve_loop (local: sieve_loop)
// Variant: uncurried, lifted
pub fn sieve_loop(R: u64, i: u64, s: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v17 = leb(mul(i, i), R);
  match bdec(v17) {
    sumbool::left => {
      let v22 = &s;
      let v25 = rocq_array::get::<u64>(&v22, i);
      let v27 = 0u64;
      let s_ = match eqb(v25, v27) {
        true => {
          s
        },
        false => {
          let v42 = mul(i, i);
          cross_loop_1(i, R, v42, s)
        },
      };
      let v64 = add(i, 1u64);
      let v70 = ltb(i, v64);
      match bdec(v70) {
        sumbool::left => {
          sieve_loop(R, add(i, 1u64), s_, ())
        },
        sumbool::right => {
          s_
        },
      }
    },
    sumbool::right => {
      s
    },
  }
}

// Rocq: Primepower.primepower_implem.sieve
pub fn sieve(R: u64) -> Rc<Array<u64>> {
  let v18 = rocq_array::make::<u64>(add(R, 1u64), 1u64);
  let v29 = rocq_array::set::<u64>(v18, 0u64, 0u64);
  let v40 = rocq_array::set::<u64>(v29, 1u64, 0u64);
  sieve_loop_1(R, 2u64, v40)
}

// Rocq: Primepower.primepower_implem.primepower_impl
// Variant: uncurried
pub fn primepower_impl(E: u64, L: u64, R: u64) -> u64 {
  match ltb(R, L) {
    true => {
      1u64
    },
    false => {
      let v18 = sieve(R);
      prod_loop_1(v18, E, L, R, 1u64)
    },
  }
}

// Rocq: Primepower.primepower_implem.primepower_impl
pub fn primepower_impl_curried(E: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> {
  let v3 = {
    move |L: u64| -> Rc<dyn Fn(u64) -> u64> {
      let E = &E;
      let v8 = Clone::clone(E);
      let v11 = {
        move |R: u64| -> u64 {
          let v19 = Clone::clone(&v8);
          let v21 = Clone::clone(&L);
          primepower_impl(v19, v21, R)
        }
      };
      let v27: Rc<dyn Fn(u64) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, u64) -> u64> = __rocq_global_428.with(Clone::clone);
  v0
}
const __rocq_global_104: u64 = 1000000007u64;
std::thread_local! { static __rocq_global_428: Rc<dyn Fn(u64, u64, u64) -> u64> = primepower(); }
std::thread_local! { static __rocq_global_431: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> u64>>> = primepower_curried(); }