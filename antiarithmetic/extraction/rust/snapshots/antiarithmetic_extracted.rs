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

// Rocq: Antiarithmetic.antiarithmetic_implem.antiarithmetic
pub fn antiarithmetic() -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
  let v0: fn(Rc<Array<u64>>) -> bool = antiarithmetic_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
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

// Rocq: Antiarithmetic.antiarithmetic_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor
// Variant: uncurried
pub fn lxor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lxor(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
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

// Rocq: Antiarithmetic.antiarithmetic_implem.inner
// Variant: uncurried
pub fn inner_1(S: Rc<Array<u64>>, R: Rc<Array<u64>>, rS: u64, lS: u64, rR: u64, lR: u64, aS: u64, aR: u64, rem: u64) -> bool {
  inner(S, R, rS, lS, rR, lR, aS, aR, rem, ())
}

// Rocq: Antiarithmetic.antiarithmetic_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(S: Rc<Array<u64>>, R: Rc<Array<u64>>, rS: u64, lS: u64, rR: u64, lR: u64, aS: u64, aR: u64, rem: u64, _H: ()) -> bool {
  let v13 = &S;
  let v17 = rocq_array::get::<u64>(&v13, aS);
  let v21 = lsr(v17, rS);
  let v30 = add(aS, 1u64);
  let v31 = &S;
  let v35 = rocq_array::get::<u64>(&v31, v30);
  let v44 = lor(v21, lsl(v35, lS));
  let v47 = &R;
  let v51 = rocq_array::get::<u64>(&v47, aR);
  let v55 = lsr(v51, rR);
  let v64 = add(aR, 1u64);
  let v65 = &R;
  let v69 = rocq_array::get::<u64>(&v65, v64);
  let w = lxor(v44, lor(v55, lsl(v69, lR)));
  let v93 = leb(rem, 63u64);
  match bdec(v93) {
    sumbool::left => {
      std::mem::drop(R);
      std::mem::drop(S);
      negb(eqb(land(w, sub(lsl(1u64, rem), 1u64)), 0u64))
    },
    sumbool::right => {
      match eqb(w, 0u64) {
        true => {
          inner(S, R, rS, lS, rR, lR, add(aS, 1u64), add(aR, 1u64), sub(rem, 63u64), ())
        },
        false => {
          std::mem::drop(R);
          std::mem::drop(S);
          true
        },
      }
    },
  }
}

// Rocq: Antiarithmetic.antiarithmetic_implem.setbit
// Variant: uncurried
pub fn setbit(t: Rc<Array<u64>>, v: u64) -> Rc<Array<u64>> {
  let a = div(v, 63u64);
  let v11 = &t;
  let v14 = rocq_array::get::<u64>(&v11, a);
  rocq_array::set::<u64>(t, a, lor(v14, lsl(1u64, mod_(v, 63u64))))
}

// Rocq: Antiarithmetic.antiarithmetic_implem.scan
// Variant: uncurried
pub fn scan_1(x: Rc<Array<u64>>, n: u64, S: Rc<Array<u64>>, R: Rc<Array<u64>>, pos: u64) -> bool {
  scan(x, n, S, R, pos, ())
}

// Rocq: Antiarithmetic.antiarithmetic_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(x: Rc<Array<u64>>, n: u64, S: Rc<Array<u64>>, R: Rc<Array<u64>>, pos: u64, _H: ()) -> bool {
  let v13 = ltb(pos, n);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &x;
      let m = rocq_array::get::<u64>(&v17, pos);
      let v30 = sub(n, 1u64);
      let c = sub(v30, m);
      let L = match ltb(m, c) {
        true => {
          m
        },
        false => {
          c
        },
      };
      let oS = add(m, 1u64);
      let oR = sub(n, m);
      let rS = mod_(oS, 63u64);
      let rR = mod_(oR, 63u64);
      let v85 = sub(63u64, rS);
      let v93 = sub(63u64, rR);
      let v101 = div(oS, 63u64);
      let v109 = div(oR, 63u64);
      let v112 = Rc::clone(&S);
      let v115 = Rc::clone(&R);
      match inner_1(v112, v115, rS, v85, rR, v93, v101, v109, L) {
        true => {
          std::mem::drop(x);
          std::mem::drop(S);
          std::mem::drop(R);
          false
        },
        false => {
          let v141 = setbit(S, m);
          let v147 = setbit(R, c);
          scan(x, n, v141, v147, add(pos, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(S);
      std::mem::drop(R);
      true
    },
  }
}

// Rocq: Antiarithmetic.antiarithmetic_implem.antiarithmetic_impl
pub fn antiarithmetic_impl(x: Rc<Array<u64>>) -> bool {
  let v1 = &x;
  let n = rocq_array::length::<u64>(&v1);
  let k = add(div(n, 63u64), 1u64);
  let v26 = rocq_array::make::<u64>(k, 0u64);
  let v33 = rocq_array::make::<u64>(k, 0u64);
  scan_1(x, n, v26, v33, 0u64)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = __rocq_global_439.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_439: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = antiarithmetic(); }