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

// Rocq: Canonical.canonical_implem.canonical
pub fn canonical() -> Rc<dyn Fn(Rc<Array<u64>>) -> bool> {
  let v0: fn(Rc<Array<u64>>) -> bool = canonical_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = Rc::new(v0);
  v1
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

// Rocq: Canonical.canonical_implem.bound
pub fn bound(c: Rc<Array<u64>>) -> u64 {
  let v1 = &c;
  let n = rocq_array::length::<u64>(&v1);
  let v11 = sub(n, 1u64);
  let v12 = &c;
  let v15 = rocq_array::get::<u64>(&v12, v11);
  let v23 = sub(n, 2u64);
  let v24 = &c;
  let v27 = rocq_array::get::<u64>(&v24, v23);
  std::mem::drop(c);
  add(v15, v27)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Canonical.canonical_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Canonical.canonical_implem.kupd
// Variant: uncurried
pub fn kupd(c: Rc<Array<u64>>, n: u64, x: u64, k: u64) -> u64 {
  let v13 = add(k, 1u64);
  match ltb(v13, n) {
    true => {
      let v27 = add(k, 1u64);
      let v28 = &c;
      let v32 = rocq_array::get::<u64>(&v28, v27);
      match leb(v32, x) {
        true => {
          std::mem::drop(c);
          add(k, 1u64)
        },
        false => {
          std::mem::drop(c);
          k
        },
      }
    },
    false => {
      std::mem::drop(c);
      k
    },
  }
}

// Rocq: Canonical.canonical_implem.minloop
// Variant: uncurried
pub fn minloop_1(c: Rc<Array<u64>>, t: Rc<Array<u64>>, x: u64, hi: u64, j: u64, acc: u64) -> u64 {
  minloop(c, t, x, hi, j, acc, ())
}

// Rocq: Canonical.canonical_implem.minloop (local: minloop)
// Variant: uncurried, lifted
pub fn minloop(c: Rc<Array<u64>>, t: Rc<Array<u64>>, x: u64, hi: u64, j: u64, acc: u64, _H: ()) -> u64 {
  let v14 = ltb(j, hi);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &c;
      let v22 = rocq_array::get::<u64>(&v19, j);
      let v27 = sub(x, v22);
      let v28 = &t;
      let v = rocq_array::get::<u64>(&v28, v27);
      let v39 = add(j, 1u64);
      let v46 = match ltb(v, acc) {
        true => {
          v
        },
        false => {
          acc
        },
      };
      minloop(c, t, x, hi, v39, v46, ())
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Canonical.canonical_implem.outer
// Variant: uncurried
pub fn outer_1(c: Rc<Array<u64>>, n: u64, B: u64, x: u64, k: u64, t: Rc<Array<u64>>, g: Rc<Array<u64>>) -> bool {
  outer(c, n, B, x, k, t, g, ())
}

// Rocq: Canonical.canonical_implem.outer (local: outer)
// Variant: uncurried, lifted
pub fn outer(c: Rc<Array<u64>>, n: u64, B: u64, x: u64, k: u64, t: Rc<Array<u64>>, g: Rc<Array<u64>>, _H: ()) -> bool {
  let v15 = ltb(x, B);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&c);
      let k_ = kupd(v22, n, x, k);
      let v32 = &c;
      let v35 = rocq_array::get::<u64>(&v32, k_);
      let v40 = sub(x, v35);
      let v41 = &g;
      let v44 = rocq_array::get::<u64>(&v41, v40);
      let gx = add(v44, 1u64);
      let v61 = add(k_, 1u64);
      let v71 = sub(x, 1u64);
      let v72 = &t;
      let v75 = rocq_array::get::<u64>(&v72, v71);
      let v78 = Rc::clone(&c);
      let v81 = Rc::clone(&t);
      let tx = add(minloop_1(v78, v81, x, v61, 1u64, v75), 1u64);
      match ltb(tx, gx) {
        true => {
          std::mem::drop(c);
          std::mem::drop(t);
          std::mem::drop(g);
          false
        },
        false => {
          let v116 = add(x, 1u64);
          let v123 = rocq_array::set::<u64>(t, x, tx);
          let v130 = rocq_array::set::<u64>(g, x, gx);
          outer(c, n, B, v116, k_, v123, v130, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(c);
      std::mem::drop(t);
      std::mem::drop(g);
      true
    },
  }
}

// Rocq: Canonical.canonical_implem.run
pub fn run_1(c: Rc<Array<u64>>) -> bool {
  let v4 = Rc::clone(&c);
  let B = bound(v4);
  let v7 = &c;
  let v8 = rocq_array::length::<u64>(&v7);
  let v19 = rocq_array::make::<u64>(B, 0u64);
  let v26 = rocq_array::make::<u64>(B, 0u64);
  outer_1(c, v8, B, 1u64, 0u64, v19, v26)
}

// Rocq: Canonical.canonical_implem.canonical_impl
pub fn canonical_impl(c: Rc<Array<u64>>) -> bool {
  run_1(c)
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
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = __rocq_global_285.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_285: Rc<dyn Fn(Rc<Array<u64>>) -> bool> = canonical(); }