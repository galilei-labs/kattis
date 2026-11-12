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

// Rocq: Xormax.xormax_implem.xormax
pub fn xormax() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>) -> u64 = xormax_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
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

// Rocq: Xormax.xormax_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor
// Variant: uncurried
pub fn lxor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lxor(v0, v1)
}

// Rocq: Xormax.xormax_implem.reduce
// Variant: uncurried
pub fn reduce_1(b: Rc<Array<u64>>, c: u64, i: u64) -> Rc<Array<u64>> {
  reduce(b, c, i, ())
}

// Rocq: Xormax.xormax_implem.reduce (local: reduce)
// Variant: uncurried, lifted
pub fn reduce(b: Rc<Array<u64>>, c: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(0u64, i);
  match bdec(v13) {
    sumbool::left => {
      let v31 = lsr(c, sub(i, 1u64));
      match eqb(v31, 0u64) {
        true => {
          reduce(b, c, sub(i, 1u64), ())
        },
        false => {
          let v69 = sub(i, 1u64);
          let v70 = &b;
          let bk = rocq_array::get::<u64>(&v70, v69);
          match eqb(bk, 0u64) {
            true => {
              rocq_array::set::<u64>(b, sub(i, 1u64), c)
            },
            false => {
              reduce(b, lxor(c, bk), sub(i, 1u64), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      b
    },
  }
}

// Rocq: Xormax.xormax_implem.build
// Variant: uncurried
pub fn build_1(x: Rc<Array<u64>>, n: u64, j: u64, b: Rc<Array<u64>>) -> Rc<Array<u64>> {
  build(x, n, j, b, ())
}

// Rocq: Xormax.xormax_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(x: Rc<Array<u64>>, n: u64, j: u64, b: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(j, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(j, 1u64);
      let v25 = &x;
      let v28 = rocq_array::get::<u64>(&v25, j);
      let v37 = reduce_1(b, v28, 63u64);
      build(x, n, v23, v37, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      b
    },
  }
}

// Rocq: Xormax.xormax_implem.greedy
// Variant: uncurried
pub fn greedy_1(b: Rc<Array<u64>>, r: u64, i: u64) -> u64 {
  greedy(b, r, i, ())
}

// Rocq: Xormax.xormax_implem.greedy (local: greedy)
// Variant: uncurried, lifted
pub fn greedy(b: Rc<Array<u64>>, r: u64, i: u64, _H: ()) -> u64 {
  let v13 = ltb(0u64, i);
  match bdec(v13) {
    sumbool::left => {
      let v25 = sub(i, 1u64);
      let v26 = &b;
      let v29 = rocq_array::get::<u64>(&v26, v25);
      let r_ = lxor(r, v29);
      let v41 = match ltb(r, r_) {
        true => {
          r_
        },
        false => {
          r
        },
      };
      greedy(b, v41, sub(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(b);
      r
    },
  }
}

// Rocq: Xormax.xormax_implem.xormax_impl
pub fn xormax_impl(x: Rc<Array<u64>>) -> u64 {
  let v2 = &x;
  let v3 = rocq_array::length::<u64>(&v2);
  let v14 = rocq_array::make::<u64>(63u64, 0u64);
  let b = build_1(x, v3, 0u64, v14);
  greedy_1(b, 0u64, 63u64)
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
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = __rocq_global_274.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_274: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = xormax(); }