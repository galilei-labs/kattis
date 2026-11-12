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

pub type sint = u64;

// Rocq: Polymul1.polymul1_implem.polymul
// Variant: uncurried
pub fn polymul() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = polymul_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Polymul1.polymul1_implem.polymul
pub fn polymul_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = polymul_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
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

// Rocq: Polymul1.polymul1_implem.bdec
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

// Rocq: Polymul1.polymul1_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(y: Rc<Array<u64>>, ai: u64, i: u64, lb: u64, j: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  row_loop(y, ai, i, lb, j, r, ())
}

// Rocq: Polymul1.polymul1_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(y: Rc<Array<u64>>, ai: u64, i: u64, lb: u64, j: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(j, lb);
  match bdec(v14) {
    sumbool::left => {
      let k = add(i, j);
      let v31 = add(j, 1u64);
      let v33 = &r;
      let v36 = rocq_array::get::<u64>(&v33, k);
      let v38 = &y;
      let v41 = rocq_array::get::<u64>(&v38, j);
      let v58 = rocq_array::set::<u64>(r, k, add(v36, mul(ai, v41)));
      row_loop(y, ai, i, lb, v31, v58, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Polymul1.polymul1_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, la: u64, lb: u64, i: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rows_loop(x, y, la, lb, i, r, ())
}

// Rocq: Polymul1.polymul1_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(x: Rc<Array<u64>>, y: Rc<Array<u64>>, la: u64, lb: u64, i: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, la);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(i, 1u64);
      let v27 = &x;
      let v30 = rocq_array::get::<u64>(&v27, i);
      let v35 = Rc::clone(&y);
      let v46 = row_loop_1(v35, v30, i, lb, 0u64, r);
      rows_loop(x, y, la, lb, v25, v46, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Polymul1.polymul1_implem.polymul_impl
// Variant: uncurried
pub fn polymul_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v2 = &x;
  let la = rocq_array::length::<u64>(&v2);
  let v4 = &y;
  let lb = rocq_array::length::<u64>(&v4);
  match eqb(la, 0u64) {
    true => {
      std::mem::drop(x);
      std::mem::drop(y);
      rocq_array::make::<u64>(0u64, 0u64)
    },
    false => {
      match eqb(lb, 0u64) {
        true => {
          std::mem::drop(x);
          std::mem::drop(y);
          rocq_array::make::<u64>(0u64, 0u64)
        },
        false => {
          let v69 = rocq_array::make::<u64>(sub(add(la, lb), 1u64), 0u64);
          rows_loop_1(x, y, la, lb, 0u64, v69)
        },
      }
    },
  }
}

// Rocq: Polymul1.polymul1_implem.polymul_impl
pub fn polymul_impl_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&x);
      polymul_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_244.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_244: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = polymul(); }
std::thread_local! { static __rocq_global_247: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = polymul_curried(); }