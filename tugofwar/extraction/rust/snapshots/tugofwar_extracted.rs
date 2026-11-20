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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Tugofwar.tugofwar_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Tugofwar.tugofwar_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(a: Rc<Array<u64>>, i: u64, acc: u64) -> u64 {
  sum_loop(a, i, acc, ())
}

// Rocq: Tugofwar.tugofwar_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(a: Rc<Array<u64>>, i: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&a, sub(i, 1u64));
      sum_loop(a, tmp_1, add(acc, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(a);
      acc
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Tugofwar.tugofwar_implem.cell_loop
// Variant: uncurried
pub fn cell_loop_1(t: Rc<Array<bool>>, W: u64, x: u64, c: u64, s: u64) -> Rc<Array<bool>> {
  cell_loop(t, W, x, c, s, ())
}

// Rocq: Tugofwar.tugofwar_implem.cell_loop (local: cell_loop)
// Variant: uncurried, lifted
pub fn cell_loop(t: Rc<Array<bool>>, W: u64, x: u64, c: u64, s: u64, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(s, W);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&t, add(mul(sub(c, 1u64), W), sub(s, x)));
      let tmp_2 = if tmp_1 {
        rocq_array::set::<bool>(t, add(mul(c, W), s), true)
      } else {
        t
      };
      cell_loop(tmp_2, W, x, c, add(s, 1u64), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Tugofwar.tugofwar_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(t: Rc<Array<bool>>, W: u64, x: u64, c: u64) -> Rc<Array<bool>> {
  row_loop(t, W, x, c, ())
}

// Rocq: Tugofwar.tugofwar_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(t: Rc<Array<bool>>, W: u64, x: u64, c: u64, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(0u64, c);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = cell_loop_1(t, W, x, c, x);
      row_loop(tmp_1, W, x, sub(c, 1u64), ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Tugofwar.tugofwar_implem.item_loop
// Variant: uncurried
pub fn item_loop_1(a: Rc<Array<u64>>, t: Rc<Array<bool>>, W: u64, K: u64, i: u64) -> Rc<Array<bool>> {
  item_loop(a, t, W, K, i, ())
}

// Rocq: Tugofwar.tugofwar_implem.item_loop (local: item_loop)
// Variant: uncurried, lifted
pub fn item_loop(a: Rc<Array<u64>>, t: Rc<Array<bool>>, W: u64, K: u64, i: u64, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&a, sub(i, 1u64));
      let tmp_2 = row_loop_1(t, W, tmp_1, K);
      item_loop(a, tmp_2, W, K, sub(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(a);
      t
    },
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Tugofwar.tugofwar_implem.best_loop
// Variant: uncurried
pub fn best_loop_1(t: Rc<Array<bool>>, W: u64, h: u64, K: u64, s: u64) -> u64 {
  best_loop(t, W, h, K, s, ())
}

// Rocq: Tugofwar.tugofwar_implem.best_loop (local: best_loop)
// Variant: uncurried, lifted
pub fn best_loop(t: Rc<Array<bool>>, W: u64, h: u64, K: u64, s: u64, _H: ()) -> u64 {
  let tmp = rocq_array::get::<bool>(&t, add(mul(h, W), s));
  let tmp_1 = rocq_array::get::<bool>(&t, add(mul(K, W), s));
  if orb(tmp, tmp_1) {
    std::mem::drop(t);
    s
  } else {
    let tmp_2 = ltb(0u64, s);
    match bdec(tmp_2) {
      sumbool::left => {
        best_loop(t, W, h, K, sub(s, 1u64), ())
      },
      sumbool::right => {
        std::mem::drop(t);
        0u64
      },
    }
  }
}

// Rocq: Tugofwar.tugofwar_implem.tugofwar_impl
pub fn tugofwar_impl(a: Rc<Array<u64>>) -> (u64, u64) {
  let n = rocq_array::length::<u64>(&a);
  let a_clone = Rc::clone(&a);
  let S = sum_loop_1(a_clone, n, 0u64);
  let half = div(S, 2u64);
  let W = add(half, 1u64);
  let h = div(n, 2u64);
  let K = sub(n, h);
  let tmp = rocq_array::make::<bool>(mul(add(K, 1u64), W), false);
  let t0 = rocq_array::set::<bool>(tmp, 0u64, true);
  let t = item_loop_1(a, t0, W, K, n);
  let b = best_loop_1(t, W, h, K, half);
  let tmp_1 = sub(S, b);
  (b, tmp_1)
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
