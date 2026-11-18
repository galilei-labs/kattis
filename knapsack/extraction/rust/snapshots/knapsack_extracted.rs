#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Knapsack.knapsack_implem.bdec
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

// Rocq: Knapsack.knapsack_implem.item_loop
// Variant: uncurried
pub fn item_loop_1(v: u64, w: u64, base: u64, k: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  item_loop(v, w, base, k, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.item_loop (local: item_loop)
// Variant: uncurried, lifted
pub fn item_loop(v: u64, w: u64, base: u64, k: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  let tmp = ltb(w, k);
  match bdec(tmp) {
    sumbool::left => {
      let c = sub(k, 1u64);
      let tmp_1 = rocq_array::get::<u64>(&row, sub(c, w));
      let cand = add(tmp_1, v);
      let tmp_2 = rocq_array::get::<u64>(&row, c);
      if ltb(tmp_2, cand) {
        let tmp_3 = rocq_array::set::<u64>(row, c, cand);
        let tmp_4 = rocq_array::set::<bool>(dec, add(base, c), true);
        item_loop(v, w, base, c, tmp_3, tmp_4, ())
      } else {
        item_loop(v, w, base, c, row, dec, ())
      }
    },
    sumbool::right => {
      (row, dec)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Knapsack.knapsack_implem.items_loop
// Variant: uncurried
pub fn items_loop_1(xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, n: u64, C1: u64, i: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  items_loop(xv, xw, n, C1, i, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.items_loop (local: items_loop)
// Variant: uncurried, lifted
pub fn items_loop(xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, n: u64, C1: u64, i: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&xv, i);
      let tmp_2 = rocq_array::get::<u64>(&xw, i);
      let rd = item_loop_1(tmp_1, tmp_2, mul(i, C1), C1, row, dec);
      let tmp_3 = add(i, 1u64);
      let rd_clone = Clone::clone(&rd);
      let tmp_4 = fst::<Rc<Array<u64>>, Rc<Array<bool>>>(rd_clone);
      let tmp_5 = snd::<Rc<Array<u64>>, Rc<Array<bool>>>(rd);
      items_loop(xv, xw, n, C1, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(xv);
      std::mem::drop(xw);
      (row, dec)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.walk
// Variant: uncurried
pub fn walk_1(xw: Rc<Array<u64>>, dec: Rc<Array<bool>>, C1: u64, i: u64, c: u64, k: u64, out: Rc<Array<u64>>) -> (u64, Rc<Array<u64>>) {
  walk(xw, dec, C1, i, c, k, out, ())
}

// Rocq: Knapsack.knapsack_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(xw: Rc<Array<u64>>, dec: Rc<Array<bool>>, C1: u64, i: u64, c: u64, k: u64, out: Rc<Array<u64>>, _H: ()) -> (u64, Rc<Array<u64>>) {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let j = sub(i, 1u64);
      let tmp_1 = rocq_array::get::<bool>(&dec, add(mul(j, C1), c));
      if tmp_1 {
        let tmp_2 = rocq_array::get::<u64>(&xw, j);
        let tmp_3 = sub(c, tmp_2);
        let tmp_4 = add(k, 1u64);
        let tmp_5 = rocq_array::set::<u64>(out, k, j);
        walk(xw, dec, C1, j, tmp_3, tmp_4, tmp_5, ())
      } else {
        walk(xw, dec, C1, j, c, k, out, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xw);
      std::mem::drop(dec);
      (k, out)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, m: u64, j: u64) -> Rc<Array<u64>> {
  copy_loop(src, dst, m, j, ())
}

// Rocq: Knapsack.knapsack_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, m: u64, j: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&src, j);
      let tmp_2 = rocq_array::set::<u64>(dst, j, tmp_1);
      copy_loop(src, tmp_2, m, add(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Knapsack.knapsack_implem.knapsack_impl
// Variant: uncurried
pub fn knapsack_impl(Cw: u64, xv: Rc<Array<u64>>, xw: Rc<Array<u64>>) -> (u64, Rc<Array<u64>>) {
  let n = rocq_array::length::<u64>(&xv);
  let C1 = add(Cw, 1u64);
  let tmp = rocq_array::make::<u64>(C1, 0u64);
  let tmp_1 = rocq_array::make::<bool>(mul(n, C1), false);
  let xw_clone = Rc::clone(&xw);
  let rd = items_loop_1(xv, xw_clone, n, C1, 0u64, tmp, tmp_1);
  let rd_clone = Clone::clone(&rd);
  let tmp_2 = fst::<Rc<Array<u64>>, Rc<Array<bool>>>(rd_clone);
  let bestv = rocq_array::get::<u64>(&tmp_2, Cw);
  std::mem::drop(tmp_2);
  let tmp_3 = snd::<Rc<Array<u64>>, Rc<Array<bool>>>(rd);
  let tmp_4 = rocq_array::make::<u64>(n, 0u64);
  let ko = walk_1(xw, tmp_3, C1, n, Cw, 0u64, tmp_4);
  let ko_clone = Clone::clone(&ko);
  let k = fst::<u64, Rc<Array<u64>>>(ko_clone);
  let tmp_5 = snd::<u64, Rc<Array<u64>>>(ko);
  let tmp_6 = rocq_array::make::<u64>(k, 0u64);
  let tmp_7 = copy_loop_1(tmp_5, tmp_6, k, 0u64);
  (bestv, tmp_7)
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
