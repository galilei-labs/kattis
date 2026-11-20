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

// Rocq: Canvas.canvas_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Canvas.canvas_implem.sift
// Variant: uncurried
pub fn sift_1(h: Rc<Array<u64>>, sz: u64, i: u64) -> Rc<Array<u64>> {
  sift(h, sz, i, ())
}

// Rocq: Canvas.canvas_implem.sift (local: sift)
// Variant: uncurried, lifted
pub fn sift(h: Rc<Array<u64>>, sz: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let x = rocq_array::get::<u64>(&h, i);
  let l = add(mul(2u64, i), 1u64);
  if ltb(l, sz) {
    let yl = rocq_array::get::<u64>(&h, l);
    let r = add(l, 1u64);
    let tmp = ltb(r, sz);
    let tmp_1 = rocq_array::get::<u64>(&h, r);
    let tmp_2 = ltb(tmp_1, yl);
    if andb(tmp, tmp_2) {
      let yr = rocq_array::get::<u64>(&h, r);
      let tmp_3 = andb(ltb(yr, x), ltb(i, r));
      match bdec(tmp_3) {
        sumbool::left => {
          let tmp_4 = rocq_array::set::<u64>(h, i, yr);
          let tmp_5 = rocq_array::set::<u64>(tmp_4, r, x);
          sift(tmp_5, sz, r, ())
        },
        sumbool::right => {
          h
        },
      }
    } else {
      let tmp_6 = andb(ltb(yl, x), ltb(i, l));
      match bdec(tmp_6) {
        sumbool::left => {
          let tmp_7 = rocq_array::set::<u64>(h, i, yl);
          let tmp_8 = rocq_array::set::<u64>(tmp_7, l, x);
          sift(tmp_8, sz, l, ())
        },
        sumbool::right => {
          h
        },
      }
    }
  } else {
    h
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Canvas.canvas_implem.build
// Variant: uncurried
pub fn build_1(h: Rc<Array<u64>>, sz: u64, k: u64) -> Rc<Array<u64>> {
  build(h, sz, k, ())
}

// Rocq: Canvas.canvas_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(h: Rc<Array<u64>>, sz: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, k);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sift_1(h, sz, sub(k, 1u64));
      build(tmp_1, sz, sub(k, 1u64), ())
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Canvas.canvas_implem.huff
// Variant: uncurried
pub fn huff_1(h: Rc<Array<u64>>, sz: u64, acc: u64) -> u64 {
  huff(h, sz, acc, ())
}

// Rocq: Canvas.canvas_implem.huff (local: huff)
// Variant: uncurried, lifted
pub fn huff(h: Rc<Array<u64>>, sz: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(1u64, sz);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&h, 0u64);
      let sz1 = sub(sz, 1u64);
      let tmp_1 = rocq_array::get::<u64>(&h, sz1);
      let tmp_2 = rocq_array::set::<u64>(h, 0u64, tmp_1);
      let h1 = sift_1(tmp_2, sz1, 0u64);
      let b = rocq_array::get::<u64>(&h1, 0u64);
      let tmp_3 = rocq_array::set::<u64>(h1, 0u64, add(a, b));
      let h2 = sift_1(tmp_3, sz1, 0u64);
      let tmp_4 = add(a, b);
      huff(h2, sz1, add(acc, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      acc
    },
  }
}

// Rocq: Canvas.canvas_implem.canvas_impl
pub fn canvas_impl(x: Rc<Array<u64>>) -> u64 {
  let sz = rocq_array::length::<u64>(&x);
  let tmp = rocq_array::copy::<u64>(&x);
  std::mem::drop(x);
  let tmp_1 = div(sz, 2u64);
  let h = build_1(tmp, sz, tmp_1);
  huff_1(h, sz, 0u64)
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
