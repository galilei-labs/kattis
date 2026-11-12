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

// Rocq: Canvas.canvas_implem.canvas
pub fn canvas() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>) -> u64 = canvas_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Canvas.canvas_implem.bdec
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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
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
  let v4 = &h;
  let x = rocq_array::get::<u64>(&v4, i);
  let l = add(mul(2u64, i), 1u64);
  match ltb(l, sz) {
    true => {
      let v31 = &h;
      let yl = rocq_array::get::<u64>(&v31, l);
      let r = add(l, 1u64);
      let v49 = ltb(r, sz);
      let v51 = &h;
      let v55 = rocq_array::get::<u64>(&v51, r);
      let v59 = ltb(v55, yl);
      match andb(v49, v59) {
        true => {
          let v66 = &h;
          let yr = rocq_array::get::<u64>(&v66, r);
          let v89 = andb(ltb(yr, x), ltb(i, r));
          match bdec(v89) {
            sumbool::left => {
              let v100 = rocq_array::set::<u64>(h, i, yr);
              let v106 = rocq_array::set::<u64>(v100, r, x);
              sift(v106, sz, r, ())
            },
            sumbool::right => {
              h
            },
          }
        },
        false => {
          let v145 = andb(ltb(yl, x), ltb(i, l));
          match bdec(v145) {
            sumbool::left => {
              let v156 = rocq_array::set::<u64>(h, i, yl);
              let v162 = rocq_array::set::<u64>(v156, l, x);
              sift(v162, sz, l, ())
            },
            sumbool::right => {
              h
            },
          }
        },
      }
    },
    false => {
      h
    },
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
  let v13 = ltb(0u64, k);
  match bdec(v13) {
    sumbool::left => {
      let v32 = sift_1(h, sz, sub(k, 1u64));
      build(v32, sz, sub(k, 1u64), ())
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
  let v13 = ltb(1u64, sz);
  match bdec(v13) {
    sumbool::left => {
      let v18 = 0u64;
      let v19 = &h;
      let a = rocq_array::get::<u64>(&v19, v18);
      let sz1 = sub(sz, 1u64);
      let v34 = &h;
      let v37 = rocq_array::get::<u64>(&v34, sz1);
      let v44 = rocq_array::set::<u64>(h, 0u64, v37);
      let h1 = sift_1(v44, sz1, 0u64);
      let v55 = 0u64;
      let v56 = &h1;
      let b = rocq_array::get::<u64>(&v56, v55);
      let v75 = rocq_array::set::<u64>(h1, 0u64, add(a, b));
      let h2 = sift_1(v75, sz1, 0u64);
      let v91 = add(a, b);
      huff(h2, sz1, add(acc, v91), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      acc
    },
  }
}

// Rocq: Canvas.canvas_implem.canvas_impl
pub fn canvas_impl(x: Rc<Array<u64>>) -> u64 {
  let v1 = &x;
  let sz = rocq_array::length::<u64>(&v1);
  let v4 = &x;
  let v5 = rocq_array::copy::<u64>(&v4);
  std::mem::drop(x);
  let v13 = div(sz, 2u64);
  let h = build_1(v5, sz, v13);
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = __rocq_global_288.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_288: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = canvas(); }