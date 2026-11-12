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

pub type uint = u64;

// Rocq: Longincsubseq.longincsubseq_implem.lis
pub fn lis() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<Array<u64>> = lis_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
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

// Rocq: Longincsubseq.longincsubseq_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Longincsubseq.longincsubseq_implem.bsearch
// Variant: uncurried
pub fn bsearch_1(x: Rc<Array<u64>>, tails: Rc<Array<u64>>, v: u64, lo: u64, hi: u64) -> u64 {
  bsearch(x, tails, v, lo, hi, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.bsearch (local: bsearch)
// Variant: uncurried, lifted
pub fn bsearch(x: Rc<Array<u64>>, tails: Rc<Array<u64>>, v: u64, lo: u64, hi: u64, _H: ()) -> u64 {
  let v13 = ltb(lo, hi);
  match bdec(v13) {
    sumbool::left => {
      let v24 = sub(hi, lo);
      let mid = add(lo, div(v24, 2u64));
      let v39 = &tails;
      let v42 = rocq_array::get::<u64>(&v39, mid);
      let v43 = &x;
      let v47 = rocq_array::get::<u64>(&v43, v42);
      let v52 = ltsb(v47, v);
      match bdec(v52) {
        sumbool::left => {
          bsearch(x, tails, v, add(mid, 1u64), hi, ())
        },
        sumbool::right => {
          bsearch(x, tails, v, lo, mid, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(tails);
      lo
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.main_loop
// Variant: uncurried
pub fn main_loop_1(x: Rc<Array<u64>>, n: u64, i: u64, L: u64, tails: Rc<Array<u64>>, pred: Rc<Array<u64>>) -> (u64, (Rc<Array<u64>>, Rc<Array<u64>>)) {
  main_loop(x, n, i, L, tails, pred, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.main_loop (local: main_loop)
// Variant: uncurried, lifted
pub fn main_loop(x: Rc<Array<u64>>, n: u64, i: u64, L: u64, tails: Rc<Array<u64>>, pred: Rc<Array<u64>>, _H: ()) -> (u64, (Rc<Array<u64>>, Rc<Array<u64>>)) {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v18 = &x;
      let v = rocq_array::get::<u64>(&v18, i);
      let v27 = Rc::clone(&x);
      let v30 = Rc::clone(&tails);
      let k = bsearch_1(v27, v30, v, 0u64, L);
      let v40 = 0u64;
      let p = match eqb(k, v40) {
        true => {
          0u64
        },
        false => {
          let v58 = sub(k, 1u64);
          let v59 = &tails;
          rocq_array::get::<u64>(&v59, v58)
        },
      };
      let pred_ = rocq_array::set::<u64>(pred, i, p);
      let tails_ = rocq_array::set::<u64>(tails, k, i);
      let v87 = add(i, 1u64);
      let v94 = match eqb(k, L) {
        true => {
          add(L, 1u64)
        },
        false => {
          L
        },
      };
      main_loop(x, n, v87, v94, tails_, pred_, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (L, (tails, pred))
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.build
// Variant: uncurried
pub fn build_1(pred: Rc<Array<u64>>, c: u64, j: u64, res: Rc<Array<u64>>) -> Rc<Array<u64>> {
  build(pred, c, j, res, ())
}

// Rocq: Longincsubseq.longincsubseq_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(pred: Rc<Array<u64>>, c: u64, j: u64, res: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(0u64, c);
  match bdec(v14) {
    sumbool::left => {
      let v25 = sub(c, 1u64);
      let v26 = &pred;
      let v29 = rocq_array::get::<u64>(&v26, j);
      let v44 = rocq_array::set::<u64>(res, sub(c, 1u64), j);
      build(pred, v25, v29, v44, ())
    },
    sumbool::right => {
      std::mem::drop(pred);
      res
    },
  }
}

// Rocq: Longincsubseq.longincsubseq_implem.lis_impl
pub fn lis_impl(x: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v1 = &x;
  let n = rocq_array::length::<u64>(&v1);
  let v14 = rocq_array::make::<u64>(n, 0u64);
  let v21 = rocq_array::make::<u64>(n, 0u64);
  let v34 = main_loop_1(x, n, 0u64, 0u64, v14, v21);
  match v34 {
    (v36, v38) => {
      match v38 {
        (v41, v43) => {
          let pred = &v41;
          let v55 = sub(v36, 1u64);
          let v57 = rocq_array::get::<u64>(&pred, v55);
          std::mem::drop(v41);
          let v64 = rocq_array::make::<u64>(v36, 0u64);
          build_1(v43, v36, v57, v64)
        },
      }
    },
  }
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_318.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_318: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = lis(); }