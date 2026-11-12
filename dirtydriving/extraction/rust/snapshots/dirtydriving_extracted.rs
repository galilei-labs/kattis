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

// Rocq: Dirtydriving.dirtydriving_implem.dirtydriving
// Variant: uncurried
pub fn dirtydriving() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, Rc<Array<u64>>) -> u64 = dirtydriving_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Dirtydriving.dirtydriving_implem.dirtydriving
pub fn dirtydriving_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> = dirtydriving_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Dirtydriving.dirtydriving_implem.split_ok
// Variant: uncurried
pub fn split_ok(lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)))
}

// Rocq: Dirtydriving.dirtydriving_implem.bdec
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

// Rocq: Dirtydriving.dirtydriving_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let v9 = sub(hi, lo);
  add(lo, div(v9, 2u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Dirtydriving.dirtydriving_implem.take_left
// Variant: uncurried
pub fn take_left(a: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64) -> bool {
  match ltb(i, mid) {
    true => {
      match ltb(j, hi) {
        true => {
          let v20 = &a;
          let v23 = rocq_array::get::<u64>(&v20, i);
          let v24 = &a;
          let v27 = rocq_array::get::<u64>(&v24, j);
          std::mem::drop(a);
          leb(v23, v27)
        },
        false => {
          std::mem::drop(a);
          true
        },
      }
    },
    false => {
      std::mem::drop(a);
      false
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(a: Rc<Array<u64>>, t: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64) -> Rc<Array<u64>> {
  merge_loop(a, t, mid, hi, i, j, k, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(a: Rc<Array<u64>>, t: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(k, hi);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&a);
      match take_left(v22, mid, hi, i, j) {
        true => {
          let v33 = &a;
          let v36 = rocq_array::get::<u64>(&v33, i);
          let v43 = rocq_array::set::<u64>(t, k, v36);
          merge_loop(a, v43, mid, hi, add(i, 1u64), j, add(k, 1u64), ())
        },
        false => {
          let v82 = &a;
          let v85 = rocq_array::get::<u64>(&v82, j);
          let v92 = rocq_array::set::<u64>(t, k, v85);
          merge_loop(a, v92, mid, hi, i, add(j, 1u64), add(k, 1u64), ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(a);
      t
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(k, hi);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<u64>(&v16, k);
      let v26 = rocq_array::set::<u64>(dst, k, v19);
      copy_loop(src, v26, hi, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.msort
// Variant: uncurried
pub fn msort_1(a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(a, t, lo, hi, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v12 = split_ok(lo, hi);
  match bdec(v12) {
    sumbool::left => {
      let v21 = midp(lo, hi);
      let v35 = msort(a, t, lo, v21, ());
      match &v35 {
        (t1, a1) => {
          let v47 = midp(lo, hi);
          let v49 = ();
          let v52 = Rc::clone(t1);
          let v53 = Rc::clone(a1);
          std::mem::drop(v35);
          let v61 = msort(v52, v53, v47, hi, v49);
          match v61 {
            (v63, v65) => {
              let t2 = &v63;
              let v74 = midp(lo, hi);
              let v80 = midp(lo, hi);
              let v82 = Rc::clone(t2);
              let t3 = merge_loop_1(v82, v65, v74, hi, lo, v80, lo);
              let v99 = Rc::clone(&t3);
              let v107 = copy_loop_1(v99, v63, hi, lo);
              (v107, t3)
            },
          }
        },
      }
    },
    sumbool::right => {
      (a, t)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Dirtydriving.dirtydriving_implem.need
// Variant: uncurried
pub fn need(p: u64, s0: u64, x: u64, k: u64) -> u64 {
  let v13 = add(k, 1u64);
  let t = add(mul(p, v13), s0);
  match ltb(x, t) {
    true => {
      sub(t, x)
    },
    false => {
      0u64
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.max_loop
// Variant: uncurried
pub fn max_loop_1(s: Rc<Array<u64>>, p: u64, s0: u64, n: u64, k: u64, acc: u64) -> u64 {
  max_loop(s, p, s0, n, k, acc, ())
}

// Rocq: Dirtydriving.dirtydriving_implem.max_loop (local: max_loop)
// Variant: uncurried, lifted
pub fn max_loop(s: Rc<Array<u64>>, p: u64, s0: u64, n: u64, k: u64, acc: u64, _H: ()) -> u64 {
  let v14 = ltb(k, n);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &s;
      let v22 = rocq_array::get::<u64>(&v19, k);
      let v = need(p, s0, v22, k);
      let v39 = add(k, 1u64);
      let v46 = match ltb(acc, v) {
        true => {
          v
        },
        false => {
          acc
        },
      };
      max_loop(s, p, s0, n, v39, v46, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      acc
    },
  }
}

// Rocq: Dirtydriving.dirtydriving_implem.dirtydriving_impl
// Variant: uncurried
pub fn dirtydriving_impl(p: u64, d: Rc<Array<u64>>) -> u64 {
  let v2 = &d;
  let n = rocq_array::length::<u64>(&v2);
  let v12 = rocq_array::make::<u64>(n, 0u64);
  let s = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(d, v12, 0u64, n));
  let v29 = 0u64;
  let v30 = &s;
  let v33 = rocq_array::get::<u64>(&v30, v29);
  max_loop_1(s, p, v33, n, 0u64, 0u64)
}

// Rocq: Dirtydriving.dirtydriving_implem.dirtydriving_impl
pub fn dirtydriving_impl_curried(p: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v3 = {
    move |d: Rc<Array<u64>>| -> u64 {
      let v9 = Clone::clone(&p);
      dirtydriving_impl(v9, d)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = __rocq_global_478.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_478: Rc<dyn Fn(u64, Rc<Array<u64>>) -> u64> = dirtydriving(); }
std::thread_local! { static __rocq_global_481: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = dirtydriving_curried(); }