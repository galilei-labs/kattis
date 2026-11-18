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

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Dirtydriving.dirtydriving_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Dirtydriving.dirtydriving_implem.take_left
// Variant: uncurried
pub fn take_left(a: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64) -> bool {
  if ltb(i, mid) {
    if ltb(j, hi) {
      let tmp = rocq_array::get::<u64>(&a, i);
      let tmp_1 = rocq_array::get::<u64>(&a, j);
      std::mem::drop(a);
      leb(tmp, tmp_1)
    } else {
      std::mem::drop(a);
      true
    }
  } else {
    std::mem::drop(a);
    false
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
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let a_clone = Rc::clone(&a);
      if take_left(a_clone, mid, hi, i, j) {
        let tmp_1 = rocq_array::get::<u64>(&a, i);
        let tmp_2 = rocq_array::set::<u64>(t, k, tmp_1);
        merge_loop(a, tmp_2, mid, hi, add(i, 1u64), j, add(k, 1u64), ())
      } else {
        let tmp_3 = rocq_array::get::<u64>(&a, j);
        let tmp_4 = rocq_array::set::<u64>(t, k, tmp_3);
        merge_loop(a, tmp_4, mid, hi, i, add(j, 1u64), add(k, 1u64), ())
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
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&src, k);
      let tmp_2 = rocq_array::set::<u64>(dst, k, tmp_1);
      copy_loop(src, tmp_2, hi, add(k, 1u64), ())
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
  let tmp = split_ok(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let tmp_2 = msort(a, t, lo, tmp_1, ());
      match &tmp_2 {
        (t1, a1) => {
          let tmp_3 = midp(lo, hi);
          let tmp_4 = ();
          let t1_clone = Rc::clone(t1);
          let a1_clone = Rc::clone(a1);
          std::mem::drop(tmp_2);
          let tmp_5 = msort(t1_clone, a1_clone, tmp_3, hi, tmp_4);
          match tmp_5 {
            (v63, v65) => {
              let t2 = &v63;
              let tmp_6 = midp(lo, hi);
              let tmp_7 = midp(lo, hi);
              let t2_clone = Rc::clone(t2);
              let t3 = merge_loop_1(t2_clone, v65, tmp_6, hi, lo, tmp_7, lo);
              let t3_clone = Rc::clone(&t3);
              let tmp_8 = copy_loop_1(t3_clone, v63, hi, lo);
              (tmp_8, t3)
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
  let tmp = add(k, 1u64);
  let t = add(mul(p, tmp), s0);
  if ltb(x, t) {
    sub(t, x)
  } else {
    0u64
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
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&s, k);
      let v = need(p, s0, tmp_1, k);
      let tmp_2 = add(k, 1u64);
      let tmp_3 = if ltb(acc, v) {
        v
      } else {
        acc
      };
      max_loop(s, p, s0, n, tmp_2, tmp_3, ())
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
  let n = rocq_array::length::<u64>(&d);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let s = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(d, tmp, 0u64, n));
  let tmp_1 = rocq_array::get::<u64>(&s, 0u64);
  max_loop_1(s, p, tmp_1, n, 0u64, 0u64)
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
