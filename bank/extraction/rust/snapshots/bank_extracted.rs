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

// Rocq: Bank.bank_implem.bdec
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

// Rocq: Bank.bank_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(m: u64, k: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(m, k, a, ())
}

// Rocq: Bank.bank_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(m: u64, k: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(a, k, k);
      init_loop(m, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Bank.bank_implem.take_left
// Variant: uncurried
pub fn take_left(cash: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64) -> bool {
  if ltb(i, mid) {
    if ltb(j, hi) {
      let tmp = rocq_array::get::<u64>(&src, j);
      let tmp_1 = rocq_array::get::<u64>(&cash, tmp);
      let tmp_2 = rocq_array::get::<u64>(&src, i);
      std::mem::drop(src);
      let tmp_3 = rocq_array::get::<u64>(&cash, tmp_2);
      std::mem::drop(cash);
      leb(tmp_1, tmp_3)
    } else {
      std::mem::drop(cash);
      std::mem::drop(src);
      true
    }
  } else {
    std::mem::drop(cash);
    std::mem::drop(src);
    false
  }
}

// Rocq: Bank.bank_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(cash: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop(cash, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Bank.bank_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(cash: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let cash_clone = Rc::clone(&cash);
      let src_clone = Rc::clone(&src);
      if take_left(cash_clone, src_clone, mid, hi, i, j) {
        let tmp_1 = add(i, 1u64);
        let tmp_2 = add(k, 1u64);
        let tmp_3 = rocq_array::get::<u64>(&src, i);
        let tmp_4 = rocq_array::set::<u64>(dst, k, tmp_3);
        merge_loop(cash, src, mid, hi, tmp_1, j, tmp_2, tmp_4, ())
      } else {
        let tmp_5 = add(j, 1u64);
        let tmp_6 = add(k, 1u64);
        let tmp_7 = rocq_array::get::<u64>(&src, j);
        let tmp_8 = rocq_array::set::<u64>(dst, k, tmp_7);
        merge_loop(cash, src, mid, hi, i, tmp_5, tmp_6, tmp_8, ())
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bank.bank_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, hi: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  copy_loop(src, hi, k, dst, ())
}

// Rocq: Bank.bank_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, hi: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&src, k);
      let tmp_3 = rocq_array::set::<u64>(dst, k, tmp_2);
      copy_loop(src, hi, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Bank.bank_implem.msort
// Variant: uncurried
pub fn msort_1(cash: Rc<Array<u64>>, a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, len: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(cash, a, b, lo, len, ())
}

// Rocq: Bank.bank_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(cash: Rc<Array<u64>>, a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, len: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(1u64, len);
  match bdec(tmp) {
    sumbool::left => {
      let len1 = div(len, 2u64);
      let mid = add(lo, len1);
      let hi = add(lo, len);
      let cash_clone = Rc::clone(&cash);
      let tmp_1 = msort(cash_clone, a, b, lo, len1, ());
      match &tmp_1 {
        (b1, a1) => {
          let tmp_2 = sub(len, len1);
          let tmp_3 = ();
          let cash_clone_1 = Rc::clone(&cash);
          let b1_clone = Rc::clone(b1);
          let a1_clone = Rc::clone(a1);
          std::mem::drop(tmp_1);
          let tmp_4 = msort(cash_clone_1, b1_clone, a1_clone, mid, tmp_2, tmp_3);
          match tmp_4 {
            (v86, v88) => {
              let b2 = &v86;
              let b2_clone = Rc::clone(b2);
              let b3 = merge_loop_1(cash, b2_clone, mid, hi, lo, mid, lo, v88);
              let b3_clone = Rc::clone(&b3);
              let a3 = copy_loop_1(b3_clone, hi, lo, v86);
              (a3, b3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      (a, b)
    },
  }
}

// Rocq: Bank.bank_implem.find
// Variant: uncurried
pub fn find_1(a: Rc<Array<u64>>, x: u64) -> (Rc<Array<u64>>, u64) {
  find(a, x, ())
}

// Rocq: Bank.bank_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(a: Rc<Array<u64>>, x: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let p = rocq_array::get::<u64>(&a, x);
  let tmp = ltb(p, x);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = find(a, p, ());
      match tmp_1 {
        (v29, v31) => {
          let tmp_2 = rocq_array::set::<u64>(v29, x, v31);
          (tmp_2, v31)
        },
      }
    },
    sumbool::right => {
      (a, x)
    },
  }
}

// Rocq: Bank.bank_implem.greedy_loop
// Variant: uncurried
pub fn greedy_loop_1(cash: Rc<Array<u64>>, dl: Rc<Array<u64>>, perm: Rc<Array<u64>>, n: u64, L: u64, j: u64, uf: Rc<Array<u64>>, tot: u64) -> u64 {
  greedy_loop(cash, dl, perm, n, L, j, uf, tot, ())
}

// Rocq: Bank.bank_implem.greedy_loop (local: greedy_loop)
// Variant: uncurried, lifted
pub fn greedy_loop(cash: Rc<Array<u64>>, dl: Rc<Array<u64>>, perm: Rc<Array<u64>>, n: u64, L: u64, j: u64, uf: Rc<Array<u64>>, tot: u64, _H: ()) -> u64 {
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let i = rocq_array::get::<u64>(&perm, j);
      let d = rocq_array::get::<u64>(&dl, i);
      let c = if ltb(d, L) {
        add(d, 1u64)
      } else {
        L
      };
      let tmp_1 = find_1(uf, c);
      match tmp_1 {
        (v55, v57) => {
          if eqb(v57, 0u64) {
            greedy_loop(cash, dl, perm, n, L, add(j, 1u64), v55, tot, ())
          } else {
            let tmp_2 = add(j, 1u64);
            let tmp_3 = sub(v57, 1u64);
            let tmp_4 = rocq_array::set::<u64>(v55, v57, tmp_3);
            let tmp_5 = rocq_array::get::<u64>(&cash, i);
            greedy_loop(cash, dl, perm, n, L, tmp_2, tmp_4, add(tot, tmp_5), ())
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(cash);
      std::mem::drop(dl);
      std::mem::drop(perm);
      std::mem::drop(uf);
      tot
    },
  }
}

// Rocq: Bank.bank_implem.bank_impl
// Variant: uncurried
pub fn bank_impl(t: u64, cash: Rc<Array<u64>>, dl: Rc<Array<u64>>) -> u64 {
  let n = rocq_array::length::<u64>(&cash);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let p0 = init_loop_1(n, 0u64, tmp);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let cash_clone = Rc::clone(&cash);
  let p = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(cash_clone, p0, tmp_1, 0u64, n));
  let L = if ltb(t, n) {
    t
  } else {
    n
  };
  let tmp_2 = add(L, 1u64);
  let tmp_3 = rocq_array::make::<u64>(add(L, 1u64), 0u64);
  let uf = init_loop_1(tmp_2, 0u64, tmp_3);
  greedy_loop_1(cash, dl, p, n, L, 0u64, uf, 0u64)
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
