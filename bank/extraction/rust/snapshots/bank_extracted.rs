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

// Rocq: Bank.bank_implem.bank
// Variant: uncurried
pub fn bank() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = bank_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Bank.bank_implem.bank
pub fn bank_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = bank_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v0);
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

// Rocq: Bank.bank_implem.bdec
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

// Rocq: Bank.bank_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(m: u64, k: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  init_loop(m, k, a, ())
}

// Rocq: Bank.bank_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(m: u64, k: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(k, m);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(k, 1u64);
      let v29 = rocq_array::set::<u64>(a, k, k);
      init_loop(m, v22, v29, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
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
  match ltb(i, mid) {
    true => {
      match ltb(j, hi) {
        true => {
          let v21 = &src;
          let v24 = rocq_array::get::<u64>(&v21, j);
          let v25 = &cash;
          let v28 = rocq_array::get::<u64>(&v25, v24);
          let v29 = &src;
          let v32 = rocq_array::get::<u64>(&v29, i);
          std::mem::drop(src);
          let v33 = &cash;
          let v36 = rocq_array::get::<u64>(&v33, v32);
          std::mem::drop(cash);
          leb(v28, v36)
        },
        false => {
          std::mem::drop(cash);
          std::mem::drop(src);
          true
        },
      }
    },
    false => {
      std::mem::drop(cash);
      std::mem::drop(src);
      false
    },
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
  let v16 = ltb(k, hi);
  match bdec(v16) {
    sumbool::left => {
      let v23 = Rc::clone(&cash);
      let v26 = Rc::clone(&src);
      match take_left(v23, v26, mid, hi, i, j) {
        true => {
          let v44 = add(i, 1u64);
          let v52 = add(k, 1u64);
          let v53 = &src;
          let v56 = rocq_array::get::<u64>(&v53, i);
          let v63 = rocq_array::set::<u64>(dst, k, v56);
          merge_loop(cash, src, mid, hi, v44, j, v52, v63, ())
        },
        false => {
          let v95 = add(j, 1u64);
          let v103 = add(k, 1u64);
          let v104 = &src;
          let v107 = rocq_array::get::<u64>(&v104, j);
          let v114 = rocq_array::set::<u64>(dst, k, v107);
          merge_loop(cash, src, mid, hi, i, v95, v103, v114, ())
        },
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
  let v12 = ltb(k, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(k, 1u64);
      let v24 = &src;
      let v27 = rocq_array::get::<u64>(&v24, k);
      let v34 = rocq_array::set::<u64>(dst, k, v27);
      copy_loop(src, hi, v23, v34, ())
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
  let v15 = ltb(1u64, len);
  match bdec(v15) {
    sumbool::left => {
      let len1 = div(len, 2u64);
      let mid = add(lo, len1);
      let hi = add(lo, len);
      let v44 = Rc::clone(&cash);
      let v55 = msort(v44, a, b, lo, len1, ());
      match &v55 {
        (b1, a1) => {
          let v67 = sub(len, len1);
          let v69 = ();
          let v73 = Rc::clone(&cash);
          let v75 = Rc::clone(b1);
          let v76 = Rc::clone(a1);
          std::mem::drop(v55);
          let v84 = msort(v73, v75, v76, mid, v67, v69);
          match v84 {
            (v86, v88) => {
              let b2 = &v86;
              let v95 = Rc::clone(b2);
              let b3 = merge_loop_1(cash, v95, mid, hi, lo, mid, lo, v88);
              let v112 = Rc::clone(&b3);
              let a3 = copy_loop_1(v112, hi, lo, v86);
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
  let v3 = &a;
  let p = rocq_array::get::<u64>(&v3, x);
  let v14 = ltb(p, x);
  match bdec(v14) {
    sumbool::left => {
      let v27 = find(a, p, ());
      match v27 {
        (v29, v31) => {
          let v40 = rocq_array::set::<u64>(v29, x, v31);
          (v40, v31)
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
  let v16 = ltb(j, n);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &perm;
      let i = rocq_array::get::<u64>(&v20, j);
      let v24 = &dl;
      let d = rocq_array::get::<u64>(&v24, i);
      let c = match ltb(d, L) {
        true => {
          add(d, 1u64)
        },
        false => {
          L
        },
      };
      let v53 = find_1(uf, c);
      match v53 {
        (v55, v57) => {
          match eqb(v57, 0u64) {
            true => {
              greedy_loop(cash, dl, perm, n, L, add(j, 1u64), v55, tot, ())
            },
            false => {
              let v107 = add(j, 1u64);
              let v115 = sub(v57, 1u64);
              let v122 = rocq_array::set::<u64>(v55, v57, v115);
              let v124 = &cash;
              let v127 = rocq_array::get::<u64>(&v124, i);
              greedy_loop(cash, dl, perm, n, L, v107, v122, add(tot, v127), ())
            },
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
  let v3 = &cash;
  let n = rocq_array::length::<u64>(&v3);
  let v14 = rocq_array::make::<u64>(n, 0u64);
  let p0 = init_loop_1(n, 0u64, v14);
  let v30 = rocq_array::make::<u64>(n, 0u64);
  let v35 = Rc::clone(&cash);
  let p = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(v35, p0, v30, 0u64, n));
  let L = match ltb(t, n) {
    true => {
      t
    },
    false => {
      n
    },
  };
  let v68 = add(L, 1u64);
  let v85 = rocq_array::make::<u64>(add(L, 1u64), 0u64);
  let uf = init_loop_1(v68, 0u64, v85);
  greedy_loop_1(cash, dl, p, n, L, 0u64, uf, 0u64)
}

// Rocq: Bank.bank_implem.bank_impl
pub fn bank_impl_curried(t: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
  let v3 = {
    move |cash: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
      let t = &t;
      let v8 = Clone::clone(t);
      let v11 = {
        move |dl: Rc<Array<u64>>| -> u64 {
          let v19 = Clone::clone(&v8);
          let v21 = Rc::clone(&cash);
          bank_impl(v19, v21, dl)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_554.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_554: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = bank(); }
std::thread_local! { static __rocq_global_557: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = bank_curried(); }