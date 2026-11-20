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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.bdec
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

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(x: Rc<Array<u64>>, n: u64, i: u64, P: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(x, n, i, P, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(x: Rc<Array<u64>>, n: u64, i: u64, P: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&P, i);
      let tmp_4 = rocq_array::get::<u64>(&x, i);
      let tmp_5 = rocq_array::set::<u64>(P, tmp_2, add(tmp_3, tmp_4));
      prefix_loop(x, n, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      P
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_front
// Variant: uncurried
pub fn pop_front_1(dq: Rc<Array<u64>>, n: u64, j: u64, h: u64, t: u64) -> u64 {
  pop_front(dq, n, j, h, t, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_front (local: pop_front)
// Variant: uncurried, lifted
pub fn pop_front(dq: Rc<Array<u64>>, n: u64, j: u64, h: u64, t: u64, _H: ()) -> u64 {
  let tmp = ltb(h, t);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&dq, mod_(h, n));
      let tmp_2 = add(tmp_1, n);
      if leb(tmp_2, j) {
        pop_front(dq, n, j, add(h, 1u64), t, ())
      } else {
        std::mem::drop(dq);
        h
      }
    },
    sumbool::right => {
      std::mem::drop(dq);
      h
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.qv
// Variant: uncurried
pub fn qv(P: Rc<Array<u64>>, n: u64, tot: u64, j: u64) -> u64 {
  if leb(j, n) {
    let tmp = rocq_array::get::<u64>(&P, j);
    std::mem::drop(P);
    tmp
  } else {
    let tmp_1 = rocq_array::get::<u64>(&P, sub(j, n));
    std::mem::drop(P);
    add(tot, tmp_1)
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_back
// Variant: uncurried
pub fn pop_back_1(dq: Rc<Array<u64>>, P: Rc<Array<u64>>, n: u64, tot: u64, qj: u64, h: u64, t: u64) -> u64 {
  pop_back(dq, P, n, tot, qj, h, t, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.pop_back (local: pop_back)
// Variant: uncurried, lifted
pub fn pop_back(dq: Rc<Array<u64>>, P: Rc<Array<u64>>, n: u64, tot: u64, qj: u64, h: u64, t: u64, _H: ()) -> u64 {
  let tmp = ltb(h, t);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&dq, mod_(sub(t, 1u64), n));
      let P_clone = Rc::clone(&P);
      let tmp_2 = qv(P_clone, n, tot, tmp_1);
      if lesb(qj, tmp_2) {
        pop_back(dq, P, n, tot, qj, h, sub(t, 1u64), ())
      } else {
        std::mem::drop(P);
        std::mem::drop(dq);
        t
      }
    },
    sumbool::right => {
      std::mem::drop(dq);
      std::mem::drop(P);
      t
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.sweep
// Variant: uncurried
pub fn sweep_1(P: Rc<Array<u64>>, n: u64, tot: u64, m: u64, j: u64, h: u64, t: u64, cnt: u64, dq: Rc<Array<u64>>) -> u64 {
  sweep(P, n, tot, m, j, h, t, cnt, dq, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(P: Rc<Array<u64>>, n: u64, tot: u64, m: u64, j: u64, h: u64, t: u64, cnt: u64, dq: Rc<Array<u64>>, _H: ()) -> u64 {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let dq_clone = Rc::clone(&dq);
      let h1 = pop_front_1(dq_clone, n, j, h, t);
      let P_clone = Rc::clone(&P);
      let qj = qv(P_clone, n, tot, j);
      let dq_clone_1 = Rc::clone(&dq);
      let P_clone_1 = Rc::clone(&P);
      let t1 = pop_back_1(dq_clone_1, P_clone_1, n, tot, qj, h1, t);
      let dq1 = rocq_array::set::<u64>(dq, mod_(t1, n), j);
      let cnt1 = if leb(n, j) {
        let tmp_1 = sub(j, n);
        let P_clone_2 = Rc::clone(&P);
        let tmp_2 = qv(P_clone_2, n, tot, tmp_1);
        let tmp_3 = rocq_array::get::<u64>(&dq1, mod_(h1, n));
        let P_clone_3 = Rc::clone(&P);
        let tmp_4 = qv(P_clone_3, n, tot, tmp_3);
        if lesb(tmp_2, tmp_4) {
          add(cnt, 1u64)
        } else {
          cnt
        }
      } else {
        cnt
      };
      sweep(P, n, tot, m, add(j, 1u64), h1, add(t1, 1u64), cnt1, dq1, ())
    },
    sumbool::right => {
      std::mem::drop(P);
      std::mem::drop(dq);
      cnt
    },
  }
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.count_impl
pub fn count_impl(x: Rc<Array<u64>>) -> u64 {
  let n = rocq_array::length::<u64>(&x);
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let P = prefix_loop_1(x, n, 0u64, tmp);
  let tot = rocq_array::get::<u64>(&P, n);
  let tmp_1 = add(n, n);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  sweep_1(P, n, tot, tmp_1, 1u64, 0u64, 0u64, 0u64, tmp_2)
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
