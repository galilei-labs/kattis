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

// Rocq: Nonnegpartsums.nonnegpartsums_implem.count_good_shifts
pub fn count_good_shifts() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>) -> u64 = count_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.bdec
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

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(x: Rc<Array<u64>>, n: u64, i: u64, P: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(x, n, i, P, ())
}

// Rocq: Nonnegpartsums.nonnegpartsums_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(x: Rc<Array<u64>>, n: u64, i: u64, P: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v31 = add(i, 1u64);
      let v33 = &P;
      let v36 = rocq_array::get::<u64>(&v33, i);
      let v37 = &x;
      let v40 = rocq_array::get::<u64>(&v37, i);
      let v52 = rocq_array::set::<u64>(P, v31, add(v36, v40));
      prefix_loop(x, n, v23, v52, ())
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
  let v13 = ltb(h, t);
  match bdec(v13) {
    sumbool::left => {
      let v24 = mod_(h, n);
      let v25 = &dq;
      let v29 = rocq_array::get::<u64>(&v25, v24);
      let v34 = add(v29, n);
      match leb(v34, j) {
        true => {
          pop_front(dq, n, j, add(h, 1u64), t, ())
        },
        false => {
          std::mem::drop(dq);
          h
        },
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
  match leb(j, n) {
    true => {
      let v11 = &P;
      let v14 = rocq_array::get::<u64>(&v11, j);
      std::mem::drop(P);
      v14
    },
    false => {
      let v23 = sub(j, n);
      let v24 = &P;
      let v27 = rocq_array::get::<u64>(&v24, v23);
      std::mem::drop(P);
      add(tot, v27)
    },
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
  let v15 = ltb(h, t);
  match bdec(v15) {
    sumbool::left => {
      let v34 = mod_(sub(t, 1u64), n);
      let v35 = &dq;
      let v38 = rocq_array::get::<u64>(&v35, v34);
      let v41 = Rc::clone(&P);
      let v48 = qv(v41, n, tot, v38);
      match lesb(qj, v48) {
        true => {
          pop_back(dq, P, n, tot, qj, h, sub(t, 1u64), ())
        },
        false => {
          std::mem::drop(P);
          std::mem::drop(dq);
          t
        },
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
  let v17 = ltb(j, m);
  match bdec(v17) {
    sumbool::left => {
      let v24 = Rc::clone(&dq);
      let h1 = pop_front_1(v24, n, j, h, t);
      let v37 = Rc::clone(&P);
      let qj = qv(v37, n, tot, j);
      let v48 = Rc::clone(&dq);
      let v51 = Rc::clone(&P);
      let t1 = pop_back_1(v48, v51, n, tot, qj, h1, t);
      let dq1 = rocq_array::set::<u64>(dq, mod_(t1, n), j);
      let cnt1 = match leb(n, j) {
        true => {
          let v90 = sub(j, n);
          let v93 = Rc::clone(&P);
          let v100 = qv(v93, n, tot, v90);
          let v107 = mod_(h1, n);
          let v108 = &dq1;
          let v111 = rocq_array::get::<u64>(&v108, v107);
          let v114 = Rc::clone(&P);
          let v121 = qv(v114, n, tot, v111);
          match lesb(v100, v121) {
            true => {
              add(cnt, 1u64)
            },
            false => {
              cnt
            },
          }
        },
        false => {
          cnt
        },
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
  let v1 = &x;
  let n = rocq_array::length::<u64>(&v1);
  let v20 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let P = prefix_loop_1(x, n, 0u64, v20);
  let v30 = &P;
  let tot = rocq_array::get::<u64>(&v30, n);
  let v40 = add(n, n);
  let v55 = rocq_array::make::<u64>(n, 0u64);
  sweep_1(P, n, tot, v40, 1u64, 0u64, 0u64, 0u64, v55)
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
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = __rocq_global_431.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_431: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = count_good_shifts(); }