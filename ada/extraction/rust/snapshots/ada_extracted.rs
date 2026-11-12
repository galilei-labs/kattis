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

// Rocq: Ada.ada_implem.ada
pub fn ada() -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> {
  let v0: fn(Rc<Array<u64>>) -> (u64, u64) = ada_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> = Rc::new(v0);
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

// Rocq: Ada.ada_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Ada.ada_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(m: u64, j: u64, t: Rc<Array<u64>>, nz: bool) -> (Rc<Array<u64>>, bool) {
  row_loop(m, j, t, nz, ())
}

// Rocq: Ada.ada_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(m: u64, j: u64, t: Rc<Array<u64>>, nz: bool, _H: ()) -> (Rc<Array<u64>>, bool) {
  let v12 = ltb(j, m);
  match bdec(v12) {
    sumbool::left => {
      let v24 = add(j, 1u64);
      let v25 = &t;
      let v28 = rocq_array::get::<u64>(&v25, v24);
      let v29 = &t;
      let v32 = rocq_array::get::<u64>(&v29, j);
      let x = sub(v28, v32);
      let v45 = add(j, 1u64);
      let v52 = rocq_array::set::<u64>(t, j, x);
      row_loop(m, v45, v52, orb(nz, negb(eqb(x, 0u64))), ())
    },
    sumbool::right => {
      (t, nz)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Ada.ada_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(n: u64, k: u64, t: Rc<Array<u64>>, d: u64) -> (Rc<Array<u64>>, u64) {
  rows_loop(n, k, t, d, ())
}

// Rocq: Ada.ada_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(n: u64, k: u64, t: Rc<Array<u64>>, d: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let v12 = ltb(k, n);
  match bdec(v12) {
    sumbool::left => {
      let r = row_loop_1(sub(n, k), 0u64, t, false);
      let v43 = add(k, 1u64);
      let v46 = Clone::clone(&r);
      let v48 = fst::<Rc<Array<u64>>, bool>(v46);
      let v53 = match snd::<Rc<Array<u64>>, bool>(r) {
        true => {
          k
        },
        false => {
          d
        },
      };
      rows_loop(n, v43, v48, v53, ())
    },
    sumbool::right => {
      (t, d)
    },
  }
}

// Rocq: Ada.ada_implem.acopy
pub fn acopy(t: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v1 = &t;
  let v2 = rocq_array::copy::<u64>(&v1);
  std::mem::drop(t);
  v2
}

// Rocq: Ada.ada_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(t: Rc<Array<u64>>, top: u64, e: u64, k: u64, acc: u64) -> u64 {
  sum_loop(t, top, e, k, acc, ())
}

// Rocq: Ada.ada_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(t: Rc<Array<u64>>, top: u64, e: u64, k: u64, acc: u64, _H: ()) -> u64 {
  let v13 = ltb(k, e);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(k, 1u64);
      let v31 = sub(top, k);
      let v32 = &t;
      let v35 = rocq_array::get::<u64>(&v32, v31);
      sum_loop(t, top, e, v24, add(acc, v35), ())
    },
    sumbool::right => {
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Ada.ada_implem.ada_impl
pub fn ada_impl(a: Rc<Array<u64>>) -> (u64, u64) {
  let v1 = &a;
  let n = rocq_array::length::<u64>(&v1);
  let v9 = acopy(a);
  let v20 = rows_loop_1(n, 1u64, v9, 0u64);
  match v20 {
    (v22, v24) => {
      let v34 = sub(n, 1u64);
      let v42 = add(v24, 1u64);
      (v24, sum_loop_1(v22, v34, v42, 0u64, 0u64))
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> = __rocq_global_289.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_289: Rc<dyn Fn(Rc<Array<u64>>) -> (u64, u64)> = ada(); }