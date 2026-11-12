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

// Rocq: Cudak.cudak_implem.cudak
// Variant: uncurried
pub fn cudak() -> Rc<dyn Fn(u64, u64, u64) -> (u64, u64)> {
  let v0: fn(u64, u64, u64) -> (u64, u64) = cudak_impl;
  let v1: Rc<dyn Fn(u64, u64, u64) -> (u64, u64)> = Rc::new(v0);
  v1
}

// Rocq: Cudak.cudak_implem.cudak
pub fn cudak_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = cudak_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Cudak.cudak_implem.bdec
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

// Rocq: Cudak.cudak_implem.digits
// Variant: uncurried
pub fn digits_1(b: u64, d: u64, q: u64) -> (u64, u64) {
  digits(b, d, q, ())
}

// Rocq: Cudak.cudak_implem.digits (local: digits)
// Variant: uncurried, lifted
pub fn digits(b: u64, d: u64, q: u64, _H: ()) -> (u64, u64) {
  let v33 = andb(ltb(d, 15u64), leb(mul(q, 10u64), b));
  match bdec(v33) {
    sumbool::left => {
      digits(b, add(d, 1u64), mul(q, 10u64), ())
    },
    sumbool::right => {
      (d, q)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Cudak.cudak_implem.vcell
// Variant: uncurried
pub fn vcell(T: Rc<Array<u64>>, base: u64, t: u64, c: u64) -> u64 {
  match leb(c, t) {
    true => {
      let v22 = add(base, sub(t, c));
      let v23 = &T;
      let v26 = rocq_array::get::<u64>(&v23, v22);
      std::mem::drop(T);
      v26
    },
    false => {
      std::mem::drop(T);
      0u64
    },
  }
}

// Rocq: Cudak.cudak_implem.rowsum
// Variant: uncurried
pub fn rowsum_1(T: Rc<Array<u64>>, base: u64, t: u64, c: u64, d: u64, acc: u64) -> u64 {
  rowsum(T, base, t, c, d, acc, ())
}

// Rocq: Cudak.cudak_implem.rowsum (local: rowsum)
// Variant: uncurried, lifted
pub fn rowsum(T: Rc<Array<u64>>, base: u64, t: u64, c: u64, d: u64, acc: u64, _H: ()) -> u64 {
  let v14 = ltb(d, c);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(d, 1u64);
      let v30 = Rc::clone(&T);
      let v37 = vcell(v30, base, t, d);
      rowsum(T, base, t, c, v25, add(acc, v37), ())
    },
    sumbool::right => {
      std::mem::drop(T);
      acc
    },
  }
}

// Rocq: Cudak.cudak_implem.fill
// Variant: uncurried
pub fn fill_1(T: Rc<Array<u64>>, s: u64, S1: u64, n: u64, idx: u64, k: u64, u: u64) -> Rc<Array<u64>> {
  fill(T, s, S1, n, idx, k, u, ())
}

// Rocq: Cudak.cudak_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(T: Rc<Array<u64>>, s: u64, S1: u64, n: u64, idx: u64, k: u64, u: u64, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(idx, n);
  match bdec(v15) {
    sumbool::left => {
      let v33 = mul(sub(k, 1u64), S1);
      let v42 = Rc::clone(&T);
      let v60 = rocq_array::set::<u64>(T, idx, rowsum_1(v42, v33, u, 10u64, 0u64, 0u64));
      let v68 = add(idx, 1u64);
      let v75 = match eqb(u, s) {
        true => {
          add(k, 1u64)
        },
        false => {
          k
        },
      };
      let v95 = match eqb(u, s) {
        true => {
          0u64
        },
        false => {
          add(u, 1u64)
        },
      };
      fill(v60, s, S1, n, v68, v75, v95, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Cudak.cudak_implem.walk
// Variant: uncurried
pub fn walk_1(T: Rc<Array<u64>>, S1: u64, j: u64, p: u64, R: u64, t: u64, acc: u64) -> u64 {
  walk(T, S1, j, p, R, t, acc, ())
}

// Rocq: Cudak.cudak_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(T: Rc<Array<u64>>, S1: u64, j: u64, p: u64, R: u64, t: u64, acc: u64, _H: ()) -> u64 {
  let v17 = ltb(0u64, j);
  match bdec(v17) {
    sumbool::left => {
      let c = div(R, p);
      let v41 = mul(sub(j, 1u64), S1);
      let v46 = Rc::clone(&T);
      let acc_ = rowsum_1(v46, v41, t, c, 0u64, acc);
      match ltb(t, c) {
        true => {
          std::mem::drop(T);
          acc_
        },
        false => {
          walk(T, S1, sub(j, 1u64), div(p, 10u64), mod_(R, p), sub(t, c), acc_, ())
        },
      }
    },
    sumbool::right => {
      match eqb(t, 0u64) {
        true => {
          std::mem::drop(T);
          add(acc, 1u64)
        },
        false => {
          std::mem::drop(T);
          acc
        },
      }
    },
  }
}

// Rocq: Cudak.cudak_implem.pick
// Variant: uncurried
pub fn pick_1(T: Rc<Array<u64>>, base: u64, t: u64, c: u64, r: u64) -> (u64, u64) {
  pick(T, base, t, c, r, ())
}

// Rocq: Cudak.cudak_implem.pick (local: pick)
// Variant: uncurried, lifted
pub fn pick(T: Rc<Array<u64>>, base: u64, t: u64, c: u64, r: u64, _H: ()) -> (u64, u64) {
  let v15 = ltb(c, 9u64);
  let v20 = Rc::clone(&T);
  let v38 = andb(v15, ltb(vcell(v20, base, t, c), r));
  match bdec(v38) {
    sumbool::left => {
      let v49 = add(c, 1u64);
      let v54 = Rc::clone(&T);
      let v61 = vcell(v54, base, t, c);
      pick(T, base, t, v49, sub(r, v61), ())
    },
    sumbool::right => {
      std::mem::drop(T);
      (c, r)
    },
  }
}

// Rocq: Cudak.cudak_implem.minwalk
// Variant: uncurried
pub fn minwalk_1(T: Rc<Array<u64>>, S1: u64, j: u64, t: u64, r: u64, x: u64) -> u64 {
  minwalk(T, S1, j, t, r, x, ())
}

// Rocq: Cudak.cudak_implem.minwalk (local: minwalk)
// Variant: uncurried, lifted
pub fn minwalk(T: Rc<Array<u64>>, S1: u64, j: u64, t: u64, r: u64, x: u64, _H: ()) -> u64 {
  let v16 = ltb(0u64, j);
  match bdec(v16) {
    sumbool::left => {
      let v34 = mul(sub(j, 1u64), S1);
      let v39 = Rc::clone(&T);
      let cr = pick_1(v39, v34, t, 0u64, r);
      let v56 = sub(j, 1u64);
      let v60 = Clone::clone(&cr);
      let v67 = sub(t, fst::<u64, u64>(v60));
      let v70 = Clone::clone(&cr);
      minwalk(T, S1, v56, v67, snd::<u64, u64>(v70), add(mul(x, 10u64), fst::<u64, u64>(cr)), ())
    },
    sumbool::right => {
      std::mem::drop(T);
      x
    },
  }
}

// Rocq: Cudak.cudak_implem.cudak_impl
// Variant: uncurried
pub fn cudak_impl(a: u64, b: u64, s: u64) -> (u64, u64) {
  let S1 = add(s, 1u64);
  let dq = digits_1(b, 1u64, 1u64);
  let v25 = Clone::clone(&dq);
  let D = fst::<u64, u64>(v25);
  let q = snd::<u64, u64>(dq);
  let n = mul(D, S1);
  let v45 = rocq_array::make::<u64>(n, 0u64);
  let v56 = rocq_array::set::<u64>(v45, 0u64, 1u64);
  let T = fill_1(v56, s, S1, n, S1, 1u64, 0u64);
  let v81 = Rc::clone(&T);
  let cb = walk_1(v81, S1, D, q, b, s, 0u64);
  let v103 = sub(a, 1u64);
  let v108 = Rc::clone(&T);
  let ca = walk_1(v108, S1, D, q, v103, s, 0u64);
  (sub(cb, ca), minwalk_1(T, S1, D, s, add(ca, 1u64), 0u64))
}

// Rocq: Cudak.cudak_implem.cudak_impl
pub fn cudak_impl_curried(a: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> {
  let v3 = {
    move |b: u64| -> Rc<dyn Fn(u64) -> (u64, u64)> {
      let a = &a;
      let v8 = Clone::clone(a);
      let v11 = {
        move |s: u64| -> (u64, u64) {
          let v19 = Clone::clone(&v8);
          let v21 = Clone::clone(&b);
          cudak_impl(v19, v21, s)
        }
      };
      let v27: Rc<dyn Fn(u64) -> (u64, u64)> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, u64, u64) -> (u64, u64)> {
  let v0: Rc<dyn Fn(u64, u64, u64) -> (u64, u64)> = __rocq_global_643.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_643: Rc<dyn Fn(u64, u64, u64) -> (u64, u64)> = cudak(); }
std::thread_local! { static __rocq_global_646: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> (u64, u64)>>> = cudak_curried(); }