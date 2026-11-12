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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

// Rocq: Knapsack.knapsack_implem.knapsack
// Variant: uncurried
pub fn knapsack() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> {
  let v0: fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>) = knapsack_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> = Rc::new(v0);
  v1
}

// Rocq: Knapsack.knapsack_implem.knapsack
pub fn knapsack_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>> = knapsack_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Knapsack.knapsack_implem.bdec
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

// Rocq: Knapsack.knapsack_implem.item_loop
// Variant: uncurried
pub fn item_loop_1(v: u64, w: u64, base: u64, k: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  item_loop(v, w, base, k, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.item_loop (local: item_loop)
// Variant: uncurried, lifted
pub fn item_loop(v: u64, w: u64, base: u64, k: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  let v14 = ltb(w, k);
  match bdec(v14) {
    sumbool::left => {
      let c = sub(k, 1u64);
      let v32 = sub(c, w);
      let v33 = &row;
      let v37 = rocq_array::get::<u64>(&v33, v32);
      let cand = add(v37, v);
      let v43 = &row;
      let v47 = rocq_array::get::<u64>(&v43, c);
      match ltb(v47, cand) {
        true => {
          let v59 = rocq_array::set::<u64>(row, c, cand);
          let v74 = rocq_array::set::<bool>(dec, add(base, c), true);
          item_loop(v, w, base, c, v59, v74, ())
        },
        false => {
          item_loop(v, w, base, c, row, dec, ())
        },
      }
    },
    sumbool::right => {
      (row, dec)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
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

// Rocq: Knapsack.knapsack_implem.items_loop
// Variant: uncurried
pub fn items_loop_1(xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, n: u64, C1: u64, i: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  items_loop(xv, xw, n, C1, i, row, dec, ())
}

// Rocq: Knapsack.knapsack_implem.items_loop (local: items_loop)
// Variant: uncurried, lifted
pub fn items_loop(xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, n: u64, C1: u64, i: u64, row: Rc<Array<u64>>, dec: Rc<Array<bool>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<bool>>) {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v20 = &xv;
      let v23 = rocq_array::get::<u64>(&v20, i);
      let v24 = &xw;
      let v27 = rocq_array::get::<u64>(&v24, i);
      let rd = item_loop_1(v23, v27, mul(i, C1), C1, row, dec);
      let v54 = add(i, 1u64);
      let v57 = Clone::clone(&rd);
      let v59 = fst::<Rc<Array<u64>>, Rc<Array<bool>>>(v57);
      let v63 = snd::<Rc<Array<u64>>, Rc<Array<bool>>>(rd);
      items_loop(xv, xw, n, C1, v54, v59, v63, ())
    },
    sumbool::right => {
      std::mem::drop(xv);
      std::mem::drop(xw);
      (row, dec)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.walk
// Variant: uncurried
pub fn walk_1(xw: Rc<Array<u64>>, dec: Rc<Array<bool>>, C1: u64, i: u64, c: u64, k: u64, out: Rc<Array<u64>>) -> (u64, Rc<Array<u64>>) {
  walk(xw, dec, C1, i, c, k, out, ())
}

// Rocq: Knapsack.knapsack_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(xw: Rc<Array<u64>>, dec: Rc<Array<bool>>, C1: u64, i: u64, c: u64, k: u64, out: Rc<Array<u64>>, _H: ()) -> (u64, Rc<Array<u64>>) {
  let v17 = ltb(0u64, i);
  match bdec(v17) {
    sumbool::left => {
      let j = sub(i, 1u64);
      let v40 = add(mul(j, C1), c);
      let v41 = &dec;
      let v44 = rocq_array::get::<bool>(&v41, v40);
      match v44 {
        true => {
          let v47 = &xw;
          let v50 = rocq_array::get::<u64>(&v47, j);
          let v55 = sub(c, v50);
          let v63 = add(k, 1u64);
          let v70 = rocq_array::set::<u64>(out, k, j);
          walk(xw, dec, C1, j, v55, v63, v70, ())
        },
        false => {
          walk(xw, dec, C1, j, c, k, out, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xw);
      std::mem::drop(dec);
      (k, out)
    },
  }
}

// Rocq: Knapsack.knapsack_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, m: u64, j: u64) -> Rc<Array<u64>> {
  copy_loop(src, dst, m, j, ())
}

// Rocq: Knapsack.knapsack_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, m: u64, j: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(j, m);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<u64>(&v16, j);
      let v26 = rocq_array::set::<u64>(dst, j, v19);
      copy_loop(src, v26, m, add(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Knapsack.knapsack_implem.knapsack_impl
// Variant: uncurried
pub fn knapsack_impl(Cw: u64, xv: Rc<Array<u64>>, xw: Rc<Array<u64>>) -> (u64, Rc<Array<u64>>) {
  let v3 = &xv;
  let n = rocq_array::length::<u64>(&v3);
  let C1 = add(Cw, 1u64);
  let v22 = rocq_array::make::<u64>(C1, 0u64);
  let v35 = rocq_array::make::<bool>(mul(n, C1), false);
  let v40 = Rc::clone(&xw);
  let rd = items_loop_1(xv, v40, n, C1, 0u64, v22, v35);
  let v54 = Clone::clone(&rd);
  let v56 = fst::<Rc<Array<u64>>, Rc<Array<bool>>>(v54);
  let v57 = &v56;
  let bestv = rocq_array::get::<u64>(&v57, Cw);
  std::mem::drop(v56);
  let v65 = snd::<Rc<Array<u64>>, Rc<Array<bool>>>(rd);
  let v74 = rocq_array::make::<u64>(n, 0u64);
  let ko = walk_1(xw, v65, C1, n, Cw, 0u64, v74);
  let v92 = Clone::clone(&ko);
  let k = fst::<u64, Rc<Array<u64>>>(v92);
  let v99 = snd::<u64, Rc<Array<u64>>>(ko);
  let v106 = rocq_array::make::<u64>(k, 0u64);
  let v117 = copy_loop_1(v99, v106, k, 0u64);
  (bestv, v117)
}

// Rocq: Knapsack.knapsack_implem.knapsack_impl
pub fn knapsack_impl_curried(Cw: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>> {
  let v3 = {
    move |xv: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> {
      let Cw = &Cw;
      let v8 = Clone::clone(Cw);
      let v11 = {
        move |xw: Rc<Array<u64>>| -> (u64, Rc<Array<u64>>) {
          let v19 = Clone::clone(&v8);
          let v21 = Rc::clone(&xv);
          knapsack_impl(v19, v21, xw)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> = __rocq_global_404.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_404: Rc<dyn Fn(u64, Rc<Array<u64>>, Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)> = knapsack(); }
std::thread_local! { static __rocq_global_407: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> (u64, Rc<Array<u64>>)>>> = knapsack_curried(); }