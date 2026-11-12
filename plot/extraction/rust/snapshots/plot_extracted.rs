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

pub type sint = u64;

// Rocq: Plot.plot_implem.plot
// Variant: uncurried
pub fn plot() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>> = plot_impl;
  let v1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Plot.plot_implem.plot
pub fn plot_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = plot_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Plot.plot_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Plot.plot_implem.horner_loop
// Variant: uncurried
pub fn horner_loop_1(y: Rc<Array<u64>>, len: u64, x: u64, j: u64, h: u64) -> u64 {
  horner_loop(y, len, x, j, h, ())
}

// Rocq: Plot.plot_implem.horner_loop (local: horner_loop)
// Variant: uncurried, lifted
pub fn horner_loop(y: Rc<Array<u64>>, len: u64, x: u64, j: u64, h: u64, _H: ()) -> u64 {
  let v13 = ltb(j, len);
  match bdec(v13) {
    sumbool::left => {
      let v24 = add(j, 1u64);
      let v31 = mul(h, x);
      let v32 = &y;
      let v35 = rocq_array::get::<u64>(&v32, j);
      horner_loop(y, len, x, v24, add(v31, v35), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      h
    },
  }
}

// Rocq: Plot.plot_implem.eval_loop
// Variant: uncurried
pub fn eval_loop_1(y: Rc<Array<u64>>, len: u64, x: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  eval_loop(y, len, x, d, ())
}

// Rocq: Plot.plot_implem.eval_loop (local: eval_loop)
// Variant: uncurried, lifted
pub fn eval_loop(y: Rc<Array<u64>>, len: u64, x: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(x, len);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(x, 1u64);
      let v31 = Rc::clone(&y);
      let v40 = horner_loop_1(v31, len, x, 0u64, 0u64);
      let v47 = rocq_array::set::<u64>(d, x, v40);
      eval_loop(y, len, v23, v47, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      d
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Plot.plot_implem.diff_inner
// Variant: uncurried
pub fn diff_inner_1(lo: u64, i: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  diff_inner(lo, i, d, ())
}

// Rocq: Plot.plot_implem.diff_inner (local: diff_inner)
// Variant: uncurried, lifted
pub fn diff_inner(lo: u64, i: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(lo, i);
  match bdec(v11) {
    sumbool::left => {
      let v16 = &d;
      let v19 = rocq_array::get::<u64>(&v16, i);
      let v27 = sub(i, 1u64);
      let v28 = &d;
      let v31 = rocq_array::get::<u64>(&v28, v27);
      let v = sub(v19, v31);
      let v44 = sub(i, 1u64);
      let v51 = rocq_array::set::<u64>(d, i, v);
      diff_inner(lo, v44, v51, ())
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Plot.plot_implem.diff_outer
// Variant: uncurried
pub fn diff_outer_1(len: u64, s: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  diff_outer(len, s, d, ())
}

// Rocq: Plot.plot_implem.diff_outer (local: diff_outer)
// Variant: uncurried, lifted
pub fn diff_outer(len: u64, s: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(s, len);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(s, 1u64);
      let v38 = diff_inner_1(s, sub(len, 1u64), d);
      diff_outer(len, v22, v38, ())
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Plot.plot_implem.plot_impl
// Variant: uncurried
pub fn plot_impl(_n: u64, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v2 = &y;
  let len = rocq_array::length::<u64>(&v2);
  let v13 = rocq_array::make::<u64>(len, 0u64);
  let d = eval_loop_1(y, len, 0u64, v13);
  diff_outer_1(len, 0u64, d)
}

// Rocq: Plot.plot_implem.plot_impl
pub fn plot_impl_curried(n: u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v9 = Clone::clone(&n);
      plot_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_281.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_281: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = plot(); }
std::thread_local! { static __rocq_global_284: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = plot_curried(); }