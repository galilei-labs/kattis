#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

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

// Rocq: Knigsoftheforest.knigsoftheforest_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
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

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(h: Rc<Array<u64>>, i: u64) -> Rc<Array<u64>> {
  sift_up(h, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(h: Rc<Array<u64>>, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let q = div(sub(i, 1u64), 2u64);
      let vi = rocq_array::get::<u64>(&h, i);
      let vq = rocq_array::get::<u64>(&h, q);
      let tmp_1 = ltb(vq, vi);
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = rocq_array::set::<u64>(h, i, vq);
          let tmp_3 = rocq_array::set::<u64>(tmp_2, q, vi);
          sift_up(tmp_3, q, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.insert
// Variant: uncurried
pub fn insert(h: Rc<Array<u64>>, s: u64, v: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::set::<u64>(h, s, v);
  sift_up_1(tmp, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.step
// Variant: uncurried
pub fn step(st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>), yr: u64, sv: u64) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  match st {
    (v4, v6) => {
      match v4 {
        (v9, v11) => {
          if eqb(yr, 2011u64) {
            let tmp = insert(v9, v11, sv);
            ((tmp, add(v11, 1u64)), v6)
          } else {
            let tmp_1 = (v9, v11);
            let tmp_2 = rocq_array::set::<u64>(v6, sub(yr, 2011u64), sv);
            (tmp_1, tmp_2)
          }
        },
      }
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill
// Variant: uncurried
pub fn fill_1(ys: Rc<Array<u64>>, ps: Rc<Array<u64>>, m: u64, i: u64, st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>)) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  fill(ys, ps, m, i, st, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(ys: Rc<Array<u64>>, ps: Rc<Array<u64>>, m: u64, i: u64, st: ((Rc<Array<u64>>, u64), Rc<Array<u64>>), _H: ()) -> ((Rc<Array<u64>>, u64), Rc<Array<u64>>) {
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&ys, i);
      let tmp_3 = rocq_array::get::<u64>(&ps, i);
      fill(ys, ps, m, tmp_1, step(st, tmp_2, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(ys);
      std::mem::drop(ps);
      st
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.pick
// Variant: uncurried
pub fn pick(h: Rc<Array<u64>>, s: u64, l: u64) -> u64 {
  let tmp = add(l, 1u64);
  if ltb(tmp, s) {
    let tmp_1 = rocq_array::get::<u64>(&h, l);
    let tmp_2 = rocq_array::get::<u64>(&h, add(l, 1u64));
    if ltb(tmp_1, tmp_2) {
      std::mem::drop(h);
      add(l, 1u64)
    } else {
      std::mem::drop(h);
      l
    }
  } else {
    std::mem::drop(h);
    l
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(h: Rc<Array<u64>>, s: u64, i: u64) -> Rc<Array<u64>> {
  sift_down(h, s, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(h: Rc<Array<u64>>, s: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, div(s, 2u64));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(mul(2u64, i), 1u64);
      let h_clone = Rc::clone(&h);
      let c = pick(h_clone, s, tmp_1);
      let vi = rocq_array::get::<u64>(&h, i);
      let vc = rocq_array::get::<u64>(&h, c);
      let tmp_2 = ltb(vi, vc);
      match bdec(tmp_2) {
        sumbool::left => {
          let tmp_3 = rocq_array::set::<u64>(h, i, vc);
          let tmp_4 = rocq_array::set::<u64>(tmp_3, c, vi);
          sift_down(tmp_4, s, c, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.extract
// Variant: uncurried
pub fn extract(h: Rc<Array<u64>>, s: u64) -> Rc<Array<u64>> {
  let s1 = sub(s, 1u64);
  let tmp = rocq_array::get::<u64>(&h, s1);
  let tmp_1 = rocq_array::set::<u64>(h, 0u64, tmp);
  sift_down_1(tmp_1, s1, 0u64)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim
// Variant: uncurried
pub fn sim_1(t: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, p: u64, s: u64, d: u64) -> Rc<option<u64>> {
  sim(t, h, n, p, s, d, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim (local: sim)
// Variant: uncurried, lifted
pub fn sim(t: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, p: u64, s: u64, d: u64, _H: ()) -> Rc<option<u64>> {
  let tmp = ltb(d, n);
  match bdec(tmp) {
    sumbool::left => {
      if eqb(s, 0u64) {
        std::mem::drop(t);
        std::mem::drop(h);
        Rc::new(option::<u64>::None)
      } else {
        let top = rocq_array::get::<u64>(&h, 0u64);
        if eqb(top, p) {
          std::mem::drop(t);
          std::mem::drop(h);
          Rc::new(option::<u64>::Some(add(2011u64, d)))
        } else {
          let tmp_1 = add(d, 1u64);
          if ltb(tmp_1, n) {
            let tmp_2 = extract(h, s);
            let tmp_3 = sub(s, 1u64);
            let tmp_4 = rocq_array::get::<u64>(&t, add(d, 1u64));
            let tmp_5 = insert(tmp_2, tmp_3, tmp_4);
            sim(t, tmp_5, n, p, s, add(d, 1u64), ())
          } else {
            std::mem::drop(t);
            std::mem::drop(h);
            Rc::new(option::<u64>::None)
          }
        }
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(h);
      Rc::new(option::<u64>::None)
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigs_impl
// Variant: uncurried
pub fn knigs_impl(_k: u64, n: u64, y: u64, p: u64, ys: Rc<Array<u64>>, ps: Rc<Array<u64>>) -> Rc<option<u64>> {
  let m = rocq_array::length::<u64>(&ys);
  let tmp = rocq_array::make::<u64>(add(m, 1u64), 0u64);
  let tmp_1 = (tmp, 0u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let st0 = step((tmp_1, tmp_2), y, p);
  let tmp_3 = fill_1(ys, ps, m, 0u64, st0);
  match tmp_3 {
    (v67, v69) => {
      match v67 {
        (v72, v74) => {
          sim_1(v69, v72, n, p, v74, 0u64)
        },
      }
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
