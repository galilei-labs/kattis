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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Convexhull.convexhull_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Convexhull.convexhull_implem.min_i
// Variant: uncurried
pub fn min_i(a: u64, b: u64) -> u64 {
  if ltb(a, b) {
    a
  } else {
    b
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Convexhull.convexhull_implem.le_pt
// Variant: uncurried
pub fn le_pt(x: Rc<Array<u64>>, y: Rc<Array<u64>>, a: u64, b: u64) -> bool {
  let xa = rocq_array::get::<u64>(&x, a);
  let xb = rocq_array::get::<u64>(&x, b);
  if ltsb(xa, xb) {
    std::mem::drop(y);
    std::mem::drop(x);
    true
  } else {
    if eqb(xa, xb) {
      std::mem::drop(x);
      let tmp = rocq_array::get::<u64>(&y, a);
      let tmp_1 = rocq_array::get::<u64>(&y, b);
      std::mem::drop(y);
      lesb(tmp, tmp_1)
    } else {
      std::mem::drop(y);
      std::mem::drop(x);
      false
    }
  }
}

// Rocq: Convexhull.convexhull_implem.take_left
// Variant: uncurried
pub fn take_left(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64) -> bool {
  if ltb(i, mid) {
    if ltb(j, hi) {
      let tmp = rocq_array::get::<u64>(&src, i);
      let tmp_1 = rocq_array::get::<u64>(&src, j);
      std::mem::drop(src);
      le_pt(x, y, tmp, tmp_1)
    } else {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      true
    }
  } else {
    std::mem::drop(x);
    std::mem::drop(y);
    std::mem::drop(src);
    false
  }
}

// Rocq: Convexhull.convexhull_implem.merge
// Variant: uncurried
pub fn merge_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge(x, y, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Convexhull.convexhull_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let src_clone = Rc::clone(&src);
      if take_left(x_clone, y_clone, src_clone, mid, hi, i, j) {
        let tmp_1 = add(i, 1u64);
        let tmp_2 = add(k, 1u64);
        let tmp_3 = rocq_array::get::<u64>(&src, i);
        let tmp_4 = rocq_array::set::<u64>(dst, k, tmp_3);
        merge(x, y, src, mid, hi, tmp_1, j, tmp_2, tmp_4, ())
      } else {
        let tmp_5 = add(j, 1u64);
        let tmp_6 = add(k, 1u64);
        let tmp_7 = rocq_array::get::<u64>(&src, j);
        let tmp_8 = rocq_array::set::<u64>(dst, k, tmp_7);
        merge(x, y, src, mid, hi, i, tmp_5, tmp_6, tmp_8, ())
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.pass
// Variant: uncurried
pub fn pass_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, w: u64, n: u64, lo: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  pass(x, y, src, w, n, lo, dst, ())
}

// Rocq: Convexhull.convexhull_implem.pass (local: pass)
// Variant: uncurried, lifted
pub fn pass(x: Rc<Array<u64>>, y: Rc<Array<u64>>, src: Rc<Array<u64>>, w: u64, n: u64, lo: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = add(lo, w);
  let tmp_1 = ltb(lo, min_i(add(tmp, w), n));
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = add(lo, w);
      let tmp_3 = min_i(add(tmp_2, w), n);
      let tmp_4 = min_i(add(lo, w), n);
      let tmp_5 = add(lo, w);
      let tmp_6 = min_i(add(tmp_5, w), n);
      let tmp_7 = min_i(add(lo, w), n);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let src_clone = Rc::clone(&src);
      let tmp_8 = merge_1(x_clone, y_clone, src_clone, tmp_4, tmp_6, lo, tmp_7, lo, dst);
      pass(x, y, src, w, n, tmp_3, tmp_8, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.sortl
// Variant: uncurried
pub fn sortl_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  sortl(x, y, n, w, src, dst, ())
}

// Rocq: Convexhull.convexhull_implem.sortl (local: sortl)
// Variant: uncurried, lifted
pub fn sortl(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(w, n);
  let tmp_1 = add(w, w);
  let tmp_2 = andb(tmp, ltb(w, tmp_1));
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = add(w, w);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let src_clone = Rc::clone(&src);
      let tmp_4 = pass_1(x_clone, y_clone, src_clone, w, n, 0u64, dst);
      sortl(x, y, n, tmp_3, tmp_4, src, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(dst);
      src
    },
  }
}

// Rocq: Convexhull.convexhull_implem.initl
// Variant: uncurried
pub fn initl_1(n: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  initl(n, i, a, ())
}

// Rocq: Convexhull.convexhull_implem.initl (local: initl)
// Variant: uncurried, lifted
pub fn initl(n: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(a, i, i);
      initl(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Convexhull.convexhull_implem.msort
// Variant: uncurried
pub fn msort(x: Rc<Array<u64>>, y: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = initl_1(n, 0u64, tmp);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  sortl_1(x, y, n, 1u64, tmp_1, tmp_2)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Convexhull.convexhull_implem.cross_m
// Variant: uncurried
pub fn cross_m(x: Rc<Array<u64>>, y: Rc<Array<u64>>, a: u64, b: u64, c: u64) -> u64 {
  let xa = rocq_array::get::<u64>(&x, a);
  let ya = rocq_array::get::<u64>(&y, a);
  let tmp = rocq_array::get::<u64>(&x, b);
  let tmp_1 = sub(tmp, xa);
  let tmp_2 = rocq_array::get::<u64>(&y, c);
  let tmp_3 = mul(tmp_1, sub(tmp_2, ya));
  let tmp_4 = rocq_array::get::<u64>(&y, b);
  std::mem::drop(y);
  let tmp_5 = sub(tmp_4, ya);
  let tmp_6 = rocq_array::get::<u64>(&x, c);
  std::mem::drop(x);
  let tmp_7 = sub(tmp_6, xa);
  sub(tmp_3, mul(tmp_5, tmp_7))
}

// Rocq: Convexhull.convexhull_implem.pop
// Variant: uncurried
pub fn pop_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, q: u64) -> u64 {
  pop(x, y, st, lim, k, q, ())
}

// Rocq: Convexhull.convexhull_implem.pop (local: pop)
// Variant: uncurried, lifted
pub fn pop(x: Rc<Array<u64>>, y: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, q: u64, _H: ()) -> u64 {
  let tmp = ltb(lim, k);
  let tmp_1 = rocq_array::get::<u64>(&st, sub(k, 2u64));
  let tmp_2 = rocq_array::get::<u64>(&st, sub(k, 1u64));
  let x_clone = Rc::clone(&x);
  let y_clone = Rc::clone(&y);
  let tmp_3 = andb(tmp, lesb(cross_m(x_clone, y_clone, tmp_1, tmp_2, q), 0u64));
  match bdec(tmp_3) {
    sumbool::left => {
      pop(x, y, st, lim, sub(k, 1u64), q, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(st);
      k
    },
  }
}

// Rocq: Convexhull.convexhull_implem.lower
// Variant: uncurried
pub fn lower_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, n: u64, k: u64, i: u64) -> (Rc<Array<u64>>, u64) {
  lower(x, y, ord, st, n, k, i, ())
}

// Rocq: Convexhull.convexhull_implem.lower (local: lower)
// Variant: uncurried, lifted
pub fn lower(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, n: u64, k: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let q = rocq_array::get::<u64>(&ord, i);
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let st_clone = Rc::clone(&st);
      let k_ = pop_1(x_clone, y_clone, st_clone, 1u64, k, q);
      let tmp_1 = rocq_array::set::<u64>(st, k_, q);
      lower(x, y, ord, tmp_1, n, add(k_, 1u64), add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.upper
// Variant: uncurried
pub fn upper_1(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, j: u64) -> (Rc<Array<u64>>, u64) {
  upper(x, y, ord, st, lim, k, j, ())
}

// Rocq: Convexhull.convexhull_implem.upper (local: upper)
// Variant: uncurried, lifted
pub fn upper(x: Rc<Array<u64>>, y: Rc<Array<u64>>, ord: Rc<Array<u64>>, st: Rc<Array<u64>>, lim: u64, k: u64, j: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(0u64, j);
  match bdec(tmp) {
    sumbool::left => {
      let q = rocq_array::get::<u64>(&ord, sub(j, 1u64));
      let x_clone = Rc::clone(&x);
      let y_clone = Rc::clone(&y);
      let st_clone = Rc::clone(&st);
      let k_ = pop_1(x_clone, y_clone, st_clone, lim, k, q);
      let tmp_1 = rocq_array::set::<u64>(st, k_, q);
      upper(x, y, ord, tmp_1, lim, add(k_, 1u64), sub(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(y);
      std::mem::drop(ord);
      (st, k)
    },
  }
}

// Rocq: Convexhull.convexhull_implem.copyl
// Variant: uncurried
pub fn copyl_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, h: u64, i: u64) -> Rc<Array<u64>> {
  copyl(src, dst, h, i, ())
}

// Rocq: Convexhull.convexhull_implem.copyl (local: copyl)
// Variant: uncurried, lifted
pub fn copyl(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, h: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, h);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&src, i);
      let tmp_2 = rocq_array::set::<u64>(dst, i, tmp_1);
      copyl(src, tmp_2, h, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Convexhull.convexhull_implem.hull
// Variant: uncurried
pub fn hull(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let n = rocq_array::length::<u64>(&x);
  let x_clone = Rc::clone(&x);
  let y_clone = Rc::clone(&y);
  let ord = msort(x_clone, y_clone, n);
  let a = rocq_array::get::<u64>(&ord, 0u64);
  let b = rocq_array::get::<u64>(&ord, sub(n, 1u64));
  let tmp = rocq_array::get::<u64>(&x, a);
  let tmp_1 = rocq_array::get::<u64>(&x, b);
  let tmp_2 = eqb(tmp, tmp_1);
  let tmp_3 = rocq_array::get::<u64>(&y, a);
  let tmp_4 = rocq_array::get::<u64>(&y, b);
  let tmp_5 = eqb(tmp_3, tmp_4);
  if andb(tmp_2, tmp_5) {
    std::mem::drop(y);
    std::mem::drop(x);
    std::mem::drop(ord);
    rocq_array::make::<u64>(1u64, a)
  } else {
    let tmp_6 = rocq_array::make::<u64>(add(n, n), 0u64);
    let tmp_7 = rocq_array::set::<u64>(tmp_6, 0u64, a);
    let x_clone_1 = Rc::clone(&x);
    let y_clone_1 = Rc::clone(&y);
    let ord_clone = Rc::clone(&ord);
    let tmp_8 = lower_1(x_clone_1, y_clone_1, ord_clone, tmp_7, n, 1u64, 1u64);
    match &tmp_8 {
      (l, st1) => {
        let tmp_9 = sub(n, 1u64);
        let l_clone = Rc::clone(l);
        let st1_clone = Clone::clone(st1);
        let st1_clone_1 = Clone::clone(st1);
        std::mem::drop(tmp_8);
        let tmp_10 = upper_1(x, y, ord, l_clone, st1_clone, st1_clone_1, tmp_9);
        match tmp_10 {
          (v152, v154) => {
            let tmp_11 = rocq_array::make::<u64>(sub(v154, 1u64), 0u64);
            copyl_1(v152, tmp_11, sub(v154, 1u64), 0u64)
          },
        }
      },
    }
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
