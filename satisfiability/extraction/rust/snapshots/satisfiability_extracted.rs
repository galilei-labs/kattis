#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub enum literal<A: 'static> {
  X(A),
  NotX(A),
}

impl<A: Clone + 'static> Clone for literal<A> {
  fn clone(&self) -> Self {
    match self {
      literal::X(__field0) => literal::X(Clone::clone(__field0)),
      literal::NotX(__field0) => literal::NotX(Clone::clone(__field0)),
    }
  }
}

pub type uint = u64;

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Satisfiability.satisfiability_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Satisfiability.satisfiability_implem.clause_ok
// Variant: uncurried
pub fn clause_ok(t: u64, p: u64, q: u64) -> bool {
  let tmp = land(p, t);
  if eqb(tmp, 0u64) {
    negb(eqb(land(q, t), q))
  } else {
    true
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Satisfiability.satisfiability_implem.check_loop
// Variant: uncurried
pub fn check_loop_1(pos: Rc<Array<u64>>, neg: Rc<Array<u64>>, m: u64, k: u64, t: u64) -> bool {
  check_loop(pos, neg, m, k, t, ())
}

// Rocq: Satisfiability.satisfiability_implem.check_loop (local: check_loop)
// Variant: uncurried, lifted
pub fn check_loop(pos: Rc<Array<u64>>, neg: Rc<Array<u64>>, m: u64, k: u64, t: u64, _H: ()) -> bool {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&pos, k);
      let tmp_2 = rocq_array::get::<u64>(&neg, k);
      if clause_ok(t, tmp_1, tmp_2) {
        check_loop(pos, neg, m, add(k, 1u64), t, ())
      } else {
        std::mem::drop(pos);
        std::mem::drop(neg);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(pos);
      std::mem::drop(neg);
      true
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.check_all
// Variant: uncurried
pub fn check_all(pos: Rc<Array<u64>>, neg: Rc<Array<u64>>, m: u64, t: u64) -> bool {
  check_loop_1(pos, neg, m, 0u64, t)
}

// Rocq: Satisfiability.satisfiability_implem.search_loop
// Variant: uncurried
pub fn search_loop_1(pos: Rc<Array<u64>>, neg: Rc<Array<u64>>, m: u64, lim: u64, t: u64) -> bool {
  search_loop(pos, neg, m, lim, t, ())
}

// Rocq: Satisfiability.satisfiability_implem.search_loop (local: search_loop)
// Variant: uncurried, lifted
pub fn search_loop(pos: Rc<Array<u64>>, neg: Rc<Array<u64>>, m: u64, lim: u64, t: u64, _H: ()) -> bool {
  let tmp = ltb(t, lim);
  match bdec(tmp) {
    sumbool::left => {
      let pos_clone = Rc::clone(&pos);
      let neg_clone = Rc::clone(&neg);
      if check_all(pos_clone, neg_clone, m, t) {
        std::mem::drop(pos);
        std::mem::drop(neg);
        true
      } else {
        search_loop(pos, neg, m, lim, add(t, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(pos);
      std::mem::drop(neg);
      false
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lor
// Variant: uncurried
pub fn lor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lor(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Satisfiability.satisfiability_implem.bitof
pub fn bitof(v: u64) -> u64 {
  lsl(1u64, sub(v, 1u64))
}

// Rocq: Satisfiability.satisfiability_implem.lit_bits
// Variant: uncurried
pub fn lit_bits(s: bool, l: Rc<literal<u64>>) -> u64 {
  let (v2, v3) = __rocq_reuse::reset(l, |__payload| Clone::clone(__payload));
  std::mem::drop(v3);
  match v2 {
    literal::X(v9) => {
      if s {
        bitof(v9)
      } else {
        0u64
      }
    },
    literal::NotX(v25) => {
      if s {
        0u64
      } else {
        bitof(v25)
      }
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.mask_loop
// Variant: uncurried
pub fn mask_loop_1(s: bool, c: Rc<Array<Rc<literal<u64>>>>, len: u64, i: u64, acc: u64) -> u64 {
  mask_loop(s, c, len, i, acc, ())
}

// Rocq: Satisfiability.satisfiability_implem.mask_loop (local: mask_loop)
// Variant: uncurried, lifted
pub fn mask_loop(s: bool, c: Rc<Array<Rc<literal<u64>>>>, len: u64, i: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(i, len);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<Rc<literal<u64>>>(&c, i);
      let tmp_3 = lit_bits(s, tmp_2);
      mask_loop(s, c, len, tmp_1, lor(acc, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(c);
      acc
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.clause_mask
// Variant: uncurried
pub fn clause_mask(s: bool, c: Rc<Array<Rc<literal<u64>>>>) -> u64 {
  let tmp = rocq_array::length::<Rc<literal<u64>>>(&c);
  mask_loop_1(s, c, tmp, 0u64, 0u64)
}

// Rocq: Satisfiability.satisfiability_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(s: bool, y: Rc<Array<Rc<Array<Rc<literal<u64>>>>>>, m: u64, k: u64, r: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(s, y, m, k, r, ())
}

// Rocq: Satisfiability.satisfiability_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(s: bool, y: Rc<Array<Rc<Array<Rc<literal<u64>>>>>>, m: u64, k: u64, r: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let y_clone = Rc::clone(&y);
      let tmp_2 = rocq_array::get::<Rc<Array<Rc<literal<u64>>>>>(&y_clone, k);
      std::mem::drop(y_clone);
      let tmp_3 = rocq_array::set::<u64>(r, k, clause_mask(s, tmp_2));
      fill_loop(s, y, m, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      r
    },
  }
}

// Rocq: Satisfiability.satisfiability_implem.masks
// Variant: uncurried
pub fn masks(s: bool, y: Rc<Array<Rc<Array<Rc<literal<u64>>>>>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::length::<Rc<Array<Rc<literal<u64>>>>>(&y);
  let tmp_1 = rocq_array::length::<Rc<Array<Rc<literal<u64>>>>>(&y);
  let tmp_2 = rocq_array::make::<u64>(tmp_1, 0u64);
  fill_loop_1(s, y, tmp, 0u64, tmp_2)
}

// Rocq: Satisfiability.satisfiability_implem.satisfiable_impl
// Variant: uncurried
pub fn satisfiable_impl(n: u64, y: Rc<Array<Rc<Array<Rc<literal<u64>>>>>>) -> bool {
  let m = rocq_array::length::<Rc<Array<Rc<literal<u64>>>>>(&y);
  let lim = lsl(1u64, n);
  let y_clone = Rc::clone(&y);
  let tmp = masks(true, y_clone);
  let tmp_1 = masks(false, y);
  search_loop_1(tmp, tmp_1, m, lim, 0u64)
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
