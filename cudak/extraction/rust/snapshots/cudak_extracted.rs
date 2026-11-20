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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = andb(ltb(d, 15u64), leb(mul(q, 10u64), b));
  match bdec(tmp) {
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
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Cudak.cudak_implem.vcell
// Variant: uncurried
pub fn vcell(T: Rc<Array<u64>>, base: u64, t: u64, c: u64) -> u64 {
  if leb(c, t) {
    let tmp = rocq_array::get::<u64>(&T, add(base, sub(t, c)));
    std::mem::drop(T);
    tmp
  } else {
    std::mem::drop(T);
    0u64
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
  let tmp = ltb(d, c);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(d, 1u64);
      let T_clone = Rc::clone(&T);
      let tmp_2 = vcell(T_clone, base, t, d);
      rowsum(T, base, t, c, tmp_1, add(acc, tmp_2), ())
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
  let tmp = ltb(idx, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mul(sub(k, 1u64), S1);
      let T_clone = Rc::clone(&T);
      let tmp_2 = rocq_array::set::<u64>(T, idx, rowsum_1(T_clone, tmp_1, u, 10u64, 0u64, 0u64));
      let tmp_3 = add(idx, 1u64);
      let tmp_4 = if eqb(u, s) {
        add(k, 1u64)
      } else {
        k
      };
      let tmp_5 = if eqb(u, s) {
        0u64
      } else {
        add(u, 1u64)
      };
      fill(tmp_2, s, S1, n, tmp_3, tmp_4, tmp_5, ())
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
  let tmp = ltb(0u64, j);
  match bdec(tmp) {
    sumbool::left => {
      let c = div(R, p);
      let tmp_1 = mul(sub(j, 1u64), S1);
      let T_clone = Rc::clone(&T);
      let acc_ = rowsum_1(T_clone, tmp_1, t, c, 0u64, acc);
      if ltb(t, c) {
        std::mem::drop(T);
        acc_
      } else {
        walk(T, S1, sub(j, 1u64), div(p, 10u64), mod_(R, p), sub(t, c), acc_, ())
      }
    },
    sumbool::right => {
      if eqb(t, 0u64) {
        std::mem::drop(T);
        add(acc, 1u64)
      } else {
        std::mem::drop(T);
        acc
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
  let tmp = ltb(c, 9u64);
  let T_clone = Rc::clone(&T);
  let tmp_1 = andb(tmp, ltb(vcell(T_clone, base, t, c), r));
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = add(c, 1u64);
      let T_clone_1 = Rc::clone(&T);
      let tmp_3 = vcell(T_clone_1, base, t, c);
      pick(T, base, t, tmp_2, sub(r, tmp_3), ())
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
  let tmp = ltb(0u64, j);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mul(sub(j, 1u64), S1);
      let T_clone = Rc::clone(&T);
      let cr = pick_1(T_clone, tmp_1, t, 0u64, r);
      let tmp_2 = sub(j, 1u64);
      let cr_clone = Clone::clone(&cr);
      let tmp_3 = sub(t, fst::<u64, u64>(cr_clone));
      let cr_clone_1 = Clone::clone(&cr);
      minwalk(T, S1, tmp_2, tmp_3, snd::<u64, u64>(cr_clone_1), add(mul(x, 10u64), fst::<u64, u64>(cr)), ())
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
  let dq_clone = Clone::clone(&dq);
  let D = fst::<u64, u64>(dq_clone);
  let q = snd::<u64, u64>(dq);
  let n = mul(D, S1);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::set::<u64>(tmp, 0u64, 1u64);
  let T = fill_1(tmp_1, s, S1, n, S1, 1u64, 0u64);
  let T_clone = Rc::clone(&T);
  let cb = walk_1(T_clone, S1, D, q, b, s, 0u64);
  let tmp_2 = sub(a, 1u64);
  let T_clone_1 = Rc::clone(&T);
  let ca = walk_1(T_clone_1, S1, D, q, tmp_2, s, 0u64);
  (sub(cb, ca), minwalk_1(T, S1, D, s, add(ca, 1u64), 0u64))
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
