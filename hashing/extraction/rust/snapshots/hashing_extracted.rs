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

pub type char63 = u64;

// Rocq: Hashing.hashing_implem.P61
pub fn P61() -> u64 {
  2305843009213693951u64
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Hashing.hashing_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Hashing.hashing_implem.addmod
// Variant: uncurried
pub fn addmod(a: u64, b: u64) -> u64 {
  let s = add(a, b);
  if leb(__rocq_global_81, s) {
    sub(s, __rocq_global_81)
  } else {
    s
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc$rust_low$uncurry$0
// Variant: uncurried
pub fn mulc_rust_low_uncurry_0(v0: u64, v1: u64) -> u64 {
  rocq_int63::mulc_low(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc$rust_high$uncurry$0
// Variant: uncurried
pub fn mulc_rust_high_uncurry_0(v0: u64, v1: u64) -> u64 {
  rocq_int63::mulc_high(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mulc
// Variant: uncurried
pub fn mulc(x: u64, x_1: u64) -> (u64, u64) {
  (mulc_rust_high_uncurry_0(x, x_1), mulc_rust_low_uncurry_0(x, x_1))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Hashing.hashing_implem.mulmod
// Variant: uncurried
pub fn mulmod(a: u64, b: u64) -> u64 {
  let tmp = mulc(a, b);
  match tmp {
    (v9, v11) => {
      let tmp_1 = add(lsl(v9, 2u64), lsr(v11, 61u64));
      let s = add(tmp_1, land(v11, __rocq_global_81));
      let t = add(lsr(s, 61u64), land(s, __rocq_global_81));
      if leb(__rocq_global_81, t) {
        sub(t, __rocq_global_81)
      } else {
        t
      }
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Hashing.hashing_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(r: u64, s: Rc<rocq_string::RocqString>, n: u64, i: u64, t: Rc<Array<u64>>, acc: u64) -> Rc<Array<u64>> {
  pre_loop(r, s, n, i, t, acc, ())
}

// Rocq: Hashing.hashing_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(r: u64, s: Rc<rocq_string::RocqString>, n: u64, i: u64, t: Rc<Array<u64>>, acc: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = mulmod(acc, r);
      let s_clone = Rc::clone(&s);
      let acc_ = addmod(tmp_1, get(s_clone, i));
      let tmp_2 = add(i, 1u64);
      let tmp_3 = rocq_array::set::<u64>(t, add(i, 1u64), acc_);
      pre_loop(r, s, n, tmp_2, tmp_3, acc_, ())
    },
    sumbool::right => {
      std::mem::drop(s);
      t
    },
  }
}

// Rocq: Hashing.hashing_implem.prefix_hashes
// Variant: uncurried
pub fn prefix_hashes(r: u64, s: Rc<rocq_string::RocqString>, n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  pre_loop_1(r, s, n, 0u64, tmp, 0u64)
}

// Rocq: Hashing.hashing_implem.pow_loop
// Variant: uncurried
pub fn pow_loop_1(r: u64, n: u64, i: u64, t: Rc<Array<u64>>, acc: u64) -> Rc<Array<u64>> {
  pow_loop(r, n, i, t, acc, ())
}

// Rocq: Hashing.hashing_implem.pow_loop (local: pow_loop)
// Variant: uncurried, lifted
pub fn pow_loop(r: u64, n: u64, i: u64, t: Rc<Array<u64>>, acc: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let acc_ = mulmod(acc, r);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(t, add(i, 1u64), acc_);
      pow_loop(r, n, tmp_1, tmp_2, acc_, ())
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Hashing.hashing_implem.powers
// Variant: uncurried
pub fn powers(r: u64, n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 1u64);
  pow_loop_1(r, n, 0u64, tmp, 1u64)
}

// Rocq: Hashing.hashing_implem.submod
// Variant: uncurried
pub fn submod(a: u64, b: u64) -> u64 {
  if leb(b, a) {
    sub(a, b)
  } else {
    sub(add(a, __rocq_global_81), b)
  }
}

// Rocq: Hashing.hashing_implem.hash
// Variant: uncurried
pub fn hash(pre: Rc<Array<u64>>, pw: Rc<Array<u64>>, L: u64, R: u64) -> u64 {
  let k = rocq_array::get::<u64>(&pw, sub(R, L));
  std::mem::drop(pw);
  let tmp = rocq_array::get::<u64>(&pre, R);
  let tmp_1 = rocq_array::get::<u64>(&pre, L);
  std::mem::drop(pre);
  addmod(submod(tmp, mulmod(tmp_1, k)), k)
}

// Rocq: Hashing.hashing_implem.q_loop
// Variant: uncurried
pub fn q_loop_1(pre: Rc<Array<u64>>, pw: Rc<Array<u64>>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>, q: u64, j: u64, out: Rc<Array<u64>>) -> Rc<Array<u64>> {
  q_loop(pre, pw, xl, xr, q, j, out, ())
}

// Rocq: Hashing.hashing_implem.q_loop (local: q_loop)
// Variant: uncurried, lifted
pub fn q_loop(pre: Rc<Array<u64>>, pw: Rc<Array<u64>>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>, q: u64, j: u64, out: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&xl, j);
      let tmp_3 = rocq_array::get::<u64>(&xr, j);
      let pre_clone = Rc::clone(&pre);
      let pw_clone = Rc::clone(&pw);
      let tmp_4 = rocq_array::set::<u64>(out, j, hash(pre_clone, pw_clone, tmp_2, tmp_3));
      q_loop(pre, pw, xl, xr, q, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(pre);
      std::mem::drop(pw);
      std::mem::drop(xl);
      std::mem::drop(xr);
      out
    },
  }
}

// Rocq: Hashing.hashing_implem.hashes_impl
// Variant: uncurried
pub fn hashes_impl(r: u64, s: Rc<rocq_string::RocqString>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let s_clone = Rc::clone(&s);
  let n = length(s_clone);
  let pre = prefix_hashes(r, s, n);
  let pw = powers(r, n);
  let q = rocq_array::length::<u64>(&xl);
  let tmp = rocq_array::make::<u64>(q, 0u64);
  q_loop_1(pre, pw, xl, xr, q, 0u64, tmp)
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
const __rocq_global_81: u64 = 2305843009213693951u64;