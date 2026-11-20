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

// Rocq: Magicsequence.magicsequence_implem.mask
pub fn mask() -> u64 {
  65535u64
}

// Rocq: Magicsequence.magicsequence_implem.K
pub fn K() -> u64 {
  65536u64
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

// Rocq: Magicsequence.magicsequence_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Magicsequence.magicsequence_implem.gen_loop
// Variant: uncurried
pub fn gen_loop_1(a: u64, b: u64, c: u64, n: u64, i: u64, t: u64, m: u64, arr: Rc<Array<u64>>, lo: Rc<Array<u64>>, hi: Rc<Array<u64>>) -> (((Rc<Array<u64>>, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  gen_loop(a, b, c, n, i, t, m, arr, lo, hi, ())
}

// Rocq: Magicsequence.magicsequence_implem.gen_loop (local: gen_loop)
// Variant: uncurried, lifted
pub fn gen_loop(a: u64, b: u64, c: u64, n: u64, i: u64, t: u64, m: u64, arr: Rc<Array<u64>>, lo: Rc<Array<u64>>, hi: Rc<Array<u64>>, _H: ()) -> (((Rc<Array<u64>>, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let dl = land(t, __rocq_global_60);
      let dh = land(lsr(t, 16u64), __rocq_global_60);
      let lo_ref = &lo;
      let tmp_1 = dl;
      let kl = Clone::clone(&(lo_ref)[tmp_1]);
      let hi_ref = &hi;
      let tmp_2 = dh;
      let kh = Clone::clone(&(hi_ref)[tmp_2]);
      let tmp_3 = add(i, 1u64);
      let tmp_4 = mod_(add(mul(t, b), a), c);
      let tmp_5 = if ltb(m, t) {
        t
      } else {
        m
      };
      let tmp_6 = rocq_array::set::<u64>(arr, i, t);
      let tmp_7 = rocq_array::set::<u64>(lo, dl, add(kl, 1u64));
      let tmp_8 = rocq_array::set::<u64>(hi, dh, add(kh, 1u64));
      gen_loop(a, b, c, n, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, ())
    },
    sumbool::right => {
      (((arr, m), lo), hi)
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(e: u64, acc: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(e, acc, cnt, ())
}

// Rocq: Magicsequence.magicsequence_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(e: u64, acc: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(e, __rocq_global_223);
  match bdec(tmp) {
    sumbool::left => {
      let cnt_ref = &cnt;
      let tmp_1 = e;
      let k = Clone::clone(&(cnt_ref)[tmp_1]);
      let tmp_2 = add(e, 1u64);
      let tmp_3 = add(acc, k);
      let tmp_4 = rocq_array::set::<u64>(cnt, e, acc);
      prefix_loop(tmp_2, tmp_3, tmp_4, ())
    },
    sumbool::right => {
      cnt
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.place_loop
// Variant: uncurried
pub fn place_loop_1(s: u64, n: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  place_loop(s, n, src, i, cnt, dst, ())
}

// Rocq: Magicsequence.magicsequence_implem.place_loop (local: place_loop)
// Variant: uncurried, lifted
pub fn place_loop(s: u64, n: u64, src: Rc<Array<u64>>, i: u64, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let src_ref = &src;
      let tmp_1 = i;
      let e = Clone::clone(&(src_ref)[tmp_1]);
      let d = land(lsr(e, s), __rocq_global_60);
      let cnt_ref = &cnt;
      let tmp_2 = d;
      let p = Clone::clone(&(cnt_ref)[tmp_2]);
      let tmp_3 = add(i, 1u64);
      let tmp_4 = rocq_array::set::<u64>(cnt, d, add(p, 1u64));
      let tmp_5 = rocq_array::set::<u64>(dst, p, e);
      place_loop(s, n, src, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(src);
      std::mem::drop(cnt);
      dst
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.pass
// Variant: uncurried
pub fn pass(s: u64, n: u64, src: Rc<Array<u64>>, cnt: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let cnt_1 = prefix_loop_1(0u64, 0u64, cnt);
  place_loop_1(s, n, src, 0u64, cnt_1, dst)
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop
// Variant: uncurried
pub fn hash_loop_1(x: u64, y: u64, n: u64, i: u64, v: u64, r: Rc<Array<u64>>) -> u64 {
  hash_loop(x, y, n, i, v, r, ())
}

// Rocq: Magicsequence.magicsequence_implem.hash_loop (local: hash_loop)
// Variant: uncurried, lifted
pub fn hash_loop(x: u64, y: u64, n: u64, i: u64, v: u64, r: Rc<Array<u64>>, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = mul(v, x);
      let r_ref = &r;
      let tmp_3 = i;
      let tmp_4 = Clone::clone(&(r_ref)[tmp_3]);
      let tmp_5 = mod_(add(tmp_2, tmp_4), y);
      hash_loop(x, y, n, tmp_1, tmp_5, r, ())
    },
    sumbool::right => {
      std::mem::drop(r);
      v
    },
  }
}

// Rocq: Magicsequence.magicsequence_implem.magic_impl
// Variant: uncurried
pub fn magic_impl(n: u64, a: u64, b: u64, c: u64, x: u64, y: u64) -> u64 {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(__rocq_global_223, 0u64);
  let tmp_2 = rocq_array::make::<u64>(__rocq_global_223, 0u64);
  let tmp_3 = gen_loop_1(a, b, c, n, 0u64, a, 0u64, tmp, tmp_1, tmp_2);
  match tmp_3 {
    (v56, v58) => {
      match v56 {
        (v61, v63) => {
          match v61 {
            (v66, v68) => {
              let m = &v66;
              let tmp_4 = rocq_array::make::<u64>(n, 0u64);
              let m_clone = Rc::clone(m);
              let r1 = pass(0u64, n, m_clone, v63, tmp_4);
              let tmp_5 = __rocq_global_223;
              let r = if ltb(v68, tmp_5) {
                std::mem::drop(v66);
                std::mem::drop(v58);
                r1
              } else {
                pass(16u64, n, r1, v58, v66)
              };
              hash_loop_1(x, y, n, 0u64, 0u64, r)
            },
          }
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
const __rocq_global_60: u64 = 65535u64;
const __rocq_global_223: u64 = 65536u64;