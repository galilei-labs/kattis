#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = u64;

pub type uint = u64;

// Rocq: Zapis.zapis_implem.MOD
pub fn MOD() -> u64 {
  100000u64
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Zapis.zapis_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Zapis.zapis_implem.okp
// Variant: uncurried
pub fn okp(a: u64, b: u64, o: u64, c: u64) -> bool {
  andb(orb(eqb(a, o), eqb(a, 63u64)), orb(eqb(b, c), eqb(b, 63u64)))
}

// Rocq: Zapis.zapis_implem.pcode
// Variant: uncurried
pub fn pcode(a: u64, b: u64) -> u64 {
  let tmp = 40u64;
  let tmp_1 = 41u64;
  let tmp_2 = if okp(a, b, tmp, tmp_1) {
    1u64
  } else {
    0u64
  };
  let tmp_3 = 91u64;
  let tmp_4 = 93u64;
  let tmp_5 = if okp(a, b, tmp_3, tmp_4) {
    1u64
  } else {
    0u64
  };
  let tmp_6 = add(tmp_2, tmp_5);
  let tmp_7 = 123u64;
  let tmp_8 = 125u64;
  let tmp_9 = if okp(a, b, tmp_7, tmp_8) {
    1u64
  } else {
    0u64
  };
  add(tmp_6, tmp_9)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Zapis.zapis_implem.ixi
// Variant: uncurried
pub fn ixi(W: u64, a: u64, b: u64) -> u64 {
  let tmp = mul(a, W);
  mul(2u64, add(tmp, b))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Zapis.zapis_implem.capm
pub fn capm(v: u64) -> u64 {
  if ltb(v, __rocq_global_216) {
    v
  } else {
    __rocq_global_216
  }
}

// Rocq: Zapis.zapis_implem.inner
// Variant: uncurried
pub fn inner_1(x: Rc<rocq_string::RocqString>, tb: Rc<Array<u64>>, W: u64, ci: u64, ii: u64, j: u64, kk: u64, t: u64, r: u64, c: u64) -> (u64, u64) {
  inner(x, tb, W, ci, ii, j, kk, t, r, c, ())
}

// Rocq: Zapis.zapis_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(x: Rc<rocq_string::RocqString>, tb: Rc<Array<u64>>, W: u64, ci: u64, ii: u64, j: u64, kk: u64, t: u64, r: u64, c: u64, _H: ()) -> (u64, u64) {
  let tmp = ltb(0u64, t);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let p = pcode(ci, get(x_clone, kk));
      let ia = ixi(W, add(ii, 1u64), kk);
      let ib = ixi(W, add(kk, 1u64), j);
      let ra = rocq_array::get::<u64>(&tb, ia);
      let ca = rocq_array::get::<u64>(&tb, add(ia, 1u64));
      let rb = rocq_array::get::<u64>(&tb, ib);
      let cb = rocq_array::get::<u64>(&tb, add(ib, 1u64));
      let tmp_1 = add(kk, 2u64);
      let tmp_2 = sub(t, 1u64);
      let tmp_3 = mod_(mul(p, ra), __rocq_global_216);
      let tmp_4 = mod_(add(r, mul(tmp_3, rb)), __rocq_global_216);
      let tmp_5 = capm(mul(p, ca));
      let tmp_6 = capm(mul(tmp_5, cb));
      inner(x, tb, W, ci, ii, j, tmp_1, tmp_2, tmp_4, capm(add(c, tmp_6)), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(tb);
      (r, c)
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

// Rocq: Zapis.zapis_implem.middle
// Variant: uncurried
pub fn middle_1(x: Rc<rocq_string::RocqString>, W: u64, h: u64, L: u64, m: u64, ii: u64, tb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  middle(x, W, h, L, m, ii, tb, ())
}

// Rocq: Zapis.zapis_implem.middle (local: middle)
// Variant: uncurried, lifted
pub fn middle(x: Rc<rocq_string::RocqString>, W: u64, h: u64, L: u64, m: u64, ii: u64, tb: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(ii, m);
  match bdec(tmp) {
    sumbool::left => {
      let j = add(ii, L);
      let tmp_1 = 0u64;
      let b0 = if eqb(h, tmp_1) {
        1u64
      } else {
        0u64
      };
      let x_clone = Rc::clone(&x);
      let tmp_2 = get(x_clone, ii);
      let tmp_3 = add(ii, 1u64);
      let x_clone_1 = Rc::clone(&x);
      let tb_clone = Rc::clone(&tb);
      let rc = inner_1(x_clone_1, tb_clone, W, tmp_2, ii, j, tmp_3, h, b0, b0);
      let p = ixi(W, ii, j);
      let tmp_4 = add(ii, 1u64);
      let rc_clone = Clone::clone(&rc);
      let tmp_5 = rocq_array::set::<u64>(tb, p, fst::<u64, u64>(rc_clone));
      let tmp_6 = rocq_array::set::<u64>(tmp_5, add(p, 1u64), snd::<u64, u64>(rc));
      middle(x, W, h, L, m, tmp_4, tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tb
    },
  }
}

// Rocq: Zapis.zapis_implem.outer
// Variant: uncurried
pub fn outer_1(x: Rc<rocq_string::RocqString>, n: u64, W: u64, hm: u64, h: u64, tb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  outer(x, n, W, hm, h, tb, ())
}

// Rocq: Zapis.zapis_implem.outer (local: outer)
// Variant: uncurried, lifted
pub fn outer(x: Rc<rocq_string::RocqString>, n: u64, W: u64, hm: u64, h: u64, tb: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(h, hm);
  match bdec(tmp) {
    sumbool::left => {
      let L = mul(2u64, h);
      let tmp_1 = add(h, 1u64);
      let tmp_2 = add(sub(n, L), 1u64);
      let x_clone = Rc::clone(&x);
      let tmp_3 = middle_1(x_clone, W, h, L, tmp_2, 0u64, tb);
      outer(x, n, W, hm, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tb
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Zapis.zapis_implem.zapis_impl
pub fn zapis_impl(x: Rc<rocq_string::RocqString>) -> (u64, bool) {
  let x_clone = Rc::clone(&x);
  let n = length(x_clone);
  let W = add(n, 1u64);
  let tmp = add(div(n, 2u64), 1u64);
  let tmp_1 = mul(W, W);
  let tmp_2 = rocq_array::make::<u64>(mul(2u64, tmp_1), 0u64);
  let tb = outer_1(x, n, W, tmp, 0u64, tmp_2);
  let p = ixi(W, 0u64, n);
  let tmp_3 = rocq_array::get::<u64>(&tb, p);
  let tmp_4 = __rocq_global_216;
  let tmp_5 = rocq_array::get::<u64>(&tb, add(p, 1u64));
  std::mem::drop(tb);
  (tmp_3, leb(tmp_4, tmp_5))
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
const __rocq_global_216: u64 = 100000u64;