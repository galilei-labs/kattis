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

pub type char63 = u64;

pub type uint = u64;

// Rocq: Zapis.zapis_implem.MOD
pub fn MOD() -> u64 {
  100000u64
}

// Rocq: Zapis.zapis_implem.zapis
pub fn zapis() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> (u64, bool)> {
  let v0: fn(Rc<rocq_string::RocqString>) -> (u64, bool) = zapis_impl;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> (u64, bool)> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
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
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
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
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
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
  let v6 = 40u64;
  let v8 = 41u64;
  let v18 = match okp(a, b, v6, v8) {
    true => {
      1u64
    },
    false => {
      0u64
    },
  };
  let v30 = 91u64;
  let v32 = 93u64;
  let v42 = match okp(a, b, v30, v32) {
    true => {
      1u64
    },
    false => {
      0u64
    },
  };
  let v56 = add(v18, v42);
  let v59 = 123u64;
  let v61 = 125u64;
  let v71 = match okp(a, b, v59, v61) {
    true => {
      1u64
    },
    false => {
      0u64
    },
  };
  add(v56, v71)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Zapis.zapis_implem.ixi
// Variant: uncurried
pub fn ixi(W: u64, a: u64, b: u64) -> u64 {
  let v13 = mul(a, W);
  mul(2u64, add(v13, b))
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
  match ltb(v, __rocq_global_216) {
    true => {
      v
    },
    false => {
      __rocq_global_216
    },
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
  let v20 = ltb(0u64, t);
  match bdec(v20) {
    sumbool::left => {
      let v28 = Rc::clone(&x);
      let p = pcode(ci, get(v28, kk));
      let ia = ixi(W, add(ii, 1u64), kk);
      let ib = ixi(W, add(kk, 1u64), j);
      let v69 = &tb;
      let ra = rocq_array::get::<u64>(&v69, ia);
      let v80 = add(ia, 1u64);
      let v81 = &tb;
      let ca = rocq_array::get::<u64>(&v81, v80);
      let v85 = &tb;
      let rb = rocq_array::get::<u64>(&v85, ib);
      let v96 = add(ib, 1u64);
      let v97 = &tb;
      let cb = rocq_array::get::<u64>(&v97, v96);
      let v108 = add(kk, 2u64);
      let v116 = sub(t, 1u64);
      let v133 = mod_(mul(p, ra), __rocq_global_216);
      let v148 = mod_(add(r, mul(v133, rb)), __rocq_global_216);
      let v163 = capm(mul(p, ca));
      let v170 = capm(mul(v163, cb));
      inner(x, tb, W, ci, ii, j, v108, v116, v148, capm(add(c, v170)), ())
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

// Rocq: Zapis.zapis_implem.middle
// Variant: uncurried
pub fn middle_1(x: Rc<rocq_string::RocqString>, W: u64, h: u64, L: u64, m: u64, ii: u64, tb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  middle(x, W, h, L, m, ii, tb, ())
}

// Rocq: Zapis.zapis_implem.middle (local: middle)
// Variant: uncurried, lifted
pub fn middle(x: Rc<rocq_string::RocqString>, W: u64, h: u64, L: u64, m: u64, ii: u64, tb: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(ii, m);
  match bdec(v15) {
    sumbool::left => {
      let j = add(ii, L);
      let v27 = 0u64;
      let b0 = match eqb(h, v27) {
        true => {
          1u64
        },
        false => {
          0u64
        },
      };
      let v47 = Rc::clone(&x);
      let v50 = get(v47, ii);
      let v58 = add(ii, 1u64);
      let v61 = Rc::clone(&x);
      let v64 = Rc::clone(&tb);
      let rc = inner_1(v61, v64, W, v50, ii, j, v58, h, b0, b0);
      let p = ixi(W, ii, j);
      let v97 = add(ii, 1u64);
      let v100 = Clone::clone(&rc);
      let v109 = rocq_array::set::<u64>(tb, p, fst::<u64, u64>(v100));
      let v128 = rocq_array::set::<u64>(v109, add(p, 1u64), snd::<u64, u64>(rc));
      middle(x, W, h, L, m, v97, v128, ())
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
  let v14 = ltb(h, hm);
  match bdec(v14) {
    sumbool::left => {
      let L = mul(2u64, h);
      let v33 = add(h, 1u64);
      let v48 = add(sub(n, L), 1u64);
      let v53 = Rc::clone(&x);
      let v66 = middle_1(v53, W, h, L, v48, 0u64, tb);
      outer(x, n, W, hm, v33, v66, ())
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
  let v4 = Rc::clone(&x);
  let n = length(v4);
  let W = add(n, 1u64);
  let v30 = add(div(n, 2u64), 1u64);
  let v41 = mul(W, W);
  let v53 = rocq_array::make::<u64>(mul(2u64, v41), 0u64);
  let tb = outer_1(x, n, W, v30, 0u64, v53);
  let p = ixi(W, 0u64, n);
  let v77 = &tb;
  let v80 = rocq_array::get::<u64>(&v77, p);
  let v82 = __rocq_global_216;
  let v90 = add(p, 1u64);
  let v91 = &tb;
  let v94 = rocq_array::get::<u64>(&v91, v90);
  std::mem::drop(tb);
  (v80, leb(v82, v94))
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

pub fn run() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> (u64, bool)> {
  let v0: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> (u64, bool)> = __rocq_global_587.with(Clone::clone);
  v0
}
const __rocq_global_216: u64 = 100000u64;
std::thread_local! { static __rocq_global_587: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> (u64, bool)> = zapis(); }