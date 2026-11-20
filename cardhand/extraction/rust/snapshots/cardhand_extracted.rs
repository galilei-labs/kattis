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

// Rocq: Cardhand.cardhand_implem.bdec
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

// Rocq: Cardhand.cardhand_implem.sidx_m
pub fn sidx_m(c: u64) -> u64 {
  if eqb(c, 115u64) {
    0u64
  } else {
    if eqb(c, 104u64) {
      1u64
    } else {
      if eqb(c, 100u64) {
        2u64
      } else {
        3u64
      }
    }
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
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

// Rocq: Cardhand.cardhand_implem.rank_m
pub fn rank_m(c: u64) -> u64 {
  if leb(c, 57u64) {
    sub(c, 50u64)
  } else {
    if eqb(c, 84u64) {
      8u64
    } else {
      if eqb(c, 74u64) {
        9u64
      } else {
        if eqb(c, 81u64) {
          10u64
        } else {
          if eqb(c, 75u64) {
            11u64
          } else {
            12u64
          }
        }
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.prep
// Variant: uncurried
pub fn prep_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  prep(x, n, i, SU, RK, ())
}

// Rocq: Cardhand.cardhand_implem.prep (local: prep)
// Variant: uncurried, lifted
pub fn prep(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, i: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, i);
      let tmp_1 = add(i, 1u64);
      let w_clone = Rc::clone(&w);
      let tmp_2 = rocq_array::set::<u64>(SU, i, sidx_m(get(w_clone, 1u64)));
      let tmp_3 = rocq_array::set::<u64>(RK, i, rank_m(get(w, 0u64)));
      prep(x, n, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (SU, RK)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Cardhand.cardhand_implem.pw4
pub fn pw4(s: u64) -> u64 {
  if eqb(s, 0u64) {
    1u64
  } else {
    if eqb(s, 1u64) {
      4u64
    } else {
      if eqb(s, 2u64) {
        16u64
      } else {
        64u64
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.sg_m
// Variant: uncurried
pub fn sg_m(t: u64, s: u64) -> u64 {
  mod_(div(t, pw4(s)), 4u64)
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Cardhand.cardhand_implem.inj_m
pub fn inj_m(t: u64) -> bool {
  let a = sg_m(t, 0u64);
  let b = sg_m(t, 1u64);
  let c = sg_m(t, 2u64);
  let d = sg_m(t, 3u64);
  let tmp = andb(negb(eqb(a, b)), negb(eqb(a, c)));
  let tmp_1 = andb(tmp, negb(eqb(a, d)));
  let tmp_2 = andb(tmp_1, negb(eqb(b, c)));
  let tmp_3 = andb(tmp_2, negb(eqb(b, d)));
  andb(tmp_3, negb(eqb(c, d)))
}

// Rocq: Cardhand.cardhand_implem.imax
// Variant: uncurried
pub fn imax(a: u64, b: u64) -> u64 {
  if ltb(a, b) {
    b
  } else {
    a
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Cardhand.cardhand_implem.pw2
pub fn pw2(s: u64) -> u64 {
  if eqb(s, 0u64) {
    256u64
  } else {
    if eqb(s, 1u64) {
      512u64
    } else {
      if eqb(s, 2u64) {
        1024u64
      } else {
        2048u64
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.dr_m
// Variant: uncurried
pub fn dr_m(t: u64, s: u64) -> u64 {
  mod_(div(t, pw2(s)), 2u64)
}

// Rocq: Cardhand.cardhand_implem.key_m
// Variant: uncurried
pub fn key_m(t: u64, s: u64, r: u64) -> u64 {
  let tmp = mul(sg_m(t, s), 13u64);
  let tmp_1 = dr_m(t, s);
  let tmp_2 = 1u64;
  let tmp_3 = if eqb(tmp_1, tmp_2) {
    r
  } else {
    sub(12u64, r)
  };
  add(tmp, tmp_3)
}

// Rocq: Cardhand.cardhand_implem.keys
// Variant: uncurried
pub fn keys_1(t: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, i: u64, K: Rc<Array<u64>>, P: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  keys(t, SU, RK, n, i, K, P, ())
}

// Rocq: Cardhand.cardhand_implem.keys (local: keys)
// Variant: uncurried, lifted
pub fn keys(t: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, i: u64, K: Rc<Array<u64>>, P: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&SU, i);
      let tmp_2 = rocq_array::get::<u64>(&RK, i);
      let k = key_m(t, tmp_1, tmp_2);
      let tmp_3 = add(i, 1u64);
      let tmp_4 = rocq_array::set::<u64>(K, i, k);
      let tmp_5 = rocq_array::set::<u64>(P, k, 1u64);
      keys(t, SU, RK, n, tmp_3, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(SU);
      std::mem::drop(RK);
      (K, P)
    },
  }
}

// Rocq: Cardhand.cardhand_implem.compact
// Variant: uncurried
pub fn compact_1(P: Rc<Array<u64>>, k: u64, B: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  compact(P, k, B, m, ())
}

// Rocq: Cardhand.cardhand_implem.compact (local: compact)
// Variant: uncurried, lifted
pub fn compact(P: Rc<Array<u64>>, k: u64, B: Rc<Array<u64>>, m: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(k, 52u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&P, k);
      if eqb(tmp_1, 1u64) {
        let tmp_2 = add(k, 1u64);
        let tmp_3 = rocq_array::set::<u64>(B, m, k);
        compact(P, tmp_2, tmp_3, add(m, 1u64), ())
      } else {
        compact(P, add(k, 1u64), B, m, ())
      }
    },
    sumbool::right => {
      std::mem::drop(P);
      (B, m)
    },
  }
}

// Rocq: Cardhand.cardhand_implem.dp
// Variant: uncurried
pub fn dp_1(K: Rc<Array<u64>>, B: Rc<Array<u64>>, m: u64, w: u64, q: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  dp(K, B, m, w, q, T, ())
}

// Rocq: Cardhand.cardhand_implem.dp (local: dp)
// Variant: uncurried, lifted
pub fn dp(K: Rc<Array<u64>>, B: Rc<Array<u64>>, m: u64, w: u64, q: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, q);
  match bdec(tmp) {
    sumbool::left => {
      let q_ = sub(q, 1u64);
      let i = div(q_, m);
      let j = mod_(q_, m);
      let tmp_1 = rocq_array::get::<u64>(&K, i);
      let tmp_2 = rocq_array::get::<u64>(&B, j);
      let c = if eqb(tmp_1, tmp_2) {
        let tmp_3 = mul(add(i, 1u64), w);
        let tmp_4 = add(j, 1u64);
        let tmp_5 = rocq_array::get::<u64>(&T, add(tmp_3, tmp_4));
        add(tmp_5, 1u64)
      } else {
        let tmp_6 = add(i, 1u64);
        let tmp_7 = rocq_array::get::<u64>(&T, add(mul(tmp_6, w), j));
        let tmp_8 = mul(i, w);
        let tmp_9 = add(j, 1u64);
        let tmp_10 = rocq_array::get::<u64>(&T, add(tmp_8, tmp_9));
        imax(tmp_7, tmp_10)
      };
      let tmp_11 = rocq_array::set::<u64>(T, add(mul(i, w), j), c);
      dp(K, B, m, w, q_, tmp_11, ())
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(B);
      T
    },
  }
}

// Rocq: Cardhand.cardhand_implem.lcs_for
// Variant: uncurried
pub fn lcs_for(t: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64) -> u64 {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(52u64, 0u64);
  let tmp_2 = keys_1(t, SU, RK, n, 0u64, tmp, tmp_1);
  match tmp_2 {
    (v39, v41) => {
      let tmp_3 = rocq_array::make::<u64>(52u64, 0u64);
      let tmp_4 = compact_1(v41, 0u64, tmp_3, 0u64);
      match tmp_4 {
        (v67, v69) => {
          let w = add(v69, 1u64);
          let tmp_5 = mul(n, v69);
          let tmp_6 = rocq_array::make::<u64>(mul(add(n, 1u64), w), 0u64);
          let T = dp_1(v39, v67, v69, w, tmp_5, tmp_6);
          let tmp_7 = rocq_array::get::<u64>(&T, 0u64);
          std::mem::drop(T);
          tmp_7
        },
      }
    },
  }
}

// Rocq: Cardhand.cardhand_implem.search
// Variant: uncurried
pub fn search_1(SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, t: u64, best: u64) -> u64 {
  search(SU, RK, n, t, best, ())
}

// Rocq: Cardhand.cardhand_implem.search (local: search)
// Variant: uncurried, lifted
pub fn search(SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, t: u64, best: u64, _H: ()) -> u64 {
  let tmp = ltb(t, 4096u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(t, 1u64);
      let tmp_2 = if inj_m(t) {
        let SU_clone = Rc::clone(&SU);
        let RK_clone = Rc::clone(&RK);
        imax(best, lcs_for(t, SU_clone, RK_clone, n))
      } else {
        best
      };
      search(SU, RK, n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(SU);
      std::mem::drop(RK);
      best
    },
  }
}

// Rocq: Cardhand.cardhand_implem.min_moves_impl
pub fn min_moves_impl(x: Rc<Array<Rc<rocq_string::RocqString>>>) -> u64 {
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&x);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = prep_1(x, n, 0u64, tmp, tmp_1);
  match tmp_2 {
    (v32, v34) => {
      let tmp_3 = search_1(v32, v34, n, 0u64, 0u64);
      sub(n, tmp_3)
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
