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

pub type char63 = u64;

// Rocq: Cardhand.cardhand_implem.min_moves
pub fn min_moves() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64 = min_moves_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64> = Rc::new(v0);
  v1
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

// Rocq: Cardhand.cardhand_implem.bdec
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

// Rocq: Cardhand.cardhand_implem.sidx_m
pub fn sidx_m(c: u64) -> u64 {
  match eqb(c, 115u64) {
    true => {
      0u64
    },
    false => {
      match eqb(c, 104u64) {
        true => {
          1u64
        },
        false => {
          match eqb(c, 100u64) {
            true => {
              2u64
            },
            false => {
              3u64
            },
          }
        },
      }
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
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
  match leb(c, 57u64) {
    true => {
      sub(c, 50u64)
    },
    false => {
      match eqb(c, 84u64) {
        true => {
          8u64
        },
        false => {
          match eqb(c, 74u64) {
            true => {
              9u64
            },
            false => {
              match eqb(c, 81u64) {
                true => {
                  10u64
                },
                false => {
                  match eqb(c, 75u64) {
                    true => {
                      11u64
                    },
                    false => {
                      12u64
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
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
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &x;
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&v17, i);
      let v28 = add(i, 1u64);
      let v35 = Rc::clone(&w);
      let v48 = rocq_array::set::<u64>(SU, i, sidx_m(get(v35, 1u64)));
      let v67 = rocq_array::set::<u64>(RK, i, rank_m(get(w, 0u64)));
      prep(x, n, v28, v48, v67, ())
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
  match eqb(s, 0u64) {
    true => {
      1u64
    },
    false => {
      match eqb(s, 1u64) {
        true => {
          4u64
        },
        false => {
          match eqb(s, 2u64) {
            true => {
              16u64
            },
            false => {
              64u64
            },
          }
        },
      }
    },
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
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Cardhand.cardhand_implem.inj_m
pub fn inj_m(t: u64) -> bool {
  let a = sg_m(t, 0u64);
  let b = sg_m(t, 1u64);
  let c = sg_m(t, 2u64);
  let d = sg_m(t, 3u64);
  let v62 = andb(negb(eqb(a, b)), negb(eqb(a, c)));
  let v77 = andb(v62, negb(eqb(a, d)));
  let v92 = andb(v77, negb(eqb(b, c)));
  let v107 = andb(v92, negb(eqb(b, d)));
  andb(v107, negb(eqb(c, d)))
}

// Rocq: Cardhand.cardhand_implem.imax
// Variant: uncurried
pub fn imax(a: u64, b: u64) -> u64 {
  match ltb(a, b) {
    true => {
      b
    },
    false => {
      a
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Cardhand.cardhand_implem.pw2
pub fn pw2(s: u64) -> u64 {
  match eqb(s, 0u64) {
    true => {
      256u64
    },
    false => {
      match eqb(s, 1u64) {
        true => {
          512u64
        },
        false => {
          match eqb(s, 2u64) {
            true => {
              1024u64
            },
            false => {
              2048u64
            },
          }
        },
      }
    },
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
  let v17 = mul(sg_m(t, s), 13u64);
  let v24 = dr_m(t, s);
  let v26 = 1u64;
  let v32 = match eqb(v24, v26) {
    true => {
      r
    },
    false => {
      sub(12u64, r)
    },
  };
  add(v17, v32)
}

// Rocq: Cardhand.cardhand_implem.keys
// Variant: uncurried
pub fn keys_1(t: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, i: u64, K: Rc<Array<u64>>, P: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  keys(t, SU, RK, n, i, K, P, ())
}

// Rocq: Cardhand.cardhand_implem.keys (local: keys)
// Variant: uncurried, lifted
pub fn keys(t: u64, SU: Rc<Array<u64>>, RK: Rc<Array<u64>>, n: u64, i: u64, K: Rc<Array<u64>>, P: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v15 = ltb(i, n);
  match bdec(v15) {
    sumbool::left => {
      let v20 = &SU;
      let v23 = rocq_array::get::<u64>(&v20, i);
      let v24 = &RK;
      let v27 = rocq_array::get::<u64>(&v24, i);
      let k = key_m(t, v23, v27);
      let v42 = add(i, 1u64);
      let v49 = rocq_array::set::<u64>(K, i, k);
      let v58 = rocq_array::set::<u64>(P, k, 1u64);
      keys(t, SU, RK, n, v42, v49, v58, ())
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
  let v14 = ltb(k, 52u64);
  match bdec(v14) {
    sumbool::left => {
      let v19 = &P;
      let v22 = rocq_array::get::<u64>(&v19, k);
      match eqb(v22, 1u64) {
        true => {
          let v38 = add(k, 1u64);
          let v45 = rocq_array::set::<u64>(B, m, k);
          compact(P, v38, v45, add(m, 1u64), ())
        },
        false => {
          compact(P, add(k, 1u64), B, m, ())
        },
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
  let v16 = ltb(0u64, q);
  match bdec(v16) {
    sumbool::left => {
      let q_ = sub(q, 1u64);
      let i = div(q_, m);
      let j = mod_(q_, m);
      let v41 = &K;
      let v44 = rocq_array::get::<u64>(&v41, i);
      let v45 = &B;
      let v48 = rocq_array::get::<u64>(&v45, j);
      let c = match eqb(v44, v48) {
        true => {
          let v70 = mul(add(i, 1u64), w);
          let v78 = add(j, 1u64);
          let v83 = add(v70, v78);
          let v84 = &T;
          let v87 = rocq_array::get::<u64>(&v84, v83);
          add(v87, 1u64)
        },
        false => {
          let v108 = add(i, 1u64);
          let v117 = add(mul(v108, w), j);
          let v118 = &T;
          let v121 = rocq_array::get::<u64>(&v118, v117);
          let v128 = mul(i, w);
          let v136 = add(j, 1u64);
          let v141 = add(v128, v136);
          let v142 = &T;
          let v145 = rocq_array::get::<u64>(&v142, v141);
          imax(v121, v145)
        },
      };
      let v172 = rocq_array::set::<u64>(T, add(mul(i, w), j), c);
      dp(K, B, m, w, q_, v172, ())
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
  let v13 = rocq_array::make::<u64>(n, 0u64);
  let v22 = rocq_array::make::<u64>(52u64, 0u64);
  let v37 = keys_1(t, SU, RK, n, 0u64, v13, v22);
  match v37 {
    (v39, v41) => {
      let v54 = rocq_array::make::<u64>(52u64, 0u64);
      let v65 = compact_1(v41, 0u64, v54, 0u64);
      match v65 {
        (v67, v69) => {
          let w = add(v69, 1u64);
          let v85 = mul(n, v69);
          let v106 = rocq_array::make::<u64>(mul(add(n, 1u64), w), 0u64);
          let T = dp_1(v39, v67, v69, w, v85, v106);
          let v121 = 0u64;
          let v122 = &T;
          let v125 = rocq_array::get::<u64>(&v122, v121);
          std::mem::drop(T);
          v125
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
  let v15 = ltb(t, 4096u64);
  match bdec(v15) {
    sumbool::left => {
      let v26 = add(t, 1u64);
      let v31 = match inj_m(t) {
        true => {
          let v38 = Rc::clone(&SU);
          let v41 = Rc::clone(&RK);
          imax(best, lcs_for(t, v38, v41, n))
        },
        false => {
          best
        },
      };
      search(SU, RK, n, v26, v31, ())
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
  let v1 = &x;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v1);
  let v12 = rocq_array::make::<u64>(n, 0u64);
  let v19 = rocq_array::make::<u64>(n, 0u64);
  let v30 = prep_1(x, n, 0u64, v12, v19);
  match v30 {
    (v32, v34) => {
      let v52 = search_1(v32, v34, n, 0u64, 0u64);
      sub(n, v52)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64> = __rocq_global_785.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_785: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> u64> = min_moves(); }