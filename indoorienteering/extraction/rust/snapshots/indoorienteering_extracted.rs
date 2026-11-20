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

// Rocq: Indoorienteering.indoorienteering_implem.hmul
pub fn hmul() -> u64 {
  7046029254386353131u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
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

// Rocq: Indoorienteering.indoorienteering_implem.bdec
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

// Rocq: Indoorienteering.indoorienteering_implem.fill
// Variant: uncurried
pub fn fill_1(x: Rc<Array<Rc<Array<u64>>>>, n: u64, N: u64, i: u64, D: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill(x, n, N, i, D, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(x: Rc<Array<Rc<Array<u64>>>>, n: u64, N: u64, i: u64, D: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, N);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = div(i, n);
      let x_clone = Rc::clone(&x);
      let tmp_3 = rocq_array::get::<Rc<Array<u64>>>(&x_clone, tmp_2);
      std::mem::drop(x_clone);
      let tmp_4 = rocq_array::get::<u64>(&tmp_3, mod_(i, n));
      std::mem::drop(tmp_3);
      let tmp_5 = rocq_array::set::<u64>(D, i, tmp_4);
      fill(x, n, N, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      D
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Indoorienteering.indoorienteering_implem.logcap
pub fn logcap(n: u64) -> u64 {
  if leb(n, 8u64) {
    7u64
  } else {
    if eqb(n, 9u64) {
      9u64
    } else {
      if eqb(n, 10u64) {
        11u64
      } else {
        if eqb(n, 11u64) {
          13u64
        } else {
          if eqb(n, 12u64) {
            15u64
          } else {
            if eqb(n, 13u64) {
              17u64
            } else {
              20u64
            }
          }
        }
      }
    }
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lxor
// Variant: uncurried
pub fn lxor(v0: u64, v1: u64) -> u64 {
  rocq_int63::lxor(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
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

// Rocq: Indoorienteering.indoorienteering_implem.find
// Variant: uncurried
pub fn find_1(t: Rc<Array<u64>>, k: u64, i: u64) -> u64 {
  find(t, k, i, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(t: Rc<Array<u64>>, k: u64, i: u64, _H: ()) -> u64 {
  let tmp = rocq_array::length::<u64>(&t);
  let tmp_1 = ltb(i, tmp);
  match bdec(tmp_1) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&t, i);
      let tmp_2 = eqb(x, 0u64);
      let tmp_3 = eqb(x, k);
      if orb(tmp_2, tmp_3) {
        std::mem::drop(t);
        i
      } else {
        find(t, k, add(i, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      i
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.hidx
// Variant: uncurried
pub fn hidx(sh: u64, k: u64) -> u64 {
  lsr(mul(k, __rocq_global_342), sh)
}

// Rocq: Indoorienteering.indoorienteering_implem.find0
// Variant: uncurried
pub fn find0(sh: u64, t: Rc<Array<u64>>, k: u64) -> u64 {
  let tmp = hidx(sh, k);
  find_1(t, k, tmp)
}

// Rocq: Indoorienteering.indoorienteering_implem.insert
// Variant: uncurried
pub fn insert(sh: u64, t: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, bool) {
  let t_clone = Rc::clone(&t);
  let j = find0(sh, t_clone, k);
  let tmp = rocq_array::length::<u64>(&t);
  if ltb(j, tmp) {
    let tmp_1 = rocq_array::get::<u64>(&t, j);
    if eqb(tmp_1, 0u64) {
      let tmp_2 = rocq_array::set::<u64>(t, j, k);
      (tmp_2, true)
    } else {
      (t, true)
    }
  } else {
    (t, false)
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.lookup
// Variant: uncurried
pub fn lookup(sh: u64, t: Rc<Array<u64>>, k: u64) -> bool {
  let t_clone = Rc::clone(&t);
  let j = find0(sh, t_clone, k);
  let tmp = rocq_array::length::<u64>(&t);
  let tmp_1 = ltb(j, tmp);
  let tmp_2 = rocq_array::get::<u64>(&t, j);
  std::mem::drop(t);
  andb(tmp_1, eqb(tmp_2, k))
}

// Rocq: Indoorienteering.indoorienteering_implem.key
// Variant: uncurried
pub fn key(S: u64, l: u64) -> u64 {
  let tmp = add(lsl(S, 50u64), l);
  add(tmp, 1u64)
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs
// Variant: uncurried
pub fn pdfs_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, base2: u64, sh: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64) -> bool {
  pdfs(n, a, D, L, base2, sh, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.pdfs (local: pdfs)
// Variant: uncurried, lifted
pub fn pdfs(n: u64, a: u64, D: Rc<Array<u64>>, L: u64, base2: u64, sh: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64, _H: ()) -> bool {
  let tmp = eqb(r, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&D, add(mul(c, n), a));
      let l = add(len, tmp_1);
      if leb(l, L) {
        std::mem::drop(D);
        lookup(sh, t, key(lxor(base2, free), sub(L, l)))
      } else {
        std::mem::drop(t);
        std::mem::drop(D);
        false
      }
    },
    sumbool::right => {
      let tmp_2 = ltb(v, n);
      match bdec(tmp_2) {
        sumbool::left => {
          let bv = lsl(1u64, v);
          let tmp_3 = land(free, bv);
          if eqb(tmp_3, 0u64) {
            pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
          } else {
            let tmp_4 = rocq_array::get::<u64>(&D, add(mul(c, n), v));
            let l = add(len, tmp_4);
            if leb(l, L) {
              let tmp_5 = lxor(free, bv);
              let tmp_6 = sub(r, 1u64);
              let D_clone = Rc::clone(&D);
              let t_clone = Rc::clone(&t);
              if pdfs(n, a, D_clone, L, base2, sh, t_clone, v, tmp_5, l, tmp_6, 0u64, ()) {
                std::mem::drop(t);
                std::mem::drop(D);
                true
              } else {
                pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
              }
            } else {
              pdfs(n, a, D, L, base2, sh, t, c, free, len, r, add(v, 1u64), ())
            }
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          std::mem::drop(t);
          false
        },
      }
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Indoorienteering.indoorienteering_implem.leafins
// Variant: uncurried
pub fn leafins(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, m: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, t: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, bool) {
  let tmp = insert(sh, t, k);
  match tmp {
    (v21, v23) => {
      let b = &v21;
      if v23 {
        std::mem::drop(D);
        (v21, false)
      } else {
        let b_clone = Rc::clone(b);
        if pdfs_1(D, n, L, a, base2, sh, b_clone, m, fr2, 0u64, k2, 0u64) {
          (v21, true)
        } else {
          std::mem::drop(v21);
          let tmp_1 = rocq_array::make::<u64>(size, 0u64);
          let tmp_2 = fst::<Rc<Array<u64>>, bool>(insert(sh, tmp_1, k));
          (tmp_2, false)
        }
      }
    },
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

// Rocq: Indoorienteering.indoorienteering_implem.idfs
// Variant: uncurried
pub fn idfs_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, m: u64, fp: u64, need: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64) -> (Rc<Array<u64>>, bool) {
  idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, v, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.idfs (local: idfs)
// Variant: uncurried, lifted
pub fn idfs(n: u64, m: u64, D: Rc<Array<u64>>, L: u64, fp: u64, a: u64, fr2: u64, base2: u64, k2: u64, sh: u64, size: u64, need: u64, t: Rc<Array<u64>>, c: u64, free: u64, len: u64, r: u64, v: u64, _H: ()) -> (Rc<Array<u64>>, bool) {
  let tmp = eqb(r, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&D, add(mul(c, n), m));
      let l = add(len, tmp_1);
      if leb(l, L) {
        leafins(D, n, L, a, m, fr2, base2, k2, sh, size, t, key(lxor(fp, free), l))
      } else {
        std::mem::drop(D);
        (t, false)
      }
    },
    sumbool::right => {
      let tmp_2 = ltb(v, n);
      match bdec(tmp_2) {
        sumbool::left => {
          let bv = lsl(1u64, v);
          let tmp_3 = land(free, bv);
          if eqb(tmp_3, 0u64) {
            idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
          } else {
            let tmp_4 = eqb(r, 1u64);
            let tmp_5 = negb(eqb(land(need, lxor(free, bv)), 0u64));
            if andb(tmp_4, tmp_5) {
              idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
            } else {
              let tmp_6 = rocq_array::get::<u64>(&D, add(mul(c, n), v));
              let l = add(len, tmp_6);
              if leb(l, L) {
                let tmp_7 = lxor(free, bv);
                let tmp_8 = sub(r, 1u64);
                let D_clone = Rc::clone(&D);
                let tmp_9 = idfs(n, m, D_clone, L, fp, a, fr2, base2, k2, sh, size, need, t, v, tmp_7, l, tmp_8, 0u64, ());
                match tmp_9 {
                  (v380, v382) => {
                    if v382 {
                      std::mem::drop(D);
                      (v380, true)
                    } else {
                      idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, v380, c, free, len, r, add(v, 1u64), ())
                    }
                  },
                }
              } else {
                idfs(n, m, D, L, fp, a, fr2, base2, k2, sh, size, need, t, c, free, len, r, add(v, 1u64), ())
              }
            }
          }
        },
        sumbool::right => {
          std::mem::drop(D);
          (t, false)
        },
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.search_m
// Variant: uncurried
pub fn search_m(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64) -> bool {
  let fp = lxor(sub(lsl(1u64, a), 1u64), lsl(1u64, m));
  let tmp = eqb(land(n, 1u64), 0u64);
  let tmp_1 = leb(4u64, n);
  let need = if andb(tmp, tmp_1) {
    let tmp_2 = 1u64;
    let tmp_3 = 0u64;
    let tmp_4 = if eqb(m, tmp_3) {
      1u64
    } else {
      0u64
    };
    lsl(tmp_2, tmp_4)
  } else {
    0u64
  };
  let fr2 = lxor(fp, need);
  let tmp_5 = rocq_array::make::<u64>(size, 0u64);
  let D_clone = Rc::clone(&D);
  let tmp_6 = idfs_1(D_clone, n, L, a, m, fp, need, fr2, need, k2, sh, size, tmp_5, a, fp, 0u64, k1, 0u64);
  match tmp_6 {
    (v160, v162) => {
      if v162 {
        std::mem::drop(D);
        std::mem::drop(v160);
        true
      } else {
        pdfs_1(D, n, L, a, need, sh, v160, m, fr2, 0u64, k2, 0u64)
      }
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop
// Variant: uncurried
pub fn mloop_1(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64) -> bool {
  mloop(D, n, L, a, k1, k2, sh, size, m, ())
}

// Rocq: Indoorienteering.indoorienteering_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(D: Rc<Array<u64>>, n: u64, L: u64, a: u64, k1: u64, k2: u64, sh: u64, size: u64, m: u64, _H: ()) -> bool {
  let tmp = ltb(m, a);
  match bdec(tmp) {
    sumbool::left => {
      let D_clone = Rc::clone(&D);
      if search_m(D_clone, n, L, a, k1, k2, sh, size, m) {
        std::mem::drop(D);
        true
      } else {
        mloop(D, n, L, a, k1, k2, sh, size, add(m, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(D);
      false
    },
  }
}

// Rocq: Indoorienteering.indoorienteering_implem.indoor
// Variant: uncurried
pub fn indoor(x: Rc<Array<Rc<Array<u64>>>>, L: u64) -> bool {
  let n = rocq_array::length::<Rc<Array<u64>>>(&x);
  let N = mul(n, n);
  let tmp = rocq_array::make::<u64>(N, 0u64);
  let D = fill_1(x, n, N, 0u64, tmp);
  let a = sub(n, 1u64);
  let k1 = div(sub(n, 2u64), 2u64);
  let tmp_1 = sub(n, 2u64);
  let k2 = sub(tmp_1, k1);
  let b = logcap(n);
  mloop_1(D, n, L, a, k1, k2, sub(63u64, b), add(lsl(1u64, b), 256u64), 0u64)
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
const __rocq_global_342: u64 = 7046029254386353131u64;