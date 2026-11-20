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

pub type res = ((u64, u64), u64);

// Rocq: Closestpair2.closestpair2_implem.INF
pub fn INF() -> u64 {
  4611686018427387904u64
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.splits
// Variant: uncurried
pub fn splits(lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)))
}

// Rocq: Closestpair2.closestpair2_implem.bdec
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

// Rocq: Closestpair2.closestpair2_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(key: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop(key, src, mid, hi, i, j, k, dst, ())
}

// Rocq: Closestpair2.closestpair2_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(key: Rc<Array<u64>>, src: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, dst: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      if ltb(i, mid) {
        if leb(hi, j) {
          let tmp_1 = add(i, 1u64);
          let tmp_2 = add(k, 1u64);
          let tmp_3 = rocq_array::get::<u64>(&src, i);
          let tmp_4 = rocq_array::set::<u64>(dst, k, tmp_3);
          merge_loop(key, src, mid, hi, tmp_1, j, tmp_2, tmp_4, ())
        } else {
          let tmp_5 = rocq_array::get::<u64>(&src, i);
          let tmp_6 = rocq_array::get::<u64>(&key, tmp_5);
          let tmp_7 = rocq_array::get::<u64>(&src, j);
          let tmp_8 = rocq_array::get::<u64>(&key, tmp_7);
          if lesb(tmp_6, tmp_8) {
            let tmp_9 = add(i, 1u64);
            let tmp_10 = add(k, 1u64);
            let tmp_11 = rocq_array::get::<u64>(&src, i);
            let tmp_12 = rocq_array::set::<u64>(dst, k, tmp_11);
            merge_loop(key, src, mid, hi, tmp_9, j, tmp_10, tmp_12, ())
          } else {
            let tmp_13 = add(j, 1u64);
            let tmp_14 = add(k, 1u64);
            let tmp_15 = rocq_array::get::<u64>(&src, j);
            let tmp_16 = rocq_array::set::<u64>(dst, k, tmp_15);
            merge_loop(key, src, mid, hi, i, tmp_13, tmp_14, tmp_16, ())
          }
        }
      } else {
        let tmp_17 = add(j, 1u64);
        let tmp_18 = add(k, 1u64);
        let tmp_19 = rocq_array::get::<u64>(&src, j);
        let tmp_20 = rocq_array::set::<u64>(dst, k, tmp_19);
        merge_loop(key, src, mid, hi, i, tmp_17, tmp_18, tmp_20, ())
      }
    },
    sumbool::right => {
      std::mem::drop(key);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.merge
// Variant: uncurried
pub fn merge(key: Rc<Array<u64>>, src: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  merge_loop_1(key, src, mid, hi, lo, mid, lo, dst)
}

// Rocq: Closestpair2.closestpair2_implem.msort
// Variant: uncurried
pub fn msort_1(xs: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(xs, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(xs: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = splits(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let xs_clone = Rc::clone(&xs);
      let tmp_1 = msort(xs_clone, lo, mid, oth, tgt, ());
      match &tmp_1 {
        (t1, o1) => {
          let tmp_2 = ();
          let xs_clone_1 = Rc::clone(&xs);
          let t1_clone = Rc::clone(t1);
          let o1_clone = Rc::clone(o1);
          std::mem::drop(tmp_1);
          let tmp_3 = msort(xs_clone_1, mid, hi, t1_clone, o1_clone, tmp_2);
          match tmp_3 {
            (v64, v66) => {
              let t2 = &v64;
              let t2_clone = Rc::clone(t2);
              let tmp_4 = merge(xs, t2_clone, lo, mid, hi, v66);
              (tmp_4, v64)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      let tmp_5 = rocq_array::set::<u64>(tgt, lo, lo);
      (tmp_5, oth)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Closestpair2.closestpair2_implem.bd
pub fn bd(r: ((u64, u64), u64)) -> u64 {
  snd::<(u64, u64), u64>(r)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Closestpair2.closestpair2_implem.near
// Variant: uncurried
pub fn near(xs: Rc<Array<u64>>, xm: u64, b: u64, v: u64) -> bool {
  let tmp = rocq_array::get::<u64>(&xs, v);
  std::mem::drop(xs);
  let dx = sub(tmp, xm);
  ltb(mul(dx, dx), b)
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop
// Variant: uncurried
pub fn strip_loop_1(xs: Rc<Array<u64>>, xm: u64, b: u64, t: Rc<Array<u64>>, hi: u64, k: u64, c: u64, o: Rc<Array<u64>>) -> (Rc<Array<u64>>, u64) {
  strip_loop(xs, xm, b, t, hi, k, c, o, ())
}

// Rocq: Closestpair2.closestpair2_implem.strip_loop (local: strip_loop)
// Variant: uncurried, lifted
pub fn strip_loop(xs: Rc<Array<u64>>, xm: u64, b: u64, t: Rc<Array<u64>>, hi: u64, k: u64, c: u64, o: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&t, k);
      let xs_clone = Rc::clone(&xs);
      if near(xs_clone, xm, b, v) {
        let tmp_1 = add(k, 1u64);
        let tmp_2 = add(c, 1u64);
        let tmp_3 = rocq_array::set::<u64>(o, c, v);
        strip_loop(xs, xm, b, t, hi, tmp_1, tmp_2, tmp_3, ())
      } else {
        strip_loop(xs, xm, b, t, hi, add(k, 1u64), c, o, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(t);
      (o, c)
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.d2
// Variant: uncurried
pub fn d2(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, a: u64, b: u64) -> u64 {
  let tmp = rocq_array::get::<u64>(&xs, a);
  let tmp_1 = rocq_array::get::<u64>(&xs, b);
  std::mem::drop(xs);
  let dx = sub(tmp, tmp_1);
  let tmp_2 = rocq_array::get::<u64>(&ys, a);
  let tmp_3 = rocq_array::get::<u64>(&ys, b);
  std::mem::drop(ys);
  let dy = sub(tmp_2, tmp_3);
  add(mul(dx, dx), mul(dy, dy))
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop
// Variant: uncurried
pub fn inner_loop_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, t: u64, r: ((u64, u64), u64)) -> ((u64, u64), u64) {
  inner_loop(xs, ys, T, e, s, t, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.inner_loop (local: inner_loop)
// Variant: uncurried, lifted
pub fn inner_loop(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, t: u64, r: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let tmp = ltb(t, e);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&T, s);
      let b = rocq_array::get::<u64>(&T, t);
      let tmp_1 = rocq_array::get::<u64>(&ys, b);
      let tmp_2 = rocq_array::get::<u64>(&ys, a);
      let dy = sub(tmp_1, tmp_2);
      let tmp_3 = mul(dy, dy);
      let r_clone = Clone::clone(&r);
      let tmp_4 = bd(r_clone);
      if ltb(tmp_3, tmp_4) {
        let xs_clone = Rc::clone(&xs);
        let ys_clone = Rc::clone(&ys);
        let d = d2(xs_clone, ys_clone, a, b);
        let tmp_5 = add(t, 1u64);
        let r_clone_1 = Clone::clone(&r);
        let tmp_6 = bd(r_clone_1);
        let tmp_7 = if ltb(d, tmp_6) {
          std::mem::drop(r);
          ((a, b), d)
        } else {
          r
        };
        inner_loop(xs, ys, T, e, s, tmp_5, tmp_7, ())
      } else {
        std::mem::drop(xs);
        std::mem::drop(T);
        std::mem::drop(ys);
        r
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop
// Variant: uncurried
pub fn outer_loop_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, r: ((u64, u64), u64)) -> ((u64, u64), u64) {
  outer_loop(xs, ys, T, e, s, r, ())
}

// Rocq: Closestpair2.closestpair2_implem.outer_loop (local: outer_loop)
// Variant: uncurried, lifted
pub fn outer_loop(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, T: Rc<Array<u64>>, e: u64, s: u64, r: ((u64, u64), u64), _H: ()) -> ((u64, u64), u64) {
  let tmp = ltb(s, e);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(s, 1u64);
      let tmp_2 = add(s, 1u64);
      let xs_clone = Rc::clone(&xs);
      let ys_clone = Rc::clone(&ys);
      let T_clone = Rc::clone(&T);
      let tmp_3 = inner_loop_1(xs_clone, ys_clone, T_clone, e, s, tmp_2, r);
      outer_loop(xs, ys, T, e, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      std::mem::drop(T);
      r
    },
  }
}

// Rocq: Closestpair2.closestpair2_implem.solve
// Variant: uncurried
pub fn solve_1(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, P: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>) -> ((Rc<Array<u64>>, Rc<Array<u64>>), ((u64, u64), u64)) {
  solve(xs, ys, P, lo, hi, tgt, oth, ())
}

// Rocq: Closestpair2.closestpair2_implem.solve (local: solve)
// Variant: uncurried, lifted
pub fn solve(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>, P: Rc<Array<u64>>, lo: u64, hi: u64, tgt: Rc<Array<u64>>, oth: Rc<Array<u64>>, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), ((u64, u64), u64)) {
  let tmp = splits(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let xs_clone = Rc::clone(&xs);
      let ys_clone = Rc::clone(&ys);
      let P_clone = Rc::clone(&P);
      let tmp_1 = solve(xs_clone, ys_clone, P_clone, lo, mid, oth, tgt, ());
      match tmp_1 {
        (v49, v51) => {
          let p = &v51;
          match v49 {
            (v55, v57) => {
              let xs_clone_1 = Rc::clone(&xs);
              let ys_clone_1 = Rc::clone(&ys);
              let P_clone_1 = Rc::clone(&P);
              let tmp_2 = solve(xs_clone_1, ys_clone_1, P_clone_1, mid, hi, v55, v57, ());
              match tmp_2 {
                (v83, v85) => {
                  let p_1 = &v85;
                  match v83 {
                    (v89, v91) => {
                      let t2 = &v89;
                      let ys_clone_2 = Rc::clone(&ys);
                      let t2_clone = Rc::clone(t2);
                      let t3 = merge(ys_clone_2, t2_clone, lo, mid, hi, v91);
                      let p_clone = Clone::clone(p_1);
                      let tmp_3 = bd(p_clone);
                      let p_clone_1 = Clone::clone(p);
                      let tmp_4 = bd(p_clone_1);
                      let r0 = if ltb(tmp_3, tmp_4) {
                        std::mem::drop(v51);
                        v85
                      } else {
                        std::mem::drop(v85);
                        v51
                      };
                      let tmp_5 = rocq_array::get::<u64>(&P, mid);
                      std::mem::drop(P);
                      let tmp_6 = rocq_array::get::<u64>(&xs, tmp_5);
                      let r0_clone = Clone::clone(&r0);
                      let tmp_7 = bd(r0_clone);
                      let xs_clone_2 = Rc::clone(&xs);
                      let t3_clone = Rc::clone(&t3);
                      let t2_clone_1 = Rc::clone(t2);
                      std::mem::drop(v89);
                      let tmp_8 = strip_loop_1(xs_clone_2, tmp_6, tmp_7, t3_clone, hi, lo, lo, t2_clone_1);
                      match tmp_8 {
                        (v163, v165) => {
                          let e = &v163;
                          let e_clone = Rc::clone(e);
                          ((t3, e_clone), outer_loop_1(xs, ys, v163, v165, lo, r0))
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
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(ys);
      let tmp_9 = rocq_array::get::<u64>(&P, lo);
      std::mem::drop(P);
      let tmp_10 = rocq_array::set::<u64>(tgt, lo, tmp_9);
      ((tmp_10, oth), ((0u64, 0u64), __rocq_global_643))
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Closestpair2.closestpair2_implem.closestpair_impl
// Variant: uncurried
pub fn closestpair_impl(xs: Rc<Array<u64>>, ys: Rc<Array<u64>>) -> (u64, u64) {
  let n = rocq_array::length::<u64>(&xs);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let xs_clone = Rc::clone(&xs);
  let tmp_2 = msort_1(xs_clone, 0u64, n, tmp, tmp_1);
  match &tmp_2 {
    (A, P) => {
      let tmp_3 = 0u64;
      let tmp_4 = rocq_array::make::<u64>(n, 0u64);
      let A_clone = Rc::clone(A);
      let P_clone = Rc::clone(P);
      std::mem::drop(tmp_2);
      let tmp_5 = solve_1(xs, ys, A_clone, tmp_3, n, P_clone, tmp_4);
      match tmp_5 {
        (v65, v67) => {
          std::mem::drop(v65);
          fst::<(u64, u64), u64>(v67)
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
const __rocq_global_643: u64 = 4611686018427387904u64;