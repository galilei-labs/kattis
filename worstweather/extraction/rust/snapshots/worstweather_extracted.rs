// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum answer {
  Ans_true,
  Ans_maybe,
  Ans_false,
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = u64;

pub type uint = u64;

// Rocq: Worstweather.worstweather_implem.worstweather
// Variant: uncurried
pub fn worstweather() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>> = worstweather_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>>> = Rc::new(v0);
  v1
}

// Rocq: Worstweather.worstweather_implem.worstweather
pub fn worstweather_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>> = worstweather_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>>> = Rc::new(v0);
  v1
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

// Rocq: Worstweather.worstweather_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Worstweather.worstweather_implem.lg_loop
// Variant: uncurried
pub fn lg_loop_1(x: u64, k: u64) -> u64 {
  lg_loop(x, k, ())
}

// Rocq: Worstweather.worstweather_implem.lg_loop (local: lg_loop)
// Variant: uncurried, lifted
pub fn lg_loop(x: u64, k: u64, _H: ()) -> u64 {
  let v12 = ltb(1u64, x);
  match bdec(v12) {
    sumbool::left => {
      lg_loop(div(x, 2u64), add(k, 1u64), ())
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Worstweather.worstweather_implem.lg
pub fn lg(x: u64) -> u64 {
  lg_loop_1(x, 0u64)
}

// Rocq: Worstweather.worstweather_implem.imax
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

// Rocq: Worstweather.worstweather_implem.row_loop
// Variant: uncurried
pub fn row_loop_1(base: u64, prev: u64, half: u64, lim: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  row_loop(base, prev, half, lim, i, T, ())
}

// Rocq: Worstweather.worstweather_implem.row_loop (local: row_loop)
// Variant: uncurried, lifted
pub fn row_loop(base: u64, prev: u64, half: u64, lim: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, lim);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(i, 1u64);
      let v31 = add(base, i);
      let v38 = add(prev, i);
      let v39 = &T;
      let v42 = rocq_array::get::<u64>(&v39, v38);
      let v50 = add(prev, i);
      let v54 = add(v50, half);
      let v55 = &T;
      let v58 = rocq_array::get::<u64>(&v55, v54);
      let v70 = rocq_array::set::<u64>(T, v31, imax(v42, v58));
      row_loop(base, prev, half, lim, v25, v70, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Worstweather.worstweather_implem.rows_loop
// Variant: uncurried
pub fn rows_loop_1(n: u64, L: u64, k: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rows_loop(n, L, k, T, ())
}

// Rocq: Worstweather.worstweather_implem.rows_loop (local: rows_loop)
// Variant: uncurried, lifted
pub fn rows_loop(n: u64, L: u64, k: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(k, L);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(k, 1u64);
      let v97 = row_loop_1(mul(k, n), mul(sub(k, 1u64), n), lsl(1u64, sub(k, 1u64)), add(sub(n, lsl(1u64, k)), 1u64), 0u64, T);
      rows_loop(n, L, v23, v97, ())
    },
    sumbool::right => {
      T
    },
  }
}

// Rocq: Worstweather.worstweather_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(rs: Rc<Array<u64>>, n: u64, i: u64, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  copy_loop(rs, n, i, T, ())
}

// Rocq: Worstweather.worstweather_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(rs: Rc<Array<u64>>, n: u64, i: u64, T: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24 = &rs;
      let v27 = rocq_array::get::<u64>(&v24, i);
      let v34 = rocq_array::set::<u64>(T, i, v27);
      copy_loop(rs, n, v23, v34, ())
    },
    sumbool::right => {
      std::mem::drop(rs);
      T
    },
  }
}

// Rocq: Worstweather.worstweather_implem.build
// Variant: uncurried
pub fn build(rs: Rc<Array<u64>>, n: u64, L: u64) -> Rc<Array<u64>> {
  let v21 = rocq_array::make::<u64>(mul(L, n), 0u64);
  let v30 = copy_loop_1(rs, n, 0u64, v21);
  rows_loop_1(n, L, 1u64, v30)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Worstweather.worstweather_implem.lb_loop
// Variant: uncurried
pub fn lb_loop_1(ys: Rc<Array<u64>>, key: u64, lo: u64, hi: u64) -> u64 {
  lb_loop(ys, key, lo, hi, ())
}

// Rocq: Worstweather.worstweather_implem.lb_loop (local: lb_loop)
// Variant: uncurried, lifted
pub fn lb_loop(ys: Rc<Array<u64>>, key: u64, lo: u64, hi: u64, _H: ()) -> u64 {
  let v12 = ltb(lo, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = sub(hi, lo);
      let mid = add(lo, div(v23, 2u64));
      let v37 = &ys;
      let v41 = rocq_array::get::<u64>(&v37, mid);
      match ltsb(v41, key) {
        true => {
          lb_loop(ys, key, add(mid, 1u64), hi, ())
        },
        false => {
          lb_loop(ys, key, lo, mid, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ys);
      lo
    },
  }
}

// Rocq: Worstweather.worstweather_implem.lower_bound
// Variant: uncurried
pub fn lower_bound(ys: Rc<Array<u64>>, n: u64, key: u64) -> u64 {
  lb_loop_1(ys, key, 0u64, n)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Worstweather.worstweather_implem.rmq
// Variant: uncurried
pub fn rmq(T: Rc<Array<u64>>, n: u64, l: u64, r: u64) -> u64 {
  let k = lg(sub(r, l));
  let v26 = add(mul(k, n), l);
  let v27 = &T;
  let v30 = rocq_array::get::<u64>(&v27, v26);
  let v56 = add(mul(k, n), sub(r, lsl(1u64, k)));
  let v57 = &T;
  let v60 = rocq_array::get::<u64>(&v57, v56);
  std::mem::drop(T);
  imax(v30, v60)
}

// Rocq: Worstweather.worstweather_implem.below
// Variant: uncurried
pub fn below(T: Rc<Array<u64>>, n: u64, lo: u64, j: u64, v: u64) -> bool {
  match ltb(lo, j) {
    true => {
      ltb(rmq(T, n, lo, j), v)
    },
    false => {
      std::mem::drop(T);
      true
    },
  }
}

// Rocq: Worstweather.worstweather_implem.answer_query
// Variant: uncurried
pub fn answer_query(ys: Rc<Array<u64>>, rs: Rc<Array<u64>>, T: Rc<Array<u64>>, n: u64, Y: u64, X: u64) -> answer {
  let v9 = Rc::clone(&ys);
  let i = lower_bound(v9, n, Y);
  let v18 = Rc::clone(&ys);
  let j = lower_bound(v18, n, X);
  let yk = match ltb(i, n) {
    true => {
      let v32 = &ys;
      let v36 = rocq_array::get::<u64>(&v32, i);
      eqb(v36, Y)
    },
    false => {
      false
    },
  };
  let xk = match ltb(j, n) {
    true => {
      let v56 = &ys;
      let v60 = rocq_array::get::<u64>(&v56, j);
      eqb(v60, X)
    },
    false => {
      false
    },
  };
  let lo = match &yk {
    true => {
      add(i, 1u64)
    },
    false => {
      i
    },
  };
  match &yk {
    true => {
      match xk {
        true => {
          let v91 = &rs;
          let v94 = rocq_array::get::<u64>(&v91, j);
          let v95 = &rs;
          let v98 = rocq_array::get::<u64>(&v95, i);
          match leb(v94, v98) {
            true => {
              let v106 = &rs;
              let v109 = rocq_array::get::<u64>(&v106, j);
              match below(T, n, lo, j, v109) {
                true => {
                  let v128 = sub(j, i);
                  let v134 = sub(X, Y);
                  match eqb(v128, v134) {
                    true => {
                      std::mem::drop(ys);
                      std::mem::drop(rs);
                      answer::Ans_true
                    },
                    false => {
                      std::mem::drop(ys);
                      std::mem::drop(rs);
                      answer::Ans_maybe
                    },
                  }
                },
                false => {
                  std::mem::drop(ys);
                  std::mem::drop(rs);
                  answer::Ans_false
                },
              }
            },
            false => {
              std::mem::drop(ys);
              std::mem::drop(rs);
              std::mem::drop(T);
              answer::Ans_false
            },
          }
        },
        false => {
          let v167 = &rs;
          let v170 = rocq_array::get::<u64>(&v167, i);
          match below(T, n, lo, j, v170) {
            true => {
              std::mem::drop(ys);
              std::mem::drop(rs);
              answer::Ans_maybe
            },
            false => {
              std::mem::drop(ys);
              std::mem::drop(rs);
              answer::Ans_false
            },
          }
        },
      }
    },
    false => {
      match xk {
        true => {
          let v199 = &rs;
          let v202 = rocq_array::get::<u64>(&v199, j);
          match below(T, n, lo, j, v202) {
            true => {
              std::mem::drop(ys);
              std::mem::drop(rs);
              answer::Ans_maybe
            },
            false => {
              std::mem::drop(ys);
              std::mem::drop(rs);
              answer::Ans_false
            },
          }
        },
        false => {
          std::mem::drop(ys);
          std::mem::drop(rs);
          std::mem::drop(T);
          answer::Ans_maybe
        },
      }
    },
  }
}

// Rocq: Worstweather.worstweather_implem.q_loop
// Variant: uncurried
pub fn q_loop_1(ys: Rc<Array<u64>>, rs: Rc<Array<u64>>, T: Rc<Array<u64>>, qy: Rc<Array<u64>>, qx: Rc<Array<u64>>, n: u64, m: u64, k: u64, out: Rc<Array<answer>>) -> Rc<Array<answer>> {
  q_loop(ys, rs, T, qy, qx, n, m, k, out, ())
}

// Rocq: Worstweather.worstweather_implem.q_loop (local: q_loop)
// Variant: uncurried, lifted
pub fn q_loop(ys: Rc<Array<u64>>, rs: Rc<Array<u64>>, T: Rc<Array<u64>>, qy: Rc<Array<u64>>, qx: Rc<Array<u64>>, n: u64, m: u64, k: u64, out: Rc<Array<answer>>, _H: ()) -> Rc<Array<answer>> {
  let v17 = ltb(k, m);
  match bdec(v17) {
    sumbool::left => {
      let v28 = add(k, 1u64);
      let v30 = &qy;
      let v33 = rocq_array::get::<u64>(&v30, k);
      let v34 = &qx;
      let v37 = rocq_array::get::<u64>(&v34, k);
      let v40 = Rc::clone(&ys);
      let v43 = Rc::clone(&rs);
      let v46 = Rc::clone(&T);
      let v60 = rocq_array::set::<answer>(out, k, answer_query(v40, v43, v46, n, v33, v37));
      q_loop(ys, rs, T, qy, qx, n, m, v28, v60, ())
    },
    sumbool::right => {
      std::mem::drop(ys);
      std::mem::drop(rs);
      std::mem::drop(T);
      std::mem::drop(qy);
      std::mem::drop(qx);
      out
    },
  }
}

// Rocq: Worstweather.worstweather_implem.worstweather_impl
// Variant: uncurried
pub fn worstweather_impl(ys: Rc<Array<u64>>, rs: Rc<Array<u64>>, qy: Rc<Array<u64>>, qx: Rc<Array<u64>>) -> Rc<Array<answer>> {
  let v4 = &ys;
  let n = rocq_array::length::<u64>(&v4);
  let v6 = &qy;
  let m = rocq_array::length::<u64>(&v6);
  let L = add(lg(n), 1u64);
  let v23 = Rc::clone(&rs);
  let T = build(v23, n, L);
  let v38 = rocq_array::make::<answer>(m, answer::Ans_false);
  q_loop_1(ys, rs, T, qy, qx, n, m, 0u64, v38)
}

// Rocq: Worstweather.worstweather_implem.worstweather_impl
pub fn worstweather_impl_curried(ys: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>> {
  let v3 = {
    move |rs: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>> {
      let ys = &ys;
      let v8 = Rc::clone(ys);
      let v11 = {
        move |qy: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>> {
          let ys = &v8;
          let rs = &rs;
          let v18 = Rc::clone(ys);
          let v20 = Rc::clone(rs);
          let v23 = {
            move |qx: Rc<Array<u64>>| -> Rc<Array<answer>> {
              let v33 = Rc::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&qy);
              worstweather_impl(v33, v35, v37, qx)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>>> = __rocq_global_719.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_719: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<answer>>> = worstweather(); }
std::thread_local! { static __rocq_global_722: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<answer>>>>>> = worstweather_curried(); }