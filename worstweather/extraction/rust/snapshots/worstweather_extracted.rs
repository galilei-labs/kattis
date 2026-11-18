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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(1u64, x);
  match bdec(tmp) {
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
  if ltb(a, b) {
    b
  } else {
    a
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
  let tmp = ltb(i, lim);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(base, i);
      let tmp_3 = rocq_array::get::<u64>(&T, add(prev, i));
      let tmp_4 = add(prev, i);
      let tmp_5 = rocq_array::get::<u64>(&T, add(tmp_4, half));
      let tmp_6 = rocq_array::set::<u64>(T, tmp_2, imax(tmp_3, tmp_5));
      row_loop(base, prev, half, lim, tmp_1, tmp_6, ())
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
  let tmp = ltb(k, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = row_loop_1(mul(k, n), mul(sub(k, 1u64), n), lsl(1u64, sub(k, 1u64)), add(sub(n, lsl(1u64, k)), 1u64), 0u64, T);
      rows_loop(n, L, tmp_1, tmp_2, ())
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&rs, i);
      let tmp_3 = rocq_array::set::<u64>(T, i, tmp_2);
      copy_loop(rs, n, tmp_1, tmp_3, ())
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
  let tmp = rocq_array::make::<u64>(mul(L, n), 0u64);
  let tmp_1 = copy_loop_1(rs, n, 0u64, tmp);
  rows_loop_1(n, L, 1u64, tmp_1)
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
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(hi, lo);
      let mid = add(lo, div(tmp_1, 2u64));
      let tmp_2 = rocq_array::get::<u64>(&ys, mid);
      if ltsb(tmp_2, key) {
        lb_loop(ys, key, add(mid, 1u64), hi, ())
      } else {
        lb_loop(ys, key, lo, mid, ())
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
  let tmp = rocq_array::get::<u64>(&T, add(mul(k, n), l));
  let tmp_1 = rocq_array::get::<u64>(&T, add(mul(k, n), sub(r, lsl(1u64, k))));
  std::mem::drop(T);
  imax(tmp, tmp_1)
}

// Rocq: Worstweather.worstweather_implem.below
// Variant: uncurried
pub fn below(T: Rc<Array<u64>>, n: u64, lo: u64, j: u64, v: u64) -> bool {
  if ltb(lo, j) {
    ltb(rmq(T, n, lo, j), v)
  } else {
    std::mem::drop(T);
    true
  }
}

// Rocq: Worstweather.worstweather_implem.answer_query
// Variant: uncurried
pub fn answer_query(ys: Rc<Array<u64>>, rs: Rc<Array<u64>>, T: Rc<Array<u64>>, n: u64, Y: u64, X: u64) -> answer {
  let ys_clone = Rc::clone(&ys);
  let i = lower_bound(ys_clone, n, Y);
  let ys_clone_1 = Rc::clone(&ys);
  let j = lower_bound(ys_clone_1, n, X);
  let yk = if ltb(i, n) {
    let tmp = rocq_array::get::<u64>(&ys, i);
    eqb(tmp, Y)
  } else {
    false
  };
  let xk = if ltb(j, n) {
    let tmp_1 = rocq_array::get::<u64>(&ys, j);
    eqb(tmp_1, X)
  } else {
    false
  };
  let lo = if yk {
    add(i, 1u64)
  } else {
    i
  };
  if yk {
    if xk {
      let tmp_2 = rocq_array::get::<u64>(&rs, j);
      let tmp_3 = rocq_array::get::<u64>(&rs, i);
      if leb(tmp_2, tmp_3) {
        let tmp_4 = rocq_array::get::<u64>(&rs, j);
        if below(T, n, lo, j, tmp_4) {
          let tmp_5 = sub(j, i);
          let tmp_6 = sub(X, Y);
          if eqb(tmp_5, tmp_6) {
            std::mem::drop(ys);
            std::mem::drop(rs);
            answer::Ans_true
          } else {
            std::mem::drop(ys);
            std::mem::drop(rs);
            answer::Ans_maybe
          }
        } else {
          std::mem::drop(ys);
          std::mem::drop(rs);
          answer::Ans_false
        }
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        std::mem::drop(T);
        answer::Ans_false
      }
    } else {
      let tmp_7 = rocq_array::get::<u64>(&rs, i);
      if below(T, n, lo, j, tmp_7) {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_maybe
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_false
      }
    }
  } else {
    if xk {
      let tmp_8 = rocq_array::get::<u64>(&rs, j);
      if below(T, n, lo, j, tmp_8) {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_maybe
      } else {
        std::mem::drop(ys);
        std::mem::drop(rs);
        answer::Ans_false
      }
    } else {
      std::mem::drop(ys);
      std::mem::drop(rs);
      std::mem::drop(T);
      answer::Ans_maybe
    }
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
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&qy, k);
      let tmp_3 = rocq_array::get::<u64>(&qx, k);
      let ys_clone = Rc::clone(&ys);
      let rs_clone = Rc::clone(&rs);
      let T_clone = Rc::clone(&T);
      let tmp_4 = rocq_array::set::<answer>(out, k, answer_query(ys_clone, rs_clone, T_clone, n, tmp_2, tmp_3));
      q_loop(ys, rs, T, qy, qx, n, m, tmp_1, tmp_4, ())
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
  let n = rocq_array::length::<u64>(&ys);
  let m = rocq_array::length::<u64>(&qy);
  let L = add(lg(n), 1u64);
  let rs_clone = Rc::clone(&rs);
  let T = build(rs_clone, n, L);
  let tmp = rocq_array::make::<answer>(m, answer::Ans_false);
  q_loop_1(ys, rs, T, qy, qx, n, m, 0u64, tmp)
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
