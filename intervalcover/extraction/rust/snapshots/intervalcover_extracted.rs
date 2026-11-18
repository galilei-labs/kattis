#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

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

// Rocq: Intervalcover.intervalcover_implem.bdec
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

// Rocq: Intervalcover.intervalcover_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Intervalcover.intervalcover_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let cont_ref: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let s_clone = Clone::clone(&s);
      let tmp_1 = cont_ref(i, s_clone);
      if tmp_1 {
        let tmp_2 = add(i, 1u64);
        let f_ref: &Rc<dyn Fn(u64, St) -> St> = &f;
        let tmp_3 = f_ref(i, s);
        wloop::<St>(hi, cont, f, tmp_2, tmp_3, ())
      } else {
        std::mem::drop(f);
        std::mem::drop(cont);
        s
      }
    },
    sumbool::right => {
      std::mem::drop(cont);
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Intervalcover.intervalcover_implem.iota_step
// Variant: uncurried
pub fn iota_step(k: u64, P: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rocq_array::set::<u64>(P, k, k)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Intervalcover.intervalcover_implem.guard
// Variant: uncurried
pub fn guard(c: u64, lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(c, sub(hi, lo)))
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

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: Intervalcover.intervalcover_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(key: &Rc<Array<f64>>, A: &Rc<Array<u64>>, mid: u64, hi: u64, k: u64, st: ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v11, v13) => {
      match v11 {
        (v16, v18) => {
          if ltb(v16, mid_1) {
            if leb(hi_1, v18) {
              let tmp = (add(v16, 1u64), v18);
              let tmp_1 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(A, v16));
              (tmp, tmp_1)
            } else {
              let a = rocq_array::get::<u64>(A, v16);
              let b = rocq_array::get::<u64>(A, v18);
              let tmp_2 = rocq_array::get::<f64>(key, a);
              let tmp_3 = rocq_array::get::<f64>(key, b);
              if leb_1(tmp_2, tmp_3) {
                let tmp_4 = (add(v16, 1u64), v18);
                let tmp_5 = rocq_array::set::<u64>(v13, k_1, a);
                (tmp_4, tmp_5)
              } else {
                let tmp_6 = (v16, add(v18, 1u64));
                let tmp_7 = rocq_array::set::<u64>(v13, k_1, b);
                (tmp_6, tmp_7)
              }
            }
          } else {
            let tmp_8 = (v16, add(v18, 1u64));
            let tmp_9 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(A, v18));
            (tmp_8, tmp_9)
          }
        },
      }
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.merge
// Variant: uncurried
pub fn merge(key: Rc<Array<f64>>, lo: u64, mid: u64, hi: u64, A: Rc<Array<u64>>, T: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = Rc::new(move |_v8: u64, v9: ((u64, u64), Rc<Array<u64>>)| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_29 = mid;
    let __anf_capture_31 = hi;
    move |v33: u64, v34: ((u64, u64), Rc<Array<u64>>)| -> ((u64, u64), Rc<Array<u64>>) {
      let key = &key;
      let A = &A;
      let tmp = merge_step(key, A, Clone::clone(&__anf_capture_29), Clone::clone(&__anf_capture_31), v33, v34);
      tmp
    }
  });
  let tmp_1 = (lo, mid);
  let tmp_2 = loop_::<((u64, u64), Rc<Array<u64>>)>(hi, callback, callback_1, lo, (tmp_1, T));
  match tmp_2 {
    (v75, v77) => {
      match v75 {
        (_v80, _v82) => {
          v77
        },
      }
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.copy_step
// Variant: uncurried
pub fn copy_step(k: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  match st {
    (v3, v5) => {
      let A = &v5;
      let tmp = rocq_array::get::<u64>(A, k);
      let tmp_1 = rocq_array::set::<u64>(v3, k, tmp);
      (tmp_1, v5)
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.merge_copy
// Variant: uncurried
pub fn merge_copy(key: Rc<Array<f64>>, lo: u64, mid: u64, hi: u64, A: Rc<Array<u64>>, T: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let A_clone = Rc::clone(&A);
  let T_1 = merge(key, lo, mid, hi, A_clone, T);
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(move |_v23: u64, v24: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
    std::mem::drop(v24);
    true
  });
  let tmp: fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) = copy_step;
  let tmp_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(tmp);
  loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(hi, callback, tmp_1, lo, (A, T_1))
}

// Rocq: Intervalcover.intervalcover_implem.msort_rec
// Variant: uncurried
pub fn msort_rec_1(key: Rc<Array<f64>>, lo: u64, hi: u64, A: Rc<Array<u64>>, T: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort_rec(key, lo, hi, A, T, ())
}

// Rocq: Intervalcover.intervalcover_implem.msort_rec (local: msort_rec)
// Variant: uncurried, lifted
pub fn msort_rec(key: Rc<Array<f64>>, lo: u64, hi: u64, A: Rc<Array<u64>>, T: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = guard(1u64, lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(hi, lo);
      let m = add(lo, div(tmp_1, 2u64));
      let key_clone = Rc::clone(&key);
      let tmp_2 = msort_rec(key_clone, lo, m, A, T, ());
      match &tmp_2 {
        (T_1, A_1) => {
          let tmp_3 = ();
          let key_clone_1 = Rc::clone(&key);
          let T_clone = Rc::clone(T_1);
          let A_clone = Rc::clone(A_1);
          std::mem::drop(tmp_2);
          let tmp_4 = msort_rec(key_clone_1, m, hi, T_clone, A_clone, tmp_3);
          match tmp_4 {
            (v82, v84) => {
              merge_copy(key, lo, m, hi, v82, v84)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(key);
      (A, T)
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.scan_cont
// Variant: borrowed, uncurried
pub fn scan_cont(ls: &Rc<Array<f64>>, P: &Rc<Array<u64>>, cur: f64, p: u64, st: (((u64, bool), f64), u64)) -> bool {
  std::mem::drop(st);
  let cur_1 = cur;
  let p_1 = p;
  leb_1(rocq_array::get::<f64>(ls, rocq_array::get::<u64>(P, p_1)), cur_1)
}

// Rocq: Intervalcover.intervalcover_implem.scan_step
// Variant: borrowed, uncurried
pub fn scan_step(rs: &Rc<Array<f64>>, P: &Rc<Array<u64>>, p: u64, st: (((u64, bool), f64), u64)) -> (((u64, bool), f64), u64) {
  let p_1 = p;
  let st_1 = st;
  match st_1 {
    (v7, v9) => {
      match v7 {
        (v12, v14) => {
          match v12 {
            (_v17, v19) => {
              let i = rocq_array::get::<u64>(P, p_1);
              let r = rocq_array::get::<f64>(rs, i);
              if leb_1(v14, r) {
                (((add(p_1, 1u64), true), r), i)
              } else {
                (((add(p_1, 1u64), v19), v14), v9)
              }
            },
          }
        },
      }
    },
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

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Intervalcover.intervalcover_implem.adv
// Variant: uncurried
pub fn adv(n: u64, q: u64, q_: u64) -> bool {
  andb(ltb(q, q_), leb(q_, n))
}

// Rocq: Intervalcover.intervalcover_implem.sweep
// Variant: uncurried
pub fn sweep_1(ls: Rc<Array<f64>>, rs: Rc<Array<f64>>, b: f64, P: Rc<Array<u64>>, n: u64, q: u64, cnt: u64, cur: f64, W: Rc<Array<u64>>) -> Rc<option<(Rc<Array<u64>>, u64)>> {
  sweep(ls, rs, b, P, n, q, cnt, cur, W, ())
}

// Rocq: Intervalcover.intervalcover_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(ls: Rc<Array<f64>>, rs: Rc<Array<f64>>, b: f64, P: Rc<Array<u64>>, n: u64, q: u64, cnt: u64, cur: f64, W: Rc<Array<u64>>, _H: ()) -> Rc<option<(Rc<Array<u64>>, u64)>> {
  let ls_clone = Rc::clone(&ls);
  let P_clone = Rc::clone(&P);
  let callback: Rc<dyn Fn(u64, (((u64, bool), f64), u64)) -> bool> = Rc::new({
    let __anf_capture_24 = cur;
    move |v26: u64, v27: (((u64, bool), f64), u64)| -> bool {
      let ls = &ls_clone;
      let P = &P_clone;
      let tmp = Clone::clone(&__anf_capture_24);
      scan_cont(ls, P, tmp, v26, v27)
    }
  });
  let rs_clone = Rc::clone(&rs);
  let P_clone_1 = Rc::clone(&P);
  let callback_1: Rc<dyn Fn(u64, (((u64, bool), f64), u64)) -> (((u64, bool), f64), u64)> = Rc::new({
    move |v53: u64, v54: (((u64, bool), f64), u64)| -> (((u64, bool), f64), u64) {
      let rs = &rs_clone;
      let P = &P_clone_1;
      let tmp_1 = scan_step(rs, P, v53, v54);
      tmp_1
    }
  });
  let tmp_2 = (q, false);
  let tmp_3 = loop_::<(((u64, bool), f64), u64)>(n, callback, callback_1, q, ((tmp_2, cur), 0u64));
  match tmp_3 {
    (v101, v103) => {
      match v101 {
        (v106, v108) => {
          match v106 {
            (v111, v113) => {
              let tmp_4 = orb(eqb(cnt, 0u64), ltb_1(cur, v108));
              if andb(v113, tmp_4) {
                let W_1 = rocq_array::set::<u64>(W, cnt, v103);
                if leb_1(b, v108) {
                  std::mem::drop(ls);
                  std::mem::drop(rs);
                  std::mem::drop(P);
                  Rc::new(option::<(Rc<Array<u64>>, u64)>::Some((W_1, add(cnt, 1u64))))
                } else {
                  let tmp_5 = adv(n, q, v111);
                  match bdec(tmp_5) {
                    sumbool::left => {
                      sweep(ls, rs, b, P, n, v111, add(cnt, 1u64), v108, W_1, ())
                    },
                    sumbool::right => {
                      std::mem::drop(W_1);
                      std::mem::drop(ls);
                      std::mem::drop(rs);
                      std::mem::drop(P);
                      Rc::new(option::<(Rc<Array<u64>>, u64)>::None)
                    },
                  }
                }
              } else {
                std::mem::drop(ls);
                std::mem::drop(rs);
                std::mem::drop(P);
                std::mem::drop(W);
                Rc::new(option::<(Rc<Array<u64>>, u64)>::None)
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.copy_out
// Variant: uncurried
pub fn copy_out(W: Rc<Array<u64>>, k: u64, O: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&W, k);
  std::mem::drop(W);
  rocq_array::set::<u64>(O, k, tmp)
}

// Rocq: Intervalcover.intervalcover_implem.cover
// Variant: uncurried
pub fn cover(x: f64, y: f64, ls: Rc<Array<f64>>, rs: Rc<Array<f64>>) -> Rc<option<Rc<Array<u64>>>> {
  let n = rocq_array::length::<f64>(&ls);
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v8: u64, v9: Rc<Array<u64>>| -> bool {
    std::mem::drop(v9);
    true
  });
  let tmp: fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>> = iota_step;
  let tmp_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(tmp);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let P = loop_::<Rc<Array<u64>>>(n, callback, tmp_1, 0u64, tmp_2);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let ls_clone = Rc::clone(&ls);
  let tmp_4 = msort_rec_1(ls_clone, 0u64, n, P, tmp_3);
  match tmp_4 {
    (v62, v64) => {
      let tmp_5 = rocq_array::make::<u64>(n, 0u64);
      let tmp_6 = sweep_1(ls, rs, y, v62, n, 0u64, 0u64, x, tmp_5);
      let (v97, v98) = __rocq_reuse::reset(tmp_6, |__payload| Clone::clone(__payload));
      std::mem::drop(v98);
      match v97 {
        option::Some(v103) => {
          std::mem::drop(v64);
          let p = &v103;
          match p {
            (k, W) => {
              let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v113: u64, v114: Rc<Array<u64>>| -> bool {
                std::mem::drop(v114);
                true
              });
              let k_clone = Rc::clone(k);
              let callback_2: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
                move |v126: u64, v127: Rc<Array<u64>>| -> Rc<Array<u64>> {
                  let tmp_7 = Rc::clone(&k_clone);
                  copy_out(tmp_7, v126, v127)
                }
              });
              let tmp_8 = 0u64;
              let tmp_9 = 0u64;
              let tmp_10 = rocq_array::make::<u64>(Clone::clone(W), tmp_9);
              let W_clone = Clone::clone(W);
              std::mem::drop(v103);
              let tmp_11 = loop_::<Rc<Array<u64>>>(W_clone, callback_1, callback_2, tmp_8, tmp_10);
              Rc::new(option::<Rc<Array<u64>>>::Some(tmp_11))
            },
          }
        },
        option::None => {
          std::mem::drop(v64);
          Rc::new(option::<Rc<Array<u64>>>::None)
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
