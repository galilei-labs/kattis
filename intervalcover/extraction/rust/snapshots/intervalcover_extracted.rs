#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

pub type uint = Int63;

// Rocq: Intervalcover.intervalcover_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Intervalcover.intervalcover_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Intervalcover.intervalcover_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St, _H: ()) -> St {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let cont_ref: &Rc<dyn Fn(Int63, St) -> bool> = &cont;
      let s_clone = Clone::clone(&s);
      let tmp_1 = cont_ref(i, s_clone);
      if tmp_1 {
        let tmp_2 = i + int63!(1);
        let f_ref: &Rc<dyn Fn(Int63, St) -> St> = &f;
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
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Intervalcover.intervalcover_implem.iota_step
// Variant: uncurried
pub fn iota_step(k: Int63, P: Array<Int63>) -> Array<Int63> {
  P.set(k, k)
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

// Rocq: Intervalcover.intervalcover_implem.guard
// Variant: uncurried
pub fn guard(c: Int63, lo: Int63, hi: Int63) -> bool {
  andb(lo < hi, c < hi - lo)
}

// Rocq: Intervalcover.intervalcover_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(key: &Array<f64>, A: &Array<Int63>, mid: Int63, hi: Int63, k: Int63, st: ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v11, v13) => {
      match v11 {
        (v16, v18) => {
          if v16 < mid_1 {
            if hi_1 <= v18 {
              ((v16 + int63!(1), v18), v13.set(k_1, A.get_cloned(v16)))
            } else {
              let a_1 = A.get_cloned(v16);
              let b_1 = A.get_cloned(v18);
              let tmp = key.get_cloned(a_1);
              let tmp_1 = key.get_cloned(b_1);
              if rocq_float64::leb(tmp, tmp_1) {
                ((v16 + int63!(1), v18), v13.set(k_1, a_1))
              } else {
                ((v16, v18 + int63!(1)), v13.set(k_1, b_1))
              }
            }
          } else {
            ((v16, v18 + int63!(1)), v13.set(k_1, A.get_cloned(v18)))
          }
        },
      }
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.merge
// Variant: uncurried
pub fn merge(key: Array<f64>, lo: Int63, mid: Int63, hi: Int63, A: Array<Int63>, T: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> bool> = Rc::new(move |_v8: Int63, v9: ((Int63, Int63), Array<Int63>)| -> bool {
    std::mem::drop(v9);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>)> = Rc::new({
    let __anf_capture_29 = mid;
    let __anf_capture_31 = hi;
    move |v33: Int63, v34: ((Int63, Int63), Array<Int63>)| -> ((Int63, Int63), Array<Int63>) {
      let key = &key;
      let A = &A;
      let tmp = merge_step(key, A, Clone::clone(&__anf_capture_29), Clone::clone(&__anf_capture_31), v33, v34);
      tmp
    }
  });
  let tmp_1 = (lo, mid);
  let tmp_2 = loop_::<((Int63, Int63), Array<Int63>)>(hi, callback, callback_1, lo, (tmp_1, T));
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
pub fn copy_step(k: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  match st {
    (v3, v5) => {
      let A = &v5;
      let tmp = A.get_cloned(k);
      (v3.set(k, tmp), v5)
    },
  }
}

// Rocq: Intervalcover.intervalcover_implem.merge_copy
// Variant: uncurried
pub fn merge_copy(key: Array<f64>, lo: Int63, mid: Int63, hi: Int63, A: Array<Int63>, T: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let A_clone = Clone::clone(&A);
  let T_1 = merge(key, lo, mid, hi, A_clone, T);
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> bool> = Rc::new(move |_v23: Int63, v24: (Array<Int63>, Array<Int63>)| -> bool {
    std::mem::drop(v24);
    true
  });
  let tmp: fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) = copy_step;
  let tmp_1: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new(tmp);
  loop_::<(Array<Int63>, Array<Int63>)>(hi, callback, tmp_1, lo, (A, T_1))
}

// Rocq: Intervalcover.intervalcover_implem.msort_rec
// Variant: uncurried
pub fn msort_rec_1(key: Array<f64>, lo: Int63, hi: Int63, A: Array<Int63>, T: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  msort_rec(key, lo, hi, A, T, ())
}

// Rocq: Intervalcover.intervalcover_implem.msort_rec (local: msort_rec)
// Variant: uncurried, lifted
pub fn msort_rec(key: Array<f64>, lo: Int63, hi: Int63, A: Array<Int63>, T: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = guard(int63!(1), lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let m = lo + tmp_1 / int63!(2);
      let key_clone = Clone::clone(&key);
      let tmp_2 = msort_rec(key_clone, lo, m, A, T, ());
      match &tmp_2 {
        (T_1, A_1) => {
          let tmp_3 = ();
          let key_clone_1 = Clone::clone(&key);
          let T_clone = Clone::clone(T_1);
          let A_clone = Clone::clone(A_1);
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
pub fn scan_cont(ls: &Array<f64>, P: &Array<Int63>, cur: f64, p: Int63, st: (((Int63, bool), f64), Int63)) -> bool {
  std::mem::drop(st);
  let cur_1 = cur;
  let p_1 = p;
  rocq_float64::leb(ls.get_cloned(P.get_cloned(p_1)), cur_1)
}

// Rocq: Intervalcover.intervalcover_implem.scan_step
// Variant: borrowed, uncurried
pub fn scan_step(rs: &Array<f64>, P: &Array<Int63>, p: Int63, st: (((Int63, bool), f64), Int63)) -> (((Int63, bool), f64), Int63) {
  let p_1 = p;
  let st_1 = st;
  match st_1 {
    (v7, v9) => {
      match v7 {
        (v12, v14) => {
          match v12 {
            (_v17, v19) => {
              let i = P.get_cloned(p_1);
              let r = rs.get_cloned(i);
              if rocq_float64::leb(v14, r) {
                (((p_1 + int63!(1), true), r), i)
              } else {
                (((p_1 + int63!(1), v19), v14), v9)
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

// Rocq: Intervalcover.intervalcover_implem.adv
// Variant: uncurried
pub fn adv(n: Int63, q: Int63, q_: Int63) -> bool {
  andb(q < q_, q_ <= n)
}

// Rocq: Intervalcover.intervalcover_implem.sweep
// Variant: uncurried
pub fn sweep_1(ls: Array<f64>, rs: Array<f64>, b_1: f64, P: Array<Int63>, n: Int63, q: Int63, cnt: Int63, cur: f64, W: Array<Int63>) -> Rc<option<(Array<Int63>, Int63)>> {
  sweep(ls, rs, b_1, P, n, q, cnt, cur, W, ())
}

// Rocq: Intervalcover.intervalcover_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(ls: Array<f64>, rs: Array<f64>, b_1: f64, P: Array<Int63>, n: Int63, q: Int63, cnt: Int63, cur: f64, W: Array<Int63>, _H: ()) -> Rc<option<(Array<Int63>, Int63)>> {
  let ls_clone = Clone::clone(&ls);
  let P_clone = Clone::clone(&P);
  let callback: Rc<dyn Fn(Int63, (((Int63, bool), f64), Int63)) -> bool> = Rc::new({
    let __anf_capture_24 = cur;
    move |v26: Int63, v27: (((Int63, bool), f64), Int63)| -> bool {
      let ls = &ls_clone;
      let P = &P_clone;
      let tmp = Clone::clone(&__anf_capture_24);
      scan_cont(ls, P, tmp, v26, v27)
    }
  });
  let rs_clone = Clone::clone(&rs);
  let P_clone_1 = Clone::clone(&P);
  let callback_1: Rc<dyn Fn(Int63, (((Int63, bool), f64), Int63)) -> (((Int63, bool), f64), Int63)> = Rc::new({
    move |v53: Int63, v54: (((Int63, bool), f64), Int63)| -> (((Int63, bool), f64), Int63) {
      let rs = &rs_clone;
      let P = &P_clone_1;
      let tmp_1 = scan_step(rs, P, v53, v54);
      tmp_1
    }
  });
  let tmp_2 = (q, false);
  let tmp_3 = loop_::<(((Int63, bool), f64), Int63)>(n, callback, callback_1, q, ((tmp_2, cur), int63!(0)));
  match tmp_3 {
    (v101, v103) => {
      match v101 {
        (v106, v108) => {
          match v106 {
            (v111, v113) => {
              let tmp_4 = orb(cnt == int63!(0), rocq_float64::ltb(cur, v108));
              if andb(v113, tmp_4) {
                let W_1 = W.set(cnt, v103);
                if rocq_float64::leb(b_1, v108) {
                  std::mem::drop(ls);
                  std::mem::drop(rs);
                  std::mem::drop(P);
                  Rc::new(option::<(Array<Int63>, Int63)>::Some((W_1, cnt + int63!(1))))
                } else {
                  let tmp_5 = adv(n, q, v111);
                  match bdec(tmp_5) {
                    sumbool::left => {
                      sweep(ls, rs, b_1, P, n, v111, cnt + int63!(1), v108, W_1, ())
                    },
                    sumbool::right => {
                      std::mem::drop(W_1);
                      std::mem::drop(ls);
                      std::mem::drop(rs);
                      std::mem::drop(P);
                      Rc::new(option::<(Array<Int63>, Int63)>::None)
                    },
                  }
                }
              } else {
                std::mem::drop(ls);
                std::mem::drop(rs);
                std::mem::drop(P);
                std::mem::drop(W);
                Rc::new(option::<(Array<Int63>, Int63)>::None)
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
pub fn copy_out(W: Array<Int63>, k: Int63, O: Array<Int63>) -> Array<Int63> {
  let tmp = W.get_cloned(k);
  std::mem::drop(W);
  O.set(k, tmp)
}

// Rocq: Intervalcover.intervalcover_implem.cover
// Variant: uncurried
pub fn cover(x: f64, y: f64, ls: Array<f64>, rs: Array<f64>) -> Rc<option<Array<Int63>>> {
  let n = ls.length();
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v8: Int63, v9: Array<Int63>| -> bool {
    std::mem::drop(v9);
    true
  });
  let tmp: fn(Int63, Array<Int63>) -> Array<Int63> = iota_step;
  let tmp_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new(tmp);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let P = loop_::<Array<Int63>>(n, callback, tmp_1, int63!(0), tmp_2);
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  let ls_clone = Clone::clone(&ls);
  let tmp_4 = msort_rec_1(ls_clone, int63!(0), n, P, tmp_3);
  match tmp_4 {
    (v62, v64) => {
      let tmp_5 = Array::<Int63>::make(n, int63!(0));
      let tmp_6 = sweep_1(ls, rs, y, v62, n, int63!(0), int63!(0), x, tmp_5);
      let (v97, v98) = __rocq_reuse::reset(tmp_6, |__payload| Clone::clone(__payload));
      std::mem::drop(v98);
      match v97 {
        option::Some(v103) => {
          std::mem::drop(v64);
          let p = &v103;
          match p {
            (k, W) => {
              let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v113: Int63, v114: Array<Int63>| -> bool {
                std::mem::drop(v114);
                true
              });
              let k_clone = Clone::clone(k);
              let callback_2: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
                move |v126: Int63, v127: Array<Int63>| -> Array<Int63> {
                  let tmp_7 = Clone::clone(&k_clone);
                  copy_out(tmp_7, v126, v127)
                }
              });
              let tmp_8 = int63!(0);
              let tmp_9 = int63!(0);
              let tmp_10 = Array::<Int63>::make(Clone::clone(W), tmp_9);
              let W_clone = Clone::clone(W);
              std::mem::drop(v103);
              Rc::new(option::<Array<Int63>>::Some(loop_::<Array<Int63>>(W_clone, callback_1, callback_2, tmp_8, tmp_10)))
            },
          }
        },
        option::None => {
          std::mem::drop(v64);
          Rc::new(option::<Array<Int63>>::None)
        },
      }
    },
  }
}
