#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Largesttriangle.largesttriangle_implem.SH
pub fn SH() -> Int63 {
  int63!(67108864)
}

// Rocq: Largesttriangle.largesttriangle_implem.OFF
pub fn OFF() -> Int63 {
  int63!(1152921504606846976)
}

// Rocq: Largesttriangle.largesttriangle_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.wloop (local: wloop)
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

// Rocq: Largesttriangle.largesttriangle_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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

// Rocq: Largesttriangle.largesttriangle_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(A: &Array<Int63>, mid: Int63, hi: Int63, k: Int63, st: ((Array<Int63>, Int63), Int63)) -> ((Array<Int63>, Int63), Int63) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let tmp = v17 < mid_1;
          let tmp_1 = orb(hi_1 <= v12, A.get_cloned(v17) <= A.get_cloned(v12));
          if andb(tmp, tmp_1) {
            ((v15.set(k_1, A.get_cloned(v17)), v17 + int63!(1)), v12)
          } else {
            ((v15.set(k_1, A.get_cloned(v12)), v17), v12 + int63!(1))
          }
        },
      }
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.merge
// Variant: uncurried
pub fn merge(A: Array<Int63>, T: Array<Int63>, lo: Int63, mid: Int63, hi: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, ((Array<Int63>, Int63), Int63)) -> bool> = Rc::new(move |_v7: Int63, v8: ((Array<Int63>, Int63), Int63)| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Array<Int63>, Int63), Int63)) -> ((Array<Int63>, Int63), Int63)> = Rc::new({
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: Int63, v29: ((Array<Int63>, Int63), Int63)| -> ((Array<Int63>, Int63), Int63) {
      let A = &A;
      let tmp = merge_step(A, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      tmp
    }
  });
  let tmp_1 = (T, lo);
  let tmp_2 = loop_::<((Array<Int63>, Int63), Int63)>(hi, callback, callback_1, lo, (tmp_1, mid));
  match tmp_2 {
    (v69, _v71) => {
      let i = &v69;
      let i_0_clone = Clone::clone(&i.0);
      std::mem::drop(v69);
      i_0_clone
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.copy_step
// Variant: uncurried
pub fn copy_step(T: Array<Int63>, k: Int63, A: Array<Int63>) -> Array<Int63> {
  let tmp = T.get_cloned(k);
  std::mem::drop(T);
  A.set(k, tmp)
}

// Rocq: Largesttriangle.largesttriangle_implem.msort
// Variant: uncurried
pub fn msort_1(A: Array<Int63>, T: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(A, T, lo, hi, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(A: Array<Int63>, T: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = andb(lo < hi, int63!(1) < hi - lo);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi - lo;
      let mid = lo + tmp_1 / int63!(2);
      let tmp_2 = msort(A, T, lo, mid, ());
      match &tmp_2 {
        (T1, A1) => {
          let tmp_3 = ();
          let T1_clone = Clone::clone(T1);
          let A1_clone = Clone::clone(A1);
          std::mem::drop(tmp_2);
          let tmp_4 = msort(T1_clone, A1_clone, mid, hi, tmp_3);
          match tmp_4 {
            (v91, v93) => {
              let T2 = &v91;
              let T2_clone = Clone::clone(T2);
              let T3 = merge(T2_clone, v93, lo, mid, hi);
              let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v110: Int63, v111: Array<Int63>| -> bool {
                std::mem::drop(v111);
                true
              });
              let T3_clone = Clone::clone(&T3);
              let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
                move |v124: Int63, v125: Array<Int63>| -> Array<Int63> {
                  let tmp_5 = Clone::clone(&T3_clone);
                  copy_step(tmp_5, v124, v125)
                }
              });
              (loop_::<Array<Int63>>(hi, callback, callback_1, lo, v91), T3)
            },
          }
        },
      }
    },
    sumbool::right => {
      (A, T)
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.sort
// Variant: uncurried
pub fn sort(K: Array<Int63>, n: Int63) -> Array<Int63> {
  fst::<Array<Int63>, Array<Int63>>(msort_1(K, Array::<Int63>::make(n, int63!(0)), int63!(0), n))
}

// Rocq: Largesttriangle.largesttriangle_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(S: &Array<Int63>, t: Int63, st: (Array<Int63>, Int63)) -> (Array<Int63>, Int63) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let tmp = v8 == int63!(0);
      let tmp_1 = m.get_cloned(v8 - int63!(1));
      let tmp_2 = tmp_1 < S.get_cloned(t_1);
      if orb(tmp, tmp_2) {
        (v6.set(v8, S.get_cloned(t_1)), v8 + int63!(1))
      } else {
        (v6, v8)
      }
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.fzero
pub fn fzero(_v0: ()) -> f64 {
  rocq_float64::of_uint63(int63!(0))
}

// Rocq: Largesttriangle.largesttriangle_implem.decode_step
// Variant: borrowed, uncurried
pub fn decode_step(D: &Array<Int63>, u: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let u_1 = u;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let d = D.get_cloned(u_1);
      (v6.set(u_1, d / __rocq_global_274), v8.set(u_1, d % __rocq_global_274))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.crs
// Variant: uncurried
pub fn crs(ax: Int63, ay: Int63, bx: Int63, by_: Int63, cx: Int63, cy: Int63) -> Int63 {
  (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay) + __rocq_global_625
}

// Rocq: Largesttriangle.largesttriangle_implem.popl
// Variant: uncurried
pub fn popl_1(X: Array<Int63>, Y: Array<Int63>, ST: Array<Int63>, s: Int63, r: Int63) -> Int63 {
  popl(X, Y, ST, s, r, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.popl (local: popl)
// Variant: uncurried, lifted
pub fn popl(X: Array<Int63>, Y: Array<Int63>, ST: Array<Int63>, s: Int63, r: Int63, _H: ()) -> Int63 {
  let tmp = int63!(1) < r;
  match bdec(tmp) {
    sumbool::left => {
      let i1 = ST.get_cloned(r - int63!(2));
      let i2 = ST.get_cloned(r - int63!(1));
      let tmp_1 = X.get_cloned(i1);
      let tmp_2 = Y.get_cloned(i1);
      let tmp_3 = X.get_cloned(i2);
      let tmp_4 = Y.get_cloned(i2);
      let tmp_5 = X.get_cloned(s);
      let tmp_6 = Y.get_cloned(s);
      let tmp_7 = crs(tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, tmp_6);
      if tmp_7 <= __rocq_global_625 {
        popl(X, Y, ST, s, r - int63!(1), ())
      } else {
        std::mem::drop(X);
        std::mem::drop(Y);
        std::mem::drop(ST);
        r
      }
    },
    sumbool::right => {
      std::mem::drop(X);
      std::mem::drop(Y);
      std::mem::drop(ST);
      r
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.pass_step
// Variant: borrowed, uncurried
pub fn pass_step(X: &Array<Int63>, Y: &Array<Int63>, s: Int63, st: (Array<Int63>, Int63)) -> (Array<Int63>, Int63) {
  let s_1 = s;
  let st_1 = st;
  match st_1 {
    (v7, v9) => {
      let r = &v7;
      let X_clone = Clone::clone(X);
      let Y_clone = Clone::clone(Y);
      let r_clone = Clone::clone(r);
      let r_ = popl_1(X_clone, Y_clone, r_clone, s_1, v9);
      (v7.set(r_, s_1), r_ + int63!(1))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: uncurried
pub fn pass_owned(X: Array<Int63>, Y: Array<Int63>, m: Int63) -> (Array<Int63>, Int63) {
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v5: Int63, v6: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |v22: Int63, v23: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let X = &X;
      let Y = &Y;
      let tmp = pass_step(X, Y, v22, v23);
      tmp
    }
  });
  let tmp_1 = Array::<Int63>::make(m, int63!(0));
  loop_::<(Array<Int63>, Int63)>(m, callback, callback_1, int63!(1), (tmp_1, int63!(1)))
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: borrowed, uncurried
pub fn pass(X: &Array<Int63>, Y: &Array<Int63>, m: Int63) -> (Array<Int63>, Int63) {
  let m_1 = m;
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v6: Int63, v7: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v7);
    true
  });
  let X_clone = Clone::clone(X);
  let Y_clone = Clone::clone(Y);
  let callback_1: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |v25: Int63, v26: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let X = &X_clone;
      let Y = &Y_clone;
      let tmp = pass_step(X, Y, v25, v26);
      tmp
    }
  });
  let tmp_1 = Array::<Int63>::make(m_1, int63!(0));
  loop_::<(Array<Int63>, Int63)>(m_1, callback, callback_1, int63!(1), (tmp_1, int63!(1)))
}

// Rocq: Largesttriangle.largesttriangle_implem.rev_step
// Variant: uncurried
pub fn rev_step(X: Array<Int63>, m: Int63, s: Int63, R: Array<Int63>) -> Array<Int63> {
  let tmp = X.get_cloned(m - int63!(1) - s);
  std::mem::drop(X);
  R.set(s, tmp)
}

// Rocq: Largesttriangle.largesttriangle_implem.low_step
// Variant: borrowed, uncurried
pub fn low_step(PX: &Array<Int63>, PY: &Array<Int63>, LS: &Array<Int63>, t: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v8, v10) => {
      let v = LS.get_cloned(t_1);
      (v8.set(t_1, PX.get_cloned(v)), v10.set(t_1, PY.get_cloned(v)))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.up_step
// Variant: borrowed, uncurried
pub fn up_step(RX: &Array<Int63>, RY: &Array<Int63>, US: &Array<Int63>, a_1: Int63, t: Int63, st: (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>) {
  let a_2 = a_1;
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      let v = US.get_cloned(t_1 - a_2 + int63!(1));
      (v10.set(t_1, RX.get_cloned(v)), v12.set(t_1, RY.get_cloned(v)))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.climb
// Variant: borrowed, uncurried
pub fn climb_1(HX: &Array<Int63>, HY: &Array<Int63>, hm: Int63, xi: Int63, yi: Int63, xj: Int63, yj: Int63, k: Int63, gk: Int63) -> Int63 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let xj_1 = xj;
  let yj_1 = yj;
  let k_1 = k;
  let gk_1 = gk;
  climb(HX, HY, hm_1, xi_1, yi_1, xj_1, yj_1, k_1, gk_1, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.climb (local: climb)
// Variant: borrowed, uncurried, lifted
pub fn climb(HX: &Array<Int63>, HY: &Array<Int63>, hm: Int63, xi: Int63, yi: Int63, xj: Int63, yj: Int63, k: Int63, gk: Int63, _H: ()) -> Int63 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let xj_1 = xj;
  let yj_1 = yj;
  let k_1 = k;
  let gk_1 = gk;
  let tmp = k_1 < hm_1;
  match bdec(tmp) {
    sumbool::left => {
      let k1 = k_1 + int63!(1);
      let g1 = crs(xi_1, yi_1, xj_1, yj_1, HX.get_cloned(k1), HY.get_cloned(k1));
      if gk_1 <= g1 {
        climb(HX, HY, hm_1, xi_1, yi_1, xj_1, yj_1, k1, g1, ())
      } else {
        k_1
      }
    },
    sumbool::right => {
      k_1
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.jloop
// Variant: borrowed, uncurried
pub fn jloop_1(HX: &Array<Int63>, HY: &Array<Int63>, hm: Int63, xi: Int63, yi: Int63, j: Int63, k: Int63, best: Int63) -> Int63 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let j_1 = j;
  let k_1 = k;
  let best_1 = best;
  jloop(HX, HY, hm_1, xi_1, yi_1, j_1, k_1, best_1, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.jloop (local: jloop)
// Variant: borrowed, uncurried, lifted
pub fn jloop(HX: &Array<Int63>, HY: &Array<Int63>, hm: Int63, xi: Int63, yi: Int63, j: Int63, k: Int63, best: Int63, _H: ()) -> Int63 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let j_1 = j;
  let k_1 = k;
  let best_1 = best;
  let tmp = j_1 < hm_1;
  match bdec(tmp) {
    sumbool::left => {
      let xj = HX.get_cloned(j_1);
      let yj = HY.get_cloned(j_1);
      let k1 = if j_1 < k_1 {
        k_1
      } else {
        j_1 + int63!(1)
      };
      let tmp_1 = crs(xi_1, yi_1, xj, yj, HX.get_cloned(k1), HY.get_cloned(k1));
      let k2 = climb_1(HX, HY, hm_1, xi_1, yi_1, xj, yj, k1, tmp_1);
      let g = crs(xi_1, yi_1, xj, yj, HX.get_cloned(k2), HY.get_cloned(k2));
      let tmp_2 = j_1 + int63!(1);
      let tmp_3 = if best_1 < g {
        g
      } else {
        best_1
      };
      jloop(HX, HY, hm_1, xi_1, yi_1, tmp_2, k2, tmp_3, ())
    },
    sumbool::right => {
      best_1
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.sweep_step
// Variant: borrowed, uncurried
pub fn sweep_step(HX: &Array<Int63>, HY: &Array<Int63>, h: Int63, i: Int63, best: Int63) -> Int63 {
  let h_1 = h;
  let i_1 = i;
  let best_1 = best;
  let tmp = h_1 - int63!(1);
  let tmp_1 = HX.get_cloned(i_1);
  let tmp_2 = HY;
  jloop_1(HX, HY, tmp, tmp_1, tmp_2.get_cloned(i_1), i_1 + int63!(1), i_1 + int63!(2), best_1)
}

// Rocq: Largesttriangle.largesttriangle_implem.sweep
// Variant: uncurried
pub fn sweep(HX: Array<Int63>, HY: Array<Int63>, h: Int63) -> Int63 {
  let tmp = h - int63!(2);
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new(move |_v13: Int63, _v14: Int63| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_32 = h;
    move |v34: Int63, v35: Int63| -> Int63 {
      let HX = &HX;
      let HY = &HY;
      let tmp_1 = Clone::clone(&__anf_capture_32);
      sweep_step(HX, HY, tmp_1, v34, v35)
    }
  });
  loop_::<Int63>(tmp, callback, callback_1, int63!(0), __rocq_global_625)
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle_impl
// Variant: uncurried
pub fn largest_triangle_impl(x: Array<Int63>, y: Array<Int63>) -> f64 {
  let n = x.length();
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<Int63>| -> bool {
    std::mem::drop(v7);
    true
  });
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |i: Int63, K: Array<Int63>| -> Array<Int63> {
      let x = &x_clone;
      let y = &y_clone;
      let tmp = x.get_cloned(i) * __rocq_global_274;
      let tmp_1 = y.get_cloned(i);
      K.set(i, tmp + tmp_1)
    }
  });
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let K = loop_::<Array<Int63>>(n, callback, callback_1, int63!(0), tmp_2);
  let S = sort(K, n);
  let callback_2: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v85: Int63, v86: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v86);
    true
  });
  let S_clone = Clone::clone(&S);
  let callback_3: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |v99: Int63, v100: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let S = &S_clone;
      let tmp_3 = dedup_step(S, v99, v100);
      tmp_3
    }
  });
  let tmp_4 = Array::<Int63>::make(n, int63!(0));
  let tmp_5 = loop_::<(Array<Int63>, Int63)>(n, callback_2, callback_3, int63!(0), (tmp_4, int63!(0)));
  match tmp_5 {
    (v141, v143) => {
      let m = &v141;
      if v143 < int63!(3) {
        std::mem::drop(S);
        std::mem::drop(x);
        std::mem::drop(y);
        std::mem::drop(v141);
        fzero(())
      } else {
        let callback_4: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> bool> = Rc::new(move |_v165: Int63, v166: (Array<Int63>, Array<Int63>)| -> bool {
          std::mem::drop(v166);
          true
        });
        let m_clone = Clone::clone(m);
        let callback_5: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
          move |v178: Int63, v179: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
            let m = &m_clone;
            let tmp_6 = decode_step(m, v178, v179);
            tmp_6
          }
        });
        let tmp_7 = Array::<Int63>::make(v143, int63!(0));
        let tmp_8 = Array::<Int63>::make(v143, int63!(0));
        let tmp_9 = loop_::<(Array<Int63>, Array<Int63>)>(v143, callback_4, callback_5, int63!(0), (tmp_7, tmp_8));
        match tmp_9 {
          (v225, v227) => {
            let PY = &v225;
            let PX = &v227;
            let tmp_10 = pass(PY, PX, v143);
            match tmp_10 {
              (v238, v240) => {
                let a_1 = &v238;
                let callback_6: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v245: Int63, v246: Array<Int63>| -> bool {
                  std::mem::drop(v246);
                  true
                });
                let PY_clone = Clone::clone(PY);
                let callback_7: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
                  let __anf_capture_260 = v143;
                  move |v262: Int63, v263: Array<Int63>| -> Array<Int63> {
                    let tmp_11 = Clone::clone(&PY_clone);
                    let tmp_12 = Clone::clone(&__anf_capture_260);
                    rev_step(tmp_11, tmp_12, v262, v263)
                  }
                });
                let tmp_13 = Array::<Int63>::make(v143, int63!(0));
                let RX = loop_::<Array<Int63>>(v143, callback_6, callback_7, int63!(0), tmp_13);
                let callback_8: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v300: Int63, v301: Array<Int63>| -> bool {
                  std::mem::drop(v301);
                  true
                });
                let PX_clone = Clone::clone(PX);
                let callback_9: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
                  let __anf_capture_315 = v143;
                  move |v317: Int63, v318: Array<Int63>| -> Array<Int63> {
                    let tmp_14 = Clone::clone(&PX_clone);
                    let tmp_15 = Clone::clone(&__anf_capture_315);
                    rev_step(tmp_14, tmp_15, v317, v318)
                  }
                });
                let tmp_16 = Array::<Int63>::make(v143, int63!(0));
                let RY = loop_::<Array<Int63>>(v143, callback_8, callback_9, int63!(0), tmp_16);
                let RX_clone = Clone::clone(&RX);
                let RY_clone = Clone::clone(&RY);
                let tmp_17 = pass_owned(RX_clone, RY_clone, v143);
                match tmp_17 {
                  (v364, v366) => {
                    let h = v240 + v366 - int63!(2);
                    if h < int63!(3) {
                      std::mem::drop(RY);
                      std::mem::drop(RX);
                      std::mem::drop(S);
                      std::mem::drop(x);
                      std::mem::drop(y);
                      std::mem::drop(v141);
                      std::mem::drop(v364);
                      std::mem::drop(v238);
                      std::mem::drop(v227);
                      std::mem::drop(v225);
                      fzero(())
                    } else {
                      std::mem::drop(S);
                      std::mem::drop(x);
                      std::mem::drop(y);
                      let callback_10: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> bool> = Rc::new(move |_v401: Int63, v402: (Array<Int63>, Array<Int63>)| -> bool {
                        std::mem::drop(v402);
                        true
                      });
                      let PY_clone_1 = Clone::clone(PY);
                      let PX_clone_1 = Clone::clone(PX);
                      let a_clone = Clone::clone(a_1);
                      let callback_11: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
                        move |v422: Int63, v423: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
                          let PY = &PY_clone_1;
                          let PX = &PX_clone_1;
                          let a_1 = &a_clone;
                          let tmp_18 = low_step(PY, PX, a_1, v422, v423);
                          tmp_18
                        }
                      });
                      let tmp_19 = loop_::<(Array<Int63>, Array<Int63>)>(v240, callback_10, callback_11, int63!(0), (Array::<Int63>::make(h, int63!(0)), Array::<Int63>::make(h, int63!(0))));
                      match &tmp_19 {
                        (HY1, HX1) => {
                          std::mem::drop(v141);
                          std::mem::drop(v225);
                          std::mem::drop(v227);
                          std::mem::drop(v238);
                          let callback_12: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> bool> = Rc::new(move |_v478: Int63, v479: (Array<Int63>, Array<Int63>)| -> bool {
                            std::mem::drop(v479);
                            true
                          });
                          let callback_13: Rc<dyn Fn(Int63, (Array<Int63>, Array<Int63>)) -> (Array<Int63>, Array<Int63>)> = Rc::new({
                            let __anf_capture_495 = RX;
                            let __anf_capture_497 = RY;
                            let __anf_capture_499 = v364;
                            let __anf_capture_501 = v240;
                            move |v503: Int63, v504: (Array<Int63>, Array<Int63>)| -> (Array<Int63>, Array<Int63>) {
                              let RX = &__anf_capture_495;
                              let RY = &__anf_capture_497;
                              let b_1 = &__anf_capture_499;
                              let tmp_20 = up_step(RX, RY, b_1, Clone::clone(&__anf_capture_501), v503, v504);
                              tmp_20
                            }
                          });
                          let HY1_clone = Clone::clone(HY1);
                          let HX1_clone = Clone::clone(HX1);
                          std::mem::drop(tmp_19);
                          let tmp_21 = loop_::<(Array<Int63>, Array<Int63>)>(h, callback_12, callback_13, v240, (HY1_clone, HX1_clone));
                          match tmp_21 {
                            (v538, v540) => {
                              let best = sweep(v538, v540, h);
                              rocq_float64::div(rocq_float64::of_uint63(best - __rocq_global_625), rocq_float64::of_uint63(int63!(2)))
                            },
                          }
                        },
                      }
                    }
                  },
                }
              },
            }
          },
        }
      }
    },
  }
}
const __rocq_global_274: Int63 = int63!(67108864);
const __rocq_global_625: Int63 = int63!(1152921504606846976);