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

pub type sint = Int63;

// Rocq: Roberthood.roberthood_implem.Kneg
pub fn Kneg() -> Int63 {
  int63!(4098000)
}

// Rocq: Roberthood.roberthood_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Roberthood.roberthood_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roberthood.roberthood_implem.wloop (local: wloop)
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

// Rocq: Roberthood.roberthood_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Roberthood.roberthood_implem.encode
// Variant: uncurried
pub fn encode(x: Int63, y: Int63) -> Int63 {
  (x + int63!(1000)) * int63!(2048) + (y + int63!(1000))
}

// Rocq: Roberthood.roberthood_implem.key_step
// Variant: uncurried
pub fn key_step(x: Array<Int63>, y: Array<Int63>, i: Int63, A: Array<Int63>) -> Array<Int63> {
  let tmp = x.get_cloned(i);
  std::mem::drop(x);
  let tmp_1 = y.get_cloned(i);
  std::mem::drop(y);
  A.set(i, encode(tmp, tmp_1))
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

// Rocq: Roberthood.roberthood_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(src: &Array<Int63>, mid: Int63, hi: Int63, k: Int63, st: ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let tmp = v15 < mid_1;
          let tmp_1 = orb(hi_1 <= v17, src.get_cloned(v15) <= src.get_cloned(v17));
          if andb(tmp, tmp_1) {
            ((v15 + int63!(1), v17), v12.set(k_1, src.get_cloned(v15)))
          } else {
            ((v15, v17 + int63!(1)), v12.set(k_1, src.get_cloned(v17)))
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.merge
// Variant: uncurried
pub fn merge(src: Array<Int63>, lo: Int63, mid: Int63, hi: Int63, D: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> bool> = Rc::new(move |_v7: Int63, v8: ((Int63, Int63), Array<Int63>)| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>)> = Rc::new({
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: Int63, v29: ((Int63, Int63), Array<Int63>)| -> ((Int63, Int63), Array<Int63>) {
      let src = &src;
      let tmp = merge_step(src, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      tmp
    }
  });
  let tmp_1 = (lo, mid);
  let tmp_2 = loop_::<((Int63, Int63), Array<Int63>)>(hi, callback, callback_1, lo, (tmp_1, D));
  match tmp_2 {
    (v69, v71) => {
      match v69 {
        (_v74, _v76) => {
          v71
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.pass_step
// Variant: uncurried
pub fn pass_step(src: Array<Int63>, n: Int63, w: Int63, c: Int63, D: Array<Int63>) -> Array<Int63> {
  let lo = c * (w + w);
  let tmp = lo + w;
  let mid = if tmp < n {
    lo + w
  } else {
    n
  };
  let tmp_1 = lo + (w + w);
  let hi = if tmp_1 < n {
    lo + (w + w)
  } else {
    n
  };
  merge(src, lo, mid, hi, D)
}

// Rocq: Roberthood.roberthood_implem.merge_pass
// Variant: uncurried
pub fn merge_pass(src: Array<Int63>, D: Array<Int63>, n: Int63, w: Int63) -> Array<Int63> {
  let tmp = (n + (w + w) - int63!(1)) / (w + w);
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v38: Int63, v39: Array<Int63>| -> bool {
    std::mem::drop(v39);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    let __anf_capture_55 = n;
    let __anf_capture_57 = w;
    move |v59: Int63, v60: Array<Int63>| -> Array<Int63> {
      let src_clone = Clone::clone(&src);
      let tmp_1 = Clone::clone(&__anf_capture_55);
      let tmp_2 = Clone::clone(&__anf_capture_57);
      pass_step(src_clone, tmp_1, tmp_2, v59, v60)
    }
  });
  loop_::<Array<Int63>>(tmp, callback, callback_1, int63!(0), D)
}

// Rocq: Roberthood.roberthood_implem.msort_rec
// Variant: uncurried
pub fn msort_rec_1(n: Int63, w: Int63, A: Array<Int63>, B: Array<Int63>) -> Array<Int63> {
  msort_rec(n, w, A, B, ())
}

// Rocq: Roberthood.roberthood_implem.msort_rec (local: msort_rec)
// Variant: uncurried, lifted
pub fn msort_rec(n: Int63, w: Int63, A: Array<Int63>, B: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = w < n;
  let tmp_1 = w + w;
  let tmp_2 = andb(tmp, w < tmp_1);
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = w + w;
      let A_clone = Clone::clone(&A);
      let tmp_4 = merge_pass(A_clone, B, n, w);
      msort_rec(n, tmp_3, tmp_4, A, ())
    },
    sumbool::right => {
      std::mem::drop(B);
      A
    },
  }
}

// Rocq: Roberthood.roberthood_implem.msort
// Variant: uncurried
pub fn msort(A: Array<Int63>, n: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, int63!(0));
  msort_rec_1(n, int63!(1), A, tmp)
}

// Rocq: Roberthood.roberthood_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(A: &Array<Int63>, i: Int63, st: (Array<Int63>, Int63)) -> (Array<Int63>, Int63) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let a_1 = A.get_cloned(i_1);
      let tmp = m.get_cloned(v8 - int63!(1));
      if a_1 == tmp {
        (v6, v8)
      } else {
        (v6.set(v8, a_1), v8 + int63!(1))
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.neg_step
// Variant: uncurried
pub fn neg_step(Q: Array<Int63>, m: Int63, i: Int63, B: Array<Int63>) -> Array<Int63> {
  let tmp = __rocq_global_654;
  let tmp_1 = Q.get_cloned(m - int63!(1) - i);
  std::mem::drop(Q);
  B.set(i, tmp - tmp_1)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Roberthood.roberthood_implem.cx
pub fn cx(k: Int63) -> Int63 {
  k / int63!(2048) - int63!(1000)
}

// Rocq: Roberthood.roberthood_implem.cy
pub fn cy(k: Int63) -> Int63 {
  k % int63!(2048) - int63!(1000)
}

// Rocq: Roberthood.roberthood_implem.mcross
// Variant: uncurried
pub fn mcross(a1: Int63, a2: Int63, b1: Int63, b2: Int63) -> Int63 {
  (cx(a2) - cx(a1)) * (cy(b2) - cy(b1)) - (cy(a2) - cy(a1)) * (cx(b2) - cx(b1))
}

// Rocq: Roberthood.roberthood_implem.pops
// Variant: uncurried
pub fn pops_1(St: Array<Int63>, c: Int63, t: Int63) -> Int63 {
  pops(St, c, t, ())
}

// Rocq: Roberthood.roberthood_implem.pops (local: pops)
// Variant: uncurried, lifted
pub fn pops(St: Array<Int63>, c: Int63, t: Int63, _H: ()) -> Int63 {
  let tmp = int63!(1) < t;
  let tmp_1 = St.get_cloned(t - int63!(2));
  let tmp_2 = St.get_cloned(t - int63!(1));
  let tmp_3 = St.get_cloned(t - int63!(2));
  let tmp_4 = andb(tmp, negb(int63!(0).ltsb(mcross(tmp_1, tmp_2, tmp_3, c))));
  match bdec(tmp_4) {
    sumbool::left => {
      pops(St, c, t - int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(St);
      t
    },
  }
}

// Rocq: Roberthood.roberthood_implem.chain_step
// Variant: borrowed, uncurried
pub fn chain_step(Q: &Array<Int63>, i: Int63, st: (Array<Int63>, Int63)) -> (Array<Int63>, Int63) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let t = &v6;
      let c = Q.get_cloned(i_1);
      let t_clone = Clone::clone(t);
      let t_1 = pops_1(t_clone, c, v8);
      (v6.set(t_1, c), t_1 + int63!(1))
    },
  }
}

// Rocq: Roberthood.roberthood_implem.chain
// Variant: uncurried
pub fn chain(Q: Array<Int63>, m: Int63) -> (Array<Int63>, Int63) {
  let callback: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v4: Int63, v5: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v5);
    true
  });
  let Q_clone = Clone::clone(&Q);
  let callback_1: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |v18: Int63, v19: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let Q = &Q_clone;
      let tmp = chain_step(Q, v18, v19);
      tmp
    }
  });
  let tmp_1 = int63!(1);
  let tmp_2 = Q.get_cloned(int63!(0));
  std::mem::drop(Q);
  let tmp_3 = Array::<Int63>::make(m, tmp_2);
  loop_::<(Array<Int63>, Int63)>(m, callback, callback_1, tmp_1, (tmp_3, int63!(1)))
}

// Rocq: Roberthood.roberthood_implem.msq
// Variant: uncurried
pub fn msq(a_1: Int63, b_1: Int63) -> Int63 {
  let dx = cx(a_1) + cx(b_1);
  let dy = cy(a_1) + cy(b_1);
  dx * dx + dy * dy
}

// Rocq: Roberthood.roberthood_implem.cal_step
// Variant: borrowed, uncurried
pub fn cal_step(L: &Array<Int63>, N: &Array<Int63>, lL: Int63, lN: Int63, _s: Int63, st: ((Int63, Int63), Int63)) -> ((Int63, Int63), Int63) {
  let lL_1 = lL;
  let lN_1 = lN;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let k = &v15;
          let j = &v17;
          let d = msq(L.get_cloned(v15), N.get_cloned(v17));
          let best = if v12 < d {
            d
          } else {
            v12
          };
          let tmp = Clone::clone(k) < lL_1;
          let tmp_1 = Clone::clone(j) == lN_1;
          let tmp_2 = L.get_cloned(Clone::clone(k));
          let tmp_3 = int63!(1);
          let tmp_4 = L.get_cloned(Clone::clone(k) + tmp_3);
          let tmp_5 = N.get_cloned(Clone::clone(j));
          let tmp_6 = int63!(1);
          let tmp_7 = orb(tmp_1, int63!(0).ltsb(mcross(tmp_2, tmp_4, tmp_5, N.get_cloned(Clone::clone(j) + tmp_6))));
          if andb(tmp, tmp_7) {
            let k_clone = Clone::clone(k);
            let tmp_8 = k_clone + int63!(1);
            let j_clone = Clone::clone(j);
            ((tmp_8, j_clone), best)
          } else {
            let j_clone_1 = Clone::clone(j);
            let tmp_9 = j_clone_1 + int63!(1);
            let k_clone_1 = Clone::clone(k);
            ((k_clone_1, tmp_9), best)
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.calipers
// Variant: uncurried
pub fn calipers(L: Array<Int63>, N: Array<Int63>, lL: Int63, lN: Int63) -> Int63 {
  let tmp = lL + lN;
  let callback: Rc<dyn Fn(Int63, ((Int63, Int63), Int63)) -> bool> = Rc::new(move |_v12: Int63, v13: ((Int63, Int63), Int63)| -> bool {
    std::mem::drop(v13);
    true
  });
  let L_clone = Clone::clone(&L);
  let N_clone = Clone::clone(&N);
  let callback_1: Rc<dyn Fn(Int63, ((Int63, Int63), Int63)) -> ((Int63, Int63), Int63)> = Rc::new({
    let __anf_capture_35 = lL;
    let __anf_capture_37 = lN;
    move |v39: Int63, v40: ((Int63, Int63), Int63)| -> ((Int63, Int63), Int63) {
      let L = &L_clone;
      let N = &N_clone;
      let tmp_1 = cal_step(L, N, Clone::clone(&__anf_capture_35), Clone::clone(&__anf_capture_37), v39, v40);
      tmp_1
    }
  });
  let tmp_2 = loop_::<((Int63, Int63), Int63)>(tmp, callback, callback_1, int63!(0), ((int63!(0), int63!(0)), int63!(0)));
  match tmp_2 {
    (v89, v91) => {
      match v89 {
        (v94, v96) => {
          let tmp_3 = L.get_cloned(v94);
          let tmp_4 = N.get_cloned(v96);
          let d = msq(tmp_3, tmp_4);
          if v91 < d {
            std::mem::drop(N);
            std::mem::drop(L);
            d
          } else {
            std::mem::drop(N);
            std::mem::drop(L);
            v91
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.diam2
// Variant: uncurried
pub fn diam2(x: Array<Int63>, y: Array<Int63>) -> Int63 {
  let n = x.length();
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v6: Int63, v7: Array<Int63>| -> bool {
    std::mem::drop(v7);
    true
  });
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |v25: Int63, v26: Array<Int63>| -> Array<Int63> {
      let tmp = Clone::clone(&x_clone);
      let tmp_1 = Clone::clone(&y_clone);
      key_step(tmp, tmp_1, v25, v26)
    }
  });
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let A = loop_::<Array<Int63>>(n, callback, callback_1, int63!(0), tmp_2);
  let A_1 = msort(A, n);
  let callback_2: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> bool> = Rc::new(move |_v69: Int63, v70: (Array<Int63>, Int63)| -> bool {
    std::mem::drop(v70);
    true
  });
  let A_clone = Clone::clone(&A_1);
  let callback_3: Rc<dyn Fn(Int63, (Array<Int63>, Int63)) -> (Array<Int63>, Int63)> = Rc::new({
    move |v83: Int63, v84: (Array<Int63>, Int63)| -> (Array<Int63>, Int63) {
      let A = &A_clone;
      let tmp_3 = dedup_step(A, v83, v84);
      tmp_3
    }
  });
  let tmp_4 = A_1.get_cloned(int63!(0));
  let tmp_5 = Array::<Int63>::make(n, tmp_4);
  let tmp_6 = loop_::<(Array<Int63>, Int63)>(n, callback_2, callback_3, int63!(1), (tmp_5, int63!(1)));
  match tmp_6 {
    (v129, v131) => {
      let m = &v129;
      if v131 < int63!(2) {
        std::mem::drop(x);
        std::mem::drop(y);
        std::mem::drop(A_1);
        std::mem::drop(v129);
        int63!(0)
      } else {
        let callback_4: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v149: Int63, v150: Array<Int63>| -> bool {
          std::mem::drop(v150);
          true
        });
        let m_clone = Clone::clone(m);
        let callback_5: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
          let __anf_capture_164 = v131;
          move |v166: Int63, v167: Array<Int63>| -> Array<Int63> {
            let tmp_7 = Clone::clone(&m_clone);
            let tmp_8 = Clone::clone(&__anf_capture_164);
            neg_step(tmp_7, tmp_8, v166, v167)
          }
        });
        let tmp_9 = Array::<Int63>::make(v131, int63!(0));
        let Q2 = loop_::<Array<Int63>>(v131, callback_4, callback_5, int63!(0), tmp_9);
        let tmp_10 = chain(v129, v131);
        match tmp_10 {
          (v209, v211) => {
            std::mem::drop(x);
            std::mem::drop(y);
            std::mem::drop(A_1);
            let tmp_11 = chain(Q2, v131);
            match tmp_11 {
              (v220, v222) => {
                calipers(v209, v220, v211 - int63!(1), v222 - int63!(1))
              },
            }
          },
        }
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.roberthood
// Variant: uncurried
pub fn roberthood(x: Array<Int63>, y: Array<Int63>) -> f64 {
  rocq_float64::sqrt(rocq_float64::of_uint63(diam2(x, y)))
}
const __rocq_global_654: Int63 = int63!(4098000);