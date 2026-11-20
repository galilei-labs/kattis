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

// Rocq: Polymul2.polymul2_implem.NL
pub fn NL() -> Int63 {
  int63!(6)
}

// Rocq: Polymul2.polymul2_implem.KOFF
pub fn KOFF() -> Int63 {
  int63!(34905131040)
}

// Rocq: Polymul2.polymul2_implem.MAGIC
pub fn MAGIC() -> f64 {
  f64::from_bits(4843621399236968448u64)
}

// Rocq: Polymul2.polymul2_implem.MAGICI
pub fn MAGICI() -> Int63 {
  int63!(6755399441055744)
}

// Rocq: Polymul2.polymul2_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Polymul2.polymul2_implem.lg_find
// Variant: uncurried
pub fn lg_find_1(L: Int63, k: Int63) -> Int63 {
  lg_find(L, k, ())
}

// Rocq: Polymul2.polymul2_implem.lg_find (local: lg_find)
// Variant: uncurried, lifted
pub fn lg_find(L: Int63, k: Int63, _H: ()) -> Int63 {
  let tmp = k < int63!(62);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(1) << k;
      if L <= tmp_1 {
        k
      } else {
        lg_find(L, k + int63!(1), ())
      }
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Polymul2.polymul2_implem.log2up
pub fn log2up(L: Int63) -> Int63 {
  lg_find_1(L, int63!(0))
}

// Rocq: Polymul2.polymul2_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Polymul2.polymul2_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St, _H: ()) -> St {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let f_ref: &Rc<dyn Fn(Int63, St) -> St> = &f;
      let tmp_2 = f_ref(i, s);
      wloop::<St>(hi, f, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      s
    },
  }
}

// Rocq: Polymul2.polymul2_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Polymul2.polymul2_implem.tw_cell
// Variant: uncurried
pub fn tw_cell(m: Int63, hm: Int63, bc: f64, bs: f64, k: Int63, st: (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>) {
  match st {
    (v7, v9) => {
      let tim = &v7;
      let tre = &v9;
      let src = hm + (k >> int63!(1));
      let ar = tim.get_cloned(src);
      let ai = tre.get_cloned(src);
      let tmp = k & int63!(1);
      if tmp == int63!(0) {
        (v7.set(m + k, ar), v9.set(m + k, ai))
      } else {
        (v7.set(m + k, rocq_float64::sub(rocq_float64::mul(ar, bc), rocq_float64::mul(ai, bs))), v9.set(m + k, rocq_float64::add(rocq_float64::mul(ar, bs), rocq_float64::mul(ai, bc))))
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.tw_stage
// Variant: uncurried
pub fn tw_stage(s: Int63, st: (((Array<f64>, Array<f64>), f64), f64)) -> (((Array<f64>, Array<f64>), f64), f64) {
  match st {
    (v3, v5) => {
      match v3 {
        (v8, v10) => {
          match v8 {
            (v13, v15) => {
              let m = int63!(1) << s;
              let tmp = int63!(1) << s - int63!(1);
              let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
                let __anf_capture_51 = m;
                let __anf_capture_55 = v10;
                let __anf_capture_57 = v5;
                move |v59: Int63, v60: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
                  let tmp_1 = Clone::clone(&__anf_capture_51);
                  let tmp_2 = Clone::clone(&tmp);
                  let tmp_3 = Clone::clone(&__anf_capture_55);
                  let tmp_4 = Clone::clone(&__anf_capture_57);
                  tw_cell(tmp_1, tmp_2, tmp_3, tmp_4, v59, v60)
                }
              });
              let tmp_5 = loop_::<(Array<f64>, Array<f64>)>(m, callback, int63!(0), (v13, v15));
              match tmp_5 {
                (v97, v99) => {
                  let c_ = rocq_float64::sqrt(rocq_float64::mul(rocq_float64::add(f64::from_bits(4607182418800017408u64), v10), f64::from_bits(4602678819172646912u64)));
                  (((v97, v99), c_), rocq_float64::div(v5, rocq_float64::mul(f64::from_bits(4611686018427387904u64), c_)))
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.build_tw
// Variant: uncurried
pub fn build_tw(lg: Int63, N: Int63) -> (Array<f64>, Array<f64>) {
  let tre = Array::<f64>::make(N, f64::from_bits(0u64)).set(int63!(1), f64::from_bits(4607182418800017408u64));
  let tim = Array::<f64>::make(N, f64::from_bits(0u64));
  let tmp: fn(Int63, (((Array<f64>, Array<f64>), f64), f64)) -> (((Array<f64>, Array<f64>), f64), f64) = tw_stage;
  let tmp_1: Rc<dyn Fn(Int63, (((Array<f64>, Array<f64>), f64), f64)) -> (((Array<f64>, Array<f64>), f64), f64)> = Rc::new(tmp);
  let tmp_2 = loop_::<(((Array<f64>, Array<f64>), f64), f64)>(lg, tmp_1, int63!(1), (((tre, tim), f64::from_bits(0u64)), f64::from_bits(4607182418800017408u64)));
  match tmp_2 {
    (v65, _v67) => {
      match v65 {
        (v70, _v72) => {
          match v70 {
            (v75, v77) => {
              (v75, v77)
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.bfly
// Variant: borrowed, uncurried
pub fn bfly(sh: Int63, m: Int63, half: Int63, neg: bool, sre: &Array<f64>, sim: &Array<f64>, tre: &Array<f64>, tim: &Array<f64>, j: Int63, st: (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>) {
  let sh_1 = sh;
  let m_1 = m;
  let half_1 = half;
  let neg_1 = neg;
  let j_1 = j;
  let st_1 = st;
  match st_1 {
    (v17, v19) => {
      let dim = &v17;
      let dre = &v19;
      let q = j_1 >> sh_1;
      let i1 = j_1 + (q << sh_1);
      let i2 = i1 + (int63!(1) << sh_1);
      let wr = tre.get_cloned(m_1 + q);
      let wi = if neg_1 {
        rocq_float64::opp(tim.get_cloned(m_1 + q))
      } else {
        tim.get_cloned(m_1 + q)
      };
      let ur = sre.get_cloned(i1);
      let ui = sim.get_cloned(i1);
      let vr = sre.get_cloned(i2);
      let vi = sim.get_cloned(i2);
      let tr = rocq_float64::sub(rocq_float64::mul(wr, vr), rocq_float64::mul(wi, vi));
      let ti = rocq_float64::add(rocq_float64::mul(wr, vi), rocq_float64::mul(wi, vr));
      let tmp = rocq_float64::add(ur, tr);
      let dim_clone = Clone::clone(dim);
      std::mem::drop(v17);
      let tmp_1 = dim_clone.set(j_1, tmp).set(j_1 + half_1, rocq_float64::sub(ur, tr));
      let tmp_2 = rocq_float64::add(ui, ti);
      let dre_clone = Clone::clone(dre);
      std::mem::drop(v19);
      (tmp_1, dre_clone.set(j_1, tmp_2).set(j_1 + half_1, rocq_float64::sub(ui, ti)))
    },
  }
}

// Rocq: Polymul2.polymul2_implem.fft_stage
// Variant: borrowed, uncurried
pub fn fft_stage(lg: Int63, half: Int63, neg: bool, tre: &Array<f64>, tim: &Array<f64>, s: Int63, st: (((Array<f64>, Array<f64>), Array<f64>), Array<f64>)) -> (((Array<f64>, Array<f64>), Array<f64>), Array<f64>) {
  let lg_1 = lg;
  let half_1 = half;
  let neg_1 = neg;
  let s_1 = s;
  let st_1 = st;
  match st_1 {
    (v13, v15) => {
      match v13 {
        (v18, v20) => {
          match v18 {
            (v23, v25) => {
              let sim = &v23;
              let sre = &v25;
              let tmp = lg_1 - int63!(1) - s_1;
              let tmp_1 = int63!(1) << s_1;
              let sim_clone = Clone::clone(sim);
              let sre_clone = Clone::clone(sre);
              let tre_clone = Clone::clone(tre);
              let tim_clone = Clone::clone(tim);
              let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
                let __anf_capture_75 = half_1;
                move |v87: Int63, v88: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
                  let v71 = &tmp;
                  let v73 = &tmp_1;
                  let half = &__anf_capture_75;
                  let neg = &neg_1;
                  let sim = &sim_clone;
                  let sre = &sre_clone;
                  let tre = &tre_clone;
                  let tim = &tim_clone;
                  let tmp_2 = bfly(Clone::clone(v71), Clone::clone(v73), Clone::clone(half), Clone::clone(neg), sim, sre, tre, tim, v87, v88);
                  tmp_2
                }
              });
              let tmp_3 = loop_::<(Array<f64>, Array<f64>)>(half_1, callback, int63!(0), (v20, v15));
              match tmp_3 {
                (v129, v131) => {
                  (((v129, v131), v23), v25)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.fft
// Variant: uncurried
pub fn fft(lg: Int63, half: Int63, neg: bool, tre: Array<f64>, tim: Array<f64>, re: Array<f64>, im: Array<f64>) -> (Array<f64>, Array<f64>) {
  let N = half + half;
  let callback: Rc<dyn Fn(Int63, (((Array<f64>, Array<f64>), Array<f64>), Array<f64>)) -> (((Array<f64>, Array<f64>), Array<f64>), Array<f64>)> = Rc::new({
    let __anf_capture_25 = lg;
    let __anf_capture_27 = half;
    move |v35: Int63, v36: (((Array<f64>, Array<f64>), Array<f64>), Array<f64>)| -> (((Array<f64>, Array<f64>), Array<f64>), Array<f64>) {
      let lg = &__anf_capture_25;
      let half = &__anf_capture_27;
      let neg = &neg;
      let tre = &tre;
      let tim = &tim;
      let tmp = fft_stage(Clone::clone(lg), Clone::clone(half), Clone::clone(neg), tre, tim, v35, v36);
      tmp
    }
  });
  let tmp_1 = loop_::<(((Array<f64>, Array<f64>), Array<f64>), Array<f64>)>(lg, callback, int63!(0), (((re, im), Array::<f64>::make(N, f64::from_bits(0u64))), Array::<f64>::make(N, f64::from_bits(0u64))));
  match tmp_1 {
    (v99, v101) => {
      match v99 {
        (v104, v106) => {
          match v104 {
            (v109, v111) => {
              std::mem::drop(v106);
              std::mem::drop(v101);
              (v109, v111)
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.limb
// Variant: uncurried
pub fn limb(c: Int63, i: Int63) -> f64 {
  rocq_float64::sub(rocq_float64::of_uint63(c + __rocq_global_760 >> int63!(6) * i & int63!(63)), f64::from_bits(4629700416936869888u64))
}

// Rocq: Polymul2.polymul2_implem.load
// Variant: borrowed, uncurried
pub fn load(x: &Array<Int63>, n: Int63, N: Int63, i: Int63) -> Array<f64> {
  let n_1 = n;
  let N_1 = N;
  let x_clone = Clone::clone(x);
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    move |t: Int63, a_1: Array<f64>| -> Array<f64> {
      let x = &x_clone;
      let i = &i;
      let tmp = x.get_cloned(t);
      let i_clone = Clone::clone(i);
      a_1.set(t, limb(tmp, i_clone))
    }
  });
  loop_::<Array<f64>>(n_1, callback, int63!(0), Array::<f64>::make(N_1, f64::from_bits(0u64)))
}

// Rocq: Polymul2.polymul2_implem.copy_out
// Variant: uncurried
pub fn copy_out(N: Int63, off: Int63, yr: Array<f64>, yi: Array<f64>, st: (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>) {
  let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
    move |k: Int63, st: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
      let yr = &yr;
      let off = &off;
      let yi = &yi;
      match st {
        (v22, v24) => {
          let tmp = v22.set(Clone::clone(off) + k, yr.get_cloned(k));
          let tmp_1 = Clone::clone(off) + k;
          let tmp_2 = yi.get_cloned(k);
          (tmp, v24.set(tmp_1, tmp_2))
        },
      }
    }
  });
  loop_::<(Array<f64>, Array<f64>)>(N, callback, int63!(0), st)
}

// Rocq: Polymul2.polymul2_implem.fwd_all
// Variant: uncurried
pub fn fwd_all(x: Array<Int63>, n: Int63, lg: Int63, half: Int63, tre: Array<f64>, tim: Array<f64>) -> (Array<f64>, Array<f64>) {
  let N = half + half;
  let tmp = __rocq_global_546;
  let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
    let __anf_capture_35 = half;
    let __anf_capture_41 = N;
    move |i: Int63, st: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
      let x = &x;
      let n = &n;
      let lg = &lg;
      let half = &__anf_capture_35;
      let tre = &tre;
      let tim = &tim;
      let N = &__anf_capture_41;
      let tmp_1 = false;
      let tmp_2 = load(x, Clone::clone(n), Clone::clone(N), i);
      let tmp_3 = f64::from_bits(0u64);
      let tmp_4 = Array::<f64>::make(Clone::clone(N), tmp_3);
      let tmp_5 = fft(Clone::clone(lg), Clone::clone(half), tmp_1, Clone::clone(tre), Clone::clone(tim), tmp_2, tmp_4);
      match tmp_5 {
        (v80, v82) => {
          let tmp_6 = i * Clone::clone(N);
          let N_clone = Clone::clone(N);
          copy_out(N_clone, tmp_6, v80, v82, st)
        },
      }
    }
  });
  loop_::<(Array<f64>, Array<f64>)>(tmp, callback, int63!(0), (Array::<f64>::make(__rocq_global_546 * N, f64::from_bits(0u64)), Array::<f64>::make(__rocq_global_546 * N, f64::from_bits(0u64))))
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

// Rocq: Polymul2.polymul2_implem.cacc
// Variant: uncurried
pub fn cacc(ar: f64, ai: f64, br: f64, bi: f64, st: (f64, f64)) -> (f64, f64) {
  match st {
    (v6, v8) => {
      let tmp = rocq_float64::add(v6, rocq_float64::sub(rocq_float64::mul(ar, br), rocq_float64::mul(ai, bi)));
      let tmp_1 = rocq_float64::add(rocq_float64::mul(ar, bi), rocq_float64::mul(ai, br));
      (tmp, rocq_float64::add(v8, tmp_1))
    },
  }
}

// Rocq: Polymul2.polymul2_implem.pterm
// Variant: borrowed, uncurried
pub fn pterm(w: Int63, N: Int63, k: Int63, AR: &Array<f64>, AI: &Array<f64>, BR: &Array<f64>, BI: &Array<f64>, i: Int63, st: (f64, f64)) -> (f64, f64) {
  let w_1 = w;
  let N_1 = N;
  let k_1 = k;
  let i_1 = i;
  let st_1 = st;
  let tmp = i_1 <= w_1;
  let tmp_1 = w_1 - i_1 < __rocq_global_546;
  if andb(tmp, tmp_1) {
    cacc(AR.get_cloned(i_1 * N_1 + k_1), AI.get_cloned(i_1 * N_1 + k_1), BR.get_cloned((w_1 - i_1) * N_1 + k_1), BI.get_cloned((w_1 - i_1) * N_1 + k_1), st_1)
  } else {
    st_1
  }
}

// Rocq: Polymul2.polymul2_implem.pcell
// Variant: borrowed, uncurried
pub fn pcell(g: Int63, N: Int63, AR: &Array<f64>, AI: &Array<f64>, BR: &Array<f64>, BI: &Array<f64>, k: Int63, st: (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>) {
  let g_1 = g;
  let N_1 = N;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v13, v15) => {
      let tmp = __rocq_global_546;
      let tmp_1 = g_1 + g_1;
      let AR_clone = Clone::clone(AR);
      let AI_clone = Clone::clone(AI);
      let BR_clone = Clone::clone(BR);
      let BI_clone = Clone::clone(BI);
      let callback: Rc<dyn Fn(Int63, (f64, f64)) -> (f64, f64)> = Rc::new({
        let __anf_capture_46 = N_1;
        let __anf_capture_48 = k_1;
        move |v58: Int63, v59: (f64, f64)| -> (f64, f64) {
          let v44 = &tmp_1;
          let N = &__anf_capture_46;
          let k = &__anf_capture_48;
          let AR = &AR_clone;
          let AI = &AI_clone;
          let BR = &BR_clone;
          let BI = &BI_clone;
          let tmp_2 = pterm(Clone::clone(v44), Clone::clone(N), Clone::clone(k), AR, AI, BR, BI, v58, v59);
          tmp_2
        }
      });
      let tmp_3 = loop_::<(f64, f64)>(tmp, callback, int63!(0), (f64::from_bits(0u64), f64::from_bits(0u64)));
      match tmp_3 {
        (v102, v104) => {
          let tmp_4 = __rocq_global_546;
          let tmp_5 = g_1 + g_1 + int63!(1);
          let AR_clone_1 = Clone::clone(AR);
          let AI_clone_1 = Clone::clone(AI);
          let BR_clone_1 = Clone::clone(BR);
          let BI_clone_1 = Clone::clone(BI);
          let callback_1: Rc<dyn Fn(Int63, (f64, f64)) -> (f64, f64)> = Rc::new({
            let __anf_capture_143 = N_1;
            let __anf_capture_145 = k_1;
            move |v155: Int63, v156: (f64, f64)| -> (f64, f64) {
              let v141 = &tmp_5;
              let N = &__anf_capture_143;
              let k = &__anf_capture_145;
              let AR = &AR_clone_1;
              let AI = &AI_clone_1;
              let BR = &BR_clone_1;
              let BI = &BI_clone_1;
              let tmp_6 = pterm(Clone::clone(v141), Clone::clone(N), Clone::clone(k), AR, AI, BR, BI, v155, v156);
              tmp_6
            }
          });
          let tmp_7 = loop_::<(f64, f64)>(tmp_4, callback_1, int63!(0), (f64::from_bits(0u64), f64::from_bits(0u64)));
          match tmp_7 {
            (v199, v201) => {
              (v13.set(k_1, rocq_float64::sub(v102, v201)), v15.set(k_1, rocq_float64::add(v104, v199)))
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.products
// Variant: borrowed, uncurried
pub fn products(g: Int63, N: Int63, AR: &Array<f64>, AI: &Array<f64>, BR: &Array<f64>, BI: &Array<f64>) -> (Array<f64>, Array<f64>) {
  let AR_clone = Clone::clone(AR);
  let AI_clone = Clone::clone(AI);
  let BR_clone = Clone::clone(BR);
  let BI_clone = Clone::clone(BI);
  let callback: Rc<dyn Fn(Int63, (Array<f64>, Array<f64>)) -> (Array<f64>, Array<f64>)> = Rc::new({
    let __anf_capture_28 = N;
    move |v38: Int63, v39: (Array<f64>, Array<f64>)| -> (Array<f64>, Array<f64>) {
      let g = &g;
      let N = &__anf_capture_28;
      let AR = &AR_clone;
      let AI = &AI_clone;
      let BR = &BR_clone;
      let BI = &BI_clone;
      let tmp = pcell(Clone::clone(g), Clone::clone(N), AR, AI, BR, BI, v38, v39);
      tmp
    }
  });
  let tmp_1 = Array::<f64>::make(N, f64::from_bits(0u64));
  let tmp_2 = Array::<f64>::make(N, f64::from_bits(0u64));
  loop_::<(Array<f64>, Array<f64>)>(N, callback, int63!(0), (tmp_1, tmp_2))
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, Int63) {
  (rocq_float64::frshiftexp_fraction(x), rocq_float64::frshiftexp_exponent(x))
}

// Rocq: Polymul2.polymul2_implem.toint
pub fn toint(z: f64) -> Int63 {
  let tmp = frshiftexp(rocq_float64::add(z, __rocq_global_1162));
  match tmp {
    (v13, _v15) => {
      rocq_float64::normfr_mantissa(v13) - __rocq_global_1171
    },
  }
}

// Rocq: Polymul2.polymul2_implem.accum
// Variant: uncurried
pub fn accum(g: Int63, L: Int63, invN: f64, yr: Array<f64>, yi: Array<f64>, R: Array<Int63>) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    move |q: Int63, R: Array<Int63>| -> Array<Int63> {
      let yr = &yr;
      let yi = &yi;
      let invN = &invN;
      let g = &g;
      let d0 = toint(rocq_float64::mul(yr.get_cloned(q), Clone::clone(invN)));
      let d1 = toint(rocq_float64::mul(yi.get_cloned(q), Clone::clone(invN)));
      let tmp = R.get_cloned(q);
      let tmp_1 = tmp + (d0 << int63!(12) * Clone::clone(g));
      let g_clone = Clone::clone(g);
      R.set(q, tmp_1 + (d1 << int63!(12) * g_clone + int63!(6)))
    }
  });
  loop_::<Array<Int63>>(L, callback, int63!(0), R)
}

// Rocq: Polymul2.polymul2_implem.polymul_impl
// Variant: uncurried
pub fn polymul_impl(x: Array<Int63>, y: Array<Int63>) -> Array<Int63> {
  let na = x.length();
  let nb = y.length();
  let L = na + nb - int63!(1);
  let lg = log2up(L);
  let half = int63!(1) << lg - int63!(1);
  let N = half + half;
  let tmp = build_tw(lg, N);
  match tmp {
    (v53, v55) => {
      let tim = &v53;
      let tre = &v55;
      let tmp_1 = fwd_all(x, na, lg, half, Clone::clone(tim), Clone::clone(tre));
      match tmp_1 {
        (v74, v76) => {
          let tim_clone = Clone::clone(tim);
          let tre_clone = Clone::clone(tre);
          let tmp_2 = fwd_all(y, nb, lg, half, tim_clone, tre_clone);
          match tmp_2 {
            (v93, v95) => {
              let invN = rocq_float64::div(f64::from_bits(4607182418800017408u64), rocq_float64::of_uint63(N));
              let tmp_3 = __rocq_global_546;
              let callback: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
                let __anf_capture_134 = N;
                let __anf_capture_144 = lg;
                let __anf_capture_146 = half;
                let __anf_capture_148 = v53;
                let __anf_capture_150 = v55;
                let __anf_capture_152 = L;
                move |g: Int63, R: Array<Int63>| -> Array<Int63> {
                  let N = &__anf_capture_134;
                  let AI = &v74;
                  let AR = &v76;
                  let BI = &v93;
                  let BR = &v95;
                  let lg = &__anf_capture_144;
                  let half = &__anf_capture_146;
                  let tim = &__anf_capture_148;
                  let tre = &__anf_capture_150;
                  let L = &__anf_capture_152;
                  let invN = &invN;
                  let tmp_4 = products(g, Clone::clone(N), AI, AR, BI, BR);
                  match &tmp_4 {
                    (pim, pr) => {
                      let lg_clone = Clone::clone(lg);
                      let half_clone = Clone::clone(half);
                      let tim_clone_1 = Clone::clone(tim);
                      let tre_clone_1 = Clone::clone(tre);
                      let pim_clone = Clone::clone(pim);
                      let pr_clone = Clone::clone(pr);
                      std::mem::drop(tmp_4);
                      let tmp_5 = fft(lg_clone, half_clone, true, tim_clone_1, tre_clone_1, pim_clone, pr_clone);
                      match tmp_5 {
                        (v193, v195) => {
                          let L_clone = Clone::clone(L);
                          let invN_clone = Clone::clone(invN);
                          accum(g, L_clone, invN_clone, v193, v195, R)
                        },
                      }
                    },
                  }
                }
              });
              loop_::<Array<Int63>>(tmp_3, callback, int63!(0), Array::<Int63>::make(L, int63!(0)))
            },
          }
        },
      }
    },
  }
}
const __rocq_global_546: Int63 = int63!(6);
const __rocq_global_760: Int63 = int63!(34905131040);
const __rocq_global_1162: f64 = f64::from_bits(4843621399236968448u64);
const __rocq_global_1171: Int63 = int63!(6755399441055744);