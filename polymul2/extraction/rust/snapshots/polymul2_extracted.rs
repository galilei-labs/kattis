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

// Rocq: Polymul2.polymul2_implem.NL
pub fn NL() -> u64 {
  6u64
}

// Rocq: Polymul2.polymul2_implem.KOFF
pub fn KOFF() -> u64 {
  34905131040u64
}

// Rocq: Polymul2.polymul2_implem.MAGIC
pub fn MAGIC() -> f64 {
  f64::from_bits(4843621399236968448u64)
}

// Rocq: Polymul2.polymul2_implem.MAGICI
pub fn MAGICI() -> u64 {
  6755399441055744u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Polymul2.polymul2_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Polymul2.polymul2_implem.lg_find
// Variant: uncurried
pub fn lg_find_1(L: u64, k: u64) -> u64 {
  lg_find(L, k, ())
}

// Rocq: Polymul2.polymul2_implem.lg_find (local: lg_find)
// Variant: uncurried, lifted
pub fn lg_find(L: u64, k: u64, _H: ()) -> u64 {
  let tmp = ltb(k, 62u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = lsl(1u64, k);
      if leb(L, tmp_1) {
        k
      } else {
        lg_find(L, add(k, 1u64), ())
      }
    },
    sumbool::right => {
      k
    },
  }
}

// Rocq: Polymul2.polymul2_implem.log2up
pub fn log2up(L: u64) -> u64 {
  lg_find_1(L, 0u64)
}

// Rocq: Polymul2.polymul2_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Polymul2.polymul2_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64, St) -> St> = &f;
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
pub fn loop_<St: Clone + 'static>(hi: u64, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Corelib.Floats.PrimFloat.sub
// Variant: uncurried
pub fn sub_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::sub(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.mul
// Variant: uncurried
pub fn mul(v0: f64, v1: f64) -> f64 {
  rocq_float64::mul(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.add
// Variant: uncurried
pub fn add_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::add(v0, v1)
}

// Rocq: Polymul2.polymul2_implem.tw_cell
// Variant: uncurried
pub fn tw_cell(m: u64, hm: u64, bc: f64, bs: f64, k: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  match st {
    (v7, v9) => {
      let tim = &v7;
      let tre = &v9;
      let src = add(hm, lsr(k, 1u64));
      let ar = rocq_array::get::<f64>(tim, src);
      let ai = rocq_array::get::<f64>(tre, src);
      let tmp = land(k, 1u64);
      if eqb(tmp, 0u64) {
        let tmp_1 = rocq_array::set::<f64>(v7, add(m, k), ar);
        let tmp_2 = rocq_array::set::<f64>(v9, add(m, k), ai);
        (tmp_1, tmp_2)
      } else {
        let tmp_3 = rocq_array::set::<f64>(v7, add(m, k), sub_1(mul(ar, bc), mul(ai, bs)));
        let tmp_4 = rocq_array::set::<f64>(v9, add(m, k), add_1(mul(ar, bs), mul(ai, bc)));
        (tmp_3, tmp_4)
      }
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.sqrt
pub fn sqrt(v0: f64) -> f64 {
  rocq_float64::sqrt(v0)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Polymul2.polymul2_implem.tw_stage
// Variant: uncurried
pub fn tw_stage(s: u64, st: (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64) {
  match st {
    (v3, v5) => {
      match v3 {
        (v8, v10) => {
          match v8 {
            (v13, v15) => {
              let m = lsl(1u64, s);
              let tmp = lsl(1u64, sub(s, 1u64));
              let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
                let __anf_capture_51 = m;
                let __anf_capture_55 = v10;
                let __anf_capture_57 = v5;
                move |v59: u64, v60: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
                  let tmp_1 = Clone::clone(&__anf_capture_51);
                  let tmp_2 = Clone::clone(&tmp);
                  let tmp_3 = Clone::clone(&__anf_capture_55);
                  let tmp_4 = Clone::clone(&__anf_capture_57);
                  tw_cell(tmp_1, tmp_2, tmp_3, tmp_4, v59, v60)
                }
              });
              let tmp_5 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(m, callback, 0u64, (v13, v15));
              match tmp_5 {
                (v97, v99) => {
                  let c_ = sqrt(mul(add_1(f64::from_bits(4607182418800017408u64), v10), f64::from_bits(4602678819172646912u64)));
                  (((v97, v99), c_), div(v5, mul(f64::from_bits(4611686018427387904u64), c_)))
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
pub fn build_tw(lg: u64, N: u64) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let tmp = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tre = rocq_array::set::<f64>(tmp, 1u64, f64::from_bits(4607182418800017408u64));
  let tim = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tmp_1: fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64) = tw_stage;
  let tmp_2: Rc<dyn Fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)> = Rc::new(tmp_1);
  let tmp_3 = loop_::<(((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)>(lg, tmp_2, 1u64, (((tre, tim), f64::from_bits(0u64)), f64::from_bits(4607182418800017408u64)));
  match tmp_3 {
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

// Rocq: Corelib.Floats.PrimFloat.opp
pub fn opp(v0: f64) -> f64 {
  rocq_float64::opp(v0)
}

// Rocq: Polymul2.polymul2_implem.bfly
// Variant: borrowed, uncurried
pub fn bfly(sh: u64, m: u64, half: u64, neg: bool, sre: &Rc<Array<f64>>, sim: &Rc<Array<f64>>, tre: &Rc<Array<f64>>, tim: &Rc<Array<f64>>, j: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
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
      let q = lsr(j_1, sh_1);
      let i1 = add(j_1, lsl(q, sh_1));
      let i2 = add(i1, lsl(1u64, sh_1));
      let wr = rocq_array::get::<f64>(tre, add(m_1, q));
      let wi = if neg_1 {
        opp(rocq_array::get::<f64>(tim, add(m_1, q)))
      } else {
        rocq_array::get::<f64>(tim, add(m_1, q))
      };
      let ur = rocq_array::get::<f64>(sre, i1);
      let ui = rocq_array::get::<f64>(sim, i1);
      let vr = rocq_array::get::<f64>(sre, i2);
      let vi = rocq_array::get::<f64>(sim, i2);
      let tr = sub_1(mul(wr, vr), mul(wi, vi));
      let ti = add_1(mul(wr, vi), mul(wi, vr));
      let tmp = add_1(ur, tr);
      let dim_clone = Rc::clone(dim);
      std::mem::drop(v17);
      let tmp_1 = rocq_array::set::<f64>(dim_clone, j_1, tmp);
      let tmp_2 = rocq_array::set::<f64>(tmp_1, add(j_1, half_1), sub_1(ur, tr));
      let tmp_3 = add_1(ui, ti);
      let dre_clone = Rc::clone(dre);
      std::mem::drop(v19);
      let tmp_4 = rocq_array::set::<f64>(dre_clone, j_1, tmp_3);
      let tmp_5 = rocq_array::set::<f64>(tmp_4, add(j_1, half_1), sub_1(ui, ti));
      (tmp_2, tmp_5)
    },
  }
}

// Rocq: Polymul2.polymul2_implem.fft_stage
// Variant: borrowed, uncurried
pub fn fft_stage(lg: u64, half: u64, neg: bool, tre: &Rc<Array<f64>>, tim: &Rc<Array<f64>>, s: u64, st: (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>) {
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
              let tmp = sub(lg_1, 1u64);
              let tmp_1 = sub(tmp, s_1);
              let tmp_2 = lsl(1u64, s_1);
              let sim_clone = Rc::clone(sim);
              let sre_clone = Rc::clone(sre);
              let tre_clone = Rc::clone(tre);
              let tim_clone = Rc::clone(tim);
              let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
                let __anf_capture_75 = half_1;
                move |v87: u64, v88: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
                  let v71 = &tmp_1;
                  let v73 = &tmp_2;
                  let half = &__anf_capture_75;
                  let neg = &neg_1;
                  let sim = &sim_clone;
                  let sre = &sre_clone;
                  let tre = &tre_clone;
                  let tim = &tim_clone;
                  let tmp_3 = bfly(Clone::clone(v71), Clone::clone(v73), Clone::clone(half), Clone::clone(neg), sim, sre, tre, tim, v87, v88);
                  tmp_3
                }
              });
              let tmp_4 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(half_1, callback, 0u64, (v20, v15));
              match tmp_4 {
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
pub fn fft(lg: u64, half: u64, neg: bool, tre: Rc<Array<f64>>, tim: Rc<Array<f64>>, re: Rc<Array<f64>>, im: Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let N = add(half, half);
  let callback: Rc<dyn Fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)> = Rc::new({
    let __anf_capture_25 = lg;
    let __anf_capture_27 = half;
    move |v35: u64, v36: (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)| -> (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>) {
      let lg = &__anf_capture_25;
      let half = &__anf_capture_27;
      let neg = &neg;
      let tre = &tre;
      let tim = &tim;
      let tmp = fft_stage(Clone::clone(lg), Clone::clone(half), Clone::clone(neg), tre, tim, v35, v36);
      tmp
    }
  });
  let tmp_1 = (re, im);
  let tmp_2 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tmp_3 = (tmp_1, tmp_2);
  let tmp_4 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tmp_5 = loop_::<(((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)>(lg, callback, 0u64, (tmp_3, tmp_4));
  match tmp_5 {
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

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul_1(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Polymul2.polymul2_implem.limb
// Variant: uncurried
pub fn limb(c: u64, i: u64) -> f64 {
  sub_1(of_uint63(land(lsr(add(c, __rocq_global_760), mul_1(6u64, i)), 63u64)), f64::from_bits(4629700416936869888u64))
}

// Rocq: Polymul2.polymul2_implem.load
// Variant: borrowed, uncurried
pub fn load(x: &Rc<Array<u64>>, n: u64, N: u64, i: u64) -> Rc<Array<f64>> {
  let n_1 = n;
  let N_1 = N;
  let x_clone = Rc::clone(x);
  let callback: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new({
    move |t: u64, a: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let x = &x_clone;
      let i = &i;
      let tmp = rocq_array::get::<u64>(x, t);
      let i_clone = Clone::clone(i);
      rocq_array::set::<f64>(a, t, limb(tmp, i_clone))
    }
  });
  let tmp_1 = rocq_array::make::<f64>(N_1, f64::from_bits(0u64));
  loop_::<Rc<Array<f64>>>(n_1, callback, 0u64, tmp_1)
}

// Rocq: Polymul2.polymul2_implem.copy_out
// Variant: uncurried
pub fn copy_out(N: u64, off: u64, yr: Rc<Array<f64>>, yi: Rc<Array<f64>>, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
    move |k: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let yr = &yr;
      let off = &off;
      let yi = &yi;
      match st {
        (v22, v24) => {
          let tmp = rocq_array::set::<f64>(v22, add(Clone::clone(off), k), rocq_array::get::<f64>(yr, k));
          let tmp_1 = add(Clone::clone(off), k);
          let tmp_2 = rocq_array::get::<f64>(yi, k);
          let tmp_3 = rocq_array::set::<f64>(v24, tmp_1, tmp_2);
          (tmp, tmp_3)
        },
      }
    }
  });
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(N, callback, 0u64, st)
}

// Rocq: Polymul2.polymul2_implem.fwd_all
// Variant: uncurried
pub fn fwd_all(x: Rc<Array<u64>>, n: u64, lg: u64, half: u64, tre: Rc<Array<f64>>, tim: Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let N = add(half, half);
  let tmp = __rocq_global_546;
  let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
    let __anf_capture_35 = half;
    let __anf_capture_41 = N;
    move |i: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let x = &x;
      let n = &n;
      let lg = &lg;
      let half = &__anf_capture_35;
      let tre = &tre;
      let tim = &tim;
      let N = &__anf_capture_41;
      let tmp_1 = load(x, Clone::clone(n), Clone::clone(N), i);
      let tmp_2 = f64::from_bits(0u64);
      let tmp_3 = rocq_array::make::<f64>(Clone::clone(N), tmp_2);
      let lg_clone = Clone::clone(lg);
      let half_clone = Clone::clone(half);
      let tre_clone = Rc::clone(tre);
      let tim_clone = Rc::clone(tim);
      let tmp_4 = fft(lg_clone, half_clone, false, tre_clone, tim_clone, tmp_1, tmp_3);
      match tmp_4 {
        (v80, v82) => {
          let tmp_5 = mul_1(i, Clone::clone(N));
          let N_clone = Clone::clone(N);
          copy_out(N_clone, tmp_5, v80, v82, st)
        },
      }
    }
  });
  let tmp_6 = rocq_array::make::<f64>(mul_1(__rocq_global_546, N), f64::from_bits(0u64));
  let tmp_7 = rocq_array::make::<f64>(mul_1(__rocq_global_546, N), f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(tmp, callback, 0u64, (tmp_6, tmp_7))
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
      let tmp = add_1(v6, sub_1(mul(ar, br), mul(ai, bi)));
      let tmp_1 = add_1(mul(ar, bi), mul(ai, br));
      (tmp, add_1(v8, tmp_1))
    },
  }
}

// Rocq: Polymul2.polymul2_implem.pterm
// Variant: borrowed, uncurried
pub fn pterm(w: u64, N: u64, k: u64, AR: &Rc<Array<f64>>, AI: &Rc<Array<f64>>, BR: &Rc<Array<f64>>, BI: &Rc<Array<f64>>, i: u64, st: (f64, f64)) -> (f64, f64) {
  let w_1 = w;
  let N_1 = N;
  let k_1 = k;
  let i_1 = i;
  let st_1 = st;
  let tmp = leb(i_1, w_1);
  let tmp_1 = ltb(sub(w_1, i_1), __rocq_global_546);
  if andb(tmp, tmp_1) {
    cacc(rocq_array::get::<f64>(AR, add(mul_1(i_1, N_1), k_1)), rocq_array::get::<f64>(AI, add(mul_1(i_1, N_1), k_1)), rocq_array::get::<f64>(BR, add(mul_1(sub(w_1, i_1), N_1), k_1)), rocq_array::get::<f64>(BI, add(mul_1(sub(w_1, i_1), N_1), k_1)), st_1)
  } else {
    st_1
  }
}

// Rocq: Polymul2.polymul2_implem.pcell
// Variant: borrowed, uncurried
pub fn pcell(g: u64, N: u64, AR: &Rc<Array<f64>>, AI: &Rc<Array<f64>>, BR: &Rc<Array<f64>>, BI: &Rc<Array<f64>>, k: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let g_1 = g;
  let N_1 = N;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v13, v15) => {
      let tmp = __rocq_global_546;
      let tmp_1 = add(g_1, g_1);
      let AR_clone = Rc::clone(AR);
      let AI_clone = Rc::clone(AI);
      let BR_clone = Rc::clone(BR);
      let BI_clone = Rc::clone(BI);
      let callback: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new({
        let __anf_capture_46 = N_1;
        let __anf_capture_48 = k_1;
        move |v58: u64, v59: (f64, f64)| -> (f64, f64) {
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
      let tmp_3 = loop_::<(f64, f64)>(tmp, callback, 0u64, (f64::from_bits(0u64), f64::from_bits(0u64)));
      match tmp_3 {
        (v102, v104) => {
          let tmp_4 = __rocq_global_546;
          let tmp_5 = add(g_1, g_1);
          let tmp_6 = add(tmp_5, 1u64);
          let AR_clone_1 = Rc::clone(AR);
          let AI_clone_1 = Rc::clone(AI);
          let BR_clone_1 = Rc::clone(BR);
          let BI_clone_1 = Rc::clone(BI);
          let callback_1: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new({
            let __anf_capture_143 = N_1;
            let __anf_capture_145 = k_1;
            move |v155: u64, v156: (f64, f64)| -> (f64, f64) {
              let v141 = &tmp_6;
              let N = &__anf_capture_143;
              let k = &__anf_capture_145;
              let AR = &AR_clone_1;
              let AI = &AI_clone_1;
              let BR = &BR_clone_1;
              let BI = &BI_clone_1;
              let tmp_7 = pterm(Clone::clone(v141), Clone::clone(N), Clone::clone(k), AR, AI, BR, BI, v155, v156);
              tmp_7
            }
          });
          let tmp_8 = loop_::<(f64, f64)>(tmp_4, callback_1, 0u64, (f64::from_bits(0u64), f64::from_bits(0u64)));
          match tmp_8 {
            (v199, v201) => {
              let tmp_9 = rocq_array::set::<f64>(v13, k_1, sub_1(v102, v201));
              let tmp_10 = rocq_array::set::<f64>(v15, k_1, add_1(v104, v199));
              (tmp_9, tmp_10)
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.products
// Variant: borrowed, uncurried
pub fn products(g: u64, N: u64, AR: &Rc<Array<f64>>, AI: &Rc<Array<f64>>, BR: &Rc<Array<f64>>, BI: &Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let AR_clone = Rc::clone(AR);
  let AI_clone = Rc::clone(AI);
  let BR_clone = Rc::clone(BR);
  let BI_clone = Rc::clone(BI);
  let callback: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new({
    let __anf_capture_28 = N;
    move |v38: u64, v39: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
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
  let tmp_1 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tmp_2 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(N, callback, 0u64, (tmp_1, tmp_2))
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp$rust_exponent$uncurry$0
pub fn frshiftexp_rust_exponent_uncurry_0(v0: f64) -> u64 {
  rocq_float64::frshiftexp_exponent(v0)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp$rust_fraction$uncurry$0
pub fn frshiftexp_rust_fraction_uncurry_0(v0: f64) -> f64 {
  rocq_float64::frshiftexp_fraction(v0)
}

// Rocq: Corelib.Floats.PrimFloat.frshiftexp
pub fn frshiftexp(x: f64) -> (f64, u64) {
  (frshiftexp_rust_fraction_uncurry_0(x), frshiftexp_rust_exponent_uncurry_0(x))
}

// Rocq: Corelib.Floats.PrimFloat.normfr_mantissa
pub fn normfr_mantissa(v0: f64) -> u64 {
  rocq_float64::normfr_mantissa(v0)
}

// Rocq: Polymul2.polymul2_implem.toint
pub fn toint(z: f64) -> u64 {
  let tmp = frshiftexp(add_1(z, __rocq_global_1162));
  match tmp {
    (v13, _v15) => {
      sub(normfr_mantissa(v13), __rocq_global_1171)
    },
  }
}

// Rocq: Polymul2.polymul2_implem.accum
// Variant: uncurried
pub fn accum(g: u64, L: u64, invN: f64, yr: Rc<Array<f64>>, yi: Rc<Array<f64>>, R: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |q: u64, R: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let yr = &yr;
      let yi = &yi;
      let invN = &invN;
      let g = &g;
      let d0 = toint(mul(rocq_array::get::<f64>(yr, q), Clone::clone(invN)));
      let d1 = toint(mul(rocq_array::get::<f64>(yi, q), Clone::clone(invN)));
      let tmp = rocq_array::get::<u64>(&R, q);
      let tmp_1 = add(tmp, lsl(d0, mul_1(12u64, Clone::clone(g))));
      let g_clone = Clone::clone(g);
      let tmp_2 = add(mul_1(12u64, g_clone), 6u64);
      rocq_array::set::<u64>(R, q, add(tmp_1, lsl(d1, tmp_2)))
    }
  });
  loop_::<Rc<Array<u64>>>(L, callback, 0u64, R)
}

// Rocq: Polymul2.polymul2_implem.polymul_impl
// Variant: uncurried
pub fn polymul_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let na = rocq_array::length::<u64>(&x);
  let nb = rocq_array::length::<u64>(&y);
  let L = sub(add(na, nb), 1u64);
  let lg = log2up(L);
  let half = lsl(1u64, sub(lg, 1u64));
  let N = add(half, half);
  let tmp = build_tw(lg, N);
  match tmp {
    (v53, v55) => {
      let tim = &v53;
      let tre = &v55;
      let tim_clone = Rc::clone(tim);
      let tre_clone = Rc::clone(tre);
      let tmp_1 = fwd_all(x, na, lg, half, tim_clone, tre_clone);
      match tmp_1 {
        (v74, v76) => {
          let tim_clone_1 = Rc::clone(tim);
          let tre_clone_1 = Rc::clone(tre);
          let tmp_2 = fwd_all(y, nb, lg, half, tim_clone_1, tre_clone_1);
          match tmp_2 {
            (v93, v95) => {
              let invN = div(f64::from_bits(4607182418800017408u64), of_uint63(N));
              let tmp_3 = __rocq_global_546;
              let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
                let __anf_capture_134 = N;
                let __anf_capture_144 = lg;
                let __anf_capture_146 = half;
                let __anf_capture_148 = v53;
                let __anf_capture_150 = v55;
                let __anf_capture_152 = L;
                move |g: u64, R: Rc<Array<u64>>| -> Rc<Array<u64>> {
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
                      let tim_clone_2 = Rc::clone(tim);
                      let tre_clone_2 = Rc::clone(tre);
                      let pim_clone = Rc::clone(pim);
                      let pr_clone = Rc::clone(pr);
                      std::mem::drop(tmp_4);
                      let tmp_5 = fft(lg_clone, half_clone, true, tim_clone_2, tre_clone_2, pim_clone, pr_clone);
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
              let tmp_6 = rocq_array::make::<u64>(L, 0u64);
              loop_::<Rc<Array<u64>>>(tmp_3, callback, 0u64, tmp_6)
            },
          }
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
const __rocq_global_546: u64 = 6u64;
const __rocq_global_760: u64 = 34905131040u64;
const __rocq_global_1162: f64 = f64::from_bits(4843621399236968448u64);
const __rocq_global_1171: u64 = 6755399441055744u64;