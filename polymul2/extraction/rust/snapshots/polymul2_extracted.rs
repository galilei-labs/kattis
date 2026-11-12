// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Polymul2.polymul2_implem.polymul
// Variant: uncurried
pub fn polymul() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = polymul_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Polymul2.polymul2_implem.polymul
pub fn polymul_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = polymul_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v0);
  v1
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
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
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
  let v12 = ltb(k, 62u64);
  match bdec(v12) {
    sumbool::left => {
      let v24 = lsl(1u64, k);
      match leb(L, v24) {
        true => {
          k
        },
        false => {
          lg_find(L, add(k, 1u64), ())
        },
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
  let v12 = ltb(i, hi);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24: &Rc<dyn Fn(u64, St) -> St> = &f;
      let v29 = v24(i, s);
      wloop::<St>(hi, f, v23, v29, ())
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
      let ar = rocq_array::get::<f64>(&tim, src);
      let ai = rocq_array::get::<f64>(&tre, src);
      let v41 = land(k, 1u64);
      match eqb(v41, 0u64) {
        true => {
          let v62 = rocq_array::set::<f64>(v7, add(m, k), ar);
          let v75 = rocq_array::set::<f64>(v9, add(m, k), ai);
          (v62, v75)
        },
        false => {
          let v114 = rocq_array::set::<f64>(v7, add(m, k), sub_1(mul(ar, bc), mul(ai, bs)));
          let v145 = rocq_array::set::<f64>(v9, add(m, k), add_1(mul(ar, bs), mul(ai, bc)));
          (v114, v145)
        },
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
              let v41 = lsl(1u64, sub(s, 1u64));
              let v50 = {
                let __anf_capture_51 = m;
                let __anf_capture_55 = v10;
                let __anf_capture_57 = v5;
                move |v59: u64, v60: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
                  let v63 = Clone::clone(&__anf_capture_51);
                  let v65 = Clone::clone(&v41);
                  let v67 = Clone::clone(&__anf_capture_55);
                  let v69 = Clone::clone(&__anf_capture_57);
                  tw_cell(v63, v65, v67, v69, v59, v60)
                }
              };
              let v77: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v50);
              let v95 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(m, v77, 0u64, (v13, v15));
              match v95 {
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
  let v8 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let tre = rocq_array::set::<f64>(v8, 1u64, f64::from_bits(4607182418800017408u64));
  let tim = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let v28: fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64) = tw_stage;
  let v29: Rc<dyn Fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)> = Rc::new(v28);
  let v63 = loop_::<(((Rc<Array<f64>>, Rc<Array<f64>>), f64), f64)>(lg, v29, 1u64, (((tre, tim), f64::from_bits(0u64)), f64::from_bits(4607182418800017408u64)));
  match v63 {
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
      let v60 = add(m_1, q);
      let v61 = tre;
      let wr = rocq_array::get::<f64>(&v61, v60);
      let wi = match neg_1 {
        true => {
          let v72 = add(m_1, q);
          let v73 = tim;
          opp(rocq_array::get::<f64>(&v73, v72))
        },
        false => {
          let v87 = add(m_1, q);
          let v88 = tim;
          rocq_array::get::<f64>(&v88, v87)
        },
      };
      let v95 = sre;
      let ur = rocq_array::get::<f64>(&v95, i1);
      let v99 = sim;
      let ui = rocq_array::get::<f64>(&v99, i1);
      let v103 = sre;
      let vr = rocq_array::get::<f64>(&v103, i2);
      let v107 = sim;
      let vi = rocq_array::get::<f64>(&v107, i2);
      let tr = sub_1(mul(wr, vr), mul(wi, vi));
      let ti = add_1(mul(wr, vi), mul(wi, vr));
      let v152 = add_1(ur, tr);
      let v153 = Rc::clone(dim);
      std::mem::drop(v17);
      let v159 = rocq_array::set::<f64>(v153, j_1, v152);
      let v178 = rocq_array::set::<f64>(v159, add(j_1, half_1), sub_1(ur, tr));
      let v184 = add_1(ui, ti);
      let v185 = Rc::clone(dre);
      std::mem::drop(v19);
      let v191 = rocq_array::set::<f64>(v185, j_1, v184);
      let v210 = rocq_array::set::<f64>(v191, add(j_1, half_1), sub_1(ui, ti));
      (v178, v210)
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
              let v39 = sub(lg_1, 1u64);
              let v43 = sub(v39, s_1);
              let v51 = lsl(1u64, s_1);
              let v61 = Rc::clone(sim);
              let v63 = Rc::clone(sre);
              let v66 = Rc::clone(tre);
              let v69 = Rc::clone(tim);
              let v70 = {
                let __anf_capture_75 = half_1;
                move |v87: u64, v88: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
                  let v71 = &v43;
                  let v73 = &v51;
                  let half = &__anf_capture_75;
                  let neg = &neg_1;
                  let sim = &v61;
                  let sre = &v63;
                  let tre = &v66;
                  let tim = &v69;
                  let v106 = bfly(Clone::clone(v71), Clone::clone(v73), Clone::clone(half), Clone::clone(neg), sim, sre, tre, tim, v87, v88);
                  v106
                }
              };
              let v109: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v70);
              let v127 = loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(half_1, v109, 0u64, (v20, v15));
              match v127 {
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
  let v24 = {
    let __anf_capture_25 = lg;
    let __anf_capture_27 = half;
    move |v35: u64, v36: (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)| -> (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>) {
      let lg = &__anf_capture_25;
      let half = &__anf_capture_27;
      let neg = &neg;
      let tre = &tre;
      let tim = &tim;
      let v50 = fft_stage(Clone::clone(lg), Clone::clone(half), Clone::clone(neg), tre, tim, v35, v36);
      v50
    }
  };
  let v53: Rc<dyn Fn(u64, (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)) -> (((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)> = Rc::new(v24);
  let v61 = (re, im);
  let v69 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let v74 = (v61, v69);
  let v82 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let v97 = loop_::<(((Rc<Array<f64>>, Rc<Array<f64>>), Rc<Array<f64>>), Rc<Array<f64>>)>(lg, v53, 0u64, (v74, v82));
  match v97 {
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
  let v10 = Rc::clone(x);
  let v13 = {
    move |t: u64, a: Rc<Array<f64>>| -> Rc<Array<f64>> {
      let x = &v10;
      let i = &i;
      let v24 = rocq_array::get::<u64>(&x, t);
      let v27 = Clone::clone(i);
      rocq_array::set::<f64>(a, t, limb(v24, v27))
    }
  };
  let v38: Rc<dyn Fn(u64, Rc<Array<f64>>) -> Rc<Array<f64>>> = Rc::new(v13);
  let v48 = rocq_array::make::<f64>(N_1, f64::from_bits(0u64));
  loop_::<Rc<Array<f64>>>(n_1, v38, 0u64, v48)
}

// Rocq: Polymul2.polymul2_implem.copy_out
// Variant: uncurried
pub fn copy_out(N: u64, off: u64, yr: Rc<Array<f64>>, yi: Rc<Array<f64>>, st: (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let v12 = {
    move |k: u64, st: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let yr = &yr;
      let off = &off;
      let yi = &yi;
      match st {
        (v22, v24) => {
          let v41 = rocq_array::set::<f64>(v22, add(Clone::clone(off), k), rocq_array::get::<f64>(&yr, k));
          let v47 = add(Clone::clone(off), k);
          let v50 = rocq_array::get::<f64>(&yi, k);
          let v57 = rocq_array::set::<f64>(v24, v47, v50);
          (v41, v57)
        },
      }
    }
  };
  let v69: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v12);
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(N, v69, 0u64, st)
}

// Rocq: Polymul2.polymul2_implem.fwd_all
// Variant: uncurried
pub fn fwd_all(x: Rc<Array<u64>>, n: u64, lg: u64, half: u64, tre: Rc<Array<f64>>, tim: Rc<Array<f64>>) -> (Rc<Array<f64>>, Rc<Array<f64>>) {
  let N = add(half, half);
  let v13 = __rocq_global_546;
  let v28 = {
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
      let v56 = load(x, Clone::clone(n), Clone::clone(N), i);
      let v58 = f64::from_bits(0u64);
      let v63 = rocq_array::make::<f64>(Clone::clone(N), v58);
      let v65 = Clone::clone(lg);
      let v67 = Clone::clone(half);
      let v71 = Rc::clone(tre);
      let v73 = Rc::clone(tim);
      let v78 = fft(v65, v67, false, v71, v73, v56, v63);
      match v78 {
        (v80, v82) => {
          let v90 = mul_1(i, Clone::clone(N));
          let v92 = Clone::clone(N);
          copy_out(v92, v90, v80, v82, st)
        },
      }
    }
  };
  let v107: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v28);
  let v124 = rocq_array::make::<f64>(mul_1(__rocq_global_546, N), f64::from_bits(0u64));
  let v138 = rocq_array::make::<f64>(mul_1(__rocq_global_546, N), f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(v13, v107, 0u64, (v124, v138))
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Polymul2.polymul2_implem.cacc
// Variant: uncurried
pub fn cacc(ar: f64, ai: f64, br: f64, bi: f64, st: (f64, f64)) -> (f64, f64) {
  match st {
    (v6, v8) => {
      let v33 = add_1(v6, sub_1(mul(ar, br), mul(ai, bi)));
      let v52 = add_1(mul(ar, bi), mul(ai, br));
      (v33, add_1(v8, v52))
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
  let v20 = leb(i_1, w_1);
  let v33 = ltb(sub(w_1, i_1), __rocq_global_546);
  match andb(v20, v33) {
    true => {
      let v52 = add(mul_1(i_1, N_1), k_1);
      let v53 = AR;
      let v56 = rocq_array::get::<f64>(&v53, v52);
      let v68 = add(mul_1(i_1, N_1), k_1);
      let v69 = AI;
      let v72 = rocq_array::get::<f64>(&v69, v68);
      let v90 = add(mul_1(sub(w_1, i_1), N_1), k_1);
      let v91 = BR;
      let v94 = rocq_array::get::<f64>(&v91, v90);
      let v112 = add(mul_1(sub(w_1, i_1), N_1), k_1);
      let v113 = BI;
      cacc(v56, v72, v94, rocq_array::get::<f64>(&v113, v112), st_1)
    },
    false => {
      st_1
    },
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
      let v18 = __rocq_global_546;
      let v25 = add(g_1, g_1);
      let v33 = Rc::clone(AR);
      let v36 = Rc::clone(AI);
      let v39 = Rc::clone(BR);
      let v42 = Rc::clone(BI);
      let v43 = {
        let __anf_capture_46 = N_1;
        let __anf_capture_48 = k_1;
        move |v58: u64, v59: (f64, f64)| -> (f64, f64) {
          let v44 = &v25;
          let N = &__anf_capture_46;
          let k = &__anf_capture_48;
          let AR = &v33;
          let AI = &v36;
          let BR = &v39;
          let BI = &v42;
          let v75 = pterm(Clone::clone(v44), Clone::clone(N), Clone::clone(k), AR, AI, BR, BI, v58, v59);
          v75
        }
      };
      let v78: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new(v43);
      let v100 = loop_::<(f64, f64)>(v18, v78, 0u64, (f64::from_bits(0u64), f64::from_bits(0u64)));
      match v100 {
        (v102, v104) => {
          let v107 = __rocq_global_546;
          let v114 = add(g_1, g_1);
          let v122 = add(v114, 1u64);
          let v130 = Rc::clone(AR);
          let v133 = Rc::clone(AI);
          let v136 = Rc::clone(BR);
          let v139 = Rc::clone(BI);
          let v140 = {
            let __anf_capture_143 = N_1;
            let __anf_capture_145 = k_1;
            move |v155: u64, v156: (f64, f64)| -> (f64, f64) {
              let v141 = &v122;
              let N = &__anf_capture_143;
              let k = &__anf_capture_145;
              let AR = &v130;
              let AI = &v133;
              let BR = &v136;
              let BI = &v139;
              let v172 = pterm(Clone::clone(v141), Clone::clone(N), Clone::clone(k), AR, AI, BR, BI, v155, v156);
              v172
            }
          };
          let v175: Rc<dyn Fn(u64, (f64, f64)) -> (f64, f64)> = Rc::new(v140);
          let v197 = loop_::<(f64, f64)>(v107, v175, 0u64, (f64::from_bits(0u64), f64::from_bits(0u64)));
          match v197 {
            (v199, v201) => {
              let v215 = rocq_array::set::<f64>(v13, k_1, sub_1(v102, v201));
              let v228 = rocq_array::set::<f64>(v15, k_1, add_1(v104, v199));
              (v215, v228)
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
  let v15 = Rc::clone(AR);
  let v18 = Rc::clone(AI);
  let v21 = Rc::clone(BR);
  let v24 = Rc::clone(BI);
  let v25 = {
    let __anf_capture_28 = N;
    move |v38: u64, v39: (Rc<Array<f64>>, Rc<Array<f64>>)| -> (Rc<Array<f64>>, Rc<Array<f64>>) {
      let g = &g;
      let N = &__anf_capture_28;
      let AR = &v15;
      let AI = &v18;
      let BR = &v21;
      let BI = &v24;
      let v53 = pcell(Clone::clone(g), Clone::clone(N), AR, AI, BR, BI, v38, v39);
      v53
    }
  };
  let v56: Rc<dyn Fn(u64, (Rc<Array<f64>>, Rc<Array<f64>>)) -> (Rc<Array<f64>>, Rc<Array<f64>>)> = Rc::new(v25);
  let v66 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  let v73 = rocq_array::make::<f64>(N, f64::from_bits(0u64));
  loop_::<(Rc<Array<f64>>, Rc<Array<f64>>)>(N, v56, 0u64, (v66, v73))
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
  let v11 = frshiftexp(add_1(z, __rocq_global_1162));
  match v11 {
    (v13, _v15) => {
      sub(normfr_mantissa(v13), __rocq_global_1171)
    },
  }
}

// Rocq: Polymul2.polymul2_implem.accum
// Variant: uncurried
pub fn accum(g: u64, L: u64, invN: f64, yr: Rc<Array<f64>>, yi: Rc<Array<f64>>, R: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v15 = {
    move |q: u64, R: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let yr = &yr;
      let yi = &yi;
      let invN = &invN;
      let g = &g;
      let d0 = toint(mul(rocq_array::get::<f64>(&yr, q), Clone::clone(invN)));
      let d1 = toint(mul(rocq_array::get::<f64>(&yi, q), Clone::clone(invN)));
      let v54 = &R;
      let v57 = rocq_array::get::<u64>(&v54, q);
      let v76 = add(v57, lsl(d0, mul_1(12u64, Clone::clone(g))));
      let v85 = Clone::clone(g);
      let v93 = add(mul_1(12u64, v85), 6u64);
      rocq_array::set::<u64>(R, q, add(v76, lsl(d1, v93)))
    }
  };
  let v113: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v15);
  loop_::<Rc<Array<u64>>>(L, v113, 0u64, R)
}

// Rocq: Polymul2.polymul2_implem.polymul_impl
// Variant: uncurried
pub fn polymul_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v2 = &x;
  let na = rocq_array::length::<u64>(&v2);
  let v4 = &y;
  let nb = rocq_array::length::<u64>(&v4);
  let L = sub(add(na, nb), 1u64);
  let lg = log2up(L);
  let half = lsl(1u64, sub(lg, 1u64));
  let N = add(half, half);
  let v51 = build_tw(lg, N);
  match v51 {
    (v53, v55) => {
      let tim = &v53;
      let tre = &v55;
      let v69 = Rc::clone(tim);
      let v71 = Rc::clone(tre);
      let v72 = fwd_all(x, na, lg, half, v69, v71);
      match v72 {
        (v74, v76) => {
          let v88 = Rc::clone(tim);
          let v90 = Rc::clone(tre);
          let v91 = fwd_all(y, nb, lg, half, v88, v90);
          match v91 {
            (v93, v95) => {
              let invN = div(f64::from_bits(4607182418800017408u64), of_uint63(N));
              let v110 = __rocq_global_546;
              let v133 = {
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
                  let v167 = products(g, Clone::clone(N), AI, AR, BI, BR);
                  match &v167 {
                    (pim, pr) => {
                      let v178 = Clone::clone(lg);
                      let v180 = Clone::clone(half);
                      let v184 = Rc::clone(tim);
                      let v186 = Rc::clone(tre);
                      let v188 = Rc::clone(pim);
                      let v189 = Rc::clone(pr);
                      std::mem::drop(v167);
                      let v191 = fft(v178, v180, true, v184, v186, v188, v189);
                      match v191 {
                        (v193, v195) => {
                          let v201 = Clone::clone(L);
                          let v203 = Clone::clone(invN);
                          accum(g, v201, v203, v193, v195, R)
                        },
                      }
                    },
                  }
                }
              };
              let v219: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v133);
              let v229 = rocq_array::make::<u64>(L, 0u64);
              loop_::<Rc<Array<u64>>>(v110, v219, 0u64, v229)
            },
          }
        },
      }
    },
  }
}

// Rocq: Polymul2.polymul2_implem.polymul_impl
pub fn polymul_impl_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&x);
      polymul_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_1313.with(Clone::clone);
  v0
}
const __rocq_global_546: u64 = 6u64;
const __rocq_global_760: u64 = 34905131040u64;
const __rocq_global_1162: f64 = f64::from_bits(4843621399236968448u64);
const __rocq_global_1171: u64 = 6755399441055744u64;
std::thread_local! { static __rocq_global_1313: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = polymul(); }
std::thread_local! { static __rocq_global_1316: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = polymul_curried(); }