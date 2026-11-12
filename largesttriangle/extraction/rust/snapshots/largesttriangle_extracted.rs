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

pub type uint = u64;

// Rocq: Largesttriangle.largesttriangle_implem.SH
pub fn SH() -> u64 {
  67108864u64
}

// Rocq: Largesttriangle.largesttriangle_implem.OFF
pub fn OFF() -> u64 {
  1152921504606846976u64
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle
// Variant: uncurried
pub fn largest_triangle() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64 = largest_triangle_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = Rc::new(v0);
  v1
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle
pub fn largest_triangle_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64> = largest_triangle_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> = Rc::new(v0);
  v1
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

// Rocq: Largesttriangle.largesttriangle_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Largesttriangle.largesttriangle_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.wloop (local: wloop)
// Variant: uncurried, lifted
pub fn wloop<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St, _H: ()) -> St {
  let v13 = ltb(i, hi);
  match bdec(v13) {
    sumbool::left => {
      let v17: &Rc<dyn Fn(u64, St) -> bool> = &cont;
      let v21 = Clone::clone(&s);
      let v23 = v17(i, v21);
      match v23 {
        true => {
          let v32 = add(i, 1u64);
          let v33: &Rc<dyn Fn(u64, St) -> St> = &f;
          let v38 = v33(i, s);
          wloop::<St>(hi, cont, f, v32, v38, ())
        },
        false => {
          std::mem::drop(f);
          std::mem::drop(cont);
          s
        },
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
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Largesttriangle.largesttriangle_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(A: &Rc<Array<u64>>, mid: u64, hi: u64, k: u64, st: ((Rc<Array<u64>>, u64), u64)) -> ((Rc<Array<u64>>, u64), u64) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let v25 = ltb(v17, mid_1);
          let v32 = leb(hi_1, v12);
          let v34 = A;
          let v37 = rocq_array::get::<u64>(&v34, v17);
          let v38 = A;
          let v51 = orb(v32, leb(v37, rocq_array::get::<u64>(&v38, v12)));
          match andb(v25, v51) {
            true => {
              let v58 = A;
              let v68 = rocq_array::set::<u64>(v15, k_1, rocq_array::get::<u64>(&v58, v17));
              ((v68, add(v17, 1u64)), v12)
            },
            false => {
              let v91 = A;
              let v102 = rocq_array::set::<u64>(v15, k_1, rocq_array::get::<u64>(&v91, v12));
              ((v102, v17), add(v12, 1u64))
            },
          }
        },
      }
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.merge
// Variant: uncurried
pub fn merge(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64) -> Rc<Array<u64>> {
  let v6 = {
    move |_v7: u64, v8: ((Rc<Array<u64>>, u64), u64)| -> bool {
      std::mem::drop(v8);
      true
    }
  };
  let v13: Rc<dyn Fn(u64, ((Rc<Array<u64>>, u64), u64)) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, ((Rc<Array<u64>>, u64), u64)) -> bool> = v13;
  let v21 = {
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: u64, v29: ((Rc<Array<u64>>, u64), u64)| -> ((Rc<Array<u64>>, u64), u64) {
      let A = &A;
      let v40 = merge_step(A, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      v40
    }
  };
  let v43: Rc<dyn Fn(u64, ((Rc<Array<u64>>, u64), u64)) -> ((Rc<Array<u64>>, u64), u64)> = Rc::new(v21);
  let v49 = (T, lo);
  let v67 = loop_::<((Rc<Array<u64>>, u64), u64)>(hi, v14, v43, lo, (v49, mid));
  match v67 {
    (v69, _v71) => {
      let i = &v69;
      let v75 = Rc::clone((&(i).0));
      std::mem::drop(v69);
      v75
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.copy_step
// Variant: uncurried
pub fn copy_step(T: Rc<Array<u64>>, k: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v3 = &T;
  let v6 = rocq_array::get::<u64>(&v3, k);
  std::mem::drop(T);
  rocq_array::set::<u64>(A, k, v6)
}

// Rocq: Largesttriangle.largesttriangle_implem.msort
// Variant: uncurried
pub fn msort_1(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(A, T, lo, hi, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v32 = andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)));
  match bdec(v32) {
    sumbool::left => {
      let v43 = sub(hi, lo);
      let mid = add(lo, div(v43, 2u64));
      let v69 = msort(A, T, lo, mid, ());
      match &v69 {
        (T1, A1) => {
          let v77 = ();
          let v80 = Rc::clone(T1);
          let v81 = Rc::clone(A1);
          std::mem::drop(v69);
          let v89 = msort(v80, v81, mid, hi, v77);
          match v89 {
            (v91, v93) => {
              let T2 = &v91;
              let v98 = Rc::clone(T2);
              let T3 = merge(v98, v93, lo, mid, hi);
              let v109 = {
                move |_v110: u64, v111: Rc<Array<u64>>| -> bool {
                  std::mem::drop(v111);
                  true
                }
              };
              let v116: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v109);
              let v117: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v116;
              let v120 = Rc::clone(&T3);
              let v121 = {
                move |v124: u64, v125: Rc<Array<u64>>| -> Rc<Array<u64>> {
                  let v128 = Rc::clone(&v120);
                  copy_step(v128, v124, v125)
                }
              };
              let v136: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v121);
              let v149 = loop_::<Rc<Array<u64>>>(hi, v117, v136, lo, v91);
              (v149, T3)
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
pub fn sort(K: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let v10 = rocq_array::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(K, v10, 0u64, n))
}

// Rocq: Largesttriangle.largesttriangle_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(S: &Rc<Array<u64>>, t: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let v19 = eqb(v8, 0u64);
      let v29 = sub(v8, 1u64);
      let v31 = rocq_array::get::<u64>(&m, v29);
      let v32 = S;
      let v40 = ltb(v31, rocq_array::get::<u64>(&v32, t_1));
      match orb(v19, v40) {
        true => {
          let v47 = S;
          let v57 = rocq_array::set::<u64>(v6, v8, rocq_array::get::<u64>(&v47, t_1));
          (v57, add(v8, 1u64))
        },
        false => {
          (v6, v8)
        },
      }
    },
  }
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
}

// Rocq: Largesttriangle.largesttriangle_implem.fzero
pub fn fzero(_v0: ()) -> f64 {
  of_uint63(0u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Largesttriangle.largesttriangle_implem.decode_step
// Variant: borrowed, uncurried
pub fn decode_step(D: &Rc<Array<u64>>, u: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let u_1 = u;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let v10 = D;
      let d = rocq_array::get::<u64>(&v10, u_1);
      let v27 = rocq_array::set::<u64>(v6, u_1, div(d, __rocq_global_274));
      let v41 = rocq_array::set::<u64>(v8, u_1, mod_(d, __rocq_global_274));
      (v27, v41)
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.crs
// Variant: uncurried
pub fn crs(ax: u64, ay: u64, bx: u64, by_: u64, cx: u64, cy: u64) -> u64 {
  let v25 = mul(sub(bx, ax), sub(cy, ay));
  let v32 = sub(cx, ax);
  let v38 = sub(by_, ay);
  add(sub(v25, mul(v32, v38)), __rocq_global_625)
}

// Rocq: Largesttriangle.largesttriangle_implem.popl
// Variant: uncurried
pub fn popl_1(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, ST: Rc<Array<u64>>, s: u64, r: u64) -> u64 {
  popl(X, Y, ST, s, r, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.popl (local: popl)
// Variant: uncurried, lifted
pub fn popl(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, ST: Rc<Array<u64>>, s: u64, r: u64, _H: ()) -> u64 {
  let v15 = ltb(1u64, r);
  match bdec(v15) {
    sumbool::left => {
      let v26 = sub(r, 2u64);
      let v27 = &ST;
      let i1 = rocq_array::get::<u64>(&v27, v26);
      let v38 = sub(r, 1u64);
      let v39 = &ST;
      let i2 = rocq_array::get::<u64>(&v39, v38);
      let v45 = &X;
      let v48 = rocq_array::get::<u64>(&v45, i1);
      let v49 = &Y;
      let v52 = rocq_array::get::<u64>(&v49, i1);
      let v53 = &X;
      let v56 = rocq_array::get::<u64>(&v53, i2);
      let v57 = &Y;
      let v60 = rocq_array::get::<u64>(&v57, i2);
      let v61 = &X;
      let v64 = rocq_array::get::<u64>(&v61, s);
      let v65 = &Y;
      let v68 = rocq_array::get::<u64>(&v65, s);
      let v81 = crs(v48, v52, v56, v60, v64, v68);
      match leb(v81, __rocq_global_625) {
        true => {
          popl(X, Y, ST, s, sub(r, 1u64), ())
        },
        false => {
          std::mem::drop(X);
          std::mem::drop(Y);
          std::mem::drop(ST);
          r
        },
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
pub fn pass_step(X: &Rc<Array<u64>>, Y: &Rc<Array<u64>>, s: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let s_1 = s;
  let st_1 = st;
  match st_1 {
    (v7, v9) => {
      let r = &v7;
      let v15 = Rc::clone(X);
      let v18 = Rc::clone(Y);
      let v20 = Rc::clone(r);
      let r_ = popl_1(v15, v18, v20, s_1, v9);
      let v32 = rocq_array::set::<u64>(v7, r_, s_1);
      (v32, add(r_, 1u64))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: uncurried
pub fn pass_owned(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let v4 = {
    move |_v5: u64, v6: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v11;
  let v17 = {
    move |v22: u64, v23: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let X = &X;
      let Y = &Y;
      let v31 = pass_step(X, Y, v22, v23);
      v31
    }
  };
  let v34: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v17);
  let v44 = rocq_array::make::<u64>(m, 0u64);
  loop_::<(Rc<Array<u64>>, u64)>(m, v12, v34, 1u64, (v44, 1u64))
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: borrowed, uncurried
pub fn pass(X: &Rc<Array<u64>>, Y: &Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let m_1 = m;
  let v5 = {
    move |_v6: u64, v7: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v12;
  let v16 = Rc::clone(X);
  let v19 = Rc::clone(Y);
  let v20 = {
    move |v25: u64, v26: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let X = &v16;
      let Y = &v19;
      let v34 = pass_step(X, Y, v25, v26);
      v34
    }
  };
  let v37: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v20);
  let v47 = rocq_array::make::<u64>(m_1, 0u64);
  loop_::<(Rc<Array<u64>>, u64)>(m_1, v13, v37, 1u64, (v47, 1u64))
}

// Rocq: Largesttriangle.largesttriangle_implem.rev_step
// Variant: uncurried
pub fn rev_step(X: Rc<Array<u64>>, m: u64, s: u64, R: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v13 = sub(m, 1u64);
  let v17 = sub(v13, s);
  let v18 = &X;
  let v21 = rocq_array::get::<u64>(&v18, v17);
  std::mem::drop(X);
  rocq_array::set::<u64>(R, s, v21)
}

// Rocq: Largesttriangle.largesttriangle_implem.low_step
// Variant: borrowed, uncurried
pub fn low_step(PX: &Rc<Array<u64>>, PY: &Rc<Array<u64>>, LS: &Rc<Array<u64>>, t: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v8, v10) => {
      let v12 = LS;
      let v = rocq_array::get::<u64>(&v12, t_1);
      let v16 = PX;
      let v26 = rocq_array::set::<u64>(v8, t_1, rocq_array::get::<u64>(&v16, v));
      let v27 = PY;
      let v37 = rocq_array::set::<u64>(v10, t_1, rocq_array::get::<u64>(&v27, v));
      (v26, v37)
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.up_step
// Variant: borrowed, uncurried
pub fn up_step(RX: &Rc<Array<u64>>, RY: &Rc<Array<u64>>, US: &Rc<Array<u64>>, a: u64, t: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let a_1 = a;
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      let v27 = add(sub(t_1, a_1), 1u64);
      let v28 = US;
      let v = rocq_array::get::<u64>(&v28, v27);
      let v32 = RX;
      let v42 = rocq_array::set::<u64>(v10, t_1, rocq_array::get::<u64>(&v32, v));
      let v43 = RY;
      let v53 = rocq_array::set::<u64>(v12, t_1, rocq_array::get::<u64>(&v43, v));
      (v42, v53)
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.climb
// Variant: borrowed, uncurried
pub fn climb_1(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, hm: u64, xi: u64, yi: u64, xj: u64, yj: u64, k: u64, gk: u64) -> u64 {
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
pub fn climb(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, hm: u64, xi: u64, yi: u64, xj: u64, yj: u64, k: u64, gk: u64, _H: ()) -> u64 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let xj_1 = xj;
  let yj_1 = yj;
  let k_1 = k;
  let gk_1 = gk;
  let v24 = ltb(k_1, hm_1);
  match bdec(v24) {
    sumbool::left => {
      let k1 = add(k_1, 1u64);
      let v37 = HX;
      let v40 = rocq_array::get::<u64>(&v37, k1);
      let v41 = HY;
      let g1 = crs(xi_1, yi_1, xj_1, yj_1, v40, rocq_array::get::<u64>(&v41, k1));
      match leb(gk_1, g1) {
        true => {
          climb(HX, HY, hm_1, xi_1, yi_1, xj_1, yj_1, k1, g1, ())
        },
        false => {
          k_1
        },
      }
    },
    sumbool::right => {
      k_1
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.jloop
// Variant: borrowed, uncurried
pub fn jloop_1(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, hm: u64, xi: u64, yi: u64, j: u64, k: u64, best: u64) -> u64 {
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
pub fn jloop(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, hm: u64, xi: u64, yi: u64, j: u64, k: u64, best: u64, _H: ()) -> u64 {
  let hm_1 = hm;
  let xi_1 = xi;
  let yi_1 = yi;
  let j_1 = j;
  let k_1 = k;
  let best_1 = best;
  let v22 = ltb(j_1, hm_1);
  match bdec(v22) {
    sumbool::left => {
      let v26 = HX;
      let xj = rocq_array::get::<u64>(&v26, j_1);
      let v30 = HY;
      let yj = rocq_array::get::<u64>(&v30, j_1);
      let k1 = match ltb(j_1, k_1) {
        true => {
          k_1
        },
        false => {
          add(j_1, 1u64)
        },
      };
      let v55 = HX;
      let v58 = rocq_array::get::<u64>(&v55, k1);
      let v59 = HY;
      let v75 = crs(xi_1, yi_1, xj, yj, v58, rocq_array::get::<u64>(&v59, k1));
      let k2 = climb_1(HX, HY, hm_1, xi_1, yi_1, xj, yj, k1, v75);
      let v97 = HX;
      let v100 = rocq_array::get::<u64>(&v97, k2);
      let v101 = HY;
      let g = crs(xi_1, yi_1, xj, yj, v100, rocq_array::get::<u64>(&v101, k2));
      let v125 = add(j_1, 1u64);
      let v132 = match ltb(best_1, g) {
        true => {
          g
        },
        false => {
          best_1
        },
      };
      jloop(HX, HY, hm_1, xi_1, yi_1, v125, k2, v132, ())
    },
    sumbool::right => {
      best_1
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.sweep_step
// Variant: borrowed, uncurried
pub fn sweep_step(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, h: u64, i: u64, best: u64) -> u64 {
  let h_1 = h;
  let i_1 = i;
  let best_1 = best;
  let v15 = sub(h_1, 1u64);
  let v16 = HX;
  let v19 = rocq_array::get::<u64>(&v16, i_1);
  let v20 = HY;
  jloop_1(HX, HY, v15, v19, rocq_array::get::<u64>(&v20, i_1), add(i_1, 1u64), add(i_1, 2u64), best_1)
}

// Rocq: Largesttriangle.largesttriangle_implem.sweep
// Variant: uncurried
pub fn sweep(HX: Rc<Array<u64>>, HY: Rc<Array<u64>>, h: u64) -> u64 {
  let v11 = sub(h, 2u64);
  let v12 = {
    move |_v13: u64, _v14: u64| -> bool {
      true
    }
  };
  let v19: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v12);
  let v20: Rc<dyn Fn(u64, u64) -> bool> = v19;
  let v27 = {
    let __anf_capture_32 = h;
    move |v34: u64, v35: u64| -> u64 {
      let HX = &HX;
      let HY = &HY;
      let v37 = Clone::clone(&__anf_capture_32);
      sweep_step(HX, HY, v37, v34, v35)
    }
  };
  let v48: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v27);
  loop_::<u64>(v11, v20, v48, 0u64, __rocq_global_625)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle_impl
// Variant: uncurried
pub fn largest_triangle_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> f64 {
  let v2 = &x;
  let n = rocq_array::length::<u64>(&v2);
  let v5 = {
    move |_v6: u64, v7: Rc<Array<u64>>| -> bool {
      std::mem::drop(v7);
      true
    }
  };
  let v12: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v5);
  let v13: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v12;
  let v16 = Rc::clone(&x);
  let v19 = Rc::clone(&y);
  let v20 = {
    move |i: u64, K: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let x = &v16;
      let y = &v19;
      let v37 = mul(rocq_array::get::<u64>(&x, i), __rocq_global_274);
      let v40 = rocq_array::get::<u64>(&y, i);
      rocq_array::set::<u64>(K, i, add(v37, v40))
    }
  };
  let v55: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v20);
  let v65 = rocq_array::make::<u64>(n, 0u64);
  let K = loop_::<Rc<Array<u64>>>(n, v13, v55, 0u64, v65);
  let S = sort(K, n);
  let v84 = {
    move |_v85: u64, v86: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v86);
      true
    }
  };
  let v91: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v84);
  let v92: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v91;
  let v95 = Rc::clone(&S);
  let v96 = {
    move |v99: u64, v100: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let S = &v95;
      let v107 = dedup_step(S, v99, v100);
      v107
    }
  };
  let v110: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v96);
  let v120 = rocq_array::make::<u64>(n, 0u64);
  let v139 = loop_::<(Rc<Array<u64>>, u64)>(n, v92, v110, 0u64, (v120, 0u64));
  match v139 {
    (v141, v143) => {
      let m = &v141;
      match ltb(v143, 3u64) {
        true => {
          std::mem::drop(S);
          std::mem::drop(x);
          std::mem::drop(y);
          std::mem::drop(v141);
          fzero(())
        },
        false => {
          let v164 = {
            move |_v165: u64, v166: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
              std::mem::drop(v166);
              true
            }
          };
          let v171: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(v164);
          let v172: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = v171;
          let v174 = Rc::clone(m);
          let v175 = {
            move |v178: u64, v179: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
              let m = &v174;
              let v186 = decode_step(m, v178, v179);
              v186
            }
          };
          let v189: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v175);
          let v199 = rocq_array::make::<u64>(v143, 0u64);
          let v206 = rocq_array::make::<u64>(v143, 0u64);
          let v223 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v143, v172, v189, 0u64, (v199, v206));
          match v223 {
            (v225, v227) => {
              let PY = &v225;
              let PX = &v227;
              let v236 = pass(PY, PX, v143);
              match v236 {
                (v238, v240) => {
                  let a = &v238;
                  let v244 = {
                    move |_v245: u64, v246: Rc<Array<u64>>| -> bool {
                      std::mem::drop(v246);
                      true
                    }
                  };
                  let v251: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v244);
                  let v252: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v251;
                  let v254 = Rc::clone(PY);
                  let v257 = {
                    let __anf_capture_260 = v143;
                    move |v262: u64, v263: Rc<Array<u64>>| -> Rc<Array<u64>> {
                      let v266 = Rc::clone(&v254);
                      let v268 = Clone::clone(&__anf_capture_260);
                      rev_step(v266, v268, v262, v263)
                    }
                  };
                  let v276: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v257);
                  let v286 = rocq_array::make::<u64>(v143, 0u64);
                  let RX = loop_::<Rc<Array<u64>>>(v143, v252, v276, 0u64, v286);
                  let v299 = {
                    move |_v300: u64, v301: Rc<Array<u64>>| -> bool {
                      std::mem::drop(v301);
                      true
                    }
                  };
                  let v306: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v299);
                  let v307: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v306;
                  let v309 = Rc::clone(PX);
                  let v312 = {
                    let __anf_capture_315 = v143;
                    move |v317: u64, v318: Rc<Array<u64>>| -> Rc<Array<u64>> {
                      let v321 = Rc::clone(&v309);
                      let v323 = Clone::clone(&__anf_capture_315);
                      rev_step(v321, v323, v317, v318)
                    }
                  };
                  let v331: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v312);
                  let v341 = rocq_array::make::<u64>(v143, 0u64);
                  let RY = loop_::<Rc<Array<u64>>>(v143, v307, v331, 0u64, v341);
                  let v356 = Rc::clone(&RX);
                  let v359 = Rc::clone(&RY);
                  let v362 = pass_owned(v356, v359, v143);
                  match v362 {
                    (v364, v366) => {
                      let h = sub(add(v240, v366), 2u64);
                      match ltb(h, 3u64) {
                        true => {
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
                        },
                        false => {
                          std::mem::drop(S);
                          std::mem::drop(x);
                          std::mem::drop(y);
                          let v400 = {
                            move |_v401: u64, v402: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
                              std::mem::drop(v402);
                              true
                            }
                          };
                          let v407: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(v400);
                          let v408: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = v407;
                          let v410 = Rc::clone(PY);
                          let v412 = Rc::clone(PX);
                          let v414 = Rc::clone(a);
                          let v415 = {
                            move |v422: u64, v423: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
                              let PY = &v410;
                              let PX = &v412;
                              let a = &v414;
                              let v432 = low_step(PY, PX, a, v422, v423);
                              v432
                            }
                          };
                          let v435: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v415);
                          let v445 = rocq_array::make::<u64>(h, 0u64);
                          let v452 = rocq_array::make::<u64>(h, 0u64);
                          let v469 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v240, v408, v435, 0u64, (v445, v452));
                          match &v469 {
                            (HY1, HX1) => {
                              std::mem::drop(v141);
                              std::mem::drop(v225);
                              std::mem::drop(v227);
                              std::mem::drop(v238);
                              let v477 = {
                                move |_v478: u64, v479: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
                                  std::mem::drop(v479);
                                  true
                                }
                              };
                              let v484: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(v477);
                              let v485: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = v484;
                              let v494 = {
                                let __anf_capture_495 = RX;
                                let __anf_capture_497 = RY;
                                let __anf_capture_499 = v364;
                                let __anf_capture_501 = v240;
                                move |v503: u64, v504: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
                                  let RX = &__anf_capture_495;
                                  let RY = &__anf_capture_497;
                                  let b = &__anf_capture_499;
                                  let v515 = up_step(RX, RY, b, Clone::clone(&__anf_capture_501), v503, v504);
                                  v515
                                }
                              };
                              let v518: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new(v494);
                              let v521 = Rc::clone(HY1);
                              let v522 = Rc::clone(HX1);
                              std::mem::drop(v469);
                              let v536 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(h, v485, v518, v240, (v521, v522));
                              match v536 {
                                (v538, v540) => {
                                  let best = sweep(v538, v540, h);
                                  div_1(of_uint63(sub(best, __rocq_global_625)), of_uint63(2u64))
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
          }
        },
      }
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle_impl
pub fn largest_triangle_impl_curried(x: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64> {
  let v3 = {
    move |y: Rc<Array<u64>>| -> f64 {
      let v9 = Rc::clone(&x);
      largest_triangle_impl(v9, y)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<u64>>) -> f64> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = __rocq_global_1292.with(Clone::clone);
  v0
}
const __rocq_global_274: u64 = 67108864u64;
const __rocq_global_625: u64 = 1152921504606846976u64;
std::thread_local! { static __rocq_global_1292: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = largest_triangle(); }
std::thread_local! { static __rocq_global_1295: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> f64>> = largest_triangle_curried(); }