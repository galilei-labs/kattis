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

// Rocq: Largesttriangle.largesttriangle_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.wloop (local: wloop)
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
  if b1 {
    true
  } else {
    b2
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
          let tmp = ltb(v17, mid_1);
          let tmp_1 = orb(leb(hi_1, v12), leb(rocq_array::get::<u64>(A, v17), rocq_array::get::<u64>(A, v12)));
          if andb(tmp, tmp_1) {
            let tmp_2 = rocq_array::set::<u64>(v15, k_1, rocq_array::get::<u64>(A, v17));
            ((tmp_2, add(v17, 1u64)), v12)
          } else {
            let tmp_3 = rocq_array::set::<u64>(v15, k_1, rocq_array::get::<u64>(A, v12));
            ((tmp_3, v17), add(v12, 1u64))
          }
        },
      }
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.merge
// Variant: uncurried
pub fn merge(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, ((Rc<Array<u64>>, u64), u64)) -> bool> = Rc::new(move |_v7: u64, v8: ((Rc<Array<u64>>, u64), u64)| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((Rc<Array<u64>>, u64), u64)) -> ((Rc<Array<u64>>, u64), u64)> = Rc::new({
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: u64, v29: ((Rc<Array<u64>>, u64), u64)| -> ((Rc<Array<u64>>, u64), u64) {
      let A = &A;
      let tmp = merge_step(A, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      tmp
    }
  });
  let tmp_1 = (T, lo);
  let tmp_2 = loop_::<((Rc<Array<u64>>, u64), u64)>(hi, callback, callback_1, lo, (tmp_1, mid));
  match tmp_2 {
    (v69, _v71) => {
      let i = &v69;
      let i_0_clone = Rc::clone(&i.0);
      std::mem::drop(v69);
      i_0_clone
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.copy_step
// Variant: uncurried
pub fn copy_step(T: Rc<Array<u64>>, k: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&T, k);
  std::mem::drop(T);
  rocq_array::set::<u64>(A, k, tmp)
}

// Rocq: Largesttriangle.largesttriangle_implem.msort
// Variant: uncurried
pub fn msort_1(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(A, T, lo, hi, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(A: Rc<Array<u64>>, T: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(hi, lo);
      let mid = add(lo, div(tmp_1, 2u64));
      let tmp_2 = msort(A, T, lo, mid, ());
      match &tmp_2 {
        (T1, A1) => {
          let tmp_3 = ();
          let T1_clone = Rc::clone(T1);
          let A1_clone = Rc::clone(A1);
          std::mem::drop(tmp_2);
          let tmp_4 = msort(T1_clone, A1_clone, mid, hi, tmp_3);
          match tmp_4 {
            (v91, v93) => {
              let T2 = &v91;
              let T2_clone = Rc::clone(T2);
              let T3 = merge(T2_clone, v93, lo, mid, hi);
              let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v110: u64, v111: Rc<Array<u64>>| -> bool {
                std::mem::drop(v111);
                true
              });
              let T3_clone = Rc::clone(&T3);
              let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
                move |v124: u64, v125: Rc<Array<u64>>| -> Rc<Array<u64>> {
                  let tmp_5 = Rc::clone(&T3_clone);
                  copy_step(tmp_5, v124, v125)
                }
              });
              let tmp_6 = loop_::<Rc<Array<u64>>>(hi, callback, callback_1, lo, v91);
              (tmp_6, T3)
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
  let tmp = rocq_array::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(K, tmp, 0u64, n))
}

// Rocq: Largesttriangle.largesttriangle_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(S: &Rc<Array<u64>>, t: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let tmp = eqb(v8, 0u64);
      let tmp_1 = rocq_array::get::<u64>(m, sub(v8, 1u64));
      let tmp_2 = ltb(tmp_1, rocq_array::get::<u64>(S, t_1));
      if orb(tmp, tmp_2) {
        let tmp_3 = rocq_array::set::<u64>(v6, v8, rocq_array::get::<u64>(S, t_1));
        (tmp_3, add(v8, 1u64))
      } else {
        (v6, v8)
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
      let d = rocq_array::get::<u64>(D, u_1);
      let tmp = rocq_array::set::<u64>(v6, u_1, div(d, __rocq_global_274));
      let tmp_1 = rocq_array::set::<u64>(v8, u_1, mod_(d, __rocq_global_274));
      (tmp, tmp_1)
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.crs
// Variant: uncurried
pub fn crs(ax: u64, ay: u64, bx: u64, by_: u64, cx: u64, cy: u64) -> u64 {
  let tmp = mul(sub(bx, ax), sub(cy, ay));
  let tmp_1 = sub(cx, ax);
  let tmp_2 = sub(by_, ay);
  add(sub(tmp, mul(tmp_1, tmp_2)), __rocq_global_625)
}

// Rocq: Largesttriangle.largesttriangle_implem.popl
// Variant: uncurried
pub fn popl_1(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, ST: Rc<Array<u64>>, s: u64, r: u64) -> u64 {
  popl(X, Y, ST, s, r, ())
}

// Rocq: Largesttriangle.largesttriangle_implem.popl (local: popl)
// Variant: uncurried, lifted
pub fn popl(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, ST: Rc<Array<u64>>, s: u64, r: u64, _H: ()) -> u64 {
  let tmp = ltb(1u64, r);
  match bdec(tmp) {
    sumbool::left => {
      let i1 = rocq_array::get::<u64>(&ST, sub(r, 2u64));
      let i2 = rocq_array::get::<u64>(&ST, sub(r, 1u64));
      let tmp_1 = rocq_array::get::<u64>(&X, i1);
      let tmp_2 = rocq_array::get::<u64>(&Y, i1);
      let tmp_3 = rocq_array::get::<u64>(&X, i2);
      let tmp_4 = rocq_array::get::<u64>(&Y, i2);
      let tmp_5 = rocq_array::get::<u64>(&X, s);
      let tmp_6 = rocq_array::get::<u64>(&Y, s);
      let tmp_7 = crs(tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, tmp_6);
      if leb(tmp_7, __rocq_global_625) {
        popl(X, Y, ST, s, sub(r, 1u64), ())
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
pub fn pass_step(X: &Rc<Array<u64>>, Y: &Rc<Array<u64>>, s: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let s_1 = s;
  let st_1 = st;
  match st_1 {
    (v7, v9) => {
      let r = &v7;
      let X_clone = Rc::clone(X);
      let Y_clone = Rc::clone(Y);
      let r_clone = Rc::clone(r);
      let r_ = popl_1(X_clone, Y_clone, r_clone, s_1, v9);
      let tmp = rocq_array::set::<u64>(v7, r_, s_1);
      (tmp, add(r_, 1u64))
    },
  }
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: uncurried
pub fn pass_owned(X: Rc<Array<u64>>, Y: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v5: u64, v6: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |v22: u64, v23: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let X = &X;
      let Y = &Y;
      let tmp = pass_step(X, Y, v22, v23);
      tmp
    }
  });
  let tmp_1 = rocq_array::make::<u64>(m, 0u64);
  loop_::<(Rc<Array<u64>>, u64)>(m, callback, callback_1, 1u64, (tmp_1, 1u64))
}

// Rocq: Largesttriangle.largesttriangle_implem.pass
// Variant: borrowed, uncurried
pub fn pass(X: &Rc<Array<u64>>, Y: &Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let m_1 = m;
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v6: u64, v7: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v7);
    true
  });
  let X_clone = Rc::clone(X);
  let Y_clone = Rc::clone(Y);
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |v25: u64, v26: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let X = &X_clone;
      let Y = &Y_clone;
      let tmp = pass_step(X, Y, v25, v26);
      tmp
    }
  });
  let tmp_1 = rocq_array::make::<u64>(m_1, 0u64);
  loop_::<(Rc<Array<u64>>, u64)>(m_1, callback, callback_1, 1u64, (tmp_1, 1u64))
}

// Rocq: Largesttriangle.largesttriangle_implem.rev_step
// Variant: uncurried
pub fn rev_step(X: Rc<Array<u64>>, m: u64, s: u64, R: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = sub(m, 1u64);
  let tmp_1 = rocq_array::get::<u64>(&X, sub(tmp, s));
  std::mem::drop(X);
  rocq_array::set::<u64>(R, s, tmp_1)
}

// Rocq: Largesttriangle.largesttriangle_implem.low_step
// Variant: borrowed, uncurried
pub fn low_step(PX: &Rc<Array<u64>>, PY: &Rc<Array<u64>>, LS: &Rc<Array<u64>>, t: u64, st: (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let t_1 = t;
  let st_1 = st;
  match st_1 {
    (v8, v10) => {
      let v = rocq_array::get::<u64>(LS, t_1);
      let tmp = rocq_array::set::<u64>(v8, t_1, rocq_array::get::<u64>(PX, v));
      let tmp_1 = rocq_array::set::<u64>(v10, t_1, rocq_array::get::<u64>(PY, v));
      (tmp, tmp_1)
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
      let v = rocq_array::get::<u64>(US, add(sub(t_1, a_1), 1u64));
      let tmp = rocq_array::set::<u64>(v10, t_1, rocq_array::get::<u64>(RX, v));
      let tmp_1 = rocq_array::set::<u64>(v12, t_1, rocq_array::get::<u64>(RY, v));
      (tmp, tmp_1)
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
  let tmp = ltb(k_1, hm_1);
  match bdec(tmp) {
    sumbool::left => {
      let k1 = add(k_1, 1u64);
      let g1 = crs(xi_1, yi_1, xj_1, yj_1, rocq_array::get::<u64>(HX, k1), rocq_array::get::<u64>(HY, k1));
      if leb(gk_1, g1) {
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
  let tmp = ltb(j_1, hm_1);
  match bdec(tmp) {
    sumbool::left => {
      let xj = rocq_array::get::<u64>(HX, j_1);
      let yj = rocq_array::get::<u64>(HY, j_1);
      let k1 = if ltb(j_1, k_1) {
        k_1
      } else {
        add(j_1, 1u64)
      };
      let tmp_1 = crs(xi_1, yi_1, xj, yj, rocq_array::get::<u64>(HX, k1), rocq_array::get::<u64>(HY, k1));
      let k2 = climb_1(HX, HY, hm_1, xi_1, yi_1, xj, yj, k1, tmp_1);
      let g = crs(xi_1, yi_1, xj, yj, rocq_array::get::<u64>(HX, k2), rocq_array::get::<u64>(HY, k2));
      let tmp_2 = add(j_1, 1u64);
      let tmp_3 = if ltb(best_1, g) {
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
pub fn sweep_step(HX: &Rc<Array<u64>>, HY: &Rc<Array<u64>>, h: u64, i: u64, best: u64) -> u64 {
  let h_1 = h;
  let i_1 = i;
  let best_1 = best;
  let tmp = sub(h_1, 1u64);
  let tmp_1 = rocq_array::get::<u64>(HX, i_1);
  let tmp_2 = HY;
  jloop_1(HX, HY, tmp, tmp_1, rocq_array::get::<u64>(tmp_2, i_1), add(i_1, 1u64), add(i_1, 2u64), best_1)
}

// Rocq: Largesttriangle.largesttriangle_implem.sweep
// Variant: uncurried
pub fn sweep(HX: Rc<Array<u64>>, HY: Rc<Array<u64>>, h: u64) -> u64 {
  let tmp = sub(h, 2u64);
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(move |_v13: u64, _v14: u64| -> bool {
    true
  });
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_32 = h;
    move |v34: u64, v35: u64| -> u64 {
      let HX = &HX;
      let HY = &HY;
      let tmp_1 = Clone::clone(&__anf_capture_32);
      sweep_step(HX, HY, tmp_1, v34, v35)
    }
  });
  loop_::<u64>(tmp, callback, callback_1, 0u64, __rocq_global_625)
}

// Rocq: Corelib.Floats.PrimFloat.div
// Variant: uncurried
pub fn div_1(v0: f64, v1: f64) -> f64 {
  rocq_float64::div(v0, v1)
}

// Rocq: Largesttriangle.largesttriangle_implem.largest_triangle_impl
// Variant: uncurried
pub fn largest_triangle_impl(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> f64 {
  let n = rocq_array::length::<u64>(&x);
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<u64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let x_clone = Rc::clone(&x);
  let y_clone = Rc::clone(&y);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |i: u64, K: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let x = &x_clone;
      let y = &y_clone;
      let tmp = mul(rocq_array::get::<u64>(x, i), __rocq_global_274);
      let tmp_1 = rocq_array::get::<u64>(y, i);
      rocq_array::set::<u64>(K, i, add(tmp, tmp_1))
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let K = loop_::<Rc<Array<u64>>>(n, callback, callback_1, 0u64, tmp_2);
  let S = sort(K, n);
  let callback_2: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v85: u64, v86: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v86);
    true
  });
  let S_clone = Rc::clone(&S);
  let callback_3: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |v99: u64, v100: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let S = &S_clone;
      let tmp_3 = dedup_step(S, v99, v100);
      tmp_3
    }
  });
  let tmp_4 = rocq_array::make::<u64>(n, 0u64);
  let tmp_5 = loop_::<(Rc<Array<u64>>, u64)>(n, callback_2, callback_3, 0u64, (tmp_4, 0u64));
  match tmp_5 {
    (v141, v143) => {
      let m = &v141;
      if ltb(v143, 3u64) {
        std::mem::drop(S);
        std::mem::drop(x);
        std::mem::drop(y);
        std::mem::drop(v141);
        fzero(())
      } else {
        let callback_4: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(move |_v165: u64, v166: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
          std::mem::drop(v166);
          true
        });
        let m_clone = Rc::clone(m);
        let callback_5: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
          move |v178: u64, v179: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
            let m = &m_clone;
            let tmp_6 = decode_step(m, v178, v179);
            tmp_6
          }
        });
        let tmp_7 = rocq_array::make::<u64>(v143, 0u64);
        let tmp_8 = rocq_array::make::<u64>(v143, 0u64);
        let tmp_9 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v143, callback_4, callback_5, 0u64, (tmp_7, tmp_8));
        match tmp_9 {
          (v225, v227) => {
            let PY = &v225;
            let PX = &v227;
            let tmp_10 = pass(PY, PX, v143);
            match tmp_10 {
              (v238, v240) => {
                let a = &v238;
                let callback_6: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v245: u64, v246: Rc<Array<u64>>| -> bool {
                  std::mem::drop(v246);
                  true
                });
                let PY_clone = Rc::clone(PY);
                let callback_7: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
                  let __anf_capture_260 = v143;
                  move |v262: u64, v263: Rc<Array<u64>>| -> Rc<Array<u64>> {
                    let tmp_11 = Rc::clone(&PY_clone);
                    let tmp_12 = Clone::clone(&__anf_capture_260);
                    rev_step(tmp_11, tmp_12, v262, v263)
                  }
                });
                let tmp_13 = rocq_array::make::<u64>(v143, 0u64);
                let RX = loop_::<Rc<Array<u64>>>(v143, callback_6, callback_7, 0u64, tmp_13);
                let callback_8: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v300: u64, v301: Rc<Array<u64>>| -> bool {
                  std::mem::drop(v301);
                  true
                });
                let PX_clone = Rc::clone(PX);
                let callback_9: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
                  let __anf_capture_315 = v143;
                  move |v317: u64, v318: Rc<Array<u64>>| -> Rc<Array<u64>> {
                    let tmp_14 = Rc::clone(&PX_clone);
                    let tmp_15 = Clone::clone(&__anf_capture_315);
                    rev_step(tmp_14, tmp_15, v317, v318)
                  }
                });
                let tmp_16 = rocq_array::make::<u64>(v143, 0u64);
                let RY = loop_::<Rc<Array<u64>>>(v143, callback_8, callback_9, 0u64, tmp_16);
                let RX_clone = Rc::clone(&RX);
                let RY_clone = Rc::clone(&RY);
                let tmp_17 = pass_owned(RX_clone, RY_clone, v143);
                match tmp_17 {
                  (v364, v366) => {
                    let h = sub(add(v240, v366), 2u64);
                    if ltb(h, 3u64) {
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
                      let callback_10: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(move |_v401: u64, v402: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
                        std::mem::drop(v402);
                        true
                      });
                      let PY_clone_1 = Rc::clone(PY);
                      let PX_clone_1 = Rc::clone(PX);
                      let a_clone = Rc::clone(a);
                      let callback_11: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
                        move |v422: u64, v423: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
                          let PY = &PY_clone_1;
                          let PX = &PX_clone_1;
                          let a = &a_clone;
                          let tmp_18 = low_step(PY, PX, a, v422, v423);
                          tmp_18
                        }
                      });
                      let tmp_19 = rocq_array::make::<u64>(h, 0u64);
                      let tmp_20 = rocq_array::make::<u64>(h, 0u64);
                      let tmp_21 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(v240, callback_10, callback_11, 0u64, (tmp_19, tmp_20));
                      match &tmp_21 {
                        (HY1, HX1) => {
                          std::mem::drop(v141);
                          std::mem::drop(v225);
                          std::mem::drop(v227);
                          std::mem::drop(v238);
                          let callback_12: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> bool> = Rc::new(move |_v478: u64, v479: (Rc<Array<u64>>, Rc<Array<u64>>)| -> bool {
                            std::mem::drop(v479);
                            true
                          });
                          let callback_13: Rc<dyn Fn(u64, (Rc<Array<u64>>, Rc<Array<u64>>)) -> (Rc<Array<u64>>, Rc<Array<u64>>)> = Rc::new({
                            let __anf_capture_495 = RX;
                            let __anf_capture_497 = RY;
                            let __anf_capture_499 = v364;
                            let __anf_capture_501 = v240;
                            move |v503: u64, v504: (Rc<Array<u64>>, Rc<Array<u64>>)| -> (Rc<Array<u64>>, Rc<Array<u64>>) {
                              let RX = &__anf_capture_495;
                              let RY = &__anf_capture_497;
                              let b = &__anf_capture_499;
                              let tmp_22 = up_step(RX, RY, b, Clone::clone(&__anf_capture_501), v503, v504);
                              tmp_22
                            }
                          });
                          let HY1_clone = Rc::clone(HY1);
                          let HX1_clone = Rc::clone(HX1);
                          std::mem::drop(tmp_21);
                          let tmp_23 = loop_::<(Rc<Array<u64>>, Rc<Array<u64>>)>(h, callback_12, callback_13, v240, (HY1_clone, HX1_clone));
                          match tmp_23 {
                            (v538, v540) => {
                              let best = sweep(v538, v540, h);
                              div_1(of_uint63(sub(best, __rocq_global_625)), of_uint63(2u64))
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
const __rocq_global_274: u64 = 67108864u64;
const __rocq_global_625: u64 = 1152921504606846976u64;