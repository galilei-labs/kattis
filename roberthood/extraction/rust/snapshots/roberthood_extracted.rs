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

// Rocq: Roberthood.roberthood_implem.Kneg
pub fn Kneg() -> u64 {
  4098000u64
}

// Rocq: Corelib.Floats.PrimFloat.sqrt
pub fn sqrt(v0: f64) -> f64 {
  rocq_float64::sqrt(v0)
}

// Rocq: Corelib.Floats.PrimFloat.of_uint63
pub fn of_uint63(v0: u64) -> f64 {
  rocq_float64::of_uint63(v0)
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

// Rocq: Roberthood.roberthood_implem.bdec
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

// Rocq: Roberthood.roberthood_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roberthood.roberthood_implem.wloop (local: wloop)
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

// Rocq: Roberthood.roberthood_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Roberthood.roberthood_implem.encode
// Variant: uncurried
pub fn encode(x: u64, y: u64) -> u64 {
  let tmp = mul(add(x, 1000u64), 2048u64);
  let tmp_1 = add(y, 1000u64);
  add(tmp, tmp_1)
}

// Rocq: Roberthood.roberthood_implem.key_step
// Variant: uncurried
pub fn key_step(x: Rc<Array<u64>>, y: Rc<Array<u64>>, i: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&x, i);
  std::mem::drop(x);
  let tmp_1 = rocq_array::get::<u64>(&y, i);
  std::mem::drop(y);
  rocq_array::set::<u64>(A, i, encode(tmp, tmp_1))
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Roberthood.roberthood_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(src: &Rc<Array<u64>>, mid: u64, hi: u64, k: u64, st: ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let tmp = ltb(v15, mid_1);
          let tmp_1 = orb(leb(hi_1, v17), leb(rocq_array::get::<u64>(src, v15), rocq_array::get::<u64>(src, v17)));
          if andb(tmp, tmp_1) {
            let tmp_2 = (add(v15, 1u64), v17);
            let tmp_3 = rocq_array::set::<u64>(v12, k_1, rocq_array::get::<u64>(src, v15));
            (tmp_2, tmp_3)
          } else {
            let tmp_4 = (v15, add(v17, 1u64));
            let tmp_5 = rocq_array::set::<u64>(v12, k_1, rocq_array::get::<u64>(src, v17));
            (tmp_4, tmp_5)
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.merge
// Variant: uncurried
pub fn merge(src: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64, D: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = Rc::new(move |_v7: u64, v8: ((u64, u64), Rc<Array<u64>>)| -> bool {
    std::mem::drop(v8);
    true
  });
  let callback_1: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: u64, v29: ((u64, u64), Rc<Array<u64>>)| -> ((u64, u64), Rc<Array<u64>>) {
      let src = &src;
      let tmp = merge_step(src, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      tmp
    }
  });
  let tmp_1 = (lo, mid);
  let tmp_2 = loop_::<((u64, u64), Rc<Array<u64>>)>(hi, callback, callback_1, lo, (tmp_1, D));
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
pub fn pass_step(src: Rc<Array<u64>>, n: u64, w: u64, c: u64, D: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let lo = mul(c, add(w, w));
  let tmp = add(lo, w);
  let mid = if ltb(tmp, n) {
    add(lo, w)
  } else {
    n
  };
  let tmp_1 = add(w, w);
  let tmp_2 = add(lo, tmp_1);
  let hi = if ltb(tmp_2, n) {
    let tmp_3 = add(w, w);
    add(lo, tmp_3)
  } else {
    n
  };
  merge(src, lo, mid, hi, D)
}

// Rocq: Roberthood.roberthood_implem.merge_pass
// Variant: uncurried
pub fn merge_pass(src: Rc<Array<u64>>, D: Rc<Array<u64>>, n: u64, w: u64) -> Rc<Array<u64>> {
  let tmp = add(w, w);
  let tmp_1 = div(sub(add(n, tmp), 1u64), add(w, w));
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v38: u64, v39: Rc<Array<u64>>| -> bool {
    std::mem::drop(v39);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    let __anf_capture_55 = n;
    let __anf_capture_57 = w;
    move |v59: u64, v60: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let src_clone = Rc::clone(&src);
      let tmp_2 = Clone::clone(&__anf_capture_55);
      let tmp_3 = Clone::clone(&__anf_capture_57);
      pass_step(src_clone, tmp_2, tmp_3, v59, v60)
    }
  });
  loop_::<Rc<Array<u64>>>(tmp_1, callback, callback_1, 0u64, D)
}

// Rocq: Roberthood.roberthood_implem.msort_rec
// Variant: uncurried
pub fn msort_rec_1(n: u64, w: u64, A: Rc<Array<u64>>, B: Rc<Array<u64>>) -> Rc<Array<u64>> {
  msort_rec(n, w, A, B, ())
}

// Rocq: Roberthood.roberthood_implem.msort_rec (local: msort_rec)
// Variant: uncurried, lifted
pub fn msort_rec(n: u64, w: u64, A: Rc<Array<u64>>, B: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(w, n);
  let tmp_1 = add(w, w);
  let tmp_2 = andb(tmp, ltb(w, tmp_1));
  match bdec(tmp_2) {
    sumbool::left => {
      let tmp_3 = add(w, w);
      let A_clone = Rc::clone(&A);
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
pub fn msort(A: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  msort_rec_1(n, 1u64, A, tmp)
}

// Rocq: Roberthood.roberthood_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(A: &Rc<Array<u64>>, i: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let a = rocq_array::get::<u64>(A, i_1);
      let tmp = rocq_array::get::<u64>(m, sub(v8, 1u64));
      if eqb(a, tmp) {
        (v6, v8)
      } else {
        let tmp_1 = rocq_array::set::<u64>(v6, v8, a);
        (tmp_1, add(v8, 1u64))
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.neg_step
// Variant: uncurried
pub fn neg_step(Q: Rc<Array<u64>>, m: u64, i: u64, B: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = __rocq_global_654;
  let tmp_1 = sub(m, 1u64);
  let tmp_2 = rocq_array::get::<u64>(&Q, sub(tmp_1, i));
  std::mem::drop(Q);
  rocq_array::set::<u64>(B, i, sub(tmp, tmp_2))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltsb
// Variant: uncurried
pub fn ltsb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltsb(v0, v1)
}

// Rocq: Roberthood.roberthood_implem.cx
pub fn cx(k: u64) -> u64 {
  sub(div(k, 2048u64), 1000u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Roberthood.roberthood_implem.cy
pub fn cy(k: u64) -> u64 {
  sub(mod_(k, 2048u64), 1000u64)
}

// Rocq: Roberthood.roberthood_implem.mcross
// Variant: uncurried
pub fn mcross(a1: u64, a2: u64, b1: u64, b2: u64) -> u64 {
  let tmp = mul(sub(cx(a2), cx(a1)), sub(cy(b2), cy(b1)));
  let tmp_1 = sub(cy(a2), cy(a1));
  let tmp_2 = sub(cx(b2), cx(b1));
  sub(tmp, mul(tmp_1, tmp_2))
}

// Rocq: Roberthood.roberthood_implem.pops
// Variant: uncurried
pub fn pops_1(St: Rc<Array<u64>>, c: u64, t: u64) -> u64 {
  pops(St, c, t, ())
}

// Rocq: Roberthood.roberthood_implem.pops (local: pops)
// Variant: uncurried, lifted
pub fn pops(St: Rc<Array<u64>>, c: u64, t: u64, _H: ()) -> u64 {
  let tmp = ltb(1u64, t);
  let tmp_1 = rocq_array::get::<u64>(&St, sub(t, 2u64));
  let tmp_2 = rocq_array::get::<u64>(&St, sub(t, 1u64));
  let tmp_3 = rocq_array::get::<u64>(&St, sub(t, 2u64));
  let tmp_4 = andb(tmp, negb(ltsb(0u64, mcross(tmp_1, tmp_2, tmp_3, c))));
  match bdec(tmp_4) {
    sumbool::left => {
      pops(St, c, sub(t, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(St);
      t
    },
  }
}

// Rocq: Roberthood.roberthood_implem.chain_step
// Variant: borrowed, uncurried
pub fn chain_step(Q: &Rc<Array<u64>>, i: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let t = &v6;
      let c = rocq_array::get::<u64>(Q, i_1);
      let t_clone = Rc::clone(t);
      let t_1 = pops_1(t_clone, c, v8);
      let tmp = rocq_array::set::<u64>(v6, t_1, c);
      (tmp, add(t_1, 1u64))
    },
  }
}

// Rocq: Roberthood.roberthood_implem.chain
// Variant: uncurried
pub fn chain(Q: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let callback: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v4: u64, v5: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v5);
    true
  });
  let Q_clone = Rc::clone(&Q);
  let callback_1: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |v18: u64, v19: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let Q = &Q_clone;
      let tmp = chain_step(Q, v18, v19);
      tmp
    }
  });
  let tmp_1 = 1u64;
  let tmp_2 = rocq_array::get::<u64>(&Q, 0u64);
  std::mem::drop(Q);
  let tmp_3 = rocq_array::make::<u64>(m, tmp_2);
  loop_::<(Rc<Array<u64>>, u64)>(m, callback, callback_1, tmp_1, (tmp_3, 1u64))
}

// Rocq: Roberthood.roberthood_implem.msq
// Variant: uncurried
pub fn msq(a: u64, b: u64) -> u64 {
  let dx = add(cx(a), cx(b));
  let dy = add(cy(a), cy(b));
  add(mul(dx, dx), mul(dy, dy))
}

// Rocq: Roberthood.roberthood_implem.cal_step
// Variant: borrowed, uncurried
pub fn cal_step(L: &Rc<Array<u64>>, N: &Rc<Array<u64>>, lL: u64, lN: u64, _s: u64, st: ((u64, u64), u64)) -> ((u64, u64), u64) {
  let lL_1 = lL;
  let lN_1 = lN;
  let st_1 = st;
  match st_1 {
    (v10, v12) => {
      match v10 {
        (v15, v17) => {
          let k = &v15;
          let j = &v17;
          let d = msq(rocq_array::get::<u64>(L, v15), rocq_array::get::<u64>(N, v17));
          let best = if ltb(v12, d) {
            d
          } else {
            v12
          };
          let tmp = ltb(Clone::clone(k), lL_1);
          let tmp_1 = eqb(Clone::clone(j), lN_1);
          let tmp_2 = rocq_array::get::<u64>(L, Clone::clone(k));
          let tmp_3 = 1u64;
          let tmp_4 = rocq_array::get::<u64>(L, add(Clone::clone(k), tmp_3));
          let tmp_5 = rocq_array::get::<u64>(N, Clone::clone(j));
          let tmp_6 = 1u64;
          let tmp_7 = orb(tmp_1, ltsb(0u64, mcross(tmp_2, tmp_4, tmp_5, rocq_array::get::<u64>(N, add(Clone::clone(j), tmp_6)))));
          if andb(tmp, tmp_7) {
            let k_clone = Clone::clone(k);
            let tmp_8 = add(k_clone, 1u64);
            let j_clone = Clone::clone(j);
            ((tmp_8, j_clone), best)
          } else {
            let j_clone_1 = Clone::clone(j);
            let tmp_9 = add(j_clone_1, 1u64);
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
pub fn calipers(L: Rc<Array<u64>>, N: Rc<Array<u64>>, lL: u64, lN: u64) -> u64 {
  let tmp = add(lL, lN);
  let callback: Rc<dyn Fn(u64, ((u64, u64), u64)) -> bool> = Rc::new(move |_v12: u64, v13: ((u64, u64), u64)| -> bool {
    std::mem::drop(v13);
    true
  });
  let L_clone = Rc::clone(&L);
  let N_clone = Rc::clone(&N);
  let callback_1: Rc<dyn Fn(u64, ((u64, u64), u64)) -> ((u64, u64), u64)> = Rc::new({
    let __anf_capture_35 = lL;
    let __anf_capture_37 = lN;
    move |v39: u64, v40: ((u64, u64), u64)| -> ((u64, u64), u64) {
      let L = &L_clone;
      let N = &N_clone;
      let tmp_1 = cal_step(L, N, Clone::clone(&__anf_capture_35), Clone::clone(&__anf_capture_37), v39, v40);
      tmp_1
    }
  });
  let tmp_2 = loop_::<((u64, u64), u64)>(tmp, callback, callback_1, 0u64, ((0u64, 0u64), 0u64));
  match tmp_2 {
    (v89, v91) => {
      match v89 {
        (v94, v96) => {
          let tmp_3 = rocq_array::get::<u64>(&L, v94);
          let tmp_4 = rocq_array::get::<u64>(&N, v96);
          let d = msq(tmp_3, tmp_4);
          if ltb(v91, d) {
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
pub fn diam2(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> u64 {
  let n = rocq_array::length::<u64>(&x);
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v6: u64, v7: Rc<Array<u64>>| -> bool {
    std::mem::drop(v7);
    true
  });
  let x_clone = Rc::clone(&x);
  let y_clone = Rc::clone(&y);
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    move |v25: u64, v26: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let tmp = Rc::clone(&x_clone);
      let tmp_1 = Rc::clone(&y_clone);
      key_step(tmp, tmp_1, v25, v26)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let A = loop_::<Rc<Array<u64>>>(n, callback, callback_1, 0u64, tmp_2);
  let A_1 = msort(A, n);
  let callback_2: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(move |_v69: u64, v70: (Rc<Array<u64>>, u64)| -> bool {
    std::mem::drop(v70);
    true
  });
  let A_clone = Rc::clone(&A_1);
  let callback_3: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new({
    move |v83: u64, v84: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let A = &A_clone;
      let tmp_3 = dedup_step(A, v83, v84);
      tmp_3
    }
  });
  let tmp_4 = rocq_array::get::<u64>(&A_1, 0u64);
  let tmp_5 = rocq_array::make::<u64>(n, tmp_4);
  let tmp_6 = loop_::<(Rc<Array<u64>>, u64)>(n, callback_2, callback_3, 1u64, (tmp_5, 1u64));
  match tmp_6 {
    (v129, v131) => {
      let m = &v129;
      if ltb(v131, 2u64) {
        std::mem::drop(x);
        std::mem::drop(y);
        std::mem::drop(A_1);
        std::mem::drop(v129);
        0u64
      } else {
        let callback_4: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v149: u64, v150: Rc<Array<u64>>| -> bool {
          std::mem::drop(v150);
          true
        });
        let m_clone = Rc::clone(m);
        let callback_5: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
          let __anf_capture_164 = v131;
          move |v166: u64, v167: Rc<Array<u64>>| -> Rc<Array<u64>> {
            let tmp_7 = Rc::clone(&m_clone);
            let tmp_8 = Clone::clone(&__anf_capture_164);
            neg_step(tmp_7, tmp_8, v166, v167)
          }
        });
        let tmp_9 = rocq_array::make::<u64>(v131, 0u64);
        let Q2 = loop_::<Rc<Array<u64>>>(v131, callback_4, callback_5, 0u64, tmp_9);
        let tmp_10 = chain(v129, v131);
        match tmp_10 {
          (v209, v211) => {
            std::mem::drop(x);
            std::mem::drop(y);
            std::mem::drop(A_1);
            let tmp_11 = chain(Q2, v131);
            match tmp_11 {
              (v220, v222) => {
                calipers(v209, v220, sub(v211, 1u64), sub(v222, 1u64))
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
pub fn roberthood(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> f64 {
  sqrt(of_uint63(diam2(x, y)))
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
const __rocq_global_654: u64 = 4098000u64;