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

// Rocq: Roberthood.roberthood_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Roberthood.roberthood_implem.wloop (local: wloop)
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
  let v18 = mul(add(x, 1000u64), 2048u64);
  let v26 = add(y, 1000u64);
  add(v18, v26)
}

// Rocq: Roberthood.roberthood_implem.key_step
// Variant: uncurried
pub fn key_step(x: Rc<Array<u64>>, y: Rc<Array<u64>>, i: u64, A: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = &x;
  let v8 = rocq_array::get::<u64>(&v5, i);
  std::mem::drop(x);
  let v9 = &y;
  let v12 = rocq_array::get::<u64>(&v9, i);
  std::mem::drop(y);
  rocq_array::set::<u64>(A, i, encode(v8, v12))
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
          let v25 = ltb(v15, mid_1);
          let v32 = leb(hi_1, v17);
          let v34 = src;
          let v37 = rocq_array::get::<u64>(&v34, v15);
          let v38 = src;
          let v51 = orb(v32, leb(v37, rocq_array::get::<u64>(&v38, v17)));
          match andb(v25, v51) {
            true => {
              let v70 = (add(v15, 1u64), v17);
              let v72 = src;
              let v82 = rocq_array::set::<u64>(v12, k_1, rocq_array::get::<u64>(&v72, v15));
              (v70, v82)
            },
            false => {
              let v103 = (v15, add(v17, 1u64));
              let v105 = src;
              let v115 = rocq_array::set::<u64>(v12, k_1, rocq_array::get::<u64>(&v105, v17));
              (v103, v115)
            },
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.merge
// Variant: uncurried
pub fn merge(src: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64, D: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v6 = {
    move |_v7: u64, v8: ((u64, u64), Rc<Array<u64>>)| -> bool {
      std::mem::drop(v8);
      true
    }
  };
  let v13: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = Rc::new(v6);
  let v14: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = v13;
  let v21 = {
    let __anf_capture_24 = mid;
    let __anf_capture_26 = hi;
    move |v28: u64, v29: ((u64, u64), Rc<Array<u64>>)| -> ((u64, u64), Rc<Array<u64>>) {
      let src = &src;
      let v40 = merge_step(src, Clone::clone(&__anf_capture_24), Clone::clone(&__anf_capture_26), v28, v29);
      v40
    }
  };
  let v43: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>)> = Rc::new(v21);
  let v49 = (lo, mid);
  let v67 = loop_::<((u64, u64), Rc<Array<u64>>)>(hi, v14, v43, lo, (v49, D));
  match v67 {
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
  let v24 = add(lo, w);
  let mid = match ltb(v24, n) {
    true => {
      add(lo, w)
    },
    false => {
      n
    },
  };
  let v48 = add(w, w);
  let v54 = add(lo, v48);
  let hi = match ltb(v54, n) {
    true => {
      let v66 = add(w, w);
      add(lo, v66)
    },
    false => {
      n
    },
  };
  merge(src, lo, mid, hi, D)
}

// Rocq: Roberthood.roberthood_implem.merge_pass
// Variant: uncurried
pub fn merge_pass(src: Rc<Array<u64>>, D: Rc<Array<u64>>, n: u64, w: u64) -> Rc<Array<u64>> {
  let v13 = add(w, w);
  let v36 = div(sub(add(n, v13), 1u64), add(w, w));
  let v37 = {
    move |_v38: u64, v39: Rc<Array<u64>>| -> bool {
      std::mem::drop(v39);
      true
    }
  };
  let v44: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v37);
  let v45: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v44;
  let v52 = {
    let __anf_capture_55 = n;
    let __anf_capture_57 = w;
    move |v59: u64, v60: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v63 = Rc::clone(&src);
      let v65 = Clone::clone(&__anf_capture_55);
      let v67 = Clone::clone(&__anf_capture_57);
      pass_step(v63, v65, v67, v59, v60)
    }
  };
  let v75: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v52);
  loop_::<Rc<Array<u64>>>(v36, v45, v75, 0u64, D)
}

// Rocq: Roberthood.roberthood_implem.msort_rec
// Variant: uncurried
pub fn msort_rec_1(n: u64, w: u64, A: Rc<Array<u64>>, B: Rc<Array<u64>>) -> Rc<Array<u64>> {
  msort_rec(n, w, A, B, ())
}

// Rocq: Roberthood.roberthood_implem.msort_rec (local: msort_rec)
// Variant: uncurried, lifted
pub fn msort_rec(n: u64, w: u64, A: Rc<Array<u64>>, B: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(w, n);
  let v19 = add(w, w);
  let v30 = andb(v12, ltb(w, v19));
  match bdec(v30) {
    sumbool::left => {
      let v39 = add(w, w);
      let v43 = Rc::clone(&A);
      let v50 = merge_pass(v43, B, n, w);
      msort_rec(n, v39, v50, A, ())
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
  let v11 = rocq_array::make::<u64>(n, 0u64);
  msort_rec_1(n, 1u64, A, v11)
}

// Rocq: Roberthood.roberthood_implem.dedup_step
// Variant: borrowed, uncurried
pub fn dedup_step(A: &Rc<Array<u64>>, i: u64, st: (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64) {
  let i_1 = i;
  let st_1 = st;
  match st_1 {
    (v6, v8) => {
      let m = &v6;
      let v11 = A;
      let a = rocq_array::get::<u64>(&v11, i_1);
      let v24 = sub(v8, 1u64);
      let v26 = rocq_array::get::<u64>(&m, v24);
      match eqb(a, v26) {
        true => {
          (v6, v8)
        },
        false => {
          let v47 = rocq_array::set::<u64>(v6, v8, a);
          (v47, add(v8, 1u64))
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.neg_step
// Variant: uncurried
pub fn neg_step(Q: Rc<Array<u64>>, m: u64, i: u64, B: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v5 = __rocq_global_654;
  let v15 = sub(m, 1u64);
  let v19 = sub(v15, i);
  let v20 = &Q;
  let v23 = rocq_array::get::<u64>(&v20, v19);
  std::mem::drop(Q);
  rocq_array::set::<u64>(B, i, sub(v5, v23))
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
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
  let v38 = mul(sub(cx(a2), cx(a1)), sub(cy(b2), cy(b1)));
  let v53 = sub(cy(a2), cy(a1));
  let v67 = sub(cx(b2), cx(b1));
  sub(v38, mul(v53, v67))
}

// Rocq: Roberthood.roberthood_implem.pops
// Variant: uncurried
pub fn pops_1(St: Rc<Array<u64>>, c: u64, t: u64) -> u64 {
  pops(St, c, t, ())
}

// Rocq: Roberthood.roberthood_implem.pops (local: pops)
// Variant: uncurried, lifted
pub fn pops(St: Rc<Array<u64>>, c: u64, t: u64, _H: ()) -> u64 {
  let v13 = ltb(1u64, t);
  let v26 = sub(t, 2u64);
  let v27 = &St;
  let v30 = rocq_array::get::<u64>(&v27, v26);
  let v38 = sub(t, 1u64);
  let v39 = &St;
  let v42 = rocq_array::get::<u64>(&v39, v38);
  let v50 = sub(t, 2u64);
  let v51 = &St;
  let v54 = rocq_array::get::<u64>(&v51, v50);
  let v77 = andb(v13, negb(ltsb(0u64, mcross(v30, v42, v54, c))));
  match bdec(v77) {
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
      let v11 = Q;
      let c = rocq_array::get::<u64>(&v11, i_1);
      let v17 = Rc::clone(t);
      let t_1 = pops_1(v17, c, v8);
      let v29 = rocq_array::set::<u64>(v6, t_1, c);
      (v29, add(t_1, 1u64))
    },
  }
}

// Rocq: Roberthood.roberthood_implem.chain
// Variant: uncurried
pub fn chain(Q: Rc<Array<u64>>, m: u64) -> (Rc<Array<u64>>, u64) {
  let v3 = {
    move |_v4: u64, v5: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v5);
      true
    }
  };
  let v10: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v3);
  let v11: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v10;
  let v14 = Rc::clone(&Q);
  let v15 = {
    move |v18: u64, v19: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let Q = &v14;
      let v26 = chain_step(Q, v18, v19);
      v26
    }
  };
  let v29: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v15);
  let v32 = 1u64;
  let v34 = 0u64;
  let v35 = &Q;
  let v38 = rocq_array::get::<u64>(&v35, v34);
  std::mem::drop(Q);
  let v43 = rocq_array::make::<u64>(m, v38);
  loop_::<(Rc<Array<u64>>, u64)>(m, v11, v29, v32, (v43, 1u64))
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
          let v22 = L;
          let v25 = rocq_array::get::<u64>(&v22, v15);
          let v26 = N;
          let d = msq(v25, rocq_array::get::<u64>(&v26, v17));
          let best = match ltb(v12, d) {
            true => {
              d
            },
            false => {
              v12
            },
          };
          let v53 = ltb(Clone::clone(k), lL_1);
          let v60 = eqb(Clone::clone(j), lN_1);
          let v65 = L;
          let v67 = Clone::clone(k);
          let v68 = rocq_array::get::<u64>(&v65, v67);
          let v71 = 1u64;
          let v76 = add(Clone::clone(k), v71);
          let v77 = L;
          let v80 = rocq_array::get::<u64>(&v77, v76);
          let v81 = N;
          let v83 = Clone::clone(j);
          let v84 = rocq_array::get::<u64>(&v81, v83);
          let v87 = 1u64;
          let v92 = add(Clone::clone(j), v87);
          let v93 = N;
          let v115 = orb(v60, ltsb(0u64, mcross(v68, v80, v84, rocq_array::get::<u64>(&v93, v92))));
          match andb(v53, v115) {
            true => {
              let v126 = Clone::clone(k);
              let v130 = add(v126, 1u64);
              let v133 = Clone::clone(j);
              ((v130, v133), best)
            },
            false => {
              let v148 = Clone::clone(j);
              let v151 = add(v148, 1u64);
              let v153 = Clone::clone(k);
              ((v153, v151), best)
            },
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.calipers
// Variant: uncurried
pub fn calipers(L: Rc<Array<u64>>, N: Rc<Array<u64>>, lL: u64, lN: u64) -> u64 {
  let v10 = add(lL, lN);
  let v11 = {
    move |_v12: u64, v13: ((u64, u64), u64)| -> bool {
      std::mem::drop(v13);
      true
    }
  };
  let v18: Rc<dyn Fn(u64, ((u64, u64), u64)) -> bool> = Rc::new(v11);
  let v19: Rc<dyn Fn(u64, ((u64, u64), u64)) -> bool> = v18;
  let v22 = Rc::clone(&L);
  let v25 = Rc::clone(&N);
  let v30 = {
    let __anf_capture_35 = lL;
    let __anf_capture_37 = lN;
    move |v39: u64, v40: ((u64, u64), u64)| -> ((u64, u64), u64) {
      let L = &v22;
      let N = &v25;
      let v52 = cal_step(L, N, Clone::clone(&__anf_capture_35), Clone::clone(&__anf_capture_37), v39, v40);
      v52
    }
  };
  let v55: Rc<dyn Fn(u64, ((u64, u64), u64)) -> ((u64, u64), u64)> = Rc::new(v30);
  let v87 = loop_::<((u64, u64), u64)>(v10, v19, v55, 0u64, ((0u64, 0u64), 0u64));
  match v87 {
    (v89, v91) => {
      match v89 {
        (v94, v96) => {
          let v99 = &L;
          let v102 = rocq_array::get::<u64>(&v99, v94);
          let v103 = &N;
          let v106 = rocq_array::get::<u64>(&v103, v96);
          let d = msq(v102, v106);
          match ltb(v91, d) {
            true => {
              std::mem::drop(N);
              std::mem::drop(L);
              d
            },
            false => {
              std::mem::drop(N);
              std::mem::drop(L);
              v91
            },
          }
        },
      }
    },
  }
}

// Rocq: Roberthood.roberthood_implem.diam2
// Variant: uncurried
pub fn diam2(x: Rc<Array<u64>>, y: Rc<Array<u64>>) -> u64 {
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
    move |v25: u64, v26: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let v29 = Rc::clone(&v16);
      let v31 = Rc::clone(&v19);
      key_step(v29, v31, v25, v26)
    }
  };
  let v39: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v20);
  let v49 = rocq_array::make::<u64>(n, 0u64);
  let A = loop_::<Rc<Array<u64>>>(n, v13, v39, 0u64, v49);
  let A_1 = msort(A, n);
  let v68 = {
    move |_v69: u64, v70: (Rc<Array<u64>>, u64)| -> bool {
      std::mem::drop(v70);
      true
    }
  };
  let v75: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = Rc::new(v68);
  let v76: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> bool> = v75;
  let v79 = Rc::clone(&A_1);
  let v80 = {
    move |v83: u64, v84: (Rc<Array<u64>>, u64)| -> (Rc<Array<u64>>, u64) {
      let A = &v79;
      let v91 = dedup_step(A, v83, v84);
      v91
    }
  };
  let v94: Rc<dyn Fn(u64, (Rc<Array<u64>>, u64)) -> (Rc<Array<u64>>, u64)> = Rc::new(v80);
  let v99 = 0u64;
  let v100 = &A_1;
  let v103 = rocq_array::get::<u64>(&v100, v99);
  let v108 = rocq_array::make::<u64>(n, v103);
  let v127 = loop_::<(Rc<Array<u64>>, u64)>(n, v76, v94, 1u64, (v108, 1u64));
  match v127 {
    (v129, v131) => {
      let m = &v129;
      match ltb(v131, 2u64) {
        true => {
          std::mem::drop(x);
          std::mem::drop(y);
          std::mem::drop(A_1);
          std::mem::drop(v129);
          0u64
        },
        false => {
          let v148 = {
            move |_v149: u64, v150: Rc<Array<u64>>| -> bool {
              std::mem::drop(v150);
              true
            }
          };
          let v155: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v148);
          let v156: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v155;
          let v158 = Rc::clone(m);
          let v161 = {
            let __anf_capture_164 = v131;
            move |v166: u64, v167: Rc<Array<u64>>| -> Rc<Array<u64>> {
              let v170 = Rc::clone(&v158);
              let v172 = Clone::clone(&__anf_capture_164);
              neg_step(v170, v172, v166, v167)
            }
          };
          let v180: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v161);
          let v190 = rocq_array::make::<u64>(v131, 0u64);
          let Q2 = loop_::<Rc<Array<u64>>>(v131, v156, v180, 0u64, v190);
          let v207 = chain(v129, v131);
          match v207 {
            (v209, v211) => {
              std::mem::drop(x);
              std::mem::drop(y);
              std::mem::drop(A_1);
              let v218 = chain(Q2, v131);
              match v218 {
                (v220, v222) => {
                  calipers(v209, v220, sub(v211, 1u64), sub(v222, 1u64))
                },
              }
            },
          }
        },
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64 = roberthood;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>) -> f64> = Rc::new(v0);
  v1
}
const __rocq_global_654: u64 = 4098000u64;