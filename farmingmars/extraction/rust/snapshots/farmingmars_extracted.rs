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

// Rocq: Farmingmars.farmingmars_implem.farmingmars
// Variant: uncurried
pub fn farmingmars() -> Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> {
  let v0: fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>> = farm;
  let v1: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = Rc::new(v0);
  v1
}

// Rocq: Farmingmars.farmingmars_implem.farmingmars
pub fn farmingmars_curried() -> Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> {
  let v0: fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>> = farm_curried;
  let v1: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Farmingmars.farmingmars_implem.bdec
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

// Rocq: Farmingmars.farmingmars_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Farmingmars.farmingmars_implem.wloop (local: wloop)
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

// Rocq: Farmingmars.farmingmars_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Farmingmars.farmingmars_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(le: &Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> bool>>, src: &Rc<Array<u64>>, mid: u64, hi: u64, k: u64, st: ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v11, v13) => {
      match v11 {
        (v16, v18) => {
          match ltb(v16, mid_1) {
            true => {
              match ltb(v18, hi_1) {
                true => {
                  let v34 = src;
                  let v41: Rc<dyn Fn(u64) -> bool> = le(rocq_array::get::<u64>(&v34, v16));
                  let v42 = src;
                  let v45 = rocq_array::get::<u64>(&v42, v18);
                  let v46: &Rc<dyn Fn(u64) -> bool> = &v41;
                  let v49 = v46(v45);
                  match v49 {
                    true => {
                      std::mem::drop(v41);
                      let v63 = (add(v16, 1u64), v18);
                      let v65 = src;
                      let v75 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(&v65, v16));
                      (v63, v75)
                    },
                    false => {
                      std::mem::drop(v41);
                      let v96 = (v16, add(v18, 1u64));
                      let v98 = src;
                      let v108 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(&v98, v18));
                      (v96, v108)
                    },
                  }
                },
                false => {
                  let v132 = (add(v16, 1u64), v18);
                  let v134 = src;
                  let v144 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(&v134, v16));
                  (v132, v144)
                },
              }
            },
            false => {
              let v168 = (v16, add(v18, 1u64));
              let v170 = src;
              let v180 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(&v170, v18));
              (v168, v180)
            },
          }
        },
      }
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.merge
// Variant: uncurried
pub fn merge(le: Rc<dyn Fn(u64, u64) -> bool>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64) -> Rc<Array<u64>> {
  let v8 = {
    move |v11: u64| -> Rc<dyn Fn(u64) -> bool> {
      let le = &le;
      let v12: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
      let v16 = {
        move |v21: u64| -> bool {
          let le = &v12;
          let v23 = Clone::clone(&v11);
          le(v23, v21)
        }
      };
      let v29: Rc<dyn Fn(u64) -> bool> = Rc::new(v16);
      v29
    }
  };
  let v33: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> bool>> = Rc::new(v8);
  let le_1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> bool>> = v33;
  let v37 = {
    move |_v38: u64, v39: ((u64, u64), Rc<Array<u64>>)| -> bool {
      std::mem::drop(v39);
      true
    }
  };
  let v44: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = Rc::new(v37);
  let v45: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = v44;
  let v54 = {
    let __anf_capture_59 = mid;
    let __anf_capture_61 = hi;
    move |v63: u64, v64: ((u64, u64), Rc<Array<u64>>)| -> ((u64, u64), Rc<Array<u64>>) {
      let le = &le_1;
      let src = &src;
      let v76 = merge_step(le, src, Clone::clone(&__anf_capture_59), Clone::clone(&__anf_capture_61), v63, v64);
      v76
    }
  };
  let v79: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>)> = Rc::new(v54);
  let v85 = (lo, mid);
  snd::<(u64, u64), Rc<Array<u64>>>(loop_::<((u64, u64), Rc<Array<u64>>)>(hi, v45, v79, lo, (v85, dst)))
}

// Rocq: Farmingmars.farmingmars_implem.seg_mid
// Variant: uncurried
pub fn seg_mid(n: u64, w: u64, lo: u64) -> u64 {
  let v10 = add(lo, w);
  match ltb(v10, n) {
    true => {
      add(lo, w)
    },
    false => {
      n
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.pass
// Variant: uncurried
pub fn pass(le: Rc<dyn Fn(u64, u64) -> bool>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let w2 = add(w, w);
  let v31 = div(sub(add(n, w2), 1u64), w2);
  let v32 = {
    move |_v33: u64, v34: Rc<Array<u64>>| -> bool {
      std::mem::drop(v34);
      true
    }
  };
  let v39: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v32);
  let v40: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v39;
  let v51 = {
    let __anf_capture_52 = w;
    let __anf_capture_54 = n;
    let __anf_capture_56 = w2;
    move |s: u64, d: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let w = &__anf_capture_52;
      let n = &__anf_capture_54;
      let w2 = &__anf_capture_56;
      let le = &le;
      let src = &src;
      let lo = mul(s, Clone::clone(w2));
      let v78 = seg_mid(Clone::clone(n), Clone::clone(w), lo);
      let v86 = seg_mid(Clone::clone(n), Clone::clone(w2), lo);
      let v87: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
      let v90 = Rc::clone(src);
      merge(v87, v90, d, lo, v78, v86)
    }
  };
  let v102: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v51);
  loop_::<Rc<Array<u64>>>(v31, v40, v102, 0u64, dst)
}

// Rocq: Farmingmars.farmingmars_implem.iota
pub fn iota(n: u64) -> Rc<Array<u64>> {
  let v2 = {
    move |_v3: u64, v4: Rc<Array<u64>>| -> bool {
      std::mem::drop(v4);
      true
    }
  };
  let v9: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v2);
  let v10: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v9;
  let v11 = {
    move |i: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
      rocq_array::set::<u64>(a, i, i)
    }
  };
  let v23: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v11);
  let v33 = rocq_array::make::<u64>(n, 0u64);
  loop_::<Rc<Array<u64>>>(n, v10, v23, 0u64, v33)
}

// Rocq: Farmingmars.farmingmars_implem.msort
// Variant: uncurried
pub fn msort(le: Rc<dyn Fn(u64, u64) -> bool>, n: u64) -> Rc<Array<u64>> {
  let v6 = 23u64;
  let v9 = {
    let __anf_capture_10 = n;
    move |_v12: u64, st: ((u64, Rc<Array<u64>>), Rc<Array<u64>>)| -> bool {
      let n = &__anf_capture_10;
      let v23 = fst::<u64, Rc<Array<u64>>>(fst::<(u64, Rc<Array<u64>>), Rc<Array<u64>>>(st));
      let v26 = Clone::clone(n);
      ltb(v23, v26)
    }
  };
  let v30: Rc<dyn Fn(u64, ((u64, Rc<Array<u64>>), Rc<Array<u64>>)) -> bool> = Rc::new(v9);
  let v31: Rc<dyn Fn(u64, ((u64, Rc<Array<u64>>), Rc<Array<u64>>)) -> bool> = v30;
  let v36 = {
    let __anf_capture_39 = n;
    move |_v41: u64, st: ((u64, Rc<Array<u64>>), Rc<Array<u64>>)| -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
      let le = &le;
      let n = &__anf_capture_39;
      match st {
        (v44, v46) => {
          match v44 {
            (v49, v51) => {
              let w = &v51;
              let v59 = add(v49, v49);
              let v61: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
              let v64 = Clone::clone(n);
              let v68 = Rc::clone(w);
              let v71 = pass(v61, v64, v49, v68, v46);
              ((v59, v71), v51)
            },
          }
        },
      }
    }
  };
  let v92: Rc<dyn Fn(u64, ((u64, Rc<Array<u64>>), Rc<Array<u64>>)) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>)> = Rc::new(v36);
  let v101 = iota(n);
  let v106 = (1u64, v101);
  let v114 = rocq_array::make::<u64>(n, 0u64);
  snd::<u64, Rc<Array<u64>>>(fst::<(u64, Rc<Array<u64>>), Rc<Array<u64>>>(loop_::<((u64, Rc<Array<u64>>), Rc<Array<u64>>)>(v6, v31, v92, 0u64, (v106, v114))))
}

// Rocq: Corelib.Floats.PrimFloat.leb
// Variant: uncurried
pub fn leb(v0: f64, v1: f64) -> bool {
  rocq_float64::leb(v0, v1)
}

// Rocq: Corelib.Floats.PrimFloat.ltb
// Variant: uncurried
pub fn ltb_1(v0: f64, v1: f64) -> bool {
  rocq_float64::ltb(v0, v1)
}

// Rocq: Farmingmars.farmingmars_implem.bs
// Variant: borrowed, uncurried
pub fn bs_1(p: &Rc<Array<f64>>, P: &Rc<Array<u64>>, v: f64, lo: u64, hi: u64) -> u64 {
  let v_1 = v;
  let lo_1 = lo;
  let hi_1 = hi;
  bs(p, P, v_1, lo_1, hi_1, ())
}

// Rocq: Farmingmars.farmingmars_implem.bs (local: bs)
// Variant: borrowed, uncurried, lifted
pub fn bs(p: &Rc<Array<f64>>, P: &Rc<Array<u64>>, v: f64, lo: u64, hi: u64, _H: ()) -> u64 {
  let v_1 = v;
  let lo_1 = lo;
  let hi_1 = hi;
  let v16 = ltb(lo_1, hi_1);
  match bdec(v16) {
    sumbool::left => {
      let v28 = sub(hi_1, lo_1);
      let v40 = add(lo_1, div(v28, 2u64));
      let v41 = P;
      let v44 = rocq_array::get::<u64>(&v41, v40);
      let v45 = p;
      let v49 = rocq_array::get::<f64>(&v45, v44);
      match ltb_1(v49, v_1) {
        true => {
          let v63 = sub(hi_1, lo_1);
          let v75 = add(lo_1, div(v63, 2u64));
          bs(p, P, v_1, add(v75, 1u64), hi_1, ())
        },
        false => {
          let v108 = sub(hi_1, lo_1);
          let v120 = add(lo_1, div(v108, 2u64));
          bs(p, P, v_1, lo_1, v120, ())
        },
      }
    },
    sumbool::right => {
      lo_1
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.lbound
// Variant: borrowed, uncurried
pub fn lbound(p: &Rc<Array<f64>>, P: &Rc<Array<u64>>, n: u64, v: f64) -> u64 {
  let n_1 = n;
  let v_1 = v;
  bs_1(p, P, v_1, 0u64, n_1)
}

// Rocq: Farmingmars.farmingmars_implem.mk_ids
// Variant: uncurried
pub fn mk_ids(p: Rc<Array<f64>>, P: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let v4 = {
    move |_v5: u64, v6: Rc<Array<u64>>| -> bool {
      std::mem::drop(v6);
      true
    }
  };
  let v11: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(v4);
  let v12: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = v11;
  let v19 = {
    let __anf_capture_24 = n;
    move |i: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let p = &p;
      let P = &P;
      let n = &__anf_capture_24;
      let v30 = rocq_array::get::<f64>(&p, i);
      let v38 = lbound(p, P, Clone::clone(n), v30);
      rocq_array::set::<u64>(a, i, v38)
    }
  };
  let v48: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v19);
  let v58 = rocq_array::make::<u64>(n, 0u64);
  loop_::<Rc<Array<u64>>>(n, v12, v48, 0u64, v58)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb_1(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Farmingmars.farmingmars_implem.mo_le
// Variant: borrowed, uncurried
pub fn mo_le(ls: &Rc<Array<u64>>, rs: &Rc<Array<u64>>, B: u64, a: u64, b: u64) -> bool {
  let B_1 = B;
  let a_1 = a;
  let b_1 = b;
  let v10 = ls;
  let ba = div(sub(rocq_array::get::<u64>(&v10, a_1), 1u64), B_1);
  let v28 = ls;
  let bb = div(sub(rocq_array::get::<u64>(&v28, b_1), 1u64), B_1);
  match ltb(ba, bb) {
    true => {
      true
    },
    false => {
      match ltb(bb, ba) {
        true => {
          false
        },
        false => {
          let v67 = rs;
          let v70 = rocq_array::get::<u64>(&v67, a_1);
          let v71 = rs;
          leb_1(v70, rocq_array::get::<u64>(&v71, b_1))
        },
      }
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.blk
pub fn blk(n: u64) -> u64 {
  let v4 = {
    let __anf_capture_5 = n;
    move |_v7: u64, b: u64| -> bool {
      let n = &__anf_capture_5;
      let v16 = mul(b, b);
      let v19 = Clone::clone(n);
      ltb(v16, v19)
    }
  };
  let v23: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v4);
  let v24: Rc<dyn Fn(u64, u64) -> bool> = v23;
  let v25 = {
    move |_v26: u64, b: u64| -> u64 {
      add(b, 1u64)
    }
  };
  let v38: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v25);
  loop_::<u64>(n, v24, v38, 0u64, 1u64)
}

// Rocq: Farmingmars.farmingmars_implem.add
// Variant: uncurried
pub fn add_1(ids: Rc<Array<u64>>, pos: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v4 = &ids;
  let v = rocq_array::get::<u64>(&v4, pos);
  std::mem::drop(ids);
  let v9 = &cnt;
  let v12 = rocq_array::get::<u64>(&v9, v);
  let c = add(v12, 1u64);
  let v26 = rocq_array::set::<u64>(cnt, v, c);
  let v28 = &ge;
  let v31 = rocq_array::get::<u64>(&v28, c);
  let v45 = rocq_array::set::<u64>(ge, c, add(v31, 1u64));
  (v26, v45)
}

// Rocq: Farmingmars.farmingmars_implem.rem
// Variant: uncurried
pub fn rem(ids: Rc<Array<u64>>, pos: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v4 = &ids;
  let v = rocq_array::get::<u64>(&v4, pos);
  std::mem::drop(ids);
  let v8 = &cnt;
  let c = rocq_array::get::<u64>(&v8, v);
  let v26 = rocq_array::set::<u64>(cnt, v, sub(c, 1u64));
  let v28 = &ge;
  let v31 = rocq_array::get::<u64>(&v28, c);
  let v45 = rocq_array::set::<u64>(ge, c, sub(v31, 1u64));
  (v26, v45)
}

// Rocq: Farmingmars.farmingmars_implem.move
// Variant: uncurried
pub fn move__1(ids: Rc<Array<u64>>, tl: u64, tr: u64, L: u64, R: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  move_(ids, tl, tr, L, R, cnt, ge, ())
}

// Rocq: Farmingmars.farmingmars_implem.move (local: move)
// Variant: uncurried, lifted
pub fn move_(ids: Rc<Array<u64>>, tl: u64, tr: u64, L: u64, R: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>, _H: ()) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  let v15 = ltb(tl, L);
  match bdec(v15) {
    sumbool::left => {
      let v27 = sub(L, 1u64);
      let v30 = Rc::clone(&ids);
      let v37 = add_1(v30, v27, cnt, ge);
      match v37 {
        (v39, v41) => {
          move_(ids, tl, tr, sub(L, 1u64), R, v39, v41, ())
        },
      }
    },
    sumbool::right => {
      let v83 = ltb(R, tr);
      match bdec(v83) {
        sumbool::left => {
          let v90 = Rc::clone(&ids);
          let v97 = add_1(v90, R, cnt, ge);
          match v97 {
            (v99, v101) => {
              move_(ids, tl, tr, L, add(R, 1u64), v99, v101, ())
            },
          }
        },
        sumbool::right => {
          let v143 = ltb(L, tl);
          match bdec(v143) {
            sumbool::left => {
              let v150 = Rc::clone(&ids);
              let v157 = rem(v150, L, cnt, ge);
              match v157 {
                (v159, v161) => {
                  move_(ids, tl, tr, add(L, 1u64), R, v159, v161, ())
                },
              }
            },
            sumbool::right => {
              let v203 = ltb(tr, R);
              match bdec(v203) {
                sumbool::left => {
                  let v215 = sub(R, 1u64);
                  let v218 = Rc::clone(&ids);
                  let v225 = rem(v218, v215, cnt, ge);
                  match v225 {
                    (v227, v229) => {
                      move_(ids, tl, tr, L, sub(R, 1u64), v227, v229, ())
                    },
                  }
                },
                sumbool::right => {
                  std::mem::drop(ids);
                  (((L, R), cnt), ge)
                },
              }
            },
          }
        },
      }
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.mo_step
// Variant: borrowed, uncurried
pub fn mo_step(ids: &Rc<Array<u64>>, ls: &Rc<Array<u64>>, rs: &Rc<Array<u64>>, Q: &Rc<Array<u64>>, k: u64, st: ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>) {
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v9, v11) => {
      match v9 {
        (v14, v16) => {
          let ge = &v14;
          match ge {
            (cnt, p1) => {
              match cnt {
                (R, L) => {
                  let v29 = Q;
                  let q = rocq_array::get::<u64>(&v29, k_1);
                  let v34 = ls;
                  let tl = sub(rocq_array::get::<u64>(&v34, q), 1u64);
                  let v45 = rs;
                  let tr = rocq_array::get::<u64>(&v45, q);
                  let v52 = Rc::clone(ids);
                  let v58 = Clone::clone(R);
                  let v60 = Clone::clone(L);
                  let v61 = Rc::clone(p1);
                  std::mem::drop(v14);
                  let v65 = move__1(v52, tl, tr, v58, v60, v61, v16);
                  match v65 {
                    (v67, v69) => {
                      let p = &v69;
                      match v67 {
                        (v73, v75) => {
                          match v73 {
                            (v78, v80) => {
                              let v92 = ((v78, v80), v75);
                              let v97 = Rc::clone(p);
                              let v99 = (v92, v97);
                              let v102 = 0u64;
                              let v125 = add(div(sub(tr, tl), 2u64), 1u64);
                              let v127 = rocq_array::get::<u64>(&p, v125);
                              std::mem::drop(v69);
                              let v139 = rocq_array::set::<bool>(v11, q, ltb(v102, v127));
                              (v99, v139)
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

// Rocq: Farmingmars.farmingmars_implem.farm
// Variant: uncurried
pub fn farm(p: Rc<Array<f64>>, ls: Rc<Array<u64>>, rs: Rc<Array<u64>>) -> Rc<Array<bool>> {
  let v3 = &p;
  let n = rocq_array::length::<f64>(&v3);
  let v5 = &ls;
  let m = rocq_array::length::<u64>(&v5);
  let v10 = Rc::clone(&p);
  let v11 = {
    move |a: u64, b: u64| -> bool {
      let p = &v10;
      let v19 = rocq_array::get::<f64>(&p, a);
      let v22 = rocq_array::get::<f64>(&p, b);
      leb(v19, v22)
    }
  };
  let v30: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v11);
  let P = msort(v30, n);
  let ids = mk_ids(p, P, n);
  let v49 = blk(n);
  let v52 = Rc::clone(&ls);
  let v55 = Rc::clone(&rs);
  let v58 = {
    move |v65: u64, v66: u64| -> bool {
      let ls = &v52;
      let rs = &v55;
      let v68 = Clone::clone(&v49);
      mo_le(ls, rs, v68, v65, v66)
    }
  };
  let v79: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v58);
  let Q = msort(v79, m);
  let v88 = {
    move |_v89: u64, v90: ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)| -> bool {
      std::mem::drop(v90);
      true
    }
  };
  let v95: Rc<dyn Fn(u64, ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> bool> = Rc::new(v88);
  let v96: Rc<dyn Fn(u64, ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> bool> = v95;
  let v105 = {
    let __anf_capture_108 = ls;
    let __anf_capture_110 = rs;
    move |v114: u64, v115: ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)| -> ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>) {
      let ids = &ids;
      let ls = &__anf_capture_108;
      let rs = &__anf_capture_110;
      let Q = &Q;
      let v125 = mo_step(ids, ls, rs, Q, v114, v115);
      v125
    }
  };
  let v128: Rc<dyn Fn(u64, ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)> = Rc::new(v105);
  let v140 = (0u64, 0u64);
  let v148 = rocq_array::make::<u64>(n, 0u64);
  let v153 = (v140, v148);
  let v169 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v174 = (v153, v169);
  let v182 = rocq_array::make::<bool>(m, false);
  snd::<(((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>>(loop_::<((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)>(m, v96, v128, 0u64, (v174, v182)))
}

// Rocq: Farmingmars.farmingmars_implem.farm
pub fn farm_curried(p: Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>> {
  let v3 = {
    move |ls: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>> {
      let p = &p;
      let v8 = Rc::clone(p);
      let v11 = {
        move |rs: Rc<Array<u64>>| -> Rc<Array<bool>> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&ls);
          farm(v19, v21, rs)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> {
  let v0: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = __rocq_global_1291.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1291: Rc<dyn Fn(Rc<Array<f64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<bool>>> = farmingmars(); }
std::thread_local! { static __rocq_global_1294: Rc<dyn Fn(Rc<Array<f64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<bool>>>>> = farmingmars_curried(); }