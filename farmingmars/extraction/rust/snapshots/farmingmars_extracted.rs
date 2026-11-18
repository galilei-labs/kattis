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

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Farmingmars.farmingmars_implem.bdec
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

// Rocq: Farmingmars.farmingmars_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: u64, cont: Rc<dyn Fn(u64, St) -> bool>, f: Rc<dyn Fn(u64, St) -> St>, i: u64, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Farmingmars.farmingmars_implem.wloop (local: wloop)
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
          if ltb(v16, mid_1) {
            if ltb(v18, hi_1) {
              let tmp: Rc<dyn Fn(u64) -> bool> = le(rocq_array::get::<u64>(src, v16));
              let tmp_1 = rocq_array::get::<u64>(src, v18);
              let tmp_2: &Rc<dyn Fn(u64) -> bool> = &tmp;
              let tmp_3 = tmp_2(tmp_1);
              if tmp_3 {
                std::mem::drop(tmp);
                let tmp_4 = (add(v16, 1u64), v18);
                let tmp_5 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(src, v16));
                (tmp_4, tmp_5)
              } else {
                std::mem::drop(tmp);
                let tmp_6 = (v16, add(v18, 1u64));
                let tmp_7 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(src, v18));
                (tmp_6, tmp_7)
              }
            } else {
              let tmp_8 = (add(v16, 1u64), v18);
              let tmp_9 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(src, v16));
              (tmp_8, tmp_9)
            }
          } else {
            let tmp_10 = (v16, add(v18, 1u64));
            let tmp_11 = rocq_array::set::<u64>(v13, k_1, rocq_array::get::<u64>(src, v18));
            (tmp_10, tmp_11)
          }
        },
      }
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.merge
// Variant: uncurried
pub fn merge(le: Rc<dyn Fn(u64, u64) -> bool>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, lo: u64, mid: u64, hi: u64) -> Rc<Array<u64>> {
  let le_1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> bool>> = Rc::new({
    move |v11: u64| -> Rc<dyn Fn(u64) -> bool> {
      let le = &le;
      let le_clone: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
      let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
        move |v21: u64| -> bool {
          let le = &le_clone;
          let tmp = Clone::clone(&v11);
          le(tmp, v21)
        }
      });
      callback
    }
  });
  let callback_1: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> bool> = Rc::new(move |_v38: u64, v39: ((u64, u64), Rc<Array<u64>>)| -> bool {
    std::mem::drop(v39);
    true
  });
  let callback_2: Rc<dyn Fn(u64, ((u64, u64), Rc<Array<u64>>)) -> ((u64, u64), Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_59 = mid;
    let __anf_capture_61 = hi;
    move |v63: u64, v64: ((u64, u64), Rc<Array<u64>>)| -> ((u64, u64), Rc<Array<u64>>) {
      let le = &le_1;
      let src = &src;
      let tmp_1 = merge_step(le, src, Clone::clone(&__anf_capture_59), Clone::clone(&__anf_capture_61), v63, v64);
      tmp_1
    }
  });
  let tmp_2 = (lo, mid);
  snd::<(u64, u64), Rc<Array<u64>>>(loop_::<((u64, u64), Rc<Array<u64>>)>(hi, callback_1, callback_2, lo, (tmp_2, dst)))
}

// Rocq: Farmingmars.farmingmars_implem.seg_mid
// Variant: uncurried
pub fn seg_mid(n: u64, w: u64, lo: u64) -> u64 {
  let tmp = add(lo, w);
  if ltb(tmp, n) {
    add(lo, w)
  } else {
    n
  }
}

// Rocq: Farmingmars.farmingmars_implem.pass
// Variant: uncurried
pub fn pass(le: Rc<dyn Fn(u64, u64) -> bool>, n: u64, w: u64, src: Rc<Array<u64>>, dst: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let w2 = add(w, w);
  let tmp = div(sub(add(n, w2), 1u64), w2);
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v33: u64, v34: Rc<Array<u64>>| -> bool {
    std::mem::drop(v34);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
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
      let tmp_1 = seg_mid(Clone::clone(n), Clone::clone(w), lo);
      let tmp_2 = seg_mid(Clone::clone(n), Clone::clone(w2), lo);
      let le_clone: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
      let src_clone = Rc::clone(src);
      merge(le_clone, src_clone, d, lo, tmp_1, tmp_2)
    }
  });
  loop_::<Rc<Array<u64>>>(tmp, callback, callback_1, 0u64, dst)
}

// Rocq: Farmingmars.farmingmars_implem.iota
pub fn iota(n: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v3: u64, v4: Rc<Array<u64>>| -> bool {
    std::mem::drop(v4);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(move |i: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
    rocq_array::set::<u64>(a, i, i)
  });
  let tmp = rocq_array::make::<u64>(n, 0u64);
  loop_::<Rc<Array<u64>>>(n, callback, callback_1, 0u64, tmp)
}

// Rocq: Farmingmars.farmingmars_implem.msort
// Variant: uncurried
pub fn msort(le: Rc<dyn Fn(u64, u64) -> bool>, n: u64) -> Rc<Array<u64>> {
  let tmp = 23u64;
  let callback: Rc<dyn Fn(u64, ((u64, Rc<Array<u64>>), Rc<Array<u64>>)) -> bool> = Rc::new({
    let __anf_capture_10 = n;
    move |_v12: u64, st: ((u64, Rc<Array<u64>>), Rc<Array<u64>>)| -> bool {
      let n = &__anf_capture_10;
      let tmp_1 = fst::<u64, Rc<Array<u64>>>(fst::<(u64, Rc<Array<u64>>), Rc<Array<u64>>>(st));
      let n_clone = Clone::clone(n);
      ltb(tmp_1, n_clone)
    }
  });
  let callback_1: Rc<dyn Fn(u64, ((u64, Rc<Array<u64>>), Rc<Array<u64>>)) -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>)> = Rc::new({
    let __anf_capture_39 = n;
    move |_v41: u64, st: ((u64, Rc<Array<u64>>), Rc<Array<u64>>)| -> ((u64, Rc<Array<u64>>), Rc<Array<u64>>) {
      let le = &le;
      let n = &__anf_capture_39;
      match st {
        (v44, v46) => {
          match v44 {
            (v49, v51) => {
              let w = &v51;
              let tmp_2 = add(v49, v49);
              let le_clone: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(le);
              let n_clone_1 = Clone::clone(n);
              let w_clone = Rc::clone(w);
              let tmp_3 = pass(le_clone, n_clone_1, v49, w_clone, v46);
              ((tmp_2, tmp_3), v51)
            },
          }
        },
      }
    }
  });
  let tmp_4 = iota(n);
  let tmp_5 = (1u64, tmp_4);
  let tmp_6 = rocq_array::make::<u64>(n, 0u64);
  snd::<u64, Rc<Array<u64>>>(fst::<(u64, Rc<Array<u64>>), Rc<Array<u64>>>(loop_::<((u64, Rc<Array<u64>>), Rc<Array<u64>>)>(tmp, callback, callback_1, 0u64, (tmp_5, tmp_6))))
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
  let tmp = ltb(lo_1, hi_1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(hi_1, lo_1);
      let tmp_2 = rocq_array::get::<f64>(p, rocq_array::get::<u64>(P, add(lo_1, div(tmp_1, 2u64))));
      if ltb_1(tmp_2, v_1) {
        let tmp_3 = sub(hi_1, lo_1);
        let tmp_4 = add(lo_1, div(tmp_3, 2u64));
        bs(p, P, v_1, add(tmp_4, 1u64), hi_1, ())
      } else {
        let tmp_5 = sub(hi_1, lo_1);
        let tmp_6 = add(lo_1, div(tmp_5, 2u64));
        bs(p, P, v_1, lo_1, tmp_6, ())
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
  let callback: Rc<dyn Fn(u64, Rc<Array<u64>>) -> bool> = Rc::new(move |_v5: u64, v6: Rc<Array<u64>>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(u64, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new({
    let __anf_capture_24 = n;
    move |i: u64, a: Rc<Array<u64>>| -> Rc<Array<u64>> {
      let p = &p;
      let P = &P;
      let n = &__anf_capture_24;
      let tmp = rocq_array::get::<f64>(p, i);
      let tmp_1 = lbound(p, P, Clone::clone(n), tmp);
      rocq_array::set::<u64>(a, i, tmp_1)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  loop_::<Rc<Array<u64>>>(n, callback, callback_1, 0u64, tmp_2)
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
  let ba = div(sub(rocq_array::get::<u64>(ls, a_1), 1u64), B_1);
  let bb = div(sub(rocq_array::get::<u64>(ls, b_1), 1u64), B_1);
  if ltb(ba, bb) {
    true
  } else {
    if ltb(bb, ba) {
      false
    } else {
      leb_1(rocq_array::get::<u64>(rs, a_1), rocq_array::get::<u64>(rs, b_1))
    }
  }
}

// Rocq: Farmingmars.farmingmars_implem.blk
pub fn blk(n: u64) -> u64 {
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    let __anf_capture_5 = n;
    move |_v7: u64, b: u64| -> bool {
      let n = &__anf_capture_5;
      let tmp = mul(b, b);
      let n_clone = Clone::clone(n);
      ltb(tmp, n_clone)
    }
  });
  let callback_1: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(move |_v26: u64, b: u64| -> u64 {
    add(b, 1u64)
  });
  loop_::<u64>(n, callback, callback_1, 0u64, 1u64)
}

// Rocq: Farmingmars.farmingmars_implem.add
// Variant: uncurried
pub fn add_1(ids: Rc<Array<u64>>, pos: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v = rocq_array::get::<u64>(&ids, pos);
  std::mem::drop(ids);
  let tmp = rocq_array::get::<u64>(&cnt, v);
  let c = add(tmp, 1u64);
  let tmp_1 = rocq_array::set::<u64>(cnt, v, c);
  let tmp_2 = rocq_array::get::<u64>(&ge, c);
  let tmp_3 = rocq_array::set::<u64>(ge, c, add(tmp_2, 1u64));
  (tmp_1, tmp_3)
}

// Rocq: Farmingmars.farmingmars_implem.rem
// Variant: uncurried
pub fn rem(ids: Rc<Array<u64>>, pos: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v = rocq_array::get::<u64>(&ids, pos);
  std::mem::drop(ids);
  let c = rocq_array::get::<u64>(&cnt, v);
  let tmp = rocq_array::set::<u64>(cnt, v, sub(c, 1u64));
  let tmp_1 = rocq_array::get::<u64>(&ge, c);
  let tmp_2 = rocq_array::set::<u64>(ge, c, sub(tmp_1, 1u64));
  (tmp, tmp_2)
}

// Rocq: Farmingmars.farmingmars_implem.move
// Variant: uncurried
pub fn move__1(ids: Rc<Array<u64>>, tl: u64, tr: u64, L: u64, R: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  move_(ids, tl, tr, L, R, cnt, ge, ())
}

// Rocq: Farmingmars.farmingmars_implem.move (local: move)
// Variant: uncurried, lifted
pub fn move_(ids: Rc<Array<u64>>, tl: u64, tr: u64, L: u64, R: u64, cnt: Rc<Array<u64>>, ge: Rc<Array<u64>>, _H: ()) -> (((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(tl, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(L, 1u64);
      let ids_clone = Rc::clone(&ids);
      let tmp_2 = add_1(ids_clone, tmp_1, cnt, ge);
      match tmp_2 {
        (v39, v41) => {
          move_(ids, tl, tr, sub(L, 1u64), R, v39, v41, ())
        },
      }
    },
    sumbool::right => {
      let tmp_3 = ltb(R, tr);
      match bdec(tmp_3) {
        sumbool::left => {
          let ids_clone_1 = Rc::clone(&ids);
          let tmp_4 = add_1(ids_clone_1, R, cnt, ge);
          match tmp_4 {
            (v99, v101) => {
              move_(ids, tl, tr, L, add(R, 1u64), v99, v101, ())
            },
          }
        },
        sumbool::right => {
          let tmp_5 = ltb(L, tl);
          match bdec(tmp_5) {
            sumbool::left => {
              let ids_clone_2 = Rc::clone(&ids);
              let tmp_6 = rem(ids_clone_2, L, cnt, ge);
              match tmp_6 {
                (v159, v161) => {
                  move_(ids, tl, tr, add(L, 1u64), R, v159, v161, ())
                },
              }
            },
            sumbool::right => {
              let tmp_7 = ltb(tr, R);
              match bdec(tmp_7) {
                sumbool::left => {
                  let tmp_8 = sub(R, 1u64);
                  let ids_clone_3 = Rc::clone(&ids);
                  let tmp_9 = rem(ids_clone_3, tmp_8, cnt, ge);
                  match tmp_9 {
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
                  let q = rocq_array::get::<u64>(Q, k_1);
                  let tl = sub(rocq_array::get::<u64>(ls, q), 1u64);
                  let tr = rocq_array::get::<u64>(rs, q);
                  let ids_clone = Rc::clone(ids);
                  let R_clone = Clone::clone(R);
                  let L_clone = Clone::clone(L);
                  let p1_clone = Rc::clone(p1);
                  std::mem::drop(v14);
                  let tmp = move__1(ids_clone, tl, tr, R_clone, L_clone, p1_clone, v16);
                  match tmp {
                    (v67, v69) => {
                      let p = &v69;
                      match v67 {
                        (v73, v75) => {
                          match v73 {
                            (v78, v80) => {
                              let tmp_1 = ((v78, v80), v75);
                              let p_clone = Rc::clone(p);
                              let tmp_2 = (tmp_1, p_clone);
                              let tmp_3 = 0u64;
                              let tmp_4 = rocq_array::get::<u64>(p, add(div(sub(tr, tl), 2u64), 1u64));
                              std::mem::drop(v69);
                              let tmp_5 = rocq_array::set::<bool>(v11, q, ltb(tmp_3, tmp_4));
                              (tmp_2, tmp_5)
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
  let n = rocq_array::length::<f64>(&p);
  let m = rocq_array::length::<u64>(&ls);
  let p_clone = Rc::clone(&p);
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    move |a: u64, b: u64| -> bool {
      let tmp = rocq_array::get::<f64>(&p_clone, a);
      let tmp_1 = rocq_array::get::<f64>(&p_clone, b);
      leb(tmp, tmp_1)
    }
  });
  let P = msort(callback, n);
  let ids = mk_ids(p, P, n);
  let tmp_2 = blk(n);
  let ls_clone = Rc::clone(&ls);
  let rs_clone = Rc::clone(&rs);
  let callback_1: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    move |v65: u64, v66: u64| -> bool {
      let ls = &ls_clone;
      let rs = &rs_clone;
      let tmp_3 = Clone::clone(&tmp_2);
      mo_le(ls, rs, tmp_3, v65, v66)
    }
  });
  let Q = msort(callback_1, m);
  let callback_2: Rc<dyn Fn(u64, ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> bool> = Rc::new(move |_v89: u64, v90: ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)| -> bool {
    std::mem::drop(v90);
    true
  });
  let callback_3: Rc<dyn Fn(u64, ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)) -> ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)> = Rc::new({
    let __anf_capture_108 = ls;
    let __anf_capture_110 = rs;
    move |v114: u64, v115: ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)| -> ((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>) {
      let ids = &ids;
      let ls = &__anf_capture_108;
      let rs = &__anf_capture_110;
      let Q = &Q;
      let tmp_4 = mo_step(ids, ls, rs, Q, v114, v115);
      tmp_4
    }
  });
  let tmp_5 = (0u64, 0u64);
  let tmp_6 = rocq_array::make::<u64>(n, 0u64);
  let tmp_7 = (tmp_5, tmp_6);
  let tmp_8 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let tmp_9 = (tmp_7, tmp_8);
  let tmp_10 = rocq_array::make::<bool>(m, false);
  snd::<(((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>>(loop_::<((((u64, u64), Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<bool>>)>(m, callback_2, callback_3, 0u64, (tmp_9, tmp_10)))
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
