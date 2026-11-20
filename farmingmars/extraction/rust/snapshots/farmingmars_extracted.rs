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

pub type uint = Int63;

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

// Rocq: Farmingmars.farmingmars_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Farmingmars.farmingmars_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, cont, f, i, s, ())
}

// Rocq: Farmingmars.farmingmars_implem.wloop (local: wloop)
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

// Rocq: Farmingmars.farmingmars_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, cont: Rc<dyn Fn(Int63, St) -> bool>, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, cont, f, i, s)
}

// Rocq: Farmingmars.farmingmars_implem.merge_step
// Variant: borrowed, uncurried
pub fn merge_step(le: &Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> bool>>, src: &Array<Int63>, mid: Int63, hi: Int63, k: Int63, st: ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>) {
  let mid_1 = mid;
  let hi_1 = hi;
  let k_1 = k;
  let st_1 = st;
  match st_1 {
    (v11, v13) => {
      match v11 {
        (v16, v18) => {
          if v16 < mid_1 {
            if v18 < hi_1 {
              let tmp: Rc<dyn Fn(Int63) -> bool> = le(src.get_cloned(v16));
              let tmp_1 = src.get_cloned(v18);
              let tmp_2: &Rc<dyn Fn(Int63) -> bool> = &tmp;
              let tmp_3 = tmp_2(tmp_1);
              if tmp_3 {
                std::mem::drop(tmp);
                ((v16 + int63!(1), v18), v13.set(k_1, src.get_cloned(v16)))
              } else {
                std::mem::drop(tmp);
                ((v16, v18 + int63!(1)), v13.set(k_1, src.get_cloned(v18)))
              }
            } else {
              ((v16 + int63!(1), v18), v13.set(k_1, src.get_cloned(v16)))
            }
          } else {
            ((v16, v18 + int63!(1)), v13.set(k_1, src.get_cloned(v18)))
          }
        },
      }
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.merge
// Variant: uncurried
pub fn merge(le: Rc<dyn Fn(Int63, Int63) -> bool>, src: Array<Int63>, dst: Array<Int63>, lo: Int63, mid: Int63, hi: Int63) -> Array<Int63> {
  let le_1: Rc<dyn Fn(Int63) -> Rc<dyn Fn(Int63) -> bool>> = Rc::new({
    move |v11: Int63| -> Rc<dyn Fn(Int63) -> bool> {
      let le = &le;
      let le_clone: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(le);
      let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
        move |v21: Int63| -> bool {
          let le = &le_clone;
          let tmp = Clone::clone(&v11);
          le(tmp, v21)
        }
      });
      callback
    }
  });
  let callback_1: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> bool> = Rc::new(move |_v38: Int63, v39: ((Int63, Int63), Array<Int63>)| -> bool {
    std::mem::drop(v39);
    true
  });
  let callback_2: Rc<dyn Fn(Int63, ((Int63, Int63), Array<Int63>)) -> ((Int63, Int63), Array<Int63>)> = Rc::new({
    let __anf_capture_59 = mid;
    let __anf_capture_61 = hi;
    move |v63: Int63, v64: ((Int63, Int63), Array<Int63>)| -> ((Int63, Int63), Array<Int63>) {
      let le = &le_1;
      let src = &src;
      let tmp_1 = merge_step(le, src, Clone::clone(&__anf_capture_59), Clone::clone(&__anf_capture_61), v63, v64);
      tmp_1
    }
  });
  let tmp_2 = (lo, mid);
  snd::<(Int63, Int63), Array<Int63>>(loop_::<((Int63, Int63), Array<Int63>)>(hi, callback_1, callback_2, lo, (tmp_2, dst)))
}

// Rocq: Farmingmars.farmingmars_implem.seg_mid
// Variant: uncurried
pub fn seg_mid(n: Int63, w: Int63, lo: Int63) -> Int63 {
  let tmp = lo + w;
  if tmp < n {
    lo + w
  } else {
    n
  }
}

// Rocq: Farmingmars.farmingmars_implem.pass
// Variant: uncurried
pub fn pass(le: Rc<dyn Fn(Int63, Int63) -> bool>, n: Int63, w: Int63, src: Array<Int63>, dst: Array<Int63>) -> Array<Int63> {
  let w2 = w + w;
  let tmp = (n + w2 - int63!(1)) / w2;
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v33: Int63, v34: Array<Int63>| -> bool {
    std::mem::drop(v34);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    let __anf_capture_52 = w;
    let __anf_capture_54 = n;
    let __anf_capture_56 = w2;
    move |s: Int63, d: Array<Int63>| -> Array<Int63> {
      let w = &__anf_capture_52;
      let n = &__anf_capture_54;
      let w2 = &__anf_capture_56;
      let le = &le;
      let src = &src;
      let lo = s * Clone::clone(w2);
      let tmp_1 = seg_mid(Clone::clone(n), Clone::clone(w), lo);
      let tmp_2 = seg_mid(Clone::clone(n), Clone::clone(w2), lo);
      let le_clone: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(le);
      let src_clone = Clone::clone(src);
      merge(le_clone, src_clone, d, lo, tmp_1, tmp_2)
    }
  });
  loop_::<Array<Int63>>(tmp, callback, callback_1, int63!(0), dst)
}

// Rocq: Farmingmars.farmingmars_implem.iota
pub fn iota(n: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v3: Int63, v4: Array<Int63>| -> bool {
    std::mem::drop(v4);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new(move |i: Int63, a_1: Array<Int63>| -> Array<Int63> {
    a_1.set(i, i)
  });
  let tmp = Array::<Int63>::make(n, int63!(0));
  loop_::<Array<Int63>>(n, callback, callback_1, int63!(0), tmp)
}

// Rocq: Farmingmars.farmingmars_implem.msort
// Variant: uncurried
pub fn msort(le: Rc<dyn Fn(Int63, Int63) -> bool>, n: Int63) -> Array<Int63> {
  let tmp = int63!(23);
  let callback: Rc<dyn Fn(Int63, ((Int63, Array<Int63>), Array<Int63>)) -> bool> = Rc::new({
    let __anf_capture_10 = n;
    move |_v12: Int63, st: ((Int63, Array<Int63>), Array<Int63>)| -> bool {
      let n = &__anf_capture_10;
      let tmp_1 = fst::<Int63, Array<Int63>>(fst::<(Int63, Array<Int63>), Array<Int63>>(st));
      let n_clone = Clone::clone(n);
      tmp_1 < n_clone
    }
  });
  let callback_1: Rc<dyn Fn(Int63, ((Int63, Array<Int63>), Array<Int63>)) -> ((Int63, Array<Int63>), Array<Int63>)> = Rc::new({
    let __anf_capture_39 = n;
    move |_v41: Int63, st: ((Int63, Array<Int63>), Array<Int63>)| -> ((Int63, Array<Int63>), Array<Int63>) {
      let le = &le;
      let n = &__anf_capture_39;
      match st {
        (v44, v46) => {
          match v44 {
            (v49, v51) => {
              let w = &v51;
              let tmp_2 = v49 + v49;
              let le_clone: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::clone(le);
              let n_clone_1 = Clone::clone(n);
              let w_clone = Clone::clone(w);
              ((tmp_2, pass(le_clone, n_clone_1, v49, w_clone, v46)), v51)
            },
          }
        },
      }
    }
  });
  snd::<Int63, Array<Int63>>(fst::<(Int63, Array<Int63>), Array<Int63>>(loop_::<((Int63, Array<Int63>), Array<Int63>)>(tmp, callback, callback_1, int63!(0), ((int63!(1), iota(n)), Array::<Int63>::make(n, int63!(0))))))
}

// Rocq: Farmingmars.farmingmars_implem.bs
// Variant: borrowed, uncurried
pub fn bs_1(p: &Array<f64>, P: &Array<Int63>, v: f64, lo: Int63, hi: Int63) -> Int63 {
  let v_1 = v;
  let lo_1 = lo;
  let hi_1 = hi;
  bs(p, P, v_1, lo_1, hi_1, ())
}

// Rocq: Farmingmars.farmingmars_implem.bs (local: bs)
// Variant: borrowed, uncurried, lifted
pub fn bs(p: &Array<f64>, P: &Array<Int63>, v: f64, lo: Int63, hi: Int63, _H: ()) -> Int63 {
  let v_1 = v;
  let lo_1 = lo;
  let hi_1 = hi;
  let tmp = lo_1 < hi_1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = hi_1 - lo_1;
      let tmp_2 = p.get_cloned(P.get_cloned(lo_1 + tmp_1 / int63!(2)));
      if rocq_float64::ltb(tmp_2, v_1) {
        let tmp_3 = hi_1 - lo_1;
        bs(p, P, v_1, lo_1 + tmp_3 / int63!(2) + int63!(1), hi_1, ())
      } else {
        let tmp_4 = hi_1 - lo_1;
        let tmp_5 = lo_1 + tmp_4 / int63!(2);
        bs(p, P, v_1, lo_1, tmp_5, ())
      }
    },
    sumbool::right => {
      lo_1
    },
  }
}

// Rocq: Farmingmars.farmingmars_implem.lbound
// Variant: borrowed, uncurried
pub fn lbound(p: &Array<f64>, P: &Array<Int63>, n: Int63, v: f64) -> Int63 {
  let n_1 = n;
  let v_1 = v;
  bs_1(p, P, v_1, int63!(0), n_1)
}

// Rocq: Farmingmars.farmingmars_implem.mk_ids
// Variant: uncurried
pub fn mk_ids(p: Array<f64>, P: Array<Int63>, n: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Array<Int63>) -> bool> = Rc::new(move |_v5: Int63, v6: Array<Int63>| -> bool {
    std::mem::drop(v6);
    true
  });
  let callback_1: Rc<dyn Fn(Int63, Array<Int63>) -> Array<Int63>> = Rc::new({
    let __anf_capture_24 = n;
    move |i: Int63, a_1: Array<Int63>| -> Array<Int63> {
      let p = &p;
      let P = &P;
      let n = &__anf_capture_24;
      let tmp = p.get_cloned(i);
      let tmp_1 = lbound(p, P, Clone::clone(n), tmp);
      a_1.set(i, tmp_1)
    }
  });
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  loop_::<Array<Int63>>(n, callback, callback_1, int63!(0), tmp_2)
}

// Rocq: Farmingmars.farmingmars_implem.mo_le
// Variant: borrowed, uncurried
pub fn mo_le(ls: &Array<Int63>, rs: &Array<Int63>, B: Int63, a_1: Int63, b_1: Int63) -> bool {
  let B_1 = B;
  let a_2 = a_1;
  let b_2 = b_1;
  let ba = (ls.get_cloned(a_2) - int63!(1)) / B_1;
  let bb = (ls.get_cloned(b_2) - int63!(1)) / B_1;
  if ba < bb {
    true
  } else {
    if bb < ba {
      false
    } else {
      rs.get_cloned(a_2) <= rs.get_cloned(b_2)
    }
  }
}

// Rocq: Farmingmars.farmingmars_implem.blk
pub fn blk(n: Int63) -> Int63 {
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    let __anf_capture_5 = n;
    move |_v7: Int63, b_1: Int63| -> bool {
      let n = &__anf_capture_5;
      let tmp = b_1 * b_1;
      let n_clone = Clone::clone(n);
      tmp < n_clone
    }
  });
  let callback_1: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new(move |_v26: Int63, b_1: Int63| -> Int63 {
    b_1 + int63!(1)
  });
  loop_::<Int63>(n, callback, callback_1, int63!(0), int63!(1))
}

// Rocq: Farmingmars.farmingmars_implem.add
// Variant: uncurried
pub fn add(ids: Array<Int63>, pos: Int63, cnt: Array<Int63>, ge: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let v = ids.get_cloned(pos);
  std::mem::drop(ids);
  let tmp = cnt.get_cloned(v);
  let c = tmp + int63!(1);
  let tmp_1 = cnt.set(v, c);
  let tmp_2 = ge.get_cloned(c);
  (tmp_1, ge.set(c, tmp_2 + int63!(1)))
}

// Rocq: Farmingmars.farmingmars_implem.rem
// Variant: uncurried
pub fn rem(ids: Array<Int63>, pos: Int63, cnt: Array<Int63>, ge: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let v = ids.get_cloned(pos);
  std::mem::drop(ids);
  let c = cnt.get_cloned(v);
  let tmp = cnt.set(v, c - int63!(1));
  let tmp_1 = ge.get_cloned(c);
  (tmp, ge.set(c, tmp_1 - int63!(1)))
}

// Rocq: Farmingmars.farmingmars_implem.move
// Variant: uncurried
pub fn move__1(ids: Array<Int63>, tl: Int63, tr: Int63, L: Int63, R: Int63, cnt: Array<Int63>, ge: Array<Int63>) -> (((Int63, Int63), Array<Int63>), Array<Int63>) {
  move_(ids, tl, tr, L, R, cnt, ge, ())
}

// Rocq: Farmingmars.farmingmars_implem.move (local: move)
// Variant: uncurried, lifted
pub fn move_(ids: Array<Int63>, tl: Int63, tr: Int63, L: Int63, R: Int63, cnt: Array<Int63>, ge: Array<Int63>, _H: ()) -> (((Int63, Int63), Array<Int63>), Array<Int63>) {
  let tmp = tl < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = L - int63!(1);
      let ids_clone = Clone::clone(&ids);
      let tmp_2 = add(ids_clone, tmp_1, cnt, ge);
      match tmp_2 {
        (v39, v41) => {
          move_(ids, tl, tr, L - int63!(1), R, v39, v41, ())
        },
      }
    },
    sumbool::right => {
      let tmp_3 = R < tr;
      match bdec(tmp_3) {
        sumbool::left => {
          let ids_clone_1 = Clone::clone(&ids);
          let tmp_4 = add(ids_clone_1, R, cnt, ge);
          match tmp_4 {
            (v99, v101) => {
              move_(ids, tl, tr, L, R + int63!(1), v99, v101, ())
            },
          }
        },
        sumbool::right => {
          let tmp_5 = L < tl;
          match bdec(tmp_5) {
            sumbool::left => {
              let ids_clone_2 = Clone::clone(&ids);
              let tmp_6 = rem(ids_clone_2, L, cnt, ge);
              match tmp_6 {
                (v159, v161) => {
                  move_(ids, tl, tr, L + int63!(1), R, v159, v161, ())
                },
              }
            },
            sumbool::right => {
              let tmp_7 = tr < R;
              match bdec(tmp_7) {
                sumbool::left => {
                  let tmp_8 = R - int63!(1);
                  let ids_clone_3 = Clone::clone(&ids);
                  let tmp_9 = rem(ids_clone_3, tmp_8, cnt, ge);
                  match tmp_9 {
                    (v227, v229) => {
                      move_(ids, tl, tr, L, R - int63!(1), v227, v229, ())
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
pub fn mo_step(ids: &Array<Int63>, ls: &Array<Int63>, rs: &Array<Int63>, Q: &Array<Int63>, k: Int63, st: ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)) -> ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>) {
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
                  let q = Q.get_cloned(k_1);
                  let tl = ls.get_cloned(q) - int63!(1);
                  let tr = rs.get_cloned(q);
                  let ids_clone = Clone::clone(ids);
                  let R_clone = Clone::clone(R);
                  let L_clone = Clone::clone(L);
                  let p1_clone = Clone::clone(p1);
                  std::mem::drop(v14);
                  let tmp = move__1(ids_clone, tl, tr, R_clone, L_clone, p1_clone, v16);
                  match tmp {
                    (v67, v69) => {
                      let p = &v69;
                      match v67 {
                        (v73, v75) => {
                          match v73 {
                            (v78, v80) => {
                              let tmp_1 = (((v78, v80), v75), Clone::clone(p));
                              let tmp_2 = int63!(0);
                              let tmp_3 = p.get_cloned((tr - tl) / int63!(2) + int63!(1));
                              std::mem::drop(v69);
                              (tmp_1, v11.set(q, tmp_2 < tmp_3))
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
pub fn farm(p: Array<f64>, ls: Array<Int63>, rs: Array<Int63>) -> Array<bool> {
  let n = p.length();
  let m = ls.length();
  let p_clone = Clone::clone(&p);
  let callback: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    move |a_1: Int63, b_1: Int63| -> bool {
      let tmp = p_clone.get_cloned(a_1);
      let tmp_1 = p_clone.get_cloned(b_1);
      rocq_float64::leb(tmp, tmp_1)
    }
  });
  let P = msort(callback, n);
  let ids = mk_ids(p, P, n);
  let tmp_2 = blk(n);
  let ls_clone = Clone::clone(&ls);
  let rs_clone = Clone::clone(&rs);
  let callback_1: Rc<dyn Fn(Int63, Int63) -> bool> = Rc::new({
    move |v65: Int63, v66: Int63| -> bool {
      let ls = &ls_clone;
      let rs = &rs_clone;
      let tmp_3 = Clone::clone(&tmp_2);
      mo_le(ls, rs, tmp_3, v65, v66)
    }
  });
  let Q = msort(callback_1, m);
  let callback_2: Rc<dyn Fn(Int63, ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)) -> bool> = Rc::new(move |_v89: Int63, v90: ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)| -> bool {
    std::mem::drop(v90);
    true
  });
  let callback_3: Rc<dyn Fn(Int63, ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)) -> ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)> = Rc::new({
    let __anf_capture_108 = ls;
    let __anf_capture_110 = rs;
    move |v114: Int63, v115: ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)| -> ((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>) {
      let ids = &ids;
      let ls = &__anf_capture_108;
      let rs = &__anf_capture_110;
      let Q = &Q;
      let tmp_4 = mo_step(ids, ls, rs, Q, v114, v115);
      tmp_4
    }
  });
  let tmp_5 = (((int63!(0), int63!(0)), Array::<Int63>::make(n, int63!(0))), Array::<Int63>::make(n + int63!(1), int63!(0)));
  let tmp_6 = Array::<bool>::make(m, false);
  snd::<(((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>>(loop_::<((((Int63, Int63), Array<Int63>), Array<Int63>), Array<bool>)>(m, callback_2, callback_3, int63!(0), (tmp_5, tmp_6)))
}
