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

pub type uint = Int63;

// Rocq: Corelib.Floats.PrimFloat.zero
pub fn zero() -> f64 {
  f64::from_bits(0u64)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.wloop
// Variant: uncurried
pub fn wloop_1<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop::<St>(hi, f, i, s, ())
}

// Rocq: Communicationssatellite.communicationssatellite_implem.wloop (local: wloop)
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

// Rocq: Communicationssatellite.communicationssatellite_implem.loop
// Variant: uncurried
pub fn loop_<St: Clone + 'static>(hi: Int63, f: Rc<dyn Fn(Int63, St) -> St>, i: Int63, s: St) -> St {
  wloop_1::<St>(hi, f, i, s)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.dsq
// Variant: uncurried
pub fn dsq(x: Array<Int63>, y: Array<Int63>, i: Int63, j: Int63) -> Int63 {
  let tmp = x.get_cloned(i);
  let tmp_1 = x.get_cloned(j);
  std::mem::drop(x);
  let dx = tmp - tmp_1;
  let tmp_2 = y.get_cloned(i);
  let tmp_3 = y.get_cloned(j);
  std::mem::drop(y);
  let dy = tmp_2 - tmp_3;
  dx * dx + dy * dy
}

// Rocq: Communicationssatellite.communicationssatellite_implem.wt
// Variant: uncurried
pub fn wt(x: Array<Int63>, y: Array<Int63>, r: Array<Int63>, i: Int63, j: Int63) -> f64 {
  let tmp = rocq_float64::sqrt(rocq_float64::of_uint63(dsq(x, y, i, j)));
  let tmp_1 = r.get_cloned(i);
  let tmp_2 = r.get_cloned(j);
  std::mem::drop(r);
  rocq_float64::sub(tmp, rocq_float64::of_uint63(tmp_1 + tmp_2))
}

// Rocq: Communicationssatellite.communicationssatellite_implem.init_step
// Variant: uncurried
pub fn init_step(x: Array<Int63>, y: Array<Int63>, r: Array<Int63>, v: Int63, key: Array<f64>) -> Array<f64> {
  let tmp = wt(x, y, r, int63!(0), v);
  key.set(v, tmp)
}

// Rocq: Communicationssatellite.communicationssatellite_implem.amin_step
// Variant: borrowed, uncurried
pub fn amin_step(n: Int63, inT: &Array<bool>, key: &Array<f64>, v: Int63, st: (Int63, f64)) -> (Int63, f64) {
  let n_1 = n;
  let v_1 = v;
  let st_1 = st;
  match &st_1 {
    (bv, b_1) => {
      if inT.get_cloned(v_1) {
        st_1
      } else {
        let bv_clone = Clone::clone(bv);
        if bv_clone == n_1 {
          std::mem::drop(st_1);
          let tmp = key.get_cloned(v_1);
          (v_1, tmp)
        } else {
          let tmp_1 = key.get_cloned(v_1);
          let b_clone = Clone::clone(b_1);
          if rocq_float64::ltb(tmp_1, b_clone) {
            std::mem::drop(st_1);
            let tmp_2 = key.get_cloned(v_1);
            (v_1, tmp_2)
          } else {
            st_1
          }
        }
      }
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.upd_step
// Variant: uncurried
pub fn upd_step(x: Array<Int63>, y: Array<Int63>, r: Array<Int63>, inT: Array<bool>, b_1: Int63, v: Int63, key: Array<f64>) -> Array<f64> {
  let tmp = inT.get_cloned(v);
  if tmp {
    std::mem::drop(x);
    std::mem::drop(y);
    std::mem::drop(r);
    std::mem::drop(inT);
    key
  } else {
    let wv = wt(x, y, r, b_1, v);
    let tmp_1 = key.get_cloned(v);
    if rocq_float64::ltb(wv, tmp_1) {
      std::mem::drop(inT);
      key.set(v, wv)
    } else {
      std::mem::drop(inT);
      key
    }
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.prim_step
// Variant: borrowed, uncurried
pub fn prim_step(x: &Array<Int63>, y: &Array<Int63>, r: &Array<Int63>, n: Int63, _k: Int63, st: ((Array<bool>, Array<f64>), f64)) -> ((Array<bool>, Array<f64>), f64) {
  let n_1 = n;
  let st_1 = st;
  match st_1 {
    (v9, v11) => {
      match v9 {
        (v14, v16) => {
          let key = &v14;
          let inT = &v16;
          let key_clone = Clone::clone(key);
          let inT_clone = Clone::clone(inT);
          let callback: Rc<dyn Fn(Int63, (Int63, f64)) -> (Int63, f64)> = Rc::new({
            let __anf_capture_28 = n_1;
            move |v34: Int63, v35: (Int63, f64)| -> (Int63, f64) {
              let n = &__anf_capture_28;
              let key = &key_clone;
              let inT = &inT_clone;
              let tmp = amin_step(Clone::clone(n), key, inT, v34, v35);
              tmp
            }
          });
          let tmp_1 = (n_1, __rocq_global_353);
          let tmp_2 = loop_::<(Int63, f64)>(n_1, callback, int63!(0), tmp_1);
          match tmp_2 {
            (v69, _v71) => {
              let tmp_3 = inT.get_cloned(v69);
              let tot = rocq_float64::add(v11, tmp_3);
              let inT_1 = v14.set(v69, true);
              let x_clone = Clone::clone(x);
              let y_clone = Clone::clone(y);
              let r_clone = Clone::clone(r);
              let inT_clone_1 = Clone::clone(&inT_1);
              let callback_1: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
                let __anf_capture_115 = v69;
                move |v117: Int63, v118: Array<f64>| -> Array<f64> {
                  let tmp_4 = Clone::clone(&x_clone);
                  let tmp_5 = Clone::clone(&y_clone);
                  let tmp_6 = Clone::clone(&r_clone);
                  let tmp_7 = Clone::clone(&inT_clone_1);
                  let tmp_8 = Clone::clone(&__anf_capture_115);
                  upd_step(tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, v117, v118)
                }
              });
              let key_1 = loop_::<Array<f64>>(n_1, callback_1, int63!(0), v16);
              ((inT_1, key_1), tot)
            },
          }
        },
      }
    },
  }
}

// Rocq: Communicationssatellite.communicationssatellite_implem.comsat
// Variant: uncurried
pub fn comsat(x: Array<Int63>, y: Array<Int63>, r: Array<Int63>) -> f64 {
  let n = x.length();
  let inT = Array::<bool>::make(n, false).set(int63!(0), true);
  let x_clone = Clone::clone(&x);
  let y_clone = Clone::clone(&y);
  let r_clone = Clone::clone(&r);
  let callback: Rc<dyn Fn(Int63, Array<f64>) -> Array<f64>> = Rc::new({
    move |v40: Int63, v41: Array<f64>| -> Array<f64> {
      let tmp = Clone::clone(&x_clone);
      let tmp_1 = Clone::clone(&y_clone);
      let tmp_2 = Clone::clone(&r_clone);
      init_step(tmp, tmp_1, tmp_2, v40, v41)
    }
  });
  let tmp_3 = Array::<f64>::make(n, __rocq_global_353);
  let key = loop_::<Array<f64>>(n, callback, int63!(0), tmp_3);
  let callback_1: Rc<dyn Fn(Int63, ((Array<bool>, Array<f64>), f64)) -> ((Array<bool>, Array<f64>), f64)> = Rc::new({
    let __anf_capture_85 = x;
    let __anf_capture_87 = y;
    let __anf_capture_89 = r;
    let __anf_capture_91 = n;
    move |v93: Int63, v94: ((Array<bool>, Array<f64>), f64)| -> ((Array<bool>, Array<f64>), f64) {
      let x = &__anf_capture_85;
      let y = &__anf_capture_87;
      let r = &__anf_capture_89;
      let tmp_4 = prim_step(x, y, r, Clone::clone(&__anf_capture_91), v93, v94);
      tmp_4
    }
  });
  let tmp_5 = loop_::<((Array<bool>, Array<f64>), f64)>(n, callback_1, int63!(1), ((inT, key), __rocq_global_353));
  match tmp_5 {
    (v135, v137) => {
      match v135 {
        (v140, v142) => {
          std::mem::drop(v140);
          std::mem::drop(v142);
          v137
        },
      }
    },
  }
}
const __rocq_global_353: f64 = f64::from_bits(0u64);