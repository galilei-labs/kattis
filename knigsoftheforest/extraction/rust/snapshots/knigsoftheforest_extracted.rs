#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

// Rocq: Knigsoftheforest.knigsoftheforest_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(h: Array<Int63>, i: Int63) -> Array<Int63> {
  sift_up(h, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(h: Array<Int63>, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let q = (i - int63!(1)) / int63!(2);
      let vi = h.get_cloned(i);
      let vq = h.get_cloned(q);
      let tmp_1 = vq < vi;
      match bdec(tmp_1) {
        sumbool::left => {
          sift_up(h.set(i, vq).set(q, vi), q, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.insert
// Variant: uncurried
pub fn insert(h: Array<Int63>, s: Int63, v: Int63) -> Array<Int63> {
  sift_up_1(h.set(s, v), s)
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.step
// Variant: uncurried
pub fn step(st: ((Array<Int63>, Int63), Array<Int63>), yr: Int63, sv: Int63) -> ((Array<Int63>, Int63), Array<Int63>) {
  match st {
    (v4, v6) => {
      match v4 {
        (v9, v11) => {
          if yr == int63!(2011) {
            ((insert(v9, v11, sv), v11 + int63!(1)), v6)
          } else {
            ((v9, v11), v6.set(yr - int63!(2011), sv))
          }
        },
      }
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill
// Variant: uncurried
pub fn fill_1(ys: Array<Int63>, ps: Array<Int63>, m: Int63, i: Int63, st: ((Array<Int63>, Int63), Array<Int63>)) -> ((Array<Int63>, Int63), Array<Int63>) {
  fill(ys, ps, m, i, st, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.fill (local: fill)
// Variant: uncurried, lifted
pub fn fill(ys: Array<Int63>, ps: Array<Int63>, m: Int63, i: Int63, st: ((Array<Int63>, Int63), Array<Int63>), _H: ()) -> ((Array<Int63>, Int63), Array<Int63>) {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = ys.get_cloned(i);
      let tmp_3 = ps.get_cloned(i);
      fill(ys, ps, m, tmp_1, step(st, tmp_2, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(ys);
      std::mem::drop(ps);
      st
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.pick
// Variant: uncurried
pub fn pick(h: Array<Int63>, s: Int63, l: Int63) -> Int63 {
  let tmp = l + int63!(1);
  if tmp < s {
    let tmp_1 = h.get_cloned(l);
    let tmp_2 = h.get_cloned(l + int63!(1));
    if tmp_1 < tmp_2 {
      std::mem::drop(h);
      l + int63!(1)
    } else {
      std::mem::drop(h);
      l
    }
  } else {
    std::mem::drop(h);
    l
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(h: Array<Int63>, s: Int63, i: Int63) -> Array<Int63> {
  sift_down(h, s, i, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(h: Array<Int63>, s: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < s / int63!(2);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = int63!(2) * i + int63!(1);
      let h_clone = Clone::clone(&h);
      let c = pick(h_clone, s, tmp_1);
      let vi = h.get_cloned(i);
      let vc = h.get_cloned(c);
      let tmp_2 = vi < vc;
      match bdec(tmp_2) {
        sumbool::left => {
          sift_down(h.set(i, vc).set(c, vi), s, c, ())
        },
        sumbool::right => {
          h
        },
      }
    },
    sumbool::right => {
      h
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.extract
// Variant: uncurried
pub fn extract(h: Array<Int63>, s: Int63) -> Array<Int63> {
  let s1 = s - int63!(1);
  let tmp = h.get_cloned(s1);
  sift_down_1(h.set(int63!(0), tmp), s1, int63!(0))
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim
// Variant: uncurried
pub fn sim_1(t: Array<Int63>, h: Array<Int63>, n: Int63, p: Int63, s: Int63, d: Int63) -> Rc<option<Int63>> {
  sim(t, h, n, p, s, d, ())
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.sim (local: sim)
// Variant: uncurried, lifted
pub fn sim(t: Array<Int63>, h: Array<Int63>, n: Int63, p: Int63, s: Int63, d: Int63, _H: ()) -> Rc<option<Int63>> {
  let tmp = d < n;
  match bdec(tmp) {
    sumbool::left => {
      if s == int63!(0) {
        std::mem::drop(t);
        std::mem::drop(h);
        Rc::new(option::<Int63>::None)
      } else {
        let top = h.get_cloned(int63!(0));
        if top == p {
          std::mem::drop(t);
          std::mem::drop(h);
          Rc::new(option::<Int63>::Some(int63!(2011) + d))
        } else {
          let tmp_1 = d + int63!(1);
          if tmp_1 < n {
            let tmp_2 = extract(h, s);
            let tmp_3 = s - int63!(1);
            let tmp_4 = t.get_cloned(d + int63!(1));
            sim(t, insert(tmp_2, tmp_3, tmp_4), n, p, s, d + int63!(1), ())
          } else {
            std::mem::drop(t);
            std::mem::drop(h);
            Rc::new(option::<Int63>::None)
          }
        }
      }
    },
    sumbool::right => {
      std::mem::drop(t);
      std::mem::drop(h);
      Rc::new(option::<Int63>::None)
    },
  }
}

// Rocq: Knigsoftheforest.knigsoftheforest_implem.knigs_impl
// Variant: uncurried
pub fn knigs_impl(_k: Int63, n: Int63, y: Int63, p: Int63, ys: Array<Int63>, ps: Array<Int63>) -> Rc<option<Int63>> {
  let m = ys.length();
  let st0 = step(((Array::<Int63>::make(m + int63!(1), int63!(0)), int63!(0)), Array::<Int63>::make(n, int63!(0))), y, p);
  let tmp = fill_1(ys, ps, m, int63!(0), st0);
  match tmp {
    (v67, v69) => {
      match v67 {
        (v72, v74) => {
          sim_1(v69, v72, n, p, v74, int63!(0))
        },
      }
    },
  }
}
