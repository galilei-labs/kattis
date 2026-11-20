#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub enum inter<A: 'static> {
  Empty,
  Point { x: A, y: A, denominator: A },
  Segment { start_x: A, start_y: A, end_x: A, end_y: A },
}

impl<A: Clone + 'static> Clone for inter<A> {
  fn clone(&self) -> Self {
    match self {
      inter::Empty => inter::Empty,
      inter::Point { x: __field0, y: __field1, denominator: __field2 } => inter::Point { x: Clone::clone(__field0), y: Clone::clone(__field1), denominator: Clone::clone(__field2) },
      inter::Segment { start_x: __field0, start_y: __field1, end_x: __field2, end_y: __field3 } => inter::Segment { start_x: Clone::clone(__field0), start_y: Clone::clone(__field1), end_x: Clone::clone(__field2), end_y: Clone::clone(__field3) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type sint = Int63;

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
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

// Rocq: Segmentintersection.segmentintersection_implem.onseg_m
// Variant: uncurried
pub fn onseg_m(ax: Int63, ay: Int63, bx: Int63, by_: Int63, px: Int63, py: Int63) -> bool {
  let tmp = (bx - ax) * (py - ay) == (by_ - ay) * (px - ax);
  let tmp_1 = andb(ax.lesb(px), px.lesb(bx));
  let tmp_2 = andb(bx.lesb(px), px.lesb(ax));
  let tmp_3 = andb(tmp, orb(tmp_1, tmp_2));
  let tmp_4 = andb(ay.lesb(py), py.lesb(by_));
  let tmp_5 = andb(by_.lesb(py), py.lesb(ay));
  andb(tmp_3, orb(tmp_4, tmp_5))
}

// Rocq: Segmentintersection.segmentintersection_implem.lexle_m
// Variant: uncurried
pub fn lexle_m(ux: Int63, uy: Int63, vx: Int63, vy: Int63) -> bool {
  orb(ux.ltsb(vx), andb(ux == vx, uy.lesb(vy)))
}

// Rocq: Segmentintersection.segmentintersection_implem.lexlt_m
// Variant: uncurried
pub fn lexlt_m(ux: Int63, uy: Int63, vx: Int63, vy: Int63) -> bool {
  orb(ux.ltsb(vx), andb(ux == vx, uy.ltsb(vy)))
}

// Rocq: Segmentintersection.segmentintersection_implem.finish_m
// Variant: uncurried
pub fn finish_m(lox: Int63, loy: Int63, hix: Int63, hiy: Int63) -> Rc<inter<Int63>> {
  if lexlt_m(lox, loy, hix, hiy) {
    Rc::new(inter::<Int63>::Segment { start_x: lox, start_y: loy, end_x: hix, end_y: hiy })
  } else {
    let tmp = lox == hix;
    let tmp_1 = loy == hiy;
    if andb(tmp, tmp_1) {
      Rc::new(inter::<Int63>::Point { x: lox, y: loy, denominator: int63!(1) })
    } else {
      Rc::new(inter::<Int63>::Empty)
    }
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll2_m
// Variant: uncurried
pub fn coll2_m(p1x: Int63, p1y: Int63, p2x: Int63, p2y: Int63, p3x: Int63, p3y: Int63, p4x: Int63, p4y: Int63) -> Rc<inter<Int63>> {
  if lexle_m(p1x, p1y, p3x, p3y) {
    if lexle_m(p2x, p2y, p4x, p4y) {
      finish_m(p3x, p3y, p2x, p2y)
    } else {
      finish_m(p3x, p3y, p4x, p4y)
    }
  } else {
    if lexle_m(p2x, p2y, p4x, p4y) {
      finish_m(p1x, p1y, p2x, p2y)
    } else {
      finish_m(p1x, p1y, p4x, p4y)
    }
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll1_m
// Variant: uncurried
pub fn coll1_m(p1x: Int63, p1y: Int63, p2x: Int63, p2y: Int63, x3: Int63, y3: Int63, x4: Int63, y4: Int63) -> Rc<inter<Int63>> {
  if lexle_m(x3, y3, x4, y4) {
    coll2_m(p1x, p1y, p2x, p2y, x3, y3, x4, y4)
  } else {
    coll2_m(p1x, p1y, p2x, p2y, x4, y4, x3, y3)
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.coll_m
// Variant: uncurried
pub fn coll_m(x1: Int63, y1: Int63, x2: Int63, y2: Int63, x3: Int63, y3: Int63, x4: Int63, y4: Int63) -> Rc<inter<Int63>> {
  if lexle_m(x1, y1, x2, y2) {
    coll1_m(x1, y1, x2, y2, x3, y3, x4, y4)
  } else {
    coll1_m(x2, y2, x1, y1, x3, y3, x4, y4)
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.cross_fin_m
// Variant: uncurried
pub fn cross_fin_m(x1: Int63, y1: Int63, rx: Int63, ry: Int63, den: Int63, tn: Int63, un: Int63) -> Rc<inter<Int63>> {
  let tmp = andb(int63!(0).lesb(tn), tn.lesb(den));
  let tmp_1 = andb(tmp, int63!(0).lesb(un));
  let tmp_2 = un.lesb(den);
  if andb(tmp_1, tmp_2) {
    Rc::new(inter::<Int63>::Point { x: x1 * den + tn * rx, y: y1 * den + tn * ry, denominator: den })
  } else {
    Rc::new(inter::<Int63>::Empty)
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.crossing_m
// Variant: uncurried
pub fn crossing_m(x1: Int63, y1: Int63, rx: Int63, ry: Int63, den: Int63, tn: Int63, un: Int63) -> Rc<inter<Int63>> {
  if den.ltsb(int63!(0)) {
    cross_fin_m(x1, y1, rx, ry, int63!(0) - den, int63!(0) - tn, int63!(0) - un)
  } else {
    cross_fin_m(x1, y1, rx, ry, den, tn, un)
  }
}

// Rocq: Segmentintersection.segmentintersection_implem.isect_m
// Variant: uncurried
pub fn isect_m(x1: Int63, y1: Int63, x2: Int63, y2: Int63, x3: Int63, y3: Int63, x4: Int63, y4: Int63) -> Rc<inter<Int63>> {
  let rx = x2 - x1;
  let ry = y2 - y1;
  let sx = x4 - x3;
  let sy = y4 - y3;
  let qx = x3 - x1;
  let qy = y3 - y1;
  let den = rx * sy - ry * sx;
  let un = qx * ry - qy * rx;
  if den == int63!(0) {
    let tmp = rx == int63!(0);
    let tmp_1 = ry == int63!(0);
    if andb(tmp, tmp_1) {
      if onseg_m(x3, y3, x4, y4, x1, y1) {
        Rc::new(inter::<Int63>::Point { x: x1, y: y1, denominator: int63!(1) })
      } else {
        Rc::new(inter::<Int63>::Empty)
      }
    } else {
      let tmp_2 = sx == int63!(0);
      let tmp_3 = sy == int63!(0);
      if andb(tmp_2, tmp_3) {
        if onseg_m(x1, y1, x2, y2, x3, y3) {
          Rc::new(inter::<Int63>::Point { x: x3, y: y3, denominator: int63!(1) })
        } else {
          Rc::new(inter::<Int63>::Empty)
        }
      } else {
        if un == int63!(0) {
          coll_m(x1, y1, x2, y2, x3, y3, x4, y4)
        } else {
          Rc::new(inter::<Int63>::Empty)
        }
      }
    }
  } else {
    crossing_m(x1, y1, rx, ry, den, qx * sy - qy * sx, un)
  }
}
