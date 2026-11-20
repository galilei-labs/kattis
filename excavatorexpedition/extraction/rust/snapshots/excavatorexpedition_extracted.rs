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

pub type char63 = Int63;

pub type uint = Int63;

pub type sint = Int63;

// Rocq: Excavatorexpedition.excavatorexpedition_implem.NEG
pub fn NEG() -> Int63 {
  int63!(4611686018427387904)
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.MONE
pub fn MONE() -> Int63 {
  int63!(9223372036854775807)
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xsrc: Array<Int63>, E: Int63, k: Int63, c: Array<Int63>) -> Array<Int63> {
  cnt_loop(xsrc, E, k, c, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xsrc: Array<Int63>, E: Int63, k: Int63, c: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = k < E;
  match bdec(tmp) {
    sumbool::left => {
      let u = xsrc.get_cloned(k);
      let tmp_1 = k + int63!(1);
      let tmp_2 = c.get_cloned(u);
      cnt_loop(xsrc, E, tmp_1, c.set(u, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(xsrc);
      c
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(V: Int63, i: Int63, c: Array<Int63>) -> Array<Int63> {
  pre_loop(V, i, c, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(V: Int63, i: Int63, c: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < V;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = i + int63!(1);
      let tmp_3 = c.get_cloned(i + int63!(1));
      let tmp_4 = c.get_cloned(i);
      pre_loop(V, tmp_1, c.set(tmp_2, tmp_3 + tmp_4), ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.rfill_loop
// Variant: uncurried
pub fn rfill_loop_1(xsrc: Array<Int63>, xdst: Array<Int63>, k: Int63, c: Array<Int63>, adj: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  rfill_loop(xsrc, xdst, k, c, adj, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.rfill_loop (local: rfill_loop)
// Variant: uncurried, lifted
pub fn rfill_loop(xsrc: Array<Int63>, xdst: Array<Int63>, k: Int63, c: Array<Int63>, adj: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0) < k;
  match bdec(tmp) {
    sumbool::left => {
      let k1 = k - int63!(1);
      let u = xsrc.get_cloned(k1);
      let tmp_1 = c.get_cloned(u);
      let p = tmp_1 - int63!(1);
      let tmp_2 = c.set(u, p);
      let tmp_3 = xdst.get_cloned(k1);
      rfill_loop(xsrc, xdst, k1, tmp_2, adj.set(p, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(xsrc);
      std::mem::drop(xdst);
      (c, adj)
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.ind_loop
// Variant: uncurried
pub fn ind_loop_1(adj: Array<Int63>, E: Int63, j: Int63, d: Array<Int63>) -> Array<Int63> {
  ind_loop(adj, E, j, d, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.ind_loop (local: ind_loop)
// Variant: uncurried, lifted
pub fn ind_loop(adj: Array<Int63>, E: Int63, j: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < E;
  match bdec(tmp) {
    sumbool::left => {
      let v = adj.get_cloned(j);
      let tmp_1 = j + int63!(1);
      let tmp_2 = d.get_cloned(v);
      ind_loop(adj, E, tmp_1, d.set(v, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(adj);
      d
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.q0_loop
// Variant: uncurried
pub fn q0_loop_1(V: Int63, x: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63) -> (Array<Int63>, Int63) {
  q0_loop(V, x, d, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.q0_loop (local: q0_loop)
// Variant: uncurried, lifted
pub fn q0_loop(V: Int63, x: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = x < V;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d.get_cloned(x);
      if tmp_1 == int63!(0) {
        q0_loop(V, x + int63!(1), d, q.set(t, x), t + int63!(1), ())
      } else {
        q0_loop(V, x + int63!(1), d, q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(d);
      (q, t)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.wt
// Variant: uncurried
pub fn wt(xs: rocq_string::RocqString, V: Int63, v: Int63) -> Int63 {
  if v == int63!(0) {
    std::mem::drop(xs);
    int63!(0)
  } else {
    let tmp = V - int63!(1);
    if v == tmp {
      std::mem::drop(xs);
      int63!(0)
    } else {
      let c = get(xs, v);
      if c == int63!(88) {
        int63!(1)
      } else {
        if c == int63!(46) {
          __rocq_global_365
        } else {
          int63!(0)
        }
      }
    }
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax1
// Variant: uncurried
pub fn relax1(xs: rocq_string::RocqString, V: Int63, du: Int63, v: Int63, dist: Array<Int63>) -> Array<Int63> {
  if du == __rocq_global_349 {
    std::mem::drop(xs);
    dist
  } else {
    let cand = du + wt(xs, V, v);
    let tmp = dist.get_cloned(v);
    if tmp.ltsb(cand) {
      dist.set(v, cand)
    } else {
      dist
    }
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax_loop
// Variant: uncurried
pub fn relax_loop_1(xs: rocq_string::RocqString, V: Int63, adj: Array<Int63>, du: Int63, hi: Int63, j: Int63, d: Array<Int63>, dist: Array<Int63>, q: Array<Int63>, t: Int63) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  relax_loop(xs, V, adj, du, hi, j, d, dist, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.relax_loop (local: relax_loop)
// Variant: uncurried, lifted
pub fn relax_loop(xs: rocq_string::RocqString, V: Int63, adj: Array<Int63>, du: Int63, hi: Int63, j: Int63, d: Array<Int63>, dist: Array<Int63>, q: Array<Int63>, t: Int63, _H: ()) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  let tmp = j < hi;
  match bdec(tmp) {
    sumbool::left => {
      let v = adj.get_cloned(j);
      let xs_clone = Clone::clone(&xs);
      let dist_ = relax1(xs_clone, V, du, v, dist);
      let tmp_1 = d.get_cloned(v);
      let e = tmp_1 - int63!(1);
      if e == int63!(0) {
        relax_loop(xs, V, adj, du, hi, j + int63!(1), d.set(v, e), dist_, q.set(t, v), t + int63!(1), ())
      } else {
        relax_loop(xs, V, adj, du, hi, j + int63!(1), d.set(v, e), dist_, q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(adj);
      (((d, dist), q), t)
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.kahn_loop
// Variant: uncurried
pub fn kahn_loop_1(xs: rocq_string::RocqString, V: Int63, off: Array<Int63>, adj: Array<Int63>, h: Int63, d: Array<Int63>, dist: Array<Int63>, q: Array<Int63>, t: Int63) -> Array<Int63> {
  kahn_loop(xs, V, off, adj, h, d, dist, q, t, ())
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.kahn_loop (local: kahn_loop)
// Variant: uncurried, lifted
pub fn kahn_loop(xs: rocq_string::RocqString, V: Int63, off: Array<Int63>, adj: Array<Int63>, h: Int63, d: Array<Int63>, dist: Array<Int63>, q: Array<Int63>, t: Int63, _H: ()) -> Array<Int63> {
  let tmp = h < t;
  match bdec(tmp) {
    sumbool::left => {
      let u = q.get_cloned(h);
      let lo = off.get_cloned(u);
      let tmp_1 = dist.get_cloned(u);
      let tmp_2 = off.get_cloned(u + int63!(1));
      let xs_clone = Clone::clone(&xs);
      let adj_clone = Clone::clone(&adj);
      let tmp_3 = relax_loop_1(xs_clone, V, adj_clone, tmp_1, tmp_2, lo, d, dist, q, t);
      match tmp_3 {
        (v70, v72) => {
          match v70 {
            (v75, v77) => {
              match v75 {
                (v80, v82) => {
                  kahn_loop(xs, V, off, adj, h + int63!(1), v80, v82, v77, v72, ())
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(xs);
      std::mem::drop(off);
      std::mem::drop(adj);
      std::mem::drop(d);
      std::mem::drop(q);
      dist
    },
  }
}

// Rocq: Excavatorexpedition.excavatorexpedition_implem.excavator_impl
// Variant: uncurried
pub fn excavator_impl(xs: rocq_string::RocqString, xsrc: Array<Int63>, xdst: Array<Int63>) -> Int63 {
  let xs_clone = Clone::clone(&xs);
  let V = length(xs_clone);
  let E = xsrc.length();
  let tmp = Array::<Int63>::make(V + int63!(1), int63!(0));
  let xsrc_clone = Clone::clone(&xsrc);
  let c = cnt_loop_1(xsrc_clone, E, int63!(0), tmp);
  let c_1 = pre_loop_1(V, int63!(0), c);
  let tmp_1 = Array::<Int63>::make(E, int63!(0));
  let tmp_2 = rfill_loop_1(xsrc, xdst, E, c_1, tmp_1);
  match tmp_2 {
    (v68, v70) => {
      let off = &v70;
      let tmp_3 = Array::<Int63>::make(V, int63!(0));
      let off_clone = Clone::clone(off);
      let d = ind_loop_1(off_clone, E, int63!(0), tmp_3);
      let tmp_4 = Array::<Int63>::make(V, int63!(0));
      let d_clone = Clone::clone(&d);
      let tmp_5 = q0_loop_1(V, int63!(0), d_clone, tmp_4, int63!(0));
      match tmp_5 {
        (v117, v119) => {
          let dist = Array::<Int63>::make(V, __rocq_global_349).set(int63!(0), int63!(0));
          let dist_1 = kahn_loop_1(xs, V, v68, v70, int63!(0), d, dist, v117, v119);
          let tmp_6 = dist_1.get_cloned(V - int63!(1));
          std::mem::drop(dist_1);
          tmp_6
        },
      }
    },
  }
}
const __rocq_global_349: Int63 = int63!(4611686018427387904);
const __rocq_global_365: Int63 = int63!(9223372036854775807);