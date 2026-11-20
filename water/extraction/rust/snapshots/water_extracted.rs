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

// Rocq: Water.water_implem.big
pub fn big() -> Int63 {
  int63!(4611686018427387903)
}

// Rocq: Water.water_implem.budget
pub fn budget() -> Int63 {
  int63!(1099511627776)
}

// Rocq: Water.water_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Water.water_implem.add_pipe
// Variant: uncurried
pub fn add_pipe(m: Int63, r: Array<Int63>, a_1: Int63, b_1: Int63, c: Int63) -> Array<Int63> {
  let i1 = a_1 * m + b_1;
  let tmp = r.get_cloned(i1);
  let r1 = r.set(i1, tmp + c);
  let i2 = b_1 * m + a_1;
  let tmp_1 = r1.get_cloned(i2);
  r1.set(i2, tmp_1 + c)
}

// Rocq: Water.water_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(pa: Array<Int63>, pb: Array<Int63>, pc: Array<Int63>, m: Int63, p: Int63, j: Int63, r: Array<Int63>) -> Array<Int63> {
  init_loop(pa, pb, pc, m, p, j, r, ())
}

// Rocq: Water.water_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(pa: Array<Int63>, pb: Array<Int63>, pc: Array<Int63>, m: Int63, p: Int63, j: Int63, r: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < p;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = pa.get_cloned(j);
      let tmp_3 = pb.get_cloned(j);
      let tmp_4 = pc.get_cloned(j);
      let tmp_5 = add_pipe(m, r, tmp_2, tmp_3, tmp_4);
      init_loop(pa, pb, pc, m, p, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(pa);
      std::mem::drop(pb);
      std::mem::drop(pc);
      r
    },
  }
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

// Rocq: Water.water_implem.scan
// Variant: uncurried
pub fn scan_1(r: Array<Int63>, m: Int63, u: Int63, bu: Int63, v: Int63, par: Array<Int63>, bott: Array<Int63>, q: Array<Int63>, tail: Int63) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  scan(r, m, u, bu, v, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(r: Array<Int63>, m: Int63, u: Int63, bu: Int63, v: Int63, par: Array<Int63>, bott: Array<Int63>, q: Array<Int63>, tail: Int63, _H: ()) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  let tmp = v < m;
  match bdec(tmp) {
    sumbool::left => {
      let x = r.get_cloned(u * m + v);
      let tmp_1 = par.get_cloned(v);
      let tmp_2 = tmp_1 == int63!(0);
      let tmp_3 = int63!(0) < x;
      if andb(tmp_2, tmp_3) {
        let tmp_4 = v + int63!(1);
        let tmp_5 = par.set(v, u);
        let tmp_6 = if bu < x {
          bu
        } else {
          x
        };
        scan(r, m, u, bu, tmp_4, tmp_5, bott.set(v, tmp_6), q.set(tail, v), tail + int63!(1), ())
      } else {
        scan(r, m, u, bu, v + int63!(1), par, bott, q, tail, ())
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      (((par, bott), q), tail)
    },
  }
}

// Rocq: Water.water_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(r: Array<Int63>, m: Int63, head: Int63, par: Array<Int63>, bott: Array<Int63>, q: Array<Int63>, tail: Int63) -> (Array<Int63>, Array<Int63>) {
  bfs_loop(r, m, head, par, bott, q, tail, ())
}

// Rocq: Water.water_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(r: Array<Int63>, m: Int63, head: Int63, par: Array<Int63>, bott: Array<Int63>, q: Array<Int63>, tail: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = head < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = head < tail;
      let tmp_2 = par.get_cloned(int63!(2));
      let tmp_3 = tmp_2 == int63!(0);
      if andb(tmp_1, tmp_3) {
        let u = q.get_cloned(head);
        let tmp_4 = bott.get_cloned(u);
        let r_clone = Clone::clone(&r);
        let tmp_5 = scan_1(r_clone, m, u, tmp_4, int63!(1), par, bott, q, tail);
        match tmp_5 {
          (v78, v80) => {
            match v78 {
              (v83, v85) => {
                match v83 {
                  (v88, v90) => {
                    bfs_loop(r, m, head + int63!(1), v88, v90, v85, v80, ())
                  },
                }
              },
            }
          },
        }
      } else {
        std::mem::drop(r);
        std::mem::drop(q);
        (par, bott)
      }
    },
    sumbool::right => {
      std::mem::drop(r);
      std::mem::drop(q);
      (par, bott)
    },
  }
}

// Rocq: Water.water_implem.bfs
// Variant: uncurried
pub fn bfs(r: Array<Int63>, m: Int63) -> (Array<Int63>, Array<Int63>) {
  let tmp = Array::<Int63>::make(m, int63!(0)).set(int63!(1), int63!(1));
  let tmp_1 = Array::<Int63>::make(m, int63!(0)).set(int63!(1), __rocq_global_376);
  let tmp_2 = Array::<Int63>::make(m, int63!(0));
  bfs_loop_1(r, m, int63!(0), tmp, tmp_1, tmp_2.set(int63!(0), int63!(1)), int63!(1))
}

// Rocq: Water.water_implem.walk
// Variant: uncurried
pub fn walk_1(par: Array<Int63>, m: Int63, d: Int63, r: Array<Int63>, cur: Int63, i: Int63) -> Array<Int63> {
  walk(par, m, d, r, cur, i, ())
}

// Rocq: Water.water_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(par: Array<Int63>, m: Int63, d: Int63, r: Array<Int63>, cur: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      if cur == int63!(1) {
        std::mem::drop(par);
        r
      } else {
        let u = par.get_cloned(cur);
        let i1 = u * m + cur;
        let tmp_1 = r.get_cloned(i1);
        let r1 = r.set(i1, tmp_1 - d);
        let i2 = cur * m + u;
        let tmp_2 = r1.get_cloned(i2);
        let r2 = r1.set(i2, tmp_2 + d);
        walk(par, m, d, r2, u, i + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(par);
      r
    },
  }
}

// Rocq: Water.water_implem.augment
// Variant: uncurried
pub fn augment_1(m: Int63, B: Int63, r: Array<Int63>, val: Int63, i: Int63) -> (Array<Int63>, Int63) {
  augment(m, B, r, val, i, ())
}

// Rocq: Water.water_implem.augment (local: augment)
// Variant: uncurried, lifted
pub fn augment(m: Int63, B: Int63, r: Array<Int63>, val: Int63, i: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = i < B;
  match bdec(tmp) {
    sumbool::left => {
      let r_clone = Clone::clone(&r);
      let tmp_1 = bfs(r_clone, m);
      match tmp_1 {
        (v25, v27) => {
          let bott = &v25;
          let par = &v27;
          let tmp_2 = bott.get_cloned(int63!(2));
          if tmp_2 == int63!(0) {
            std::mem::drop(v25);
            std::mem::drop(v27);
            (r, val)
          } else {
            let d = par.get_cloned(int63!(2));
            std::mem::drop(v27);
            let tmp_3 = walk_1(v25, m, d, r, int63!(2), int63!(0));
            augment(m, B, tmp_3, val + d, i + int63!(1), ())
          }
        },
      }
    },
    sumbool::right => {
      (r, val)
    },
  }
}

// Rocq: Water.water_implem.imp_loop
// Variant: uncurried
pub fn imp_loop_1(ia: Array<Int63>, ib: Array<Int63>, ic: Array<Int63>, m: Int63, k: Int63, t: Int63, r: Array<Int63>, val: Int63, out: Array<Int63>) -> Array<Int63> {
  imp_loop(ia, ib, ic, m, k, t, r, val, out, ())
}

// Rocq: Water.water_implem.imp_loop (local: imp_loop)
// Variant: uncurried, lifted
pub fn imp_loop(ia: Array<Int63>, ib: Array<Int63>, ic: Array<Int63>, m: Int63, k: Int63, t: Int63, r: Array<Int63>, val: Int63, out: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = t < k;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ia.get_cloned(t);
      let tmp_2 = ib.get_cloned(t);
      let tmp_3 = ic.get_cloned(t);
      let r1 = add_pipe(m, r, tmp_1, tmp_2, tmp_3);
      let tmp_4 = augment_1(m, __rocq_global_569, r1, val, int63!(0));
      match tmp_4 {
        (v61, v63) => {
          let tmp_5 = t + int63!(1);
          let tmp_6 = out.set(t + int63!(1), v63);
          imp_loop(ia, ib, ic, m, k, tmp_5, v61, v63, tmp_6, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(ia);
      std::mem::drop(ib);
      std::mem::drop(ic);
      std::mem::drop(r);
      out
    },
  }
}

// Rocq: Water.water_implem.water_impl
// Variant: uncurried
pub fn water_impl(n: Int63, pa: Array<Int63>, pb: Array<Int63>, pc: Array<Int63>, ia: Array<Int63>, ib: Array<Int63>, ic: Array<Int63>) -> Array<Int63> {
  let m = n + int63!(1);
  let p = pa.length();
  let tmp = m * m;
  let r = init_loop_1(pa, pb, pc, m, p, int63!(0), Array::<Int63>::make(tmp, int63!(0)));
  let tmp_1 = augment_1(m, __rocq_global_569, r, int63!(0), int63!(0));
  match tmp_1 {
    (v66, v68) => {
      let k = ia.length();
      let tmp_2 = Array::<Int63>::make(k + int63!(1), int63!(0)).set(int63!(0), v68);
      imp_loop_1(ia, ib, ic, m, k, int63!(0), v66, v68, tmp_2)
    },
  }
}
const __rocq_global_376: Int63 = int63!(4611686018427387903);
const __rocq_global_569: Int63 = int63!(1099511627776);