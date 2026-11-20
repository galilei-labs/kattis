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

// Rocq: Kingpinescape.kingpinescape_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(col: Array<Int63>, m: Int63, i: Int63, deg: Array<Int63>) -> Array<Int63> {
  cnt_loop(col, m, i, deg, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(col: Array<Int63>, m: Int63, i: Int63, deg: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let v = col.get_cloned(i);
      let tmp_1 = i + int63!(1);
      let tmp_2 = deg.get_cloned(v);
      cnt_loop(col, m, tmp_1, deg.set(v, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(col);
      deg
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(deg: Array<Int63>, n: Int63, i: Int63, acc: Int63, pos: Array<Int63>) -> Array<Int63> {
  pre_loop(deg, n, i, acc, pos, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(deg: Array<Int63>, n: Int63, i: Int63, acc: Int63, pos: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = deg.get_cloned(i);
      pre_loop(deg, n, tmp_1, acc + tmp_2, pos.set(i, acc), ())
    },
    sumbool::right => {
      std::mem::drop(deg);
      pos
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(col: Array<Int63>, base: Int63, m: Int63, i: Int63, pos: Array<Int63>, adj: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  fill_loop(col, base, m, i, pos, adj, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(col: Array<Int63>, base: Int63, m: Int63, i: Int63, pos: Array<Int63>, adj: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let v = col.get_cloned(i);
      let p = pos.get_cloned(v);
      let tmp_1 = i + int63!(1);
      let tmp_2 = pos.set(v, p + int63!(1));
      let tmp_3 = base + i;
      fill_loop(col, base, m, tmp_1, tmp_2, adj.set(p, tmp_3), ())
    },
    sumbool::right => {
      std::mem::drop(col);
      (pos, adj)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop
// Variant: uncurried
pub fn root_loop_1(deg: Array<Int63>, n: Int63, i: Int63) -> Int63 {
  root_loop(deg, n, i, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.root_loop (local: root_loop)
// Variant: uncurried, lifted
pub fn root_loop(deg: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = deg.get_cloned(i);
      if int63!(2) <= tmp_1 {
        std::mem::drop(deg);
        i
      } else {
        root_loop(deg, n, i + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(deg);
      int63!(0)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.other
// Variant: uncurried
pub fn other(ea: Array<Int63>, eb: Array<Int63>, m: Int63, hh: Int63) -> Int63 {
  if hh < m {
    std::mem::drop(ea);
    let tmp = eb.get_cloned(hh);
    std::mem::drop(eb);
    tmp
  } else {
    std::mem::drop(eb);
    let tmp_1 = ea.get_cloned(hh - m);
    std::mem::drop(ea);
    tmp_1
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop
// Variant: uncurried
pub fn nb_loop_1(ea: Array<Int63>, eb: Array<Int63>, adj: Array<Int63>, m: Int63, e: Int63, s: Int63, mark: Array<Int63>, stk: Array<Int63>, sp: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  nb_loop(ea, eb, adj, m, e, s, mark, stk, sp, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.nb_loop (local: nb_loop)
// Variant: uncurried, lifted
pub fn nb_loop(ea: Array<Int63>, eb: Array<Int63>, adj: Array<Int63>, m: Int63, e: Int63, s: Int63, mark: Array<Int63>, stk: Array<Int63>, sp: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = s < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = adj.get_cloned(s);
      let ea_clone = Clone::clone(&ea);
      let eb_clone = Clone::clone(&eb);
      let w = other(ea_clone, eb_clone, m, tmp_1);
      let tmp_2 = mark.get_cloned(w);
      if tmp_2 == int63!(0) {
        nb_loop(ea, eb, adj, m, e, s + int63!(1), mark.set(w, int63!(1)), stk.set(sp, w), sp + int63!(1), ())
      } else {
        nb_loop(ea, eb, adj, m, e, s + int63!(1), mark, stk, sp, ())
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      ((mark, stk), sp)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop
// Variant: uncurried
pub fn dfs_loop_1(ea: Array<Int63>, eb: Array<Int63>, adj: Array<Int63>, deg: Array<Int63>, pos: Array<Int63>, n: Int63, m: Int63, t: Int63, mark: Array<Int63>, stk: Array<Int63>, sp: Int63, lv: Array<Int63>, L: Int63) -> (Array<Int63>, Int63) {
  dfs_loop(ea, eb, adj, deg, pos, n, m, t, mark, stk, sp, lv, L, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.dfs_loop (local: dfs_loop)
// Variant: uncurried, lifted
pub fn dfs_loop(ea: Array<Int63>, eb: Array<Int63>, adj: Array<Int63>, deg: Array<Int63>, pos: Array<Int63>, n: Int63, m: Int63, t: Int63, mark: Array<Int63>, stk: Array<Int63>, sp: Int63, lv: Array<Int63>, L: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = t < n;
  match bdec(tmp) {
    sumbool::left => {
      if int63!(0) < sp {
        let v = stk.get_cloned(sp - int63!(1));
        let dv = deg.get_cloned(v);
        let e = pos.get_cloned(v);
        let tmp_1 = int63!(1);
        let lv_ = if dv == tmp_1 {
          lv.set(L, v)
        } else {
          lv
        };
        let tmp_2 = int63!(1);
        let L_ = if dv == tmp_2 {
          L + int63!(1)
        } else {
          L
        };
        let tmp_3 = e - dv;
        let tmp_4 = sp - int63!(1);
        let ea_clone = Clone::clone(&ea);
        let eb_clone = Clone::clone(&eb);
        let adj_clone = Clone::clone(&adj);
        let tmp_5 = nb_loop_1(ea_clone, eb_clone, adj_clone, m, e, tmp_3, mark, stk, tmp_4);
        match tmp_5 {
          (v135, v137) => {
            match v135 {
              (v140, v142) => {
                dfs_loop(ea, eb, adj, deg, pos, n, m, t + int63!(1), v140, v142, v137, lv_, L_, ())
              },
            }
          },
        }
      } else {
        std::mem::drop(ea);
        std::mem::drop(eb);
        std::mem::drop(adj);
        std::mem::drop(deg);
        std::mem::drop(pos);
        std::mem::drop(mark);
        std::mem::drop(stk);
        (lv, L)
      }
    },
    sumbool::right => {
      std::mem::drop(ea);
      std::mem::drop(eb);
      std::mem::drop(adj);
      std::mem::drop(deg);
      std::mem::drop(pos);
      std::mem::drop(mark);
      std::mem::drop(stk);
      (lv, L)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(lv: Array<Int63>, a_1: Int63, c: Int63, i: Int63, xs: Array<Int63>, ys: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  out_loop(lv, a_1, c, i, xs, ys, ())
}

// Rocq: Kingpinescape.kingpinescape_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(lv: Array<Int63>, a_1: Int63, c: Int63, i: Int63, xs: Array<Int63>, ys: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < c;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = lv.get_cloned(i);
      let tmp_3 = xs.set(i, tmp_2);
      let tmp_4 = lv.get_cloned(i + a_1);
      out_loop(lv, a_1, c, tmp_1, tmp_3, ys.set(i, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(lv);
      (xs, ys)
    },
  }
}

// Rocq: Kingpinescape.kingpinescape_implem.kingpin_impl
// Variant: uncurried
pub fn kingpin_impl(n: Int63, _h: Int63, ea: Array<Int63>, eb: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  let m = n - int63!(1);
  let tmp = Array::<Int63>::make(n, int63!(0));
  let ea_clone = Clone::clone(&ea);
  let deg0 = cnt_loop_1(ea_clone, m, int63!(0), tmp);
  let eb_clone = Clone::clone(&eb);
  let deg = cnt_loop_1(eb_clone, m, int63!(0), deg0);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let deg_clone = Clone::clone(&deg);
  let pos0 = pre_loop_1(deg_clone, n, int63!(0), int63!(0), tmp_1);
  let tmp_2 = Array::<Int63>::make(m + m, int63!(0));
  let ea_clone_1 = Clone::clone(&ea);
  let tmp_3 = fill_loop_1(ea_clone_1, int63!(0), m, int63!(0), pos0, tmp_2);
  match tmp_3 {
    (v102, v104) => {
      let eb_clone_1 = Clone::clone(&eb);
      let tmp_4 = fill_loop_1(eb_clone_1, m, m, int63!(0), v102, v104);
      match &tmp_4 {
        (adj, pos) => {
          let deg_clone_1 = Clone::clone(&deg);
          let r = root_loop_1(deg_clone_1, n, int63!(0));
          let mark = Array::<Int63>::make(n, int63!(0)).set(r, int63!(1));
          let stk = Array::<Int63>::make(n, int63!(0)).set(int63!(0), r);
          let tmp_5 = int63!(0);
          let tmp_6 = int63!(1);
          let tmp_7 = Array::<Int63>::make(n, int63!(0));
          let tmp_8 = int63!(0);
          let pos_clone = Clone::clone(pos);
          let adj_clone = Clone::clone(adj);
          std::mem::drop(tmp_4);
          let tmp_9 = dfs_loop_1(ea, eb, pos_clone, deg, adj_clone, n, m, tmp_5, mark, stk, tmp_6, tmp_7, tmp_8);
          match tmp_9 {
            (v214, v216) => {
              let a_1 = v216 >> int63!(1);
              let c = v216 - a_1;
              let tmp_10 = Array::<Int63>::make(c, int63!(0));
              let tmp_11 = Array::<Int63>::make(c, int63!(0));
              out_loop_1(v214, a_1, c, int63!(0), tmp_10, tmp_11)
            },
          }
        },
      }
    },
  }
}
