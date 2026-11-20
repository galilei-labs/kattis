#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};
#[allow(unused_imports)] use rocq_bigint as b;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct bst {
  pub b_vis: Array<Int63>,
  pub b_comp: Array<Int63>,
  pub b_par: Array<Int63>,
  pub b_d: Array<Int63>,
  pub b_tail: Int63,
  pub b_flag: bool,
}

impl Clone for bst {
  fn clone(&self) -> Self {
    match self {
      bst { b_vis: __field0, b_comp: __field1, b_par: __field2, b_d: __field3, b_tail: __field4, b_flag: __field5 } => bst { b_vis: Clone::clone(__field0), b_comp: Clone::clone(__field1), b_par: Clone::clone(__field2), b_d: Clone::clone(__field3), b_tail: Clone::clone(__field4), b_flag: Clone::clone(__field5) },
    }
  }
}

pub struct mst {
  pub m_vis: Array<Int63>,
  pub m_comp: Array<Int63>,
  pub m_par: Array<Int63>,
  pub m_d: Array<Int63>,
  pub m_sz: Array<Int63>,
  pub m_big: Array<Int63>,
  pub m_T: Rc<lct>,
  pub m_best: Array<Int63>,
}

impl Clone for mst {
  fn clone(&self) -> Self {
    match self {
      mst { m_vis: __field0, m_comp: __field1, m_par: __field2, m_d: __field3, m_sz: __field4, m_big: __field5, m_T: __field6, m_best: __field7 } => mst { m_vis: Clone::clone(__field0), m_comp: Clone::clone(__field1), m_par: Clone::clone(__field2), m_d: Clone::clone(__field3), m_sz: Clone::clone(__field4), m_big: Clone::clone(__field5), m_T: Clone::clone(__field6), m_best: Clone::clone(__field7) },
    }
  }
}

pub struct lct {
  pub l_st: Array<Int63>,
  pub l_m: Array<Int63>,
  pub l_b: Array<Int63>,
}

impl Clone for lct {
  fn clone(&self) -> Self {
    match self {
      lct { l_st: __field0, l_m: __field1, l_b: __field2 } => lct { l_st: Clone::clone(__field0), l_m: Clone::clone(__field1), l_b: Clone::clone(__field2) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<b::IntegerTag>; };

pub type uint = Int63;

// Rocq: Yatp.yatp_implem.INF
pub fn INF() -> Int63 {
  int63!(4611686018427387904)
}

// Rocq: Yatp.yatp_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Yatp.yatp_implem.hsrc
// Variant: uncurried
pub fn hsrc(xu: Array<Int63>, xv: Array<Int63>, h: Int63) -> Int63 {
  let tmp = h % int63!(2);
  if tmp == int63!(0) {
    std::mem::drop(xv);
    let tmp_1 = xu.get_cloned(h / int63!(2));
    std::mem::drop(xu);
    tmp_1
  } else {
    std::mem::drop(xu);
    let tmp_2 = xv.get_cloned(h / int63!(2));
    std::mem::drop(xv);
    tmp_2
  }
}

// Rocq: Yatp.yatp_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(xu: Array<Int63>, xv: Array<Int63>, hh: Int63, h: Int63, deg: Array<Int63>) -> Array<Int63> {
  deg_loop(xu, xv, hh, h, deg, ())
}

// Rocq: Yatp.yatp_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(xu: Array<Int63>, xv: Array<Int63>, hh: Int63, h: Int63, deg: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = h < hh;
  match bdec(tmp) {
    sumbool::left => {
      let xu_clone = Clone::clone(&xu);
      let xv_clone = Clone::clone(&xv);
      let x = hsrc(xu_clone, xv_clone, h);
      let tmp_1 = h + int63!(1);
      let tmp_2 = deg.get_cloned(x);
      deg_loop(xu, xv, hh, tmp_1, deg.set(x, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(xv);
      deg
    },
  }
}

// Rocq: Yatp.yatp_implem.start_loop
// Variant: uncurried
pub fn start_loop_1(deg: Array<Int63>, n1: Int63, x: Int63, sa: Array<Int63>, pos: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  start_loop(deg, n1, x, sa, pos, ())
}

// Rocq: Yatp.yatp_implem.start_loop (local: start_loop)
// Variant: uncurried, lifted
pub fn start_loop(deg: Array<Int63>, n1: Int63, x: Int63, sa: Array<Int63>, pos: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = x < n1;
  match bdec(tmp) {
    sumbool::left => {
      let s = sa.get_cloned(x);
      let tmp_1 = x + int63!(1);
      let tmp_2 = x + int63!(1);
      let tmp_3 = deg.get_cloned(x);
      start_loop(deg, n1, tmp_1, sa.set(tmp_2, s + tmp_3), pos.set(x, s), ())
    },
    sumbool::right => {
      std::mem::drop(deg);
      (sa, pos)
    },
  }
}

// Rocq: Yatp.yatp_implem.hdst
// Variant: uncurried
pub fn hdst(xu: Array<Int63>, xv: Array<Int63>, h: Int63) -> Int63 {
  let tmp = h % int63!(2);
  if tmp == int63!(0) {
    std::mem::drop(xu);
    let tmp_1 = xv.get_cloned(h / int63!(2));
    std::mem::drop(xv);
    tmp_1
  } else {
    std::mem::drop(xv);
    let tmp_2 = xu.get_cloned(h / int63!(2));
    std::mem::drop(xu);
    tmp_2
  }
}

// Rocq: Yatp.yatp_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(xu: Array<Int63>, xv: Array<Int63>, xw: Array<Int63>, hh: Int63, h: Int63, pos: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  fill_loop(xu, xv, xw, hh, h, pos, nbr, wt, ())
}

// Rocq: Yatp.yatp_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(xu: Array<Int63>, xv: Array<Int63>, xw: Array<Int63>, hh: Int63, h: Int63, pos: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = h < hh;
  match bdec(tmp) {
    sumbool::left => {
      let xu_clone = Clone::clone(&xu);
      let xv_clone = Clone::clone(&xv);
      let x = hsrc(xu_clone, xv_clone, h);
      let i = pos.get_cloned(x);
      let tmp_1 = h + int63!(1);
      let tmp_2 = pos.set(x, i + int63!(1));
      let xu_clone_1 = Clone::clone(&xu);
      let xv_clone_1 = Clone::clone(&xv);
      let tmp_3 = nbr.set(i, hdst(xu_clone_1, xv_clone_1, h));
      let tmp_4 = xw.get_cloned(h / int63!(2));
      fill_loop(xu, xv, xw, hh, tmp_1, tmp_2, tmp_3, wt.set(i, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(xu);
      std::mem::drop(xv);
      std::mem::drop(xw);
      std::mem::drop(pos);
      (nbr, wt)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Yatp.yatp_implem.max_loop
// Variant: uncurried
pub fn max_loop_1(a_1: Array<Int63>, n: Int63, i: Int63, acc: Int63) -> Int63 {
  max_loop(a_1, n, i, acc, ())
}

// Rocq: Yatp.yatp_implem.max_loop (local: max_loop)
// Variant: uncurried, lifted
pub fn max_loop(a_1: Array<Int63>, n: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = a_1.get_cloned(i);
      let tmp_3 = if acc < tmp_2 {
        a_1.get_cloned(i)
      } else {
        acc
      };
      max_loop(a_1, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(a_1);
      acc
    },
  }
}

// Rocq: Yatp.yatp_implem.true_loop
// Variant: uncurried
pub fn true_loop_1(n1: Int63, i: Int63, a_1: Array<bool>) -> Array<bool> {
  true_loop(n1, i, a_1, ())
}

// Rocq: Yatp.yatp_implem.true_loop (local: true_loop)
// Variant: uncurried, lifted
pub fn true_loop(n1: Int63, i: Int63, a_1: Array<bool>, _H: ()) -> Array<bool> {
  let tmp = i < n1;
  match bdec(tmp) {
    sumbool::left => {
      true_loop(n1, i + int63!(1), a_1.set(i, true), ())
    },
    sumbool::right => {
      a_1
    },
  }
}

// Rocq: Yatp.yatp_implem.b_tail
// Variant: borrowed
pub fn b_tail(b_1: &Rc<bst>) -> Int63 {
  let tmp = b_1;
  Clone::clone(&tmp.b_tail)
}

// Rocq: Yatp.yatp_implem.b_comp
pub fn b_comp(b_1: Rc<bst>) -> Array<Int63> {
  let b_b_comp_clone = Clone::clone(&b_1.b_comp);
  std::mem::drop(b_1);
  b_b_comp_clone
}

// Rocq: Yatp.yatp_implem.b_vis
pub fn b_vis(b_1: Rc<bst>) -> Array<Int63> {
  let b_b_vis_clone = Clone::clone(&b_1.b_vis);
  std::mem::drop(b_1);
  b_b_vis_clone
}

// Rocq: Yatp.yatp_implem.b_par
pub fn b_par(b_1: Rc<bst>) -> Array<Int63> {
  let b_b_par_clone = Clone::clone(&b_1.b_par);
  std::mem::drop(b_1);
  b_b_par_clone
}

// Rocq: Yatp.yatp_implem.b_d
pub fn b_d(b_1: Rc<bst>) -> Array<Int63> {
  let b_b_d_clone = Clone::clone(&b_1.b_d);
  std::mem::drop(b_1);
  b_b_d_clone
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

// Rocq: Yatp.yatp_implem.b_flag
pub fn b_flag_owned(b_1: Rc<bst>) -> bool {
  let b_b_flag_clone = Clone::clone(&b_1.b_flag);
  std::mem::drop(b_1);
  b_b_flag_clone
}

// Rocq: Yatp.yatp_implem.b_flag
// Variant: borrowed
pub fn b_flag(b_1: &Rc<bst>) -> bool {
  let tmp = b_1;
  Clone::clone(&tmp.b_flag)
}

// Rocq: Yatp.yatp_implem.scan_step
// Variant: uncurried
pub fn scan_step(alive: Array<bool>, s: Int63, x: Int63, dx: Int63, y: Int63, w: Int63, b_1: Rc<bst>) -> Rc<bst> {
  let tmp = alive.get_cloned(y);
  if tmp {
    let b_clone = Rc::clone(&b_1);
    let tmp_1 = b_vis(b_clone);
    let tmp_2 = tmp_1.get_cloned(y);
    if tmp_2 == s {
      std::mem::drop(tmp_1);
      std::mem::drop(alive);
      let b_clone_1 = Rc::clone(&b_1);
      let tmp_3 = b_vis(b_clone_1);
      let b_clone_2 = Rc::clone(&b_1);
      let tmp_4 = b_comp(b_clone_2);
      let b_clone_3 = Rc::clone(&b_1);
      let tmp_5 = b_par(b_clone_3);
      let b_clone_4 = Rc::clone(&b_1);
      let tmp_6 = b_d(b_clone_4);
      let tmp_7 = b_tail(&b_1);
      let tmp_8 = b_flag(&b_1);
      let tmp_9 = b_d(b_1);
      let tmp_10 = tmp_9.get_cloned(y);
      std::mem::drop(tmp_9);
      Rc::new(bst { b_vis: tmp_3, b_comp: tmp_4, b_par: tmp_5, b_d: tmp_6, b_tail: tmp_7, b_flag: andb(tmp_8, tmp_10 <= dx + w) })
    } else {
      std::mem::drop(tmp_1);
      std::mem::drop(alive);
      let b_clone_5 = Rc::clone(&b_1);
      let tmp_11 = b_vis(b_clone_5).set(y, s);
      let b_clone_6 = Rc::clone(&b_1);
      let tmp_12 = b_comp(b_clone_6);
      let tmp_13 = b_tail(&b_1);
      let tmp_14 = tmp_12.set(tmp_13, y);
      let b_clone_7 = Rc::clone(&b_1);
      let tmp_15 = b_par(b_clone_7).set(y, x);
      let b_clone_8 = Rc::clone(&b_1);
      let tmp_16 = b_d(b_clone_8).set(y, dx + w);
      let tmp_17 = b_tail(&b_1);
      Rc::new(bst { b_vis: tmp_11, b_comp: tmp_14, b_par: tmp_15, b_d: tmp_16, b_tail: tmp_17 + int63!(1), b_flag: b_flag_owned(b_1) })
    }
  } else {
    std::mem::drop(alive);
    b_1
  }
}

// Rocq: Yatp.yatp_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, s: Int63, x: Int63, dx: Int63, e: Int63, j: Int63, b_1: Rc<bst>) -> Rc<bst> {
  scan_loop(nbr, wt, alive, s, x, dx, e, j, b_1, ())
}

// Rocq: Yatp.yatp_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, s: Int63, x: Int63, dx: Int63, e: Int63, j: Int63, b_1: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = j < e;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let tmp_2 = nbr.get_cloned(j);
      let tmp_3 = wt.get_cloned(j);
      let alive_clone = Clone::clone(&alive);
      let tmp_4 = scan_step(alive_clone, s, x, dx, tmp_2, tmp_3, b_1);
      scan_loop(nbr, wt, alive, s, x, dx, e, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      b_1
    },
  }
}

// Rocq: Yatp.yatp_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, s: Int63, L: Int63, head: Int63, b_1: Rc<bst>) -> Rc<bst> {
  bfs_loop(sa, nbr, wt, alive, s, L, head, b_1, ())
}

// Rocq: Yatp.yatp_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, s: Int63, L: Int63, head: Int63, b_1: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = head < b_tail(&b_1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = head < L;
      match bdec(tmp_1) {
        sumbool::left => {
          let b_clone = Rc::clone(&b_1);
          let tmp_2 = b_comp(b_clone);
          let x = tmp_2.get_cloned(head);
          std::mem::drop(tmp_2);
          let tmp_3 = head + int63!(1);
          let b_clone_1 = Rc::clone(&b_1);
          let tmp_4 = b_d(b_clone_1);
          let tmp_5 = tmp_4.get_cloned(x);
          std::mem::drop(tmp_4);
          let tmp_6 = sa.get_cloned(x + int63!(1));
          let tmp_7 = sa.get_cloned(x);
          let nbr_clone = Clone::clone(&nbr);
          let wt_clone = Clone::clone(&wt);
          let alive_clone = Clone::clone(&alive);
          let tmp_8 = scan_loop_1(nbr_clone, wt_clone, alive_clone, s, x, tmp_5, tmp_6, tmp_7, b_1);
          bfs_loop(sa, nbr, wt, alive, s, L, tmp_3, tmp_8, ())
        },
        sumbool::right => {
          std::mem::drop(sa);
          std::mem::drop(nbr);
          std::mem::drop(wt);
          std::mem::drop(alive);
          b_1
        },
      }
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      b_1
    },
  }
}

// Rocq: Yatp.yatp_implem.bfs_init
// Variant: uncurried
pub fn bfs_init(s: Int63, root: Int63, vis: Array<Int63>, comp: Array<Int63>, par: Array<Int63>, d: Array<Int63>) -> Rc<bst> {
  Rc::new(bst { b_vis: vis.set(root, s), b_comp: comp.set(int63!(0), root), b_par: par.set(root, root), b_d: d.set(root, int63!(0)), b_tail: int63!(1), b_flag: true })
}

// Rocq: Yatp.yatp_implem.bfs
// Variant: uncurried
pub fn bfs(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, s: Int63, root: Int63, vis: Array<Int63>, comp: Array<Int63>, par: Array<Int63>, d: Array<Int63>) -> Rc<bst> {
  let tmp = comp.length();
  let tmp_1 = bfs_init(s, root, vis, comp, par, d);
  bfs_loop_1(sa, nbr, wt, alive, s, tmp, int63!(0), tmp_1)
}

// Rocq: Yatp.yatp_implem.m_vis
pub fn m_vis(m: Rc<mst>) -> Array<Int63> {
  let m_m_vis_clone = Clone::clone(&m.m_vis);
  std::mem::drop(m);
  m_m_vis_clone
}

// Rocq: Yatp.yatp_implem.m_comp
pub fn m_comp(m: Rc<mst>) -> Array<Int63> {
  let m_m_comp_clone = Clone::clone(&m.m_comp);
  std::mem::drop(m);
  m_m_comp_clone
}

// Rocq: Yatp.yatp_implem.m_par
pub fn m_par(m: Rc<mst>) -> Array<Int63> {
  let m_m_par_clone = Clone::clone(&m.m_par);
  std::mem::drop(m);
  m_m_par_clone
}

// Rocq: Yatp.yatp_implem.m_d
pub fn m_d(m: Rc<mst>) -> Array<Int63> {
  let m_m_d_clone = Clone::clone(&m.m_d);
  std::mem::drop(m);
  m_m_d_clone
}

// Rocq: Yatp.yatp_implem.sz_init
// Variant: uncurried
pub fn sz_init_1(comp: Array<Int63>, t: Int63, i: Int63, sz: Array<Int63>, big: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  sz_init(comp, t, i, sz, big, ())
}

// Rocq: Yatp.yatp_implem.sz_init (local: sz_init)
// Variant: uncurried, lifted
pub fn sz_init(comp: Array<Int63>, t: Int63, i: Int63, sz: Array<Int63>, big: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let x = comp.get_cloned(i);
      sz_init(comp, t, i + int63!(1), sz.set(x, int63!(1)), big.set(x, int63!(0)), ())
    },
    sumbool::right => {
      std::mem::drop(comp);
      (sz, big)
    },
  }
}

// Rocq: Yatp.yatp_implem.sz_acc
// Variant: uncurried
pub fn sz_acc_1(comp: Array<Int63>, par: Array<Int63>, i: Int63, sz: Array<Int63>, big: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  sz_acc(comp, par, i, sz, big, ())
}

// Rocq: Yatp.yatp_implem.sz_acc (local: sz_acc)
// Variant: uncurried, lifted
pub fn sz_acc(comp: Array<Int63>, par: Array<Int63>, i: Int63, sz: Array<Int63>, big: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let x = comp.get_cloned(i);
      let p = par.get_cloned(x);
      let v = sz.get_cloned(x);
      let tmp_1 = i - int63!(1);
      let tmp_2 = sz.get_cloned(p);
      let tmp_3 = sz.set(p, tmp_2 + v);
      let tmp_4 = big.get_cloned(p);
      let tmp_5 = if tmp_4 < v {
        big.set(p, v)
      } else {
        big
      };
      sz_acc(comp, par, tmp_1, tmp_3, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(comp);
      std::mem::drop(par);
      (sz, big)
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Yatp.yatp_implem.argmin
// Variant: uncurried
pub fn argmin_1(comp: Array<Int63>, sz: Array<Int63>, big: Array<Int63>, t: Int63, i: Int63, bi: Int63, bv: Int63) -> Int63 {
  argmin(comp, sz, big, t, i, bi, bv, ())
}

// Rocq: Yatp.yatp_implem.argmin (local: argmin)
// Variant: uncurried, lifted
pub fn argmin(comp: Array<Int63>, sz: Array<Int63>, big: Array<Int63>, t: Int63, i: Int63, bi: Int63, bv: Int63, _H: ()) -> Int63 {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let x = comp.get_cloned(i);
      let tmp_1 = sz.get_cloned(x);
      let up = t - tmp_1;
      let tmp_2 = big.get_cloned(x);
      let v = if tmp_2 < up {
        up
      } else {
        big.get_cloned(x)
      };
      if v < bv {
        argmin(comp, sz, big, t, i + int63!(1), i, v, ())
      } else {
        argmin(comp, sz, big, t, i + int63!(1), bi, bv, ())
      }
    },
    sumbool::right => {
      std::mem::drop(comp);
      std::mem::drop(sz);
      std::mem::drop(big);
      bi
    },
  }
}

// Rocq: Yatp.yatp_implem.centroid
// Variant: uncurried
pub fn centroid(comp: Array<Int63>, par: Array<Int63>, sz: Array<Int63>, big: Array<Int63>, t: Int63) -> (Int63, (Array<Int63>, Array<Int63>)) {
  let comp_clone = Clone::clone(&comp);
  let sb = sz_init_1(comp_clone, t, int63!(0), sz, big);
  let tmp = t - int63!(1);
  let sb_clone = Clone::clone(&sb);
  let tmp_1 = fst::<Array<Int63>, Array<Int63>>(sb_clone);
  let tmp_2 = snd::<Array<Int63>, Array<Int63>>(sb);
  let comp_clone_1 = Clone::clone(&comp);
  let sb_ = sz_acc_1(comp_clone_1, par, tmp, tmp_1, tmp_2);
  let sb__clone = Clone::clone(&sb_);
  let tmp_3 = fst::<Array<Int63>, Array<Int63>>(sb__clone);
  let sb__clone_1 = Clone::clone(&sb_);
  let tmp_4 = snd::<Array<Int63>, Array<Int63>>(sb__clone_1);
  let comp_clone_2 = Clone::clone(&comp);
  let tmp_5 = comp.get_cloned(argmin_1(comp_clone_2, tmp_3, tmp_4, t, int63!(0), int63!(0), t));
  std::mem::drop(comp);
  (tmp_5, sb_)
}

// Rocq: Yatp.yatp_implem.m_sz
pub fn m_sz(m: Rc<mst>) -> Array<Int63> {
  let m_m_sz_clone = Clone::clone(&m.m_sz);
  std::mem::drop(m);
  m_m_sz_clone
}

// Rocq: Yatp.yatp_implem.m_big
pub fn m_big(m: Rc<mst>) -> Array<Int63> {
  let m_m_big_clone = Clone::clone(&m.m_big);
  std::mem::drop(m);
  m_m_big_clone
}

// Rocq: Yatp.yatp_implem.pick
// Variant: uncurried
pub fn pick(alive: Array<bool>, c: Int63, r: Int63) -> Int63 {
  let tmp = alive.length();
  let tmp_1 = c < tmp;
  let tmp_2 = alive.get_cloned(c);
  if andb(tmp_1, tmp_2) {
    std::mem::drop(alive);
    c
  } else {
    std::mem::drop(alive);
    r
  }
}

// Rocq: Yatp.yatp_implem.rscan
// Variant: uncurried
pub fn rscan_1(nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, dx: Int63, e: Int63, j: Int63, d: Array<Int63>, ch: bool) -> (Array<Int63>, bool) {
  rscan(nbr, wt, alive, dx, e, j, d, ch, ())
}

// Rocq: Yatp.yatp_implem.rscan (local: rscan)
// Variant: uncurried, lifted
pub fn rscan(nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, dx: Int63, e: Int63, j: Int63, d: Array<Int63>, ch: bool, _H: ()) -> (Array<Int63>, bool) {
  let tmp = j < e;
  match bdec(tmp) {
    sumbool::left => {
      let y = nbr.get_cloned(j);
      let tmp_1 = wt.get_cloned(j);
      let nv = dx + tmp_1;
      let tmp_2 = alive.get_cloned(y);
      let tmp_3 = d.length();
      let tmp_4 = andb(tmp_2, y < tmp_3);
      let tmp_5 = d.get_cloned(y);
      let tmp_6 = nv < tmp_5;
      if andb(tmp_4, tmp_6) {
        rscan(nbr, wt, alive, dx, e, j + int63!(1), d.set(y, nv), true, ())
      } else {
        rscan(nbr, wt, alive, dx, e, j + int63!(1), d, ch, ())
      }
    },
    sumbool::right => {
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      (d, ch)
    },
  }
}

// Rocq: Yatp.yatp_implem.rpass
// Variant: uncurried
pub fn rpass_1(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, comp: Array<Int63>, t: Int63, i: Int63, d: Array<Int63>, ch: bool) -> (Array<Int63>, bool) {
  rpass(sa, nbr, wt, alive, comp, t, i, d, ch, ())
}

// Rocq: Yatp.yatp_implem.rpass (local: rpass)
// Variant: uncurried, lifted
pub fn rpass(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, comp: Array<Int63>, t: Int63, i: Int63, d: Array<Int63>, ch: bool, _H: ()) -> (Array<Int63>, bool) {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let x = comp.get_cloned(i);
      let tmp_1 = d.get_cloned(x);
      let tmp_2 = sa.get_cloned(x + int63!(1));
      let tmp_3 = sa.get_cloned(x);
      let nbr_clone = Clone::clone(&nbr);
      let wt_clone = Clone::clone(&wt);
      let alive_clone = Clone::clone(&alive);
      let r = rscan_1(nbr_clone, wt_clone, alive_clone, tmp_1, tmp_2, tmp_3, d, ch);
      let tmp_4 = i + int63!(1);
      let r_clone = Clone::clone(&r);
      rpass(sa, nbr, wt, alive, comp, t, tmp_4, fst::<Array<Int63>, bool>(r_clone), snd::<Array<Int63>, bool>(r), ())
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      std::mem::drop(comp);
      (d, ch)
    },
  }
}

// Rocq: Yatp.yatp_implem.rloop
// Variant: uncurried
pub fn rloop_1(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, comp: Array<Int63>, t: Int63, d: Array<Int63>) -> Array<Int63> {
  rloop(sa, nbr, wt, alive, comp, t, d, ())
}

// Rocq: Yatp.yatp_implem.rloop (local: rloop)
// Variant: uncurried, lifted
pub fn rloop(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, comp: Array<Int63>, t: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let sa_clone = Clone::clone(&sa);
  let nbr_clone = Clone::clone(&nbr);
  let wt_clone = Clone::clone(&wt);
  let alive_clone = Clone::clone(&alive);
  let comp_clone = Clone::clone(&comp);
  let pr = rpass_1(sa_clone, nbr_clone, wt_clone, alive_clone, comp_clone, t, int63!(0), d, false);
  let pr_clone = Clone::clone(&pr);
  let tmp = snd::<Array<Int63>, bool>(pr_clone);
  match bdec(tmp) {
    sumbool::left => {
      rloop(sa, nbr, wt, alive, comp, t, fst::<Array<Int63>, bool>(pr), ())
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      std::mem::drop(comp);
      fst::<Array<Int63>, bool>(pr)
    },
  }
}

// Rocq: Yatp.yatp_implem.relax
// Variant: uncurried
pub fn relax(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, alive: Array<bool>, comp: Array<Int63>, t: Int63, b_1: Rc<bst>) -> Array<Int63> {
  if b_flag(&b_1) {
    std::mem::drop(sa);
    std::mem::drop(nbr);
    std::mem::drop(wt);
    std::mem::drop(alive);
    std::mem::drop(comp);
    b_d(b_1)
  } else {
    rloop_1(sa, nbr, wt, alive, comp, t, b_d(b_1))
  }
}

// Rocq: Yatp.yatp_implem.lkey
// Variant: uncurried
pub fn lkey(X: Int63, lo: Int63, hi: Int63) -> Int63 {
  if lo == hi {
    X + lo
  } else {
    let tmp = hi - lo;
    lo + tmp / int63!(2) + int63!(1)
  }
}

// Rocq: Yatp.yatp_implem.l_st
pub fn l_st_owned(l: Rc<lct>) -> Array<Int63> {
  let l_l_st_clone = Clone::clone(&l.l_st);
  std::mem::drop(l);
  l_l_st_clone
}

// Rocq: Yatp.yatp_implem.l_st
// Variant: borrowed
pub fn l_st(l: &Rc<lct>) -> Array<Int63> {
  let tmp = l;
  Clone::clone(&tmp.l_st)
}

// Rocq: Yatp.yatp_implem.l_m
pub fn l_m_owned(l: Rc<lct>) -> Array<Int63> {
  let l_l_m_clone = Clone::clone(&l.l_m);
  std::mem::drop(l);
  l_l_m_clone
}

// Rocq: Yatp.yatp_implem.l_m
// Variant: borrowed
pub fn l_m(l: &Rc<lct>) -> Array<Int63> {
  let tmp = l;
  Clone::clone(&tmp.l_m)
}

// Rocq: Yatp.yatp_implem.l_b
pub fn l_b_owned(l: Rc<lct>) -> Array<Int63> {
  let l_l_b_clone = Clone::clone(&l.l_b);
  std::mem::drop(l);
  l_l_b_clone
}

// Rocq: Yatp.yatp_implem.l_b
// Variant: borrowed
pub fn l_b(l: &Rc<lct>) -> Array<Int63> {
  let tmp = l;
  Clone::clone(&tmp.l_b)
}

// Rocq: Yatp.yatp_implem.lc_insert
// Variant: uncurried
pub fn lc_insert_1(X: Int63, s: Int63, lo: Int63, hi: Int63, m: Int63, b_1: Int63, T: Rc<lct>) -> Rc<lct> {
  lc_insert(X, s, lo, hi, m, b_1, T, ())
}

// Rocq: Yatp.yatp_implem.lc_insert (local: lc_insert)
// Variant: uncurried, lifted
pub fn lc_insert(X: Int63, s: Int63, lo: Int63, hi: Int63, m: Int63, b_1: Int63, T: Rc<lct>, _H: ()) -> Rc<lct> {
  let k = lkey(X, lo, hi);
  let T_clone = Rc::clone(&T);
  let tmp = l_st_owned(T_clone);
  let tmp_1 = tmp.get_cloned(k);
  if tmp_1 == s {
    let T_clone_1 = Rc::clone(&T);
    let tmp_2 = l_m_owned(T_clone_1);
    let cm = tmp_2.get_cloned(k);
    let T_clone_2 = Rc::clone(&T);
    let tmp_3 = l_b_owned(T_clone_2);
    let cb = tmp_3.get_cloned(k);
    let tmp_4 = hi - lo;
    let mid = lo + tmp_4 / int63!(2);
    let nb = m * mid + b_1 < cm * mid + cb;
    let wm = if nb {
      m
    } else {
      cm
    };
    let wb = if nb {
      b_1
    } else {
      cb
    };
    let om = if nb {
      cm
    } else {
      m
    };
    let ob = if nb {
      cb
    } else {
      b_1
    };
    let T1 = if nb {
      let T_clone_3 = Rc::clone(&T);
      let tmp_5 = l_st_owned(T_clone_3);
      let T_clone_4 = Rc::clone(&T);
      Rc::new(lct { l_st: tmp_5, l_m: l_m_owned(T_clone_4).set(k, m), l_b: l_b_owned(T).set(k, b_1) })
    } else {
      T
    };
    let tmp_6 = lo < hi;
    match bdec(tmp_6) {
      sumbool::left => {
        let tmp_7 = om * lo + ob;
        let tmp_8 = wm * lo + wb;
        if tmp_7 < tmp_8 {
          std::mem::drop(tmp_3);
          std::mem::drop(tmp_2);
          std::mem::drop(tmp);
          lc_insert(X, s, lo, mid, om, ob, T1, ())
        } else {
          std::mem::drop(tmp_3);
          std::mem::drop(tmp_2);
          std::mem::drop(tmp);
          lc_insert(X, s, mid + int63!(1), hi, om, ob, T1, ())
        }
      },
      sumbool::right => {
        std::mem::drop(tmp_3);
        std::mem::drop(tmp_2);
        std::mem::drop(tmp);
        T1
      },
    }
  } else {
    std::mem::drop(tmp);
    let T_clone_5 = Rc::clone(&T);
    let tmp_9 = l_st_owned(T_clone_5).set(k, s);
    let T_clone_6 = Rc::clone(&T);
    Rc::new(lct { l_st: tmp_9, l_m: l_m_owned(T_clone_6).set(k, m), l_b: l_b_owned(T).set(k, b_1) })
  }
}

// Rocq: Yatp.yatp_implem.ins_loop
// Variant: uncurried
pub fn ins_loop_1(xp: Array<Int63>, comp: Array<Int63>, d: Array<Int63>, X: Int63, s: Int63, t: Int63, i: Int63, T: Rc<lct>) -> Rc<lct> {
  ins_loop(xp, comp, d, X, s, t, i, T, ())
}

// Rocq: Yatp.yatp_implem.ins_loop (local: ins_loop)
// Variant: uncurried, lifted
pub fn ins_loop(xp: Array<Int63>, comp: Array<Int63>, d: Array<Int63>, X: Int63, s: Int63, t: Int63, i: Int63, T: Rc<lct>, _H: ()) -> Rc<lct> {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let v = comp.get_cloned(i);
      let tmp_1 = i + int63!(1);
      let tmp_2 = X - int63!(1);
      let tmp_3 = xp.get_cloned(v - int63!(1));
      let tmp_4 = d.get_cloned(v);
      let tmp_5 = lc_insert_1(X, s, int63!(0), tmp_2, tmp_3, tmp_4, T);
      ins_loop(xp, comp, d, X, s, t, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(xp);
      std::mem::drop(comp);
      std::mem::drop(d);
      T
    },
  }
}

// Rocq: Yatp.yatp_implem.m_T
pub fn m_T(m: Rc<mst>) -> Rc<lct> {
  let m_m_T_clone = Rc::clone(&m.m_T);
  std::mem::drop(m);
  m_m_T_clone
}

// Rocq: Yatp.yatp_implem.lc_query
// Variant: borrowed, uncurried
pub fn lc_query_1(X: Int63, s: Int63, lo: Int63, hi: Int63, x: Int63, T: &Rc<lct>) -> Int63 {
  let X_1 = X;
  let s_1 = s;
  let lo_1 = lo;
  let hi_1 = hi;
  let x_1 = x;
  lc_query(X_1, s_1, lo_1, hi_1, x_1, T, ())
}

// Rocq: Yatp.yatp_implem.lc_query (local: lc_query)
// Variant: borrowed, uncurried, lifted
pub fn lc_query(X: Int63, s: Int63, lo: Int63, hi: Int63, x: Int63, T: &Rc<lct>, _H: ()) -> Int63 {
  let X_1 = X;
  let s_1 = s;
  let lo_1 = lo;
  let hi_1 = hi;
  let x_1 = x;
  let k = lkey(X_1, lo_1, hi_1);
  let tmp = l_st(T);
  let tmp_1 = tmp.get_cloned(k);
  let v = if tmp_1 == s_1 {
    let tmp_2 = l_m(T);
    let tmp_3 = tmp_2.get_cloned(k);
    std::mem::drop(tmp_2);
    let tmp_4 = tmp_3 * x_1;
    let tmp_5 = l_b(T);
    let tmp_6 = tmp_5.get_cloned(k);
    std::mem::drop(tmp_5);
    tmp_4 + tmp_6
  } else {
    __rocq_global_443
  };
  let tmp_7 = lo_1 < hi_1;
  match bdec(tmp_7) {
    sumbool::left => {
      let tmp_8 = hi_1 - lo_1;
      let mid = lo_1 + tmp_8 / int63!(2);
      let r = if x_1 <= mid {
        lc_query(X_1, s_1, lo_1, mid, x_1, T, ())
      } else {
        lc_query(X_1, s_1, mid + int63!(1), hi_1, x_1, T, ())
      };
      if r < v {
        std::mem::drop(tmp);
        r
      } else {
        std::mem::drop(tmp);
        v
      }
    },
    sumbool::right => {
      std::mem::drop(tmp);
      v
    },
  }
}

// Rocq: Yatp.yatp_implem.qry_loop
// Variant: uncurried
pub fn qry_loop_1(xp: Array<Int63>, comp: Array<Int63>, d: Array<Int63>, X: Int63, s: Int63, t: Int63, i: Int63, T: Rc<lct>, best: Array<Int63>) -> Array<Int63> {
  qry_loop(xp, comp, d, X, s, t, i, T, best, ())
}

// Rocq: Yatp.yatp_implem.qry_loop (local: qry_loop)
// Variant: uncurried, lifted
pub fn qry_loop(xp: Array<Int63>, comp: Array<Int63>, d: Array<Int63>, X: Int63, s: Int63, t: Int63, i: Int63, T: Rc<lct>, best: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < t;
  match bdec(tmp) {
    sumbool::left => {
      let u = comp.get_cloned(i);
      let tmp_1 = d.get_cloned(u);
      let tmp_2 = X - int63!(1);
      let tmp_3 = xp.get_cloned(u - int63!(1));
      let q = tmp_1 + lc_query_1(X, s, int63!(0), tmp_2, tmp_3, &T);
      let tmp_4 = i + int63!(1);
      let tmp_5 = best.get_cloned(u);
      let tmp_6 = if q < tmp_5 {
        best.set(u, q)
      } else {
        best
      };
      qry_loop(xp, comp, d, X, s, t, tmp_4, T, tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(xp);
      std::mem::drop(comp);
      std::mem::drop(d);
      std::mem::drop(T);
      best
    },
  }
}

// Rocq: Yatp.yatp_implem.m_best
pub fn m_best(m: Rc<mst>) -> Array<Int63> {
  let m_m_best_clone = Clone::clone(&m.m_best);
  std::mem::drop(m);
  m_m_best_clone
}

// Rocq: Yatp.yatp_implem.process
// Variant: uncurried
pub fn process(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, xp: Array<Int63>, X: Int63, alive: Array<bool>, r: Int63, rnd: Int63, S: Rc<mst>) -> (Int63, Rc<mst>) {
  let tmp = int63!(2) * rnd;
  let S_clone = Rc::clone(&S);
  let tmp_1 = m_vis(S_clone);
  let S_clone_1 = Rc::clone(&S);
  let tmp_2 = m_comp(S_clone_1);
  let S_clone_2 = Rc::clone(&S);
  let tmp_3 = m_par(S_clone_2);
  let S_clone_3 = Rc::clone(&S);
  let tmp_4 = m_d(S_clone_3);
  let sa_clone = Clone::clone(&sa);
  let nbr_clone = Clone::clone(&nbr);
  let wt_clone = Clone::clone(&wt);
  let alive_clone = Clone::clone(&alive);
  let b1 = bfs(sa_clone, nbr_clone, wt_clone, alive_clone, tmp, r, tmp_1, tmp_2, tmp_3, tmp_4);
  let b1_clone = Rc::clone(&b1);
  let tmp_5 = b_comp(b1_clone);
  let b1_clone_1 = Rc::clone(&b1);
  let tmp_6 = b_par(b1_clone_1);
  let S_clone_4 = Rc::clone(&S);
  let tmp_7 = m_sz(S_clone_4);
  let S_clone_5 = Rc::clone(&S);
  let tmp_8 = m_big(S_clone_5);
  let tmp_9 = b_tail(&b1);
  let cr = centroid(tmp_5, tmp_6, tmp_7, tmp_8, tmp_9);
  let cr_clone = Clone::clone(&cr);
  let tmp_10 = fst::<Int63, (Array<Int63>, Array<Int63>)>(cr_clone);
  let alive_clone_1 = Clone::clone(&alive);
  let c = pick(alive_clone_1, tmp_10, r);
  let tmp_11 = int63!(2) * rnd + int63!(1);
  let b1_clone_2 = Rc::clone(&b1);
  let tmp_12 = b_vis(b1_clone_2);
  let b1_clone_3 = Rc::clone(&b1);
  let tmp_13 = b_comp(b1_clone_3);
  let b1_clone_4 = Rc::clone(&b1);
  let tmp_14 = b_par(b1_clone_4);
  let tmp_15 = b_d(b1);
  let sa_clone_1 = Clone::clone(&sa);
  let nbr_clone_1 = Clone::clone(&nbr);
  let wt_clone_1 = Clone::clone(&wt);
  let alive_clone_2 = Clone::clone(&alive);
  let b2 = bfs(sa_clone_1, nbr_clone_1, wt_clone_1, alive_clone_2, tmp_11, c, tmp_12, tmp_13, tmp_14, tmp_15);
  let t = b_tail(&b2);
  let b2_clone = Rc::clone(&b2);
  let tmp_16 = b_comp(b2_clone);
  let b2_clone_1 = Rc::clone(&b2);
  let d = relax(sa, nbr, wt, alive, tmp_16, t, b2_clone_1);
  let b2_clone_2 = Rc::clone(&b2);
  let tmp_17 = b_comp(b2_clone_2);
  let S_clone_6 = Rc::clone(&S);
  let tmp_18 = m_T(S_clone_6);
  let xp_clone = Clone::clone(&xp);
  let d_clone = Clone::clone(&d);
  let T = ins_loop_1(xp_clone, tmp_17, d_clone, X, rnd, t, int63!(0), tmp_18);
  let b2_clone_3 = Rc::clone(&b2);
  let tmp_19 = b_comp(b2_clone_3);
  let tmp_20 = m_best(S);
  let d_clone_1 = Clone::clone(&d);
  let T_clone = Rc::clone(&T);
  let best = qry_loop_1(xp, tmp_19, d_clone_1, X, rnd, t, int63!(0), T_clone, tmp_20);
  let b2_clone_4 = Rc::clone(&b2);
  let tmp_21 = b_vis(b2_clone_4);
  let b2_clone_5 = Rc::clone(&b2);
  let tmp_22 = b_comp(b2_clone_5);
  let tmp_23 = b_par(b2);
  let cr_clone_1 = Clone::clone(&cr);
  (c, Rc::new(mst { m_vis: tmp_21, m_comp: tmp_22, m_par: tmp_23, m_d: d, m_sz: fst::<Array<Int63>, Array<Int63>>(snd::<Int63, (Array<Int63>, Array<Int63>)>(cr_clone_1)), m_big: snd::<Array<Int63>, Array<Int63>>(snd::<Int63, (Array<Int63>, Array<Int63>)>(cr)), m_T: T, m_best: best }))
}

// Rocq: Yatp.yatp_implem.main_loop
// Variant: uncurried
pub fn main_loop_1(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, xp: Array<Int63>, X: Int63, r: Int63, rnd: Int63, alive: Array<bool>, S: Rc<mst>) -> Array<Int63> {
  main_loop(sa, nbr, wt, xp, X, r, rnd, alive, S, ())
}

// Rocq: Yatp.yatp_implem.main_loop (local: main_loop)
// Variant: uncurried, lifted
pub fn main_loop(sa: Array<Int63>, nbr: Array<Int63>, wt: Array<Int63>, xp: Array<Int63>, X: Int63, r: Int63, rnd: Int63, alive: Array<bool>, S: Rc<mst>, _H: ()) -> Array<Int63> {
  let tmp = alive.length();
  let tmp_1 = r < tmp;
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = alive.get_cloned(r);
      match bdec(tmp_2) {
        sumbool::left => {
          let sa_clone = Clone::clone(&sa);
          let nbr_clone = Clone::clone(&nbr);
          let wt_clone = Clone::clone(&wt);
          let xp_clone = Clone::clone(&xp);
          let alive_clone = Clone::clone(&alive);
          let cS = process(sa_clone, nbr_clone, wt_clone, xp_clone, X, alive_clone, r, rnd, S);
          let tmp_3 = rnd + int63!(1);
          let cS_clone = Clone::clone(&cS);
          main_loop(sa, nbr, wt, xp, X, r, tmp_3, alive.set(fst::<Int63, Rc<mst>>(cS_clone), false), snd::<Int63, Rc<mst>>(cS), ())
        },
        sumbool::right => {
          main_loop(sa, nbr, wt, xp, X, r + int63!(1), rnd, alive, S, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(xp);
      std::mem::drop(alive);
      m_best(S)
    },
  }
}

// Rocq: Yatp.yatp_implem.sum_loop
// Variant: uncurried
pub fn sum_loop_1(best: Array<Int63>, n1: Int63, i: Int63, acc: Int63) -> Int63 {
  sum_loop(best, n1, i, acc, ())
}

// Rocq: Yatp.yatp_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(best: Array<Int63>, n1: Int63, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < n1;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = best.get_cloned(i);
      sum_loop(best, n1, tmp_1, acc + tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(best);
      acc
    },
  }
}

// Rocq: Yatp.yatp_implem.yatp_impl
// Variant: uncurried
pub fn yatp_impl(xp: Array<Int63>, xu: Array<Int63>, xv: Array<Int63>, xw: Array<Int63>) -> Int63 {
  let n = xp.length();
  let n1 = n + int63!(1);
  let tmp = xu.length();
  let tmp_1 = xu.length();
  let hh = tmp + tmp_1;
  let tmp_2 = Array::<Int63>::make(n1, int63!(0));
  let xu_clone = Clone::clone(&xu);
  let xv_clone = Clone::clone(&xv);
  let deg = deg_loop_1(xu_clone, xv_clone, hh, int63!(0), tmp_2);
  let tmp_3 = Array::<Int63>::make(n1 + int63!(1), int63!(0));
  let tmp_4 = Array::<Int63>::make(n1, int63!(0));
  let sp = start_loop_1(deg, n1, int63!(0), tmp_3, tmp_4);
  let sp_clone = Clone::clone(&sp);
  let tmp_5 = snd::<Array<Int63>, Array<Int63>>(sp_clone);
  let tmp_6 = Array::<Int63>::make(hh, int63!(0));
  let tmp_7 = Array::<Int63>::make(hh, int63!(0));
  let nw = fill_loop_1(xu, xv, xw, hh, int63!(0), tmp_5, tmp_6, tmp_7);
  let xp_clone = Clone::clone(&xp);
  let X = max_loop_1(xp_clone, n, int63!(0), int63!(0)) + int63!(1);
  let tmp_8 = Array::<bool>::make(n1, false);
  let alive = true_loop_1(n1, int63!(1), tmp_8);
  let tmp_9 = Array::<Int63>::make(n1, int63!(0));
  let tmp_10 = Array::<Int63>::make(n1, int63!(0));
  let tmp_11 = Array::<Int63>::make(n1, int63!(0));
  let tmp_12 = Array::<Int63>::make(n1, int63!(0));
  let tmp_13 = Array::<Int63>::make(n1, int63!(0));
  let tmp_14 = Array::<Int63>::make(n1, int63!(0));
  let tmp_15 = Rc::new(lct { l_st: Array::<Int63>::make(X + X, int63!(0)), l_m: Array::<Int63>::make(X + X, int63!(0)), l_b: Array::<Int63>::make(X + X, int63!(0)) });
  let S = Rc::new(mst { m_vis: tmp_9, m_comp: tmp_10, m_par: tmp_11, m_d: tmp_12, m_sz: tmp_13, m_big: tmp_14, m_T: tmp_15, m_best: Array::<Int63>::make(n1, __rocq_global_443) });
  let tmp_16 = fst::<Array<Int63>, Array<Int63>>(sp);
  let nw_clone = Clone::clone(&nw);
  let best = main_loop_1(tmp_16, fst::<Array<Int63>, Array<Int63>>(nw_clone), snd::<Array<Int63>, Array<Int63>>(nw), xp, X, int63!(1), int63!(1), alive, S);
  sum_loop_1(best, n1, int63!(1), int63!(0))
}
const __rocq_global_443: Int63 = int63!(4611686018427387904);