#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct bst {
  pub b_vis: Rc<Array<u64>>,
  pub b_comp: Rc<Array<u64>>,
  pub b_par: Rc<Array<u64>>,
  pub b_d: Rc<Array<u64>>,
  pub b_tail: u64,
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
  pub m_vis: Rc<Array<u64>>,
  pub m_comp: Rc<Array<u64>>,
  pub m_par: Rc<Array<u64>>,
  pub m_d: Rc<Array<u64>>,
  pub m_sz: Rc<Array<u64>>,
  pub m_big: Rc<Array<u64>>,
  pub m_T: Rc<lct>,
  pub m_best: Rc<Array<u64>>,
}

impl Clone for mst {
  fn clone(&self) -> Self {
    match self {
      mst { m_vis: __field0, m_comp: __field1, m_par: __field2, m_d: __field3, m_sz: __field4, m_big: __field5, m_T: __field6, m_best: __field7 } => mst { m_vis: Clone::clone(__field0), m_comp: Clone::clone(__field1), m_par: Clone::clone(__field2), m_d: Clone::clone(__field3), m_sz: Clone::clone(__field4), m_big: Clone::clone(__field5), m_T: Clone::clone(__field6), m_best: Clone::clone(__field7) },
    }
  }
}

pub struct lct {
  pub l_st: Rc<Array<u64>>,
  pub l_m: Rc<Array<u64>>,
  pub l_b: Rc<Array<u64>>,
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

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::PositiveTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::NaturalTag>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<rocq_bigint::IntegerTag>; };

pub type uint = u64;

// Rocq: Yatp.yatp_implem.INF
pub fn INF() -> u64 {
  4611686018427387904u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Yatp.yatp_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Yatp.yatp_implem.hsrc
// Variant: uncurried
pub fn hsrc(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, h: u64) -> u64 {
  let tmp = mod_(h, 2u64);
  if eqb(tmp, 0u64) {
    std::mem::drop(xv);
    let tmp_1 = rocq_array::get::<u64>(&xu, div(h, 2u64));
    std::mem::drop(xu);
    tmp_1
  } else {
    std::mem::drop(xu);
    let tmp_2 = rocq_array::get::<u64>(&xv, div(h, 2u64));
    std::mem::drop(xv);
    tmp_2
  }
}

// Rocq: Yatp.yatp_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, hh: u64, h: u64, deg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  deg_loop(xu, xv, hh, h, deg, ())
}

// Rocq: Yatp.yatp_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, hh: u64, h: u64, deg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(h, hh);
  match bdec(tmp) {
    sumbool::left => {
      let xu_clone = Rc::clone(&xu);
      let xv_clone = Rc::clone(&xv);
      let x = hsrc(xu_clone, xv_clone, h);
      let tmp_1 = add(h, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&deg, x);
      let tmp_3 = rocq_array::set::<u64>(deg, x, add(tmp_2, 1u64));
      deg_loop(xu, xv, hh, tmp_1, tmp_3, ())
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
pub fn start_loop_1(deg: Rc<Array<u64>>, n1: u64, x: u64, sa: Rc<Array<u64>>, pos: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  start_loop(deg, n1, x, sa, pos, ())
}

// Rocq: Yatp.yatp_implem.start_loop (local: start_loop)
// Variant: uncurried, lifted
pub fn start_loop(deg: Rc<Array<u64>>, n1: u64, x: u64, sa: Rc<Array<u64>>, pos: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(x, n1);
  match bdec(tmp) {
    sumbool::left => {
      let s = rocq_array::get::<u64>(&sa, x);
      let tmp_1 = add(x, 1u64);
      let tmp_2 = add(x, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&deg, x);
      let tmp_4 = rocq_array::set::<u64>(sa, tmp_2, add(s, tmp_3));
      let tmp_5 = rocq_array::set::<u64>(pos, x, s);
      start_loop(deg, n1, tmp_1, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(deg);
      (sa, pos)
    },
  }
}

// Rocq: Yatp.yatp_implem.hdst
// Variant: uncurried
pub fn hdst(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, h: u64) -> u64 {
  let tmp = mod_(h, 2u64);
  if eqb(tmp, 0u64) {
    std::mem::drop(xu);
    let tmp_1 = rocq_array::get::<u64>(&xv, div(h, 2u64));
    std::mem::drop(xv);
    tmp_1
  } else {
    std::mem::drop(xv);
    let tmp_2 = rocq_array::get::<u64>(&xu, div(h, 2u64));
    std::mem::drop(xu);
    tmp_2
  }
}

// Rocq: Yatp.yatp_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, hh: u64, h: u64, pos: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill_loop(xu, xv, xw, hh, h, pos, nbr, wt, ())
}

// Rocq: Yatp.yatp_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, xw: Rc<Array<u64>>, hh: u64, h: u64, pos: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(h, hh);
  match bdec(tmp) {
    sumbool::left => {
      let xu_clone = Rc::clone(&xu);
      let xv_clone = Rc::clone(&xv);
      let x = hsrc(xu_clone, xv_clone, h);
      let i = rocq_array::get::<u64>(&pos, x);
      let tmp_1 = add(h, 1u64);
      let tmp_2 = rocq_array::set::<u64>(pos, x, add(i, 1u64));
      let xu_clone_1 = Rc::clone(&xu);
      let xv_clone_1 = Rc::clone(&xv);
      let tmp_3 = rocq_array::set::<u64>(nbr, i, hdst(xu_clone_1, xv_clone_1, h));
      let tmp_4 = rocq_array::get::<u64>(&xw, div(h, 2u64));
      let tmp_5 = rocq_array::set::<u64>(wt, i, tmp_4);
      fill_loop(xu, xv, xw, hh, tmp_1, tmp_2, tmp_3, tmp_5, ())
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
pub fn max_loop_1(a: Rc<Array<u64>>, n: u64, i: u64, acc: u64) -> u64 {
  max_loop(a, n, i, acc, ())
}

// Rocq: Yatp.yatp_implem.max_loop (local: max_loop)
// Variant: uncurried, lifted
pub fn max_loop(a: Rc<Array<u64>>, n: u64, i: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&a, i);
      let tmp_3 = if ltb(acc, tmp_2) {
        rocq_array::get::<u64>(&a, i)
      } else {
        acc
      };
      max_loop(a, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(a);
      acc
    },
  }
}

// Rocq: Yatp.yatp_implem.true_loop
// Variant: uncurried
pub fn true_loop_1(n1: u64, i: u64, a: Rc<Array<bool>>) -> Rc<Array<bool>> {
  true_loop(n1, i, a, ())
}

// Rocq: Yatp.yatp_implem.true_loop (local: true_loop)
// Variant: uncurried, lifted
pub fn true_loop(n1: u64, i: u64, a: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(i, n1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<bool>(a, i, true);
      true_loop(n1, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Yatp.yatp_implem.b_tail
// Variant: borrowed
pub fn b_tail(b: &Rc<bst>) -> u64 {
  let tmp = b;
  Clone::clone(&tmp.b_tail)
}

// Rocq: Yatp.yatp_implem.b_comp
pub fn b_comp(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_b_comp_clone = Rc::clone(&b.b_comp);
  std::mem::drop(b);
  b_b_comp_clone
}

// Rocq: Yatp.yatp_implem.b_vis
pub fn b_vis(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_b_vis_clone = Rc::clone(&b.b_vis);
  std::mem::drop(b);
  b_b_vis_clone
}

// Rocq: Yatp.yatp_implem.b_par
pub fn b_par(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_b_par_clone = Rc::clone(&b.b_par);
  std::mem::drop(b);
  b_b_par_clone
}

// Rocq: Yatp.yatp_implem.b_d
pub fn b_d(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_b_d_clone = Rc::clone(&b.b_d);
  std::mem::drop(b);
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
pub fn b_flag_owned(b: Rc<bst>) -> bool {
  let b_b_flag_clone = Clone::clone(&b.b_flag);
  std::mem::drop(b);
  b_b_flag_clone
}

// Rocq: Yatp.yatp_implem.b_flag
// Variant: borrowed
pub fn b_flag(b: &Rc<bst>) -> bool {
  let tmp = b;
  Clone::clone(&tmp.b_flag)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Yatp.yatp_implem.scan_step
// Variant: uncurried
pub fn scan_step(alive: Rc<Array<bool>>, s: u64, x: u64, dx: u64, y: u64, w: u64, b: Rc<bst>) -> Rc<bst> {
  let tmp = rocq_array::get::<bool>(&alive, y);
  if tmp {
    let b_clone = Rc::clone(&b);
    let tmp_1 = b_vis(b_clone);
    let tmp_2 = rocq_array::get::<u64>(&tmp_1, y);
    if eqb(tmp_2, s) {
      std::mem::drop(tmp_1);
      std::mem::drop(alive);
      let b_clone_1 = Rc::clone(&b);
      let tmp_3 = b_vis(b_clone_1);
      let b_clone_2 = Rc::clone(&b);
      let tmp_4 = b_comp(b_clone_2);
      let b_clone_3 = Rc::clone(&b);
      let tmp_5 = b_par(b_clone_3);
      let b_clone_4 = Rc::clone(&b);
      let tmp_6 = b_d(b_clone_4);
      let tmp_7 = b_tail(&b);
      let tmp_8 = b_flag(&b);
      let tmp_9 = b_d(b);
      let tmp_10 = rocq_array::get::<u64>(&tmp_9, y);
      std::mem::drop(tmp_9);
      Rc::new(bst { b_vis: tmp_3, b_comp: tmp_4, b_par: tmp_5, b_d: tmp_6, b_tail: tmp_7, b_flag: andb(tmp_8, leb(tmp_10, add(dx, w))) })
    } else {
      std::mem::drop(tmp_1);
      std::mem::drop(alive);
      let b_clone_5 = Rc::clone(&b);
      let tmp_11 = b_vis(b_clone_5);
      let tmp_12 = rocq_array::set::<u64>(tmp_11, y, s);
      let b_clone_6 = Rc::clone(&b);
      let tmp_13 = b_comp(b_clone_6);
      let tmp_14 = b_tail(&b);
      let tmp_15 = rocq_array::set::<u64>(tmp_13, tmp_14, y);
      let b_clone_7 = Rc::clone(&b);
      let tmp_16 = b_par(b_clone_7);
      let tmp_17 = rocq_array::set::<u64>(tmp_16, y, x);
      let b_clone_8 = Rc::clone(&b);
      let tmp_18 = b_d(b_clone_8);
      let tmp_19 = rocq_array::set::<u64>(tmp_18, y, add(dx, w));
      let tmp_20 = b_tail(&b);
      Rc::new(bst { b_vis: tmp_12, b_comp: tmp_15, b_par: tmp_17, b_d: tmp_19, b_tail: add(tmp_20, 1u64), b_flag: b_flag_owned(b) })
    }
  } else {
    std::mem::drop(alive);
    b
  }
}

// Rocq: Yatp.yatp_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, x: u64, dx: u64, e: u64, j: u64, b: Rc<bst>) -> Rc<bst> {
  scan_loop(nbr, wt, alive, s, x, dx, e, j, b, ())
}

// Rocq: Yatp.yatp_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, x: u64, dx: u64, e: u64, j: u64, b: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = ltb(j, e);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&nbr, j);
      let tmp_3 = rocq_array::get::<u64>(&wt, j);
      let alive_clone = Rc::clone(&alive);
      let tmp_4 = scan_step(alive_clone, s, x, dx, tmp_2, tmp_3, b);
      scan_loop(nbr, wt, alive, s, x, dx, e, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      b
    },
  }
}

// Rocq: Yatp.yatp_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, L: u64, head: u64, b: Rc<bst>) -> Rc<bst> {
  bfs_loop(sa, nbr, wt, alive, s, L, head, b, ())
}

// Rocq: Yatp.yatp_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, L: u64, head: u64, b: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = ltb(head, b_tail(&b));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(head, L);
      match bdec(tmp_1) {
        sumbool::left => {
          let b_clone = Rc::clone(&b);
          let tmp_2 = b_comp(b_clone);
          let x = rocq_array::get::<u64>(&tmp_2, head);
          std::mem::drop(tmp_2);
          let tmp_3 = add(head, 1u64);
          let b_clone_1 = Rc::clone(&b);
          let tmp_4 = b_d(b_clone_1);
          let tmp_5 = rocq_array::get::<u64>(&tmp_4, x);
          std::mem::drop(tmp_4);
          let tmp_6 = rocq_array::get::<u64>(&sa, add(x, 1u64));
          let tmp_7 = rocq_array::get::<u64>(&sa, x);
          let nbr_clone = Rc::clone(&nbr);
          let wt_clone = Rc::clone(&wt);
          let alive_clone = Rc::clone(&alive);
          let tmp_8 = scan_loop_1(nbr_clone, wt_clone, alive_clone, s, x, tmp_5, tmp_6, tmp_7, b);
          bfs_loop(sa, nbr, wt, alive, s, L, tmp_3, tmp_8, ())
        },
        sumbool::right => {
          std::mem::drop(sa);
          std::mem::drop(nbr);
          std::mem::drop(wt);
          std::mem::drop(alive);
          b
        },
      }
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      b
    },
  }
}

// Rocq: Yatp.yatp_implem.bfs_init
// Variant: uncurried
pub fn bfs_init(s: u64, root: u64, vis: Rc<Array<u64>>, comp: Rc<Array<u64>>, par: Rc<Array<u64>>, d: Rc<Array<u64>>) -> Rc<bst> {
  let tmp = rocq_array::set::<u64>(vis, root, s);
  let tmp_1 = rocq_array::set::<u64>(comp, 0u64, root);
  let tmp_2 = rocq_array::set::<u64>(par, root, root);
  let tmp_3 = rocq_array::set::<u64>(d, root, 0u64);
  Rc::new(bst { b_vis: tmp, b_comp: tmp_1, b_par: tmp_2, b_d: tmp_3, b_tail: 1u64, b_flag: true })
}

// Rocq: Yatp.yatp_implem.bfs
// Variant: uncurried
pub fn bfs(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, root: u64, vis: Rc<Array<u64>>, comp: Rc<Array<u64>>, par: Rc<Array<u64>>, d: Rc<Array<u64>>) -> Rc<bst> {
  let tmp = rocq_array::length::<u64>(&comp);
  let tmp_1 = bfs_init(s, root, vis, comp, par, d);
  bfs_loop_1(sa, nbr, wt, alive, s, tmp, 0u64, tmp_1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Yatp.yatp_implem.m_vis
pub fn m_vis(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_vis_clone = Rc::clone(&m.m_vis);
  std::mem::drop(m);
  m_m_vis_clone
}

// Rocq: Yatp.yatp_implem.m_comp
pub fn m_comp(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_comp_clone = Rc::clone(&m.m_comp);
  std::mem::drop(m);
  m_m_comp_clone
}

// Rocq: Yatp.yatp_implem.m_par
pub fn m_par(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_par_clone = Rc::clone(&m.m_par);
  std::mem::drop(m);
  m_m_par_clone
}

// Rocq: Yatp.yatp_implem.m_d
pub fn m_d(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_d_clone = Rc::clone(&m.m_d);
  std::mem::drop(m);
  m_m_d_clone
}

// Rocq: Yatp.yatp_implem.sz_init
// Variant: uncurried
pub fn sz_init_1(comp: Rc<Array<u64>>, t: u64, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sz_init(comp, t, i, sz, big, ())
}

// Rocq: Yatp.yatp_implem.sz_init (local: sz_init)
// Variant: uncurried, lifted
pub fn sz_init(comp: Rc<Array<u64>>, t: u64, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&comp, i);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(sz, x, 1u64);
      let tmp_3 = rocq_array::set::<u64>(big, x, 0u64);
      sz_init(comp, t, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(comp);
      (sz, big)
    },
  }
}

// Rocq: Yatp.yatp_implem.sz_acc
// Variant: uncurried
pub fn sz_acc_1(comp: Rc<Array<u64>>, par: Rc<Array<u64>>, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sz_acc(comp, par, i, sz, big, ())
}

// Rocq: Yatp.yatp_implem.sz_acc (local: sz_acc)
// Variant: uncurried, lifted
pub fn sz_acc(comp: Rc<Array<u64>>, par: Rc<Array<u64>>, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&comp, i);
      let p = rocq_array::get::<u64>(&par, x);
      let v = rocq_array::get::<u64>(&sz, x);
      let tmp_1 = sub(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&sz, p);
      let tmp_3 = rocq_array::set::<u64>(sz, p, add(tmp_2, v));
      let tmp_4 = rocq_array::get::<u64>(&big, p);
      let tmp_5 = if ltb(tmp_4, v) {
        rocq_array::set::<u64>(big, p, v)
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
pub fn argmin_1(comp: Rc<Array<u64>>, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, t: u64, i: u64, bi: u64, bv: u64) -> u64 {
  argmin(comp, sz, big, t, i, bi, bv, ())
}

// Rocq: Yatp.yatp_implem.argmin (local: argmin)
// Variant: uncurried, lifted
pub fn argmin(comp: Rc<Array<u64>>, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, t: u64, i: u64, bi: u64, bv: u64, _H: ()) -> u64 {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&comp, i);
      let tmp_1 = rocq_array::get::<u64>(&sz, x);
      let up = sub(t, tmp_1);
      let tmp_2 = rocq_array::get::<u64>(&big, x);
      let v = if ltb(tmp_2, up) {
        up
      } else {
        rocq_array::get::<u64>(&big, x)
      };
      if ltb(v, bv) {
        argmin(comp, sz, big, t, add(i, 1u64), i, v, ())
      } else {
        argmin(comp, sz, big, t, add(i, 1u64), bi, bv, ())
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
pub fn centroid(comp: Rc<Array<u64>>, par: Rc<Array<u64>>, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, t: u64) -> (u64, (Rc<Array<u64>>, Rc<Array<u64>>)) {
  let comp_clone = Rc::clone(&comp);
  let sb = sz_init_1(comp_clone, t, 0u64, sz, big);
  let tmp = sub(t, 1u64);
  let sb_clone = Clone::clone(&sb);
  let tmp_1 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sb_clone);
  let tmp_2 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(sb);
  let comp_clone_1 = Rc::clone(&comp);
  let sb_ = sz_acc_1(comp_clone_1, par, tmp, tmp_1, tmp_2);
  let sb__clone = Clone::clone(&sb_);
  let tmp_3 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sb__clone);
  let sb__clone_1 = Clone::clone(&sb_);
  let tmp_4 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(sb__clone_1);
  let comp_clone_2 = Rc::clone(&comp);
  let tmp_5 = rocq_array::get::<u64>(&comp, argmin_1(comp_clone_2, tmp_3, tmp_4, t, 0u64, 0u64, t));
  std::mem::drop(comp);
  (tmp_5, sb_)
}

// Rocq: Yatp.yatp_implem.m_sz
pub fn m_sz(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_sz_clone = Rc::clone(&m.m_sz);
  std::mem::drop(m);
  m_m_sz_clone
}

// Rocq: Yatp.yatp_implem.m_big
pub fn m_big(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_big_clone = Rc::clone(&m.m_big);
  std::mem::drop(m);
  m_m_big_clone
}

// Rocq: Yatp.yatp_implem.pick
// Variant: uncurried
pub fn pick(alive: Rc<Array<bool>>, c: u64, r: u64) -> u64 {
  let tmp = rocq_array::length::<bool>(&alive);
  let tmp_1 = ltb(c, tmp);
  let tmp_2 = rocq_array::get::<bool>(&alive, c);
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
pub fn rscan_1(nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, dx: u64, e: u64, j: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  rscan(nbr, wt, alive, dx, e, j, d, ch, ())
}

// Rocq: Yatp.yatp_implem.rscan (local: rscan)
// Variant: uncurried, lifted
pub fn rscan(nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, dx: u64, e: u64, j: u64, d: Rc<Array<u64>>, ch: bool, _H: ()) -> (Rc<Array<u64>>, bool) {
  let tmp = ltb(j, e);
  match bdec(tmp) {
    sumbool::left => {
      let y = rocq_array::get::<u64>(&nbr, j);
      let tmp_1 = rocq_array::get::<u64>(&wt, j);
      let nv = add(dx, tmp_1);
      let tmp_2 = rocq_array::get::<bool>(&alive, y);
      let tmp_3 = rocq_array::length::<u64>(&d);
      let tmp_4 = andb(tmp_2, ltb(y, tmp_3));
      let tmp_5 = rocq_array::get::<u64>(&d, y);
      let tmp_6 = ltb(nv, tmp_5);
      if andb(tmp_4, tmp_6) {
        let tmp_7 = add(j, 1u64);
        let tmp_8 = rocq_array::set::<u64>(d, y, nv);
        rscan(nbr, wt, alive, dx, e, tmp_7, tmp_8, true, ())
      } else {
        rscan(nbr, wt, alive, dx, e, add(j, 1u64), d, ch, ())
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
pub fn rpass_1(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, comp: Rc<Array<u64>>, t: u64, i: u64, d: Rc<Array<u64>>, ch: bool) -> (Rc<Array<u64>>, bool) {
  rpass(sa, nbr, wt, alive, comp, t, i, d, ch, ())
}

// Rocq: Yatp.yatp_implem.rpass (local: rpass)
// Variant: uncurried, lifted
pub fn rpass(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, comp: Rc<Array<u64>>, t: u64, i: u64, d: Rc<Array<u64>>, ch: bool, _H: ()) -> (Rc<Array<u64>>, bool) {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let x = rocq_array::get::<u64>(&comp, i);
      let tmp_1 = rocq_array::get::<u64>(&d, x);
      let tmp_2 = rocq_array::get::<u64>(&sa, add(x, 1u64));
      let tmp_3 = rocq_array::get::<u64>(&sa, x);
      let nbr_clone = Rc::clone(&nbr);
      let wt_clone = Rc::clone(&wt);
      let alive_clone = Rc::clone(&alive);
      let r = rscan_1(nbr_clone, wt_clone, alive_clone, tmp_1, tmp_2, tmp_3, d, ch);
      let tmp_4 = add(i, 1u64);
      let r_clone = Clone::clone(&r);
      let tmp_5 = fst::<Rc<Array<u64>>, bool>(r_clone);
      rpass(sa, nbr, wt, alive, comp, t, tmp_4, tmp_5, snd::<Rc<Array<u64>>, bool>(r), ())
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
pub fn rloop_1(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, comp: Rc<Array<u64>>, t: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rloop(sa, nbr, wt, alive, comp, t, d, ())
}

// Rocq: Yatp.yatp_implem.rloop (local: rloop)
// Variant: uncurried, lifted
pub fn rloop(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, comp: Rc<Array<u64>>, t: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let sa_clone = Rc::clone(&sa);
  let nbr_clone = Rc::clone(&nbr);
  let wt_clone = Rc::clone(&wt);
  let alive_clone = Rc::clone(&alive);
  let comp_clone = Rc::clone(&comp);
  let pr = rpass_1(sa_clone, nbr_clone, wt_clone, alive_clone, comp_clone, t, 0u64, d, false);
  let pr_clone = Clone::clone(&pr);
  let tmp = snd::<Rc<Array<u64>>, bool>(pr_clone);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = fst::<Rc<Array<u64>>, bool>(pr);
      rloop(sa, nbr, wt, alive, comp, t, tmp_1, ())
    },
    sumbool::right => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      std::mem::drop(comp);
      fst::<Rc<Array<u64>>, bool>(pr)
    },
  }
}

// Rocq: Yatp.yatp_implem.relax
// Variant: uncurried
pub fn relax(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, comp: Rc<Array<u64>>, t: u64, b: Rc<bst>) -> Rc<Array<u64>> {
  if b_flag(&b) {
    std::mem::drop(sa);
    std::mem::drop(nbr);
    std::mem::drop(wt);
    std::mem::drop(alive);
    std::mem::drop(comp);
    b_d(b)
  } else {
    let tmp = b_d(b);
    rloop_1(sa, nbr, wt, alive, comp, t, tmp)
  }
}

// Rocq: Yatp.yatp_implem.lkey
// Variant: uncurried
pub fn lkey(X: u64, lo: u64, hi: u64) -> u64 {
  if eqb(lo, hi) {
    add(X, lo)
  } else {
    let tmp = sub(hi, lo);
    let tmp_1 = add(lo, div(tmp, 2u64));
    add(tmp_1, 1u64)
  }
}

// Rocq: Yatp.yatp_implem.l_st
pub fn l_st_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let l_l_st_clone = Rc::clone(&l.l_st);
  std::mem::drop(l);
  l_l_st_clone
}

// Rocq: Yatp.yatp_implem.l_st
// Variant: borrowed
pub fn l_st(l: &Rc<lct>) -> Rc<Array<u64>> {
  let tmp = l;
  Rc::clone(&tmp.l_st)
}

// Rocq: Yatp.yatp_implem.l_m
pub fn l_m_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let l_l_m_clone = Rc::clone(&l.l_m);
  std::mem::drop(l);
  l_l_m_clone
}

// Rocq: Yatp.yatp_implem.l_m
// Variant: borrowed
pub fn l_m(l: &Rc<lct>) -> Rc<Array<u64>> {
  let tmp = l;
  Rc::clone(&tmp.l_m)
}

// Rocq: Yatp.yatp_implem.l_b
pub fn l_b_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let l_l_b_clone = Rc::clone(&l.l_b);
  std::mem::drop(l);
  l_l_b_clone
}

// Rocq: Yatp.yatp_implem.l_b
// Variant: borrowed
pub fn l_b(l: &Rc<lct>) -> Rc<Array<u64>> {
  let tmp = l;
  Rc::clone(&tmp.l_b)
}

// Rocq: Yatp.yatp_implem.lc_insert
// Variant: uncurried
pub fn lc_insert_1(X: u64, s: u64, lo: u64, hi: u64, m: u64, b: u64, T: Rc<lct>) -> Rc<lct> {
  lc_insert(X, s, lo, hi, m, b, T, ())
}

// Rocq: Yatp.yatp_implem.lc_insert (local: lc_insert)
// Variant: uncurried, lifted
pub fn lc_insert(X: u64, s: u64, lo: u64, hi: u64, m: u64, b: u64, T: Rc<lct>, _H: ()) -> Rc<lct> {
  let k = lkey(X, lo, hi);
  let T_clone = Rc::clone(&T);
  let tmp = l_st_owned(T_clone);
  let tmp_1 = rocq_array::get::<u64>(&tmp, k);
  if eqb(tmp_1, s) {
    let T_clone_1 = Rc::clone(&T);
    let tmp_2 = l_m_owned(T_clone_1);
    let cm = rocq_array::get::<u64>(&tmp_2, k);
    let T_clone_2 = Rc::clone(&T);
    let tmp_3 = l_b_owned(T_clone_2);
    let cb = rocq_array::get::<u64>(&tmp_3, k);
    let tmp_4 = sub(hi, lo);
    let mid = add(lo, div(tmp_4, 2u64));
    let nb = ltb(add(mul(m, mid), b), add(mul(cm, mid), cb));
    let wm = if nb {
      m
    } else {
      cm
    };
    let wb = if nb {
      b
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
      b
    };
    let T1 = if nb {
      let T_clone_3 = Rc::clone(&T);
      let tmp_5 = l_st_owned(T_clone_3);
      let T_clone_4 = Rc::clone(&T);
      let tmp_6 = l_m_owned(T_clone_4);
      let tmp_7 = rocq_array::set::<u64>(tmp_6, k, m);
      let tmp_8 = l_b_owned(T);
      let tmp_9 = rocq_array::set::<u64>(tmp_8, k, b);
      Rc::new(lct { l_st: tmp_5, l_m: tmp_7, l_b: tmp_9 })
    } else {
      T
    };
    let tmp_10 = ltb(lo, hi);
    match bdec(tmp_10) {
      sumbool::left => {
        let tmp_11 = add(mul(om, lo), ob);
        let tmp_12 = add(mul(wm, lo), wb);
        if ltb(tmp_11, tmp_12) {
          std::mem::drop(tmp_3);
          std::mem::drop(tmp_2);
          std::mem::drop(tmp);
          lc_insert(X, s, lo, mid, om, ob, T1, ())
        } else {
          std::mem::drop(tmp_3);
          std::mem::drop(tmp_2);
          std::mem::drop(tmp);
          lc_insert(X, s, add(mid, 1u64), hi, om, ob, T1, ())
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
    let tmp_13 = l_st_owned(T_clone_5);
    let tmp_14 = rocq_array::set::<u64>(tmp_13, k, s);
    let T_clone_6 = Rc::clone(&T);
    let tmp_15 = l_m_owned(T_clone_6);
    let tmp_16 = rocq_array::set::<u64>(tmp_15, k, m);
    let tmp_17 = l_b_owned(T);
    let tmp_18 = rocq_array::set::<u64>(tmp_17, k, b);
    Rc::new(lct { l_st: tmp_14, l_m: tmp_16, l_b: tmp_18 })
  }
}

// Rocq: Yatp.yatp_implem.ins_loop
// Variant: uncurried
pub fn ins_loop_1(xp: Rc<Array<u64>>, comp: Rc<Array<u64>>, d: Rc<Array<u64>>, X: u64, s: u64, t: u64, i: u64, T: Rc<lct>) -> Rc<lct> {
  ins_loop(xp, comp, d, X, s, t, i, T, ())
}

// Rocq: Yatp.yatp_implem.ins_loop (local: ins_loop)
// Variant: uncurried, lifted
pub fn ins_loop(xp: Rc<Array<u64>>, comp: Rc<Array<u64>>, d: Rc<Array<u64>>, X: u64, s: u64, t: u64, i: u64, T: Rc<lct>, _H: ()) -> Rc<lct> {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&comp, i);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = sub(X, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&xp, sub(v, 1u64));
      let tmp_4 = rocq_array::get::<u64>(&d, v);
      let tmp_5 = lc_insert_1(X, s, 0u64, tmp_2, tmp_3, tmp_4, T);
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
pub fn lc_query_1(X: u64, s: u64, lo: u64, hi: u64, x: u64, T: &Rc<lct>) -> u64 {
  let X_1 = X;
  let s_1 = s;
  let lo_1 = lo;
  let hi_1 = hi;
  let x_1 = x;
  lc_query(X_1, s_1, lo_1, hi_1, x_1, T, ())
}

// Rocq: Yatp.yatp_implem.lc_query (local: lc_query)
// Variant: borrowed, uncurried, lifted
pub fn lc_query(X: u64, s: u64, lo: u64, hi: u64, x: u64, T: &Rc<lct>, _H: ()) -> u64 {
  let X_1 = X;
  let s_1 = s;
  let lo_1 = lo;
  let hi_1 = hi;
  let x_1 = x;
  let k = lkey(X_1, lo_1, hi_1);
  let tmp = l_st(T);
  let tmp_1 = rocq_array::get::<u64>(&tmp, k);
  let v = if eqb(tmp_1, s_1) {
    let tmp_2 = l_m(T);
    let tmp_3 = rocq_array::get::<u64>(&tmp_2, k);
    std::mem::drop(tmp_2);
    let tmp_4 = mul(tmp_3, x_1);
    let tmp_5 = l_b(T);
    let tmp_6 = rocq_array::get::<u64>(&tmp_5, k);
    std::mem::drop(tmp_5);
    add(tmp_4, tmp_6)
  } else {
    __rocq_global_443
  };
  let tmp_7 = ltb(lo_1, hi_1);
  match bdec(tmp_7) {
    sumbool::left => {
      let tmp_8 = sub(hi_1, lo_1);
      let mid = add(lo_1, div(tmp_8, 2u64));
      let r = if leb(x_1, mid) {
        lc_query(X_1, s_1, lo_1, mid, x_1, T, ())
      } else {
        lc_query(X_1, s_1, add(mid, 1u64), hi_1, x_1, T, ())
      };
      if ltb(r, v) {
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
pub fn qry_loop_1(xp: Rc<Array<u64>>, comp: Rc<Array<u64>>, d: Rc<Array<u64>>, X: u64, s: u64, t: u64, i: u64, T: Rc<lct>, best: Rc<Array<u64>>) -> Rc<Array<u64>> {
  qry_loop(xp, comp, d, X, s, t, i, T, best, ())
}

// Rocq: Yatp.yatp_implem.qry_loop (local: qry_loop)
// Variant: uncurried, lifted
pub fn qry_loop(xp: Rc<Array<u64>>, comp: Rc<Array<u64>>, d: Rc<Array<u64>>, X: u64, s: u64, t: u64, i: u64, T: Rc<lct>, best: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, t);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&comp, i);
      let tmp_1 = rocq_array::get::<u64>(&d, u);
      let tmp_2 = sub(X, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&xp, sub(u, 1u64));
      let q = add(tmp_1, lc_query_1(X, s, 0u64, tmp_2, tmp_3, &T));
      let tmp_4 = add(i, 1u64);
      let tmp_5 = rocq_array::get::<u64>(&best, u);
      let tmp_6 = if ltb(q, tmp_5) {
        rocq_array::set::<u64>(best, u, q)
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
pub fn m_best(m: Rc<mst>) -> Rc<Array<u64>> {
  let m_m_best_clone = Rc::clone(&m.m_best);
  std::mem::drop(m);
  m_m_best_clone
}

// Rocq: Yatp.yatp_implem.process
// Variant: uncurried
pub fn process(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, alive: Rc<Array<bool>>, r: u64, rnd: u64, S: Rc<mst>) -> (u64, Rc<mst>) {
  let tmp = mul(2u64, rnd);
  let S_clone = Rc::clone(&S);
  let tmp_1 = m_vis(S_clone);
  let S_clone_1 = Rc::clone(&S);
  let tmp_2 = m_comp(S_clone_1);
  let S_clone_2 = Rc::clone(&S);
  let tmp_3 = m_par(S_clone_2);
  let S_clone_3 = Rc::clone(&S);
  let tmp_4 = m_d(S_clone_3);
  let sa_clone = Rc::clone(&sa);
  let nbr_clone = Rc::clone(&nbr);
  let wt_clone = Rc::clone(&wt);
  let alive_clone = Rc::clone(&alive);
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
  let tmp_10 = fst::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(cr_clone);
  let alive_clone_1 = Rc::clone(&alive);
  let c = pick(alive_clone_1, tmp_10, r);
  let tmp_11 = add(mul(2u64, rnd), 1u64);
  let b1_clone_2 = Rc::clone(&b1);
  let tmp_12 = b_vis(b1_clone_2);
  let b1_clone_3 = Rc::clone(&b1);
  let tmp_13 = b_comp(b1_clone_3);
  let b1_clone_4 = Rc::clone(&b1);
  let tmp_14 = b_par(b1_clone_4);
  let tmp_15 = b_d(b1);
  let sa_clone_1 = Rc::clone(&sa);
  let nbr_clone_1 = Rc::clone(&nbr);
  let wt_clone_1 = Rc::clone(&wt);
  let alive_clone_2 = Rc::clone(&alive);
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
  let xp_clone = Rc::clone(&xp);
  let d_clone = Rc::clone(&d);
  let T = ins_loop_1(xp_clone, tmp_17, d_clone, X, rnd, t, 0u64, tmp_18);
  let b2_clone_3 = Rc::clone(&b2);
  let tmp_19 = b_comp(b2_clone_3);
  let tmp_20 = m_best(S);
  let d_clone_1 = Rc::clone(&d);
  let T_clone = Rc::clone(&T);
  let best = qry_loop_1(xp, tmp_19, d_clone_1, X, rnd, t, 0u64, T_clone, tmp_20);
  let b2_clone_4 = Rc::clone(&b2);
  let tmp_21 = b_vis(b2_clone_4);
  let b2_clone_5 = Rc::clone(&b2);
  let tmp_22 = b_comp(b2_clone_5);
  let tmp_23 = b_par(b2);
  let cr_clone_1 = Clone::clone(&cr);
  let tmp_24 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(snd::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(cr_clone_1));
  let tmp_25 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(snd::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(cr));
  (c, Rc::new(mst { m_vis: tmp_21, m_comp: tmp_22, m_par: tmp_23, m_d: d, m_sz: tmp_24, m_big: tmp_25, m_T: T, m_best: best }))
}

// Rocq: Yatp.yatp_implem.main_loop
// Variant: uncurried
pub fn main_loop_1(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, r: u64, rnd: u64, alive: Rc<Array<bool>>, S: Rc<mst>) -> Rc<Array<u64>> {
  main_loop(sa, nbr, wt, xp, X, r, rnd, alive, S, ())
}

// Rocq: Yatp.yatp_implem.main_loop (local: main_loop)
// Variant: uncurried, lifted
pub fn main_loop(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, r: u64, rnd: u64, alive: Rc<Array<bool>>, S: Rc<mst>, _H: ()) -> Rc<Array<u64>> {
  let tmp = rocq_array::length::<bool>(&alive);
  let tmp_1 = ltb(r, tmp);
  match bdec(tmp_1) {
    sumbool::left => {
      let tmp_2 = rocq_array::get::<bool>(&alive, r);
      match bdec(tmp_2) {
        sumbool::left => {
          let sa_clone = Rc::clone(&sa);
          let nbr_clone = Rc::clone(&nbr);
          let wt_clone = Rc::clone(&wt);
          let xp_clone = Rc::clone(&xp);
          let alive_clone = Rc::clone(&alive);
          let cS = process(sa_clone, nbr_clone, wt_clone, xp_clone, X, alive_clone, r, rnd, S);
          let tmp_3 = add(rnd, 1u64);
          let cS_clone = Clone::clone(&cS);
          let tmp_4 = rocq_array::set::<bool>(alive, fst::<u64, Rc<mst>>(cS_clone), false);
          main_loop(sa, nbr, wt, xp, X, r, tmp_3, tmp_4, snd::<u64, Rc<mst>>(cS), ())
        },
        sumbool::right => {
          main_loop(sa, nbr, wt, xp, X, add(r, 1u64), rnd, alive, S, ())
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
pub fn sum_loop_1(best: Rc<Array<u64>>, n1: u64, i: u64, acc: u64) -> u64 {
  sum_loop(best, n1, i, acc, ())
}

// Rocq: Yatp.yatp_implem.sum_loop (local: sum_loop)
// Variant: uncurried, lifted
pub fn sum_loop(best: Rc<Array<u64>>, n1: u64, i: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&best, i);
      sum_loop(best, n1, tmp_1, add(acc, tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(best);
      acc
    },
  }
}

// Rocq: Yatp.yatp_implem.yatp_impl
// Variant: uncurried
pub fn yatp_impl(xp: Rc<Array<u64>>, xu: Rc<Array<u64>>, xv: Rc<Array<u64>>, xw: Rc<Array<u64>>) -> u64 {
  let n = rocq_array::length::<u64>(&xp);
  let n1 = add(n, 1u64);
  let tmp = rocq_array::length::<u64>(&xu);
  let tmp_1 = rocq_array::length::<u64>(&xu);
  let hh = add(tmp, tmp_1);
  let tmp_2 = rocq_array::make::<u64>(n1, 0u64);
  let xu_clone = Rc::clone(&xu);
  let xv_clone = Rc::clone(&xv);
  let deg = deg_loop_1(xu_clone, xv_clone, hh, 0u64, tmp_2);
  let tmp_3 = rocq_array::make::<u64>(add(n1, 1u64), 0u64);
  let tmp_4 = rocq_array::make::<u64>(n1, 0u64);
  let sp = start_loop_1(deg, n1, 0u64, tmp_3, tmp_4);
  let sp_clone = Clone::clone(&sp);
  let tmp_5 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(sp_clone);
  let tmp_6 = rocq_array::make::<u64>(hh, 0u64);
  let tmp_7 = rocq_array::make::<u64>(hh, 0u64);
  let nw = fill_loop_1(xu, xv, xw, hh, 0u64, tmp_5, tmp_6, tmp_7);
  let xp_clone = Rc::clone(&xp);
  let X = add(max_loop_1(xp_clone, n, 0u64, 0u64), 1u64);
  let tmp_8 = rocq_array::make::<bool>(n1, false);
  let alive = true_loop_1(n1, 1u64, tmp_8);
  let tmp_9 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_10 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_11 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_12 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_13 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_14 = rocq_array::make::<u64>(n1, 0u64);
  let tmp_15 = rocq_array::make::<u64>(add(X, X), 0u64);
  let tmp_16 = rocq_array::make::<u64>(add(X, X), 0u64);
  let tmp_17 = rocq_array::make::<u64>(add(X, X), 0u64);
  let tmp_18 = Rc::new(lct { l_st: tmp_15, l_m: tmp_16, l_b: tmp_17 });
  let tmp_19 = rocq_array::make::<u64>(n1, __rocq_global_443);
  let S = Rc::new(mst { m_vis: tmp_9, m_comp: tmp_10, m_par: tmp_11, m_d: tmp_12, m_sz: tmp_13, m_big: tmp_14, m_T: tmp_18, m_best: tmp_19 });
  let tmp_20 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sp);
  let nw_clone = Clone::clone(&nw);
  let tmp_21 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(nw_clone);
  let tmp_22 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(nw);
  let best = main_loop_1(tmp_20, tmp_21, tmp_22, xp, X, 1u64, 1u64, alive, S);
  sum_loop_1(best, n1, 1u64, 0u64)
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
const __rocq_global_443: u64 = 4611686018427387904u64;