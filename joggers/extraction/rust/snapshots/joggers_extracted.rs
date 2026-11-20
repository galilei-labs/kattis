#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct bst {
  pub vis: Array<bool>,
  pub dst: Array<Int63>,
  pub par: Array<Int63>,
  pub pe: Array<Int63>,
  pub ord: Array<Int63>,
  pub tl: Int63,
}

impl Clone for bst {
  fn clone(&self) -> Self {
    match self {
      bst { vis: __field0, dst: __field1, par: __field2, pe: __field3, ord: __field4, tl: __field5 } => bst { vis: Clone::clone(__field0), dst: Clone::clone(__field1), par: Clone::clone(__field2), pe: Clone::clone(__field3), ord: Clone::clone(__field4), tl: Clone::clone(__field5) },
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

// Rocq: Joggers.joggers_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Joggers.joggers_implem.lamp_loop
// Variant: uncurried
pub fn lamp_loop_1(xl: Array<Int63>, L: Int63, i: Int63, inl: Array<bool>) -> Array<bool> {
  lamp_loop(xl, L, i, inl, ())
}

// Rocq: Joggers.joggers_implem.lamp_loop (local: lamp_loop)
// Variant: uncurried, lifted
pub fn lamp_loop(xl: Array<Int63>, L: Int63, i: Int63, inl: Array<bool>, _H: ()) -> Array<bool> {
  let tmp = i < L;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = xl.get_cloned(i);
      lamp_loop(xl, L, tmp_1, inl.set(tmp_2, true), ())
    },
    sumbool::right => {
      std::mem::drop(xl);
      inl
    },
  }
}

// Rocq: Joggers.joggers_implem.ep
// Variant: uncurried
pub fn ep(xa: Array<Int63>, xb: Array<Int63>, m: Int63, k: Int63) -> Int63 {
  if k < m {
    std::mem::drop(xb);
    let tmp = xa.get_cloned(k);
    std::mem::drop(xa);
    tmp
  } else {
    std::mem::drop(xa);
    let tmp_1 = xb.get_cloned(k - m);
    std::mem::drop(xb);
    tmp_1
  }
}

// Rocq: Joggers.joggers_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xa: Array<Int63>, xb: Array<Int63>, m: Int63, K: Int63, i: Int63, cnt: Array<Int63>) -> Array<Int63> {
  cnt_loop(xa, xb, m, K, i, cnt, ())
}

// Rocq: Joggers.joggers_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xa: Array<Int63>, xb: Array<Int63>, m: Int63, K: Int63, i: Int63, cnt: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < K;
  match bdec(tmp) {
    sumbool::left => {
      let xa_clone = Clone::clone(&xa);
      let xb_clone = Clone::clone(&xb);
      let w = ep(xa_clone, xb_clone, m, i);
      let tmp_1 = i + int63!(1);
      let tmp_2 = cnt.get_cloned(w);
      cnt_loop(xa, xb, m, K, tmp_1, cnt.set(w, tmp_2 + int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      cnt
    },
  }
}

// Rocq: Joggers.joggers_implem.off_loop
// Variant: uncurried
pub fn off_loop_1(cnt: Array<Int63>, V: Int63, v: Int63, off: Array<Int63>, cur: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  off_loop(cnt, V, v, off, cur, ())
}

// Rocq: Joggers.joggers_implem.off_loop (local: off_loop)
// Variant: uncurried, lifted
pub fn off_loop(cnt: Array<Int63>, V: Int63, v: Int63, off: Array<Int63>, cur: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = v < V;
  match bdec(tmp) {
    sumbool::left => {
      let o = off.get_cloned(v);
      let tmp_1 = v + int63!(1);
      let tmp_2 = v + int63!(1);
      let tmp_3 = cnt.get_cloned(v);
      off_loop(cnt, V, tmp_1, off.set(tmp_2, o + tmp_3), cur.set(v, o), ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      (off, cur)
    },
  }
}

// Rocq: Joggers.joggers_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(xa: Array<Int63>, xb: Array<Int63>, m: Int63, K: Int63, i: Int63, cur: Array<Int63>, adj: Array<Int63>) -> Array<Int63> {
  fill_loop(xa, xb, m, K, i, cur, adj, ())
}

// Rocq: Joggers.joggers_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(xa: Array<Int63>, xb: Array<Int63>, m: Int63, K: Int63, i: Int63, cur: Array<Int63>, adj: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < K;
  match bdec(tmp) {
    sumbool::left => {
      let xa_clone = Clone::clone(&xa);
      let xb_clone = Clone::clone(&xb);
      let w = ep(xa_clone, xb_clone, m, i);
      let c = cur.get_cloned(w);
      fill_loop(xa, xb, m, K, i + int63!(1), cur.set(w, c + int63!(1)), adj.set(c, i), ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(cur);
      adj
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Joggers.joggers_implem.tl
pub fn tl_owned(b_1: Rc<bst>) -> Int63 {
  let b_tl_clone = Clone::clone(&b_1.tl);
  std::mem::drop(b_1);
  b_tl_clone
}

// Rocq: Joggers.joggers_implem.tl
// Variant: borrowed
pub fn tl(b_1: &Rc<bst>) -> Int63 {
  let tmp = b_1;
  Clone::clone(&tmp.tl)
}

// Rocq: Joggers.joggers_implem.ord
pub fn ord(b_1: Rc<bst>) -> Array<Int63> {
  let b_ord_clone = Clone::clone(&b_1.ord);
  std::mem::drop(b_1);
  b_ord_clone
}

// Rocq: Joggers.joggers_implem.oth
// Variant: uncurried
pub fn oth(xa: Array<Int63>, xb: Array<Int63>, m: Int63, k: Int63) -> Int63 {
  if k < m {
    std::mem::drop(xa);
    let tmp = xb.get_cloned(k);
    std::mem::drop(xb);
    tmp
  } else {
    std::mem::drop(xb);
    let tmp_1 = xa.get_cloned(k - m);
    std::mem::drop(xa);
    tmp_1
  }
}

// Rocq: Joggers.joggers_implem.vis
pub fn vis(b_1: Rc<bst>) -> Array<bool> {
  let b_vis_clone = Clone::clone(&b_1.vis);
  std::mem::drop(b_1);
  b_vis_clone
}

// Rocq: Joggers.joggers_implem.eid
// Variant: uncurried
pub fn eid(m: Int63, k: Int63) -> Int63 {
  if k < m {
    k
  } else {
    k - m
  }
}

// Rocq: Joggers.joggers_implem.dst
pub fn dst(b_1: Rc<bst>) -> Array<Int63> {
  let b_dst_clone = Clone::clone(&b_1.dst);
  std::mem::drop(b_1);
  b_dst_clone
}

// Rocq: Joggers.joggers_implem.par
pub fn par(b_1: Rc<bst>) -> Array<Int63> {
  let b_par_clone = Clone::clone(&b_1.par);
  std::mem::drop(b_1);
  b_par_clone
}

// Rocq: Joggers.joggers_implem.pe
pub fn pe(b_1: Rc<bst>) -> Array<Int63> {
  let b_pe_clone = Clone::clone(&b_1.pe);
  std::mem::drop(b_1);
  b_pe_clone
}

// Rocq: Joggers.joggers_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(xa: Array<Int63>, xb: Array<Int63>, xd: Array<Int63>, m: Int63, adj: Array<Int63>, u: Int63, du: Int63, hi: Int63, i: Int63, st: Rc<bst>) -> Rc<bst> {
  scan_loop(xa, xb, xd, m, adj, u, du, hi, i, st, ())
}

// Rocq: Joggers.joggers_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(xa: Array<Int63>, xb: Array<Int63>, xd: Array<Int63>, m: Int63, adj: Array<Int63>, u: Int63, du: Int63, hi: Int63, i: Int63, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = i < hi;
  match bdec(tmp) {
    sumbool::left => {
      let k = adj.get_cloned(i);
      let xa_clone = Clone::clone(&xa);
      let xb_clone = Clone::clone(&xb);
      let w = oth(xa_clone, xb_clone, m, k);
      let st_clone = Rc::clone(&st);
      let tmp_1 = vis(st_clone);
      let tmp_2 = tmp_1.get_cloned(w);
      let st_ = if tmp_2 {
        std::mem::drop(tmp_1);
        st
      } else {
        std::mem::drop(tmp_1);
        let e = eid(m, k);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = vis(st_clone_1).set(w, true);
        let st_clone_2 = Rc::clone(&st);
        let tmp_4 = dst(st_clone_2);
        let tmp_5 = xd.get_cloned(e);
        let tmp_6 = tmp_4.set(w, du + tmp_5);
        let st_clone_3 = Rc::clone(&st);
        let tmp_7 = par(st_clone_3).set(w, u);
        let st_clone_4 = Rc::clone(&st);
        let tmp_8 = pe(st_clone_4).set(w, e);
        let st_clone_5 = Rc::clone(&st);
        let tmp_9 = ord(st_clone_5);
        let tmp_10 = tl(&st);
        Rc::new(bst { vis: tmp_3, dst: tmp_6, par: tmp_7, pe: tmp_8, ord: tmp_9.set(tmp_10, w), tl: tl_owned(st) + int63!(1) })
      };
      scan_loop(xa, xb, xd, m, adj, u, du, hi, i + int63!(1), st_, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(xd);
      std::mem::drop(adj);
      st
    },
  }
}

// Rocq: Joggers.joggers_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(xa: Array<Int63>, xb: Array<Int63>, xd: Array<Int63>, m: Int63, adj: Array<Int63>, off: Array<Int63>, h: Int63, st: Rc<bst>) -> Rc<bst> {
  bfs_loop(xa, xb, xd, m, adj, off, h, st, ())
}

// Rocq: Joggers.joggers_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(xa: Array<Int63>, xb: Array<Int63>, xd: Array<Int63>, m: Int63, adj: Array<Int63>, off: Array<Int63>, h: Int63, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = h < tl(&st);
  match bdec(tmp) {
    sumbool::left => {
      let st_clone = Rc::clone(&st);
      let tmp_1 = ord(st_clone);
      let u = tmp_1.get_cloned(h);
      std::mem::drop(tmp_1);
      let st_clone_1 = Rc::clone(&st);
      let tmp_2 = dst(st_clone_1);
      let tmp_3 = tmp_2.get_cloned(u);
      std::mem::drop(tmp_2);
      let tmp_4 = off.get_cloned(u + int63!(1));
      let tmp_5 = off.get_cloned(u);
      let xa_clone = Clone::clone(&xa);
      let xb_clone = Clone::clone(&xb);
      let xd_clone = Clone::clone(&xd);
      let adj_clone = Clone::clone(&adj);
      let st_ = scan_loop_1(xa_clone, xb_clone, xd_clone, m, adj_clone, u, tmp_3, tmp_4, tmp_5, st);
      bfs_loop(xa, xb, xd, m, adj, off, h + int63!(1), st_, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(xd);
      std::mem::drop(adj);
      std::mem::drop(off);
      st
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
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

// Rocq: Joggers.joggers_implem.sweep_loop
// Variant: uncurried
pub fn sweep_loop_1(s: Int63, inl: Array<bool>, ord_1: Array<Int63>, par_1: Array<Int63>, dst_1: Array<Int63>, i: Int63, ch: Array<bool>, c: Int63) -> Int63 {
  sweep_loop(s, inl, ord_1, par_1, dst_1, i, ch, c, ())
}

// Rocq: Joggers.joggers_implem.sweep_loop (local: sweep_loop)
// Variant: uncurried, lifted
pub fn sweep_loop(s: Int63, inl: Array<bool>, ord_1: Array<Int63>, par_1: Array<Int63>, dst_1: Array<Int63>, i: Int63, ch: Array<bool>, c: Int63, _H: ()) -> Int63 {
  let tmp = int63!(0) < i;
  match bdec(tmp) {
    sumbool::left => {
      let v = ord_1.get_cloned(i);
      let p = par_1.get_cloned(v);
      let dp = dst_1.get_cloned(p);
      let tmp_1 = dp + dp < s;
      let tmp_2 = inl.get_cloned(v);
      let tmp_3 = ch.get_cloned(v);
      let tmp_4 = andb(tmp_1, negb(orb(tmp_2, tmp_3)));
      let tmp_5 = inl.get_cloned(p);
      let tmp_6 = ch.get_cloned(p);
      let tmp_7 = negb(orb(tmp_5, tmp_6));
      if andb(tmp_4, tmp_7) {
        sweep_loop(s, inl, ord_1, par_1, dst_1, i - int63!(1), ch.set(p, true), c + int63!(1), ())
      } else {
        sweep_loop(s, inl, ord_1, par_1, dst_1, i - int63!(1), ch, c, ())
      }
    },
    sumbool::right => {
      std::mem::drop(inl);
      std::mem::drop(ord_1);
      std::mem::drop(par_1);
      std::mem::drop(dst_1);
      std::mem::drop(ch);
      c
    },
  }
}

// Rocq: Joggers.joggers_implem.joggers_impl
// Variant: uncurried
pub fn joggers_impl(n: Int63, s: Int63, xa: Array<Int63>, xb: Array<Int63>, xd: Array<Int63>, xl: Array<Int63>) -> Int63 {
  let m = xa.length();
  let K = m + m;
  let V = n + int63!(1);
  let tmp = xl.length();
  let inl = lamp_loop_1(xl, tmp, int63!(0), Array::<bool>::make(V, false));
  let tmp_1 = Array::<Int63>::make(V, int63!(0));
  let xa_clone = Clone::clone(&xa);
  let xb_clone = Clone::clone(&xb);
  let cnt = cnt_loop_1(xa_clone, xb_clone, m, K, int63!(0), tmp_1);
  let tmp_2 = Array::<Int63>::make(V + int63!(1), int63!(0));
  let tmp_3 = Array::<Int63>::make(V, int63!(0));
  let oc = off_loop_1(cnt, V, int63!(0), tmp_2, tmp_3);
  let oc_clone = Clone::clone(&oc);
  let tmp_4 = snd::<Array<Int63>, Array<Int63>>(oc_clone);
  let tmp_5 = Array::<Int63>::make(K, int63!(0));
  let xa_clone_1 = Clone::clone(&xa);
  let xb_clone_1 = Clone::clone(&xb);
  let adj = fill_loop_1(xa_clone_1, xb_clone_1, m, K, int63!(0), tmp_4, tmp_5);
  let st0 = Rc::new(bst { vis: Array::<bool>::make(V, false).set(int63!(1), true), dst: Array::<Int63>::make(V, int63!(0)), par: Array::<Int63>::make(V, int63!(0)), pe: Array::<Int63>::make(V, int63!(0)), ord: Array::<Int63>::make(n, int63!(0)).set(int63!(0), int63!(1)), tl: int63!(1) });
  let st = bfs_loop_1(xa, xb, xd, m, adj, fst::<Array<Int63>, Array<Int63>>(oc), int63!(0), st0);
  let st_clone = Rc::clone(&st);
  let tmp_6 = ord(st_clone);
  let st_clone_1 = Rc::clone(&st);
  let tmp_7 = par(st_clone_1);
  let st_clone_2 = Rc::clone(&st);
  sweep_loop_1(s, inl, tmp_6, tmp_7, dst(st_clone_2), tl_owned(st) - int63!(1), Array::<bool>::make(V, false), int63!(0))
}
