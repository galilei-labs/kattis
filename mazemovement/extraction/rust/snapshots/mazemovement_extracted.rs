#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct st {
  pub s_tbl: Array<Int63>,
  pub s_ex: Array<Int63>,
  pub s_h: Array<Int63>,
  pub s_cur: Array<Int63>,
  pub s_cnt: Array<Int63>,
  pub s_q: Array<Int63>,
  pub s_qh: Int63,
  pub s_ql: Int63,
  pub s_cu: Int63,
  pub s_rl: Int63,
}

impl Clone for st {
  fn clone(&self) -> Self {
    match self {
      st { s_tbl: __field0, s_ex: __field1, s_h: __field2, s_cur: __field3, s_cnt: __field4, s_q: __field5, s_qh: __field6, s_ql: __field7, s_cu: __field8, s_rl: __field9 } => st { s_tbl: Clone::clone(__field0), s_ex: Clone::clone(__field1), s_h: Clone::clone(__field2), s_cur: Clone::clone(__field3), s_cnt: Clone::clone(__field4), s_q: Clone::clone(__field5), s_qh: Clone::clone(__field6), s_ql: Clone::clone(__field7), s_cu: Clone::clone(__field8), s_rl: Clone::clone(__field9) },
    }
  }
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

pub type uint = Int63;

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Mazemovement.mazemovement_implem.nn
pub fn nn(x: Array<Int63>) -> Int63 {
  let tmp = x.length();
  std::mem::drop(x);
  tmp
}

// Rocq: Mazemovement.mazemovement_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Mazemovement.mazemovement_implem.rng_ok
// Variant: uncurried
pub fn rng_ok_1(x: Array<Int63>, n: Int63, i: Int63) -> bool {
  rng_ok(x, n, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.rng_ok (local: rng_ok)
// Variant: uncurried, lifted
pub fn rng_ok(x: Array<Int63>, n: Int63, i: Int63, _H: ()) -> bool {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = x.get_cloned(i);
      let tmp_2 = int63!(2) <= tmp_1;
      let tmp_3 = x.get_cloned(i);
      let tmp_4 = tmp_3 <= int63!(2000000000);
      if andb(tmp_2, tmp_4) {
        rng_ok(x, n, i + int63!(1), ())
      } else {
        std::mem::drop(x);
        false
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      true
    },
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

// Rocq: Mazemovement.mazemovement_implem.amin
// Variant: uncurried
pub fn amin_1(x: Array<Int63>, n: Int63, i: Int63, best: Int63) -> Int63 {
  amin(x, n, i, best, ())
}

// Rocq: Mazemovement.mazemovement_implem.amin (local: amin)
// Variant: uncurried, lifted
pub fn amin(x: Array<Int63>, n: Int63, i: Int63, best: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x.get_cloned(i);
      let tmp_3 = x.get_cloned(best);
      let tmp_4 = if tmp_2 < tmp_3 {
        i
      } else {
        best
      };
      amin(x, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      best
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.ss
pub fn ss(x: Array<Int63>) -> Int63 {
  let x_clone = Clone::clone(&x);
  amin_1(x, nn(x_clone), int63!(1), int63!(0))
}

// Rocq: Mazemovement.mazemovement_implem.amax
// Variant: uncurried
pub fn amax_1(x: Array<Int63>, n: Int63, i: Int63, best: Int63) -> Int63 {
  amax(x, n, i, best, ())
}

// Rocq: Mazemovement.mazemovement_implem.amax (local: amax)
// Variant: uncurried, lifted
pub fn amax(x: Array<Int63>, n: Int63, i: Int63, best: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let tmp_2 = x.get_cloned(best);
      let tmp_3 = x.get_cloned(i);
      let tmp_4 = if tmp_2 < tmp_3 {
        i
      } else {
        best
      };
      amax(x, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      best
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.tt
pub fn tt(x: Array<Int63>) -> Int63 {
  let x_clone = Clone::clone(&x);
  amax_1(x, nn(x_clone), int63!(1), int63!(0))
}

// Rocq: Mazemovement.mazemovement_implem.guard
pub fn guard(x: Array<Int63>) -> bool {
  let x_clone = Clone::clone(&x);
  let tmp = int63!(2) <= nn(x_clone);
  let x_clone_1 = Clone::clone(&x);
  let tmp_1 = andb(tmp, nn(x_clone_1) <= int63!(1000));
  let x_clone_2 = Clone::clone(&x);
  let tmp_2 = nn(x_clone_2);
  let x_clone_3 = Clone::clone(&x);
  let tmp_3 = andb(tmp_1, rng_ok_1(x_clone_3, tmp_2, int63!(0)));
  let x_clone_4 = Clone::clone(&x);
  andb(tmp_3, negb(ss(x_clone_4) == tt(x)))
}

// Rocq: Mazemovement.mazemovement_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop(a_1, b_1, ())
}

// Rocq: Mazemovement.mazemovement_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a_1: Int63, b_1: Int63, _H: ()) -> Int63 {
  let tmp = b_1 == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      a_1
    },
    sumbool::right => {
      let tmp_1 = a_1 % b_1;
      gcd_loop(b_1, tmp_1, ())
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.igcd
// Variant: uncurried
pub fn igcd(a_1: Int63, b_1: Int63) -> Int63 {
  gcd_loop_1(a_1, b_1)
}

// Rocq: Mazemovement.mazemovement_implem.capf
// Variant: uncurried
pub fn capf(x: Array<Int63>, i: Int63, j: Int63) -> Int63 {
  if i == j {
    std::mem::drop(x);
    int63!(0)
  } else {
    let tmp = x.get_cloned(i);
    let tmp_1 = x.get_cloned(j);
    let g = igcd(tmp, tmp_1);
    if int63!(1) < g {
      std::mem::drop(x);
      g
    } else {
      std::mem::drop(x);
      int63!(0)
    }
  }
}

// Rocq: Mazemovement.mazemovement_implem.fill_row
// Variant: uncurried
pub fn fill_row_1(x: Array<Int63>, n: Int63, i: Int63, tbl: Array<Int63>, j: Int63) -> Array<Int63> {
  fill_row(x, n, i, tbl, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.fill_row (local: fill_row)
// Variant: uncurried, lifted
pub fn fill_row(x: Array<Int63>, n: Int63, i: Int63, tbl: Array<Int63>, j: Int63, _H: ()) -> Array<Int63> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let c = capf(x_clone, i, j);
      let tmp_1 = tbl.set(i * n + j, c);
      let tmp_2 = j * n + i;
      fill_row(x, n, i, tmp_1.set(tmp_2, c), j + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tbl
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.fill_tab
// Variant: uncurried
pub fn fill_tab_1(x: Array<Int63>, n: Int63, tbl: Array<Int63>, i: Int63) -> Array<Int63> {
  fill_tab(x, n, tbl, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.fill_tab (local: fill_tab)
// Variant: uncurried, lifted
pub fn fill_tab(x: Array<Int63>, n: Int63, tbl: Array<Int63>, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Clone::clone(&x);
      let tmp_1 = fill_row_1(x_clone, n, i, tbl, i);
      fill_tab(x, n, tmp_1, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tbl
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.sat
// Variant: uncurried
pub fn sat_1(n: Int63, s: Int63, t: Int63, tbl: Array<Int63>, ex: Array<Int63>, q: Array<Int63>, ql: Int63, v: Int63) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  sat(n, s, t, tbl, ex, q, ql, v, ())
}

// Rocq: Mazemovement.mazemovement_implem.sat (local: sat)
// Variant: uncurried, lifted
pub fn sat(n: Int63, s: Int63, t: Int63, tbl: Array<Int63>, ex: Array<Int63>, q: Array<Int63>, ql: Int63, v: Int63, _H: ()) -> (((Array<Int63>, Array<Int63>), Array<Int63>), Int63) {
  let tmp = v < n;
  match bdec(tmp) {
    sumbool::left => {
      let c = tbl.get_cloned(s * n + v);
      let tbl1 = tbl.set(s * n + v, int63!(0));
      let tmp_1 = v * n + s;
      let tmp_2 = tbl1.get_cloned(v * n + s);
      let tbl2 = tbl1.set(tmp_1, tmp_2 + c);
      let ex1 = ex.set(v, c);
      let tmp_3 = andb(int63!(0) < c, negb(v == t));
      let b_1 = andb(tmp_3, negb(v == s));
      let q1 = if b_1 {
        q.set(ql, v)
      } else {
        q
      };
      let ql1 = if b_1 {
        ql + int63!(1)
      } else {
        ql
      };
      sat(n, s, t, tbl2, ex1, q1, ql1, v + int63!(1), ())
    },
    sumbool::right => {
      (((tbl, ex), q), ql)
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.has_val
// Variant: uncurried
pub fn has_val_1(d: Array<Int63>, n: Int63, L: Int63, j: Int63) -> bool {
  has_val(d, n, L, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.has_val (local: has_val)
// Variant: uncurried, lifted
pub fn has_val(d: Array<Int63>, n: Int63, L: Int63, j: Int63, _H: ()) -> bool {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d.get_cloned(j);
      if tmp_1 == L {
        std::mem::drop(d);
        true
      } else {
        has_val(d, n, L, j + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(d);
      false
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.amap
// Variant: uncurried
pub fn amap_1(F: Rc<dyn Fn(Int63, Int63) -> Int63>, a_1: Array<Int63>, i: Int63, m: Int63) -> Array<Int63> {
  amap(F, a_1, i, m, ())
}

// Rocq: Mazemovement.mazemovement_implem.amap (local: amap)
// Variant: uncurried, lifted
pub fn amap(F: Rc<dyn Fn(Int63, Int63) -> Int63>, a_1: Array<Int63>, i: Int63, m: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < m;
  match bdec(tmp) {
    sumbool::left => {
      let o = a_1.get_cloned(i);
      let F_ref: &Rc<dyn Fn(Int63, Int63) -> Int63> = &F;
      let w = F_ref(i, o);
      let tmp_1 = if w == o {
        a_1
      } else {
        a_1.set(i, w)
      };
      amap(F, tmp_1, i + int63!(1), m, ())
    },
    sumbool::right => {
      std::mem::drop(F);
      a_1
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.relaxF
// Variant: borrowed, uncurried
pub fn relaxF(tbl: &Array<Int63>, n: Int63, b_1: Int63, L1: Int63, a_1: Int63, o: Int63) -> Int63 {
  let n_1 = n;
  let b_2 = b_1;
  let L1_1 = L1;
  let a_2 = a_1;
  let o_1 = o;
  let tmp = int63!(0) < tbl.get_cloned(a_2 * n_1 + b_2);
  let tmp_1 = L1_1 < o_1;
  if andb(tmp, tmp_1) {
    L1_1
  } else {
    o_1
  }
}

// Rocq: Mazemovement.mazemovement_implem.lscan
// Variant: uncurried
pub fn lscan_1(tbl: Array<Int63>, n: Int63, L: Int63, d: Array<Int63>, j: Int63) -> Array<Int63> {
  lscan(tbl, n, L, d, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.lscan (local: lscan)
// Variant: uncurried, lifted
pub fn lscan(tbl: Array<Int63>, n: Int63, L: Int63, d: Array<Int63>, j: Int63, _H: ()) -> Array<Int63> {
  let tmp = j < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = d.get_cloned(j);
      let tmp_2 = if tmp_1 == L {
        let tmp_3 = L + int63!(1);
        let tbl_clone = Clone::clone(&tbl);
        let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
          let __anf_capture_49 = n;
          let __anf_capture_51 = j;
          move |v55: Int63, v56: Int63| -> Int63 {
            let tbl = &tbl_clone;
            let tmp_4 = Clone::clone(&__anf_capture_49);
            let tmp_5 = Clone::clone(&__anf_capture_51);
            let tmp_6 = Clone::clone(&tmp_3);
            relaxF(tbl, tmp_4, tmp_5, tmp_6, v55, v56)
          }
        });
        amap_1(callback, d, int63!(0), n)
      } else {
        d
      };
      lscan(tbl, n, L, tmp_2, j + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(tbl);
      d
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.layers
// Variant: uncurried
pub fn layers_1(tbl: Array<Int63>, n: Int63, L: Int63, d: Array<Int63>) -> Array<Int63> {
  layers(tbl, n, L, d, ())
}

// Rocq: Mazemovement.mazemovement_implem.layers (local: layers)
// Variant: uncurried, lifted
pub fn layers(tbl: Array<Int63>, n: Int63, L: Int63, d: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = L < n;
  match bdec(tmp) {
    sumbool::left => {
      let d_clone = Clone::clone(&d);
      if has_val_1(d_clone, n, L, int63!(0)) {
        let tmp_1 = L + int63!(1);
        let tbl_clone = Clone::clone(&tbl);
        let tmp_2 = lscan_1(tbl_clone, n, L, d, int63!(0));
        layers(tbl, n, tmp_1, tmp_2, ())
      } else {
        std::mem::drop(tbl);
        d
      }
    },
    sumbool::right => {
      std::mem::drop(tbl);
      d
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.bfs
// Variant: uncurried
pub fn bfs(tbl: Array<Int63>, n: Int63, t: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, n);
  layers_1(tbl, n, int63!(0), tmp.set(t, int63!(0)))
}

// Rocq: Mazemovement.mazemovement_implem.maxF
// Variant: borrowed, uncurried
pub fn maxF(d: &Array<Int63>, y: Int63, o: Int63) -> Int63 {
  let y_1 = y;
  let o_1 = o;
  let tmp = d.get_cloned(y_1);
  if o_1 < tmp {
    d.get_cloned(y_1)
  } else {
    o_1
  }
}

// Rocq: Mazemovement.mazemovement_implem.glob
// Variant: uncurried
pub fn glob(tbl: Array<Int63>, n: Int63, t: Int63, h: Array<Int63>) -> Array<Int63> {
  let d = bfs(tbl, n, t);
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    move |v18: Int63, v19: Int63| -> Int63 {
      maxF(&d, v18, v19)
    }
  });
  amap_1(callback, h, int63!(0), n)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Mazemovement.mazemovement_implem.cntl
// Variant: uncurried
pub fn cntl_1(h: Array<Int63>, cnt: Array<Int63>, n: Int63, i: Int63) -> Array<Int63> {
  cntl(h, cnt, n, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.cntl (local: cntl)
// Variant: uncurried, lifted
pub fn cntl(h: Array<Int63>, cnt: Array<Int63>, n: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let k = h.get_cloned(i);
      let tmp_1 = cnt.get_cloned(k);
      cntl(h, cnt.set(k, tmp_1 + int63!(1)), n, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      cnt
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.count
// Variant: uncurried
pub fn count(h: Array<Int63>, n: Int63) -> Array<Int63> {
  cntl_1(h, Array::<Int63>::make(n + int63!(1), int63!(0)), n, int63!(0))
}

// Rocq: Mazemovement.mazemovement_implem.init_state
pub fn init_state(x: Array<Int63>) -> Rc<st> {
  let x_clone = Clone::clone(&x);
  let n = nn(x_clone);
  let x_clone_1 = Clone::clone(&x);
  let s = ss(x_clone_1);
  let x_clone_2 = Clone::clone(&x);
  let t = tt(x_clone_2);
  let tmp = n * n;
  let tbl0 = fill_tab_1(x, n, Array::<Int63>::make(tmp, int63!(0)), int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let p = sat_1(n, s, t, tbl0, tmp_1, tmp_2, int63!(0), int63!(0));
  let h0 = Array::<Int63>::make(n, int63!(0)).set(s, n);
  let p_clone = Clone::clone(&p);
  let h1 = glob(fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Array<Int63>>(fst::<((Array<Int63>, Array<Int63>), Array<Int63>), Int63>(p_clone))), n, t, h0);
  let p_clone_1 = Clone::clone(&p);
  let tmp_3 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Array<Int63>>(fst::<((Array<Int63>, Array<Int63>), Array<Int63>), Int63>(p_clone_1)));
  let p_clone_2 = Clone::clone(&p);
  let tmp_4 = snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Array<Int63>>(fst::<((Array<Int63>, Array<Int63>), Array<Int63>), Int63>(p_clone_2)));
  let tmp_5 = Array::<Int63>::make(n, int63!(0));
  let h1_clone = Clone::clone(&h1);
  let tmp_6 = count(h1_clone, n);
  let p_clone_3 = Clone::clone(&p);
  Rc::new(st { s_tbl: tmp_3, s_ex: tmp_4, s_h: h1, s_cur: tmp_5, s_cnt: tmp_6, s_q: snd::<(Array<Int63>, Array<Int63>), Array<Int63>>(fst::<((Array<Int63>, Array<Int63>), Array<Int63>), Int63>(p_clone_3)), s_qh: int63!(0), s_ql: snd::<((Array<Int63>, Array<Int63>), Array<Int63>), Int63>(p), s_cu: n, s_rl: int63!(0) })
}

// Rocq: Mazemovement.mazemovement_implem.adm
// Variant: uncurried
pub fn adm(tbl: Array<Int63>, h: Array<Int63>, n: Int63, u: Int63, v: Int63) -> bool {
  let tmp = int63!(0);
  let tmp_1 = tbl.get_cloned(u * n + v);
  std::mem::drop(tbl);
  let tmp_2 = tmp < tmp_1;
  let tmp_3 = h.get_cloned(u);
  let tmp_4 = h.get_cloned(v);
  std::mem::drop(h);
  andb(tmp_2, tmp_3 == tmp_4 + int63!(1))
}

// Rocq: Mazemovement.mazemovement_implem.enq_pos
// Variant: uncurried
pub fn enq_pos(qh: Int63, ql: Int63, n: Int63) -> Int63 {
  let p = qh + ql;
  if p < n {
    p
  } else {
    p - n
  }
}

// Rocq: Mazemovement.mazemovement_implem.rmin
// Variant: uncurried
pub fn rmin_1(tbl: Array<Int63>, n: Int63, u: Int63, h: Array<Int63>, b_1: Int63, acc: Int63) -> Int63 {
  rmin(tbl, n, u, h, b_1, acc, ())
}

// Rocq: Mazemovement.mazemovement_implem.rmin (local: rmin)
// Variant: uncurried, lifted
pub fn rmin(tbl: Array<Int63>, n: Int63, u: Int63, h: Array<Int63>, b_1: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = b_1 < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = b_1 + int63!(1);
      let tmp_2 = tbl.get_cloned(u * n + b_1);
      let tmp_3 = int63!(0) < tmp_2;
      let tmp_4 = h.get_cloned(b_1);
      let tmp_5 = tmp_4 + int63!(1) < acc;
      let tmp_6 = if andb(tmp_3, tmp_5) {
        let tmp_7 = h.get_cloned(b_1);
        tmp_7 + int63!(1)
      } else {
        acc
      };
      rmin(tbl, n, u, h, tmp_1, tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(tbl);
      std::mem::drop(h);
      acc
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.no_height
// Variant: uncurried
pub fn no_height_1(h: Array<Int63>, n: Int63, k: Int63, i: Int63) -> bool {
  no_height(h, n, k, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.no_height (local: no_height)
// Variant: uncurried, lifted
pub fn no_height(h: Array<Int63>, n: Int63, k: Int63, i: Int63, _H: ()) -> bool {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = h.get_cloned(i);
      if tmp_1 == k {
        std::mem::drop(h);
        false
      } else {
        no_height(h, n, k, i + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(h);
      true
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.cnt_lift
// Variant: uncurried
pub fn cnt_lift_1(h: Array<Int63>, cnt: Array<Int63>, n: Int63, k: Int63, i: Int63) -> Array<Int63> {
  cnt_lift(h, cnt, n, k, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.cnt_lift (local: cnt_lift)
// Variant: uncurried, lifted
pub fn cnt_lift(h: Array<Int63>, cnt: Array<Int63>, n: Int63, k: Int63, i: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let o = h.get_cloned(i);
      let tmp_1 = k < o;
      let tmp_2 = o < n;
      let tmp_3 = if andb(tmp_1, tmp_2) {
        let tmp_4 = cnt.get_cloned(o);
        cnt.set(o, tmp_4 - int63!(1))
      } else {
        cnt
      };
      cnt_lift(h, tmp_3, n, k, i + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      cnt
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.liftF
// Variant: uncurried
pub fn liftF(n: Int63, k: Int63, _y: Int63, o: Int63) -> Int63 {
  let tmp = k < o;
  let tmp_1 = o < n;
  if andb(tmp, tmp_1) {
    n
  } else {
    o
  }
}

// Rocq: Mazemovement.mazemovement_implem.lift
// Variant: uncurried
pub fn lift(h: Array<Int63>, n: Int63, k: Int63) -> Array<Int63> {
  let callback: Rc<dyn Fn(Int63, Int63) -> Int63> = Rc::new({
    let __anf_capture_9 = n;
    move |v13: Int63, v14: Int63| -> Int63 {
      let tmp = Clone::clone(&__anf_capture_9);
      let k_clone = Clone::clone(&k);
      liftF(tmp, k_clone, v13, v14)
    }
  });
  amap_1(callback, h, int63!(0), n)
}

// Rocq: Mazemovement.mazemovement_implem.active
// Variant: uncurried
pub fn active(ex: Array<Int63>, h: Array<Int63>, n: Int63, s: Int63, t: Int63, v: Int63) -> bool {
  let tmp = int63!(0);
  let tmp_1 = ex.get_cloned(v);
  std::mem::drop(ex);
  let tmp_2 = tmp < tmp_1;
  let tmp_3 = h.get_cloned(v);
  std::mem::drop(h);
  let tmp_4 = andb(tmp_2, tmp_3 < n);
  let tmp_5 = andb(tmp_4, negb(v == s));
  andb(tmp_5, negb(v == t))
}

// Rocq: Mazemovement.mazemovement_implem.find_act
// Variant: uncurried
pub fn find_act_1(ex: Array<Int63>, h: Array<Int63>, n: Int63, s: Int63, t: Int63, i: Int63) -> Int63 {
  find_act(ex, h, n, s, t, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.find_act (local: find_act)
// Variant: uncurried, lifted
pub fn find_act(ex: Array<Int63>, h: Array<Int63>, n: Int63, s: Int63, t: Int63, i: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let ex_clone = Clone::clone(&ex);
      let h_clone = Clone::clone(&h);
      if active(ex_clone, h_clone, n, s, t, i) {
        std::mem::drop(ex);
        std::mem::drop(h);
        i
      } else {
        find_act(ex, h, n, s, t, i + int63!(1), ())
      }
    },
    sumbool::right => {
      std::mem::drop(ex);
      std::mem::drop(h);
      n
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.mloop
// Variant: uncurried
pub fn mloop_1(n: Int63, s: Int63, t: Int63, tbl: Array<Int63>, ex: Array<Int63>, h: Array<Int63>, cur: Array<Int63>, cnt: Array<Int63>, q: Array<Int63>, qh: Int63, ql: Int63, cu: Int63, rl: Int63) -> Int63 {
  mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh, ql, cu, rl, ())
}

// Rocq: Mazemovement.mazemovement_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(n: Int63, s: Int63, t: Int63, tbl: Array<Int63>, ex: Array<Int63>, h: Array<Int63>, cur: Array<Int63>, cnt: Array<Int63>, q: Array<Int63>, qh: Int63, ql: Int63, cu: Int63, rl: Int63, _H: ()) -> Int63 {
  let tmp = cu < n;
  match bdec(tmp) {
    sumbool::left => {
      let v = cur.get_cloned(cu);
      let tmp_1 = v < n;
      match bdec(tmp_1) {
        sumbool::left => {
          let tbl_clone = Clone::clone(&tbl);
          let h_clone = Clone::clone(&h);
          let tmp_2 = adm(tbl_clone, h_clone, n, cu, v);
          match bdec(tmp_2) {
            sumbool::left => {
              let r = tbl.get_cloned(cu * n + v);
              let e = ex.get_cloned(cu);
              let d = if e < r {
                e
              } else {
                r
              };
              let tbl1 = tbl.set(cu * n + v, r - d);
              let tmp_3 = v * n + cu;
              let tmp_4 = tbl1.get_cloned(v * n + cu);
              let tbl2 = tbl1.set(tmp_3, tmp_4 + d);
              let ev = ex.get_cloned(v);
              let ex1 = ex.set(cu, e - d);
              let ex2 = ex1.set(v, ev + d);
              let tmp_5 = andb(ev == int63!(0), negb(v == t));
              let tmp_6 = andb(tmp_5, negb(v == s));
              let b_1 = andb(tmp_6, ql < n);
              let q1 = if b_1 {
                q.set(enq_pos(qh, ql, n), v)
              } else {
                q
              };
              let ql1 = if b_1 {
                ql + int63!(1)
              } else {
                ql
              };
              let tmp_7 = e - d;
              let tmp_8 = int63!(0);
              let cu1 = if tmp_7 == tmp_8 {
                n
              } else {
                cu
              };
              mloop(n, s, t, tbl2, ex2, h, cur, cnt, q1, qh, ql1, cu1, rl, ())
            },
            sumbool::right => {
              mloop(n, s, t, tbl, ex, h, cur.set(cu, v + int63!(1)), cnt, q, qh, ql, cu, rl, ())
            },
          }
        },
        sumbool::right => {
          let oh = h.get_cloned(cu);
          let tbl_clone_1 = Clone::clone(&tbl);
          let h_clone_1 = Clone::clone(&h);
          let nh = rmin_1(tbl_clone_1, n, cu, h_clone_1, int63!(0), n);
          let h1 = h.set(cu, nh);
          let cur1 = cur.set(cu, int63!(0));
          let tmp_9 = cnt.get_cloned(oh);
          let co = tmp_9 - int63!(1);
          let cnt1 = cnt.set(oh, co);
          let tmp_10 = cnt1.get_cloned(nh);
          let cnt2 = cnt1.set(nh, tmp_10 + int63!(1));
          let tmp_11 = andb(co == int63!(0), int63!(0) < oh);
          let tmp_12 = andb(tmp_11, oh < n);
          let h1_clone = Clone::clone(&h1);
          let g = andb(tmp_12, no_height_1(h1_clone, n, oh, int63!(0)));
          let cnt3 = if g {
            let h1_clone_1 = Clone::clone(&h1);
            cnt_lift_1(h1_clone_1, cnt2, n, oh, int63!(0))
          } else {
            cnt2
          };
          let h2 = if g {
            lift(h1, n, oh)
          } else {
            h1
          };
          let rl1 = rl + int63!(1);
          let gl = n <= rl1;
          let h3 = if gl {
            let tbl_clone_2 = Clone::clone(&tbl);
            glob(tbl_clone_2, n, t, h2)
          } else {
            h2
          };
          let cur2 = if gl {
            std::mem::drop(cur1);
            Array::<Int63>::make(n, int63!(0))
          } else {
            cur1
          };
          let cnt4 = if gl {
            std::mem::drop(cnt3);
            let h3_clone = Clone::clone(&h3);
            count(h3_clone, n)
          } else {
            cnt3
          };
          let rl2 = if gl {
            int63!(0)
          } else {
            rl1
          };
          let tmp_13 = h3.get_cloned(cu);
          let cu1 = if tmp_13 < n {
            cu
          } else {
            n
          };
          mloop(n, s, t, tbl, ex, h3, cur2, cnt4, q, qh, ql, cu1, rl2, ())
        },
      }
    },
    sumbool::right => {
      let tmp_14 = int63!(0) < ql;
      match bdec(tmp_14) {
        sumbool::left => {
          let v = q.get_cloned(qh);
          let tmp_15 = qh + int63!(1);
          let qh1 = if tmp_15 == n {
            int63!(0)
          } else {
            qh + int63!(1)
          };
          let tmp_16 = v < n;
          let ex_clone = Clone::clone(&ex);
          let h_clone_2 = Clone::clone(&h);
          let tmp_17 = active(ex_clone, h_clone_2, n, s, t, v);
          let cu1 = if andb(tmp_16, tmp_17) {
            v
          } else {
            n
          };
          mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh1, ql - int63!(1), cu1, rl, ())
        },
        sumbool::right => {
          let ex_clone_1 = Clone::clone(&ex);
          let h_clone_3 = Clone::clone(&h);
          let v = find_act_1(ex_clone_1, h_clone_3, n, s, t, int63!(0));
          let tmp_18 = v < n;
          match bdec(tmp_18) {
            sumbool::left => {
              mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh, ql, v, rl, ())
            },
            sumbool::right => {
              std::mem::drop(tbl);
              std::mem::drop(h);
              std::mem::drop(cur);
              std::mem::drop(cnt);
              std::mem::drop(q);
              let tmp_19 = ex.get_cloned(t);
              std::mem::drop(ex);
              tmp_19
            },
          }
        },
      }
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.s_tbl
pub fn s_tbl(s: Rc<st>) -> Array<Int63> {
  let s_s_tbl_clone = Clone::clone(&s.s_tbl);
  std::mem::drop(s);
  s_s_tbl_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_ex
pub fn s_ex(s: Rc<st>) -> Array<Int63> {
  let s_s_ex_clone = Clone::clone(&s.s_ex);
  std::mem::drop(s);
  s_s_ex_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_h
pub fn s_h(s: Rc<st>) -> Array<Int63> {
  let s_s_h_clone = Clone::clone(&s.s_h);
  std::mem::drop(s);
  s_s_h_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_cur
pub fn s_cur(s: Rc<st>) -> Array<Int63> {
  let s_s_cur_clone = Clone::clone(&s.s_cur);
  std::mem::drop(s);
  s_s_cur_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_cnt
pub fn s_cnt(s: Rc<st>) -> Array<Int63> {
  let s_s_cnt_clone = Clone::clone(&s.s_cnt);
  std::mem::drop(s);
  s_s_cnt_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_q
pub fn s_q(s: Rc<st>) -> Array<Int63> {
  let s_s_q_clone = Clone::clone(&s.s_q);
  std::mem::drop(s);
  s_s_q_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_qh
// Variant: borrowed
pub fn s_qh(s: &Rc<st>) -> Int63 {
  let tmp = s;
  Clone::clone(&tmp.s_qh)
}

// Rocq: Mazemovement.mazemovement_implem.s_ql
// Variant: borrowed
pub fn s_ql(s: &Rc<st>) -> Int63 {
  let tmp = s;
  Clone::clone(&tmp.s_ql)
}

// Rocq: Mazemovement.mazemovement_implem.s_cu
// Variant: borrowed
pub fn s_cu(s: &Rc<st>) -> Int63 {
  let tmp = s;
  Clone::clone(&tmp.s_cu)
}

// Rocq: Mazemovement.mazemovement_implem.s_rl
pub fn s_rl(s: Rc<st>) -> Int63 {
  let s_s_rl_clone = Clone::clone(&s.s_rl);
  std::mem::drop(s);
  s_s_rl_clone
}

// Rocq: Mazemovement.mazemovement_implem.mazemovement_impl
pub fn mazemovement_impl(x: Array<Int63>) -> Int63 {
  let x_clone = Clone::clone(&x);
  let tmp = guard(x_clone);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone_1 = Clone::clone(&x);
      let S = init_state(x_clone_1);
      let x_clone_2 = Clone::clone(&x);
      let tmp_1 = nn(x_clone_2);
      let x_clone_3 = Clone::clone(&x);
      let tmp_2 = ss(x_clone_3);
      let tmp_3 = tt(x);
      let S_clone = Rc::clone(&S);
      let tmp_4 = s_tbl(S_clone);
      let S_clone_1 = Rc::clone(&S);
      let tmp_5 = s_ex(S_clone_1);
      let S_clone_2 = Rc::clone(&S);
      let tmp_6 = s_h(S_clone_2);
      let S_clone_3 = Rc::clone(&S);
      let tmp_7 = s_cur(S_clone_3);
      let S_clone_4 = Rc::clone(&S);
      let tmp_8 = s_cnt(S_clone_4);
      let S_clone_5 = Rc::clone(&S);
      let tmp_9 = s_q(S_clone_5);
      let tmp_10 = s_qh(&S);
      let tmp_11 = s_ql(&S);
      let tmp_12 = s_cu(&S);
      mloop_1(tmp_1, tmp_2, tmp_3, tmp_4, tmp_5, tmp_6, tmp_7, tmp_8, tmp_9, tmp_10, tmp_11, tmp_12, s_rl(S))
    },
    sumbool::right => {
      std::mem::drop(x);
      int63!(0)
    },
  }
}
