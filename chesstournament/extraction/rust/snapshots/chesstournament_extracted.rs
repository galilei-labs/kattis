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

// Rocq: Chesstournament.chesstournament_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Chesstournament.chesstournament_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(n: Int63, x: Int63, p: Array<Int63>) -> Array<Int63> {
  iota_loop(n, x, p, ())
}

// Rocq: Chesstournament.chesstournament_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(n: Int63, x: Int63, p: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = x < n;
  match bdec(tmp) {
    sumbool::left => {
      iota_loop(n, x + int63!(1), p.set(x, x), ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.iota
pub fn iota(n: Int63) -> Array<Int63> {
  let tmp = Array::<Int63>::make(n, int63!(0));
  iota_loop_1(n, int63!(0), tmp)
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

// Rocq: Chesstournament.chesstournament_implem.find
// Variant: uncurried
pub fn find_1(p: Array<Int63>, x: Int63) -> (Array<Int63>, Int63) {
  find(p, x, ())
}

// Rocq: Chesstournament.chesstournament_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(p: Array<Int63>, x: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let y = p.get_cloned(x);
  let tmp = y == x;
  match bdec(tmp) {
    sumbool::left => {
      (p, x)
    },
    sumbool::right => {
      let f = find(p, y, ());
      let f_clone = Clone::clone(&f);
      let tmp_1 = fst::<Array<Int63>, Int63>(f_clone);
      let f_clone_1 = Clone::clone(&f);
      (tmp_1.set(x, snd::<Array<Int63>, Int63>(f_clone_1)), snd::<Array<Int63>, Int63>(f))
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.union
// Variant: uncurried
pub fn union(p: Array<Int63>, rk: Array<Int63>, a_1: Int63, b_1: Int63) -> (Array<Int63>, Array<Int63>) {
  if a_1 == b_1 {
    (p, rk)
  } else {
    let ra = rk.get_cloned(a_1);
    let rb = rk.get_cloned(b_1);
    if ra < rb {
      (p.set(a_1, b_1), rk)
    } else {
      if rb < ra {
        (p.set(b_1, a_1), rk)
      } else {
        (p.set(b_1, a_1), rk.set(a_1, ra + int63!(1)))
      }
    }
  }
}

// Rocq: Chesstournament.chesstournament_implem.unite
// Variant: uncurried
pub fn unite(p: Array<Int63>, rk: Array<Int63>, k: Int63, l: Int63) -> (Array<Int63>, Array<Int63>) {
  let f1 = find_1(p, k);
  let f1_clone = Clone::clone(&f1);
  let f2 = find_1(fst::<Array<Int63>, Int63>(f1_clone), l);
  let f2_clone = Clone::clone(&f2);
  union(fst::<Array<Int63>, Int63>(f2_clone), rk, snd::<Array<Int63>, Int63>(f1), snd::<Array<Int63>, Int63>(f2))
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop
// Variant: uncurried
pub fn uf_loop_1(ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, p: Array<Int63>, rk: Array<Int63>) -> Array<Int63> {
  uf_loop(ks, wins, ls, m, j, p, rk, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop (local: uf_loop)
// Variant: uncurried, lifted
pub fn uf_loop(ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, p: Array<Int63>, rk: Array<Int63>, _Hp: (), _H: ()) -> Array<Int63> {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = wins.get_cloned(j);
      if tmp_1 {
        uf_loop(ks, wins, ls, m, j + int63!(1), p, rk, (), ())
      } else {
        let tmp_2 = ks.get_cloned(j);
        let tmp_3 = ls.get_cloned(j);
        let u = unite(p, rk, tmp_2, tmp_3);
        let tmp_4 = j + int63!(1);
        let u_clone = Clone::clone(&u);
        uf_loop(ks, wins, ls, m, tmp_4, fst::<Array<Int63>, Array<Int63>>(u_clone), snd::<Array<Int63>, Array<Int63>>(u), (), ())
      }
    },
    sumbool::right => {
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(rk);
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop
// Variant: uncurried
pub fn rep_loop_1(n: Int63, x: Int63, p: Array<Int63>, rep: Array<Int63>) -> Array<Int63> {
  rep_loop(n, x, p, rep, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop (local: rep_loop)
// Variant: uncurried, lifted
pub fn rep_loop(n: Int63, x: Int63, p: Array<Int63>, rep: Array<Int63>, _Hp: (), _H: ()) -> Array<Int63> {
  let tmp = x < n;
  match bdec(tmp) {
    sumbool::left => {
      let f = find_1(p, x);
      let tmp_1 = x + int63!(1);
      let f_clone = Clone::clone(&f);
      rep_loop(n, tmp_1, fst::<Array<Int63>, Int63>(f_clone), rep.set(x, snd::<Array<Int63>, Int63>(f)), (), ())
    },
    sumbool::right => {
      std::mem::drop(p);
      rep
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(rep: Array<Int63>, ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, od: Array<Int63>, id: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  deg_loop(rep, ks, wins, ls, m, j, od, id, ())
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(rep: Array<Int63>, ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, od: Array<Int63>, id: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = wins.get_cloned(j);
      if tmp_1 {
        let tmp_2 = ks.get_cloned(j);
        let a_1 = rep.get_cloned(tmp_2);
        let tmp_3 = ls.get_cloned(j);
        let b_1 = rep.get_cloned(tmp_3);
        let tmp_4 = j + int63!(1);
        let tmp_5 = od.get_cloned(a_1);
        let tmp_6 = od.set(a_1, tmp_5 + int63!(1));
        let tmp_7 = id.get_cloned(b_1);
        deg_loop(rep, ks, wins, ls, m, tmp_4, tmp_6, id.set(b_1, tmp_7 + int63!(1)), ())
      } else {
        deg_loop(rep, ks, wins, ls, m, j + int63!(1), od, id, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      (od, id)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(od: Array<Int63>, n: Int63, u: Int63, s: Int63, st: Array<Int63>, pos: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  pre_loop(od, n, u, s, st, pos, ())
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(od: Array<Int63>, n: Int63, u: Int63, s: Int63, st: Array<Int63>, pos: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = u < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = od.get_cloned(u);
      let s_ = s + tmp_1;
      let tmp_2 = u + int63!(1);
      let tmp_3 = st.set(u + int63!(1), s_);
      pre_loop(od, n, tmp_2, s_, tmp_3, pos.set(u, s), ())
    },
    sumbool::right => {
      std::mem::drop(od);
      (st, pos)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(rep: Array<Int63>, ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, pos: Array<Int63>, adj: Array<Int63>) -> Array<Int63> {
  fill_loop(rep, ks, wins, ls, m, j, pos, adj, ())
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(rep: Array<Int63>, ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>, m: Int63, j: Int63, pos: Array<Int63>, adj: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = j < m;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = wins.get_cloned(j);
      if tmp_1 {
        let tmp_2 = ks.get_cloned(j);
        let a_1 = rep.get_cloned(tmp_2);
        let pa = pos.get_cloned(a_1);
        let tmp_3 = j + int63!(1);
        let tmp_4 = pos.set(a_1, pa + int63!(1));
        let tmp_5 = ls.get_cloned(j);
        let tmp_6 = rep.get_cloned(tmp_5);
        fill_loop(rep, ks, wins, ls, m, tmp_3, tmp_4, adj.set(pa, tmp_6), ())
      } else {
        fill_loop(rep, ks, wins, ls, m, j + int63!(1), pos, adj, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(pos);
      adj
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(id: Array<Int63>, n: Int63, v: Int63, q: Array<Int63>, t: Int63) -> (Array<Int63>, Int63) {
  init_loop(id, n, v, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(id: Array<Int63>, n: Int63, v: Int63, q: Array<Int63>, t: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = v < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = id.get_cloned(v);
      if tmp_1 == int63!(0) {
        init_loop(id, n, v + int63!(1), q.set(t, v), t + int63!(1), ())
      } else {
        init_loop(id, n, v + int63!(1), q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(id);
      (q, t)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.inner
// Variant: uncurried
pub fn inner_1(adj: Array<Int63>, hi: Int63, e: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63) -> ((Array<Int63>, Array<Int63>), Int63) {
  inner(adj, hi, e, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(adj: Array<Int63>, hi: Int63, e: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63, _H: ()) -> ((Array<Int63>, Array<Int63>), Int63) {
  let tmp = e < hi;
  match bdec(tmp) {
    sumbool::left => {
      let v = adj.get_cloned(e);
      let tmp_1 = d.get_cloned(v);
      let dv = tmp_1 - int63!(1);
      if dv == int63!(0) {
        inner(adj, hi, e + int63!(1), d.set(v, dv), q.set(t, v), t + int63!(1), ())
      } else {
        inner(adj, hi, e + int63!(1), d.set(v, dv), q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(adj);
      ((d, q), t)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.kahn
// Variant: uncurried
pub fn kahn_1(adj: Array<Int63>, st: Array<Int63>, h: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63) -> Int63 {
  kahn(adj, st, h, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.kahn (local: kahn)
// Variant: uncurried, lifted
pub fn kahn(adj: Array<Int63>, st: Array<Int63>, h: Int63, d: Array<Int63>, q: Array<Int63>, t: Int63, _H: ()) -> Int63 {
  let tmp = h < t;
  match bdec(tmp) {
    sumbool::left => {
      let u = q.get_cloned(h);
      let tmp_1 = st.get_cloned(u + int63!(1));
      let tmp_2 = st.get_cloned(u);
      let adj_clone = Clone::clone(&adj);
      let r = inner_1(adj_clone, tmp_1, tmp_2, d, q, t);
      let tmp_3 = h + int63!(1);
      let r_clone = Clone::clone(&r);
      let tmp_4 = fst::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      kahn(adj, st, tmp_3, tmp_4, snd::<Array<Int63>, Array<Int63>>(fst::<(Array<Int63>, Array<Int63>), Int63>(r_clone_1)), snd::<(Array<Int63>, Array<Int63>), Int63>(r), ())
    },
    sumbool::right => {
      std::mem::drop(adj);
      std::mem::drop(st);
      std::mem::drop(d);
      std::mem::drop(q);
      t
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.chess_impl
// Variant: uncurried
pub fn chess_impl(n: Int63, ks: Array<Int63>, wins: Array<bool>, ls: Array<Int63>) -> bool {
  let m = ks.length();
  let p0 = iota(n);
  let tmp = Array::<Int63>::make(n, int63!(0));
  let ks_clone = Clone::clone(&ks);
  let wins_clone = Clone::clone(&wins);
  let ls_clone = Clone::clone(&ls);
  let p1 = uf_loop_1(ks_clone, wins_clone, ls_clone, m, int63!(0), p0, tmp);
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let rep = rep_loop_1(n, int63!(0), p1, tmp_1);
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  let tmp_3 = Array::<Int63>::make(n, int63!(0));
  let rep_clone = Clone::clone(&rep);
  let ks_clone_1 = Clone::clone(&ks);
  let wins_clone_1 = Clone::clone(&wins);
  let ls_clone_1 = Clone::clone(&ls);
  let dg = deg_loop_1(rep_clone, ks_clone_1, wins_clone_1, ls_clone_1, m, int63!(0), tmp_2, tmp_3);
  let dg_clone = Clone::clone(&dg);
  let tmp_4 = fst::<Array<Int63>, Array<Int63>>(dg_clone);
  let tmp_5 = Array::<Int63>::make(n + int63!(1), int63!(0));
  let tmp_6 = Array::<Int63>::make(n, int63!(0));
  let sp = pre_loop_1(tmp_4, n, int63!(0), int63!(0), tmp_5, tmp_6);
  let sp_clone = Clone::clone(&sp);
  let tmp_7 = snd::<Array<Int63>, Array<Int63>>(sp_clone);
  let tmp_8 = Array::<Int63>::make(m, int63!(0));
  let adj = fill_loop_1(rep, ks, wins, ls, m, int63!(0), tmp_7, tmp_8);
  let dg_clone_1 = Clone::clone(&dg);
  let tmp_9 = snd::<Array<Int63>, Array<Int63>>(dg_clone_1);
  let tmp_10 = Array::<Int63>::make(n, int63!(0));
  let qi = init_loop_1(tmp_9, n, int63!(0), tmp_10, int63!(0));
  let tmp_11 = fst::<Array<Int63>, Array<Int63>>(sp);
  let tmp_12 = snd::<Array<Int63>, Array<Int63>>(dg);
  let qi_clone = Clone::clone(&qi);
  let t = kahn_1(adj, tmp_11, int63!(0), tmp_12, fst::<Array<Int63>, Int63>(qi_clone), snd::<Array<Int63>, Int63>(qi));
  t == n
}
