// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct bst {
  pub vis: Rc<Array<bool>>,
  pub dst: Rc<Array<u64>>,
  pub par: Rc<Array<u64>>,
  pub pe: Rc<Array<u64>>,
  pub ord: Rc<Array<u64>>,
  pub tl: u64,
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

pub type uint = u64;

// Rocq: Joggers.joggers_implem.joggers
// Variant: uncurried
pub fn joggers() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = joggers_impl;
  let v1: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Joggers.joggers_implem.joggers
pub fn joggers_curried() -> Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>> {
  let v0: fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>> = joggers_impl_curried;
  let v1: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Joggers.joggers_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
  }
}

// Rocq: Joggers.joggers_implem.lamp_loop
// Variant: uncurried
pub fn lamp_loop_1(xl: Rc<Array<u64>>, L: u64, i: u64, inl: Rc<Array<bool>>) -> Rc<Array<bool>> {
  lamp_loop(xl, L, i, inl, ())
}

// Rocq: Joggers.joggers_implem.lamp_loop (local: lamp_loop)
// Variant: uncurried, lifted
pub fn lamp_loop(xl: Rc<Array<u64>>, L: u64, i: u64, inl: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let v12 = ltb(i, L);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24 = &xl;
      let v27 = rocq_array::get::<u64>(&v24, i);
      let v36 = rocq_array::set::<bool>(inl, v27, true);
      lamp_loop(xl, L, v23, v36, ())
    },
    sumbool::right => {
      std::mem::drop(xl);
      inl
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Joggers.joggers_implem.ep
// Variant: uncurried
pub fn ep(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64) -> u64 {
  match ltb(k, m) {
    true => {
      std::mem::drop(xb);
      let v11 = &xa;
      let v14 = rocq_array::get::<u64>(&v11, k);
      std::mem::drop(xa);
      v14
    },
    false => {
      std::mem::drop(xa);
      let v22 = sub(k, m);
      let v23 = &xb;
      let v26 = rocq_array::get::<u64>(&v23, v22);
      std::mem::drop(xb);
      v26
    },
  }
}

// Rocq: Joggers.joggers_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(xa, xb, m, K, i, cnt, ())
}

// Rocq: Joggers.joggers_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v14 = ltb(i, K);
  match bdec(v14) {
    sumbool::left => {
      let v21 = Rc::clone(&xa);
      let v24 = Rc::clone(&xb);
      let w = ep(v21, v24, m, i);
      let v37 = add(i, 1u64);
      let v39 = &cnt;
      let v42 = rocq_array::get::<u64>(&v39, w);
      let v56 = rocq_array::set::<u64>(cnt, w, add(v42, 1u64));
      cnt_loop(xa, xb, m, K, v37, v56, ())
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
pub fn off_loop_1(cnt: Rc<Array<u64>>, V: u64, v: u64, off: Rc<Array<u64>>, cur: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  off_loop(cnt, V, v, off, cur, ())
}

// Rocq: Joggers.joggers_implem.off_loop (local: off_loop)
// Variant: uncurried, lifted
pub fn off_loop(cnt: Rc<Array<u64>>, V: u64, v: u64, off: Rc<Array<u64>>, cur: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(v, V);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &off;
      let o = rocq_array::get::<u64>(&v17, v);
      let v28 = add(v, 1u64);
      let v36 = add(v, 1u64);
      let v38 = &cnt;
      let v41 = rocq_array::get::<u64>(&v38, v);
      let v53 = rocq_array::set::<u64>(off, v36, add(o, v41));
      let v60 = rocq_array::set::<u64>(cur, v, o);
      off_loop(cnt, V, v28, v53, v60, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      (off, cur)
    },
  }
}

// Rocq: Joggers.joggers_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cur: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(xa, xb, m, K, i, cur, adj, ())
}

// Rocq: Joggers.joggers_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cur: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(i, K);
  match bdec(v15) {
    sumbool::left => {
      let v22 = Rc::clone(&xa);
      let v25 = Rc::clone(&xb);
      let w = ep(v22, v25, m, i);
      let v31 = &cur;
      let c = rocq_array::get::<u64>(&v31, w);
      let v42 = add(i, 1u64);
      let v57 = rocq_array::set::<u64>(cur, w, add(c, 1u64));
      let v64 = rocq_array::set::<u64>(adj, c, i);
      fill_loop(xa, xb, m, K, v42, v57, v64, ())
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
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Joggers.joggers_implem.tl
pub fn tl_owned(b: Rc<bst>) -> u64 {
  let v3 = Clone::clone((&(&**&b).tl));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.tl
// Variant: borrowed
pub fn tl(b: &Rc<bst>) -> u64 {
  let v1 = b;
  Clone::clone((&(&**v1).tl))
}

// Rocq: Joggers.joggers_implem.ord
pub fn ord(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).ord));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.oth
// Variant: uncurried
pub fn oth(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64) -> u64 {
  match ltb(k, m) {
    true => {
      std::mem::drop(xa);
      let v11 = &xb;
      let v14 = rocq_array::get::<u64>(&v11, k);
      std::mem::drop(xb);
      v14
    },
    false => {
      std::mem::drop(xb);
      let v22 = sub(k, m);
      let v23 = &xa;
      let v26 = rocq_array::get::<u64>(&v23, v22);
      std::mem::drop(xa);
      v26
    },
  }
}

// Rocq: Joggers.joggers_implem.vis
pub fn vis(b: Rc<bst>) -> Rc<Array<bool>> {
  let v3 = Rc::clone((&(&**&b).vis));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.eid
// Variant: uncurried
pub fn eid(m: u64, k: u64) -> u64 {
  match ltb(k, m) {
    true => {
      k
    },
    false => {
      sub(k, m)
    },
  }
}

// Rocq: Joggers.joggers_implem.dst
pub fn dst(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).dst));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.par
pub fn par(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).par));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.pe
pub fn pe(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).pe));
  std::mem::drop(b);
  v3
}

// Rocq: Joggers.joggers_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, u: u64, du: u64, hi: u64, i: u64, st: Rc<bst>) -> Rc<bst> {
  scan_loop(xa, xb, xd, m, adj, u, du, hi, i, st, ())
}

// Rocq: Joggers.joggers_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, u: u64, du: u64, hi: u64, i: u64, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let v18 = ltb(i, hi);
  match bdec(v18) {
    sumbool::left => {
      let v22 = &adj;
      let k = rocq_array::get::<u64>(&v22, i);
      let v29 = Rc::clone(&xa);
      let v32 = Rc::clone(&xb);
      let w = oth(v29, v32, m, k);
      let v41 = Rc::clone(&st);
      let v42 = vis(v41);
      let v43 = &v42;
      let v46 = rocq_array::get::<bool>(&v43, w);
      let st_ = match v46 {
        true => {
          std::mem::drop(v42);
          st
        },
        false => {
          std::mem::drop(v42);
          let e = eid(m, k);
          let v59 = Rc::clone(&st);
          let v60 = vis(v59);
          let v69 = rocq_array::set::<bool>(v60, w, true);
          let v73 = Rc::clone(&st);
          let v74 = dst(v73);
          let v76 = &xd;
          let v79 = rocq_array::get::<u64>(&v76, e);
          let v91 = rocq_array::set::<u64>(v74, w, add(du, v79));
          let v95 = Rc::clone(&st);
          let v97 = par(v95);
          let v103 = rocq_array::set::<u64>(v97, w, u);
          let v107 = Rc::clone(&st);
          let v109 = pe(v107);
          let v115 = rocq_array::set::<u64>(v109, w, e);
          let v119 = Rc::clone(&st);
          let v120 = ord(v119);
          let v124 = tl(&st);
          let v131 = rocq_array::set::<u64>(v120, v124, w);
          Rc::new(bst { vis: v69, dst: v91, par: v103, pe: v115, ord: v131, tl: add(tl_owned(st), 1u64) })
        },
      };
      scan_loop(xa, xb, xd, m, adj, u, du, hi, add(i, 1u64), st_, ())
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
pub fn bfs_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, off: Rc<Array<u64>>, h: u64, st: Rc<bst>) -> Rc<bst> {
  bfs_loop(xa, xb, xd, m, adj, off, h, st, ())
}

// Rocq: Joggers.joggers_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, off: Rc<Array<u64>>, h: u64, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let v20 = ltb(h, tl(&st));
  match bdec(v20) {
    sumbool::left => {
      let v27 = Rc::clone(&st);
      let v28 = ord(v27);
      let v29 = &v28;
      let u = rocq_array::get::<u64>(&v29, h);
      std::mem::drop(v28);
      let v37 = Rc::clone(&st);
      let v38 = dst(v37);
      let v39 = &v38;
      let v42 = rocq_array::get::<u64>(&v39, u);
      std::mem::drop(v38);
      let v50 = add(u, 1u64);
      let v51 = &off;
      let v54 = rocq_array::get::<u64>(&v51, v50);
      let v55 = &off;
      let v58 = rocq_array::get::<u64>(&v55, u);
      let v61 = Rc::clone(&xa);
      let v64 = Rc::clone(&xb);
      let v67 = Rc::clone(&xd);
      let v72 = Rc::clone(&adj);
      let st_ = scan_loop_1(v61, v64, v67, m, v72, u, v42, v54, v58, st);
      bfs_loop(xa, xb, xd, m, adj, off, add(h, 1u64), st_, ())
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
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      b2
    },
    false => {
      false
    },
  }
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  match b {
    true => {
      false
    },
    false => {
      true
    },
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
  }
}

// Rocq: Joggers.joggers_implem.sweep_loop
// Variant: uncurried
pub fn sweep_loop_1(s: u64, inl: Rc<Array<bool>>, ord_1: Rc<Array<u64>>, par_1: Rc<Array<u64>>, dst_1: Rc<Array<u64>>, i: u64, ch: Rc<Array<bool>>, c: u64) -> u64 {
  sweep_loop(s, inl, ord_1, par_1, dst_1, i, ch, c, ())
}

// Rocq: Joggers.joggers_implem.sweep_loop (local: sweep_loop)
// Variant: uncurried, lifted
pub fn sweep_loop(s: u64, inl: Rc<Array<bool>>, ord_1: Rc<Array<u64>>, par_1: Rc<Array<u64>>, dst_1: Rc<Array<u64>>, i: u64, ch: Rc<Array<bool>>, c: u64, _H: ()) -> u64 {
  let v18 = ltb(0u64, i);
  match bdec(v18) {
    sumbool::left => {
      let v22 = &ord_1;
      let v = rocq_array::get::<u64>(&v22, i);
      let v26 = &par_1;
      let p = rocq_array::get::<u64>(&v26, v);
      let v30 = &dst_1;
      let dp = rocq_array::get::<u64>(&v30, p);
      let v47 = ltb(add(dp, dp), s);
      let v50 = &inl;
      let v53 = rocq_array::get::<bool>(&v50, v);
      let v54 = &ch;
      let v57 = rocq_array::get::<bool>(&v54, v);
      let v70 = andb(v47, negb(orb(v53, v57)));
      let v73 = &inl;
      let v76 = rocq_array::get::<bool>(&v73, p);
      let v77 = &ch;
      let v80 = rocq_array::get::<bool>(&v77, p);
      let v88 = negb(orb(v76, v80));
      match andb(v70, v88) {
        true => {
          let v102 = sub(i, 1u64);
          let v111 = rocq_array::set::<bool>(ch, p, true);
          sweep_loop(s, inl, ord_1, par_1, dst_1, v102, v111, add(c, 1u64), ())
        },
        false => {
          sweep_loop(s, inl, ord_1, par_1, dst_1, sub(i, 1u64), ch, c, ())
        },
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
pub fn joggers_impl(n: u64, s: u64, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, xl: Rc<Array<u64>>) -> u64 {
  let v6 = &xa;
  let m = rocq_array::length::<u64>(&v6);
  let K = add(m, m);
  let V = add(n, 1u64);
  let v23 = &xl;
  let v24 = rocq_array::length::<u64>(&v23);
  let v33 = rocq_array::make::<bool>(V, false);
  let inl = lamp_loop_1(xl, v24, 0u64, v33);
  let v52 = rocq_array::make::<u64>(V, 0u64);
  let v55 = Rc::clone(&xa);
  let v58 = Rc::clone(&xb);
  let cnt = cnt_loop_1(v55, v58, m, K, 0u64, v52);
  let v85 = rocq_array::make::<u64>(add(V, 1u64), 0u64);
  let v92 = rocq_array::make::<u64>(V, 0u64);
  let oc = off_loop_1(cnt, V, 0u64, v85, v92);
  let v109 = Clone::clone(&oc);
  let v111 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v109);
  let v118 = rocq_array::make::<u64>(K, 0u64);
  let v121 = Rc::clone(&xa);
  let v124 = Rc::clone(&xb);
  let adj = fill_loop_1(v121, v124, m, K, 0u64, v111, v118);
  let v142 = rocq_array::make::<bool>(V, false);
  let v153 = rocq_array::set::<bool>(v142, 1u64, true);
  let v160 = rocq_array::make::<u64>(V, 0u64);
  let v167 = rocq_array::make::<u64>(V, 0u64);
  let v174 = rocq_array::make::<u64>(V, 0u64);
  let v181 = rocq_array::make::<u64>(n, 0u64);
  let v192 = rocq_array::set::<u64>(v181, 0u64, 1u64);
  let st0 = Rc::new(bst { vis: v153, dst: v160, par: v167, pe: v174, ord: v192, tl: 1u64 });
  let v214 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(oc);
  let st = bfs_loop_1(xa, xb, xd, m, adj, v214, 0u64, st0);
  let v238 = Rc::clone(&st);
  let v239 = ord(v238);
  let v243 = Rc::clone(&st);
  let v244 = par(v243);
  let v248 = Rc::clone(&st);
  let v249 = dst(v248);
  let v261 = sub(tl_owned(st), 1u64);
  let v268 = rocq_array::make::<bool>(V, false);
  sweep_loop_1(s, inl, v239, v244, v249, v261, v268, 0u64)
}

// Rocq: Joggers.joggers_implem.joggers_impl
pub fn joggers_impl_curried(n: u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>> {
  let v3 = {
    move |s: u64| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> {
      let n = &n;
      let v8 = Clone::clone(n);
      let v11 = {
        move |xa: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
          let n = &v8;
          let s = &s;
          let v18 = Clone::clone(n);
          let v20 = Clone::clone(s);
          let v23 = {
            move |xb: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
              let n = &v18;
              let s = &v20;
              let xa = &xa;
              let v32 = Clone::clone(n);
              let v34 = Clone::clone(s);
              let v36 = Rc::clone(xa);
              let v39 = {
                move |xd: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
                  let n = &v32;
                  let s = &v34;
                  let xa = &v36;
                  let xb = &xb;
                  let v50 = Clone::clone(n);
                  let v52 = Clone::clone(s);
                  let v54 = Rc::clone(xa);
                  let v56 = Rc::clone(xb);
                  let v59 = {
                    move |xl: Rc<Array<u64>>| -> u64 {
                      let v73 = Clone::clone(&v50);
                      let v75 = Clone::clone(&v52);
                      let v77 = Rc::clone(&v54);
                      let v79 = Rc::clone(&v56);
                      let v81 = Rc::clone(&xd);
                      joggers_impl(v73, v75, v77, v79, v81, xl)
                    }
                  };
                  let v87: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v59);
                  v87
                }
              };
              let v91: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v39);
              v91
            }
          };
          let v95: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v23);
          v95
        }
      };
      let v99: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> = Rc::new(v11);
      v99
    }
  };
  let v103: Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>> = Rc::new(v3);
  v103
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

pub fn run() -> Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_801.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_801: Rc<dyn Fn(u64, u64, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = joggers(); }
std::thread_local! { static __rocq_global_804: Rc<dyn Fn(u64) -> Rc<dyn Fn(u64) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>>>> = joggers_curried(); }