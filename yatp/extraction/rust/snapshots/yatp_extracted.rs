// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Yatp.yatp_implem.yatp
// Variant: uncurried
pub fn yatp() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64 = yatp_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
}

// Rocq: Yatp.yatp_implem.yatp
pub fn yatp_curried() -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> {
  let v0: fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = yatp_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> = Rc::new(v0);
  v1
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
  match b {
    true => {
      sumbool::left
    },
    false => {
      sumbool::right
    },
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
  let v11 = mod_(h, 2u64);
  match eqb(v11, 0u64) {
    true => {
      std::mem::drop(xv);
      let v27 = div(h, 2u64);
      let v28 = &xu;
      let v31 = rocq_array::get::<u64>(&v28, v27);
      std::mem::drop(xu);
      v31
    },
    false => {
      std::mem::drop(xu);
      let v41 = div(h, 2u64);
      let v42 = &xv;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      std::mem::drop(xv);
      v45
    },
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
  let v13 = ltb(h, hh);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&xu);
      let v23 = Rc::clone(&xv);
      let x = hsrc(v20, v23, h);
      let v34 = add(h, 1u64);
      let v36 = &deg;
      let v39 = rocq_array::get::<u64>(&v36, x);
      let v53 = rocq_array::set::<u64>(deg, x, add(v39, 1u64));
      deg_loop(xu, xv, hh, v34, v53, ())
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
  let v13 = ltb(x, n1);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &sa;
      let s = rocq_array::get::<u64>(&v17, x);
      let v28 = add(x, 1u64);
      let v36 = add(x, 1u64);
      let v38 = &deg;
      let v41 = rocq_array::get::<u64>(&v38, x);
      let v53 = rocq_array::set::<u64>(sa, v36, add(s, v41));
      let v60 = rocq_array::set::<u64>(pos, x, s);
      start_loop(deg, n1, v28, v53, v60, ())
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
  let v11 = mod_(h, 2u64);
  match eqb(v11, 0u64) {
    true => {
      std::mem::drop(xu);
      let v27 = div(h, 2u64);
      let v28 = &xv;
      let v31 = rocq_array::get::<u64>(&v28, v27);
      std::mem::drop(xv);
      v31
    },
    false => {
      std::mem::drop(xv);
      let v41 = div(h, 2u64);
      let v42 = &xu;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      std::mem::drop(xu);
      v45
    },
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
  let v16 = ltb(h, hh);
  match bdec(v16) {
    sumbool::left => {
      let v23 = Rc::clone(&xu);
      let v26 = Rc::clone(&xv);
      let x = hsrc(v23, v26, h);
      let v30 = &pos;
      let i = rocq_array::get::<u64>(&v30, x);
      let v41 = add(h, 1u64);
      let v56 = rocq_array::set::<u64>(pos, x, add(i, 1u64));
      let v60 = Rc::clone(&xu);
      let v63 = Rc::clone(&xv);
      let v73 = rocq_array::set::<u64>(nbr, i, hdst(v60, v63, h));
      let v81 = div(h, 2u64);
      let v82 = &xw;
      let v85 = rocq_array::get::<u64>(&v82, v81);
      let v92 = rocq_array::set::<u64>(wt, i, v85);
      fill_loop(xu, xv, xw, hh, v41, v56, v73, v92, ())
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
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Yatp.yatp_implem.max_loop
// Variant: uncurried
pub fn max_loop_1(a: Rc<Array<u64>>, n: u64, i: u64, acc: u64) -> u64 {
  max_loop(a, n, i, acc, ())
}

// Rocq: Yatp.yatp_implem.max_loop (local: max_loop)
// Variant: uncurried, lifted
pub fn max_loop(a: Rc<Array<u64>>, n: u64, i: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v25 = &a;
      let v28 = rocq_array::get::<u64>(&v25, i);
      let v34 = match ltb(acc, v28) {
        true => {
          let v35 = &a;
          rocq_array::get::<u64>(&v35, i)
        },
        false => {
          acc
        },
      };
      max_loop(a, n, v23, v34, ())
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
  let v11 = ltb(i, n1);
  match bdec(v11) {
    sumbool::left => {
      let v22 = add(i, 1u64);
      let v31 = rocq_array::set::<bool>(a, i, true);
      true_loop(n1, v22, v31, ())
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
  let v1 = b;
  Clone::clone((&(&**v1).b_tail))
}

// Rocq: Yatp.yatp_implem.b_comp
pub fn b_comp(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_comp));
  std::mem::drop(b);
  v3
}

// Rocq: Yatp.yatp_implem.b_vis
pub fn b_vis(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_vis));
  std::mem::drop(b);
  v3
}

// Rocq: Yatp.yatp_implem.b_par
pub fn b_par(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_par));
  std::mem::drop(b);
  v3
}

// Rocq: Yatp.yatp_implem.b_d
pub fn b_d(b: Rc<bst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_d));
  std::mem::drop(b);
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

// Rocq: Yatp.yatp_implem.b_flag
pub fn b_flag_owned(b: Rc<bst>) -> bool {
  let v3 = Clone::clone((&(&**&b).b_flag));
  std::mem::drop(b);
  v3
}

// Rocq: Yatp.yatp_implem.b_flag
// Variant: borrowed
pub fn b_flag(b: &Rc<bst>) -> bool {
  let v1 = b;
  Clone::clone((&(&**v1).b_flag))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Yatp.yatp_implem.scan_step
// Variant: uncurried
pub fn scan_step(alive: Rc<Array<bool>>, s: u64, x: u64, dx: u64, y: u64, w: u64, b: Rc<bst>) -> Rc<bst> {
  let v7 = &alive;
  let v10 = rocq_array::get::<bool>(&v7, y);
  match v10 {
    true => {
      let v16 = Rc::clone(&b);
      let v17 = b_vis(v16);
      let v18 = &v17;
      let v22 = rocq_array::get::<u64>(&v18, y);
      match eqb(v22, s) {
        true => {
          std::mem::drop(v17);
          std::mem::drop(alive);
          let v31 = Rc::clone(&b);
          let v32 = b_vis(v31);
          let v36 = Rc::clone(&b);
          let v37 = b_comp(v36);
          let v41 = Rc::clone(&b);
          let v42 = b_par(v41);
          let v46 = Rc::clone(&b);
          let v47 = b_d(v46);
          let v51 = b_tail(&b);
          let v56 = b_flag(&b);
          let v61 = b_d(b);
          let v62 = &v61;
          let v65 = rocq_array::get::<u64>(&v62, y);
          std::mem::drop(v61);
          Rc::new(bst { b_vis: v32, b_comp: v37, b_par: v42, b_d: v47, b_tail: v51, b_flag: andb(v56, leb(v65, add(dx, w))) })
        },
        false => {
          std::mem::drop(v17);
          std::mem::drop(alive);
          let v102 = Rc::clone(&b);
          let v104 = b_vis(v102);
          let v110 = rocq_array::set::<u64>(v104, y, s);
          let v114 = Rc::clone(&b);
          let v115 = b_comp(v114);
          let v119 = b_tail(&b);
          let v126 = rocq_array::set::<u64>(v115, v119, y);
          let v130 = Rc::clone(&b);
          let v132 = b_par(v130);
          let v138 = rocq_array::set::<u64>(v132, y, x);
          let v142 = Rc::clone(&b);
          let v143 = b_d(v142);
          let v156 = rocq_array::set::<u64>(v143, y, add(dx, w));
          let v161 = b_tail(&b);
          Rc::new(bst { b_vis: v110, b_comp: v126, b_par: v138, b_d: v156, b_tail: add(v161, 1u64), b_flag: b_flag_owned(b) })
        },
      }
    },
    false => {
      std::mem::drop(alive);
      b
    },
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
  let v17 = ltb(j, e);
  match bdec(v17) {
    sumbool::left => {
      let v28 = add(j, 1u64);
      let v30 = &nbr;
      let v33 = rocq_array::get::<u64>(&v30, j);
      let v34 = &wt;
      let v37 = rocq_array::get::<u64>(&v34, j);
      let v40 = Rc::clone(&alive);
      let v53 = scan_step(v40, s, x, dx, v33, v37, b);
      scan_loop(nbr, wt, alive, s, x, dx, e, v28, v53, ())
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
  let v20 = ltb(head, b_tail(&b));
  match bdec(v20) {
    sumbool::left => {
      let v31 = ltb(head, L);
      match bdec(v31) {
        sumbool::left => {
          let v38 = Rc::clone(&b);
          let v39 = b_comp(v38);
          let v40 = &v39;
          let x = rocq_array::get::<u64>(&v40, head);
          std::mem::drop(v39);
          let v51 = add(head, 1u64);
          let v56 = Rc::clone(&b);
          let v57 = b_d(v56);
          let v58 = &v57;
          let v61 = rocq_array::get::<u64>(&v58, x);
          std::mem::drop(v57);
          let v69 = add(x, 1u64);
          let v70 = &sa;
          let v73 = rocq_array::get::<u64>(&v70, v69);
          let v74 = &sa;
          let v77 = rocq_array::get::<u64>(&v74, x);
          let v80 = Rc::clone(&nbr);
          let v83 = Rc::clone(&wt);
          let v86 = Rc::clone(&alive);
          let v99 = scan_loop_1(v80, v83, v86, s, x, v61, v73, v77, b);
          bfs_loop(sa, nbr, wt, alive, s, L, v51, v99, ())
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
  let v12 = rocq_array::set::<u64>(vis, root, s);
  let v21 = rocq_array::set::<u64>(comp, 0u64, root);
  let v28 = rocq_array::set::<u64>(par, root, root);
  let v37 = rocq_array::set::<u64>(d, root, 0u64);
  Rc::new(bst { b_vis: v12, b_comp: v21, b_par: v28, b_d: v37, b_tail: 1u64, b_flag: true })
}

// Rocq: Yatp.yatp_implem.bfs
// Variant: uncurried
pub fn bfs(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, alive: Rc<Array<bool>>, s: u64, root: u64, vis: Rc<Array<u64>>, comp: Rc<Array<u64>>, par: Rc<Array<u64>>, d: Rc<Array<u64>>) -> Rc<bst> {
  let v11 = &comp;
  let v12 = rocq_array::length::<u64>(&v11);
  let v28 = bfs_init(s, root, vis, comp, par, d);
  bfs_loop_1(sa, nbr, wt, alive, s, v12, 0u64, v28)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Yatp.yatp_implem.m_vis
pub fn m_vis(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_vis));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.m_comp
pub fn m_comp(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_comp));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.m_par
pub fn m_par(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_par));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.m_d
pub fn m_d(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_d));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.sz_init
// Variant: uncurried
pub fn sz_init_1(comp: Rc<Array<u64>>, t: u64, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sz_init(comp, t, i, sz, big, ())
}

// Rocq: Yatp.yatp_implem.sz_init (local: sz_init)
// Variant: uncurried, lifted
pub fn sz_init(comp: Rc<Array<u64>>, t: u64, i: u64, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(i, t);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &comp;
      let x = rocq_array::get::<u64>(&v17, i);
      let v28 = add(i, 1u64);
      let v37 = rocq_array::set::<u64>(sz, x, 1u64);
      let v46 = rocq_array::set::<u64>(big, x, 0u64);
      sz_init(comp, t, v28, v37, v46, ())
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
  let v15 = ltb(0u64, i);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &comp;
      let x = rocq_array::get::<u64>(&v19, i);
      let v23 = &par;
      let p = rocq_array::get::<u64>(&v23, x);
      let v27 = &sz;
      let v = rocq_array::get::<u64>(&v27, x);
      let v38 = sub(i, 1u64);
      let v40 = &sz;
      let v44 = rocq_array::get::<u64>(&v40, p);
      let v55 = rocq_array::set::<u64>(sz, p, add(v44, v));
      let v57 = &big;
      let v61 = rocq_array::get::<u64>(&v57, p);
      let v66 = match ltb(v61, v) {
        true => {
          rocq_array::set::<u64>(big, p, v)
        },
        false => {
          big
        },
      };
      sz_acc(comp, par, v38, v55, v66, ())
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
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Yatp.yatp_implem.argmin
// Variant: uncurried
pub fn argmin_1(comp: Rc<Array<u64>>, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, t: u64, i: u64, bi: u64, bv: u64) -> u64 {
  argmin(comp, sz, big, t, i, bi, bv, ())
}

// Rocq: Yatp.yatp_implem.argmin (local: argmin)
// Variant: uncurried, lifted
pub fn argmin(comp: Rc<Array<u64>>, sz: Rc<Array<u64>>, big: Rc<Array<u64>>, t: u64, i: u64, bi: u64, bv: u64, _H: ()) -> u64 {
  let v15 = ltb(i, t);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &comp;
      let x = rocq_array::get::<u64>(&v19, i);
      let v24 = &sz;
      let v27 = rocq_array::get::<u64>(&v24, x);
      let up = sub(t, v27);
      let v34 = &big;
      let v38 = rocq_array::get::<u64>(&v34, x);
      let v = match ltb(v38, up) {
        true => {
          up
        },
        false => {
          let v46 = &big;
          rocq_array::get::<u64>(&v46, x)
        },
      };
      match ltb(v, bv) {
        true => {
          argmin(comp, sz, big, t, add(i, 1u64), i, v, ())
        },
        false => {
          argmin(comp, sz, big, t, add(i, 1u64), bi, bv, ())
        },
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
  let v10 = Rc::clone(&comp);
  let sb = sz_init_1(v10, t, 0u64, sz, big);
  let v28 = sub(t, 1u64);
  let v31 = Clone::clone(&sb);
  let v33 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v31);
  let v37 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(sb);
  let v40 = Rc::clone(&comp);
  let sb_ = sz_acc_1(v40, par, v28, v33, v37);
  let v53 = Clone::clone(&sb_);
  let v55 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v53);
  let v58 = Clone::clone(&sb_);
  let v60 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v58);
  let v67 = Rc::clone(&comp);
  let v80 = argmin_1(v67, v55, v60, t, 0u64, 0u64, t);
  let v81 = &comp;
  let v84 = rocq_array::get::<u64>(&v81, v80);
  std::mem::drop(comp);
  (v84, sb_)
}

// Rocq: Yatp.yatp_implem.m_sz
pub fn m_sz(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_sz));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.m_big
pub fn m_big(m: Rc<mst>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&m).m_big));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.pick
// Variant: uncurried
pub fn pick(alive: Rc<Array<bool>>, c: u64, r: u64) -> u64 {
  let v5 = &alive;
  let v6 = rocq_array::length::<bool>(&v5);
  let v11 = ltb(c, v6);
  let v12 = &alive;
  let v15 = rocq_array::get::<bool>(&v12, c);
  match andb(v11, v15) {
    true => {
      std::mem::drop(alive);
      c
    },
    false => {
      std::mem::drop(alive);
      r
    },
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
  let v16 = ltb(j, e);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &nbr;
      let y = rocq_array::get::<u64>(&v20, j);
      let v25 = &wt;
      let v28 = rocq_array::get::<u64>(&v25, j);
      let nv = add(dx, v28);
      let v36 = &alive;
      let v39 = rocq_array::get::<bool>(&v36, y);
      let v41 = &d;
      let v42 = rocq_array::length::<u64>(&v41);
      let v52 = andb(v39, ltb(y, v42));
      let v54 = &d;
      let v57 = rocq_array::get::<u64>(&v54, y);
      let v62 = ltb(nv, v57);
      match andb(v52, v62) {
        true => {
          let v76 = add(j, 1u64);
          let v83 = rocq_array::set::<u64>(d, y, nv);
          rscan(nbr, wt, alive, dx, e, v76, v83, true, ())
        },
        false => {
          rscan(nbr, wt, alive, dx, e, add(j, 1u64), d, ch, ())
        },
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
  let v17 = ltb(i, t);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &comp;
      let x = rocq_array::get::<u64>(&v21, i);
      let v26 = &d;
      let v29 = rocq_array::get::<u64>(&v26, x);
      let v37 = add(x, 1u64);
      let v38 = &sa;
      let v41 = rocq_array::get::<u64>(&v38, v37);
      let v42 = &sa;
      let v45 = rocq_array::get::<u64>(&v42, x);
      let v48 = Rc::clone(&nbr);
      let v51 = Rc::clone(&wt);
      let v54 = Rc::clone(&alive);
      let r = rscan_1(v48, v51, v54, v29, v41, v45, d, ch);
      let v73 = add(i, 1u64);
      let v76 = Clone::clone(&r);
      let v78 = fst::<Rc<Array<u64>>, bool>(v76);
      rpass(sa, nbr, wt, alive, comp, t, v73, v78, snd::<Rc<Array<u64>>, bool>(r), ())
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
  let v15 = Rc::clone(&sa);
  let v18 = Rc::clone(&nbr);
  let v21 = Rc::clone(&wt);
  let v24 = Rc::clone(&alive);
  let v27 = Rc::clone(&comp);
  let pr = rpass_1(v15, v18, v21, v24, v27, t, 0u64, d, false);
  let v40 = Clone::clone(&pr);
  let v43 = snd::<Rc<Array<u64>>, bool>(v40);
  match bdec(v43) {
    sumbool::left => {
      let v50 = fst::<Rc<Array<u64>>, bool>(pr);
      rloop(sa, nbr, wt, alive, comp, t, v50, ())
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
  match b_flag(&b) {
    true => {
      std::mem::drop(sa);
      std::mem::drop(nbr);
      std::mem::drop(wt);
      std::mem::drop(alive);
      std::mem::drop(comp);
      b_d(b)
    },
    false => {
      let v22 = b_d(b);
      rloop_1(sa, nbr, wt, alive, comp, t, v22)
    },
  }
}

// Rocq: Yatp.yatp_implem.lkey
// Variant: uncurried
pub fn lkey(X: u64, lo: u64, hi: u64) -> u64 {
  match eqb(lo, hi) {
    true => {
      add(X, lo)
    },
    false => {
      let v26 = sub(hi, lo);
      let v38 = add(lo, div(v26, 2u64));
      add(v38, 1u64)
    },
  }
}

// Rocq: Yatp.yatp_implem.l_st
pub fn l_st_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&l).l_st));
  std::mem::drop(l);
  v3
}

// Rocq: Yatp.yatp_implem.l_st
// Variant: borrowed
pub fn l_st(l: &Rc<lct>) -> Rc<Array<u64>> {
  let v1 = l;
  Rc::clone((&(&**v1).l_st))
}

// Rocq: Yatp.yatp_implem.l_m
pub fn l_m_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&l).l_m));
  std::mem::drop(l);
  v3
}

// Rocq: Yatp.yatp_implem.l_m
// Variant: borrowed
pub fn l_m(l: &Rc<lct>) -> Rc<Array<u64>> {
  let v1 = l;
  Rc::clone((&(&**v1).l_m))
}

// Rocq: Yatp.yatp_implem.l_b
pub fn l_b_owned(l: Rc<lct>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&l).l_b));
  std::mem::drop(l);
  v3
}

// Rocq: Yatp.yatp_implem.l_b
// Variant: borrowed
pub fn l_b(l: &Rc<lct>) -> Rc<Array<u64>> {
  let v1 = l;
  Rc::clone((&(&**v1).l_b))
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
  let v20 = Rc::clone(&T);
  let v21 = l_st_owned(v20);
  let v22 = &v21;
  let v26 = rocq_array::get::<u64>(&v22, k);
  match eqb(v26, s) {
    true => {
      let v35 = Rc::clone(&T);
      let v36 = l_m_owned(v35);
      let v37 = &v36;
      let cm = rocq_array::get::<u64>(&v37, k);
      let v44 = Rc::clone(&T);
      let v45 = l_b_owned(v44);
      let v46 = &v45;
      let cb = rocq_array::get::<u64>(&v46, k);
      let v57 = sub(hi, lo);
      let mid = add(lo, div(v57, 2u64));
      let nb = ltb(add(mul(m, mid), b), add(mul(cm, mid), cb));
      let wm = match &nb {
        true => {
          m
        },
        false => {
          cm
        },
      };
      let wb = match &nb {
        true => {
          b
        },
        false => {
          cb
        },
      };
      let om = match &nb {
        true => {
          cm
        },
        false => {
          m
        },
      };
      let ob = match &nb {
        true => {
          cb
        },
        false => {
          b
        },
      };
      let T1 = match &nb {
        true => {
          let v133 = Rc::clone(&T);
          let v134 = l_st_owned(v133);
          let v138 = Rc::clone(&T);
          let v140 = l_m_owned(v138);
          let v146 = rocq_array::set::<u64>(v140, k, m);
          let v151 = l_b_owned(T);
          let v157 = rocq_array::set::<u64>(v151, k, b);
          Rc::new(lct { l_st: v134, l_m: v146, l_b: v157 })
        },
        false => {
          T
        },
      };
      let v179 = ltb(lo, hi);
      match bdec(v179) {
        sumbool::left => {
          let v195 = add(mul(om, lo), ob);
          let v207 = add(mul(wm, lo), wb);
          match ltb(v195, v207) {
            true => {
              std::mem::drop(v45);
              std::mem::drop(v36);
              std::mem::drop(v21);
              lc_insert(X, s, lo, mid, om, ob, T1, ())
            },
            false => {
              std::mem::drop(v45);
              std::mem::drop(v36);
              std::mem::drop(v21);
              lc_insert(X, s, add(mid, 1u64), hi, om, ob, T1, ())
            },
          }
        },
        sumbool::right => {
          std::mem::drop(v45);
          std::mem::drop(v36);
          std::mem::drop(v21);
          T1
        },
      }
    },
    false => {
      std::mem::drop(v21);
      let v277 = Rc::clone(&T);
      let v279 = l_st_owned(v277);
      let v285 = rocq_array::set::<u64>(v279, k, s);
      let v289 = Rc::clone(&T);
      let v291 = l_m_owned(v289);
      let v297 = rocq_array::set::<u64>(v291, k, m);
      let v302 = l_b_owned(T);
      let v308 = rocq_array::set::<u64>(v302, k, b);
      Rc::new(lct { l_st: v285, l_m: v297, l_b: v308 })
    },
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
  let v16 = ltb(i, t);
  match bdec(v16) {
    sumbool::left => {
      let v20 = &comp;
      let v = rocq_array::get::<u64>(&v20, i);
      let v31 = add(i, 1u64);
      let v42 = sub(X, 1u64);
      let v50 = sub(v, 1u64);
      let v51 = &xp;
      let v54 = rocq_array::get::<u64>(&v51, v50);
      let v55 = &d;
      let v58 = rocq_array::get::<u64>(&v55, v);
      let v73 = lc_insert_1(X, s, 0u64, v42, v54, v58, T);
      ins_loop(xp, comp, d, X, s, t, v31, v73, ())
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
  let v3 = Rc::clone((&(&**&m).m_T));
  std::mem::drop(m);
  v3
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
  let v24 = l_st(T);
  let v25 = &v24;
  let v29 = rocq_array::get::<u64>(&v25, k);
  let v = match eqb(v29, s_1) {
    true => {
      let v40 = l_m(T);
      let v41 = &v40;
      let v44 = rocq_array::get::<u64>(&v41, k);
      std::mem::drop(v40);
      let v49 = mul(v44, x_1);
      let v53 = l_b(T);
      let v54 = &v53;
      let v57 = rocq_array::get::<u64>(&v54, k);
      std::mem::drop(v53);
      add(v49, v57)
    },
    false => {
      __rocq_global_443
    },
  };
  let v76 = ltb(lo_1, hi_1);
  match bdec(v76) {
    sumbool::left => {
      let v87 = sub(hi_1, lo_1);
      let mid = add(lo_1, div(v87, 2u64));
      let r = match leb(x_1, mid) {
        true => {
          lc_query(X_1, s_1, lo_1, mid, x_1, T, ())
        },
        false => {
          lc_query(X_1, s_1, add(mid, 1u64), hi_1, x_1, T, ())
        },
      };
      match ltb(r, v) {
        true => {
          std::mem::drop(v24);
          r
        },
        false => {
          std::mem::drop(v24);
          v
        },
      }
    },
    sumbool::right => {
      std::mem::drop(v24);
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
  let v17 = ltb(i, t);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &comp;
      let u = rocq_array::get::<u64>(&v21, i);
      let v26 = &d;
      let v29 = rocq_array::get::<u64>(&v26, u);
      let v39 = sub(X, 1u64);
      let v47 = sub(u, 1u64);
      let v48 = &xp;
      let v51 = rocq_array::get::<u64>(&v48, v47);
      let q = add(v29, lc_query_1(X, s, 0u64, v39, v51, &T));
      let v78 = add(i, 1u64);
      let v80 = &best;
      let v83 = rocq_array::get::<u64>(&v80, u);
      let v89 = match ltb(q, v83) {
        true => {
          rocq_array::set::<u64>(best, u, q)
        },
        false => {
          best
        },
      };
      qry_loop(xp, comp, d, X, s, t, v78, T, v89, ())
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
  let v3 = Rc::clone((&(&**&m).m_best));
  std::mem::drop(m);
  v3
}

// Rocq: Yatp.yatp_implem.process
// Variant: uncurried
pub fn process(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, alive: Rc<Array<bool>>, r: u64, rnd: u64, S: Rc<mst>) -> (u64, Rc<mst>) {
  let v17 = mul(2u64, rnd);
  let v21 = Rc::clone(&S);
  let v22 = m_vis(v21);
  let v26 = Rc::clone(&S);
  let v27 = m_comp(v26);
  let v31 = Rc::clone(&S);
  let v32 = m_par(v31);
  let v36 = Rc::clone(&S);
  let v37 = m_d(v36);
  let v40 = Rc::clone(&sa);
  let v43 = Rc::clone(&nbr);
  let v46 = Rc::clone(&wt);
  let v49 = Rc::clone(&alive);
  let b1 = bfs(v40, v43, v46, v49, v17, r, v22, v27, v32, v37);
  let v67 = Rc::clone(&b1);
  let v68 = b_comp(v67);
  let v72 = Rc::clone(&b1);
  let v73 = b_par(v72);
  let v77 = Rc::clone(&S);
  let v78 = m_sz(v77);
  let v82 = Rc::clone(&S);
  let v83 = m_big(v82);
  let v87 = b_tail(&b1);
  let cr = centroid(v68, v73, v78, v83, v87);
  let v102 = Clone::clone(&cr);
  let v104 = fst::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(v102);
  let v107 = Rc::clone(&alive);
  let c = pick(v107, v104, r);
  let v129 = add(mul(2u64, rnd), 1u64);
  let v133 = Rc::clone(&b1);
  let v134 = b_vis(v133);
  let v138 = Rc::clone(&b1);
  let v139 = b_comp(v138);
  let v143 = Rc::clone(&b1);
  let v144 = b_par(v143);
  let v148 = b_d(b1);
  let v151 = Rc::clone(&sa);
  let v154 = Rc::clone(&nbr);
  let v157 = Rc::clone(&wt);
  let v160 = Rc::clone(&alive);
  let b2 = bfs(v151, v154, v157, v160, v129, c, v134, v139, v144, v148);
  let t = b_tail(&b2);
  let v182 = Rc::clone(&b2);
  let v183 = b_comp(v182);
  let v198 = Rc::clone(&b2);
  let d = relax(sa, nbr, wt, alive, v183, t, v198);
  let v204 = Rc::clone(&b2);
  let v205 = b_comp(v204);
  let v211 = Rc::clone(&S);
  let v212 = m_T(v211);
  let v215 = Rc::clone(&xp);
  let v220 = Rc::clone(&d);
  let T = ins_loop_1(v215, v205, v220, X, rnd, t, 0u64, v212);
  let v236 = Rc::clone(&b2);
  let v237 = b_comp(v236);
  let v243 = m_best(S);
  let v250 = Rc::clone(&d);
  let v261 = Rc::clone(&T);
  let best = qry_loop_1(xp, v237, v250, X, rnd, t, 0u64, v261, v243);
  let v268 = Rc::clone(&b2);
  let v269 = b_vis(v268);
  let v273 = Rc::clone(&b2);
  let v274 = b_comp(v273);
  let v278 = b_par(b2);
  let v282 = Clone::clone(&cr);
  let v287 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(snd::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(v282));
  let v295 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(snd::<u64, (Rc<Array<u64>>, Rc<Array<u64>>)>(cr));
  (c, Rc::new(mst { m_vis: v269, m_comp: v274, m_par: v278, m_d: d, m_sz: v287, m_big: v295, m_T: T, m_best: best }))
}

// Rocq: Yatp.yatp_implem.main_loop
// Variant: uncurried
pub fn main_loop_1(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, r: u64, rnd: u64, alive: Rc<Array<bool>>, S: Rc<mst>) -> Rc<Array<u64>> {
  main_loop(sa, nbr, wt, xp, X, r, rnd, alive, S, ())
}

// Rocq: Yatp.yatp_implem.main_loop (local: main_loop)
// Variant: uncurried, lifted
pub fn main_loop(sa: Rc<Array<u64>>, nbr: Rc<Array<u64>>, wt: Rc<Array<u64>>, xp: Rc<Array<u64>>, X: u64, r: u64, rnd: u64, alive: Rc<Array<bool>>, S: Rc<mst>, _H: ()) -> Rc<Array<u64>> {
  let v12 = &alive;
  let v13 = rocq_array::length::<bool>(&v12);
  let v19 = ltb(r, v13);
  match bdec(v19) {
    sumbool::left => {
      let v24 = &alive;
      let v28 = rocq_array::get::<bool>(&v24, r);
      match bdec(v28) {
        sumbool::left => {
          let v35 = Rc::clone(&sa);
          let v38 = Rc::clone(&nbr);
          let v41 = Rc::clone(&wt);
          let v44 = Rc::clone(&xp);
          let v49 = Rc::clone(&alive);
          let cS = process(v35, v38, v41, v44, X, v49, r, rnd, S);
          let v64 = add(rnd, 1u64);
          let v67 = Clone::clone(&cS);
          let v78 = rocq_array::set::<bool>(alive, fst::<u64, Rc<mst>>(v67), false);
          main_loop(sa, nbr, wt, xp, X, r, v64, v78, snd::<u64, Rc<mst>>(cS), ())
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
  let v12 = ltb(i, n1);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v25 = &best;
      let v28 = rocq_array::get::<u64>(&v25, i);
      sum_loop(best, n1, v23, add(acc, v28), ())
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
  let v4 = &xp;
  let n = rocq_array::length::<u64>(&v4);
  let n1 = add(n, 1u64);
  let v15 = &xu;
  let v16 = rocq_array::length::<u64>(&v15);
  let v17 = &xu;
  let v18 = rocq_array::length::<u64>(&v17);
  let hh = add(v16, v18);
  let v33 = rocq_array::make::<u64>(n1, 0u64);
  let v36 = Rc::clone(&xu);
  let v39 = Rc::clone(&xv);
  let deg = deg_loop_1(v36, v39, hh, 0u64, v33);
  let v64 = rocq_array::make::<u64>(add(n1, 1u64), 0u64);
  let v71 = rocq_array::make::<u64>(n1, 0u64);
  let sp = start_loop_1(deg, n1, 0u64, v64, v71);
  let v88 = Clone::clone(&sp);
  let v90 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(v88);
  let v97 = rocq_array::make::<u64>(hh, 0u64);
  let v104 = rocq_array::make::<u64>(hh, 0u64);
  let nw = fill_loop_1(xu, xv, xw, hh, 0u64, v90, v97, v104);
  let v130 = Rc::clone(&xp);
  let X = add(max_loop_1(v130, n, 0u64, 0u64), 1u64);
  let v154 = rocq_array::make::<bool>(n1, false);
  let alive = true_loop_1(n1, 1u64, v154);
  let v168 = rocq_array::make::<u64>(n1, 0u64);
  let v175 = rocq_array::make::<u64>(n1, 0u64);
  let v182 = rocq_array::make::<u64>(n1, 0u64);
  let v189 = rocq_array::make::<u64>(n1, 0u64);
  let v196 = rocq_array::make::<u64>(n1, 0u64);
  let v203 = rocq_array::make::<u64>(n1, 0u64);
  let v216 = rocq_array::make::<u64>(add(X, X), 0u64);
  let v229 = rocq_array::make::<u64>(add(X, X), 0u64);
  let v242 = rocq_array::make::<u64>(add(X, X), 0u64);
  let v251 = Rc::new(lct { l_st: v216, l_m: v229, l_b: v242 });
  let v257 = rocq_array::make::<u64>(n1, __rocq_global_443);
  let S = Rc::new(mst { m_vis: v168, m_comp: v175, m_par: v182, m_d: v189, m_sz: v196, m_big: v203, m_T: v251, m_best: v257 });
  let v281 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sp);
  let v284 = Clone::clone(&nw);
  let v286 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v284);
  let v290 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(nw);
  let best = main_loop_1(v281, v286, v290, xp, X, 1u64, 1u64, alive, S);
  sum_loop_1(best, n1, 1u64, 0u64)
}

// Rocq: Yatp.yatp_implem.yatp_impl
pub fn yatp_impl_curried(xp: Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> {
  let v3 = {
    move |xu: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> {
      let xp = &xp;
      let v8 = Rc::clone(xp);
      let v11 = {
        move |xv: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
          let xp = &v8;
          let xu = &xu;
          let v18 = Rc::clone(xp);
          let v20 = Rc::clone(xu);
          let v23 = {
            move |xw: Rc<Array<u64>>| -> u64 {
              let v33 = Rc::clone(&v18);
              let v35 = Rc::clone(&v20);
              let v37 = Rc::clone(&xv);
              yatp_impl(v33, v35, v37, xw)
            }
          };
          let v43: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v23);
          v43
        }
      };
      let v47: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>> = Rc::new(v11);
      v47
    }
  };
  let v51: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>> = Rc::new(v3);
  v51
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = __rocq_global_2177.with(Clone::clone);
  v0
}
const __rocq_global_443: u64 = 4611686018427387904u64;
std::thread_local! { static __rocq_global_2177: Rc<dyn Fn(Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>, Rc<Array<u64>>) -> u64> = yatp(); }
std::thread_local! { static __rocq_global_2180: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> u64>>>> = yatp_curried(); }