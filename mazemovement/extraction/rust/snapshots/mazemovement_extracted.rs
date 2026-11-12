// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct st {
  pub s_tbl: Rc<Array<u64>>,
  pub s_ex: Rc<Array<u64>>,
  pub s_h: Rc<Array<u64>>,
  pub s_cur: Rc<Array<u64>>,
  pub s_cnt: Rc<Array<u64>>,
  pub s_q: Rc<Array<u64>>,
  pub s_qh: u64,
  pub s_ql: u64,
  pub s_cu: u64,
  pub s_rl: u64,
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

pub type uint = u64;

// Rocq: Mazemovement.mazemovement_implem.mazemovement
pub fn mazemovement() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: fn(Rc<Array<u64>>) -> u64 = mazemovement_impl;
  let v1: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = Rc::new(v0);
  v1
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.nn
pub fn nn(x: Rc<Array<u64>>) -> u64 {
  let v1 = &x;
  let v2 = rocq_array::length::<u64>(&v1);
  std::mem::drop(x);
  v2
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

// Rocq: Mazemovement.mazemovement_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.rng_ok
// Variant: uncurried
pub fn rng_ok_1(x: Rc<Array<u64>>, n: u64, i: u64) -> bool {
  rng_ok(x, n, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.rng_ok (local: rng_ok)
// Variant: uncurried, lifted
pub fn rng_ok(x: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> bool {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v19 = &x;
      let v22 = rocq_array::get::<u64>(&v19, i);
      let v27 = leb(2u64, v22);
      let v29 = &x;
      let v32 = rocq_array::get::<u64>(&v29, i);
      let v39 = leb(v32, 2000000000u64);
      match andb(v27, v39) {
        true => {
          rng_ok(x, n, add(i, 1u64), ())
        },
        false => {
          std::mem::drop(x);
          false
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      true
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

// Rocq: Mazemovement.mazemovement_implem.amin
// Variant: uncurried
pub fn amin_1(x: Rc<Array<u64>>, n: u64, i: u64, best: u64) -> u64 {
  amin(x, n, i, best, ())
}

// Rocq: Mazemovement.mazemovement_implem.amin (local: amin)
// Variant: uncurried, lifted
pub fn amin(x: Rc<Array<u64>>, n: u64, i: u64, best: u64, _H: ()) -> u64 {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v25 = &x;
      let v28 = rocq_array::get::<u64>(&v25, i);
      let v29 = &x;
      let v32 = rocq_array::get::<u64>(&v29, best);
      let v38 = match ltb(v28, v32) {
        true => {
          i
        },
        false => {
          best
        },
      };
      amin(x, n, v23, v38, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      best
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.ss
pub fn ss(x: Rc<Array<u64>>) -> u64 {
  let v5 = Rc::clone(&x);
  amin_1(x, nn(v5), 1u64, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.amax
// Variant: uncurried
pub fn amax_1(x: Rc<Array<u64>>, n: u64, i: u64, best: u64) -> u64 {
  amax(x, n, i, best, ())
}

// Rocq: Mazemovement.mazemovement_implem.amax (local: amax)
// Variant: uncurried, lifted
pub fn amax(x: Rc<Array<u64>>, n: u64, i: u64, best: u64, _H: ()) -> u64 {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v25 = &x;
      let v28 = rocq_array::get::<u64>(&v25, best);
      let v29 = &x;
      let v32 = rocq_array::get::<u64>(&v29, i);
      let v38 = match ltb(v28, v32) {
        true => {
          i
        },
        false => {
          best
        },
      };
      amax(x, n, v23, v38, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      best
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.tt
pub fn tt(x: Rc<Array<u64>>) -> u64 {
  let v5 = Rc::clone(&x);
  amax_1(x, nn(v5), 1u64, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.guard
pub fn guard(x: Rc<Array<u64>>) -> bool {
  let v10 = Rc::clone(&x);
  let v16 = leb(2u64, nn(v10));
  let v21 = Rc::clone(&x);
  let v34 = andb(v16, leb(nn(v21), 1000u64));
  let v39 = Rc::clone(&x);
  let v40 = nn(v39);
  let v45 = Rc::clone(&x);
  let v55 = andb(v34, rng_ok_1(v45, v40, 0u64));
  let v61 = Rc::clone(&x);
  andb(v55, negb(eqb(ss(v61), tt(x))))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mod
// Variant: uncurried
pub fn mod_(v0: u64, v1: u64) -> u64 {
  rocq_int63::modulo(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.gcd_loop
// Variant: uncurried
pub fn gcd_loop_1(a: u64, b: u64) -> u64 {
  gcd_loop(a, b, ())
}

// Rocq: Mazemovement.mazemovement_implem.gcd_loop (local: gcd_loop)
// Variant: uncurried, lifted
pub fn gcd_loop(a: u64, b: u64, _H: ()) -> u64 {
  let v12 = eqb(b, 0u64);
  match bdec(v12) {
    sumbool::left => {
      a
    },
    sumbool::right => {
      let v23 = mod_(a, b);
      gcd_loop(b, v23, ())
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.igcd
// Variant: uncurried
pub fn igcd(a: u64, b: u64) -> u64 {
  gcd_loop_1(a, b)
}

// Rocq: Mazemovement.mazemovement_implem.capf
// Variant: uncurried
pub fn capf(x: Rc<Array<u64>>, i: u64, j: u64) -> u64 {
  match eqb(i, j) {
    true => {
      std::mem::drop(x);
      0u64
    },
    false => {
      let v15 = &x;
      let v18 = rocq_array::get::<u64>(&v15, i);
      let v19 = &x;
      let v22 = rocq_array::get::<u64>(&v19, j);
      let g = igcd(v18, v22);
      match ltb(1u64, g) {
        true => {
          std::mem::drop(x);
          g
        },
        false => {
          std::mem::drop(x);
          0u64
        },
      }
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.fill_row
// Variant: uncurried
pub fn fill_row_1(x: Rc<Array<u64>>, n: u64, i: u64, tbl: Rc<Array<u64>>, j: u64) -> Rc<Array<u64>> {
  fill_row(x, n, i, tbl, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.fill_row (local: fill_row)
// Variant: uncurried, lifted
pub fn fill_row(x: Rc<Array<u64>>, n: u64, i: u64, tbl: Rc<Array<u64>>, j: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(j, n);
  match bdec(v13) {
    sumbool::left => {
      let v20 = Rc::clone(&x);
      let c = capf(v20, i, j);
      let v44 = rocq_array::set::<u64>(tbl, add(mul(i, n), j), c);
      let v63 = rocq_array::set::<u64>(v44, add(mul(j, n), i), c);
      fill_row(x, n, i, v63, add(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tbl
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.fill_tab
// Variant: uncurried
pub fn fill_tab_1(x: Rc<Array<u64>>, n: u64, tbl: Rc<Array<u64>>, i: u64) -> Rc<Array<u64>> {
  fill_tab(x, n, tbl, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.fill_tab (local: fill_tab)
// Variant: uncurried, lifted
pub fn fill_tab(x: Rc<Array<u64>>, n: u64, tbl: Rc<Array<u64>>, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v19 = Rc::clone(&x);
      let v28 = fill_row_1(v19, n, i, tbl, i);
      fill_tab(x, n, v28, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      tbl
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.sat
// Variant: uncurried
pub fn sat_1(n: u64, s: u64, t: u64, tbl: Rc<Array<u64>>, ex: Rc<Array<u64>>, q: Rc<Array<u64>>, ql: u64, v: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  sat(n, s, t, tbl, ex, q, ql, v, ())
}

// Rocq: Mazemovement.mazemovement_implem.sat (local: sat)
// Variant: uncurried, lifted
pub fn sat(n: u64, s: u64, t: u64, tbl: Rc<Array<u64>>, ex: Rc<Array<u64>>, q: Rc<Array<u64>>, ql: u64, v: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64) {
  let v16 = ltb(v, n);
  match bdec(v16) {
    sumbool::left => {
      let v31 = add(mul(s, n), v);
      let v32 = &tbl;
      let c = rocq_array::get::<u64>(&v32, v31);
      let tbl1 = rocq_array::set::<u64>(tbl, add(mul(s, n), v), 0u64);
      let v68 = add(mul(v, n), s);
      let v81 = add(mul(v, n), s);
      let v82 = &tbl1;
      let v86 = rocq_array::get::<u64>(&v82, v81);
      let tbl2 = rocq_array::set::<u64>(tbl1, v68, add(v86, c));
      let ex1 = rocq_array::set::<u64>(ex, v, c);
      let v129 = andb(ltb(0u64, c), negb(eqb(v, t)));
      let b = andb(v129, negb(eqb(v, s)));
      let q1 = match &b {
        true => {
          rocq_array::set::<u64>(q, ql, v)
        },
        false => {
          q
        },
      };
      let ql1 = match &b {
        true => {
          add(ql, 1u64)
        },
        false => {
          ql
        },
      };
      sat(n, s, t, tbl2, ex1, q1, ql1, add(v, 1u64), ())
    },
    sumbool::right => {
      (((tbl, ex), q), ql)
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.has_val
// Variant: uncurried
pub fn has_val_1(d: Rc<Array<u64>>, n: u64, L: u64, j: u64) -> bool {
  has_val(d, n, L, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.has_val (local: has_val)
// Variant: uncurried, lifted
pub fn has_val(d: Rc<Array<u64>>, n: u64, L: u64, j: u64, _H: ()) -> bool {
  let v12 = ltb(j, n);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &d;
      let v21 = rocq_array::get::<u64>(&v17, j);
      match eqb(v21, L) {
        true => {
          std::mem::drop(d);
          true
        },
        false => {
          has_val(d, n, L, add(j, 1u64), ())
        },
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
pub fn amap_1(F: Rc<dyn Fn(u64, u64) -> u64>, a: Rc<Array<u64>>, i: u64, m: u64) -> Rc<Array<u64>> {
  amap(F, a, i, m, ())
}

// Rocq: Mazemovement.mazemovement_implem.amap (local: amap)
// Variant: uncurried, lifted
pub fn amap(F: Rc<dyn Fn(u64, u64) -> u64>, a: Rc<Array<u64>>, i: u64, m: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, m);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &a;
      let o = rocq_array::get::<u64>(&v16, i);
      let v20: &Rc<dyn Fn(u64, u64) -> u64> = &F;
      let w = v20(i, o);
      let v32 = match eqb(w, o) {
        true => {
          a
        },
        false => {
          rocq_array::set::<u64>(a, i, w)
        },
      };
      amap(F, v32, add(i, 1u64), m, ())
    },
    sumbool::right => {
      std::mem::drop(F);
      a
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.relaxF
// Variant: borrowed, uncurried
pub fn relaxF(tbl: &Rc<Array<u64>>, n: u64, b: u64, L1: u64, a: u64, o: u64) -> u64 {
  let n_1 = n;
  let b_1 = b;
  let L1_1 = L1;
  let a_1 = a;
  let o_1 = o;
  let v26 = add(mul(a_1, n_1), b_1);
  let v27 = tbl;
  let v35 = ltb(0u64, rocq_array::get::<u64>(&v27, v26));
  let v41 = ltb(L1_1, o_1);
  match andb(v35, v41) {
    true => {
      L1_1
    },
    false => {
      o_1
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.lscan
// Variant: uncurried
pub fn lscan_1(tbl: Rc<Array<u64>>, n: u64, L: u64, d: Rc<Array<u64>>, j: u64) -> Rc<Array<u64>> {
  lscan(tbl, n, L, d, j, ())
}

// Rocq: Mazemovement.mazemovement_implem.lscan (local: lscan)
// Variant: uncurried, lifted
pub fn lscan(tbl: Rc<Array<u64>>, n: u64, L: u64, d: Rc<Array<u64>>, j: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(j, n);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &d;
      let v22 = rocq_array::get::<u64>(&v18, j);
      let v27 = match eqb(v22, L) {
        true => {
          let v36 = add(L, 1u64);
          let v39 = Rc::clone(&tbl);
          let v46 = {
            let __anf_capture_49 = n;
            let __anf_capture_51 = j;
            move |v55: u64, v56: u64| -> u64 {
              let tbl = &v39;
              let v58 = Clone::clone(&__anf_capture_49);
              let v60 = Clone::clone(&__anf_capture_51);
              let v62 = Clone::clone(&v36);
              relaxF(tbl, v58, v60, v62, v55, v56)
            }
          };
          let v72: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v46);
          amap_1(v72, d, 0u64, n)
        },
        false => {
          d
        },
      };
      lscan(tbl, n, L, v27, add(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(tbl);
      d
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.layers
// Variant: uncurried
pub fn layers_1(tbl: Rc<Array<u64>>, n: u64, L: u64, d: Rc<Array<u64>>) -> Rc<Array<u64>> {
  layers(tbl, n, L, d, ())
}

// Rocq: Mazemovement.mazemovement_implem.layers (local: layers)
// Variant: uncurried, lifted
pub fn layers(tbl: Rc<Array<u64>>, n: u64, L: u64, d: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(L, n);
  match bdec(v12) {
    sumbool::left => {
      let v21 = Rc::clone(&d);
      match has_val_1(v21, n, L, 0u64) {
        true => {
          let v37 = add(L, 1u64);
          let v43 = Rc::clone(&tbl);
          let v52 = lscan_1(v43, n, L, d, 0u64);
          layers(tbl, n, v37, v52, ())
        },
        false => {
          std::mem::drop(tbl);
          d
        },
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
pub fn bfs(tbl: Rc<Array<u64>>, n: u64, t: u64) -> Rc<Array<u64>> {
  let v10 = rocq_array::make::<u64>(n, n);
  let v19 = rocq_array::set::<u64>(v10, t, 0u64);
  layers_1(tbl, n, 0u64, v19)
}

// Rocq: Mazemovement.mazemovement_implem.maxF
// Variant: borrowed, uncurried
pub fn maxF(d: &Rc<Array<u64>>, y: u64, o: u64) -> u64 {
  let y_1 = y;
  let o_1 = o;
  let v6 = d;
  let v9 = rocq_array::get::<u64>(&v6, y_1);
  match ltb(o_1, v9) {
    true => {
      let v16 = d;
      rocq_array::get::<u64>(&v16, y_1)
    },
    false => {
      o_1
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.glob
// Variant: uncurried
pub fn glob(tbl: Rc<Array<u64>>, n: u64, t: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let d = bfs(tbl, n, t);
  let v15 = {
    move |v18: u64, v19: u64| -> u64 {
      maxF(&d, v18, v19)
    }
  };
  let v29: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v15);
  amap_1(v29, h, 0u64, n)
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let v3 = Clone::clone((&(&p).0));
  std::mem::drop(p);
  v3
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let v3 = Clone::clone((&(&p).1));
  std::mem::drop(p);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.cntl
// Variant: uncurried
pub fn cntl_1(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  cntl(h, cnt, n, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.cntl (local: cntl)
// Variant: uncurried, lifted
pub fn cntl(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &h;
      let k = rocq_array::get::<u64>(&v16, i);
      let v21 = &cnt;
      let v24 = rocq_array::get::<u64>(&v21, k);
      let v38 = rocq_array::set::<u64>(cnt, k, add(v24, 1u64));
      cntl(h, v38, n, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      cnt
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.count
// Variant: uncurried
pub fn count(h: Rc<Array<u64>>, n: u64) -> Rc<Array<u64>> {
  let v17 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  cntl_1(h, v17, n, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.init_state
pub fn init_state(x: Rc<Array<u64>>) -> Rc<st> {
  let v4 = Rc::clone(&x);
  let n = nn(v4);
  let v9 = Rc::clone(&x);
  let s = ss(v9);
  let v14 = Rc::clone(&x);
  let t = tt(v14);
  let v29 = rocq_array::make::<u64>(mul(n, n), 0u64);
  let tbl0 = fill_tab_1(x, n, v29, 0u64);
  let v48 = rocq_array::make::<u64>(n, 0u64);
  let v55 = rocq_array::make::<u64>(n, 0u64);
  let p = sat_1(n, s, t, tbl0, v48, v55, 0u64, 0u64);
  let v84 = rocq_array::make::<u64>(n, 0u64);
  let h0 = rocq_array::set::<u64>(v84, s, n);
  let v96 = Clone::clone(&p);
  let v105 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(v96)));
  let h1 = glob(v105, n, t, h0);
  let v118 = Clone::clone(&p);
  let v126 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(v118)));
  let v131 = Clone::clone(&p);
  let v139 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(v131)));
  let v146 = rocq_array::make::<u64>(n, 0u64);
  let v150 = Rc::clone(&h1);
  let v153 = count(v150, n);
  let v157 = Clone::clone(&p);
  let v162 = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(v157));
  Rc::new(st { s_tbl: v126, s_ex: v139, s_h: h1, s_cur: v146, s_cnt: v153, s_q: v162, s_qh: 0u64, s_ql: snd::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p), s_cu: n, s_rl: 0u64 })
}

// Rocq: Mazemovement.mazemovement_implem.adm
// Variant: uncurried
pub fn adm(tbl: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, u: u64, v: u64) -> bool {
  let v8 = 0u64;
  let v20 = add(mul(u, n), v);
  let v21 = &tbl;
  let v24 = rocq_array::get::<u64>(&v21, v20);
  std::mem::drop(tbl);
  let v29 = ltb(v8, v24);
  let v31 = &h;
  let v34 = rocq_array::get::<u64>(&v31, u);
  let v36 = &h;
  let v39 = rocq_array::get::<u64>(&v36, v);
  std::mem::drop(h);
  andb(v29, eqb(v34, add(v39, 1u64)))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.enq_pos
// Variant: uncurried
pub fn enq_pos(qh: u64, ql: u64, n: u64) -> u64 {
  let p = add(qh, ql);
  match ltb(p, n) {
    true => {
      p
    },
    false => {
      sub(p, n)
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.rmin
// Variant: uncurried
pub fn rmin_1(tbl: Rc<Array<u64>>, n: u64, u: u64, h: Rc<Array<u64>>, b: u64, acc: u64) -> u64 {
  rmin(tbl, n, u, h, b, acc, ())
}

// Rocq: Mazemovement.mazemovement_implem.rmin (local: rmin)
// Variant: uncurried, lifted
pub fn rmin(tbl: Rc<Array<u64>>, n: u64, u: u64, h: Rc<Array<u64>>, b: u64, acc: u64, _H: ()) -> u64 {
  let v14 = ltb(b, n);
  match bdec(v14) {
    sumbool::left => {
      let v25 = add(b, 1u64);
      let v41 = add(mul(u, n), b);
      let v42 = &tbl;
      let v45 = rocq_array::get::<u64>(&v42, v41);
      let v50 = ltb(0u64, v45);
      let v53 = &h;
      let v56 = rocq_array::get::<u64>(&v53, b);
      let v68 = ltb(add(v56, 1u64), acc);
      let v74 = match andb(v50, v68) {
        true => {
          let v76 = &h;
          let v79 = rocq_array::get::<u64>(&v76, b);
          add(v79, 1u64)
        },
        false => {
          acc
        },
      };
      rmin(tbl, n, u, h, v25, v74, ())
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
pub fn no_height_1(h: Rc<Array<u64>>, n: u64, k: u64, i: u64) -> bool {
  no_height(h, n, k, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.no_height (local: no_height)
// Variant: uncurried, lifted
pub fn no_height(h: Rc<Array<u64>>, n: u64, k: u64, i: u64, _H: ()) -> bool {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v17 = &h;
      let v21 = rocq_array::get::<u64>(&v17, i);
      match eqb(v21, k) {
        true => {
          std::mem::drop(h);
          false
        },
        false => {
          no_height(h, n, k, add(i, 1u64), ())
        },
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
pub fn cnt_lift_1(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, k: u64, i: u64) -> Rc<Array<u64>> {
  cnt_lift(h, cnt, n, k, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.cnt_lift (local: cnt_lift)
// Variant: uncurried, lifted
pub fn cnt_lift(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, k: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &h;
      let o = rocq_array::get::<u64>(&v17, i);
      let v27 = ltb(k, o);
      let v33 = ltb(o, n);
      let v39 = match andb(v27, v33) {
        true => {
          let v41 = &cnt;
          let v44 = rocq_array::get::<u64>(&v41, o);
          rocq_array::set::<u64>(cnt, o, sub(v44, 1u64))
        },
        false => {
          cnt
        },
      };
      cnt_lift(h, v39, n, k, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(h);
      cnt
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.liftF
// Variant: uncurried
pub fn liftF(n: u64, k: u64, _y: u64, o: u64) -> u64 {
  let v10 = ltb(k, o);
  let v16 = ltb(o, n);
  match andb(v10, v16) {
    true => {
      n
    },
    false => {
      o
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.lift
// Variant: uncurried
pub fn lift(h: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<u64>> {
  let v8 = {
    let __anf_capture_9 = n;
    move |v13: u64, v14: u64| -> u64 {
      let v17 = Clone::clone(&__anf_capture_9);
      let v19 = Clone::clone(&k);
      liftF(v17, v19, v13, v14)
    }
  };
  let v27: Rc<dyn Fn(u64, u64) -> u64> = Rc::new(v8);
  amap_1(v27, h, 0u64, n)
}

// Rocq: Mazemovement.mazemovement_implem.active
// Variant: uncurried
pub fn active(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, v: u64) -> bool {
  let v11 = 0u64;
  let v12 = &ex;
  let v15 = rocq_array::get::<u64>(&v12, v);
  std::mem::drop(ex);
  let v20 = ltb(v11, v15);
  let v22 = &h;
  let v25 = rocq_array::get::<u64>(&v22, v);
  std::mem::drop(h);
  let v35 = andb(v20, ltb(v25, n));
  let v50 = andb(v35, negb(eqb(v, s)));
  andb(v50, negb(eqb(v, t)))
}

// Rocq: Mazemovement.mazemovement_implem.find_act
// Variant: uncurried
pub fn find_act_1(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, i: u64) -> u64 {
  find_act(ex, h, n, s, t, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.find_act (local: find_act)
// Variant: uncurried, lifted
pub fn find_act(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, i: u64, _H: ()) -> u64 {
  let v14 = ltb(i, n);
  match bdec(v14) {
    sumbool::left => {
      let v21 = Rc::clone(&ex);
      let v24 = Rc::clone(&h);
      match active(v21, v24, n, s, t, i) {
        true => {
          std::mem::drop(ex);
          std::mem::drop(h);
          i
        },
        false => {
          find_act(ex, h, n, s, t, add(i, 1u64), ())
        },
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
pub fn mloop_1(n: u64, s: u64, t: u64, tbl: Rc<Array<u64>>, ex: Rc<Array<u64>>, h: Rc<Array<u64>>, cur: Rc<Array<u64>>, cnt: Rc<Array<u64>>, q: Rc<Array<u64>>, qh: u64, ql: u64, cu: u64, rl: u64) -> u64 {
  mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh, ql, cu, rl, ())
}

// Rocq: Mazemovement.mazemovement_implem.mloop (local: mloop)
// Variant: uncurried, lifted
pub fn mloop(n: u64, s: u64, t: u64, tbl: Rc<Array<u64>>, ex: Rc<Array<u64>>, h: Rc<Array<u64>>, cur: Rc<Array<u64>>, cnt: Rc<Array<u64>>, q: Rc<Array<u64>>, qh: u64, ql: u64, cu: u64, rl: u64, _H: ()) -> u64 {
  let v21 = ltb(cu, n);
  match bdec(v21) {
    sumbool::left => {
      let v25 = &cur;
      let v = rocq_array::get::<u64>(&v25, cu);
      let v36 = ltb(v, n);
      match bdec(v36) {
        sumbool::left => {
          let v44 = Rc::clone(&tbl);
          let v47 = Rc::clone(&h);
          let v55 = adm(v44, v47, n, cu, v);
          match bdec(v55) {
            sumbool::left => {
              let v70 = add(mul(cu, n), v);
              let v71 = &tbl;
              let r = rocq_array::get::<u64>(&v71, v70);
              let v75 = &ex;
              let e = rocq_array::get::<u64>(&v75, cu);
              let d = match ltb(e, r) {
                true => {
                  e
                },
                false => {
                  r
                },
              };
              let tbl1 = rocq_array::set::<u64>(tbl, add(mul(cu, n), v), sub(r, d));
              let v127 = add(mul(v, n), cu);
              let v140 = add(mul(v, n), cu);
              let v141 = &tbl1;
              let v145 = rocq_array::get::<u64>(&v141, v140);
              let tbl2 = rocq_array::set::<u64>(tbl1, v127, add(v145, d));
              let v157 = &ex;
              let ev = rocq_array::get::<u64>(&v157, v);
              let ex1 = rocq_array::set::<u64>(ex, cu, sub(e, d));
              let ex2 = rocq_array::set::<u64>(ex1, v, add(ev, d));
              let v212 = andb(eqb(ev, 0u64), negb(eqb(v, t)));
              let v227 = andb(v212, negb(eqb(v, s)));
              let b = andb(v227, ltb(ql, n));
              let q1 = match &b {
                true => {
                  rocq_array::set::<u64>(q, enq_pos(qh, ql, n), v)
                },
                false => {
                  q
                },
              };
              let ql1 = match &b {
                true => {
                  add(ql, 1u64)
                },
                false => {
                  ql
                },
              };
              let v282 = sub(e, d);
              let v284 = 0u64;
              let cu1 = match eqb(v282, v284) {
                true => {
                  n
                },
                false => {
                  cu
                },
              };
              mloop(n, s, t, tbl2, ex2, h, cur, cnt, q1, qh, ql1, cu1, rl, ())
            },
            sumbool::right => {
              let v344 = rocq_array::set::<u64>(cur, cu, add(v, 1u64));
              mloop(n, s, t, tbl, ex, h, v344, cnt, q, qh, ql, cu, rl, ())
            },
          }
        },
        sumbool::right => {
          let v382 = &h;
          let oh = rocq_array::get::<u64>(&v382, cu);
          let v391 = Rc::clone(&tbl);
          let v398 = Rc::clone(&h);
          let nh = rmin_1(v391, n, cu, v398, 0u64, n);
          let h1 = rocq_array::set::<u64>(h, cu, nh);
          let cur1 = rocq_array::set::<u64>(cur, cu, 0u64);
          let v421 = &cnt;
          let v424 = rocq_array::get::<u64>(&v421, oh);
          let co = sub(v424, 1u64);
          let cnt1 = rocq_array::set::<u64>(cnt, oh, co);
          let v440 = &cnt1;
          let v443 = rocq_array::get::<u64>(&v440, nh);
          let cnt2 = rocq_array::set::<u64>(cnt1, nh, add(v443, 1u64));
          let v481 = andb(eqb(co, 0u64), ltb(0u64, oh));
          let v492 = andb(v481, ltb(oh, n));
          let v498 = Rc::clone(&h1);
          let g = andb(v492, no_height_1(v498, n, oh, 0u64));
          let cnt3 = match &g {
            true => {
              let v518 = Rc::clone(&h1);
              cnt_lift_1(v518, cnt2, n, oh, 0u64)
            },
            false => {
              cnt2
            },
          };
          let h2 = match &g {
            true => {
              lift(h1, n, oh)
            },
            false => {
              h1
            },
          };
          let rl1 = add(rl, 1u64);
          let gl = leb(n, rl1);
          let h3 = match &gl {
            true => {
              let v567 = Rc::clone(&tbl);
              glob(v567, n, t, h2)
            },
            false => {
              h2
            },
          };
          let cur2 = match &gl {
            true => {
              std::mem::drop(cur1);
              rocq_array::make::<u64>(n, 0u64)
            },
            false => {
              cur1
            },
          };
          let cnt4 = match &gl {
            true => {
              std::mem::drop(cnt3);
              let v599 = Rc::clone(&h3);
              count(v599, n)
            },
            false => {
              cnt3
            },
          };
          let rl2 = match &gl {
            true => {
              0u64
            },
            false => {
              rl1
            },
          };
          let v618 = &h3;
          let v622 = rocq_array::get::<u64>(&v618, cu);
          let cu1 = match ltb(v622, n) {
            true => {
              cu
            },
            false => {
              n
            },
          };
          mloop(n, s, t, tbl, ex, h3, cur2, cnt4, q, qh, ql, cu1, rl2, ())
        },
      }
    },
    sumbool::right => {
      let v679 = ltb(0u64, ql);
      match bdec(v679) {
        sumbool::left => {
          let v683 = &q;
          let v = rocq_array::get::<u64>(&v683, qh);
          let v696 = add(qh, 1u64);
          let qh1 = match eqb(v696, n) {
            true => {
              0u64
            },
            false => {
              add(qh, 1u64)
            },
          };
          let v723 = ltb(v, n);
          let v727 = Rc::clone(&ex);
          let v730 = Rc::clone(&h);
          let v739 = active(v727, v730, n, s, t, v);
          let cu1 = match andb(v723, v739) {
            true => {
              v
            },
            false => {
              n
            },
          };
          mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh1, sub(ql, 1u64), cu1, rl, ())
        },
        sumbool::right => {
          let v798 = Rc::clone(&ex);
          let v801 = Rc::clone(&h);
          let v = find_act_1(v798, v801, n, s, t, 0u64);
          let v818 = ltb(v, n);
          match bdec(v818) {
            sumbool::left => {
              mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh, ql, v, rl, ())
            },
            sumbool::right => {
              std::mem::drop(tbl);
              std::mem::drop(h);
              std::mem::drop(cur);
              std::mem::drop(cnt);
              std::mem::drop(q);
              let v856 = &ex;
              let v859 = rocq_array::get::<u64>(&v856, t);
              std::mem::drop(ex);
              v859
            },
          }
        },
      }
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.s_tbl
pub fn s_tbl(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_tbl));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_ex
pub fn s_ex(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_ex));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_h
pub fn s_h(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_h));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_cur
pub fn s_cur(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_cur));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_cnt
pub fn s_cnt(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_cnt));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_q
pub fn s_q(s: Rc<st>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&s).s_q));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.s_qh
// Variant: borrowed
pub fn s_qh(s: &Rc<st>) -> u64 {
  let v1 = s;
  Clone::clone((&(&**v1).s_qh))
}

// Rocq: Mazemovement.mazemovement_implem.s_ql
// Variant: borrowed
pub fn s_ql(s: &Rc<st>) -> u64 {
  let v1 = s;
  Clone::clone((&(&**v1).s_ql))
}

// Rocq: Mazemovement.mazemovement_implem.s_cu
// Variant: borrowed
pub fn s_cu(s: &Rc<st>) -> u64 {
  let v1 = s;
  Clone::clone((&(&**v1).s_cu))
}

// Rocq: Mazemovement.mazemovement_implem.s_rl
pub fn s_rl(s: Rc<st>) -> u64 {
  let v3 = Clone::clone((&(&**&s).s_rl));
  std::mem::drop(s);
  v3
}

// Rocq: Mazemovement.mazemovement_implem.mazemovement_impl
pub fn mazemovement_impl(x: Rc<Array<u64>>) -> u64 {
  let v5 = Rc::clone(&x);
  let v7 = guard(v5);
  match bdec(v7) {
    sumbool::left => {
      let v14 = Rc::clone(&x);
      let S = init_state(v14);
      let v20 = Rc::clone(&x);
      let v21 = nn(v20);
      let v25 = Rc::clone(&x);
      let v26 = ss(v25);
      let v30 = tt(x);
      let v34 = Rc::clone(&S);
      let v35 = s_tbl(v34);
      let v39 = Rc::clone(&S);
      let v40 = s_ex(v39);
      let v44 = Rc::clone(&S);
      let v45 = s_h(v44);
      let v49 = Rc::clone(&S);
      let v50 = s_cur(v49);
      let v54 = Rc::clone(&S);
      let v55 = s_cnt(v54);
      let v59 = Rc::clone(&S);
      let v60 = s_q(v59);
      let v64 = s_qh(&S);
      let v68 = s_ql(&S);
      let v72 = s_cu(&S);
      mloop_1(v21, v26, v30, v35, v40, v45, v50, v55, v60, v64, v68, v72, s_rl(S))
    },
    sumbool::right => {
      std::mem::drop(x);
      0u64
    },
  }
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

pub fn run() -> Rc<dyn Fn(Rc<Array<u64>>) -> u64> {
  let v0: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = __rocq_global_1947.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1947: Rc<dyn Fn(Rc<Array<u64>>) -> u64> = mazemovement(); }