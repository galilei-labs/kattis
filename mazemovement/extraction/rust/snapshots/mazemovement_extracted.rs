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

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1: bool, b2: bool) -> bool {
  if b1 {
    b2
  } else {
    false
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Mazemovement.mazemovement_implem.nn
pub fn nn(x: Rc<Array<u64>>) -> u64 {
  let tmp = rocq_array::length::<u64>(&x);
  std::mem::drop(x);
  tmp
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
  if b {
    sumbool::left
  } else {
    sumbool::right
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&x, i);
      let tmp_2 = leb(2u64, tmp_1);
      let tmp_3 = rocq_array::get::<u64>(&x, i);
      let tmp_4 = leb(tmp_3, 2000000000u64);
      if andb(tmp_2, tmp_4) {
        rng_ok(x, n, add(i, 1u64), ())
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
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&x, i);
      let tmp_3 = rocq_array::get::<u64>(&x, best);
      let tmp_4 = if ltb(tmp_2, tmp_3) {
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
pub fn ss(x: Rc<Array<u64>>) -> u64 {
  let x_clone = Rc::clone(&x);
  amin_1(x, nn(x_clone), 1u64, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.amax
// Variant: uncurried
pub fn amax_1(x: Rc<Array<u64>>, n: u64, i: u64, best: u64) -> u64 {
  amax(x, n, i, best, ())
}

// Rocq: Mazemovement.mazemovement_implem.amax (local: amax)
// Variant: uncurried, lifted
pub fn amax(x: Rc<Array<u64>>, n: u64, i: u64, best: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&x, best);
      let tmp_3 = rocq_array::get::<u64>(&x, i);
      let tmp_4 = if ltb(tmp_2, tmp_3) {
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
pub fn tt(x: Rc<Array<u64>>) -> u64 {
  let x_clone = Rc::clone(&x);
  amax_1(x, nn(x_clone), 1u64, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.guard
pub fn guard(x: Rc<Array<u64>>) -> bool {
  let x_clone = Rc::clone(&x);
  let tmp = leb(2u64, nn(x_clone));
  let x_clone_1 = Rc::clone(&x);
  let tmp_1 = andb(tmp, leb(nn(x_clone_1), 1000u64));
  let x_clone_2 = Rc::clone(&x);
  let tmp_2 = nn(x_clone_2);
  let x_clone_3 = Rc::clone(&x);
  let tmp_3 = andb(tmp_1, rng_ok_1(x_clone_3, tmp_2, 0u64));
  let x_clone_4 = Rc::clone(&x);
  andb(tmp_3, negb(eqb(ss(x_clone_4), tt(x))))
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
  let tmp = eqb(b, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      a
    },
    sumbool::right => {
      let tmp_1 = mod_(a, b);
      gcd_loop(b, tmp_1, ())
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
  if eqb(i, j) {
    std::mem::drop(x);
    0u64
  } else {
    let tmp = rocq_array::get::<u64>(&x, i);
    let tmp_1 = rocq_array::get::<u64>(&x, j);
    let g = igcd(tmp, tmp_1);
    if ltb(1u64, g) {
      std::mem::drop(x);
      g
    } else {
      std::mem::drop(x);
      0u64
    }
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let c = capf(x_clone, i, j);
      let tmp_1 = rocq_array::set::<u64>(tbl, add(mul(i, n), j), c);
      let tmp_2 = rocq_array::set::<u64>(tmp_1, add(mul(j, n), i), c);
      fill_row(x, n, i, tmp_2, add(j, 1u64), ())
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let tmp_1 = fill_row_1(x_clone, n, i, tbl, i);
      fill_tab(x, n, tmp_1, add(i, 1u64), ())
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
  let tmp = ltb(v, n);
  match bdec(tmp) {
    sumbool::left => {
      let c = rocq_array::get::<u64>(&tbl, add(mul(s, n), v));
      let tbl1 = rocq_array::set::<u64>(tbl, add(mul(s, n), v), 0u64);
      let tmp_1 = add(mul(v, n), s);
      let tmp_2 = rocq_array::get::<u64>(&tbl1, add(mul(v, n), s));
      let tbl2 = rocq_array::set::<u64>(tbl1, tmp_1, add(tmp_2, c));
      let ex1 = rocq_array::set::<u64>(ex, v, c);
      let tmp_3 = andb(ltb(0u64, c), negb(eqb(v, t)));
      let b = andb(tmp_3, negb(eqb(v, s)));
      let q1 = if b {
        rocq_array::set::<u64>(q, ql, v)
      } else {
        q
      };
      let ql1 = if b {
        add(ql, 1u64)
      } else {
        ql
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&d, j);
      if eqb(tmp_1, L) {
        std::mem::drop(d);
        true
      } else {
        has_val(d, n, L, add(j, 1u64), ())
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
  let tmp = ltb(i, m);
  match bdec(tmp) {
    sumbool::left => {
      let o = rocq_array::get::<u64>(&a, i);
      let F_ref: &Rc<dyn Fn(u64, u64) -> u64> = &F;
      let w = F_ref(i, o);
      let tmp_1 = if eqb(w, o) {
        a
      } else {
        rocq_array::set::<u64>(a, i, w)
      };
      amap(F, tmp_1, add(i, 1u64), m, ())
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
  let tmp = ltb(0u64, rocq_array::get::<u64>(tbl, add(mul(a_1, n_1), b_1)));
  let tmp_1 = ltb(L1_1, o_1);
  if andb(tmp, tmp_1) {
    L1_1
  } else {
    o_1
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
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&d, j);
      let tmp_2 = if eqb(tmp_1, L) {
        let tmp_3 = add(L, 1u64);
        let tbl_clone = Rc::clone(&tbl);
        let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
          let __anf_capture_49 = n;
          let __anf_capture_51 = j;
          move |v55: u64, v56: u64| -> u64 {
            let tbl = &tbl_clone;
            let tmp_4 = Clone::clone(&__anf_capture_49);
            let tmp_5 = Clone::clone(&__anf_capture_51);
            let tmp_6 = Clone::clone(&tmp_3);
            relaxF(tbl, tmp_4, tmp_5, tmp_6, v55, v56)
          }
        });
        amap_1(callback, d, 0u64, n)
      } else {
        d
      };
      lscan(tbl, n, L, tmp_2, add(j, 1u64), ())
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
  let tmp = ltb(L, n);
  match bdec(tmp) {
    sumbool::left => {
      let d_clone = Rc::clone(&d);
      if has_val_1(d_clone, n, L, 0u64) {
        let tmp_1 = add(L, 1u64);
        let tbl_clone = Rc::clone(&tbl);
        let tmp_2 = lscan_1(tbl_clone, n, L, d, 0u64);
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
pub fn bfs(tbl: Rc<Array<u64>>, n: u64, t: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, n);
  let tmp_1 = rocq_array::set::<u64>(tmp, t, 0u64);
  layers_1(tbl, n, 0u64, tmp_1)
}

// Rocq: Mazemovement.mazemovement_implem.maxF
// Variant: borrowed, uncurried
pub fn maxF(d: &Rc<Array<u64>>, y: u64, o: u64) -> u64 {
  let y_1 = y;
  let o_1 = o;
  let tmp = rocq_array::get::<u64>(d, y_1);
  if ltb(o_1, tmp) {
    rocq_array::get::<u64>(d, y_1)
  } else {
    o_1
  }
}

// Rocq: Mazemovement.mazemovement_implem.glob
// Variant: uncurried
pub fn glob(tbl: Rc<Array<u64>>, n: u64, t: u64, h: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let d = bfs(tbl, n, t);
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    move |v18: u64, v19: u64| -> u64 {
      maxF(&d, v18, v19)
    }
  });
  amap_1(callback, h, 0u64, n)
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
pub fn cntl_1(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  cntl(h, cnt, n, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.cntl (local: cntl)
// Variant: uncurried, lifted
pub fn cntl(h: Rc<Array<u64>>, cnt: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let k = rocq_array::get::<u64>(&h, i);
      let tmp_1 = rocq_array::get::<u64>(&cnt, k);
      let tmp_2 = rocq_array::set::<u64>(cnt, k, add(tmp_1, 1u64));
      cntl(h, tmp_2, n, add(i, 1u64), ())
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
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  cntl_1(h, tmp, n, 0u64)
}

// Rocq: Mazemovement.mazemovement_implem.init_state
pub fn init_state(x: Rc<Array<u64>>) -> Rc<st> {
  let x_clone = Rc::clone(&x);
  let n = nn(x_clone);
  let x_clone_1 = Rc::clone(&x);
  let s = ss(x_clone_1);
  let x_clone_2 = Rc::clone(&x);
  let t = tt(x_clone_2);
  let tmp = rocq_array::make::<u64>(mul(n, n), 0u64);
  let tbl0 = fill_tab_1(x, n, tmp, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let p = sat_1(n, s, t, tbl0, tmp_1, tmp_2, 0u64, 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let h0 = rocq_array::set::<u64>(tmp_3, s, n);
  let p_clone = Clone::clone(&p);
  let tmp_4 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p_clone)));
  let h1 = glob(tmp_4, n, t, h0);
  let p_clone_1 = Clone::clone(&p);
  let tmp_5 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p_clone_1)));
  let p_clone_2 = Clone::clone(&p);
  let tmp_6 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p_clone_2)));
  let tmp_7 = rocq_array::make::<u64>(n, 0u64);
  let h1_clone = Rc::clone(&h1);
  let tmp_8 = count(h1_clone, n);
  let p_clone_3 = Clone::clone(&p);
  let tmp_9 = snd::<(Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>>(fst::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p_clone_3));
  Rc::new(st { s_tbl: tmp_5, s_ex: tmp_6, s_h: h1, s_cur: tmp_7, s_cnt: tmp_8, s_q: tmp_9, s_qh: 0u64, s_ql: snd::<((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), u64>(p), s_cu: n, s_rl: 0u64 })
}

// Rocq: Mazemovement.mazemovement_implem.adm
// Variant: uncurried
pub fn adm(tbl: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, u: u64, v: u64) -> bool {
  let tmp = 0u64;
  let tmp_1 = rocq_array::get::<u64>(&tbl, add(mul(u, n), v));
  std::mem::drop(tbl);
  let tmp_2 = ltb(tmp, tmp_1);
  let tmp_3 = rocq_array::get::<u64>(&h, u);
  let tmp_4 = rocq_array::get::<u64>(&h, v);
  std::mem::drop(h);
  andb(tmp_2, eqb(tmp_3, add(tmp_4, 1u64)))
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
  if ltb(p, n) {
    p
  } else {
    sub(p, n)
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
  let tmp = ltb(b, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(b, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&tbl, add(mul(u, n), b));
      let tmp_3 = ltb(0u64, tmp_2);
      let tmp_4 = rocq_array::get::<u64>(&h, b);
      let tmp_5 = ltb(add(tmp_4, 1u64), acc);
      let tmp_6 = if andb(tmp_3, tmp_5) {
        let tmp_7 = rocq_array::get::<u64>(&h, b);
        add(tmp_7, 1u64)
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
pub fn no_height_1(h: Rc<Array<u64>>, n: u64, k: u64, i: u64) -> bool {
  no_height(h, n, k, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.no_height (local: no_height)
// Variant: uncurried, lifted
pub fn no_height(h: Rc<Array<u64>>, n: u64, k: u64, i: u64, _H: ()) -> bool {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&h, i);
      if eqb(tmp_1, k) {
        std::mem::drop(h);
        false
      } else {
        no_height(h, n, k, add(i, 1u64), ())
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
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let o = rocq_array::get::<u64>(&h, i);
      let tmp_1 = ltb(k, o);
      let tmp_2 = ltb(o, n);
      let tmp_3 = if andb(tmp_1, tmp_2) {
        let tmp_4 = rocq_array::get::<u64>(&cnt, o);
        rocq_array::set::<u64>(cnt, o, sub(tmp_4, 1u64))
      } else {
        cnt
      };
      cnt_lift(h, tmp_3, n, k, add(i, 1u64), ())
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
  let tmp = ltb(k, o);
  let tmp_1 = ltb(o, n);
  if andb(tmp, tmp_1) {
    n
  } else {
    o
  }
}

// Rocq: Mazemovement.mazemovement_implem.lift
// Variant: uncurried
pub fn lift(h: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, u64) -> u64> = Rc::new({
    let __anf_capture_9 = n;
    move |v13: u64, v14: u64| -> u64 {
      let tmp = Clone::clone(&__anf_capture_9);
      let k_clone = Clone::clone(&k);
      liftF(tmp, k_clone, v13, v14)
    }
  });
  amap_1(callback, h, 0u64, n)
}

// Rocq: Mazemovement.mazemovement_implem.active
// Variant: uncurried
pub fn active(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, v: u64) -> bool {
  let tmp = 0u64;
  let tmp_1 = rocq_array::get::<u64>(&ex, v);
  std::mem::drop(ex);
  let tmp_2 = ltb(tmp, tmp_1);
  let tmp_3 = rocq_array::get::<u64>(&h, v);
  std::mem::drop(h);
  let tmp_4 = andb(tmp_2, ltb(tmp_3, n));
  let tmp_5 = andb(tmp_4, negb(eqb(v, s)));
  andb(tmp_5, negb(eqb(v, t)))
}

// Rocq: Mazemovement.mazemovement_implem.find_act
// Variant: uncurried
pub fn find_act_1(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, i: u64) -> u64 {
  find_act(ex, h, n, s, t, i, ())
}

// Rocq: Mazemovement.mazemovement_implem.find_act (local: find_act)
// Variant: uncurried, lifted
pub fn find_act(ex: Rc<Array<u64>>, h: Rc<Array<u64>>, n: u64, s: u64, t: u64, i: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let ex_clone = Rc::clone(&ex);
      let h_clone = Rc::clone(&h);
      if active(ex_clone, h_clone, n, s, t, i) {
        std::mem::drop(ex);
        std::mem::drop(h);
        i
      } else {
        find_act(ex, h, n, s, t, add(i, 1u64), ())
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
  let tmp = ltb(cu, n);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&cur, cu);
      let tmp_1 = ltb(v, n);
      match bdec(tmp_1) {
        sumbool::left => {
          let tbl_clone = Rc::clone(&tbl);
          let h_clone = Rc::clone(&h);
          let tmp_2 = adm(tbl_clone, h_clone, n, cu, v);
          match bdec(tmp_2) {
            sumbool::left => {
              let r = rocq_array::get::<u64>(&tbl, add(mul(cu, n), v));
              let e = rocq_array::get::<u64>(&ex, cu);
              let d = if ltb(e, r) {
                e
              } else {
                r
              };
              let tbl1 = rocq_array::set::<u64>(tbl, add(mul(cu, n), v), sub(r, d));
              let tmp_3 = add(mul(v, n), cu);
              let tmp_4 = rocq_array::get::<u64>(&tbl1, add(mul(v, n), cu));
              let tbl2 = rocq_array::set::<u64>(tbl1, tmp_3, add(tmp_4, d));
              let ev = rocq_array::get::<u64>(&ex, v);
              let ex1 = rocq_array::set::<u64>(ex, cu, sub(e, d));
              let ex2 = rocq_array::set::<u64>(ex1, v, add(ev, d));
              let tmp_5 = andb(eqb(ev, 0u64), negb(eqb(v, t)));
              let tmp_6 = andb(tmp_5, negb(eqb(v, s)));
              let b = andb(tmp_6, ltb(ql, n));
              let q1 = if b {
                rocq_array::set::<u64>(q, enq_pos(qh, ql, n), v)
              } else {
                q
              };
              let ql1 = if b {
                add(ql, 1u64)
              } else {
                ql
              };
              let tmp_7 = sub(e, d);
              let tmp_8 = 0u64;
              let cu1 = if eqb(tmp_7, tmp_8) {
                n
              } else {
                cu
              };
              mloop(n, s, t, tbl2, ex2, h, cur, cnt, q1, qh, ql1, cu1, rl, ())
            },
            sumbool::right => {
              let tmp_9 = rocq_array::set::<u64>(cur, cu, add(v, 1u64));
              mloop(n, s, t, tbl, ex, h, tmp_9, cnt, q, qh, ql, cu, rl, ())
            },
          }
        },
        sumbool::right => {
          let oh = rocq_array::get::<u64>(&h, cu);
          let tbl_clone_1 = Rc::clone(&tbl);
          let h_clone_1 = Rc::clone(&h);
          let nh = rmin_1(tbl_clone_1, n, cu, h_clone_1, 0u64, n);
          let h1 = rocq_array::set::<u64>(h, cu, nh);
          let cur1 = rocq_array::set::<u64>(cur, cu, 0u64);
          let tmp_10 = rocq_array::get::<u64>(&cnt, oh);
          let co = sub(tmp_10, 1u64);
          let cnt1 = rocq_array::set::<u64>(cnt, oh, co);
          let tmp_11 = rocq_array::get::<u64>(&cnt1, nh);
          let cnt2 = rocq_array::set::<u64>(cnt1, nh, add(tmp_11, 1u64));
          let tmp_12 = andb(eqb(co, 0u64), ltb(0u64, oh));
          let tmp_13 = andb(tmp_12, ltb(oh, n));
          let h1_clone = Rc::clone(&h1);
          let g = andb(tmp_13, no_height_1(h1_clone, n, oh, 0u64));
          let cnt3 = if g {
            let h1_clone_1 = Rc::clone(&h1);
            cnt_lift_1(h1_clone_1, cnt2, n, oh, 0u64)
          } else {
            cnt2
          };
          let h2 = if g {
            lift(h1, n, oh)
          } else {
            h1
          };
          let rl1 = add(rl, 1u64);
          let gl = leb(n, rl1);
          let h3 = if gl {
            let tbl_clone_2 = Rc::clone(&tbl);
            glob(tbl_clone_2, n, t, h2)
          } else {
            h2
          };
          let cur2 = if gl {
            std::mem::drop(cur1);
            rocq_array::make::<u64>(n, 0u64)
          } else {
            cur1
          };
          let cnt4 = if gl {
            std::mem::drop(cnt3);
            let h3_clone = Rc::clone(&h3);
            count(h3_clone, n)
          } else {
            cnt3
          };
          let rl2 = if gl {
            0u64
          } else {
            rl1
          };
          let tmp_14 = rocq_array::get::<u64>(&h3, cu);
          let cu1 = if ltb(tmp_14, n) {
            cu
          } else {
            n
          };
          mloop(n, s, t, tbl, ex, h3, cur2, cnt4, q, qh, ql, cu1, rl2, ())
        },
      }
    },
    sumbool::right => {
      let tmp_15 = ltb(0u64, ql);
      match bdec(tmp_15) {
        sumbool::left => {
          let v = rocq_array::get::<u64>(&q, qh);
          let tmp_16 = add(qh, 1u64);
          let qh1 = if eqb(tmp_16, n) {
            0u64
          } else {
            add(qh, 1u64)
          };
          let tmp_17 = ltb(v, n);
          let ex_clone = Rc::clone(&ex);
          let h_clone_2 = Rc::clone(&h);
          let tmp_18 = active(ex_clone, h_clone_2, n, s, t, v);
          let cu1 = if andb(tmp_17, tmp_18) {
            v
          } else {
            n
          };
          mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh1, sub(ql, 1u64), cu1, rl, ())
        },
        sumbool::right => {
          let ex_clone_1 = Rc::clone(&ex);
          let h_clone_3 = Rc::clone(&h);
          let v = find_act_1(ex_clone_1, h_clone_3, n, s, t, 0u64);
          let tmp_19 = ltb(v, n);
          match bdec(tmp_19) {
            sumbool::left => {
              mloop(n, s, t, tbl, ex, h, cur, cnt, q, qh, ql, v, rl, ())
            },
            sumbool::right => {
              std::mem::drop(tbl);
              std::mem::drop(h);
              std::mem::drop(cur);
              std::mem::drop(cnt);
              std::mem::drop(q);
              let tmp_20 = rocq_array::get::<u64>(&ex, t);
              std::mem::drop(ex);
              tmp_20
            },
          }
        },
      }
    },
  }
}

// Rocq: Mazemovement.mazemovement_implem.s_tbl
pub fn s_tbl(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_tbl_clone = Rc::clone(&s.s_tbl);
  std::mem::drop(s);
  s_s_tbl_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_ex
pub fn s_ex(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_ex_clone = Rc::clone(&s.s_ex);
  std::mem::drop(s);
  s_s_ex_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_h
pub fn s_h(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_h_clone = Rc::clone(&s.s_h);
  std::mem::drop(s);
  s_s_h_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_cur
pub fn s_cur(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_cur_clone = Rc::clone(&s.s_cur);
  std::mem::drop(s);
  s_s_cur_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_cnt
pub fn s_cnt(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_cnt_clone = Rc::clone(&s.s_cnt);
  std::mem::drop(s);
  s_s_cnt_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_q
pub fn s_q(s: Rc<st>) -> Rc<Array<u64>> {
  let s_s_q_clone = Rc::clone(&s.s_q);
  std::mem::drop(s);
  s_s_q_clone
}

// Rocq: Mazemovement.mazemovement_implem.s_qh
// Variant: borrowed
pub fn s_qh(s: &Rc<st>) -> u64 {
  let tmp = s;
  Clone::clone(&tmp.s_qh)
}

// Rocq: Mazemovement.mazemovement_implem.s_ql
// Variant: borrowed
pub fn s_ql(s: &Rc<st>) -> u64 {
  let tmp = s;
  Clone::clone(&tmp.s_ql)
}

// Rocq: Mazemovement.mazemovement_implem.s_cu
// Variant: borrowed
pub fn s_cu(s: &Rc<st>) -> u64 {
  let tmp = s;
  Clone::clone(&tmp.s_cu)
}

// Rocq: Mazemovement.mazemovement_implem.s_rl
pub fn s_rl(s: Rc<st>) -> u64 {
  let s_s_rl_clone = Clone::clone(&s.s_rl);
  std::mem::drop(s);
  s_s_rl_clone
}

// Rocq: Mazemovement.mazemovement_implem.mazemovement_impl
pub fn mazemovement_impl(x: Rc<Array<u64>>) -> u64 {
  let x_clone = Rc::clone(&x);
  let tmp = guard(x_clone);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone_1 = Rc::clone(&x);
      let S = init_state(x_clone_1);
      let x_clone_2 = Rc::clone(&x);
      let tmp_1 = nn(x_clone_2);
      let x_clone_3 = Rc::clone(&x);
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
