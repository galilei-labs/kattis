#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub type uint = u64;

pub type char63 = u64;

pub type sint = u64;

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bdec
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy
// Variant: uncurried
pub fn copy_1(a: Rc<Array<u64>>, b: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy(a, b, hi, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(a: Rc<Array<u64>>, b: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&a, k);
      let tmp_2 = rocq_array::set::<u64>(b, k, tmp_1);
      copy(a, tmp_2, hi, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(a);
      b
    },
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.merge
// Variant: uncurried
pub fn merge_1(le: Rc<dyn Fn(u64, u64) -> bool>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64) -> Rc<Array<u64>> {
  merge(le, src, dst, mid, hi, i, j, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.merge (local: merge)
// Variant: uncurried, lifted
pub fn merge(le: Rc<dyn Fn(u64, u64) -> bool>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, mid: u64, hi: u64, i: u64, j: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(i, mid);
      let tmp_2 = leb(hi, j);
      let tmp_3 = rocq_array::get::<u64>(&src, i);
      let tmp_4 = rocq_array::get::<u64>(&src, j);
      let le_ref: &Rc<dyn Fn(u64, u64) -> bool> = &le;
      let tmp_5 = le_ref(tmp_3, tmp_4);
      let tmp_6 = orb(tmp_2, tmp_5);
      if andb(tmp_1, tmp_6) {
        let tmp_7 = rocq_array::get::<u64>(&src, i);
        let tmp_8 = rocq_array::set::<u64>(dst, k, tmp_7);
        merge(le, src, tmp_8, mid, hi, add(i, 1u64), j, add(k, 1u64), ())
      } else {
        let tmp_9 = rocq_array::get::<u64>(&src, j);
        let tmp_10 = rocq_array::set::<u64>(dst, k, tmp_9);
        merge(le, src, tmp_10, mid, hi, i, add(j, 1u64), add(k, 1u64), ())
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.msort
// Variant: uncurried
pub fn msort_1(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(le, a, b, lo, hi, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(le: Rc<dyn Fn(u64, u64) -> bool>, a: Rc<Array<u64>>, b: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)));
  match bdec(tmp) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let le_clone: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
      let tmp_1 = msort(le_clone, a, b, lo, mid, ());
      match &tmp_1 {
        (b1, a1) => {
          let tmp_2 = ();
          let le_clone_1: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
          let b1_clone = Rc::clone(b1);
          let a1_clone = Rc::clone(a1);
          std::mem::drop(tmp_1);
          let tmp_3 = msort(le_clone_1, b1_clone, a1_clone, mid, hi, tmp_2);
          match tmp_3 {
            (v84, v86) => {
              let b2 = &v84;
              let b2_clone = Rc::clone(b2);
              let b3 = copy_1(b2_clone, v86, hi, lo);
              let b3_clone = Rc::clone(&b3);
              let tmp_4 = merge_1(le, b3_clone, v84, mid, hi, lo, mid, lo);
              (tmp_4, b3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(le);
      (a, b)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.r2
// Variant: borrowed, uncurried
pub fn r2(rk: &Rc<Array<u64>>, h: u64, n: u64, p: u64) -> u64 {
  let h_1 = h;
  let n_1 = n;
  let p_1 = p;
  let tmp = add(p_1, h_1);
  if ltb(tmp, n_1) {
    let tmp_1 = add(p_1, h_1);
    add(rocq_array::get::<u64>(rk, tmp_1), 1u64)
  } else {
    0u64
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.keyle
// Variant: borrowed, uncurried
pub fn keyle(rk: &Rc<Array<u64>>, h: u64, n: u64, p: u64, q: u64) -> bool {
  let h_1 = h;
  let n_1 = n;
  let p_1 = p;
  let q_1 = q;
  orb(ltb(rocq_array::get::<u64>(rk, p_1), rocq_array::get::<u64>(rk, q_1)), andb(eqb(rocq_array::get::<u64>(rk, p_1), rocq_array::get::<u64>(rk, q_1)), leb(r2(rk, h_1, n_1, p_1), r2(rk, h_1, n_1, q_1))))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(a: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  iota_loop(a, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(a: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::set::<u64>(a, i, i);
      iota_loop(tmp_1, n, add(i, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.sort_round
// Variant: uncurried
pub fn sort_round(rk: Rc<Array<u64>>, h: u64, n: u64) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    let __anf_capture_16 = n;
    move |v18: u64, v19: u64| -> bool {
      let rk = &rk;
      let h_clone = Clone::clone(&h);
      let tmp = Clone::clone(&__anf_capture_16);
      keyle(rk, h_clone, tmp, v18, v19)
    }
  });
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let tmp_2 = iota_loop_1(tmp_1, n, 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(callback, tmp_2, tmp_3, 0u64, n))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop
// Variant: uncurried
pub fn rank_loop_1(le: Rc<dyn Fn(u64, u64) -> bool>, sa: Rc<Array<u64>>, nr: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  rank_loop(le, sa, nr, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop (local: rank_loop)
// Variant: uncurried, lifted
pub fn rank_loop(le: Rc<dyn Fn(u64, u64) -> bool>, sa: Rc<Array<u64>>, nr: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let p = rocq_array::get::<u64>(&sa, i);
      let q = rocq_array::get::<u64>(&sa, sub(i, 1u64));
      let tmp_1 = rocq_array::get::<u64>(&nr, q);
      let le_ref: &Rc<dyn Fn(u64, u64) -> bool> = &le;
      let tmp_2 = le_ref(p, q);
      let tmp_3 = if tmp_2 {
        0u64
      } else {
        1u64
      };
      let tmp_4 = rocq_array::set::<u64>(nr, p, add(tmp_1, tmp_3));
      rank_loop(le, sa, tmp_4, n, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(le);
      std::mem::drop(sa);
      nr
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

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rounds
// Variant: uncurried
pub fn rounds_1(n: u64, rk: Rc<Array<u64>>, h: u64) -> Rc<Array<u64>> {
  rounds(n, rk, h, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rounds (local: rounds)
// Variant: uncurried, lifted
pub fn rounds(n: u64, rk: Rc<Array<u64>>, h: u64, _H: ()) -> Rc<Array<u64>> {
  let rk_clone = Rc::clone(&rk);
  let sa = sort_round(rk_clone, h, n);
  let rk_clone_1 = Rc::clone(&rk);
  let callback: Rc<dyn Fn(u64, u64) -> bool> = Rc::new({
    let __anf_capture_24 = h;
    let __anf_capture_26 = n;
    move |v28: u64, v29: u64| -> bool {
      let rk = &rk_clone_1;
      let tmp = Clone::clone(&__anf_capture_24);
      let tmp_1 = Clone::clone(&__anf_capture_26);
      keyle(rk, tmp, tmp_1, v28, v29)
    }
  });
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let sa_clone = Rc::clone(&sa);
  let nr = rank_loop_1(callback, sa_clone, tmp_2, n, 1u64);
  let tmp_3 = andb(ltb(0u64, h), ltb(h, n));
  let tmp_4 = sub(n, h);
  let tmp_5 = ltb(h, tmp_4);
  let tmp_6 = rocq_array::get::<u64>(&sa, sub(n, 1u64));
  let tmp_7 = rocq_array::get::<u64>(&nr, tmp_6);
  let tmp_8 = andb(tmp_5, negb(eqb(tmp_7, sub(n, 1u64))));
  let tmp_9 = andb(tmp_3, tmp_8);
  match bdec(tmp_9) {
    sumbool::left => {
      std::mem::drop(rk);
      std::mem::drop(sa);
      rounds(n, nr, add(h, h), ())
    },
    sumbool::right => {
      std::mem::drop(rk);
      std::mem::drop(nr);
      sa
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get_owned(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: borrowed, uncurried
pub fn get(v0: &Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  rocq_string::get(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.init_rk
// Variant: uncurried
pub fn init_rk_1(x: Rc<rocq_string::RocqString>, rk: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  init_rk(x, rk, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.init_rk (local: init_rk)
// Variant: uncurried, lifted
pub fn init_rk(x: Rc<rocq_string::RocqString>, rk: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      let tmp_1 = get_owned(x_clone, i);
      let tmp_2 = rocq_array::set::<u64>(rk, i, tmp_1);
      init_rk(x, tmp_2, n, add(i, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      rk
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build_sa
// Variant: uncurried
pub fn build_sa(x: Rc<rocq_string::RocqString>, n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let tmp_1 = init_rk_1(x, tmp, n, 0u64);
  rounds_1(n, tmp_1, 1u64)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.depth_loop
// Variant: uncurried
pub fn depth_loop_1(n: u64, d: u64) -> u64 {
  depth_loop(n, d, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.depth_loop (local: depth_loop)
// Variant: uncurried, lifted
pub fn depth_loop(n: u64, d: u64, _H: ()) -> u64 {
  let tmp = ltb(d, 20u64);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = lsl(1u64, d);
      if ltb(tmp_1, n) {
        depth_loop(n, add(d, 1u64), ())
      } else {
        d
      }
    },
    sumbool::right => {
      d
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.ins
// Variant: uncurried
pub fn ins_1(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, nx: u64, x: u64, d: u64, v: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  ins(L, R, C, nx, x, d, v, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.ins (local: ins)
// Variant: uncurried, lifted
pub fn ins(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, nx: u64, x: u64, d: u64, v: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(0u64, d);
  match bdec(tmp) {
    sumbool::left => {
      let half = lsl(1u64, sub(d, 1u64));
      let y = add(nx, d);
      if ltb(v, half) {
        let tmp_1 = rocq_array::get::<u64>(&L, x);
        let tmp_2 = ins(L, R, C, nx, tmp_1, sub(d, 1u64), v, ());
        match tmp_2 {
          (v84, v86) => {
            let p = &v86;
            match v84 {
              (v90, v92) => {
                let Lq = &v92;
                let tmp_3 = rocq_array::set::<u64>(v90, y, add(nx, sub(d, 1u64)));
                let tmp_4 = rocq_array::get::<u64>(Lq, x);
                let tmp_5 = rocq_array::set::<u64>(v92, y, tmp_4);
                let tmp_6 = (tmp_3, tmp_5);
                let tmp_7 = rocq_array::get::<u64>(p, x);
                let tmp_8 = rocq_array::set::<u64>(v86, y, add(tmp_7, 1u64));
                (tmp_6, tmp_8)
              },
            }
          },
        }
      } else {
        let tmp_9 = rocq_array::get::<u64>(&R, x);
        let tmp_10 = ins(L, R, C, nx, tmp_9, sub(d, 1u64), sub(v, half), ());
        match tmp_10 {
          (v203, v205) => {
            let p = &v205;
            match v203 {
              (v209, v211) => {
                let Rq = &v209;
                let tmp_11 = rocq_array::get::<u64>(Rq, x);
                let tmp_12 = rocq_array::set::<u64>(v209, y, tmp_11);
                let tmp_13 = rocq_array::set::<u64>(v211, y, add(nx, sub(d, 1u64)));
                let tmp_14 = (tmp_12, tmp_13);
                let tmp_15 = rocq_array::get::<u64>(p, x);
                let tmp_16 = rocq_array::set::<u64>(v205, y, add(tmp_15, 1u64));
                (tmp_14, tmp_16)
              },
            }
          },
        }
      }
    },
    sumbool::right => {
      let tmp_17 = (L, R);
      let tmp_18 = rocq_array::get::<u64>(&C, x);
      let tmp_19 = rocq_array::set::<u64>(C, nx, add(tmp_18, 1u64));
      (tmp_17, tmp_19)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build
// Variant: uncurried
pub fn build_1(sa: Rc<Array<u64>>, L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, roots: Rc<Array<u64>>, n: u64, D: u64, i: u64, nx: u64) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  build(sa, L, R, C, roots, n, D, i, nx, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(sa: Rc<Array<u64>>, L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, roots: Rc<Array<u64>>, n: u64, D: u64, i: u64, nx: u64, _H: ()) -> (((Rc<Array<u64>>, Rc<Array<u64>>), Rc<Array<u64>>), Rc<Array<u64>>) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&roots, i);
      let tmp_2 = rocq_array::get::<u64>(&sa, i);
      let tmp_3 = ins_1(L, R, C, nx, tmp_1, D, tmp_2);
      match tmp_3 {
        (v46, v48) => {
          match v46 {
            (v51, v53) => {
              let tmp_4 = rocq_array::set::<u64>(roots, add(i, 1u64), add(nx, D));
              let tmp_5 = add(i, 1u64);
              let tmp_6 = add(nx, D);
              build(sa, v51, v53, v48, tmp_4, n, D, tmp_5, add(tmp_6, 1u64), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(sa);
      (((L, R), C), roots)
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bs
// Variant: uncurried
pub fn bs_1(P: Rc<dyn Fn(u64) -> bool>, lo: u64, hi: u64) -> u64 {
  bs(P, lo, hi, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.bs (local: bs)
// Variant: uncurried, lifted
pub fn bs(P: Rc<dyn Fn(u64) -> bool>, lo: u64, hi: u64, _H: ()) -> u64 {
  let tmp = ltb(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let P_ref: &Rc<dyn Fn(u64) -> bool> = &P;
      let tmp_2 = P_ref(tmp_1);
      if tmp_2 {
        let tmp_3 = midp(lo, hi);
        bs(P, lo, tmp_3, ())
      } else {
        bs(P, add(midp(lo, hi), 1u64), hi, ())
      }
    },
    sumbool::right => {
      std::mem::drop(P);
      lo
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmpt
// Variant: borrowed, uncurried
pub fn cmpt_1(x: &Rc<rocq_string::RocqString>, t: &Rc<rocq_string::RocqString>, n: u64, m: u64, p: u64, k: u64) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let p_1 = p;
  let k_1 = k;
  cmpt(x, t, n_1, m_1, p_1, k_1, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmpt (local: cmpt)
// Variant: borrowed, uncurried, lifted
pub fn cmpt(x: &Rc<rocq_string::RocqString>, t: &Rc<rocq_string::RocqString>, n: u64, m: u64, p: u64, k: u64, _H: ()) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let p_1 = p;
  let k_1 = k;
  let tmp = ltb(k_1, m_1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(p_1, k_1);
      if ltb(tmp_1, n_1) {
        let a = get(t, k_1);
        let b = get(x, add(p_1, k_1));
        if ltb(a, b) {
          std::cmp::Ordering::Less
        } else {
          if ltb(b, a) {
            std::cmp::Ordering::Greater
          } else {
            cmpt(x, t, n_1, m_1, p_1, add(k_1, 1u64), ())
          }
        }
      } else {
        std::cmp::Ordering::Greater
      }
    },
    sumbool::right => {
      std::cmp::Ordering::Equal
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.cmp_at
// Variant: borrowed, uncurried
pub fn cmp_at(x: &Rc<rocq_string::RocqString>, t: &Rc<rocq_string::RocqString>, n: u64, m: u64, sa: &Rc<Array<u64>>, i: u64) -> std::cmp::Ordering {
  let n_1 = n;
  let m_1 = m;
  let i_1 = i;
  cmpt_1(x, t, n_1, m_1, rocq_array::get::<u64>(sa, i_1), 0u64)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry
// Variant: uncurried
pub fn qry_1(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, a: u64, b: u64, d: u64, k: u64) -> u64 {
  qry(L, R, C, a, b, d, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry (local: qry)
// Variant: uncurried, lifted
pub fn qry(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, a: u64, b: u64, d: u64, k: u64, _H: ()) -> u64 {
  let tmp = ltb(0u64, d);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&L, b);
      let tmp_2 = rocq_array::get::<u64>(&C, tmp_1);
      let tmp_3 = rocq_array::get::<u64>(&L, a);
      let tmp_4 = rocq_array::get::<u64>(&C, tmp_3);
      let cl = sub(tmp_2, tmp_4);
      if leb(k, cl) {
        let tmp_5 = rocq_array::get::<u64>(&L, a);
        let tmp_6 = rocq_array::get::<u64>(&L, b);
        qry(L, R, C, tmp_5, tmp_6, sub(d, 1u64), k, ())
      } else {
        let tmp_7 = lsl(1u64, sub(d, 1u64));
        let tmp_8 = rocq_array::get::<u64>(&R, a);
        let tmp_9 = rocq_array::get::<u64>(&R, b);
        add(tmp_7, qry(L, R, C, tmp_8, tmp_9, sub(d, 1u64), sub(k, cl), ()))
      }
    },
    sumbool::right => {
      std::mem::drop(L);
      std::mem::drop(R);
      std::mem::drop(C);
      0u64
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.answer1
// Variant: uncurried
pub fn answer1(x: Rc<rocq_string::RocqString>, n: u64, sa: Rc<Array<u64>>, L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, roots: Rc<Array<u64>>, D: u64, t: Rc<rocq_string::RocqString>, k: u64) -> u64 {
  let t_clone = Rc::clone(&t);
  let m = length(t_clone);
  let x_clone = Rc::clone(&x);
  let t_clone_1 = Rc::clone(&t);
  let sa_clone = Rc::clone(&sa);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_34 = n;
    let __anf_capture_36 = m;
    move |i: u64| -> bool {
      let x = &x_clone;
      let t = &t_clone_1;
      let n = &__anf_capture_34;
      let m = &__anf_capture_36;
      let sa = &sa_clone;
      let n_clone = Clone::clone(n);
      let m_clone = Clone::clone(m);
      match cmp_at(x, t, n_clone, m_clone, sa, i) {
        std::cmp::Ordering::Equal => {
          true
        },
        std::cmp::Ordering::Less => {
          true
        },
        std::cmp::Ordering::Greater => {
          false
        },
      }
    }
  });
  let lo = bs_1(callback, 0u64, n);
  let x_clone_1 = Rc::clone(&x);
  let t_clone_2 = Rc::clone(&t);
  let sa_clone_1 = Rc::clone(&sa);
  let callback_1: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_98 = n;
    let __anf_capture_100 = m;
    move |i: u64| -> bool {
      let x = &x_clone_1;
      let t = &t_clone_2;
      let n = &__anf_capture_98;
      let m = &__anf_capture_100;
      let sa = &sa_clone_1;
      let n_clone_1 = Clone::clone(n);
      let m_clone_1 = Clone::clone(m);
      match cmp_at(x, t, n_clone_1, m_clone_1, sa, i) {
        std::cmp::Ordering::Equal => {
          false
        },
        std::cmp::Ordering::Less => {
          true
        },
        std::cmp::Ordering::Greater => {
          false
        },
      }
    }
  });
  let hi = bs_1(callback_1, 0u64, n);
  let tmp = sub(hi, lo);
  if leb(k, tmp) {
    std::mem::drop(x);
    std::mem::drop(sa);
    std::mem::drop(t);
    let tmp_1 = rocq_array::get::<u64>(&roots, lo);
    let tmp_2 = rocq_array::get::<u64>(&roots, hi);
    std::mem::drop(roots);
    add(qry_1(L, R, C, tmp_1, tmp_2, D, k), 1u64)
  } else {
    std::mem::drop(x);
    std::mem::drop(sa);
    std::mem::drop(L);
    std::mem::drop(R);
    std::mem::drop(C);
    std::mem::drop(roots);
    std::mem::drop(t);
    sub(0u64, 1u64)
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qloop
// Variant: uncurried
pub fn qloop_1(x: Rc<rocq_string::RocqString>, n: u64, sa: Rc<Array<u64>>, L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, roots: Rc<Array<u64>>, D: u64, ts: Rc<Array<Rc<rocq_string::RocqString>>>, ks: Rc<Array<u64>>, out: Rc<Array<u64>>, q: u64, Q: u64) -> Rc<Array<u64>> {
  qloop(x, n, sa, L, R, C, roots, D, ts, ks, out, q, Q, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qloop (local: qloop)
// Variant: uncurried, lifted
pub fn qloop(x: Rc<rocq_string::RocqString>, n: u64, sa: Rc<Array<u64>>, L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, roots: Rc<Array<u64>>, D: u64, ts: Rc<Array<Rc<rocq_string::RocqString>>>, ks: Rc<Array<u64>>, out: Rc<Array<u64>>, q: u64, Q: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(q, Q);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&ts, q);
      let tmp_2 = rocq_array::get::<u64>(&ks, q);
      let x_clone = Rc::clone(&x);
      let sa_clone = Rc::clone(&sa);
      let L_clone = Rc::clone(&L);
      let R_clone = Rc::clone(&R);
      let C_clone = Rc::clone(&C);
      let roots_clone = Rc::clone(&roots);
      let tmp_3 = rocq_array::set::<u64>(out, q, answer1(x_clone, n, sa_clone, L_clone, R_clone, C_clone, roots_clone, D, tmp_1, tmp_2));
      qloop(x, n, sa, L, R, C, roots, D, ts, ks, tmp_3, add(q, 1u64), Q, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(sa);
      std::mem::drop(L);
      std::mem::drop(R);
      std::mem::drop(C);
      std::mem::drop(roots);
      std::mem::drop(ts);
      std::mem::drop(ks);
      out
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.kth_occurrences_impl
// Variant: uncurried
pub fn kth_occurrences_impl(x: Rc<rocq_string::RocqString>, ts: Rc<Array<Rc<rocq_string::RocqString>>>, ks: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let x_clone = Rc::clone(&x);
  let n = length(x_clone);
  let x_clone_1 = Rc::clone(&x);
  let sa = build_sa(x_clone_1, n);
  let D = depth_loop_1(n, 0u64);
  let tmp = add(D, 1u64);
  let M = add(mul(n, tmp), 1u64);
  let tmp_1 = rocq_array::make::<u64>(M, 0u64);
  let tmp_2 = rocq_array::make::<u64>(M, 0u64);
  let tmp_3 = rocq_array::make::<u64>(M, 0u64);
  let tmp_4 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let sa_clone = Rc::clone(&sa);
  let tmp_5 = build_1(sa_clone, tmp_1, tmp_2, tmp_3, tmp_4, n, D, 0u64, 1u64);
  match tmp_5 {
    (v107, v109) => {
      match v107 {
        (v112, v114) => {
          match v112 {
            (v117, v119) => {
              let Q = rocq_array::length::<Rc<rocq_string::RocqString>>(&ts);
              let tmp_6 = rocq_array::make::<u64>(Q, 0u64);
              qloop_1(x, n, sa, v117, v119, v114, v109, D, ts, ks, tmp_6, 0u64, Q)
            },
          }
        },
      }
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
