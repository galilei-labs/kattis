// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.kth_occurrences
// Variant: uncurried
pub fn kth_occurrences() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>> = kth_occurrences_impl;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.kth_occurrences
pub fn kth_occurrences_curried() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> {
  let v0: fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = kth_occurrences_impl_curried;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let v9 = sub(hi, lo);
  add(lo, div(v9, 2u64))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy
// Variant: uncurried
pub fn copy_1(a: Rc<Array<u64>>, b: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy(a, b, hi, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.copy (local: copy)
// Variant: uncurried, lifted
pub fn copy(a: Rc<Array<u64>>, b: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(k, hi);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &a;
      let v19 = rocq_array::get::<u64>(&v16, k);
      let v26 = rocq_array::set::<u64>(b, k, v19);
      copy(a, v26, hi, add(k, 1u64), ())
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
  match b1 {
    true => {
      true
    },
    false => {
      b2
    },
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
  let v16 = ltb(k, hi);
  match bdec(v16) {
    sumbool::left => {
      let v26 = ltb(i, mid);
      let v33 = leb(hi, j);
      let v34 = &src;
      let v37 = rocq_array::get::<u64>(&v34, i);
      let v38 = &src;
      let v41 = rocq_array::get::<u64>(&v38, j);
      let v42: &Rc<dyn Fn(u64, u64) -> bool> = &le;
      let v47 = v42(v37, v41);
      let v52 = orb(v33, v47);
      match andb(v26, v52) {
        true => {
          let v59 = &src;
          let v62 = rocq_array::get::<u64>(&v59, i);
          let v69 = rocq_array::set::<u64>(dst, k, v62);
          merge(le, src, v69, mid, hi, add(i, 1u64), j, add(k, 1u64), ())
        },
        false => {
          let v110 = &src;
          let v113 = rocq_array::get::<u64>(&v110, j);
          let v120 = rocq_array::set::<u64>(dst, k, v113);
          merge(le, src, v120, mid, hi, i, add(j, 1u64), add(k, 1u64), ())
        },
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
  let v33 = andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)));
  match bdec(v33) {
    sumbool::left => {
      let mid = midp(lo, hi);
      let v47: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
      let v59 = msort(v47, a, b, lo, mid, ());
      match &v59 {
        (b1, a1) => {
          let v67 = ();
          let v70: Rc<dyn Fn(u64, u64) -> bool> = Rc::clone(&le);
          let v73 = Rc::clone(b1);
          let v74 = Rc::clone(a1);
          std::mem::drop(v59);
          let v82 = msort(v70, v73, v74, mid, hi, v67);
          match v82 {
            (v84, v86) => {
              let b2 = &v84;
              let v91 = Rc::clone(b2);
              let b3 = copy_1(v91, v86, hi, lo);
              let v104 = Rc::clone(&b3);
              let v118 = merge_1(le, v104, v84, mid, hi, lo, mid, lo);
              (v118, b3)
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
  let v14 = add(p_1, h_1);
  match ltb(v14, n_1) {
    true => {
      let v26 = add(p_1, h_1);
      let v27 = rk;
      add(rocq_array::get::<u64>(&v27, v26), 1u64)
    },
    false => {
      0u64
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.keyle
// Variant: borrowed, uncurried
pub fn keyle(rk: &Rc<Array<u64>>, h: u64, n: u64, p: u64, q: u64) -> bool {
  let h_1 = h;
  let n_1 = n;
  let p_1 = p;
  let q_1 = q;
  let v11 = rk;
  let v14 = rocq_array::get::<u64>(&v11, p_1);
  let v15 = rk;
  let v23 = ltb(v14, rocq_array::get::<u64>(&v15, q_1));
  let v26 = rk;
  let v29 = rocq_array::get::<u64>(&v26, p_1);
  let v30 = rk;
  orb(v23, andb(eqb(v29, rocq_array::get::<u64>(&v30, q_1)), leb(r2(rk, h_1, n_1, p_1), r2(rk, h_1, n_1, q_1))))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(a: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  iota_loop(a, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(a: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(i, n);
  match bdec(v11) {
    sumbool::left => {
      let v21 = rocq_array::set::<u64>(a, i, i);
      iota_loop(v21, n, add(i, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.sort_round
// Variant: uncurried
pub fn sort_round(rk: Rc<Array<u64>>, h: u64, n: u64) -> Rc<Array<u64>> {
  let v11 = {
    let __anf_capture_16 = n;
    move |v18: u64, v19: u64| -> bool {
      let rk = &rk;
      let v21 = Clone::clone(&h);
      let v23 = Clone::clone(&__anf_capture_16);
      keyle(rk, v21, v23, v18, v19)
    }
  };
  let v33: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v11);
  let v42 = rocq_array::make::<u64>(n, 0u64);
  let v51 = iota_loop_1(v42, n, 0u64);
  let v58 = rocq_array::make::<u64>(n, 0u64);
  fst::<Rc<Array<u64>>, Rc<Array<u64>>>(msort_1(v33, v51, v58, 0u64, n))
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop
// Variant: uncurried
pub fn rank_loop_1(le: Rc<dyn Fn(u64, u64) -> bool>, sa: Rc<Array<u64>>, nr: Rc<Array<u64>>, n: u64, i: u64) -> Rc<Array<u64>> {
  rank_loop(le, sa, nr, n, i, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.rank_loop (local: rank_loop)
// Variant: uncurried, lifted
pub fn rank_loop(le: Rc<dyn Fn(u64, u64) -> bool>, sa: Rc<Array<u64>>, nr: Rc<Array<u64>>, n: u64, i: u64, _H: ()) -> Rc<Array<u64>> {
  let v13 = ltb(i, n);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &sa;
      let p = rocq_array::get::<u64>(&v17, i);
      let v28 = sub(i, 1u64);
      let v29 = &sa;
      let q = rocq_array::get::<u64>(&v29, v28);
      let v34 = &nr;
      let v37 = rocq_array::get::<u64>(&v34, q);
      let v38: &Rc<dyn Fn(u64, u64) -> bool> = &le;
      let v43 = v38(p, q);
      let v44 = match v43 {
        true => {
          0u64
        },
        false => {
          1u64
        },
      };
      let v65 = rocq_array::set::<u64>(nr, p, add(v37, v44));
      rank_loop(le, sa, v65, n, add(i, 1u64), ())
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
  match b {
    true => {
      false
    },
    false => {
      true
    },
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
  let v7 = Rc::clone(&rk);
  let sa = sort_round(v7, h, n);
  let v16 = Rc::clone(&rk);
  let v21 = {
    let __anf_capture_24 = h;
    let __anf_capture_26 = n;
    move |v28: u64, v29: u64| -> bool {
      let rk = &v16;
      let v31 = Clone::clone(&__anf_capture_24);
      let v33 = Clone::clone(&__anf_capture_26);
      keyle(rk, v31, v33, v28, v29)
    }
  };
  let v43: Rc<dyn Fn(u64, u64) -> bool> = Rc::new(v21);
  let v51 = rocq_array::make::<u64>(n, 0u64);
  let v58 = Rc::clone(&sa);
  let nr = rank_loop_1(v43, v58, v51, n, 1u64);
  let v87 = andb(ltb(0u64, h), ltb(h, n));
  let v95 = sub(n, h);
  let v100 = ltb(h, v95);
  let v110 = sub(n, 1u64);
  let v111 = &sa;
  let v114 = rocq_array::get::<u64>(&v111, v110);
  let v115 = &nr;
  let v118 = rocq_array::get::<u64>(&v115, v114);
  let v139 = andb(v100, negb(eqb(v118, sub(n, 1u64))));
  let v145 = andb(v87, v139);
  match bdec(v145) {
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
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
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
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v19 = Rc::clone(&x);
      let v22 = get_owned(v19, i);
      let v29 = rocq_array::set::<u64>(rk, i, v22);
      init_rk(x, v29, n, add(i, 1u64), ())
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
  let v10 = rocq_array::make::<u64>(n, 0u64);
  let v21 = init_rk_1(x, v10, n, 0u64);
  rounds_1(n, v21, 1u64)
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
  let v12 = ltb(d, 20u64);
  match bdec(v12) {
    sumbool::left => {
      let v25 = lsl(1u64, d);
      match ltb(v25, n) {
        true => {
          depth_loop(n, add(d, 1u64), ())
        },
        false => {
          d
        },
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
  let v17 = ltb(0u64, d);
  match bdec(v17) {
    sumbool::left => {
      let half = lsl(1u64, sub(d, 1u64));
      let y = add(nx, d);
      let v48 = ltb(v, half);
      match &v48 {
        true => {
          let v51 = &L;
          let v54 = rocq_array::get::<u64>(&v51, x);
          let v82 = ins(L, R, C, nx, v54, sub(d, 1u64), v, ());
          match v82 {
            (v84, v86) => {
              let p = &v86;
              match v84 {
                (v90, v92) => {
                  let Lq = &v92;
                  let v115 = rocq_array::set::<u64>(v90, y, add(nx, sub(d, 1u64)));
                  let v118 = rocq_array::get::<u64>(&Lq, x);
                  let v125 = rocq_array::set::<u64>(v92, y, v118);
                  let v131 = (v115, v125);
                  let v135 = rocq_array::get::<u64>(&p, x);
                  let v149 = rocq_array::set::<u64>(v86, y, add(v135, 1u64));
                  (v131, v149)
                },
              }
            },
          }
        },
        false => {
          let v164 = &R;
          let v167 = rocq_array::get::<u64>(&v164, x);
          let v201 = ins(L, R, C, nx, v167, sub(d, 1u64), sub(v, half), ());
          match v201 {
            (v203, v205) => {
              let p = &v205;
              match v203 {
                (v209, v211) => {
                  let Rq = &v209;
                  let v216 = rocq_array::get::<u64>(&Rq, x);
                  let v223 = rocq_array::set::<u64>(v209, y, v216);
                  let v244 = rocq_array::set::<u64>(v211, y, add(nx, sub(d, 1u64)));
                  let v250 = (v223, v244);
                  let v254 = rocq_array::get::<u64>(&p, x);
                  let v268 = rocq_array::set::<u64>(v205, y, add(v254, 1u64));
                  (v250, v268)
                },
              }
            },
          }
        },
      }
    },
    sumbool::right => {
      let v291 = (L, R);
      let v293 = &C;
      let v296 = rocq_array::get::<u64>(&v293, x);
      let v310 = rocq_array::set::<u64>(C, nx, add(v296, 1u64));
      (v291, v310)
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
  let v17 = ltb(i, n);
  match bdec(v17) {
    sumbool::left => {
      let v22 = &roots;
      let v25 = rocq_array::get::<u64>(&v22, i);
      let v26 = &sa;
      let v29 = rocq_array::get::<u64>(&v26, i);
      let v44 = ins_1(L, R, C, nx, v25, D, v29);
      match v44 {
        (v46, v48) => {
          match v46 {
            (v51, v53) => {
              let v75 = rocq_array::set::<u64>(roots, add(i, 1u64), add(nx, D));
              let v83 = add(i, 1u64);
              let v90 = add(nx, D);
              build(sa, v51, v53, v48, v75, n, D, v83, add(v90, 1u64), ())
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
  let v11 = ltb(lo, hi);
  match bdec(v11) {
    sumbool::left => {
      let v20 = midp(lo, hi);
      let v21: &Rc<dyn Fn(u64) -> bool> = &P;
      let v24 = v21(v20);
      match v24 {
        true => {
          let v31 = midp(lo, hi);
          bs(P, lo, v31, ())
        },
        false => {
          bs(P, add(midp(lo, hi), 1u64), hi, ())
        },
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
  let v18 = ltb(k_1, m_1);
  match bdec(v18) {
    sumbool::left => {
      let v29 = add(p_1, k_1);
      match ltb(v29, n_1) {
        true => {
          let a = get(t, k_1);
          let b = get(x, add(p_1, k_1));
          match ltb(a, b) {
            true => {
              std::cmp::Ordering::Less
            },
            false => {
              match ltb(b, a) {
                true => {
                  std::cmp::Ordering::Greater
                },
                false => {
                  cmpt(x, t, n_1, m_1, p_1, add(k_1, 1u64), ())
                },
              }
            },
          }
        },
        false => {
          std::cmp::Ordering::Greater
        },
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
  let v9 = sa;
  cmpt_1(x, t, n_1, m_1, rocq_array::get::<u64>(&v9, i_1), 0u64)
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry
// Variant: uncurried
pub fn qry_1(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, a: u64, b: u64, d: u64, k: u64) -> u64 {
  qry(L, R, C, a, b, d, k, ())
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.qry (local: qry)
// Variant: uncurried, lifted
pub fn qry(L: Rc<Array<u64>>, R: Rc<Array<u64>>, C: Rc<Array<u64>>, a: u64, b: u64, d: u64, k: u64, _H: ()) -> u64 {
  let v17 = ltb(0u64, d);
  match bdec(v17) {
    sumbool::left => {
      let v22 = &L;
      let v25 = rocq_array::get::<u64>(&v22, b);
      let v26 = &C;
      let v29 = rocq_array::get::<u64>(&v26, v25);
      let v30 = &L;
      let v33 = rocq_array::get::<u64>(&v30, a);
      let v34 = &C;
      let v37 = rocq_array::get::<u64>(&v34, v33);
      let cl = sub(v29, v37);
      match leb(k, cl) {
        true => {
          let v50 = &L;
          let v53 = rocq_array::get::<u64>(&v50, a);
          let v54 = &L;
          let v57 = rocq_array::get::<u64>(&v54, b);
          qry(L, R, C, v53, v57, sub(d, 1u64), k, ())
        },
        false => {
          let v104 = lsl(1u64, sub(d, 1u64));
          let v105 = &R;
          let v108 = rocq_array::get::<u64>(&v105, a);
          let v109 = &R;
          let v112 = rocq_array::get::<u64>(&v109, b);
          add(v104, qry(L, R, C, v108, v112, sub(d, 1u64), sub(k, cl), ()))
        },
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
  let v13 = Rc::clone(&t);
  let m = length(v13);
  let v18 = Rc::clone(&x);
  let v21 = Rc::clone(&t);
  let v28 = Rc::clone(&sa);
  let v29 = {
    let __anf_capture_34 = n;
    let __anf_capture_36 = m;
    move |i: u64| -> bool {
      let x = &v18;
      let t = &v21;
      let n = &__anf_capture_34;
      let m = &__anf_capture_36;
      let sa = &v28;
      let v42 = Clone::clone(n);
      let v44 = Clone::clone(m);
      match cmp_at(x, t, v42, v44, sa, i) {
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
  };
  let v68: Rc<dyn Fn(u64) -> bool> = Rc::new(v29);
  let lo = bs_1(v68, 0u64, n);
  let v82 = Rc::clone(&x);
  let v85 = Rc::clone(&t);
  let v92 = Rc::clone(&sa);
  let v93 = {
    let __anf_capture_98 = n;
    let __anf_capture_100 = m;
    move |i: u64| -> bool {
      let x = &v82;
      let t = &v85;
      let n = &__anf_capture_98;
      let m = &__anf_capture_100;
      let sa = &v92;
      let v106 = Clone::clone(n);
      let v108 = Clone::clone(m);
      match cmp_at(x, t, v106, v108, sa, i) {
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
  };
  let v132: Rc<dyn Fn(u64) -> bool> = Rc::new(v93);
  let hi = bs_1(v132, 0u64, n);
  let v149 = sub(hi, lo);
  match leb(k, v149) {
    true => {
      std::mem::drop(x);
      std::mem::drop(sa);
      std::mem::drop(t);
      let v158 = &roots;
      let v161 = rocq_array::get::<u64>(&v158, lo);
      let v162 = &roots;
      let v165 = rocq_array::get::<u64>(&v162, hi);
      std::mem::drop(roots);
      add(qry_1(L, R, C, v161, v165, D, k), 1u64)
    },
    false => {
      std::mem::drop(x);
      std::mem::drop(sa);
      std::mem::drop(L);
      std::mem::drop(R);
      std::mem::drop(C);
      std::mem::drop(roots);
      std::mem::drop(t);
      sub(0u64, 1u64)
    },
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
  let v21 = ltb(q, Q);
  match bdec(v21) {
    sumbool::left => {
      let v26 = &ts;
      let v29 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v26, q);
      let v30 = &ks;
      let v33 = rocq_array::get::<u64>(&v30, q);
      let v36 = Rc::clone(&x);
      let v41 = Rc::clone(&sa);
      let v44 = Rc::clone(&L);
      let v47 = Rc::clone(&R);
      let v50 = Rc::clone(&C);
      let v53 = Rc::clone(&roots);
      let v67 = rocq_array::set::<u64>(out, q, answer1(v36, n, v41, v44, v47, v50, v53, D, v29, v33));
      qloop(x, n, sa, L, R, C, roots, D, ts, ks, v67, add(q, 1u64), Q, ())
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
  let v6 = Rc::clone(&x);
  let n = length(v6);
  let v11 = Rc::clone(&x);
  let sa = build_sa(v11, n);
  let D = depth_loop_1(n, 0u64);
  let v32 = add(D, 1u64);
  let M = add(mul(n, v32), 1u64);
  let v52 = rocq_array::make::<u64>(M, 0u64);
  let v59 = rocq_array::make::<u64>(M, 0u64);
  let v66 = rocq_array::make::<u64>(M, 0u64);
  let v81 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v88 = Rc::clone(&sa);
  let v105 = build_1(v88, v52, v59, v66, v81, n, D, 0u64, 1u64);
  match v105 {
    (v107, v109) => {
      match v107 {
        (v112, v114) => {
          match v112 {
            (v117, v119) => {
              let v121 = &ts;
              let Q = rocq_array::length::<Rc<rocq_string::RocqString>>(&v121);
              let v130 = rocq_array::make::<u64>(Q, 0u64);
              qloop_1(x, n, sa, v117, v119, v114, v109, D, ts, ks, v130, 0u64, Q)
            },
          }
        },
      }
    },
  }
}

// Rocq: Anothersubstringqueryproblem.anothersubstringqueryproblem_implem.kth_occurrences_impl
pub fn kth_occurrences_impl_curried(x: Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v3 = {
    move |ts: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
      let x = &x;
      let v8 = Rc::clone(x);
      let v11 = {
        move |ks: Rc<Array<u64>>| -> Rc<Array<u64>> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&ts);
          kth_occurrences_impl(v19, v21, ks)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v3);
  v31
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

pub fn run() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_2117.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_2117: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = kth_occurrences(); }
std::thread_local! { static __rocq_global_2120: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = kth_occurrences_curried(); }