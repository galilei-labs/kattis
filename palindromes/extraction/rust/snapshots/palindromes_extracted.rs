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

pub type uint = u64;

pub type char63 = u64;

// Rocq: Palindromes.palindromes_implem.palindromes
// Variant: uncurried
pub fn palindromes() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>> = palindromes_impl;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Palindromes.palindromes_implem.palindromes
pub fn palindromes_curried() -> Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> {
  let v0: fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = palindromes_impl_curried;
  let v1: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = Rc::new(v0);
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.land
// Variant: uncurried
pub fn land(v0: u64, v1: u64) -> u64 {
  rocq_int63::land(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Palindromes.palindromes_implem.bdec
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

// Rocq: Palindromes.palindromes_implem.imin
// Variant: uncurried
pub fn imin(a: u64, b: u64) -> u64 {
  match ltb(a, b) {
    true => {
      a
    },
    false => {
      b
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
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

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Palindromes.palindromes_implem.hcond
// Variant: uncurried
pub fn hcond(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64) -> bool {
  let v19 = leb(k, lsr(q, 1u64));
  let v30 = add(q, 1u64);
  let v52 = andb(v19, ltb(add(lsr(v30, 1u64), k), n));
  let v68 = sub(lsr(q, 1u64), k);
  let v71 = Rc::clone(&x);
  let v74 = get(v71, v68);
  let v85 = add(q, 1u64);
  andb(v52, eqb(v74, get(x, add(lsr(v85, 1u64), k))))
}

// Rocq: Palindromes.palindromes_implem.expand
// Variant: uncurried
pub fn expand_1(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64) -> u64 {
  expand(x, n, q, k, ())
}

// Rocq: Palindromes.palindromes_implem.expand (local: expand)
// Variant: uncurried, lifted
pub fn expand(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64, _H: ()) -> u64 {
  let v12 = ltb(k, n);
  match bdec(v12) {
    sumbool::left => {
      let v19 = Rc::clone(&x);
      match hcond(v19, n, q, k) {
        true => {
          expand(x, n, q, add(k, 1u64), ())
        },
        false => {
          std::mem::drop(x);
          k
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      k
    },
  }
}

// Rocq: Palindromes.palindromes_implem.man
// Variant: uncurried
pub fn man_1(x: Rc<rocq_string::RocqString>, n: u64, n2: u64, cnt: Rc<Array<u64>>, q: u64, Q: u64, rb: u64) -> Rc<Array<u64>> {
  man(x, n, n2, cnt, q, Q, rb, ())
}

// Rocq: Palindromes.palindromes_implem.man (local: man)
// Variant: uncurried, lifted
pub fn man(x: Rc<rocq_string::RocqString>, n: u64, n2: u64, cnt: Rc<Array<u64>>, q: u64, Q: u64, rb: u64, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(q, n2);
  match bdec(v15) {
    sumbool::left => {
      let bq = lsr(add(q, 1u64), 1u64);
      let k0 = match ltb(bq, rb) {
        true => {
          let v54 = sub(add(Q, Q), q);
          let v55 = &cnt;
          let v58 = rocq_array::get::<u64>(&v55, v54);
          imin(v58, sub(rb, bq))
        },
        false => {
          0u64
        },
      };
      let v80 = Rc::clone(&x);
      let c = expand_1(v80, n, q, k0);
      let v94 = add(bq, c);
      match ltb(rb, v94) {
        true => {
          let v107 = rocq_array::set::<u64>(cnt, q, c);
          man(x, n, n2, v107, add(q, 1u64), q, add(bq, c), ())
        },
        false => {
          let v150 = rocq_array::set::<u64>(cnt, q, c);
          man(x, n, n2, v150, add(q, 1u64), Q, rb, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      cnt
    },
  }
}

// Rocq: Palindromes.palindromes_implem.manacher
pub fn manacher(x: Rc<rocq_string::RocqString>) -> Rc<Array<u64>> {
  let v4 = Rc::clone(&x);
  let n = length(v4);
  let v12 = add(n, n);
  let v25 = rocq_array::make::<u64>(add(n, n), 0u64);
  man_1(x, n, v12, v25, 0u64, 0u64, 0u64)
}

// Rocq: Palindromes.palindromes_implem.tab_loop
// Variant: uncurried
pub fn tab_loop_1(f: Rc<dyn Fn(u64) -> u64>, n: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  tab_loop(f, n, i, a, ())
}

// Rocq: Palindromes.palindromes_implem.tab_loop (local: tab_loop)
// Variant: uncurried, lifted
pub fn tab_loop(f: Rc<dyn Fn(u64) -> u64>, n: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let v12 = ltb(i, n);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(i, 1u64);
      let v24: &Rc<dyn Fn(u64) -> u64> = &f;
      let v27 = v24(i);
      let v34 = rocq_array::set::<u64>(a, i, v27);
      tab_loop(f, n, v23, v34, ())
    },
    sumbool::right => {
      std::mem::drop(f);
      a
    },
  }
}

// Rocq: Palindromes.palindromes_implem.tab
// Variant: uncurried
pub fn tab(n: u64, f: Rc<dyn Fn(u64) -> u64>) -> Rc<Array<u64>> {
  let v11 = rocq_array::make::<u64>(n, 0u64);
  tab_loop_1(f, n, 0u64, v11)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Palindromes.palindromes_implem.build
// Variant: uncurried
pub fn build_1(ts: Rc<Array<u64>>, m: u64, k: u64, head: Rc<Array<u64>>, next: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  build(ts, m, k, head, next, ())
}

// Rocq: Palindromes.palindromes_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(ts: Rc<Array<u64>>, m: u64, k: u64, head: Rc<Array<u64>>, next: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(k, m);
  match bdec(v13) {
    sumbool::left => {
      let v17 = &ts;
      let t = rocq_array::get::<u64>(&v17, k);
      let v21 = &head;
      let h = rocq_array::get::<u64>(&v21, t);
      let v32 = add(k, 1u64);
      let v47 = rocq_array::set::<u64>(head, t, add(k, 1u64));
      let v54 = rocq_array::set::<u64>(next, k, h);
      build(ts, m, v32, v47, v54, ())
    },
    sumbool::right => {
      std::mem::drop(ts);
      (head, next)
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fen_sum
// Variant: uncurried
pub fn fen_sum_1(t: Rc<Array<u64>>, j: u64, acc: u64) -> u64 {
  fen_sum(t, j, acc, ())
}

// Rocq: Palindromes.palindromes_implem.fen_sum (local: fen_sum)
// Variant: uncurried, lifted
pub fn fen_sum(t: Rc<Array<u64>>, j: u64, acc: u64, _H: ()) -> u64 {
  let v13 = ltb(0u64, j);
  match bdec(v13) {
    sumbool::left => {
      let v25 = sub(j, 1u64);
      let v30 = land(j, v25);
      let v32 = &t;
      let v35 = rocq_array::get::<u64>(&v32, j);
      fen_sum(t, v30, add(acc, v35), ())
    },
    sumbool::right => {
      std::mem::drop(t);
      acc
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fsum
// Variant: uncurried
pub fn fsum(t: Rc<Array<u64>>, j: u64) -> u64 {
  fen_sum_1(t, j, 0u64)
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

// Rocq: Palindromes.palindromes_implem.fval
// Variant: uncurried
pub fn fval(t: (Rc<Array<u64>>, Rc<Array<u64>>), a: u64) -> u64 {
  let v6 = Clone::clone(&t);
  let v8 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v6);
  let v21 = fsum(v8, add(a, 1u64));
  let v27 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(t);
  let v35 = add(a, 1u64);
  add(v21, mul(a, fsum(v27, v35)))
}

// Rocq: Palindromes.palindromes_implem.walk
// Variant: uncurried
pub fn walk_1(as_: Rc<Array<u64>>, next: Rc<Array<u64>>, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, ptr: u64) -> Rc<Array<u64>> {
  walk(as_, next, t, v, ptr, ())
}

// Rocq: Palindromes.palindromes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(as_: Rc<Array<u64>>, next: Rc<Array<u64>>, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, ptr: u64, _H: ()) -> Rc<Array<u64>> {
  let v15 = ltb(0u64, ptr);
  match bdec(v15) {
    sumbool::left => {
      let k = sub(ptr, 1u64);
      let v27 = &next;
      let nx = rocq_array::get::<u64>(&v27, k);
      let v32 = &as_;
      let v35 = rocq_array::get::<u64>(&v32, k);
      let v37 = Clone::clone(&t);
      let v_ = rocq_array::set::<u64>(v, k, fval(v37, v35));
      let v56 = ltb(nx, ptr);
      match bdec(v56) {
        sumbool::left => {
          walk(as_, next, t, v_, nx, ())
        },
        sumbool::right => {
          std::mem::drop(next);
          std::mem::drop(t);
          std::mem::drop(as_);
          v_
        },
      }
    },
    sumbool::right => {
      std::mem::drop(as_);
      std::mem::drop(next);
      std::mem::drop(t);
      v
    },
  }
}

// Rocq: Palindromes.palindromes_implem.lowb
pub fn lowb(j: u64) -> u64 {
  let v10 = sub(j, 1u64);
  let v15 = land(j, v10);
  sub(j, v15)
}

// Rocq: Palindromes.palindromes_implem.fen_add
// Variant: uncurried
pub fn fen_add_1(t: Rc<Array<u64>>, N: u64, j: u64, delta: u64) -> Rc<Array<u64>> {
  fen_add(t, N, j, delta, ())
}

// Rocq: Palindromes.palindromes_implem.fen_add (local: fen_add)
// Variant: uncurried, lifted
pub fn fen_add(t: Rc<Array<u64>>, N: u64, j: u64, delta: u64, _H: ()) -> Rc<Array<u64>> {
  let v26 = andb(ltb(0u64, j), leb(j, N));
  match bdec(v26) {
    sumbool::left => {
      let v31 = &t;
      let v35 = rocq_array::get::<u64>(&v31, j);
      let t_ = rocq_array::set::<u64>(t, j, add(v35, delta));
      let v51 = lowb(j);
      let nj = add(j, v51);
      let v64 = ltb(j, nj);
      match bdec(v64) {
        sumbool::left => {
          fen_add(t_, N, nj, delta, ())
        },
        sumbool::right => {
          t_
        },
      }
    },
    sumbool::right => {
      t
    },
  }
}

// Rocq: Palindromes.palindromes_implem.fadd
// Variant: uncurried
pub fn fadd(t: Rc<Array<u64>>, N: u64, j: u64, delta: u64) -> Rc<Array<u64>> {
  fen_add_1(t, N, j, delta)
}

// Rocq: Palindromes.palindromes_implem.insert
// Variant: uncurried
pub fn insert(NN: u64, t: (Rc<Array<u64>>, Rc<Array<u64>>), i: u64, di: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let dd = imin(di, add(i, 1u64));
  let lft = sub(add(i, 1u64), dd);
  let v35 = Clone::clone(&t);
  let v37 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v35);
  let t0 = fadd(v37, NN, 1u64, dd);
  let t0_1 = fadd(t0, NN, add(lft, 2u64), lft);
  let t0_2 = fadd(t0_1, NN, add(i, 2u64), sub(0u64, add(i, 1u64)));
  let v105 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(t);
  let t1 = fadd(v105, NN, add(lft, 2u64), sub(0u64, 1u64));
  let t1_1 = fadd(t1, NN, add(i, 2u64), 1u64);
  (t0_2, t1_1)
}

// Rocq: Palindromes.palindromes_implem.sweep
// Variant: uncurried
pub fn sweep_1(d: Rc<Array<u64>>, as_: Rc<Array<u64>>, head: Rc<Array<u64>>, next: Rc<Array<u64>>, n: u64, n1: u64, NN: u64, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, tau: u64) -> Rc<Array<u64>> {
  sweep(d, as_, head, next, n, n1, NN, t, v, tau, ())
}

// Rocq: Palindromes.palindromes_implem.sweep (local: sweep)
// Variant: uncurried, lifted
pub fn sweep(d: Rc<Array<u64>>, as_: Rc<Array<u64>>, head: Rc<Array<u64>>, next: Rc<Array<u64>>, n: u64, n1: u64, NN: u64, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, tau: u64, _H: ()) -> Rc<Array<u64>> {
  let v18 = ltb(tau, n1);
  match bdec(v18) {
    sumbool::left => {
      let v23 = &head;
      let v26 = rocq_array::get::<u64>(&v23, tau);
      let v29 = Rc::clone(&as_);
      let v32 = Rc::clone(&next);
      let v34 = Clone::clone(&t);
      let v_ = walk_1(v29, v32, v34, v, v26);
      let t_ = match ltb(tau, n) {
        true => {
          let v49 = &d;
          let v52 = rocq_array::get::<u64>(&v49, tau);
          insert(NN, t, tau, v52)
        },
        false => {
          t
        },
      };
      sweep(d, as_, head, next, n, n1, NN, t_, v_, add(tau, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(d);
      std::mem::drop(as_);
      std::mem::drop(head);
      std::mem::drop(next);
      std::mem::drop(t);
      v
    },
  }
}

// Rocq: Palindromes.palindromes_implem.lsum_all
// Variant: uncurried
pub fn lsum_all(n: u64, m: u64, d: Rc<Array<u64>>, as_: Rc<Array<u64>>, ts: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v22 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let v29 = rocq_array::make::<u64>(m, 0u64);
  let hn = build_1(ts, m, 0u64, v22, v29);
  let NN = add(n, 2u64);
  let v52 = Clone::clone(&hn);
  let v54 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(v52);
  let v58 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(hn);
  let v66 = add(n, 1u64);
  let v81 = rocq_array::make::<u64>(add(NN, 1u64), 0u64);
  let v96 = rocq_array::make::<u64>(add(NN, 1u64), 0u64);
  let v101 = (v81, v96);
  let v109 = rocq_array::make::<u64>(m, 0u64);
  sweep_1(d, as_, v54, v58, n, v66, NN, v101, v109, 0u64)
}

// Rocq: Palindromes.palindromes_implem.fam
// Variant: uncurried
pub fn fam(n: u64, m: u64, cnt: Rc<Array<u64>>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>, par: u64, rev: bool) -> Rc<Array<u64>> {
  let v16 = {
    let __anf_capture_17 = rev;
    let __anf_capture_19 = n;
    let __anf_capture_21 = par;
    move |i: u64| -> u64 {
      let rev = &__anf_capture_17;
      let n = &__anf_capture_19;
      let par = &__anf_capture_21;
      let cnt = &cnt;
      let v29 = 2u64;
      let v30 = match rev {
        true => {
          let v34 = 1u64;
          let v40 = sub(Clone::clone(n), v34);
          sub(v40, i)
        },
        false => {
          i
        },
      };
      let v60 = add(mul(v29, v30), Clone::clone(par));
      rocq_array::get::<u64>(&cnt, v60)
    }
  };
  let v65: Rc<dyn Fn(u64) -> u64> = Rc::new(v16);
  let d = tab(n, v65);
  let v77 = Rc::clone(&xr);
  let v84 = Rc::clone(&xl);
  let v85 = {
    let __anf_capture_86 = rev;
    let __anf_capture_90 = par;
    let __anf_capture_92 = n;
    move |k: u64| -> u64 {
      let rev = &__anf_capture_86;
      let xr = &v77;
      let par = &__anf_capture_90;
      let n = &__anf_capture_92;
      let xl = &v84;
      match rev {
        true => {
          let v107 = sub(rocq_array::get::<u64>(&xr, k), Clone::clone(par));
          let v109 = Clone::clone(n);
          sub(v109, v107)
        },
        false => {
          let v118 = rocq_array::get::<u64>(&xl, k);
          sub(v118, 1u64)
        },
      }
    }
  };
  let v131: Rc<dyn Fn(u64) -> u64> = Rc::new(v85);
  let as_ = tab(m, v131);
  let v149 = {
    let __anf_capture_150 = xl;
    let __anf_capture_152 = xr;
    let __anf_capture_154 = par;
    let __anf_capture_156 = rev;
    let __anf_capture_158 = n;
    move |k: u64| -> u64 {
      let xl = &__anf_capture_150;
      let xr = &__anf_capture_152;
      let par = &__anf_capture_154;
      let rev = &__anf_capture_156;
      let n = &__anf_capture_158;
      let h = lsr(sub(add(rocq_array::get::<u64>(&xl, k), rocq_array::get::<u64>(&xr, k)), Clone::clone(par)), 1u64);
      match rev {
        true => {
          let v190 = Clone::clone(n);
          sub(v190, h)
        },
        false => {
          h
        },
      }
    }
  };
  let v201: Rc<dyn Fn(u64) -> u64> = Rc::new(v149);
  let ts = tab(m, v201);
  lsum_all(n, m, d, as_, ts)
}

// Rocq: Palindromes.palindromes_implem.palindromes_impl
// Variant: uncurried
pub fn palindromes_impl(x: Rc<rocq_string::RocqString>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let v6 = Rc::clone(&x);
  let n = length(v6);
  let v8 = &xl;
  let m = rocq_array::length::<u64>(&v8);
  let cnt = manacher(x);
  let v25 = Rc::clone(&cnt);
  let v28 = Rc::clone(&xl);
  let v31 = Rc::clone(&xr);
  let v0 = fam(n, m, v25, v28, v31, 0u64, false);
  let v48 = Rc::clone(&cnt);
  let v51 = Rc::clone(&xl);
  let v54 = Rc::clone(&xr);
  let v1 = fam(n, m, v48, v51, v54, 0u64, true);
  let v71 = Rc::clone(&cnt);
  let v74 = Rc::clone(&xl);
  let v77 = Rc::clone(&xr);
  let v2 = fam(n, m, v71, v74, v77, 1u64, false);
  let v3_1 = fam(n, m, cnt, xl, xr, 1u64, true);
  let v112 = {
    move |k: u64| -> u64 {
      let v0 = &v0;
      let v1 = &v1;
      let v2 = &v2;
      let v3 = &v3_1;
      let v135 = add(rocq_array::get::<u64>(&v0, k), rocq_array::get::<u64>(&v1, k));
      let v143 = add(v135, rocq_array::get::<u64>(&v2, k));
      let v146 = rocq_array::get::<u64>(&v3, k);
      add(v143, v146)
    }
  };
  let v154: Rc<dyn Fn(u64) -> u64> = Rc::new(v112);
  tab(m, v154)
}

// Rocq: Palindromes.palindromes_implem.palindromes_impl
pub fn palindromes_impl_curried(x: Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> {
  let v3 = {
    move |xl: Rc<Array<u64>>| -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> {
      let x = &x;
      let v8 = Rc::clone(x);
      let v11 = {
        move |xr: Rc<Array<u64>>| -> Rc<Array<u64>> {
          let v19 = Rc::clone(&v8);
          let v21 = Rc::clone(&xl);
          palindromes_impl(v19, v21, xr)
        }
      };
      let v27: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>> = Rc::new(v11);
      v27
    }
  };
  let v31: Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>> = Rc::new(v3);
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

pub fn run() -> Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = __rocq_global_1058.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_1058: Rc<dyn Fn(Rc<rocq_string::RocqString>, Rc<Array<u64>>, Rc<Array<u64>>) -> Rc<Array<u64>>> = palindromes(); }
std::thread_local! { static __rocq_global_1061: Rc<dyn Fn(Rc<rocq_string::RocqString>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<dyn Fn(Rc<Array<u64>>) -> Rc<Array<u64>>>>> = palindromes_curried(); }