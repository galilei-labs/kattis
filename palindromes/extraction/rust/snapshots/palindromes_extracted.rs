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

// Rocq: Palindromes.palindromes_implem.imin
// Variant: uncurried
pub fn imin(a: u64, b: u64) -> u64 {
  if ltb(a, b) {
    a
  } else {
    b
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

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Palindromes.palindromes_implem.hcond
// Variant: uncurried
pub fn hcond(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64) -> bool {
  let tmp = leb(k, lsr(q, 1u64));
  let tmp_1 = add(q, 1u64);
  let tmp_2 = andb(tmp, ltb(add(lsr(tmp_1, 1u64), k), n));
  let tmp_3 = sub(lsr(q, 1u64), k);
  let x_clone = Rc::clone(&x);
  let tmp_4 = get(x_clone, tmp_3);
  let tmp_5 = add(q, 1u64);
  andb(tmp_2, eqb(tmp_4, get(x, add(lsr(tmp_5, 1u64), k))))
}

// Rocq: Palindromes.palindromes_implem.expand
// Variant: uncurried
pub fn expand_1(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64) -> u64 {
  expand(x, n, q, k, ())
}

// Rocq: Palindromes.palindromes_implem.expand (local: expand)
// Variant: uncurried, lifted
pub fn expand(x: Rc<rocq_string::RocqString>, n: u64, q: u64, k: u64, _H: ()) -> u64 {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let x_clone = Rc::clone(&x);
      if hcond(x_clone, n, q, k) {
        expand(x, n, q, add(k, 1u64), ())
      } else {
        std::mem::drop(x);
        k
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
  let tmp = ltb(q, n2);
  match bdec(tmp) {
    sumbool::left => {
      let bq = lsr(add(q, 1u64), 1u64);
      let k0 = if ltb(bq, rb) {
        let tmp_1 = rocq_array::get::<u64>(&cnt, sub(add(Q, Q), q));
        imin(tmp_1, sub(rb, bq))
      } else {
        0u64
      };
      let x_clone = Rc::clone(&x);
      let c = expand_1(x_clone, n, q, k0);
      let tmp_2 = add(bq, c);
      if ltb(rb, tmp_2) {
        let tmp_3 = rocq_array::set::<u64>(cnt, q, c);
        man(x, n, n2, tmp_3, add(q, 1u64), q, add(bq, c), ())
      } else {
        let tmp_4 = rocq_array::set::<u64>(cnt, q, c);
        man(x, n, n2, tmp_4, add(q, 1u64), Q, rb, ())
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
  let x_clone = Rc::clone(&x);
  let n = length(x_clone);
  let tmp = add(n, n);
  let tmp_1 = rocq_array::make::<u64>(add(n, n), 0u64);
  man_1(x, n, tmp, tmp_1, 0u64, 0u64, 0u64)
}

// Rocq: Palindromes.palindromes_implem.tab_loop
// Variant: uncurried
pub fn tab_loop_1(f: Rc<dyn Fn(u64) -> u64>, n: u64, i: u64, a: Rc<Array<u64>>) -> Rc<Array<u64>> {
  tab_loop(f, n, i, a, ())
}

// Rocq: Palindromes.palindromes_implem.tab_loop (local: tab_loop)
// Variant: uncurried, lifted
pub fn tab_loop(f: Rc<dyn Fn(u64) -> u64>, n: u64, i: u64, a: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let f_ref: &Rc<dyn Fn(u64) -> u64> = &f;
      let tmp_2 = f_ref(i);
      let tmp_3 = rocq_array::set::<u64>(a, i, tmp_2);
      tab_loop(f, n, tmp_1, tmp_3, ())
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
  let tmp = rocq_array::make::<u64>(n, 0u64);
  tab_loop_1(f, n, 0u64, tmp)
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
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let t = rocq_array::get::<u64>(&ts, k);
      let h = rocq_array::get::<u64>(&head, t);
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(head, t, add(k, 1u64));
      let tmp_3 = rocq_array::set::<u64>(next, k, h);
      build(ts, m, tmp_1, tmp_2, tmp_3, ())
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
  let tmp = ltb(0u64, j);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(j, 1u64);
      let tmp_2 = land(j, tmp_1);
      let tmp_3 = rocq_array::get::<u64>(&t, j);
      fen_sum(t, tmp_2, add(acc, tmp_3), ())
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

// Rocq: Palindromes.palindromes_implem.fval
// Variant: uncurried
pub fn fval(t: (Rc<Array<u64>>, Rc<Array<u64>>), a: u64) -> u64 {
  let t_clone = Clone::clone(&t);
  let tmp = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(t_clone);
  let tmp_1 = fsum(tmp, add(a, 1u64));
  let tmp_2 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(t);
  let tmp_3 = add(a, 1u64);
  add(tmp_1, mul(a, fsum(tmp_2, tmp_3)))
}

// Rocq: Palindromes.palindromes_implem.walk
// Variant: uncurried
pub fn walk_1(as_: Rc<Array<u64>>, next: Rc<Array<u64>>, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, ptr: u64) -> Rc<Array<u64>> {
  walk(as_, next, t, v, ptr, ())
}

// Rocq: Palindromes.palindromes_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(as_: Rc<Array<u64>>, next: Rc<Array<u64>>, t: (Rc<Array<u64>>, Rc<Array<u64>>), v: Rc<Array<u64>>, ptr: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, ptr);
  match bdec(tmp) {
    sumbool::left => {
      let k = sub(ptr, 1u64);
      let nx = rocq_array::get::<u64>(&next, k);
      let tmp_1 = rocq_array::get::<u64>(&as_, k);
      let t_clone = Clone::clone(&t);
      let v_ = rocq_array::set::<u64>(v, k, fval(t_clone, tmp_1));
      let tmp_2 = ltb(nx, ptr);
      match bdec(tmp_2) {
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
  let tmp = sub(j, 1u64);
  let tmp_1 = land(j, tmp);
  sub(j, tmp_1)
}

// Rocq: Palindromes.palindromes_implem.fen_add
// Variant: uncurried
pub fn fen_add_1(t: Rc<Array<u64>>, N: u64, j: u64, delta: u64) -> Rc<Array<u64>> {
  fen_add(t, N, j, delta, ())
}

// Rocq: Palindromes.palindromes_implem.fen_add (local: fen_add)
// Variant: uncurried, lifted
pub fn fen_add(t: Rc<Array<u64>>, N: u64, j: u64, delta: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = andb(ltb(0u64, j), leb(j, N));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&t, j);
      let t_ = rocq_array::set::<u64>(t, j, add(tmp_1, delta));
      let tmp_2 = lowb(j);
      let nj = add(j, tmp_2);
      let tmp_3 = ltb(j, nj);
      match bdec(tmp_3) {
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
  let t_clone = Clone::clone(&t);
  let tmp = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(t_clone);
  let t0 = fadd(tmp, NN, 1u64, dd);
  let t0_1 = fadd(t0, NN, add(lft, 2u64), lft);
  let t0_2 = fadd(t0_1, NN, add(i, 2u64), sub(0u64, add(i, 1u64)));
  let tmp_1 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(t);
  let t1 = fadd(tmp_1, NN, add(lft, 2u64), sub(0u64, 1u64));
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
  let tmp = ltb(tau, n1);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&head, tau);
      let as__clone = Rc::clone(&as_);
      let next_clone = Rc::clone(&next);
      let t_clone = Clone::clone(&t);
      let v_ = walk_1(as__clone, next_clone, t_clone, v, tmp_1);
      let t_ = if ltb(tau, n) {
        let tmp_2 = rocq_array::get::<u64>(&d, tau);
        insert(NN, t, tau, tmp_2)
      } else {
        t
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
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let tmp_1 = rocq_array::make::<u64>(m, 0u64);
  let hn = build_1(ts, m, 0u64, tmp, tmp_1);
  let NN = add(n, 2u64);
  let hn_clone = Clone::clone(&hn);
  let tmp_2 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(hn_clone);
  let tmp_3 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(hn);
  let tmp_4 = add(n, 1u64);
  let tmp_5 = rocq_array::make::<u64>(add(NN, 1u64), 0u64);
  let tmp_6 = rocq_array::make::<u64>(add(NN, 1u64), 0u64);
  let tmp_7 = (tmp_5, tmp_6);
  let tmp_8 = rocq_array::make::<u64>(m, 0u64);
  sweep_1(d, as_, tmp_2, tmp_3, n, tmp_4, NN, tmp_7, tmp_8, 0u64)
}

// Rocq: Palindromes.palindromes_implem.fam
// Variant: uncurried
pub fn fam(n: u64, m: u64, cnt: Rc<Array<u64>>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>, par: u64, rev: bool) -> Rc<Array<u64>> {
  let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
    let __anf_capture_17 = rev;
    let __anf_capture_19 = n;
    let __anf_capture_21 = par;
    move |i: u64| -> u64 {
      let rev = &__anf_capture_17;
      let n = &__anf_capture_19;
      let par = &__anf_capture_21;
      let cnt = &cnt;
      let tmp = 2u64;
      let tmp_1 = if *rev {
        let tmp_2 = 1u64;
        let tmp_3 = sub(Clone::clone(n), tmp_2);
        sub(tmp_3, i)
      } else {
        i
      };
      let tmp_4 = add(mul(tmp, tmp_1), Clone::clone(par));
      rocq_array::get::<u64>(cnt, tmp_4)
    }
  });
  let d = tab(n, callback);
  let xr_clone = Rc::clone(&xr);
  let xl_clone = Rc::clone(&xl);
  let callback_1: Rc<dyn Fn(u64) -> u64> = Rc::new({
    let __anf_capture_86 = rev;
    let __anf_capture_90 = par;
    let __anf_capture_92 = n;
    move |k: u64| -> u64 {
      let rev = &__anf_capture_86;
      let xr = &xr_clone;
      let par = &__anf_capture_90;
      let n = &__anf_capture_92;
      let xl = &xl_clone;
      if *rev {
        let tmp_5 = sub(rocq_array::get::<u64>(xr, k), Clone::clone(par));
        let n_clone = Clone::clone(n);
        sub(n_clone, tmp_5)
      } else {
        let tmp_6 = rocq_array::get::<u64>(xl, k);
        sub(tmp_6, 1u64)
      }
    }
  });
  let as_ = tab(m, callback_1);
  let callback_2: Rc<dyn Fn(u64) -> u64> = Rc::new({
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
      let h = lsr(sub(add(rocq_array::get::<u64>(xl, k), rocq_array::get::<u64>(xr, k)), Clone::clone(par)), 1u64);
      if *rev {
        let n_clone_1 = Clone::clone(n);
        sub(n_clone_1, h)
      } else {
        h
      }
    }
  });
  let ts = tab(m, callback_2);
  lsum_all(n, m, d, as_, ts)
}

// Rocq: Palindromes.palindromes_implem.palindromes_impl
// Variant: uncurried
pub fn palindromes_impl(x: Rc<rocq_string::RocqString>, xl: Rc<Array<u64>>, xr: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let x_clone = Rc::clone(&x);
  let n = length(x_clone);
  let m = rocq_array::length::<u64>(&xl);
  let cnt = manacher(x);
  let cnt_clone = Rc::clone(&cnt);
  let xl_clone = Rc::clone(&xl);
  let xr_clone = Rc::clone(&xr);
  let v0 = fam(n, m, cnt_clone, xl_clone, xr_clone, 0u64, false);
  let cnt_clone_1 = Rc::clone(&cnt);
  let xl_clone_1 = Rc::clone(&xl);
  let xr_clone_1 = Rc::clone(&xr);
  let v1 = fam(n, m, cnt_clone_1, xl_clone_1, xr_clone_1, 0u64, true);
  let cnt_clone_2 = Rc::clone(&cnt);
  let xl_clone_2 = Rc::clone(&xl);
  let xr_clone_2 = Rc::clone(&xr);
  let v2 = fam(n, m, cnt_clone_2, xl_clone_2, xr_clone_2, 1u64, false);
  let v3_1 = fam(n, m, cnt, xl, xr, 1u64, true);
  let callback: Rc<dyn Fn(u64) -> u64> = Rc::new({
    move |k: u64| -> u64 {
      let v0 = &v0;
      let v1 = &v1;
      let v2 = &v2;
      let v3 = &v3_1;
      let tmp = add(rocq_array::get::<u64>(v0, k), rocq_array::get::<u64>(v1, k));
      let tmp_1 = add(tmp, rocq_array::get::<u64>(v2, k));
      let tmp_2 = rocq_array::get::<u64>(v3, k);
      add(tmp_1, tmp_2)
    }
  });
  tab(m, callback)
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
