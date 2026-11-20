#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub enum option<A: 'static> {
  Some(A),
  None,
}

impl<A: Clone + 'static> Clone for option<A> {
  fn clone(&self) -> Self {
    match self {
      option::Some(__field0) => option::Some(Clone::clone(__field0)),
      option::None => option::None,
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<std::cmp::Ordering>; };

pub type char63 = u64;

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

// Rocq: Catenyms.catenyms_implem.bdec
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

// Rocq: Catenyms.catenyms_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(a: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<u64>> {
  init_loop(a, n, k, ())
}

// Rocq: Catenyms.catenyms_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(a: Rc<Array<u64>>, n: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::set::<u64>(a, k, k);
      init_loop(tmp_1, n, add(k, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Catenyms.catenyms_implem.splitc
// Variant: uncurried
pub fn splitc(lo: u64, hi: u64) -> bool {
  andb(ltb(lo, hi), ltb(1u64, sub(hi, lo)))
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.div
// Variant: uncurried
pub fn div(v0: u64, v1: u64) -> u64 {
  rocq_int63::div(v0, v1)
}

// Rocq: Catenyms.catenyms_implem.midp
// Variant: uncurried
pub fn midp(lo: u64, hi: u64) -> u64 {
  let tmp = sub(hi, lo);
  add(lo, div(tmp, 2u64))
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let tmp = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.cmpw
// Variant: uncurried
pub fn cmpw(x: Rc<Array<Rc<rocq_string::RocqString>>>, i: u64, j: u64) -> bool {
  let tmp = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, i);
  let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, j);
  match compare(tmp, tmp_1) {
    std::cmp::Ordering::Equal => {
      std::mem::drop(x);
      true
    },
    std::cmp::Ordering::Less => {
      std::mem::drop(x);
      true
    },
    std::cmp::Ordering::Greater => {
      std::mem::drop(x);
      false
    },
  }
}

// Rocq: Catenyms.catenyms_implem.merge_loop
// Variant: uncurried
pub fn merge_loop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, iend: u64, jend: u64, i: u64, j: u64, k: u64) -> Rc<Array<u64>> {
  merge_loop(x, src, dst, iend, jend, i, j, k, ())
}

// Rocq: Catenyms.catenyms_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(x: Rc<Array<Rc<rocq_string::RocqString>>>, src: Rc<Array<u64>>, dst: Rc<Array<u64>>, iend: u64, jend: u64, i: u64, j: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, iend);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = ltb(j, jend);
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = rocq_array::get::<u64>(&src, i);
          let tmp_3 = rocq_array::get::<u64>(&src, j);
          let x_clone = Rc::clone(&x);
          if cmpw(x_clone, tmp_2, tmp_3) {
            let tmp_4 = rocq_array::get::<u64>(&src, i);
            let tmp_5 = rocq_array::set::<u64>(dst, k, tmp_4);
            merge_loop(x, src, tmp_5, iend, jend, add(i, 1u64), j, add(k, 1u64), ())
          } else {
            let tmp_6 = rocq_array::get::<u64>(&src, j);
            let tmp_7 = rocq_array::set::<u64>(dst, k, tmp_6);
            merge_loop(x, src, tmp_7, iend, jend, i, add(j, 1u64), add(k, 1u64), ())
          }
        },
        sumbool::right => {
          let tmp_8 = rocq_array::get::<u64>(&src, i);
          let tmp_9 = rocq_array::set::<u64>(dst, k, tmp_8);
          merge_loop(x, src, tmp_9, iend, jend, add(i, 1u64), j, add(k, 1u64), ())
        },
      }
    },
    sumbool::right => {
      let tmp_10 = ltb(j, jend);
      match bdec(tmp_10) {
        sumbool::left => {
          let tmp_11 = rocq_array::get::<u64>(&src, j);
          let tmp_12 = rocq_array::set::<u64>(dst, k, tmp_11);
          merge_loop(x, src, tmp_12, iend, jend, i, add(j, 1u64), add(k, 1u64), ())
        },
        sumbool::right => {
          std::mem::drop(x);
          std::mem::drop(src);
          dst
        },
      }
    },
  }
}

// Rocq: Catenyms.catenyms_implem.copy_loop
// Variant: uncurried
pub fn copy_loop_1(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64) -> Rc<Array<u64>> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Catenyms.catenyms_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Rc<Array<u64>>, dst: Rc<Array<u64>>, hi: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&src, k);
      let tmp_2 = rocq_array::set::<u64>(dst, k, tmp_1);
      copy_loop(src, tmp_2, hi, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Catenyms.catenyms_implem.msort
// Variant: uncurried
pub fn msort_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  msort(x, a, t, lo, hi, ())
}

// Rocq: Catenyms.catenyms_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(x: Rc<Array<Rc<rocq_string::RocqString>>>, a: Rc<Array<u64>>, t: Rc<Array<u64>>, lo: u64, hi: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = splitc(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let x_clone = Rc::clone(&x);
      let tmp_2 = msort(x_clone, a, t, lo, tmp_1, ());
      match &tmp_2 {
        (t1, a1) => {
          let tmp_3 = midp(lo, hi);
          let tmp_4 = ();
          let x_clone_1 = Rc::clone(&x);
          let t1_clone = Rc::clone(t1);
          let a1_clone = Rc::clone(a1);
          std::mem::drop(tmp_2);
          let tmp_5 = msort(x_clone_1, t1_clone, a1_clone, tmp_3, hi, tmp_4);
          match tmp_5 {
            (v70, v72) => {
              let t2 = &v70;
              let tmp_6 = midp(lo, hi);
              let tmp_7 = midp(lo, hi);
              let t2_clone = Rc::clone(t2);
              let t3 = merge_loop_1(x, t2_clone, v72, tmp_6, hi, lo, tmp_7, lo);
              let t3_clone = Rc::clone(&t3);
              let tmp_8 = copy_loop_1(t3_clone, v70, hi, lo);
              (tmp_8, t3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      (a, t)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let tmp = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.fst_ch
pub fn fst_ch(w: Rc<rocq_string::RocqString>) -> u64 {
  get(w, 0u64)
}

// Rocq: Catenyms.catenyms_implem.build_loop
// Variant: uncurried
pub fn build_loop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, n: u64, nxt: Rc<Array<u64>>, head: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  build_loop(x, ord, n, nxt, head, k, ())
}

// Rocq: Catenyms.catenyms_implem.build_loop (local: build_loop)
// Variant: uncurried, lifted
pub fn build_loop(x: Rc<Array<Rc<rocq_string::RocqString>>>, ord: Rc<Array<u64>>, n: u64, nxt: Rc<Array<u64>>, head: Rc<Array<u64>>, k: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = sub(n, 1u64);
      let e = rocq_array::get::<u64>(&ord, sub(tmp_1, k));
      let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, e);
      let c = fst_ch(tmp_2);
      let h = rocq_array::get::<u64>(&head, c);
      let tmp_3 = rocq_array::set::<u64>(nxt, e, h);
      let tmp_4 = rocq_array::set::<u64>(head, c, e);
      build_loop(x, ord, n, tmp_3, tmp_4, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(ord);
      (nxt, head)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let tmp = rocq_string::length(&v0);
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.lst_ch
pub fn lst_ch(w: Rc<rocq_string::RocqString>) -> u64 {
  let w_clone = Rc::clone(&w);
  get(w, sub(length(w_clone), 1u64))
}

// Rocq: Catenyms.catenyms_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  deg_loop(x, n, outd, ind, k, ())
}

// Rocq: Catenyms.catenyms_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, k: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, k);
      let a = fst_ch(tmp_1);
      let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, k);
      let b = lst_ch(tmp_2);
      let oa = rocq_array::get::<u64>(&outd, a);
      let ib = rocq_array::get::<u64>(&ind, b);
      let tmp_3 = rocq_array::set::<u64>(outd, a, add(oa, 1u64));
      let tmp_4 = rocq_array::set::<u64>(ind, b, add(ib, 1u64));
      deg_loop(x, n, tmp_3, tmp_4, add(k, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (outd, ind)
    },
  }
}

// Rocq: Catenyms.catenyms_implem.chk_loop
// Variant: uncurried
pub fn chk_loop_1(outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, c: u64, plus: u64, minus: u64, sv: u64, bad: bool) -> (((u64, u64), u64), bool) {
  chk_loop(outd, ind, c, plus, minus, sv, bad, ())
}

// Rocq: Catenyms.catenyms_implem.chk_loop (local: chk_loop)
// Variant: uncurried, lifted
pub fn chk_loop(outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, c: u64, plus: u64, minus: u64, sv: u64, bad: bool, _H: ()) -> (((u64, u64), u64), bool) {
  let tmp = ltb(c, 256u64);
  match bdec(tmp) {
    sumbool::left => {
      let o = rocq_array::get::<u64>(&outd, c);
      let i = rocq_array::get::<u64>(&ind, c);
      if eqb(o, i) {
        chk_loop(outd, ind, add(c, 1u64), plus, minus, sv, bad, ())
      } else {
        let tmp_1 = add(i, 1u64);
        if eqb(o, tmp_1) {
          chk_loop(outd, ind, add(c, 1u64), add(plus, 1u64), minus, c, bad, ())
        } else {
          let tmp_2 = add(o, 1u64);
          if eqb(i, tmp_2) {
            chk_loop(outd, ind, add(c, 1u64), plus, add(minus, 1u64), sv, bad, ())
          } else {
            chk_loop(outd, ind, add(c, 1u64), plus, minus, sv, true, ())
          }
        }
      }
    },
    sumbool::right => {
      std::mem::drop(outd);
      std::mem::drop(ind);
      (((plus, minus), sv), bad)
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

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Catenyms.catenyms_implem.hier_loop
// Variant: uncurried
pub fn hier_loop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, nxt: Rc<Array<u64>>, n: u64, s: u64, ptr: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, q: u64, res: Rc<Array<Rc<rocq_string::RocqString>>>, cnt: u64) -> (Rc<Array<Rc<rocq_string::RocqString>>>, u64) {
  hier_loop(x, nxt, n, s, ptr, stk, sp, q, res, cnt, ())
}

// Rocq: Catenyms.catenyms_implem.hier_loop (local: hier_loop)
// Variant: uncurried, lifted
pub fn hier_loop(x: Rc<Array<Rc<rocq_string::RocqString>>>, nxt: Rc<Array<u64>>, n: u64, s: u64, ptr: Rc<Array<u64>>, stk: Rc<Array<u64>>, sp: u64, q: u64, res: Rc<Array<Rc<rocq_string::RocqString>>>, cnt: u64, _H: ()) -> (Rc<Array<Rc<rocq_string::RocqString>>>, u64) {
  let tmp = 0u64;
  let v = if eqb(sp, tmp) {
    s
  } else {
    let tmp_1 = rocq_array::get::<u64>(&stk, sub(sp, 1u64));
    let tmp_2 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, tmp_1);
    lst_ch(tmp_2)
  };
  let p = rocq_array::get::<u64>(&ptr, v);
  let tmp_3 = andb(ltb(p, n), ltb(q, n));
  match bdec(tmp_3) {
    sumbool::left => {
      let np = rocq_array::get::<u64>(&nxt, p);
      let tmp_4 = rocq_array::set::<u64>(ptr, v, np);
      let tmp_5 = rocq_array::set::<u64>(stk, sp, p);
      hier_loop(x, nxt, n, s, tmp_4, tmp_5, add(sp, 1u64), add(q, 1u64), res, cnt, ())
    },
    sumbool::right => {
      let tmp_6 = ltb(0u64, sp);
      match bdec(tmp_6) {
        sumbool::left => {
          let e = rocq_array::get::<u64>(&stk, sub(sp, 1u64));
          let tmp_7 = sub(sp, 1u64);
          let tmp_8 = sub(n, 1u64);
          let tmp_9 = sub(tmp_8, cnt);
          let tmp_10 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, e);
          let tmp_11 = rocq_array::set::<Rc<rocq_string::RocqString>>(res, tmp_9, tmp_10);
          hier_loop(x, nxt, n, s, ptr, stk, tmp_7, q, tmp_11, add(cnt, 1u64), ())
        },
        sumbool::right => {
          std::mem::drop(x);
          std::mem::drop(nxt);
          std::mem::drop(stk);
          std::mem::drop(ptr);
          (res, cnt)
        },
      }
    },
  }
}

// Rocq: Catenyms.catenyms_implem.catenyms_impl
pub fn catenyms_impl(x: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&x);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let ord0 = init_loop_1(tmp, n, 0u64);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let x_clone = Rc::clone(&x);
  let tmp_2 = msort_1(x_clone, ord0, tmp_1, 0u64, n);
  match tmp_2 {
    (v43, v45) => {
      let a = &v43;
      let tmp_3 = rocq_array::make::<u64>(n, 0u64);
      let tmp_4 = rocq_array::make::<u64>(256u64, n);
      let x_clone_1 = Rc::clone(&x);
      let a_clone = Rc::clone(a);
      let tmp_5 = build_loop_1(x_clone_1, a_clone, n, tmp_3, tmp_4, 0u64);
      match tmp_5 {
        (v80, v82) => {
          let head = &v80;
          let nxt = &v82;
          let tmp_6 = rocq_array::make::<u64>(256u64, 0u64);
          let tmp_7 = rocq_array::make::<u64>(256u64, 0u64);
          let x_clone_2 = Rc::clone(&x);
          let tmp_8 = deg_loop_1(x_clone_2, n, tmp_6, tmp_7, 0u64);
          match tmp_8 {
            (v120, v122) => {
              let tmp_9 = chk_loop_1(v120, v122, 0u64, 0u64, 0u64, 0u64, false);
              match tmp_9 {
                (v151, v153) => {
                  let p = &v153;
                  match v151 {
                    (v157, v159) => {
                      match v157 {
                        (v162, v164) => {
                          if *p {
                            std::mem::drop(x);
                            std::mem::drop(v45);
                            std::mem::drop(v82);
                            std::mem::drop(v80);
                            std::mem::drop(v43);
                            Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                          } else {
                            let tmp_10 = eqb(v162, v164);
                            if negb(tmp_10) {
                              std::mem::drop(x);
                              std::mem::drop(v45);
                              std::mem::drop(v82);
                              std::mem::drop(v80);
                              std::mem::drop(v43);
                              Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                            } else {
                              let tmp_11 = leb(v162, 1u64);
                              if negb(tmp_11) {
                                std::mem::drop(x);
                                std::mem::drop(v45);
                                std::mem::drop(v82);
                                std::mem::drop(v80);
                                std::mem::drop(v43);
                                Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                              } else {
                                let tmp_12 = 1u64;
                                let s = if eqb(v162, tmp_12) {
                                  v159
                                } else {
                                  let tmp_13 = rocq_array::get::<Rc<rocq_string::RocqString>>(&x, rocq_array::get::<u64>(a, 0u64));
                                  fst_ch(tmp_13)
                                };
                                let tmp_14 = rocq_array::make::<u64>(n, 0u64);
                                let tmp_15 = rocq_string::RocqString::from_bytes(vec![]);
                                let tmp_16 = Rc::new(tmp_15);
                                let tmp_17 = rocq_array::make::<Rc<rocq_string::RocqString>>(n, tmp_16);
                                let head_clone = Rc::clone(head);
                                let nxt_clone = Rc::clone(nxt);
                                let tmp_18 = hier_loop_1(x, head_clone, n, s, nxt_clone, tmp_14, 0u64, 0u64, tmp_17, 0u64);
                                match tmp_18 {
                                  (v277, v279) => {
                                    if eqb(v279, n) {
                                      std::mem::drop(v45);
                                      std::mem::drop(v82);
                                      std::mem::drop(v80);
                                      std::mem::drop(v43);
                                      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(v277))
                                    } else {
                                      std::mem::drop(v45);
                                      std::mem::drop(v277);
                                      std::mem::drop(v82);
                                      std::mem::drop(v80);
                                      std::mem::drop(v43);
                                      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                                    }
                                  },
                                }
                              }
                            }
                          }
                        },
                      }
                    },
                  }
                },
              }
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
