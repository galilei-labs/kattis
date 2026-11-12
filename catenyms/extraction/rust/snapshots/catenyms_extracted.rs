// Generated from OwnedANF. This printer is not verified.
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

// Rocq: Catenyms.catenyms_implem.catenyms
pub fn catenyms() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> = catenyms_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>> = Rc::new(v0);
  v1
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

// Rocq: Catenyms.catenyms_implem.bdec
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

// Rocq: Catenyms.catenyms_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(a: Rc<Array<u64>>, n: u64, k: u64) -> Rc<Array<u64>> {
  init_loop(a, n, k, ())
}

// Rocq: Catenyms.catenyms_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(a: Rc<Array<u64>>, n: u64, k: u64, _H: ()) -> Rc<Array<u64>> {
  let v11 = ltb(k, n);
  match bdec(v11) {
    sumbool::left => {
      let v21 = rocq_array::set::<u64>(a, k, k);
      init_loop(v21, n, add(k, 1u64), ())
    },
    sumbool::right => {
      a
    },
  }
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
  let v9 = sub(hi, lo);
  add(lo, div(v9, 2u64))
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: Rc<rocq_string::RocqString>, v1: Rc<rocq_string::RocqString>) -> std::cmp::Ordering {
  let v4 = rocq_string::compare(&v0, &v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  v4
}

// Rocq: Catenyms.catenyms_implem.cmpw
// Variant: uncurried
pub fn cmpw(x: Rc<Array<Rc<rocq_string::RocqString>>>, i: u64, j: u64) -> bool {
  let v4 = &x;
  let v7 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v4, i);
  let v8 = &x;
  let v11 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v8, j);
  match compare(v7, v11) {
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
  let v16 = ltb(i, iend);
  match bdec(v16) {
    sumbool::left => {
      let v27 = ltb(j, jend);
      match bdec(v27) {
        sumbool::left => {
          let v32 = &src;
          let v35 = rocq_array::get::<u64>(&v32, i);
          let v36 = &src;
          let v39 = rocq_array::get::<u64>(&v36, j);
          let v42 = Rc::clone(&x);
          match cmpw(v42, v35, v39) {
            true => {
              let v49 = &src;
              let v52 = rocq_array::get::<u64>(&v49, i);
              let v59 = rocq_array::set::<u64>(dst, k, v52);
              merge_loop(x, src, v59, iend, jend, add(i, 1u64), j, add(k, 1u64), ())
            },
            false => {
              let v100 = &src;
              let v103 = rocq_array::get::<u64>(&v100, j);
              let v110 = rocq_array::set::<u64>(dst, k, v103);
              merge_loop(x, src, v110, iend, jend, i, add(j, 1u64), add(k, 1u64), ())
            },
          }
        },
        sumbool::right => {
          let v154 = &src;
          let v157 = rocq_array::get::<u64>(&v154, i);
          let v164 = rocq_array::set::<u64>(dst, k, v157);
          merge_loop(x, src, v164, iend, jend, add(i, 1u64), j, add(k, 1u64), ())
        },
      }
    },
    sumbool::right => {
      let v215 = ltb(j, jend);
      match bdec(v215) {
        sumbool::left => {
          let v219 = &src;
          let v222 = rocq_array::get::<u64>(&v219, j);
          let v229 = rocq_array::set::<u64>(dst, k, v222);
          merge_loop(x, src, v229, iend, jend, i, add(j, 1u64), add(k, 1u64), ())
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
  let v12 = ltb(k, hi);
  match bdec(v12) {
    sumbool::left => {
      let v16 = &src;
      let v19 = rocq_array::get::<u64>(&v16, k);
      let v26 = rocq_array::set::<u64>(dst, k, v19);
      copy_loop(src, v26, hi, add(k, 1u64), ())
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
  let v13 = splitc(lo, hi);
  match bdec(v13) {
    sumbool::left => {
      let v22 = midp(lo, hi);
      let v28 = Rc::clone(&x);
      let v39 = msort(v28, a, t, lo, v22, ());
      match &v39 {
        (t1, a1) => {
          let v51 = midp(lo, hi);
          let v53 = ();
          let v57 = Rc::clone(&x);
          let v59 = Rc::clone(t1);
          let v60 = Rc::clone(a1);
          std::mem::drop(v39);
          let v68 = msort(v57, v59, v60, v51, hi, v53);
          match v68 {
            (v70, v72) => {
              let t2 = &v70;
              let v81 = midp(lo, hi);
              let v87 = midp(lo, hi);
              let v91 = Rc::clone(t2);
              let t3 = merge_loop_1(x, v91, v72, v81, hi, lo, v87, lo);
              let v108 = Rc::clone(&t3);
              let v116 = copy_loop_1(v108, v70, hi, lo);
              (v116, t3)
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
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
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
  let v14 = ltb(k, n);
  match bdec(v14) {
    sumbool::left => {
      let v27 = sub(n, 1u64);
      let v31 = sub(v27, k);
      let v32 = &ord;
      let e = rocq_array::get::<u64>(&v32, v31);
      let v37 = &x;
      let v41 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v37, e);
      let c = fst_ch(v41);
      let v44 = &head;
      let h = rocq_array::get::<u64>(&v44, c);
      let v54 = rocq_array::set::<u64>(nxt, e, h);
      let v61 = rocq_array::set::<u64>(head, c, e);
      build_loop(x, ord, n, v54, v61, add(k, 1u64), ())
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
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
}

// Rocq: Catenyms.catenyms_implem.lst_ch
pub fn lst_ch(w: Rc<rocq_string::RocqString>) -> u64 {
  let v6 = Rc::clone(&w);
  get(w, sub(length(v6), 1u64))
}

// Rocq: Catenyms.catenyms_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, k: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  deg_loop(x, n, outd, ind, k, ())
}

// Rocq: Catenyms.catenyms_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(x: Rc<Array<Rc<rocq_string::RocqString>>>, n: u64, outd: Rc<Array<u64>>, ind: Rc<Array<u64>>, k: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let v13 = ltb(k, n);
  match bdec(v13) {
    sumbool::left => {
      let v18 = &x;
      let v22 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v18, k);
      let a = fst_ch(v22);
      let v26 = &x;
      let v30 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v26, k);
      let b = lst_ch(v30);
      let v33 = &outd;
      let oa = rocq_array::get::<u64>(&v33, a);
      let v37 = &ind;
      let ib = rocq_array::get::<u64>(&v37, b);
      let v55 = rocq_array::set::<u64>(outd, a, add(oa, 1u64));
      let v70 = rocq_array::set::<u64>(ind, b, add(ib, 1u64));
      deg_loop(x, n, v55, v70, add(k, 1u64), ())
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
  let v17 = ltb(c, 256u64);
  match bdec(v17) {
    sumbool::left => {
      let v21 = &outd;
      let o = rocq_array::get::<u64>(&v21, c);
      let v25 = &ind;
      let i = rocq_array::get::<u64>(&v25, c);
      match eqb(o, i) {
        true => {
          chk_loop(outd, ind, add(c, 1u64), plus, minus, sv, bad, ())
        },
        false => {
          let v74 = add(i, 1u64);
          match eqb(o, v74) {
            true => {
              chk_loop(outd, ind, add(c, 1u64), add(plus, 1u64), minus, c, bad, ())
            },
            false => {
              let v127 = add(o, 1u64);
              match eqb(i, v127) {
                true => {
                  chk_loop(outd, ind, add(c, 1u64), plus, add(minus, 1u64), sv, bad, ())
                },
                false => {
                  chk_loop(outd, ind, add(c, 1u64), plus, minus, sv, true, ())
                },
              }
            },
          }
        },
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
  match b {
    true => {
      false
    },
    false => {
      true
    },
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
  let v13 = 0u64;
  let v = match eqb(sp, v13) {
    true => {
      s
    },
    false => {
      let v30 = sub(sp, 1u64);
      let v31 = &stk;
      let v34 = rocq_array::get::<u64>(&v31, v30);
      let v35 = &x;
      let v39 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v35, v34);
      lst_ch(v39)
    },
  };
  let v45 = &ptr;
  let p = rocq_array::get::<u64>(&v45, v);
  let v68 = andb(ltb(p, n), ltb(q, n));
  match bdec(v68) {
    sumbool::left => {
      let v72 = &nxt;
      let np = rocq_array::get::<u64>(&v72, p);
      let v82 = rocq_array::set::<u64>(ptr, v, np);
      let v89 = rocq_array::set::<u64>(stk, sp, p);
      hier_loop(x, nxt, n, s, v82, v89, add(sp, 1u64), add(q, 1u64), res, cnt, ())
    },
    sumbool::right => {
      let v143 = ltb(0u64, sp);
      match bdec(v143) {
        sumbool::left => {
          let v154 = sub(sp, 1u64);
          let v155 = &stk;
          let e = rocq_array::get::<u64>(&v155, v154);
          let v166 = sub(sp, 1u64);
          let v176 = sub(n, 1u64);
          let v180 = sub(v176, cnt);
          let v181 = &x;
          let v184 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v181, e);
          let v191 = rocq_array::set::<Rc<rocq_string::RocqString>>(res, v180, v184);
          hier_loop(x, nxt, n, s, ptr, stk, v166, q, v191, add(cnt, 1u64), ())
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

// Rocq: Corelib.Strings.PrimString.make
// Variant: uncurried
pub fn make(v0: u64, v1: u64) -> Rc<rocq_string::RocqString> {
  let v8 = rocq_string::make(v0, v1);
  v8
}

// Rocq: Catenyms.catenyms_implem.catenyms_impl
pub fn catenyms_impl(x: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>> {
  let v1 = &x;
  let n = rocq_array::length::<Rc<rocq_string::RocqString>>(&v1);
  let v10 = rocq_array::make::<u64>(n, 0u64);
  let ord0 = init_loop_1(v10, n, 0u64);
  let v27 = rocq_array::make::<u64>(n, 0u64);
  let v32 = Rc::clone(&x);
  let v41 = msort_1(v32, ord0, v27, 0u64, n);
  match v41 {
    (v43, v45) => {
      let a = &v43;
      let v55 = rocq_array::make::<u64>(n, 0u64);
      let v62 = rocq_array::make::<u64>(256u64, n);
      let v67 = Rc::clone(&x);
      let v69 = Rc::clone(a);
      let v78 = build_loop_1(v67, v69, n, v55, v62, 0u64);
      match v78 {
        (v80, v82) => {
          let head = &v80;
          let nxt = &v82;
          let v95 = rocq_array::make::<u64>(256u64, 0u64);
          let v104 = rocq_array::make::<u64>(256u64, 0u64);
          let v109 = Rc::clone(&x);
          let v118 = deg_loop_1(v109, n, v95, v104, 0u64);
          match v118 {
            (v120, v122) => {
              let v149 = chk_loop_1(v120, v122, 0u64, 0u64, 0u64, 0u64, false);
              match v149 {
                (v151, v153) => {
                  let p = &v153;
                  match v151 {
                    (v157, v159) => {
                      match v157 {
                        (v162, v164) => {
                          match p {
                            true => {
                              std::mem::drop(x);
                              std::mem::drop(v45);
                              std::mem::drop(v82);
                              std::mem::drop(v80);
                              std::mem::drop(v43);
                              Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                            },
                            false => {
                              let v179 = eqb(v162, v164);
                              match negb(v179) {
                                true => {
                                  std::mem::drop(x);
                                  std::mem::drop(v45);
                                  std::mem::drop(v82);
                                  std::mem::drop(v80);
                                  std::mem::drop(v43);
                                  Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                                },
                                false => {
                                  let v197 = leb(v162, 1u64);
                                  match negb(v197) {
                                    true => {
                                      std::mem::drop(x);
                                      std::mem::drop(v45);
                                      std::mem::drop(v82);
                                      std::mem::drop(v80);
                                      std::mem::drop(v43);
                                      Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
                                    },
                                    false => {
                                      let v208 = 1u64;
                                      let s = match eqb(v162, v208) {
                                        true => {
                                          v159
                                        },
                                        false => {
                                          let v219 = 0u64;
                                          let v222 = rocq_array::get::<u64>(&a, v219);
                                          let v223 = &x;
                                          let v227 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v223, v222);
                                          fst_ch(v227)
                                        },
                                      };
                                      let v240 = rocq_array::make::<u64>(n, 0u64);
                                      let v254 = make(0u64, 0u64);
                                      let v259 = rocq_array::make::<Rc<rocq_string::RocqString>>(n, v254);
                                      let v265 = Rc::clone(head);
                                      let v271 = Rc::clone(nxt);
                                      let v282 = hier_loop_1(x, v265, n, s, v271, v240, 0u64, 0u64, v259, 0u64);
                                      match v282 {
                                        (v284, v286) => {
                                          match eqb(v286, n) {
                                            true => {
                                              std::mem::drop(v45);
                                              std::mem::drop(v82);
                                              std::mem::drop(v80);
                                              std::mem::drop(v43);
                                              Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::Some(v284))
                                            },
                                            false => {
                                              std::mem::drop(v45);
                                              std::mem::drop(v284);
                                              std::mem::drop(v82);
                                              std::mem::drop(v80);
                                              std::mem::drop(v43);
                                              Rc::new(option::<Rc<Array<Rc<rocq_string::RocqString>>>>::None)
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>> = __rocq_global_966.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_966: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<option<Rc<Array<Rc<rocq_string::RocqString>>>>>> = catenyms(); }