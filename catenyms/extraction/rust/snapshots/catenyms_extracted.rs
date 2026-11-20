#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

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

pub type char63 = Int63;

// Rocq: Catenyms.catenyms_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Catenyms.catenyms_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(a_1: Array<Int63>, n: Int63, k: Int63) -> Array<Int63> {
  init_loop(a_1, n, k, ())
}

// Rocq: Catenyms.catenyms_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(a_1: Array<Int63>, n: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      init_loop(a_1.set(k, k), n, k + int63!(1), ())
    },
    sumbool::right => {
      a_1
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

// Rocq: Catenyms.catenyms_implem.splitc
// Variant: uncurried
pub fn splitc(lo: Int63, hi: Int63) -> bool {
  andb(lo < hi, int63!(1) < hi - lo)
}

// Rocq: Catenyms.catenyms_implem.midp
// Variant: uncurried
pub fn midp(lo: Int63, hi: Int63) -> Int63 {
  let tmp = hi - lo;
  lo + tmp / int63!(2)
}

// Rocq: Corelib.Strings.PrimString.compare
// Variant: uncurried
pub fn compare(v0: rocq_string::RocqString, v1: rocq_string::RocqString) -> std::cmp::Ordering {
  let tmp = v0.compare(&v1);
  std::mem::drop(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.cmpw
// Variant: uncurried
pub fn cmpw(x: Array<rocq_string::RocqString>, i: Int63, j: Int63) -> bool {
  let x_ref = &x;
  let tmp = x_ref.get_cloned(i);
  let x_ref_1 = &x;
  let tmp_1 = x_ref_1.get_cloned(j);
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
pub fn merge_loop_1(x: Array<rocq_string::RocqString>, src: Array<Int63>, dst: Array<Int63>, iend: Int63, jend: Int63, i: Int63, j: Int63, k: Int63) -> Array<Int63> {
  merge_loop(x, src, dst, iend, jend, i, j, k, ())
}

// Rocq: Catenyms.catenyms_implem.merge_loop (local: merge_loop)
// Variant: uncurried, lifted
pub fn merge_loop(x: Array<rocq_string::RocqString>, src: Array<Int63>, dst: Array<Int63>, iend: Int63, jend: Int63, i: Int63, j: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = i < iend;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j < jend;
      match bdec(tmp_1) {
        sumbool::left => {
          let tmp_2 = src.get_cloned(i);
          let tmp_3 = src.get_cloned(j);
          let x_clone = Clone::clone(&x);
          if cmpw(x_clone, tmp_2, tmp_3) {
            let tmp_4 = src.get_cloned(i);
            merge_loop(x, src, dst.set(k, tmp_4), iend, jend, i + int63!(1), j, k + int63!(1), ())
          } else {
            let tmp_5 = src.get_cloned(j);
            merge_loop(x, src, dst.set(k, tmp_5), iend, jend, i, j + int63!(1), k + int63!(1), ())
          }
        },
        sumbool::right => {
          let tmp_6 = src.get_cloned(i);
          merge_loop(x, src, dst.set(k, tmp_6), iend, jend, i + int63!(1), j, k + int63!(1), ())
        },
      }
    },
    sumbool::right => {
      let tmp_7 = j < jend;
      match bdec(tmp_7) {
        sumbool::left => {
          let tmp_8 = src.get_cloned(j);
          merge_loop(x, src, dst.set(k, tmp_8), iend, jend, i, j + int63!(1), k + int63!(1), ())
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
pub fn copy_loop_1(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63) -> Array<Int63> {
  copy_loop(src, dst, hi, k, ())
}

// Rocq: Catenyms.catenyms_implem.copy_loop (local: copy_loop)
// Variant: uncurried, lifted
pub fn copy_loop(src: Array<Int63>, dst: Array<Int63>, hi: Int63, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < hi;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = src.get_cloned(k);
      copy_loop(src, dst.set(k, tmp_1), hi, k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(src);
      dst
    },
  }
}

// Rocq: Catenyms.catenyms_implem.msort
// Variant: uncurried
pub fn msort_1(x: Array<rocq_string::RocqString>, a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63) -> (Array<Int63>, Array<Int63>) {
  msort(x, a_1, t, lo, hi, ())
}

// Rocq: Catenyms.catenyms_implem.msort (local: msort)
// Variant: uncurried, lifted
pub fn msort(x: Array<rocq_string::RocqString>, a_1: Array<Int63>, t: Array<Int63>, lo: Int63, hi: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = splitc(lo, hi);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = midp(lo, hi);
      let x_clone = Clone::clone(&x);
      let tmp_2 = msort(x_clone, a_1, t, lo, tmp_1, ());
      match &tmp_2 {
        (t1, a1) => {
          let tmp_3 = midp(lo, hi);
          let tmp_4 = ();
          let x_clone_1 = Clone::clone(&x);
          let t1_clone = Clone::clone(t1);
          let a1_clone = Clone::clone(a1);
          std::mem::drop(tmp_2);
          let tmp_5 = msort(x_clone_1, t1_clone, a1_clone, tmp_3, hi, tmp_4);
          match tmp_5 {
            (v70, v72) => {
              let t2 = &v70;
              let tmp_6 = midp(lo, hi);
              let tmp_7 = midp(lo, hi);
              let t2_clone = Clone::clone(t2);
              let t3 = merge_loop_1(x, t2_clone, v72, tmp_6, hi, lo, tmp_7, lo);
              let t3_clone = Clone::clone(&t3);
              (copy_loop_1(t3_clone, v70, hi, lo), t3)
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      (a_1, t)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.fst_ch
pub fn fst_ch(w: rocq_string::RocqString) -> Int63 {
  get(w, int63!(0))
}

// Rocq: Catenyms.catenyms_implem.build_loop
// Variant: uncurried
pub fn build_loop_1(x: Array<rocq_string::RocqString>, ord: Array<Int63>, n: Int63, nxt: Array<Int63>, head: Array<Int63>, k: Int63) -> (Array<Int63>, Array<Int63>) {
  build_loop(x, ord, n, nxt, head, k, ())
}

// Rocq: Catenyms.catenyms_implem.build_loop (local: build_loop)
// Variant: uncurried, lifted
pub fn build_loop(x: Array<rocq_string::RocqString>, ord: Array<Int63>, n: Int63, nxt: Array<Int63>, head: Array<Int63>, k: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let e = ord.get_cloned(n - int63!(1) - k);
      let x_ref = &x;
      let tmp_1 = x_ref.get_cloned(e);
      let c = fst_ch(tmp_1);
      let h = head.get_cloned(c);
      build_loop(x, ord, n, nxt.set(e, h), head.set(c, e), k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(ord);
      (nxt, head)
    },
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Catenyms.catenyms_implem.lst_ch
pub fn lst_ch(w: rocq_string::RocqString) -> Int63 {
  let w_clone = Clone::clone(&w);
  get(w, length(w_clone) - int63!(1))
}

// Rocq: Catenyms.catenyms_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(x: Array<rocq_string::RocqString>, n: Int63, outd: Array<Int63>, ind: Array<Int63>, k: Int63) -> (Array<Int63>, Array<Int63>) {
  deg_loop(x, n, outd, ind, k, ())
}

// Rocq: Catenyms.catenyms_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(x: Array<rocq_string::RocqString>, n: Int63, outd: Array<Int63>, ind: Array<Int63>, k: Int63, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = k < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_ref = &x;
      let tmp_1 = x_ref.get_cloned(k);
      let a_1 = fst_ch(tmp_1);
      let x_ref_1 = &x;
      let tmp_2 = x_ref_1.get_cloned(k);
      let b_1 = lst_ch(tmp_2);
      let oa = outd.get_cloned(a_1);
      let ib = ind.get_cloned(b_1);
      deg_loop(x, n, outd.set(a_1, oa + int63!(1)), ind.set(b_1, ib + int63!(1)), k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (outd, ind)
    },
  }
}

// Rocq: Catenyms.catenyms_implem.chk_loop
// Variant: uncurried
pub fn chk_loop_1(outd: Array<Int63>, ind: Array<Int63>, c: Int63, plus: Int63, minus: Int63, sv: Int63, bad: bool) -> (((Int63, Int63), Int63), bool) {
  chk_loop(outd, ind, c, plus, minus, sv, bad, ())
}

// Rocq: Catenyms.catenyms_implem.chk_loop (local: chk_loop)
// Variant: uncurried, lifted
pub fn chk_loop(outd: Array<Int63>, ind: Array<Int63>, c: Int63, plus: Int63, minus: Int63, sv: Int63, bad: bool, _H: ()) -> (((Int63, Int63), Int63), bool) {
  let tmp = c < int63!(256);
  match bdec(tmp) {
    sumbool::left => {
      let o = outd.get_cloned(c);
      let i = ind.get_cloned(c);
      if o == i {
        chk_loop(outd, ind, c + int63!(1), plus, minus, sv, bad, ())
      } else {
        let tmp_1 = i + int63!(1);
        if o == tmp_1 {
          chk_loop(outd, ind, c + int63!(1), plus + int63!(1), minus, c, bad, ())
        } else {
          let tmp_2 = o + int63!(1);
          if i == tmp_2 {
            chk_loop(outd, ind, c + int63!(1), plus, minus + int63!(1), sv, bad, ())
          } else {
            chk_loop(outd, ind, c + int63!(1), plus, minus, sv, true, ())
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
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Catenyms.catenyms_implem.hier_loop
// Variant: uncurried
pub fn hier_loop_1(x: Array<rocq_string::RocqString>, nxt: Array<Int63>, n: Int63, s: Int63, ptr: Array<Int63>, stk: Array<Int63>, sp: Int63, q: Int63, res: Array<rocq_string::RocqString>, cnt: Int63) -> (Array<rocq_string::RocqString>, Int63) {
  hier_loop(x, nxt, n, s, ptr, stk, sp, q, res, cnt, ())
}

// Rocq: Catenyms.catenyms_implem.hier_loop (local: hier_loop)
// Variant: uncurried, lifted
pub fn hier_loop(x: Array<rocq_string::RocqString>, nxt: Array<Int63>, n: Int63, s: Int63, ptr: Array<Int63>, stk: Array<Int63>, sp: Int63, q: Int63, res: Array<rocq_string::RocqString>, cnt: Int63, _H: ()) -> (Array<rocq_string::RocqString>, Int63) {
  let tmp = int63!(0);
  let v = if sp == tmp {
    s
  } else {
    let tmp_1 = stk.get_cloned(sp - int63!(1));
    let x_ref = &x;
    let tmp_2 = x_ref.get_cloned(tmp_1);
    lst_ch(tmp_2)
  };
  let p = ptr.get_cloned(v);
  let tmp_3 = andb(p < n, q < n);
  match bdec(tmp_3) {
    sumbool::left => {
      let np = nxt.get_cloned(p);
      hier_loop(x, nxt, n, s, ptr.set(v, np), stk.set(sp, p), sp + int63!(1), q + int63!(1), res, cnt, ())
    },
    sumbool::right => {
      let tmp_4 = int63!(0) < sp;
      match bdec(tmp_4) {
        sumbool::left => {
          let e = stk.get_cloned(sp - int63!(1));
          let tmp_5 = sp - int63!(1);
          let tmp_6 = n - int63!(1) - cnt;
          let x_ref_1 = &x;
          let tmp_7 = x_ref_1.get_cloned(e);
          hier_loop(x, nxt, n, s, ptr, stk, tmp_5, q, res.set(tmp_6, tmp_7), cnt + int63!(1), ())
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
pub fn catenyms_impl(x: Array<rocq_string::RocqString>) -> Rc<option<Array<rocq_string::RocqString>>> {
  let n = x.length();
  let ord0 = init_loop_1(Array::<Int63>::make(n, int63!(0)), n, int63!(0));
  let tmp = Array::<Int63>::make(n, int63!(0));
  let x_clone = Clone::clone(&x);
  let tmp_1 = msort_1(x_clone, ord0, tmp, int63!(0), n);
  match tmp_1 {
    (v43, v45) => {
      let a_1 = &v43;
      let tmp_2 = Array::<Int63>::make(n, int63!(0));
      let tmp_3 = Array::<Int63>::make(int63!(256), n);
      let tmp_4 = int63!(0);
      let x_clone_1 = Clone::clone(&x);
      let tmp_5 = build_loop_1(x_clone_1, Clone::clone(a_1), n, tmp_2, tmp_3, tmp_4);
      match tmp_5 {
        (v80, v82) => {
          let head = &v80;
          let nxt = &v82;
          let tmp_6 = Array::<Int63>::make(int63!(256), int63!(0));
          let tmp_7 = Array::<Int63>::make(int63!(256), int63!(0));
          let x_clone_2 = Clone::clone(&x);
          let tmp_8 = deg_loop_1(x_clone_2, n, tmp_6, tmp_7, int63!(0));
          match tmp_8 {
            (v120, v122) => {
              let tmp_9 = chk_loop_1(v120, v122, int63!(0), int63!(0), int63!(0), int63!(0), false);
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
                            Rc::new(option::<Array<rocq_string::RocqString>>::None)
                          } else {
                            let tmp_10 = v162 == v164;
                            if negb(tmp_10) {
                              std::mem::drop(x);
                              std::mem::drop(v45);
                              std::mem::drop(v82);
                              std::mem::drop(v80);
                              std::mem::drop(v43);
                              Rc::new(option::<Array<rocq_string::RocqString>>::None)
                            } else {
                              let tmp_11 = v162 <= int63!(1);
                              if negb(tmp_11) {
                                std::mem::drop(x);
                                std::mem::drop(v45);
                                std::mem::drop(v82);
                                std::mem::drop(v80);
                                std::mem::drop(v43);
                                Rc::new(option::<Array<rocq_string::RocqString>>::None)
                              } else {
                                let tmp_12 = int63!(1);
                                let s = if v162 == tmp_12 {
                                  v159
                                } else {
                                  let tmp_13 = a_1.get_cloned(int63!(0));
                                  let x_ref = &x;
                                  let tmp_14 = x_ref.get_cloned(tmp_13);
                                  fst_ch(tmp_14)
                                };
                                let tmp_15 = Array::<Int63>::make(n, int63!(0));
                                let tmp_16 = int63!(0);
                                let tmp_17 = int63!(0);
                                let tmp_18 = rocq_string::StringPayload::from_static(b"");
                                let tmp_19 = Array::<rocq_string::RocqString>::make(n, rocq_string::RocqString::from_payload(tmp_18));
                                let tmp_20 = int63!(0);
                                let tmp_21 = hier_loop_1(x, Clone::clone(head), n, s, Clone::clone(nxt), tmp_15, tmp_16, tmp_17, tmp_19, tmp_20);
                                match tmp_21 {
                                  (v276, v278) => {
                                    if v278 == n {
                                      std::mem::drop(v45);
                                      std::mem::drop(v82);
                                      std::mem::drop(v80);
                                      std::mem::drop(v43);
                                      Rc::new(option::<Array<rocq_string::RocqString>>::Some(v276))
                                    } else {
                                      std::mem::drop(v45);
                                      std::mem::drop(v276);
                                      std::mem::drop(v82);
                                      std::mem::drop(v80);
                                      std::mem::drop(v43);
                                      Rc::new(option::<Array<rocq_string::RocqString>>::None)
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
