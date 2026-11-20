#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

pub struct ires {
  pub r_T: Rc<tab>,
  pub r_cnt: Array<Int63>,
  pub r_sz: Int63,
  pub r_n: Int63,
  pub r_s: Int63,
}

impl Clone for ires {
  fn clone(&self) -> Self {
    match self {
      ires { r_T: __field0, r_cnt: __field1, r_sz: __field2, r_n: __field3, r_s: __field4 } => ires { r_T: Clone::clone(__field0), r_cnt: Clone::clone(__field1), r_sz: Clone::clone(__field2), r_n: Clone::clone(__field3), r_s: Clone::clone(__field4) },
    }
  }
}

pub struct bres {
  pub b_T: Rc<tab>,
  pub b_cnt: Array<Int63>,
  pub b_end: Array<Int63>,
}

impl Clone for bres {
  fn clone(&self) -> Self {
    match self {
      bres { b_T: __field0, b_cnt: __field1, b_end: __field2 } => bres { b_T: Clone::clone(__field0), b_cnt: Clone::clone(__field1), b_end: Clone::clone(__field2) },
    }
  }
}

pub struct tab {
  pub tc0: Array<Int63>,
  pub tc1: Array<Int63>,
  pub tc2: Array<Int63>,
  pub tc3: Array<Int63>,
  pub tc4: Array<Int63>,
  pub tc5: Array<Int63>,
  pub tc6: Array<Int63>,
  pub tc7: Array<Int63>,
  pub tc8: Array<Int63>,
  pub tc9: Array<Int63>,
  pub tc10: Array<Int63>,
  pub tc11: Array<Int63>,
  pub tc12: Array<Int63>,
  pub tc13: Array<Int63>,
  pub tc14: Array<Int63>,
  pub tc15: Array<Int63>,
  pub tc16: Array<Int63>,
  pub tc17: Array<Int63>,
  pub tc18: Array<Int63>,
  pub tc19: Array<Int63>,
  pub tc20: Array<Int63>,
  pub tc21: Array<Int63>,
  pub tc22: Array<Int63>,
  pub tc23: Array<Int63>,
  pub tc24: Array<Int63>,
  pub tc25: Array<Int63>,
}

impl Clone for tab {
  fn clone(&self) -> Self {
    match self {
      tab { tc0: __field0, tc1: __field1, tc2: __field2, tc3: __field3, tc4: __field4, tc5: __field5, tc6: __field6, tc7: __field7, tc8: __field8, tc9: __field9, tc10: __field10, tc11: __field11, tc12: __field12, tc13: __field13, tc14: __field14, tc15: __field15, tc16: __field16, tc17: __field17, tc18: __field18, tc19: __field19, tc20: __field20, tc21: __field21, tc22: __field22, tc23: __field23, tc24: __field24, tc25: __field25 } => tab { tc0: Clone::clone(__field0), tc1: Clone::clone(__field1), tc2: Clone::clone(__field2), tc3: Clone::clone(__field3), tc4: Clone::clone(__field4), tc5: Clone::clone(__field5), tc6: Clone::clone(__field6), tc7: Clone::clone(__field7), tc8: Clone::clone(__field8), tc9: Clone::clone(__field9), tc10: Clone::clone(__field10), tc11: Clone::clone(__field11), tc12: Clone::clone(__field12), tc13: Clone::clone(__field13), tc14: Clone::clone(__field14), tc15: Clone::clone(__field15), tc16: Clone::clone(__field16), tc17: Clone::clone(__field17), tc18: Clone::clone(__field18), tc19: Clone::clone(__field19), tc20: Clone::clone(__field20), tc21: Clone::clone(__field21), tc22: Clone::clone(__field22), tc23: Clone::clone(__field23), tc24: Clone::clone(__field24), tc25: Clone::clone(__field25) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type char63 = Int63;

pub type uint = Int63;

// Rocq: Baza.baza_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: rocq_string::RocqString) -> Int63 {
  let tmp = v0.length();
  std::mem::drop(v0);
  tmp
}

// Rocq: Baza.baza_implem.total
// Variant: uncurried
pub fn total_1(db: Array<rocq_string::RocqString>, N: Int63, j: Int63, acc: Int63) -> Int63 {
  total(db, N, j, acc, ())
}

// Rocq: Baza.baza_implem.total (local: total)
// Variant: uncurried, lifted
pub fn total(db: Array<rocq_string::RocqString>, N: Int63, j: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = j < N;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = j + int63!(1);
      let db_ref = &db;
      let tmp_2 = db_ref.get_cloned(j);
      total(db, N, tmp_1, acc + length(tmp_2), ())
    },
    sumbool::right => {
      std::mem::drop(db);
      acc
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

// Rocq: Baza.baza_implem.tc0
pub fn tc0_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc0_clone = Clone::clone(&t.tc0);
  std::mem::drop(t);
  t_tc0_clone
}

// Rocq: Baza.baza_implem.tc0
// Variant: borrowed
pub fn tc0(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc0)
}

// Rocq: Baza.baza_implem.tc1
pub fn tc1_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc1_clone = Clone::clone(&t.tc1);
  std::mem::drop(t);
  t_tc1_clone
}

// Rocq: Baza.baza_implem.tc1
// Variant: borrowed
pub fn tc1(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc1)
}

// Rocq: Baza.baza_implem.tc2
pub fn tc2_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc2_clone = Clone::clone(&t.tc2);
  std::mem::drop(t);
  t_tc2_clone
}

// Rocq: Baza.baza_implem.tc2
// Variant: borrowed
pub fn tc2(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc2)
}

// Rocq: Baza.baza_implem.tc3
pub fn tc3_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc3_clone = Clone::clone(&t.tc3);
  std::mem::drop(t);
  t_tc3_clone
}

// Rocq: Baza.baza_implem.tc3
// Variant: borrowed
pub fn tc3(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc3)
}

// Rocq: Baza.baza_implem.tc4
pub fn tc4_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc4_clone = Clone::clone(&t.tc4);
  std::mem::drop(t);
  t_tc4_clone
}

// Rocq: Baza.baza_implem.tc4
// Variant: borrowed
pub fn tc4(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc4)
}

// Rocq: Baza.baza_implem.tc5
pub fn tc5_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc5_clone = Clone::clone(&t.tc5);
  std::mem::drop(t);
  t_tc5_clone
}

// Rocq: Baza.baza_implem.tc5
// Variant: borrowed
pub fn tc5(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc5)
}

// Rocq: Baza.baza_implem.tc6
pub fn tc6_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc6_clone = Clone::clone(&t.tc6);
  std::mem::drop(t);
  t_tc6_clone
}

// Rocq: Baza.baza_implem.tc6
// Variant: borrowed
pub fn tc6(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc6)
}

// Rocq: Baza.baza_implem.tc7
pub fn tc7_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc7_clone = Clone::clone(&t.tc7);
  std::mem::drop(t);
  t_tc7_clone
}

// Rocq: Baza.baza_implem.tc7
// Variant: borrowed
pub fn tc7(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc7)
}

// Rocq: Baza.baza_implem.tc8
pub fn tc8_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc8_clone = Clone::clone(&t.tc8);
  std::mem::drop(t);
  t_tc8_clone
}

// Rocq: Baza.baza_implem.tc8
// Variant: borrowed
pub fn tc8(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc8)
}

// Rocq: Baza.baza_implem.tc9
pub fn tc9_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc9_clone = Clone::clone(&t.tc9);
  std::mem::drop(t);
  t_tc9_clone
}

// Rocq: Baza.baza_implem.tc9
// Variant: borrowed
pub fn tc9(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc9)
}

// Rocq: Baza.baza_implem.tc10
pub fn tc10_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc10_clone = Clone::clone(&t.tc10);
  std::mem::drop(t);
  t_tc10_clone
}

// Rocq: Baza.baza_implem.tc10
// Variant: borrowed
pub fn tc10(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc10)
}

// Rocq: Baza.baza_implem.tc11
pub fn tc11_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc11_clone = Clone::clone(&t.tc11);
  std::mem::drop(t);
  t_tc11_clone
}

// Rocq: Baza.baza_implem.tc11
// Variant: borrowed
pub fn tc11(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc11)
}

// Rocq: Baza.baza_implem.tc12
pub fn tc12_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc12_clone = Clone::clone(&t.tc12);
  std::mem::drop(t);
  t_tc12_clone
}

// Rocq: Baza.baza_implem.tc12
// Variant: borrowed
pub fn tc12(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc12)
}

// Rocq: Baza.baza_implem.tc13
pub fn tc13_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc13_clone = Clone::clone(&t.tc13);
  std::mem::drop(t);
  t_tc13_clone
}

// Rocq: Baza.baza_implem.tc13
// Variant: borrowed
pub fn tc13(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc13)
}

// Rocq: Baza.baza_implem.tc14
pub fn tc14_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc14_clone = Clone::clone(&t.tc14);
  std::mem::drop(t);
  t_tc14_clone
}

// Rocq: Baza.baza_implem.tc14
// Variant: borrowed
pub fn tc14(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc14)
}

// Rocq: Baza.baza_implem.tc15
pub fn tc15_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc15_clone = Clone::clone(&t.tc15);
  std::mem::drop(t);
  t_tc15_clone
}

// Rocq: Baza.baza_implem.tc15
// Variant: borrowed
pub fn tc15(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc15)
}

// Rocq: Baza.baza_implem.tc16
pub fn tc16_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc16_clone = Clone::clone(&t.tc16);
  std::mem::drop(t);
  t_tc16_clone
}

// Rocq: Baza.baza_implem.tc16
// Variant: borrowed
pub fn tc16(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc16)
}

// Rocq: Baza.baza_implem.tc17
pub fn tc17_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc17_clone = Clone::clone(&t.tc17);
  std::mem::drop(t);
  t_tc17_clone
}

// Rocq: Baza.baza_implem.tc17
// Variant: borrowed
pub fn tc17(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc17)
}

// Rocq: Baza.baza_implem.tc18
pub fn tc18_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc18_clone = Clone::clone(&t.tc18);
  std::mem::drop(t);
  t_tc18_clone
}

// Rocq: Baza.baza_implem.tc18
// Variant: borrowed
pub fn tc18(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc18)
}

// Rocq: Baza.baza_implem.tc19
pub fn tc19_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc19_clone = Clone::clone(&t.tc19);
  std::mem::drop(t);
  t_tc19_clone
}

// Rocq: Baza.baza_implem.tc19
// Variant: borrowed
pub fn tc19(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc19)
}

// Rocq: Baza.baza_implem.tc20
pub fn tc20_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc20_clone = Clone::clone(&t.tc20);
  std::mem::drop(t);
  t_tc20_clone
}

// Rocq: Baza.baza_implem.tc20
// Variant: borrowed
pub fn tc20(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc20)
}

// Rocq: Baza.baza_implem.tc21
pub fn tc21_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc21_clone = Clone::clone(&t.tc21);
  std::mem::drop(t);
  t_tc21_clone
}

// Rocq: Baza.baza_implem.tc21
// Variant: borrowed
pub fn tc21(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc21)
}

// Rocq: Baza.baza_implem.tc22
pub fn tc22_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc22_clone = Clone::clone(&t.tc22);
  std::mem::drop(t);
  t_tc22_clone
}

// Rocq: Baza.baza_implem.tc22
// Variant: borrowed
pub fn tc22(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc22)
}

// Rocq: Baza.baza_implem.tc23
pub fn tc23_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc23_clone = Clone::clone(&t.tc23);
  std::mem::drop(t);
  t_tc23_clone
}

// Rocq: Baza.baza_implem.tc23
// Variant: borrowed
pub fn tc23(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc23)
}

// Rocq: Baza.baza_implem.tc24
pub fn tc24_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc24_clone = Clone::clone(&t.tc24);
  std::mem::drop(t);
  t_tc24_clone
}

// Rocq: Baza.baza_implem.tc24
// Variant: borrowed
pub fn tc24(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc24)
}

// Rocq: Baza.baza_implem.tc25
pub fn tc25_owned(t: Rc<tab>) -> Array<Int63> {
  let t_tc25_clone = Clone::clone(&t.tc25);
  std::mem::drop(t);
  t_tc25_clone
}

// Rocq: Baza.baza_implem.tc25
// Variant: borrowed
pub fn tc25(t: &Rc<tab>) -> Array<Int63> {
  let tmp = t;
  Clone::clone(&tmp.tc25)
}

// Rocq: Baza.baza_implem.sel
// Variant: uncurried
pub fn sel_owned(t: Rc<tab>, c: Int63) -> Array<Int63> {
  if c < int63!(13) {
    if c < int63!(6) {
      if c < int63!(3) {
        if c < int63!(1) {
          tc0_owned(t)
        } else {
          if c < int63!(2) {
            tc1_owned(t)
          } else {
            tc2_owned(t)
          }
        }
      } else {
        if c < int63!(4) {
          tc3_owned(t)
        } else {
          if c < int63!(5) {
            tc4_owned(t)
          } else {
            tc5_owned(t)
          }
        }
      }
    } else {
      if c < int63!(9) {
        if c < int63!(7) {
          tc6_owned(t)
        } else {
          if c < int63!(8) {
            tc7_owned(t)
          } else {
            tc8_owned(t)
          }
        }
      } else {
        if c < int63!(11) {
          if c < int63!(10) {
            tc9_owned(t)
          } else {
            tc10_owned(t)
          }
        } else {
          if c < int63!(12) {
            tc11_owned(t)
          } else {
            tc12_owned(t)
          }
        }
      }
    }
  } else {
    if c < int63!(19) {
      if c < int63!(16) {
        if c < int63!(14) {
          tc13_owned(t)
        } else {
          if c < int63!(15) {
            tc14_owned(t)
          } else {
            tc15_owned(t)
          }
        }
      } else {
        if c < int63!(17) {
          tc16_owned(t)
        } else {
          if c < int63!(18) {
            tc17_owned(t)
          } else {
            tc18_owned(t)
          }
        }
      }
    } else {
      if c < int63!(22) {
        if c < int63!(20) {
          tc19_owned(t)
        } else {
          if c < int63!(21) {
            tc20_owned(t)
          } else {
            tc21_owned(t)
          }
        }
      } else {
        if c < int63!(24) {
          if c < int63!(23) {
            tc22_owned(t)
          } else {
            tc23_owned(t)
          }
        } else {
          if c < int63!(25) {
            tc24_owned(t)
          } else {
            tc25_owned(t)
          }
        }
      }
    }
  }
}

// Rocq: Baza.baza_implem.sel
// Variant: borrowed, uncurried
pub fn sel(t: &Rc<tab>, c: Int63) -> Array<Int63> {
  let c_1 = c;
  if c_1 < int63!(13) {
    if c_1 < int63!(6) {
      if c_1 < int63!(3) {
        if c_1 < int63!(1) {
          tc0(t)
        } else {
          if c_1 < int63!(2) {
            tc1(t)
          } else {
            tc2(t)
          }
        }
      } else {
        if c_1 < int63!(4) {
          tc3(t)
        } else {
          if c_1 < int63!(5) {
            tc4(t)
          } else {
            tc5(t)
          }
        }
      }
    } else {
      if c_1 < int63!(9) {
        if c_1 < int63!(7) {
          tc6(t)
        } else {
          if c_1 < int63!(8) {
            tc7(t)
          } else {
            tc8(t)
          }
        }
      } else {
        if c_1 < int63!(11) {
          if c_1 < int63!(10) {
            tc9(t)
          } else {
            tc10(t)
          }
        } else {
          if c_1 < int63!(12) {
            tc11(t)
          } else {
            tc12(t)
          }
        }
      }
    }
  } else {
    if c_1 < int63!(19) {
      if c_1 < int63!(16) {
        if c_1 < int63!(14) {
          tc13(t)
        } else {
          if c_1 < int63!(15) {
            tc14(t)
          } else {
            tc15(t)
          }
        }
      } else {
        if c_1 < int63!(17) {
          tc16(t)
        } else {
          if c_1 < int63!(18) {
            tc17(t)
          } else {
            tc18(t)
          }
        }
      }
    } else {
      if c_1 < int63!(22) {
        if c_1 < int63!(20) {
          tc19(t)
        } else {
          if c_1 < int63!(21) {
            tc20(t)
          } else {
            tc21(t)
          }
        }
      } else {
        if c_1 < int63!(24) {
          if c_1 < int63!(23) {
            tc22(t)
          } else {
            tc23(t)
          }
        } else {
          if c_1 < int63!(25) {
            tc24(t)
          } else {
            tc25(t)
          }
        }
      }
    }
  }
}

// Rocq: Baza.baza_implem.tget
// Variant: borrowed, uncurried
pub fn tget(t: &Rc<tab>, c: Int63, n: Int63) -> Int63 {
  let c_1 = c;
  let n_1 = n;
  let tmp = sel(t, c_1);
  let tmp_1 = tmp.get_cloned(n_1);
  std::mem::drop(tmp);
  tmp_1
}

// Rocq: Baza.baza_implem.upd
// Variant: uncurried
pub fn upd(t: Rc<tab>, c: Int63, a_1: Array<Int63>) -> Rc<tab> {
  if c < int63!(13) {
    if c < int63!(6) {
      if c < int63!(3) {
        if c < int63!(1) {
          let t_clone = Rc::clone(&t);
          let tmp = tc1_owned(t_clone);
          let t_clone_1 = Rc::clone(&t);
          let tmp_1 = tc2_owned(t_clone_1);
          let t_clone_2 = Rc::clone(&t);
          let tmp_2 = tc3_owned(t_clone_2);
          let t_clone_3 = Rc::clone(&t);
          let tmp_3 = tc4_owned(t_clone_3);
          let t_clone_4 = Rc::clone(&t);
          let tmp_4 = tc5_owned(t_clone_4);
          let t_clone_5 = Rc::clone(&t);
          let tmp_5 = tc6_owned(t_clone_5);
          let t_clone_6 = Rc::clone(&t);
          let tmp_6 = tc7_owned(t_clone_6);
          let t_clone_7 = Rc::clone(&t);
          let tmp_7 = tc8_owned(t_clone_7);
          let t_clone_8 = Rc::clone(&t);
          let tmp_8 = tc9_owned(t_clone_8);
          let t_clone_9 = Rc::clone(&t);
          let tmp_9 = tc10_owned(t_clone_9);
          let t_clone_10 = Rc::clone(&t);
          let tmp_10 = tc11_owned(t_clone_10);
          let t_clone_11 = Rc::clone(&t);
          let tmp_11 = tc12_owned(t_clone_11);
          let t_clone_12 = Rc::clone(&t);
          let tmp_12 = tc13_owned(t_clone_12);
          let t_clone_13 = Rc::clone(&t);
          let tmp_13 = tc14_owned(t_clone_13);
          let t_clone_14 = Rc::clone(&t);
          let tmp_14 = tc15_owned(t_clone_14);
          let t_clone_15 = Rc::clone(&t);
          let tmp_15 = tc16_owned(t_clone_15);
          let t_clone_16 = Rc::clone(&t);
          let tmp_16 = tc17_owned(t_clone_16);
          let t_clone_17 = Rc::clone(&t);
          let tmp_17 = tc18_owned(t_clone_17);
          let t_clone_18 = Rc::clone(&t);
          let tmp_18 = tc19_owned(t_clone_18);
          let t_clone_19 = Rc::clone(&t);
          let tmp_19 = tc20_owned(t_clone_19);
          let t_clone_20 = Rc::clone(&t);
          let tmp_20 = tc21_owned(t_clone_20);
          let t_clone_21 = Rc::clone(&t);
          let tmp_21 = tc22_owned(t_clone_21);
          let t_clone_22 = Rc::clone(&t);
          let tmp_22 = tc23_owned(t_clone_22);
          let t_clone_23 = Rc::clone(&t);
          Rc::new(tab { tc0: a_1, tc1: tmp, tc2: tmp_1, tc3: tmp_2, tc4: tmp_3, tc5: tmp_4, tc6: tmp_5, tc7: tmp_6, tc8: tmp_7, tc9: tmp_8, tc10: tmp_9, tc11: tmp_10, tc12: tmp_11, tc13: tmp_12, tc14: tmp_13, tc15: tmp_14, tc16: tmp_15, tc17: tmp_16, tc18: tmp_17, tc19: tmp_18, tc20: tmp_19, tc21: tmp_20, tc22: tmp_21, tc23: tmp_22, tc24: tc24_owned(t_clone_23), tc25: tc25_owned(t) })
        } else {
          if c < int63!(2) {
            let t_clone_24 = Rc::clone(&t);
            let tmp_23 = tc0_owned(t_clone_24);
            let t_clone_25 = Rc::clone(&t);
            let tmp_24 = tc2_owned(t_clone_25);
            let t_clone_26 = Rc::clone(&t);
            let tmp_25 = tc3_owned(t_clone_26);
            let t_clone_27 = Rc::clone(&t);
            let tmp_26 = tc4_owned(t_clone_27);
            let t_clone_28 = Rc::clone(&t);
            let tmp_27 = tc5_owned(t_clone_28);
            let t_clone_29 = Rc::clone(&t);
            let tmp_28 = tc6_owned(t_clone_29);
            let t_clone_30 = Rc::clone(&t);
            let tmp_29 = tc7_owned(t_clone_30);
            let t_clone_31 = Rc::clone(&t);
            let tmp_30 = tc8_owned(t_clone_31);
            let t_clone_32 = Rc::clone(&t);
            let tmp_31 = tc9_owned(t_clone_32);
            let t_clone_33 = Rc::clone(&t);
            let tmp_32 = tc10_owned(t_clone_33);
            let t_clone_34 = Rc::clone(&t);
            let tmp_33 = tc11_owned(t_clone_34);
            let t_clone_35 = Rc::clone(&t);
            let tmp_34 = tc12_owned(t_clone_35);
            let t_clone_36 = Rc::clone(&t);
            let tmp_35 = tc13_owned(t_clone_36);
            let t_clone_37 = Rc::clone(&t);
            let tmp_36 = tc14_owned(t_clone_37);
            let t_clone_38 = Rc::clone(&t);
            let tmp_37 = tc15_owned(t_clone_38);
            let t_clone_39 = Rc::clone(&t);
            let tmp_38 = tc16_owned(t_clone_39);
            let t_clone_40 = Rc::clone(&t);
            let tmp_39 = tc17_owned(t_clone_40);
            let t_clone_41 = Rc::clone(&t);
            let tmp_40 = tc18_owned(t_clone_41);
            let t_clone_42 = Rc::clone(&t);
            let tmp_41 = tc19_owned(t_clone_42);
            let t_clone_43 = Rc::clone(&t);
            let tmp_42 = tc20_owned(t_clone_43);
            let t_clone_44 = Rc::clone(&t);
            let tmp_43 = tc21_owned(t_clone_44);
            let t_clone_45 = Rc::clone(&t);
            let tmp_44 = tc22_owned(t_clone_45);
            let t_clone_46 = Rc::clone(&t);
            let tmp_45 = tc23_owned(t_clone_46);
            let t_clone_47 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_23, tc1: a_1, tc2: tmp_24, tc3: tmp_25, tc4: tmp_26, tc5: tmp_27, tc6: tmp_28, tc7: tmp_29, tc8: tmp_30, tc9: tmp_31, tc10: tmp_32, tc11: tmp_33, tc12: tmp_34, tc13: tmp_35, tc14: tmp_36, tc15: tmp_37, tc16: tmp_38, tc17: tmp_39, tc18: tmp_40, tc19: tmp_41, tc20: tmp_42, tc21: tmp_43, tc22: tmp_44, tc23: tmp_45, tc24: tc24_owned(t_clone_47), tc25: tc25_owned(t) })
          } else {
            let t_clone_48 = Rc::clone(&t);
            let tmp_46 = tc0_owned(t_clone_48);
            let t_clone_49 = Rc::clone(&t);
            let tmp_47 = tc1_owned(t_clone_49);
            let t_clone_50 = Rc::clone(&t);
            let tmp_48 = tc3_owned(t_clone_50);
            let t_clone_51 = Rc::clone(&t);
            let tmp_49 = tc4_owned(t_clone_51);
            let t_clone_52 = Rc::clone(&t);
            let tmp_50 = tc5_owned(t_clone_52);
            let t_clone_53 = Rc::clone(&t);
            let tmp_51 = tc6_owned(t_clone_53);
            let t_clone_54 = Rc::clone(&t);
            let tmp_52 = tc7_owned(t_clone_54);
            let t_clone_55 = Rc::clone(&t);
            let tmp_53 = tc8_owned(t_clone_55);
            let t_clone_56 = Rc::clone(&t);
            let tmp_54 = tc9_owned(t_clone_56);
            let t_clone_57 = Rc::clone(&t);
            let tmp_55 = tc10_owned(t_clone_57);
            let t_clone_58 = Rc::clone(&t);
            let tmp_56 = tc11_owned(t_clone_58);
            let t_clone_59 = Rc::clone(&t);
            let tmp_57 = tc12_owned(t_clone_59);
            let t_clone_60 = Rc::clone(&t);
            let tmp_58 = tc13_owned(t_clone_60);
            let t_clone_61 = Rc::clone(&t);
            let tmp_59 = tc14_owned(t_clone_61);
            let t_clone_62 = Rc::clone(&t);
            let tmp_60 = tc15_owned(t_clone_62);
            let t_clone_63 = Rc::clone(&t);
            let tmp_61 = tc16_owned(t_clone_63);
            let t_clone_64 = Rc::clone(&t);
            let tmp_62 = tc17_owned(t_clone_64);
            let t_clone_65 = Rc::clone(&t);
            let tmp_63 = tc18_owned(t_clone_65);
            let t_clone_66 = Rc::clone(&t);
            let tmp_64 = tc19_owned(t_clone_66);
            let t_clone_67 = Rc::clone(&t);
            let tmp_65 = tc20_owned(t_clone_67);
            let t_clone_68 = Rc::clone(&t);
            let tmp_66 = tc21_owned(t_clone_68);
            let t_clone_69 = Rc::clone(&t);
            let tmp_67 = tc22_owned(t_clone_69);
            let t_clone_70 = Rc::clone(&t);
            let tmp_68 = tc23_owned(t_clone_70);
            let t_clone_71 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_46, tc1: tmp_47, tc2: a_1, tc3: tmp_48, tc4: tmp_49, tc5: tmp_50, tc6: tmp_51, tc7: tmp_52, tc8: tmp_53, tc9: tmp_54, tc10: tmp_55, tc11: tmp_56, tc12: tmp_57, tc13: tmp_58, tc14: tmp_59, tc15: tmp_60, tc16: tmp_61, tc17: tmp_62, tc18: tmp_63, tc19: tmp_64, tc20: tmp_65, tc21: tmp_66, tc22: tmp_67, tc23: tmp_68, tc24: tc24_owned(t_clone_71), tc25: tc25_owned(t) })
          }
        }
      } else {
        if c < int63!(4) {
          let t_clone_72 = Rc::clone(&t);
          let tmp_69 = tc0_owned(t_clone_72);
          let t_clone_73 = Rc::clone(&t);
          let tmp_70 = tc1_owned(t_clone_73);
          let t_clone_74 = Rc::clone(&t);
          let tmp_71 = tc2_owned(t_clone_74);
          let t_clone_75 = Rc::clone(&t);
          let tmp_72 = tc4_owned(t_clone_75);
          let t_clone_76 = Rc::clone(&t);
          let tmp_73 = tc5_owned(t_clone_76);
          let t_clone_77 = Rc::clone(&t);
          let tmp_74 = tc6_owned(t_clone_77);
          let t_clone_78 = Rc::clone(&t);
          let tmp_75 = tc7_owned(t_clone_78);
          let t_clone_79 = Rc::clone(&t);
          let tmp_76 = tc8_owned(t_clone_79);
          let t_clone_80 = Rc::clone(&t);
          let tmp_77 = tc9_owned(t_clone_80);
          let t_clone_81 = Rc::clone(&t);
          let tmp_78 = tc10_owned(t_clone_81);
          let t_clone_82 = Rc::clone(&t);
          let tmp_79 = tc11_owned(t_clone_82);
          let t_clone_83 = Rc::clone(&t);
          let tmp_80 = tc12_owned(t_clone_83);
          let t_clone_84 = Rc::clone(&t);
          let tmp_81 = tc13_owned(t_clone_84);
          let t_clone_85 = Rc::clone(&t);
          let tmp_82 = tc14_owned(t_clone_85);
          let t_clone_86 = Rc::clone(&t);
          let tmp_83 = tc15_owned(t_clone_86);
          let t_clone_87 = Rc::clone(&t);
          let tmp_84 = tc16_owned(t_clone_87);
          let t_clone_88 = Rc::clone(&t);
          let tmp_85 = tc17_owned(t_clone_88);
          let t_clone_89 = Rc::clone(&t);
          let tmp_86 = tc18_owned(t_clone_89);
          let t_clone_90 = Rc::clone(&t);
          let tmp_87 = tc19_owned(t_clone_90);
          let t_clone_91 = Rc::clone(&t);
          let tmp_88 = tc20_owned(t_clone_91);
          let t_clone_92 = Rc::clone(&t);
          let tmp_89 = tc21_owned(t_clone_92);
          let t_clone_93 = Rc::clone(&t);
          let tmp_90 = tc22_owned(t_clone_93);
          let t_clone_94 = Rc::clone(&t);
          let tmp_91 = tc23_owned(t_clone_94);
          let t_clone_95 = Rc::clone(&t);
          Rc::new(tab { tc0: tmp_69, tc1: tmp_70, tc2: tmp_71, tc3: a_1, tc4: tmp_72, tc5: tmp_73, tc6: tmp_74, tc7: tmp_75, tc8: tmp_76, tc9: tmp_77, tc10: tmp_78, tc11: tmp_79, tc12: tmp_80, tc13: tmp_81, tc14: tmp_82, tc15: tmp_83, tc16: tmp_84, tc17: tmp_85, tc18: tmp_86, tc19: tmp_87, tc20: tmp_88, tc21: tmp_89, tc22: tmp_90, tc23: tmp_91, tc24: tc24_owned(t_clone_95), tc25: tc25_owned(t) })
        } else {
          if c < int63!(5) {
            let t_clone_96 = Rc::clone(&t);
            let tmp_92 = tc0_owned(t_clone_96);
            let t_clone_97 = Rc::clone(&t);
            let tmp_93 = tc1_owned(t_clone_97);
            let t_clone_98 = Rc::clone(&t);
            let tmp_94 = tc2_owned(t_clone_98);
            let t_clone_99 = Rc::clone(&t);
            let tmp_95 = tc3_owned(t_clone_99);
            let t_clone_100 = Rc::clone(&t);
            let tmp_96 = tc5_owned(t_clone_100);
            let t_clone_101 = Rc::clone(&t);
            let tmp_97 = tc6_owned(t_clone_101);
            let t_clone_102 = Rc::clone(&t);
            let tmp_98 = tc7_owned(t_clone_102);
            let t_clone_103 = Rc::clone(&t);
            let tmp_99 = tc8_owned(t_clone_103);
            let t_clone_104 = Rc::clone(&t);
            let tmp_100 = tc9_owned(t_clone_104);
            let t_clone_105 = Rc::clone(&t);
            let tmp_101 = tc10_owned(t_clone_105);
            let t_clone_106 = Rc::clone(&t);
            let tmp_102 = tc11_owned(t_clone_106);
            let t_clone_107 = Rc::clone(&t);
            let tmp_103 = tc12_owned(t_clone_107);
            let t_clone_108 = Rc::clone(&t);
            let tmp_104 = tc13_owned(t_clone_108);
            let t_clone_109 = Rc::clone(&t);
            let tmp_105 = tc14_owned(t_clone_109);
            let t_clone_110 = Rc::clone(&t);
            let tmp_106 = tc15_owned(t_clone_110);
            let t_clone_111 = Rc::clone(&t);
            let tmp_107 = tc16_owned(t_clone_111);
            let t_clone_112 = Rc::clone(&t);
            let tmp_108 = tc17_owned(t_clone_112);
            let t_clone_113 = Rc::clone(&t);
            let tmp_109 = tc18_owned(t_clone_113);
            let t_clone_114 = Rc::clone(&t);
            let tmp_110 = tc19_owned(t_clone_114);
            let t_clone_115 = Rc::clone(&t);
            let tmp_111 = tc20_owned(t_clone_115);
            let t_clone_116 = Rc::clone(&t);
            let tmp_112 = tc21_owned(t_clone_116);
            let t_clone_117 = Rc::clone(&t);
            let tmp_113 = tc22_owned(t_clone_117);
            let t_clone_118 = Rc::clone(&t);
            let tmp_114 = tc23_owned(t_clone_118);
            let t_clone_119 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_92, tc1: tmp_93, tc2: tmp_94, tc3: tmp_95, tc4: a_1, tc5: tmp_96, tc6: tmp_97, tc7: tmp_98, tc8: tmp_99, tc9: tmp_100, tc10: tmp_101, tc11: tmp_102, tc12: tmp_103, tc13: tmp_104, tc14: tmp_105, tc15: tmp_106, tc16: tmp_107, tc17: tmp_108, tc18: tmp_109, tc19: tmp_110, tc20: tmp_111, tc21: tmp_112, tc22: tmp_113, tc23: tmp_114, tc24: tc24_owned(t_clone_119), tc25: tc25_owned(t) })
          } else {
            let t_clone_120 = Rc::clone(&t);
            let tmp_115 = tc0_owned(t_clone_120);
            let t_clone_121 = Rc::clone(&t);
            let tmp_116 = tc1_owned(t_clone_121);
            let t_clone_122 = Rc::clone(&t);
            let tmp_117 = tc2_owned(t_clone_122);
            let t_clone_123 = Rc::clone(&t);
            let tmp_118 = tc3_owned(t_clone_123);
            let t_clone_124 = Rc::clone(&t);
            let tmp_119 = tc4_owned(t_clone_124);
            let t_clone_125 = Rc::clone(&t);
            let tmp_120 = tc6_owned(t_clone_125);
            let t_clone_126 = Rc::clone(&t);
            let tmp_121 = tc7_owned(t_clone_126);
            let t_clone_127 = Rc::clone(&t);
            let tmp_122 = tc8_owned(t_clone_127);
            let t_clone_128 = Rc::clone(&t);
            let tmp_123 = tc9_owned(t_clone_128);
            let t_clone_129 = Rc::clone(&t);
            let tmp_124 = tc10_owned(t_clone_129);
            let t_clone_130 = Rc::clone(&t);
            let tmp_125 = tc11_owned(t_clone_130);
            let t_clone_131 = Rc::clone(&t);
            let tmp_126 = tc12_owned(t_clone_131);
            let t_clone_132 = Rc::clone(&t);
            let tmp_127 = tc13_owned(t_clone_132);
            let t_clone_133 = Rc::clone(&t);
            let tmp_128 = tc14_owned(t_clone_133);
            let t_clone_134 = Rc::clone(&t);
            let tmp_129 = tc15_owned(t_clone_134);
            let t_clone_135 = Rc::clone(&t);
            let tmp_130 = tc16_owned(t_clone_135);
            let t_clone_136 = Rc::clone(&t);
            let tmp_131 = tc17_owned(t_clone_136);
            let t_clone_137 = Rc::clone(&t);
            let tmp_132 = tc18_owned(t_clone_137);
            let t_clone_138 = Rc::clone(&t);
            let tmp_133 = tc19_owned(t_clone_138);
            let t_clone_139 = Rc::clone(&t);
            let tmp_134 = tc20_owned(t_clone_139);
            let t_clone_140 = Rc::clone(&t);
            let tmp_135 = tc21_owned(t_clone_140);
            let t_clone_141 = Rc::clone(&t);
            let tmp_136 = tc22_owned(t_clone_141);
            let t_clone_142 = Rc::clone(&t);
            let tmp_137 = tc23_owned(t_clone_142);
            let t_clone_143 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_115, tc1: tmp_116, tc2: tmp_117, tc3: tmp_118, tc4: tmp_119, tc5: a_1, tc6: tmp_120, tc7: tmp_121, tc8: tmp_122, tc9: tmp_123, tc10: tmp_124, tc11: tmp_125, tc12: tmp_126, tc13: tmp_127, tc14: tmp_128, tc15: tmp_129, tc16: tmp_130, tc17: tmp_131, tc18: tmp_132, tc19: tmp_133, tc20: tmp_134, tc21: tmp_135, tc22: tmp_136, tc23: tmp_137, tc24: tc24_owned(t_clone_143), tc25: tc25_owned(t) })
          }
        }
      }
    } else {
      if c < int63!(9) {
        if c < int63!(7) {
          let t_clone_144 = Rc::clone(&t);
          let tmp_138 = tc0_owned(t_clone_144);
          let t_clone_145 = Rc::clone(&t);
          let tmp_139 = tc1_owned(t_clone_145);
          let t_clone_146 = Rc::clone(&t);
          let tmp_140 = tc2_owned(t_clone_146);
          let t_clone_147 = Rc::clone(&t);
          let tmp_141 = tc3_owned(t_clone_147);
          let t_clone_148 = Rc::clone(&t);
          let tmp_142 = tc4_owned(t_clone_148);
          let t_clone_149 = Rc::clone(&t);
          let tmp_143 = tc5_owned(t_clone_149);
          let t_clone_150 = Rc::clone(&t);
          let tmp_144 = tc7_owned(t_clone_150);
          let t_clone_151 = Rc::clone(&t);
          let tmp_145 = tc8_owned(t_clone_151);
          let t_clone_152 = Rc::clone(&t);
          let tmp_146 = tc9_owned(t_clone_152);
          let t_clone_153 = Rc::clone(&t);
          let tmp_147 = tc10_owned(t_clone_153);
          let t_clone_154 = Rc::clone(&t);
          let tmp_148 = tc11_owned(t_clone_154);
          let t_clone_155 = Rc::clone(&t);
          let tmp_149 = tc12_owned(t_clone_155);
          let t_clone_156 = Rc::clone(&t);
          let tmp_150 = tc13_owned(t_clone_156);
          let t_clone_157 = Rc::clone(&t);
          let tmp_151 = tc14_owned(t_clone_157);
          let t_clone_158 = Rc::clone(&t);
          let tmp_152 = tc15_owned(t_clone_158);
          let t_clone_159 = Rc::clone(&t);
          let tmp_153 = tc16_owned(t_clone_159);
          let t_clone_160 = Rc::clone(&t);
          let tmp_154 = tc17_owned(t_clone_160);
          let t_clone_161 = Rc::clone(&t);
          let tmp_155 = tc18_owned(t_clone_161);
          let t_clone_162 = Rc::clone(&t);
          let tmp_156 = tc19_owned(t_clone_162);
          let t_clone_163 = Rc::clone(&t);
          let tmp_157 = tc20_owned(t_clone_163);
          let t_clone_164 = Rc::clone(&t);
          let tmp_158 = tc21_owned(t_clone_164);
          let t_clone_165 = Rc::clone(&t);
          let tmp_159 = tc22_owned(t_clone_165);
          let t_clone_166 = Rc::clone(&t);
          let tmp_160 = tc23_owned(t_clone_166);
          let t_clone_167 = Rc::clone(&t);
          Rc::new(tab { tc0: tmp_138, tc1: tmp_139, tc2: tmp_140, tc3: tmp_141, tc4: tmp_142, tc5: tmp_143, tc6: a_1, tc7: tmp_144, tc8: tmp_145, tc9: tmp_146, tc10: tmp_147, tc11: tmp_148, tc12: tmp_149, tc13: tmp_150, tc14: tmp_151, tc15: tmp_152, tc16: tmp_153, tc17: tmp_154, tc18: tmp_155, tc19: tmp_156, tc20: tmp_157, tc21: tmp_158, tc22: tmp_159, tc23: tmp_160, tc24: tc24_owned(t_clone_167), tc25: tc25_owned(t) })
        } else {
          if c < int63!(8) {
            let t_clone_168 = Rc::clone(&t);
            let tmp_161 = tc0_owned(t_clone_168);
            let t_clone_169 = Rc::clone(&t);
            let tmp_162 = tc1_owned(t_clone_169);
            let t_clone_170 = Rc::clone(&t);
            let tmp_163 = tc2_owned(t_clone_170);
            let t_clone_171 = Rc::clone(&t);
            let tmp_164 = tc3_owned(t_clone_171);
            let t_clone_172 = Rc::clone(&t);
            let tmp_165 = tc4_owned(t_clone_172);
            let t_clone_173 = Rc::clone(&t);
            let tmp_166 = tc5_owned(t_clone_173);
            let t_clone_174 = Rc::clone(&t);
            let tmp_167 = tc6_owned(t_clone_174);
            let t_clone_175 = Rc::clone(&t);
            let tmp_168 = tc8_owned(t_clone_175);
            let t_clone_176 = Rc::clone(&t);
            let tmp_169 = tc9_owned(t_clone_176);
            let t_clone_177 = Rc::clone(&t);
            let tmp_170 = tc10_owned(t_clone_177);
            let t_clone_178 = Rc::clone(&t);
            let tmp_171 = tc11_owned(t_clone_178);
            let t_clone_179 = Rc::clone(&t);
            let tmp_172 = tc12_owned(t_clone_179);
            let t_clone_180 = Rc::clone(&t);
            let tmp_173 = tc13_owned(t_clone_180);
            let t_clone_181 = Rc::clone(&t);
            let tmp_174 = tc14_owned(t_clone_181);
            let t_clone_182 = Rc::clone(&t);
            let tmp_175 = tc15_owned(t_clone_182);
            let t_clone_183 = Rc::clone(&t);
            let tmp_176 = tc16_owned(t_clone_183);
            let t_clone_184 = Rc::clone(&t);
            let tmp_177 = tc17_owned(t_clone_184);
            let t_clone_185 = Rc::clone(&t);
            let tmp_178 = tc18_owned(t_clone_185);
            let t_clone_186 = Rc::clone(&t);
            let tmp_179 = tc19_owned(t_clone_186);
            let t_clone_187 = Rc::clone(&t);
            let tmp_180 = tc20_owned(t_clone_187);
            let t_clone_188 = Rc::clone(&t);
            let tmp_181 = tc21_owned(t_clone_188);
            let t_clone_189 = Rc::clone(&t);
            let tmp_182 = tc22_owned(t_clone_189);
            let t_clone_190 = Rc::clone(&t);
            let tmp_183 = tc23_owned(t_clone_190);
            let t_clone_191 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_161, tc1: tmp_162, tc2: tmp_163, tc3: tmp_164, tc4: tmp_165, tc5: tmp_166, tc6: tmp_167, tc7: a_1, tc8: tmp_168, tc9: tmp_169, tc10: tmp_170, tc11: tmp_171, tc12: tmp_172, tc13: tmp_173, tc14: tmp_174, tc15: tmp_175, tc16: tmp_176, tc17: tmp_177, tc18: tmp_178, tc19: tmp_179, tc20: tmp_180, tc21: tmp_181, tc22: tmp_182, tc23: tmp_183, tc24: tc24_owned(t_clone_191), tc25: tc25_owned(t) })
          } else {
            let t_clone_192 = Rc::clone(&t);
            let tmp_184 = tc0_owned(t_clone_192);
            let t_clone_193 = Rc::clone(&t);
            let tmp_185 = tc1_owned(t_clone_193);
            let t_clone_194 = Rc::clone(&t);
            let tmp_186 = tc2_owned(t_clone_194);
            let t_clone_195 = Rc::clone(&t);
            let tmp_187 = tc3_owned(t_clone_195);
            let t_clone_196 = Rc::clone(&t);
            let tmp_188 = tc4_owned(t_clone_196);
            let t_clone_197 = Rc::clone(&t);
            let tmp_189 = tc5_owned(t_clone_197);
            let t_clone_198 = Rc::clone(&t);
            let tmp_190 = tc6_owned(t_clone_198);
            let t_clone_199 = Rc::clone(&t);
            let tmp_191 = tc7_owned(t_clone_199);
            let t_clone_200 = Rc::clone(&t);
            let tmp_192 = tc9_owned(t_clone_200);
            let t_clone_201 = Rc::clone(&t);
            let tmp_193 = tc10_owned(t_clone_201);
            let t_clone_202 = Rc::clone(&t);
            let tmp_194 = tc11_owned(t_clone_202);
            let t_clone_203 = Rc::clone(&t);
            let tmp_195 = tc12_owned(t_clone_203);
            let t_clone_204 = Rc::clone(&t);
            let tmp_196 = tc13_owned(t_clone_204);
            let t_clone_205 = Rc::clone(&t);
            let tmp_197 = tc14_owned(t_clone_205);
            let t_clone_206 = Rc::clone(&t);
            let tmp_198 = tc15_owned(t_clone_206);
            let t_clone_207 = Rc::clone(&t);
            let tmp_199 = tc16_owned(t_clone_207);
            let t_clone_208 = Rc::clone(&t);
            let tmp_200 = tc17_owned(t_clone_208);
            let t_clone_209 = Rc::clone(&t);
            let tmp_201 = tc18_owned(t_clone_209);
            let t_clone_210 = Rc::clone(&t);
            let tmp_202 = tc19_owned(t_clone_210);
            let t_clone_211 = Rc::clone(&t);
            let tmp_203 = tc20_owned(t_clone_211);
            let t_clone_212 = Rc::clone(&t);
            let tmp_204 = tc21_owned(t_clone_212);
            let t_clone_213 = Rc::clone(&t);
            let tmp_205 = tc22_owned(t_clone_213);
            let t_clone_214 = Rc::clone(&t);
            let tmp_206 = tc23_owned(t_clone_214);
            let t_clone_215 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_184, tc1: tmp_185, tc2: tmp_186, tc3: tmp_187, tc4: tmp_188, tc5: tmp_189, tc6: tmp_190, tc7: tmp_191, tc8: a_1, tc9: tmp_192, tc10: tmp_193, tc11: tmp_194, tc12: tmp_195, tc13: tmp_196, tc14: tmp_197, tc15: tmp_198, tc16: tmp_199, tc17: tmp_200, tc18: tmp_201, tc19: tmp_202, tc20: tmp_203, tc21: tmp_204, tc22: tmp_205, tc23: tmp_206, tc24: tc24_owned(t_clone_215), tc25: tc25_owned(t) })
          }
        }
      } else {
        if c < int63!(11) {
          if c < int63!(10) {
            let t_clone_216 = Rc::clone(&t);
            let tmp_207 = tc0_owned(t_clone_216);
            let t_clone_217 = Rc::clone(&t);
            let tmp_208 = tc1_owned(t_clone_217);
            let t_clone_218 = Rc::clone(&t);
            let tmp_209 = tc2_owned(t_clone_218);
            let t_clone_219 = Rc::clone(&t);
            let tmp_210 = tc3_owned(t_clone_219);
            let t_clone_220 = Rc::clone(&t);
            let tmp_211 = tc4_owned(t_clone_220);
            let t_clone_221 = Rc::clone(&t);
            let tmp_212 = tc5_owned(t_clone_221);
            let t_clone_222 = Rc::clone(&t);
            let tmp_213 = tc6_owned(t_clone_222);
            let t_clone_223 = Rc::clone(&t);
            let tmp_214 = tc7_owned(t_clone_223);
            let t_clone_224 = Rc::clone(&t);
            let tmp_215 = tc8_owned(t_clone_224);
            let t_clone_225 = Rc::clone(&t);
            let tmp_216 = tc10_owned(t_clone_225);
            let t_clone_226 = Rc::clone(&t);
            let tmp_217 = tc11_owned(t_clone_226);
            let t_clone_227 = Rc::clone(&t);
            let tmp_218 = tc12_owned(t_clone_227);
            let t_clone_228 = Rc::clone(&t);
            let tmp_219 = tc13_owned(t_clone_228);
            let t_clone_229 = Rc::clone(&t);
            let tmp_220 = tc14_owned(t_clone_229);
            let t_clone_230 = Rc::clone(&t);
            let tmp_221 = tc15_owned(t_clone_230);
            let t_clone_231 = Rc::clone(&t);
            let tmp_222 = tc16_owned(t_clone_231);
            let t_clone_232 = Rc::clone(&t);
            let tmp_223 = tc17_owned(t_clone_232);
            let t_clone_233 = Rc::clone(&t);
            let tmp_224 = tc18_owned(t_clone_233);
            let t_clone_234 = Rc::clone(&t);
            let tmp_225 = tc19_owned(t_clone_234);
            let t_clone_235 = Rc::clone(&t);
            let tmp_226 = tc20_owned(t_clone_235);
            let t_clone_236 = Rc::clone(&t);
            let tmp_227 = tc21_owned(t_clone_236);
            let t_clone_237 = Rc::clone(&t);
            let tmp_228 = tc22_owned(t_clone_237);
            let t_clone_238 = Rc::clone(&t);
            let tmp_229 = tc23_owned(t_clone_238);
            let t_clone_239 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_207, tc1: tmp_208, tc2: tmp_209, tc3: tmp_210, tc4: tmp_211, tc5: tmp_212, tc6: tmp_213, tc7: tmp_214, tc8: tmp_215, tc9: a_1, tc10: tmp_216, tc11: tmp_217, tc12: tmp_218, tc13: tmp_219, tc14: tmp_220, tc15: tmp_221, tc16: tmp_222, tc17: tmp_223, tc18: tmp_224, tc19: tmp_225, tc20: tmp_226, tc21: tmp_227, tc22: tmp_228, tc23: tmp_229, tc24: tc24_owned(t_clone_239), tc25: tc25_owned(t) })
          } else {
            let t_clone_240 = Rc::clone(&t);
            let tmp_230 = tc0_owned(t_clone_240);
            let t_clone_241 = Rc::clone(&t);
            let tmp_231 = tc1_owned(t_clone_241);
            let t_clone_242 = Rc::clone(&t);
            let tmp_232 = tc2_owned(t_clone_242);
            let t_clone_243 = Rc::clone(&t);
            let tmp_233 = tc3_owned(t_clone_243);
            let t_clone_244 = Rc::clone(&t);
            let tmp_234 = tc4_owned(t_clone_244);
            let t_clone_245 = Rc::clone(&t);
            let tmp_235 = tc5_owned(t_clone_245);
            let t_clone_246 = Rc::clone(&t);
            let tmp_236 = tc6_owned(t_clone_246);
            let t_clone_247 = Rc::clone(&t);
            let tmp_237 = tc7_owned(t_clone_247);
            let t_clone_248 = Rc::clone(&t);
            let tmp_238 = tc8_owned(t_clone_248);
            let t_clone_249 = Rc::clone(&t);
            let tmp_239 = tc9_owned(t_clone_249);
            let t_clone_250 = Rc::clone(&t);
            let tmp_240 = tc11_owned(t_clone_250);
            let t_clone_251 = Rc::clone(&t);
            let tmp_241 = tc12_owned(t_clone_251);
            let t_clone_252 = Rc::clone(&t);
            let tmp_242 = tc13_owned(t_clone_252);
            let t_clone_253 = Rc::clone(&t);
            let tmp_243 = tc14_owned(t_clone_253);
            let t_clone_254 = Rc::clone(&t);
            let tmp_244 = tc15_owned(t_clone_254);
            let t_clone_255 = Rc::clone(&t);
            let tmp_245 = tc16_owned(t_clone_255);
            let t_clone_256 = Rc::clone(&t);
            let tmp_246 = tc17_owned(t_clone_256);
            let t_clone_257 = Rc::clone(&t);
            let tmp_247 = tc18_owned(t_clone_257);
            let t_clone_258 = Rc::clone(&t);
            let tmp_248 = tc19_owned(t_clone_258);
            let t_clone_259 = Rc::clone(&t);
            let tmp_249 = tc20_owned(t_clone_259);
            let t_clone_260 = Rc::clone(&t);
            let tmp_250 = tc21_owned(t_clone_260);
            let t_clone_261 = Rc::clone(&t);
            let tmp_251 = tc22_owned(t_clone_261);
            let t_clone_262 = Rc::clone(&t);
            let tmp_252 = tc23_owned(t_clone_262);
            let t_clone_263 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_230, tc1: tmp_231, tc2: tmp_232, tc3: tmp_233, tc4: tmp_234, tc5: tmp_235, tc6: tmp_236, tc7: tmp_237, tc8: tmp_238, tc9: tmp_239, tc10: a_1, tc11: tmp_240, tc12: tmp_241, tc13: tmp_242, tc14: tmp_243, tc15: tmp_244, tc16: tmp_245, tc17: tmp_246, tc18: tmp_247, tc19: tmp_248, tc20: tmp_249, tc21: tmp_250, tc22: tmp_251, tc23: tmp_252, tc24: tc24_owned(t_clone_263), tc25: tc25_owned(t) })
          }
        } else {
          if c < int63!(12) {
            let t_clone_264 = Rc::clone(&t);
            let tmp_253 = tc0_owned(t_clone_264);
            let t_clone_265 = Rc::clone(&t);
            let tmp_254 = tc1_owned(t_clone_265);
            let t_clone_266 = Rc::clone(&t);
            let tmp_255 = tc2_owned(t_clone_266);
            let t_clone_267 = Rc::clone(&t);
            let tmp_256 = tc3_owned(t_clone_267);
            let t_clone_268 = Rc::clone(&t);
            let tmp_257 = tc4_owned(t_clone_268);
            let t_clone_269 = Rc::clone(&t);
            let tmp_258 = tc5_owned(t_clone_269);
            let t_clone_270 = Rc::clone(&t);
            let tmp_259 = tc6_owned(t_clone_270);
            let t_clone_271 = Rc::clone(&t);
            let tmp_260 = tc7_owned(t_clone_271);
            let t_clone_272 = Rc::clone(&t);
            let tmp_261 = tc8_owned(t_clone_272);
            let t_clone_273 = Rc::clone(&t);
            let tmp_262 = tc9_owned(t_clone_273);
            let t_clone_274 = Rc::clone(&t);
            let tmp_263 = tc10_owned(t_clone_274);
            let t_clone_275 = Rc::clone(&t);
            let tmp_264 = tc12_owned(t_clone_275);
            let t_clone_276 = Rc::clone(&t);
            let tmp_265 = tc13_owned(t_clone_276);
            let t_clone_277 = Rc::clone(&t);
            let tmp_266 = tc14_owned(t_clone_277);
            let t_clone_278 = Rc::clone(&t);
            let tmp_267 = tc15_owned(t_clone_278);
            let t_clone_279 = Rc::clone(&t);
            let tmp_268 = tc16_owned(t_clone_279);
            let t_clone_280 = Rc::clone(&t);
            let tmp_269 = tc17_owned(t_clone_280);
            let t_clone_281 = Rc::clone(&t);
            let tmp_270 = tc18_owned(t_clone_281);
            let t_clone_282 = Rc::clone(&t);
            let tmp_271 = tc19_owned(t_clone_282);
            let t_clone_283 = Rc::clone(&t);
            let tmp_272 = tc20_owned(t_clone_283);
            let t_clone_284 = Rc::clone(&t);
            let tmp_273 = tc21_owned(t_clone_284);
            let t_clone_285 = Rc::clone(&t);
            let tmp_274 = tc22_owned(t_clone_285);
            let t_clone_286 = Rc::clone(&t);
            let tmp_275 = tc23_owned(t_clone_286);
            let t_clone_287 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_253, tc1: tmp_254, tc2: tmp_255, tc3: tmp_256, tc4: tmp_257, tc5: tmp_258, tc6: tmp_259, tc7: tmp_260, tc8: tmp_261, tc9: tmp_262, tc10: tmp_263, tc11: a_1, tc12: tmp_264, tc13: tmp_265, tc14: tmp_266, tc15: tmp_267, tc16: tmp_268, tc17: tmp_269, tc18: tmp_270, tc19: tmp_271, tc20: tmp_272, tc21: tmp_273, tc22: tmp_274, tc23: tmp_275, tc24: tc24_owned(t_clone_287), tc25: tc25_owned(t) })
          } else {
            let t_clone_288 = Rc::clone(&t);
            let tmp_276 = tc0_owned(t_clone_288);
            let t_clone_289 = Rc::clone(&t);
            let tmp_277 = tc1_owned(t_clone_289);
            let t_clone_290 = Rc::clone(&t);
            let tmp_278 = tc2_owned(t_clone_290);
            let t_clone_291 = Rc::clone(&t);
            let tmp_279 = tc3_owned(t_clone_291);
            let t_clone_292 = Rc::clone(&t);
            let tmp_280 = tc4_owned(t_clone_292);
            let t_clone_293 = Rc::clone(&t);
            let tmp_281 = tc5_owned(t_clone_293);
            let t_clone_294 = Rc::clone(&t);
            let tmp_282 = tc6_owned(t_clone_294);
            let t_clone_295 = Rc::clone(&t);
            let tmp_283 = tc7_owned(t_clone_295);
            let t_clone_296 = Rc::clone(&t);
            let tmp_284 = tc8_owned(t_clone_296);
            let t_clone_297 = Rc::clone(&t);
            let tmp_285 = tc9_owned(t_clone_297);
            let t_clone_298 = Rc::clone(&t);
            let tmp_286 = tc10_owned(t_clone_298);
            let t_clone_299 = Rc::clone(&t);
            let tmp_287 = tc11_owned(t_clone_299);
            let t_clone_300 = Rc::clone(&t);
            let tmp_288 = tc13_owned(t_clone_300);
            let t_clone_301 = Rc::clone(&t);
            let tmp_289 = tc14_owned(t_clone_301);
            let t_clone_302 = Rc::clone(&t);
            let tmp_290 = tc15_owned(t_clone_302);
            let t_clone_303 = Rc::clone(&t);
            let tmp_291 = tc16_owned(t_clone_303);
            let t_clone_304 = Rc::clone(&t);
            let tmp_292 = tc17_owned(t_clone_304);
            let t_clone_305 = Rc::clone(&t);
            let tmp_293 = tc18_owned(t_clone_305);
            let t_clone_306 = Rc::clone(&t);
            let tmp_294 = tc19_owned(t_clone_306);
            let t_clone_307 = Rc::clone(&t);
            let tmp_295 = tc20_owned(t_clone_307);
            let t_clone_308 = Rc::clone(&t);
            let tmp_296 = tc21_owned(t_clone_308);
            let t_clone_309 = Rc::clone(&t);
            let tmp_297 = tc22_owned(t_clone_309);
            let t_clone_310 = Rc::clone(&t);
            let tmp_298 = tc23_owned(t_clone_310);
            let t_clone_311 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_276, tc1: tmp_277, tc2: tmp_278, tc3: tmp_279, tc4: tmp_280, tc5: tmp_281, tc6: tmp_282, tc7: tmp_283, tc8: tmp_284, tc9: tmp_285, tc10: tmp_286, tc11: tmp_287, tc12: a_1, tc13: tmp_288, tc14: tmp_289, tc15: tmp_290, tc16: tmp_291, tc17: tmp_292, tc18: tmp_293, tc19: tmp_294, tc20: tmp_295, tc21: tmp_296, tc22: tmp_297, tc23: tmp_298, tc24: tc24_owned(t_clone_311), tc25: tc25_owned(t) })
          }
        }
      }
    }
  } else {
    if c < int63!(19) {
      if c < int63!(16) {
        if c < int63!(14) {
          let t_clone_312 = Rc::clone(&t);
          let tmp_299 = tc0_owned(t_clone_312);
          let t_clone_313 = Rc::clone(&t);
          let tmp_300 = tc1_owned(t_clone_313);
          let t_clone_314 = Rc::clone(&t);
          let tmp_301 = tc2_owned(t_clone_314);
          let t_clone_315 = Rc::clone(&t);
          let tmp_302 = tc3_owned(t_clone_315);
          let t_clone_316 = Rc::clone(&t);
          let tmp_303 = tc4_owned(t_clone_316);
          let t_clone_317 = Rc::clone(&t);
          let tmp_304 = tc5_owned(t_clone_317);
          let t_clone_318 = Rc::clone(&t);
          let tmp_305 = tc6_owned(t_clone_318);
          let t_clone_319 = Rc::clone(&t);
          let tmp_306 = tc7_owned(t_clone_319);
          let t_clone_320 = Rc::clone(&t);
          let tmp_307 = tc8_owned(t_clone_320);
          let t_clone_321 = Rc::clone(&t);
          let tmp_308 = tc9_owned(t_clone_321);
          let t_clone_322 = Rc::clone(&t);
          let tmp_309 = tc10_owned(t_clone_322);
          let t_clone_323 = Rc::clone(&t);
          let tmp_310 = tc11_owned(t_clone_323);
          let t_clone_324 = Rc::clone(&t);
          let tmp_311 = tc12_owned(t_clone_324);
          let t_clone_325 = Rc::clone(&t);
          let tmp_312 = tc14_owned(t_clone_325);
          let t_clone_326 = Rc::clone(&t);
          let tmp_313 = tc15_owned(t_clone_326);
          let t_clone_327 = Rc::clone(&t);
          let tmp_314 = tc16_owned(t_clone_327);
          let t_clone_328 = Rc::clone(&t);
          let tmp_315 = tc17_owned(t_clone_328);
          let t_clone_329 = Rc::clone(&t);
          let tmp_316 = tc18_owned(t_clone_329);
          let t_clone_330 = Rc::clone(&t);
          let tmp_317 = tc19_owned(t_clone_330);
          let t_clone_331 = Rc::clone(&t);
          let tmp_318 = tc20_owned(t_clone_331);
          let t_clone_332 = Rc::clone(&t);
          let tmp_319 = tc21_owned(t_clone_332);
          let t_clone_333 = Rc::clone(&t);
          let tmp_320 = tc22_owned(t_clone_333);
          let t_clone_334 = Rc::clone(&t);
          let tmp_321 = tc23_owned(t_clone_334);
          let t_clone_335 = Rc::clone(&t);
          Rc::new(tab { tc0: tmp_299, tc1: tmp_300, tc2: tmp_301, tc3: tmp_302, tc4: tmp_303, tc5: tmp_304, tc6: tmp_305, tc7: tmp_306, tc8: tmp_307, tc9: tmp_308, tc10: tmp_309, tc11: tmp_310, tc12: tmp_311, tc13: a_1, tc14: tmp_312, tc15: tmp_313, tc16: tmp_314, tc17: tmp_315, tc18: tmp_316, tc19: tmp_317, tc20: tmp_318, tc21: tmp_319, tc22: tmp_320, tc23: tmp_321, tc24: tc24_owned(t_clone_335), tc25: tc25_owned(t) })
        } else {
          if c < int63!(15) {
            let t_clone_336 = Rc::clone(&t);
            let tmp_322 = tc0_owned(t_clone_336);
            let t_clone_337 = Rc::clone(&t);
            let tmp_323 = tc1_owned(t_clone_337);
            let t_clone_338 = Rc::clone(&t);
            let tmp_324 = tc2_owned(t_clone_338);
            let t_clone_339 = Rc::clone(&t);
            let tmp_325 = tc3_owned(t_clone_339);
            let t_clone_340 = Rc::clone(&t);
            let tmp_326 = tc4_owned(t_clone_340);
            let t_clone_341 = Rc::clone(&t);
            let tmp_327 = tc5_owned(t_clone_341);
            let t_clone_342 = Rc::clone(&t);
            let tmp_328 = tc6_owned(t_clone_342);
            let t_clone_343 = Rc::clone(&t);
            let tmp_329 = tc7_owned(t_clone_343);
            let t_clone_344 = Rc::clone(&t);
            let tmp_330 = tc8_owned(t_clone_344);
            let t_clone_345 = Rc::clone(&t);
            let tmp_331 = tc9_owned(t_clone_345);
            let t_clone_346 = Rc::clone(&t);
            let tmp_332 = tc10_owned(t_clone_346);
            let t_clone_347 = Rc::clone(&t);
            let tmp_333 = tc11_owned(t_clone_347);
            let t_clone_348 = Rc::clone(&t);
            let tmp_334 = tc12_owned(t_clone_348);
            let t_clone_349 = Rc::clone(&t);
            let tmp_335 = tc13_owned(t_clone_349);
            let t_clone_350 = Rc::clone(&t);
            let tmp_336 = tc15_owned(t_clone_350);
            let t_clone_351 = Rc::clone(&t);
            let tmp_337 = tc16_owned(t_clone_351);
            let t_clone_352 = Rc::clone(&t);
            let tmp_338 = tc17_owned(t_clone_352);
            let t_clone_353 = Rc::clone(&t);
            let tmp_339 = tc18_owned(t_clone_353);
            let t_clone_354 = Rc::clone(&t);
            let tmp_340 = tc19_owned(t_clone_354);
            let t_clone_355 = Rc::clone(&t);
            let tmp_341 = tc20_owned(t_clone_355);
            let t_clone_356 = Rc::clone(&t);
            let tmp_342 = tc21_owned(t_clone_356);
            let t_clone_357 = Rc::clone(&t);
            let tmp_343 = tc22_owned(t_clone_357);
            let t_clone_358 = Rc::clone(&t);
            let tmp_344 = tc23_owned(t_clone_358);
            let t_clone_359 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_322, tc1: tmp_323, tc2: tmp_324, tc3: tmp_325, tc4: tmp_326, tc5: tmp_327, tc6: tmp_328, tc7: tmp_329, tc8: tmp_330, tc9: tmp_331, tc10: tmp_332, tc11: tmp_333, tc12: tmp_334, tc13: tmp_335, tc14: a_1, tc15: tmp_336, tc16: tmp_337, tc17: tmp_338, tc18: tmp_339, tc19: tmp_340, tc20: tmp_341, tc21: tmp_342, tc22: tmp_343, tc23: tmp_344, tc24: tc24_owned(t_clone_359), tc25: tc25_owned(t) })
          } else {
            let t_clone_360 = Rc::clone(&t);
            let tmp_345 = tc0_owned(t_clone_360);
            let t_clone_361 = Rc::clone(&t);
            let tmp_346 = tc1_owned(t_clone_361);
            let t_clone_362 = Rc::clone(&t);
            let tmp_347 = tc2_owned(t_clone_362);
            let t_clone_363 = Rc::clone(&t);
            let tmp_348 = tc3_owned(t_clone_363);
            let t_clone_364 = Rc::clone(&t);
            let tmp_349 = tc4_owned(t_clone_364);
            let t_clone_365 = Rc::clone(&t);
            let tmp_350 = tc5_owned(t_clone_365);
            let t_clone_366 = Rc::clone(&t);
            let tmp_351 = tc6_owned(t_clone_366);
            let t_clone_367 = Rc::clone(&t);
            let tmp_352 = tc7_owned(t_clone_367);
            let t_clone_368 = Rc::clone(&t);
            let tmp_353 = tc8_owned(t_clone_368);
            let t_clone_369 = Rc::clone(&t);
            let tmp_354 = tc9_owned(t_clone_369);
            let t_clone_370 = Rc::clone(&t);
            let tmp_355 = tc10_owned(t_clone_370);
            let t_clone_371 = Rc::clone(&t);
            let tmp_356 = tc11_owned(t_clone_371);
            let t_clone_372 = Rc::clone(&t);
            let tmp_357 = tc12_owned(t_clone_372);
            let t_clone_373 = Rc::clone(&t);
            let tmp_358 = tc13_owned(t_clone_373);
            let t_clone_374 = Rc::clone(&t);
            let tmp_359 = tc14_owned(t_clone_374);
            let t_clone_375 = Rc::clone(&t);
            let tmp_360 = tc16_owned(t_clone_375);
            let t_clone_376 = Rc::clone(&t);
            let tmp_361 = tc17_owned(t_clone_376);
            let t_clone_377 = Rc::clone(&t);
            let tmp_362 = tc18_owned(t_clone_377);
            let t_clone_378 = Rc::clone(&t);
            let tmp_363 = tc19_owned(t_clone_378);
            let t_clone_379 = Rc::clone(&t);
            let tmp_364 = tc20_owned(t_clone_379);
            let t_clone_380 = Rc::clone(&t);
            let tmp_365 = tc21_owned(t_clone_380);
            let t_clone_381 = Rc::clone(&t);
            let tmp_366 = tc22_owned(t_clone_381);
            let t_clone_382 = Rc::clone(&t);
            let tmp_367 = tc23_owned(t_clone_382);
            let t_clone_383 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_345, tc1: tmp_346, tc2: tmp_347, tc3: tmp_348, tc4: tmp_349, tc5: tmp_350, tc6: tmp_351, tc7: tmp_352, tc8: tmp_353, tc9: tmp_354, tc10: tmp_355, tc11: tmp_356, tc12: tmp_357, tc13: tmp_358, tc14: tmp_359, tc15: a_1, tc16: tmp_360, tc17: tmp_361, tc18: tmp_362, tc19: tmp_363, tc20: tmp_364, tc21: tmp_365, tc22: tmp_366, tc23: tmp_367, tc24: tc24_owned(t_clone_383), tc25: tc25_owned(t) })
          }
        }
      } else {
        if c < int63!(17) {
          let t_clone_384 = Rc::clone(&t);
          let tmp_368 = tc0_owned(t_clone_384);
          let t_clone_385 = Rc::clone(&t);
          let tmp_369 = tc1_owned(t_clone_385);
          let t_clone_386 = Rc::clone(&t);
          let tmp_370 = tc2_owned(t_clone_386);
          let t_clone_387 = Rc::clone(&t);
          let tmp_371 = tc3_owned(t_clone_387);
          let t_clone_388 = Rc::clone(&t);
          let tmp_372 = tc4_owned(t_clone_388);
          let t_clone_389 = Rc::clone(&t);
          let tmp_373 = tc5_owned(t_clone_389);
          let t_clone_390 = Rc::clone(&t);
          let tmp_374 = tc6_owned(t_clone_390);
          let t_clone_391 = Rc::clone(&t);
          let tmp_375 = tc7_owned(t_clone_391);
          let t_clone_392 = Rc::clone(&t);
          let tmp_376 = tc8_owned(t_clone_392);
          let t_clone_393 = Rc::clone(&t);
          let tmp_377 = tc9_owned(t_clone_393);
          let t_clone_394 = Rc::clone(&t);
          let tmp_378 = tc10_owned(t_clone_394);
          let t_clone_395 = Rc::clone(&t);
          let tmp_379 = tc11_owned(t_clone_395);
          let t_clone_396 = Rc::clone(&t);
          let tmp_380 = tc12_owned(t_clone_396);
          let t_clone_397 = Rc::clone(&t);
          let tmp_381 = tc13_owned(t_clone_397);
          let t_clone_398 = Rc::clone(&t);
          let tmp_382 = tc14_owned(t_clone_398);
          let t_clone_399 = Rc::clone(&t);
          let tmp_383 = tc15_owned(t_clone_399);
          let t_clone_400 = Rc::clone(&t);
          let tmp_384 = tc17_owned(t_clone_400);
          let t_clone_401 = Rc::clone(&t);
          let tmp_385 = tc18_owned(t_clone_401);
          let t_clone_402 = Rc::clone(&t);
          let tmp_386 = tc19_owned(t_clone_402);
          let t_clone_403 = Rc::clone(&t);
          let tmp_387 = tc20_owned(t_clone_403);
          let t_clone_404 = Rc::clone(&t);
          let tmp_388 = tc21_owned(t_clone_404);
          let t_clone_405 = Rc::clone(&t);
          let tmp_389 = tc22_owned(t_clone_405);
          let t_clone_406 = Rc::clone(&t);
          let tmp_390 = tc23_owned(t_clone_406);
          let t_clone_407 = Rc::clone(&t);
          Rc::new(tab { tc0: tmp_368, tc1: tmp_369, tc2: tmp_370, tc3: tmp_371, tc4: tmp_372, tc5: tmp_373, tc6: tmp_374, tc7: tmp_375, tc8: tmp_376, tc9: tmp_377, tc10: tmp_378, tc11: tmp_379, tc12: tmp_380, tc13: tmp_381, tc14: tmp_382, tc15: tmp_383, tc16: a_1, tc17: tmp_384, tc18: tmp_385, tc19: tmp_386, tc20: tmp_387, tc21: tmp_388, tc22: tmp_389, tc23: tmp_390, tc24: tc24_owned(t_clone_407), tc25: tc25_owned(t) })
        } else {
          if c < int63!(18) {
            let t_clone_408 = Rc::clone(&t);
            let tmp_391 = tc0_owned(t_clone_408);
            let t_clone_409 = Rc::clone(&t);
            let tmp_392 = tc1_owned(t_clone_409);
            let t_clone_410 = Rc::clone(&t);
            let tmp_393 = tc2_owned(t_clone_410);
            let t_clone_411 = Rc::clone(&t);
            let tmp_394 = tc3_owned(t_clone_411);
            let t_clone_412 = Rc::clone(&t);
            let tmp_395 = tc4_owned(t_clone_412);
            let t_clone_413 = Rc::clone(&t);
            let tmp_396 = tc5_owned(t_clone_413);
            let t_clone_414 = Rc::clone(&t);
            let tmp_397 = tc6_owned(t_clone_414);
            let t_clone_415 = Rc::clone(&t);
            let tmp_398 = tc7_owned(t_clone_415);
            let t_clone_416 = Rc::clone(&t);
            let tmp_399 = tc8_owned(t_clone_416);
            let t_clone_417 = Rc::clone(&t);
            let tmp_400 = tc9_owned(t_clone_417);
            let t_clone_418 = Rc::clone(&t);
            let tmp_401 = tc10_owned(t_clone_418);
            let t_clone_419 = Rc::clone(&t);
            let tmp_402 = tc11_owned(t_clone_419);
            let t_clone_420 = Rc::clone(&t);
            let tmp_403 = tc12_owned(t_clone_420);
            let t_clone_421 = Rc::clone(&t);
            let tmp_404 = tc13_owned(t_clone_421);
            let t_clone_422 = Rc::clone(&t);
            let tmp_405 = tc14_owned(t_clone_422);
            let t_clone_423 = Rc::clone(&t);
            let tmp_406 = tc15_owned(t_clone_423);
            let t_clone_424 = Rc::clone(&t);
            let tmp_407 = tc16_owned(t_clone_424);
            let t_clone_425 = Rc::clone(&t);
            let tmp_408 = tc18_owned(t_clone_425);
            let t_clone_426 = Rc::clone(&t);
            let tmp_409 = tc19_owned(t_clone_426);
            let t_clone_427 = Rc::clone(&t);
            let tmp_410 = tc20_owned(t_clone_427);
            let t_clone_428 = Rc::clone(&t);
            let tmp_411 = tc21_owned(t_clone_428);
            let t_clone_429 = Rc::clone(&t);
            let tmp_412 = tc22_owned(t_clone_429);
            let t_clone_430 = Rc::clone(&t);
            let tmp_413 = tc23_owned(t_clone_430);
            let t_clone_431 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_391, tc1: tmp_392, tc2: tmp_393, tc3: tmp_394, tc4: tmp_395, tc5: tmp_396, tc6: tmp_397, tc7: tmp_398, tc8: tmp_399, tc9: tmp_400, tc10: tmp_401, tc11: tmp_402, tc12: tmp_403, tc13: tmp_404, tc14: tmp_405, tc15: tmp_406, tc16: tmp_407, tc17: a_1, tc18: tmp_408, tc19: tmp_409, tc20: tmp_410, tc21: tmp_411, tc22: tmp_412, tc23: tmp_413, tc24: tc24_owned(t_clone_431), tc25: tc25_owned(t) })
          } else {
            let t_clone_432 = Rc::clone(&t);
            let tmp_414 = tc0_owned(t_clone_432);
            let t_clone_433 = Rc::clone(&t);
            let tmp_415 = tc1_owned(t_clone_433);
            let t_clone_434 = Rc::clone(&t);
            let tmp_416 = tc2_owned(t_clone_434);
            let t_clone_435 = Rc::clone(&t);
            let tmp_417 = tc3_owned(t_clone_435);
            let t_clone_436 = Rc::clone(&t);
            let tmp_418 = tc4_owned(t_clone_436);
            let t_clone_437 = Rc::clone(&t);
            let tmp_419 = tc5_owned(t_clone_437);
            let t_clone_438 = Rc::clone(&t);
            let tmp_420 = tc6_owned(t_clone_438);
            let t_clone_439 = Rc::clone(&t);
            let tmp_421 = tc7_owned(t_clone_439);
            let t_clone_440 = Rc::clone(&t);
            let tmp_422 = tc8_owned(t_clone_440);
            let t_clone_441 = Rc::clone(&t);
            let tmp_423 = tc9_owned(t_clone_441);
            let t_clone_442 = Rc::clone(&t);
            let tmp_424 = tc10_owned(t_clone_442);
            let t_clone_443 = Rc::clone(&t);
            let tmp_425 = tc11_owned(t_clone_443);
            let t_clone_444 = Rc::clone(&t);
            let tmp_426 = tc12_owned(t_clone_444);
            let t_clone_445 = Rc::clone(&t);
            let tmp_427 = tc13_owned(t_clone_445);
            let t_clone_446 = Rc::clone(&t);
            let tmp_428 = tc14_owned(t_clone_446);
            let t_clone_447 = Rc::clone(&t);
            let tmp_429 = tc15_owned(t_clone_447);
            let t_clone_448 = Rc::clone(&t);
            let tmp_430 = tc16_owned(t_clone_448);
            let t_clone_449 = Rc::clone(&t);
            let tmp_431 = tc17_owned(t_clone_449);
            let t_clone_450 = Rc::clone(&t);
            let tmp_432 = tc19_owned(t_clone_450);
            let t_clone_451 = Rc::clone(&t);
            let tmp_433 = tc20_owned(t_clone_451);
            let t_clone_452 = Rc::clone(&t);
            let tmp_434 = tc21_owned(t_clone_452);
            let t_clone_453 = Rc::clone(&t);
            let tmp_435 = tc22_owned(t_clone_453);
            let t_clone_454 = Rc::clone(&t);
            let tmp_436 = tc23_owned(t_clone_454);
            let t_clone_455 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_414, tc1: tmp_415, tc2: tmp_416, tc3: tmp_417, tc4: tmp_418, tc5: tmp_419, tc6: tmp_420, tc7: tmp_421, tc8: tmp_422, tc9: tmp_423, tc10: tmp_424, tc11: tmp_425, tc12: tmp_426, tc13: tmp_427, tc14: tmp_428, tc15: tmp_429, tc16: tmp_430, tc17: tmp_431, tc18: a_1, tc19: tmp_432, tc20: tmp_433, tc21: tmp_434, tc22: tmp_435, tc23: tmp_436, tc24: tc24_owned(t_clone_455), tc25: tc25_owned(t) })
          }
        }
      }
    } else {
      if c < int63!(22) {
        if c < int63!(20) {
          let t_clone_456 = Rc::clone(&t);
          let tmp_437 = tc0_owned(t_clone_456);
          let t_clone_457 = Rc::clone(&t);
          let tmp_438 = tc1_owned(t_clone_457);
          let t_clone_458 = Rc::clone(&t);
          let tmp_439 = tc2_owned(t_clone_458);
          let t_clone_459 = Rc::clone(&t);
          let tmp_440 = tc3_owned(t_clone_459);
          let t_clone_460 = Rc::clone(&t);
          let tmp_441 = tc4_owned(t_clone_460);
          let t_clone_461 = Rc::clone(&t);
          let tmp_442 = tc5_owned(t_clone_461);
          let t_clone_462 = Rc::clone(&t);
          let tmp_443 = tc6_owned(t_clone_462);
          let t_clone_463 = Rc::clone(&t);
          let tmp_444 = tc7_owned(t_clone_463);
          let t_clone_464 = Rc::clone(&t);
          let tmp_445 = tc8_owned(t_clone_464);
          let t_clone_465 = Rc::clone(&t);
          let tmp_446 = tc9_owned(t_clone_465);
          let t_clone_466 = Rc::clone(&t);
          let tmp_447 = tc10_owned(t_clone_466);
          let t_clone_467 = Rc::clone(&t);
          let tmp_448 = tc11_owned(t_clone_467);
          let t_clone_468 = Rc::clone(&t);
          let tmp_449 = tc12_owned(t_clone_468);
          let t_clone_469 = Rc::clone(&t);
          let tmp_450 = tc13_owned(t_clone_469);
          let t_clone_470 = Rc::clone(&t);
          let tmp_451 = tc14_owned(t_clone_470);
          let t_clone_471 = Rc::clone(&t);
          let tmp_452 = tc15_owned(t_clone_471);
          let t_clone_472 = Rc::clone(&t);
          let tmp_453 = tc16_owned(t_clone_472);
          let t_clone_473 = Rc::clone(&t);
          let tmp_454 = tc17_owned(t_clone_473);
          let t_clone_474 = Rc::clone(&t);
          let tmp_455 = tc18_owned(t_clone_474);
          let t_clone_475 = Rc::clone(&t);
          let tmp_456 = tc20_owned(t_clone_475);
          let t_clone_476 = Rc::clone(&t);
          let tmp_457 = tc21_owned(t_clone_476);
          let t_clone_477 = Rc::clone(&t);
          let tmp_458 = tc22_owned(t_clone_477);
          let t_clone_478 = Rc::clone(&t);
          let tmp_459 = tc23_owned(t_clone_478);
          let t_clone_479 = Rc::clone(&t);
          Rc::new(tab { tc0: tmp_437, tc1: tmp_438, tc2: tmp_439, tc3: tmp_440, tc4: tmp_441, tc5: tmp_442, tc6: tmp_443, tc7: tmp_444, tc8: tmp_445, tc9: tmp_446, tc10: tmp_447, tc11: tmp_448, tc12: tmp_449, tc13: tmp_450, tc14: tmp_451, tc15: tmp_452, tc16: tmp_453, tc17: tmp_454, tc18: tmp_455, tc19: a_1, tc20: tmp_456, tc21: tmp_457, tc22: tmp_458, tc23: tmp_459, tc24: tc24_owned(t_clone_479), tc25: tc25_owned(t) })
        } else {
          if c < int63!(21) {
            let t_clone_480 = Rc::clone(&t);
            let tmp_460 = tc0_owned(t_clone_480);
            let t_clone_481 = Rc::clone(&t);
            let tmp_461 = tc1_owned(t_clone_481);
            let t_clone_482 = Rc::clone(&t);
            let tmp_462 = tc2_owned(t_clone_482);
            let t_clone_483 = Rc::clone(&t);
            let tmp_463 = tc3_owned(t_clone_483);
            let t_clone_484 = Rc::clone(&t);
            let tmp_464 = tc4_owned(t_clone_484);
            let t_clone_485 = Rc::clone(&t);
            let tmp_465 = tc5_owned(t_clone_485);
            let t_clone_486 = Rc::clone(&t);
            let tmp_466 = tc6_owned(t_clone_486);
            let t_clone_487 = Rc::clone(&t);
            let tmp_467 = tc7_owned(t_clone_487);
            let t_clone_488 = Rc::clone(&t);
            let tmp_468 = tc8_owned(t_clone_488);
            let t_clone_489 = Rc::clone(&t);
            let tmp_469 = tc9_owned(t_clone_489);
            let t_clone_490 = Rc::clone(&t);
            let tmp_470 = tc10_owned(t_clone_490);
            let t_clone_491 = Rc::clone(&t);
            let tmp_471 = tc11_owned(t_clone_491);
            let t_clone_492 = Rc::clone(&t);
            let tmp_472 = tc12_owned(t_clone_492);
            let t_clone_493 = Rc::clone(&t);
            let tmp_473 = tc13_owned(t_clone_493);
            let t_clone_494 = Rc::clone(&t);
            let tmp_474 = tc14_owned(t_clone_494);
            let t_clone_495 = Rc::clone(&t);
            let tmp_475 = tc15_owned(t_clone_495);
            let t_clone_496 = Rc::clone(&t);
            let tmp_476 = tc16_owned(t_clone_496);
            let t_clone_497 = Rc::clone(&t);
            let tmp_477 = tc17_owned(t_clone_497);
            let t_clone_498 = Rc::clone(&t);
            let tmp_478 = tc18_owned(t_clone_498);
            let t_clone_499 = Rc::clone(&t);
            let tmp_479 = tc19_owned(t_clone_499);
            let t_clone_500 = Rc::clone(&t);
            let tmp_480 = tc21_owned(t_clone_500);
            let t_clone_501 = Rc::clone(&t);
            let tmp_481 = tc22_owned(t_clone_501);
            let t_clone_502 = Rc::clone(&t);
            let tmp_482 = tc23_owned(t_clone_502);
            let t_clone_503 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_460, tc1: tmp_461, tc2: tmp_462, tc3: tmp_463, tc4: tmp_464, tc5: tmp_465, tc6: tmp_466, tc7: tmp_467, tc8: tmp_468, tc9: tmp_469, tc10: tmp_470, tc11: tmp_471, tc12: tmp_472, tc13: tmp_473, tc14: tmp_474, tc15: tmp_475, tc16: tmp_476, tc17: tmp_477, tc18: tmp_478, tc19: tmp_479, tc20: a_1, tc21: tmp_480, tc22: tmp_481, tc23: tmp_482, tc24: tc24_owned(t_clone_503), tc25: tc25_owned(t) })
          } else {
            let t_clone_504 = Rc::clone(&t);
            let tmp_483 = tc0_owned(t_clone_504);
            let t_clone_505 = Rc::clone(&t);
            let tmp_484 = tc1_owned(t_clone_505);
            let t_clone_506 = Rc::clone(&t);
            let tmp_485 = tc2_owned(t_clone_506);
            let t_clone_507 = Rc::clone(&t);
            let tmp_486 = tc3_owned(t_clone_507);
            let t_clone_508 = Rc::clone(&t);
            let tmp_487 = tc4_owned(t_clone_508);
            let t_clone_509 = Rc::clone(&t);
            let tmp_488 = tc5_owned(t_clone_509);
            let t_clone_510 = Rc::clone(&t);
            let tmp_489 = tc6_owned(t_clone_510);
            let t_clone_511 = Rc::clone(&t);
            let tmp_490 = tc7_owned(t_clone_511);
            let t_clone_512 = Rc::clone(&t);
            let tmp_491 = tc8_owned(t_clone_512);
            let t_clone_513 = Rc::clone(&t);
            let tmp_492 = tc9_owned(t_clone_513);
            let t_clone_514 = Rc::clone(&t);
            let tmp_493 = tc10_owned(t_clone_514);
            let t_clone_515 = Rc::clone(&t);
            let tmp_494 = tc11_owned(t_clone_515);
            let t_clone_516 = Rc::clone(&t);
            let tmp_495 = tc12_owned(t_clone_516);
            let t_clone_517 = Rc::clone(&t);
            let tmp_496 = tc13_owned(t_clone_517);
            let t_clone_518 = Rc::clone(&t);
            let tmp_497 = tc14_owned(t_clone_518);
            let t_clone_519 = Rc::clone(&t);
            let tmp_498 = tc15_owned(t_clone_519);
            let t_clone_520 = Rc::clone(&t);
            let tmp_499 = tc16_owned(t_clone_520);
            let t_clone_521 = Rc::clone(&t);
            let tmp_500 = tc17_owned(t_clone_521);
            let t_clone_522 = Rc::clone(&t);
            let tmp_501 = tc18_owned(t_clone_522);
            let t_clone_523 = Rc::clone(&t);
            let tmp_502 = tc19_owned(t_clone_523);
            let t_clone_524 = Rc::clone(&t);
            let tmp_503 = tc20_owned(t_clone_524);
            let t_clone_525 = Rc::clone(&t);
            let tmp_504 = tc22_owned(t_clone_525);
            let t_clone_526 = Rc::clone(&t);
            let tmp_505 = tc23_owned(t_clone_526);
            let t_clone_527 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_483, tc1: tmp_484, tc2: tmp_485, tc3: tmp_486, tc4: tmp_487, tc5: tmp_488, tc6: tmp_489, tc7: tmp_490, tc8: tmp_491, tc9: tmp_492, tc10: tmp_493, tc11: tmp_494, tc12: tmp_495, tc13: tmp_496, tc14: tmp_497, tc15: tmp_498, tc16: tmp_499, tc17: tmp_500, tc18: tmp_501, tc19: tmp_502, tc20: tmp_503, tc21: a_1, tc22: tmp_504, tc23: tmp_505, tc24: tc24_owned(t_clone_527), tc25: tc25_owned(t) })
          }
        }
      } else {
        if c < int63!(24) {
          if c < int63!(23) {
            let t_clone_528 = Rc::clone(&t);
            let tmp_506 = tc0_owned(t_clone_528);
            let t_clone_529 = Rc::clone(&t);
            let tmp_507 = tc1_owned(t_clone_529);
            let t_clone_530 = Rc::clone(&t);
            let tmp_508 = tc2_owned(t_clone_530);
            let t_clone_531 = Rc::clone(&t);
            let tmp_509 = tc3_owned(t_clone_531);
            let t_clone_532 = Rc::clone(&t);
            let tmp_510 = tc4_owned(t_clone_532);
            let t_clone_533 = Rc::clone(&t);
            let tmp_511 = tc5_owned(t_clone_533);
            let t_clone_534 = Rc::clone(&t);
            let tmp_512 = tc6_owned(t_clone_534);
            let t_clone_535 = Rc::clone(&t);
            let tmp_513 = tc7_owned(t_clone_535);
            let t_clone_536 = Rc::clone(&t);
            let tmp_514 = tc8_owned(t_clone_536);
            let t_clone_537 = Rc::clone(&t);
            let tmp_515 = tc9_owned(t_clone_537);
            let t_clone_538 = Rc::clone(&t);
            let tmp_516 = tc10_owned(t_clone_538);
            let t_clone_539 = Rc::clone(&t);
            let tmp_517 = tc11_owned(t_clone_539);
            let t_clone_540 = Rc::clone(&t);
            let tmp_518 = tc12_owned(t_clone_540);
            let t_clone_541 = Rc::clone(&t);
            let tmp_519 = tc13_owned(t_clone_541);
            let t_clone_542 = Rc::clone(&t);
            let tmp_520 = tc14_owned(t_clone_542);
            let t_clone_543 = Rc::clone(&t);
            let tmp_521 = tc15_owned(t_clone_543);
            let t_clone_544 = Rc::clone(&t);
            let tmp_522 = tc16_owned(t_clone_544);
            let t_clone_545 = Rc::clone(&t);
            let tmp_523 = tc17_owned(t_clone_545);
            let t_clone_546 = Rc::clone(&t);
            let tmp_524 = tc18_owned(t_clone_546);
            let t_clone_547 = Rc::clone(&t);
            let tmp_525 = tc19_owned(t_clone_547);
            let t_clone_548 = Rc::clone(&t);
            let tmp_526 = tc20_owned(t_clone_548);
            let t_clone_549 = Rc::clone(&t);
            let tmp_527 = tc21_owned(t_clone_549);
            let t_clone_550 = Rc::clone(&t);
            let tmp_528 = tc23_owned(t_clone_550);
            let t_clone_551 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_506, tc1: tmp_507, tc2: tmp_508, tc3: tmp_509, tc4: tmp_510, tc5: tmp_511, tc6: tmp_512, tc7: tmp_513, tc8: tmp_514, tc9: tmp_515, tc10: tmp_516, tc11: tmp_517, tc12: tmp_518, tc13: tmp_519, tc14: tmp_520, tc15: tmp_521, tc16: tmp_522, tc17: tmp_523, tc18: tmp_524, tc19: tmp_525, tc20: tmp_526, tc21: tmp_527, tc22: a_1, tc23: tmp_528, tc24: tc24_owned(t_clone_551), tc25: tc25_owned(t) })
          } else {
            let t_clone_552 = Rc::clone(&t);
            let tmp_529 = tc0_owned(t_clone_552);
            let t_clone_553 = Rc::clone(&t);
            let tmp_530 = tc1_owned(t_clone_553);
            let t_clone_554 = Rc::clone(&t);
            let tmp_531 = tc2_owned(t_clone_554);
            let t_clone_555 = Rc::clone(&t);
            let tmp_532 = tc3_owned(t_clone_555);
            let t_clone_556 = Rc::clone(&t);
            let tmp_533 = tc4_owned(t_clone_556);
            let t_clone_557 = Rc::clone(&t);
            let tmp_534 = tc5_owned(t_clone_557);
            let t_clone_558 = Rc::clone(&t);
            let tmp_535 = tc6_owned(t_clone_558);
            let t_clone_559 = Rc::clone(&t);
            let tmp_536 = tc7_owned(t_clone_559);
            let t_clone_560 = Rc::clone(&t);
            let tmp_537 = tc8_owned(t_clone_560);
            let t_clone_561 = Rc::clone(&t);
            let tmp_538 = tc9_owned(t_clone_561);
            let t_clone_562 = Rc::clone(&t);
            let tmp_539 = tc10_owned(t_clone_562);
            let t_clone_563 = Rc::clone(&t);
            let tmp_540 = tc11_owned(t_clone_563);
            let t_clone_564 = Rc::clone(&t);
            let tmp_541 = tc12_owned(t_clone_564);
            let t_clone_565 = Rc::clone(&t);
            let tmp_542 = tc13_owned(t_clone_565);
            let t_clone_566 = Rc::clone(&t);
            let tmp_543 = tc14_owned(t_clone_566);
            let t_clone_567 = Rc::clone(&t);
            let tmp_544 = tc15_owned(t_clone_567);
            let t_clone_568 = Rc::clone(&t);
            let tmp_545 = tc16_owned(t_clone_568);
            let t_clone_569 = Rc::clone(&t);
            let tmp_546 = tc17_owned(t_clone_569);
            let t_clone_570 = Rc::clone(&t);
            let tmp_547 = tc18_owned(t_clone_570);
            let t_clone_571 = Rc::clone(&t);
            let tmp_548 = tc19_owned(t_clone_571);
            let t_clone_572 = Rc::clone(&t);
            let tmp_549 = tc20_owned(t_clone_572);
            let t_clone_573 = Rc::clone(&t);
            let tmp_550 = tc21_owned(t_clone_573);
            let t_clone_574 = Rc::clone(&t);
            let tmp_551 = tc22_owned(t_clone_574);
            let t_clone_575 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_529, tc1: tmp_530, tc2: tmp_531, tc3: tmp_532, tc4: tmp_533, tc5: tmp_534, tc6: tmp_535, tc7: tmp_536, tc8: tmp_537, tc9: tmp_538, tc10: tmp_539, tc11: tmp_540, tc12: tmp_541, tc13: tmp_542, tc14: tmp_543, tc15: tmp_544, tc16: tmp_545, tc17: tmp_546, tc18: tmp_547, tc19: tmp_548, tc20: tmp_549, tc21: tmp_550, tc22: tmp_551, tc23: a_1, tc24: tc24_owned(t_clone_575), tc25: tc25_owned(t) })
          }
        } else {
          if c < int63!(25) {
            let t_clone_576 = Rc::clone(&t);
            let tmp_552 = tc0_owned(t_clone_576);
            let t_clone_577 = Rc::clone(&t);
            let tmp_553 = tc1_owned(t_clone_577);
            let t_clone_578 = Rc::clone(&t);
            let tmp_554 = tc2_owned(t_clone_578);
            let t_clone_579 = Rc::clone(&t);
            let tmp_555 = tc3_owned(t_clone_579);
            let t_clone_580 = Rc::clone(&t);
            let tmp_556 = tc4_owned(t_clone_580);
            let t_clone_581 = Rc::clone(&t);
            let tmp_557 = tc5_owned(t_clone_581);
            let t_clone_582 = Rc::clone(&t);
            let tmp_558 = tc6_owned(t_clone_582);
            let t_clone_583 = Rc::clone(&t);
            let tmp_559 = tc7_owned(t_clone_583);
            let t_clone_584 = Rc::clone(&t);
            let tmp_560 = tc8_owned(t_clone_584);
            let t_clone_585 = Rc::clone(&t);
            let tmp_561 = tc9_owned(t_clone_585);
            let t_clone_586 = Rc::clone(&t);
            let tmp_562 = tc10_owned(t_clone_586);
            let t_clone_587 = Rc::clone(&t);
            let tmp_563 = tc11_owned(t_clone_587);
            let t_clone_588 = Rc::clone(&t);
            let tmp_564 = tc12_owned(t_clone_588);
            let t_clone_589 = Rc::clone(&t);
            let tmp_565 = tc13_owned(t_clone_589);
            let t_clone_590 = Rc::clone(&t);
            let tmp_566 = tc14_owned(t_clone_590);
            let t_clone_591 = Rc::clone(&t);
            let tmp_567 = tc15_owned(t_clone_591);
            let t_clone_592 = Rc::clone(&t);
            let tmp_568 = tc16_owned(t_clone_592);
            let t_clone_593 = Rc::clone(&t);
            let tmp_569 = tc17_owned(t_clone_593);
            let t_clone_594 = Rc::clone(&t);
            let tmp_570 = tc18_owned(t_clone_594);
            let t_clone_595 = Rc::clone(&t);
            let tmp_571 = tc19_owned(t_clone_595);
            let t_clone_596 = Rc::clone(&t);
            let tmp_572 = tc20_owned(t_clone_596);
            let t_clone_597 = Rc::clone(&t);
            let tmp_573 = tc21_owned(t_clone_597);
            let t_clone_598 = Rc::clone(&t);
            let tmp_574 = tc22_owned(t_clone_598);
            let t_clone_599 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_552, tc1: tmp_553, tc2: tmp_554, tc3: tmp_555, tc4: tmp_556, tc5: tmp_557, tc6: tmp_558, tc7: tmp_559, tc8: tmp_560, tc9: tmp_561, tc10: tmp_562, tc11: tmp_563, tc12: tmp_564, tc13: tmp_565, tc14: tmp_566, tc15: tmp_567, tc16: tmp_568, tc17: tmp_569, tc18: tmp_570, tc19: tmp_571, tc20: tmp_572, tc21: tmp_573, tc22: tmp_574, tc23: tc23_owned(t_clone_599), tc24: a_1, tc25: tc25_owned(t) })
          } else {
            let t_clone_600 = Rc::clone(&t);
            let tmp_575 = tc0_owned(t_clone_600);
            let t_clone_601 = Rc::clone(&t);
            let tmp_576 = tc1_owned(t_clone_601);
            let t_clone_602 = Rc::clone(&t);
            let tmp_577 = tc2_owned(t_clone_602);
            let t_clone_603 = Rc::clone(&t);
            let tmp_578 = tc3_owned(t_clone_603);
            let t_clone_604 = Rc::clone(&t);
            let tmp_579 = tc4_owned(t_clone_604);
            let t_clone_605 = Rc::clone(&t);
            let tmp_580 = tc5_owned(t_clone_605);
            let t_clone_606 = Rc::clone(&t);
            let tmp_581 = tc6_owned(t_clone_606);
            let t_clone_607 = Rc::clone(&t);
            let tmp_582 = tc7_owned(t_clone_607);
            let t_clone_608 = Rc::clone(&t);
            let tmp_583 = tc8_owned(t_clone_608);
            let t_clone_609 = Rc::clone(&t);
            let tmp_584 = tc9_owned(t_clone_609);
            let t_clone_610 = Rc::clone(&t);
            let tmp_585 = tc10_owned(t_clone_610);
            let t_clone_611 = Rc::clone(&t);
            let tmp_586 = tc11_owned(t_clone_611);
            let t_clone_612 = Rc::clone(&t);
            let tmp_587 = tc12_owned(t_clone_612);
            let t_clone_613 = Rc::clone(&t);
            let tmp_588 = tc13_owned(t_clone_613);
            let t_clone_614 = Rc::clone(&t);
            let tmp_589 = tc14_owned(t_clone_614);
            let t_clone_615 = Rc::clone(&t);
            let tmp_590 = tc15_owned(t_clone_615);
            let t_clone_616 = Rc::clone(&t);
            let tmp_591 = tc16_owned(t_clone_616);
            let t_clone_617 = Rc::clone(&t);
            let tmp_592 = tc17_owned(t_clone_617);
            let t_clone_618 = Rc::clone(&t);
            let tmp_593 = tc18_owned(t_clone_618);
            let t_clone_619 = Rc::clone(&t);
            let tmp_594 = tc19_owned(t_clone_619);
            let t_clone_620 = Rc::clone(&t);
            let tmp_595 = tc20_owned(t_clone_620);
            let t_clone_621 = Rc::clone(&t);
            let tmp_596 = tc21_owned(t_clone_621);
            let t_clone_622 = Rc::clone(&t);
            let tmp_597 = tc22_owned(t_clone_622);
            let t_clone_623 = Rc::clone(&t);
            Rc::new(tab { tc0: tmp_575, tc1: tmp_576, tc2: tmp_577, tc3: tmp_578, tc4: tmp_579, tc5: tmp_580, tc6: tmp_581, tc7: tmp_582, tc8: tmp_583, tc9: tmp_584, tc10: tmp_585, tc11: tmp_586, tc12: tmp_587, tc13: tmp_588, tc14: tmp_589, tc15: tmp_590, tc16: tmp_591, tc17: tmp_592, tc18: tmp_593, tc19: tmp_594, tc20: tmp_595, tc21: tmp_596, tc22: tmp_597, tc23: tc23_owned(t_clone_623), tc24: tc24_owned(t), tc25: a_1 })
          }
        }
      }
    }
  }
}

// Rocq: Baza.baza_implem.tset
// Variant: uncurried
pub fn tset(t: Rc<tab>, c: Int63, n: Int63, v: Int63) -> Rc<tab> {
  let t_clone = Rc::clone(&t);
  let tmp = sel_owned(t_clone, c);
  upd(t, c, tmp.set(n, v))
}

// Rocq: Baza.baza_implem.ins_loop
// Variant: uncurried
pub fn ins_loop_1(w: rocq_string::RocqString, L: Int63, T: Rc<tab>, cnt: Array<Int63>, sz: Int63, i: Int63, n: Int63, s: Int63) -> Rc<ires> {
  ins_loop(w, L, T, cnt, sz, i, n, s, ())
}

// Rocq: Baza.baza_implem.ins_loop (local: ins_loop)
// Variant: uncurried, lifted
pub fn ins_loop(w: rocq_string::RocqString, L: Int63, T: Rc<tab>, cnt: Array<Int63>, sz: Int63, i: Int63, n: Int63, s: Int63, _H: ()) -> Rc<ires> {
  let tmp = i < L;
  match bdec(tmp) {
    sumbool::left => {
      let w_clone = Clone::clone(&w);
      let c = get(w_clone, i) - int63!(97);
      let m = tget(&T, c, n);
      if m == int63!(0) {
        ins_loop(w, L, tset(T, c, n, sz), cnt.set(sz, int63!(1)), sz + int63!(1), i + int63!(1), sz, s + int63!(1), ())
      } else {
        let tmp_1 = cnt.get_cloned(m);
        let k = tmp_1 + int63!(1);
        ins_loop(w, L, T, cnt.set(m, k), sz, i + int63!(1), m, s + k, ())
      }
    },
    sumbool::right => {
      std::mem::drop(w);
      Rc::new(ires { r_T: T, r_cnt: cnt, r_sz: sz, r_n: n, r_s: s })
    },
  }
}

// Rocq: Baza.baza_implem.r_T
pub fn r_T(i: Rc<ires>) -> Rc<tab> {
  let i_r_T_clone = Rc::clone(&i.r_T);
  std::mem::drop(i);
  i_r_T_clone
}

// Rocq: Baza.baza_implem.r_cnt
pub fn r_cnt(i: Rc<ires>) -> Array<Int63> {
  let i_r_cnt_clone = Clone::clone(&i.r_cnt);
  std::mem::drop(i);
  i_r_cnt_clone
}

// Rocq: Baza.baza_implem.r_n
// Variant: borrowed
pub fn r_n(i: &Rc<ires>) -> Int63 {
  let tmp = i;
  Clone::clone(&tmp.r_n)
}

// Rocq: Baza.baza_implem.r_s
// Variant: borrowed
pub fn r_s(i: &Rc<ires>) -> Int63 {
  let tmp = i;
  Clone::clone(&tmp.r_s)
}

// Rocq: Baza.baza_implem.r_sz
pub fn r_sz(i: Rc<ires>) -> Int63 {
  let i_r_sz_clone = Clone::clone(&i.r_sz);
  std::mem::drop(i);
  i_r_sz_clone
}

// Rocq: Baza.baza_implem.build
// Variant: uncurried
pub fn build_1(db: Array<rocq_string::RocqString>, N: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, sz: Int63, j: Int63) -> Rc<bres> {
  build(db, N, T, cnt, endv, sz, j, ())
}

// Rocq: Baza.baza_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(db: Array<rocq_string::RocqString>, N: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, sz: Int63, j: Int63, _H: ()) -> Rc<bres> {
  let tmp = j < N;
  match bdec(tmp) {
    sumbool::left => {
      let db_ref = &db;
      let w = db_ref.get_cloned(j);
      let w_clone = Clone::clone(&w);
      let r = ins_loop_1(w, length(w_clone), T, cnt, sz, int63!(0), int63!(0), int63!(0));
      let r_clone = Rc::clone(&r);
      let tmp_1 = r_T(r_clone);
      let r_clone_1 = Rc::clone(&r);
      let tmp_2 = r_cnt(r_clone_1);
      let tmp_3 = r_n(&r);
      let tmp_4 = j + int63!(1);
      let tmp_5 = r_s(&r);
      build(db, N, tmp_1, tmp_2, endv.set(tmp_3, tmp_4 + tmp_5), r_sz(r), j + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(db);
      Rc::new(bres { b_T: T, b_cnt: cnt, b_end: endv })
    },
  }
}

// Rocq: Baza.baza_implem.mk_tab
pub fn mk_tab(cap: Int63) -> Rc<tab> {
  Rc::new(tab { tc0: Array::<Int63>::make(cap, int63!(0)), tc1: Array::<Int63>::make(cap, int63!(0)), tc2: Array::<Int63>::make(cap, int63!(0)), tc3: Array::<Int63>::make(cap, int63!(0)), tc4: Array::<Int63>::make(cap, int63!(0)), tc5: Array::<Int63>::make(cap, int63!(0)), tc6: Array::<Int63>::make(cap, int63!(0)), tc7: Array::<Int63>::make(cap, int63!(0)), tc8: Array::<Int63>::make(cap, int63!(0)), tc9: Array::<Int63>::make(cap, int63!(0)), tc10: Array::<Int63>::make(cap, int63!(0)), tc11: Array::<Int63>::make(cap, int63!(0)), tc12: Array::<Int63>::make(cap, int63!(0)), tc13: Array::<Int63>::make(cap, int63!(0)), tc14: Array::<Int63>::make(cap, int63!(0)), tc15: Array::<Int63>::make(cap, int63!(0)), tc16: Array::<Int63>::make(cap, int63!(0)), tc17: Array::<Int63>::make(cap, int63!(0)), tc18: Array::<Int63>::make(cap, int63!(0)), tc19: Array::<Int63>::make(cap, int63!(0)), tc20: Array::<Int63>::make(cap, int63!(0)), tc21: Array::<Int63>::make(cap, int63!(0)), tc22: Array::<Int63>::make(cap, int63!(0)), tc23: Array::<Int63>::make(cap, int63!(0)), tc24: Array::<Int63>::make(cap, int63!(0)), tc25: Array::<Int63>::make(cap, int63!(0)) })
}

// Rocq: Baza.baza_implem.qwalk
// Variant: uncurried
pub fn qwalk_1(q: rocq_string::RocqString, L: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, N: Int63, i: Int63, n: Int63, s: Int63) -> Int63 {
  qwalk(q, L, T, cnt, endv, N, i, n, s, ())
}

// Rocq: Baza.baza_implem.qwalk (local: qwalk)
// Variant: uncurried, lifted
pub fn qwalk(q: rocq_string::RocqString, L: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, N: Int63, i: Int63, n: Int63, s: Int63, _H: ()) -> Int63 {
  let tmp = i < L;
  match bdec(tmp) {
    sumbool::left => {
      let q_clone = Clone::clone(&q);
      let m = tget(&T, get(q_clone, i) - int63!(97), n);
      if m == int63!(0) {
        std::mem::drop(q);
        std::mem::drop(cnt);
        std::mem::drop(endv);
        std::mem::drop(T);
        N + s
      } else {
        let tmp_1 = i + int63!(1);
        let tmp_2 = cnt.get_cloned(m);
        qwalk(q, L, T, cnt, endv, N, tmp_1, m, s + tmp_2, ())
      }
    },
    sumbool::right => {
      let e = endv.get_cloned(n);
      if e == int63!(0) {
        std::mem::drop(q);
        std::mem::drop(T);
        std::mem::drop(cnt);
        std::mem::drop(endv);
        N + s
      } else {
        std::mem::drop(q);
        std::mem::drop(T);
        std::mem::drop(cnt);
        std::mem::drop(endv);
        e
      }
    },
  }
}

// Rocq: Baza.baza_implem.query
// Variant: uncurried
pub fn query(q: rocq_string::RocqString, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, N: Int63) -> Int63 {
  let q_clone = Clone::clone(&q);
  qwalk_1(q, length(q_clone), T, cnt, endv, N, int63!(0), int63!(0), int63!(0))
}

// Rocq: Baza.baza_implem.answer
// Variant: uncurried
pub fn answer_1(qs: Array<rocq_string::RocqString>, Q: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, N: Int63, out: Array<Int63>, k: Int63) -> Array<Int63> {
  answer(qs, Q, T, cnt, endv, N, out, k, ())
}

// Rocq: Baza.baza_implem.answer (local: answer)
// Variant: uncurried, lifted
pub fn answer(qs: Array<rocq_string::RocqString>, Q: Int63, T: Rc<tab>, cnt: Array<Int63>, endv: Array<Int63>, N: Int63, out: Array<Int63>, k: Int63, _H: ()) -> Array<Int63> {
  let tmp = k < Q;
  match bdec(tmp) {
    sumbool::left => {
      let qs_ref = &qs;
      let tmp_1 = qs_ref.get_cloned(k);
      let T_clone = Rc::clone(&T);
      let cnt_clone = Clone::clone(&cnt);
      let endv_clone = Clone::clone(&endv);
      let tmp_2 = query(tmp_1, T_clone, cnt_clone, endv_clone, N);
      answer(qs, Q, T, cnt, endv, N, out.set(k, tmp_2), k + int63!(1), ())
    },
    sumbool::right => {
      std::mem::drop(qs);
      std::mem::drop(T);
      std::mem::drop(cnt);
      std::mem::drop(endv);
      out
    },
  }
}

// Rocq: Baza.baza_implem.b_T
pub fn b_T(b_1: Rc<bres>) -> Rc<tab> {
  let b_b_T_clone = Rc::clone(&b_1.b_T);
  std::mem::drop(b_1);
  b_b_T_clone
}

// Rocq: Baza.baza_implem.b_cnt
pub fn b_cnt(b_1: Rc<bres>) -> Array<Int63> {
  let b_b_cnt_clone = Clone::clone(&b_1.b_cnt);
  std::mem::drop(b_1);
  b_b_cnt_clone
}

// Rocq: Baza.baza_implem.b_end
pub fn b_end(b_1: Rc<bres>) -> Array<Int63> {
  let b_b_end_clone = Clone::clone(&b_1.b_end);
  std::mem::drop(b_1);
  b_b_end_clone
}

// Rocq: Baza.baza_implem.baza_impl
// Variant: uncurried
pub fn baza_impl(db: Array<rocq_string::RocqString>, qs: Array<rocq_string::RocqString>) -> Array<Int63> {
  let N = db.length();
  let db_clone = Clone::clone(&db);
  let cap = int63!(1) + total_1(db_clone, N, int63!(0), int63!(0));
  let b_1 = build_1(db, N, mk_tab(cap), Array::<Int63>::make(cap, int63!(0)), Array::<Int63>::make(cap, int63!(0)), int63!(1), int63!(0));
  let Q = qs.length();
  let b_clone = Rc::clone(&b_1);
  let tmp = b_T(b_clone);
  let b_clone_1 = Rc::clone(&b_1);
  let tmp_1 = b_cnt(b_clone_1);
  let tmp_2 = b_end(b_1);
  let tmp_3 = Array::<Int63>::make(Q, int63!(0));
  answer_1(qs, Q, tmp, tmp_1, tmp_2, N, tmp_3, int63!(0))
}
