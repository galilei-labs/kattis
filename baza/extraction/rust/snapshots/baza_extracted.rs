// Generated from OwnedANF. This printer is not verified.
#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct ires {
  pub r_T: Rc<tab>,
  pub r_cnt: Rc<Array<u64>>,
  pub r_sz: u64,
  pub r_n: u64,
  pub r_s: u64,
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
  pub b_cnt: Rc<Array<u64>>,
  pub b_end: Rc<Array<u64>>,
}

impl Clone for bres {
  fn clone(&self) -> Self {
    match self {
      bres { b_T: __field0, b_cnt: __field1, b_end: __field2 } => bres { b_T: Clone::clone(__field0), b_cnt: Clone::clone(__field1), b_end: Clone::clone(__field2) },
    }
  }
}

pub struct tab {
  pub tc0: Rc<Array<u64>>,
  pub tc1: Rc<Array<u64>>,
  pub tc2: Rc<Array<u64>>,
  pub tc3: Rc<Array<u64>>,
  pub tc4: Rc<Array<u64>>,
  pub tc5: Rc<Array<u64>>,
  pub tc6: Rc<Array<u64>>,
  pub tc7: Rc<Array<u64>>,
  pub tc8: Rc<Array<u64>>,
  pub tc9: Rc<Array<u64>>,
  pub tc10: Rc<Array<u64>>,
  pub tc11: Rc<Array<u64>>,
  pub tc12: Rc<Array<u64>>,
  pub tc13: Rc<Array<u64>>,
  pub tc14: Rc<Array<u64>>,
  pub tc15: Rc<Array<u64>>,
  pub tc16: Rc<Array<u64>>,
  pub tc17: Rc<Array<u64>>,
  pub tc18: Rc<Array<u64>>,
  pub tc19: Rc<Array<u64>>,
  pub tc20: Rc<Array<u64>>,
  pub tc21: Rc<Array<u64>>,
  pub tc22: Rc<Array<u64>>,
  pub tc23: Rc<Array<u64>>,
  pub tc24: Rc<Array<u64>>,
  pub tc25: Rc<Array<u64>>,
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

pub type char63 = u64;

pub type uint = u64;

// Rocq: Baza.baza_implem.baza
// Variant: uncurried
pub fn baza() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>> = baza_impl;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> = Rc::new(v0);
  v1
}

// Rocq: Baza.baza_implem.baza
pub fn baza_curried() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>>> {
  let v0: fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> = baza_impl_curried;
  let v1: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>>> = Rc::new(v0);
  v1
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
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

// Rocq: Baza.baza_implem.bdec
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

// Rocq: Corelib.Strings.PrimString.length
pub fn length(v0: Rc<rocq_string::RocqString>) -> u64 {
  let v2 = rocq_string::length(&v0);
  std::mem::drop(v0);
  v2
}

// Rocq: Baza.baza_implem.total
// Variant: uncurried
pub fn total_1(db: Rc<Array<Rc<rocq_string::RocqString>>>, N: u64, j: u64, acc: u64) -> u64 {
  total(db, N, j, acc, ())
}

// Rocq: Baza.baza_implem.total (local: total)
// Variant: uncurried, lifted
pub fn total(db: Rc<Array<Rc<rocq_string::RocqString>>>, N: u64, j: u64, acc: u64, _H: ()) -> u64 {
  let v12 = ltb(j, N);
  match bdec(v12) {
    sumbool::left => {
      let v23 = add(j, 1u64);
      let v26 = &db;
      let v30 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v26, j);
      total(db, N, v23, add(acc, length(v30)), ())
    },
    sumbool::right => {
      std::mem::drop(db);
      acc
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: Rc<rocq_string::RocqString>, v1: u64) -> u64 {
  let v5 = rocq_string::get(&v0, v1);
  std::mem::drop(v0);
  v5
}

// Rocq: Baza.baza_implem.tc0
pub fn tc0_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc0));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc0
// Variant: borrowed
pub fn tc0(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc0))
}

// Rocq: Baza.baza_implem.tc1
pub fn tc1_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc1));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc1
// Variant: borrowed
pub fn tc1(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc1))
}

// Rocq: Baza.baza_implem.tc2
pub fn tc2_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc2));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc2
// Variant: borrowed
pub fn tc2(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc2))
}

// Rocq: Baza.baza_implem.tc3
pub fn tc3_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc3));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc3
// Variant: borrowed
pub fn tc3(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc3))
}

// Rocq: Baza.baza_implem.tc4
pub fn tc4_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc4));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc4
// Variant: borrowed
pub fn tc4(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc4))
}

// Rocq: Baza.baza_implem.tc5
pub fn tc5_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc5));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc5
// Variant: borrowed
pub fn tc5(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc5))
}

// Rocq: Baza.baza_implem.tc6
pub fn tc6_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc6));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc6
// Variant: borrowed
pub fn tc6(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc6))
}

// Rocq: Baza.baza_implem.tc7
pub fn tc7_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc7));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc7
// Variant: borrowed
pub fn tc7(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc7))
}

// Rocq: Baza.baza_implem.tc8
pub fn tc8_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc8));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc8
// Variant: borrowed
pub fn tc8(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc8))
}

// Rocq: Baza.baza_implem.tc9
pub fn tc9_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc9));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc9
// Variant: borrowed
pub fn tc9(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc9))
}

// Rocq: Baza.baza_implem.tc10
pub fn tc10_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc10));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc10
// Variant: borrowed
pub fn tc10(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc10))
}

// Rocq: Baza.baza_implem.tc11
pub fn tc11_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc11));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc11
// Variant: borrowed
pub fn tc11(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc11))
}

// Rocq: Baza.baza_implem.tc12
pub fn tc12_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc12));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc12
// Variant: borrowed
pub fn tc12(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc12))
}

// Rocq: Baza.baza_implem.tc13
pub fn tc13_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc13));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc13
// Variant: borrowed
pub fn tc13(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc13))
}

// Rocq: Baza.baza_implem.tc14
pub fn tc14_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc14));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc14
// Variant: borrowed
pub fn tc14(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc14))
}

// Rocq: Baza.baza_implem.tc15
pub fn tc15_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc15));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc15
// Variant: borrowed
pub fn tc15(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc15))
}

// Rocq: Baza.baza_implem.tc16
pub fn tc16_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc16));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc16
// Variant: borrowed
pub fn tc16(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc16))
}

// Rocq: Baza.baza_implem.tc17
pub fn tc17_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc17));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc17
// Variant: borrowed
pub fn tc17(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc17))
}

// Rocq: Baza.baza_implem.tc18
pub fn tc18_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc18));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc18
// Variant: borrowed
pub fn tc18(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc18))
}

// Rocq: Baza.baza_implem.tc19
pub fn tc19_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc19));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc19
// Variant: borrowed
pub fn tc19(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc19))
}

// Rocq: Baza.baza_implem.tc20
pub fn tc20_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc20));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc20
// Variant: borrowed
pub fn tc20(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc20))
}

// Rocq: Baza.baza_implem.tc21
pub fn tc21_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc21));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc21
// Variant: borrowed
pub fn tc21(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc21))
}

// Rocq: Baza.baza_implem.tc22
pub fn tc22_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc22));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc22
// Variant: borrowed
pub fn tc22(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc22))
}

// Rocq: Baza.baza_implem.tc23
pub fn tc23_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc23));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc23
// Variant: borrowed
pub fn tc23(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc23))
}

// Rocq: Baza.baza_implem.tc24
pub fn tc24_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc24));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc24
// Variant: borrowed
pub fn tc24(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc24))
}

// Rocq: Baza.baza_implem.tc25
pub fn tc25_owned(t: Rc<tab>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&t).tc25));
  std::mem::drop(t);
  v3
}

// Rocq: Baza.baza_implem.tc25
// Variant: borrowed
pub fn tc25(t: &Rc<tab>) -> Rc<Array<u64>> {
  let v1 = t;
  Rc::clone((&(&**v1).tc25))
}

// Rocq: Baza.baza_implem.sel
// Variant: uncurried
pub fn sel_owned(t: Rc<tab>, c: u64) -> Rc<Array<u64>> {
  match ltb(c, 13u64) {
    true => {
      match ltb(c, 6u64) {
        true => {
          match ltb(c, 3u64) {
            true => {
              match ltb(c, 1u64) {
                true => {
                  tc0_owned(t)
                },
                false => {
                  match ltb(c, 2u64) {
                    true => {
                      tc1_owned(t)
                    },
                    false => {
                      tc2_owned(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 4u64) {
                true => {
                  tc3_owned(t)
                },
                false => {
                  match ltb(c, 5u64) {
                    true => {
                      tc4_owned(t)
                    },
                    false => {
                      tc5_owned(t)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c, 9u64) {
            true => {
              match ltb(c, 7u64) {
                true => {
                  tc6_owned(t)
                },
                false => {
                  match ltb(c, 8u64) {
                    true => {
                      tc7_owned(t)
                    },
                    false => {
                      tc8_owned(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 11u64) {
                true => {
                  match ltb(c, 10u64) {
                    true => {
                      tc9_owned(t)
                    },
                    false => {
                      tc10_owned(t)
                    },
                  }
                },
                false => {
                  match ltb(c, 12u64) {
                    true => {
                      tc11_owned(t)
                    },
                    false => {
                      tc12_owned(t)
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    false => {
      match ltb(c, 19u64) {
        true => {
          match ltb(c, 16u64) {
            true => {
              match ltb(c, 14u64) {
                true => {
                  tc13_owned(t)
                },
                false => {
                  match ltb(c, 15u64) {
                    true => {
                      tc14_owned(t)
                    },
                    false => {
                      tc15_owned(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 17u64) {
                true => {
                  tc16_owned(t)
                },
                false => {
                  match ltb(c, 18u64) {
                    true => {
                      tc17_owned(t)
                    },
                    false => {
                      tc18_owned(t)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c, 22u64) {
            true => {
              match ltb(c, 20u64) {
                true => {
                  tc19_owned(t)
                },
                false => {
                  match ltb(c, 21u64) {
                    true => {
                      tc20_owned(t)
                    },
                    false => {
                      tc21_owned(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 24u64) {
                true => {
                  match ltb(c, 23u64) {
                    true => {
                      tc22_owned(t)
                    },
                    false => {
                      tc23_owned(t)
                    },
                  }
                },
                false => {
                  match ltb(c, 25u64) {
                    true => {
                      tc24_owned(t)
                    },
                    false => {
                      tc25_owned(t)
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

// Rocq: Baza.baza_implem.sel
// Variant: borrowed, uncurried
pub fn sel(t: &Rc<tab>, c: u64) -> Rc<Array<u64>> {
  let c_1 = c;
  match ltb(c_1, 13u64) {
    true => {
      match ltb(c_1, 6u64) {
        true => {
          match ltb(c_1, 3u64) {
            true => {
              match ltb(c_1, 1u64) {
                true => {
                  tc0(t)
                },
                false => {
                  match ltb(c_1, 2u64) {
                    true => {
                      tc1(t)
                    },
                    false => {
                      tc2(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c_1, 4u64) {
                true => {
                  tc3(t)
                },
                false => {
                  match ltb(c_1, 5u64) {
                    true => {
                      tc4(t)
                    },
                    false => {
                      tc5(t)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c_1, 9u64) {
            true => {
              match ltb(c_1, 7u64) {
                true => {
                  tc6(t)
                },
                false => {
                  match ltb(c_1, 8u64) {
                    true => {
                      tc7(t)
                    },
                    false => {
                      tc8(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c_1, 11u64) {
                true => {
                  match ltb(c_1, 10u64) {
                    true => {
                      tc9(t)
                    },
                    false => {
                      tc10(t)
                    },
                  }
                },
                false => {
                  match ltb(c_1, 12u64) {
                    true => {
                      tc11(t)
                    },
                    false => {
                      tc12(t)
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    false => {
      match ltb(c_1, 19u64) {
        true => {
          match ltb(c_1, 16u64) {
            true => {
              match ltb(c_1, 14u64) {
                true => {
                  tc13(t)
                },
                false => {
                  match ltb(c_1, 15u64) {
                    true => {
                      tc14(t)
                    },
                    false => {
                      tc15(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c_1, 17u64) {
                true => {
                  tc16(t)
                },
                false => {
                  match ltb(c_1, 18u64) {
                    true => {
                      tc17(t)
                    },
                    false => {
                      tc18(t)
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c_1, 22u64) {
            true => {
              match ltb(c_1, 20u64) {
                true => {
                  tc19(t)
                },
                false => {
                  match ltb(c_1, 21u64) {
                    true => {
                      tc20(t)
                    },
                    false => {
                      tc21(t)
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c_1, 24u64) {
                true => {
                  match ltb(c_1, 23u64) {
                    true => {
                      tc22(t)
                    },
                    false => {
                      tc23(t)
                    },
                  }
                },
                false => {
                  match ltb(c_1, 25u64) {
                    true => {
                      tc24(t)
                    },
                    false => {
                      tc25(t)
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

// Rocq: Baza.baza_implem.tget
// Variant: borrowed, uncurried
pub fn tget(t: &Rc<tab>, c: u64, n: u64) -> u64 {
  let c_1 = c;
  let n_1 = n;
  let v10 = sel(t, c_1);
  let v11 = &v10;
  let v14 = rocq_array::get::<u64>(&v11, n_1);
  std::mem::drop(v10);
  v14
}

// Rocq: Baza.baza_implem.upd
// Variant: uncurried
pub fn upd(t: Rc<tab>, c: u64, a: Rc<Array<u64>>) -> Rc<tab> {
  match ltb(c, 13u64) {
    true => {
      match ltb(c, 6u64) {
        true => {
          match ltb(c, 3u64) {
            true => {
              match ltb(c, 1u64) {
                true => {
                  let v42 = Rc::clone(&t);
                  let v43 = tc1_owned(v42);
                  let v47 = Rc::clone(&t);
                  let v48 = tc2_owned(v47);
                  let v52 = Rc::clone(&t);
                  let v53 = tc3_owned(v52);
                  let v57 = Rc::clone(&t);
                  let v58 = tc4_owned(v57);
                  let v62 = Rc::clone(&t);
                  let v63 = tc5_owned(v62);
                  let v67 = Rc::clone(&t);
                  let v68 = tc6_owned(v67);
                  let v72 = Rc::clone(&t);
                  let v73 = tc7_owned(v72);
                  let v77 = Rc::clone(&t);
                  let v78 = tc8_owned(v77);
                  let v82 = Rc::clone(&t);
                  let v83 = tc9_owned(v82);
                  let v87 = Rc::clone(&t);
                  let v88 = tc10_owned(v87);
                  let v92 = Rc::clone(&t);
                  let v93 = tc11_owned(v92);
                  let v97 = Rc::clone(&t);
                  let v98 = tc12_owned(v97);
                  let v102 = Rc::clone(&t);
                  let v103 = tc13_owned(v102);
                  let v107 = Rc::clone(&t);
                  let v108 = tc14_owned(v107);
                  let v112 = Rc::clone(&t);
                  let v113 = tc15_owned(v112);
                  let v117 = Rc::clone(&t);
                  let v118 = tc16_owned(v117);
                  let v122 = Rc::clone(&t);
                  let v123 = tc17_owned(v122);
                  let v127 = Rc::clone(&t);
                  let v128 = tc18_owned(v127);
                  let v132 = Rc::clone(&t);
                  let v133 = tc19_owned(v132);
                  let v137 = Rc::clone(&t);
                  let v138 = tc20_owned(v137);
                  let v142 = Rc::clone(&t);
                  let v143 = tc21_owned(v142);
                  let v147 = Rc::clone(&t);
                  let v148 = tc22_owned(v147);
                  let v152 = Rc::clone(&t);
                  let v153 = tc23_owned(v152);
                  let v157 = Rc::clone(&t);
                  let v158 = tc24_owned(v157);
                  let v162 = tc25_owned(t);
                  Rc::new(tab { tc0: a, tc1: v43, tc2: v48, tc3: v53, tc4: v58, tc5: v63, tc6: v68, tc7: v73, tc8: v78, tc9: v83, tc10: v88, tc11: v93, tc12: v98, tc13: v103, tc14: v108, tc15: v113, tc16: v118, tc17: v123, tc18: v128, tc19: v133, tc20: v138, tc21: v143, tc22: v148, tc23: v153, tc24: v158, tc25: v162 })
                },
                false => {
                  match ltb(c, 2u64) {
                    true => {
                      let v232 = Rc::clone(&t);
                      let v233 = tc0_owned(v232);
                      let v237 = Rc::clone(&t);
                      let v238 = tc2_owned(v237);
                      let v242 = Rc::clone(&t);
                      let v243 = tc3_owned(v242);
                      let v247 = Rc::clone(&t);
                      let v248 = tc4_owned(v247);
                      let v252 = Rc::clone(&t);
                      let v253 = tc5_owned(v252);
                      let v257 = Rc::clone(&t);
                      let v258 = tc6_owned(v257);
                      let v262 = Rc::clone(&t);
                      let v263 = tc7_owned(v262);
                      let v267 = Rc::clone(&t);
                      let v268 = tc8_owned(v267);
                      let v272 = Rc::clone(&t);
                      let v273 = tc9_owned(v272);
                      let v277 = Rc::clone(&t);
                      let v278 = tc10_owned(v277);
                      let v282 = Rc::clone(&t);
                      let v283 = tc11_owned(v282);
                      let v287 = Rc::clone(&t);
                      let v288 = tc12_owned(v287);
                      let v292 = Rc::clone(&t);
                      let v293 = tc13_owned(v292);
                      let v297 = Rc::clone(&t);
                      let v298 = tc14_owned(v297);
                      let v302 = Rc::clone(&t);
                      let v303 = tc15_owned(v302);
                      let v307 = Rc::clone(&t);
                      let v308 = tc16_owned(v307);
                      let v312 = Rc::clone(&t);
                      let v313 = tc17_owned(v312);
                      let v317 = Rc::clone(&t);
                      let v318 = tc18_owned(v317);
                      let v322 = Rc::clone(&t);
                      let v323 = tc19_owned(v322);
                      let v327 = Rc::clone(&t);
                      let v328 = tc20_owned(v327);
                      let v332 = Rc::clone(&t);
                      let v333 = tc21_owned(v332);
                      let v337 = Rc::clone(&t);
                      let v338 = tc22_owned(v337);
                      let v342 = Rc::clone(&t);
                      let v343 = tc23_owned(v342);
                      let v347 = Rc::clone(&t);
                      let v348 = tc24_owned(v347);
                      let v352 = tc25_owned(t);
                      Rc::new(tab { tc0: v233, tc1: a, tc2: v238, tc3: v243, tc4: v248, tc5: v253, tc6: v258, tc7: v263, tc8: v268, tc9: v273, tc10: v278, tc11: v283, tc12: v288, tc13: v293, tc14: v298, tc15: v303, tc16: v308, tc17: v313, tc18: v318, tc19: v323, tc20: v328, tc21: v333, tc22: v338, tc23: v343, tc24: v348, tc25: v352 })
                    },
                    false => {
                      let v413 = Rc::clone(&t);
                      let v414 = tc0_owned(v413);
                      let v418 = Rc::clone(&t);
                      let v419 = tc1_owned(v418);
                      let v423 = Rc::clone(&t);
                      let v424 = tc3_owned(v423);
                      let v428 = Rc::clone(&t);
                      let v429 = tc4_owned(v428);
                      let v433 = Rc::clone(&t);
                      let v434 = tc5_owned(v433);
                      let v438 = Rc::clone(&t);
                      let v439 = tc6_owned(v438);
                      let v443 = Rc::clone(&t);
                      let v444 = tc7_owned(v443);
                      let v448 = Rc::clone(&t);
                      let v449 = tc8_owned(v448);
                      let v453 = Rc::clone(&t);
                      let v454 = tc9_owned(v453);
                      let v458 = Rc::clone(&t);
                      let v459 = tc10_owned(v458);
                      let v463 = Rc::clone(&t);
                      let v464 = tc11_owned(v463);
                      let v468 = Rc::clone(&t);
                      let v469 = tc12_owned(v468);
                      let v473 = Rc::clone(&t);
                      let v474 = tc13_owned(v473);
                      let v478 = Rc::clone(&t);
                      let v479 = tc14_owned(v478);
                      let v483 = Rc::clone(&t);
                      let v484 = tc15_owned(v483);
                      let v488 = Rc::clone(&t);
                      let v489 = tc16_owned(v488);
                      let v493 = Rc::clone(&t);
                      let v494 = tc17_owned(v493);
                      let v498 = Rc::clone(&t);
                      let v499 = tc18_owned(v498);
                      let v503 = Rc::clone(&t);
                      let v504 = tc19_owned(v503);
                      let v508 = Rc::clone(&t);
                      let v509 = tc20_owned(v508);
                      let v513 = Rc::clone(&t);
                      let v514 = tc21_owned(v513);
                      let v518 = Rc::clone(&t);
                      let v519 = tc22_owned(v518);
                      let v523 = Rc::clone(&t);
                      let v524 = tc23_owned(v523);
                      let v528 = Rc::clone(&t);
                      let v529 = tc24_owned(v528);
                      let v533 = tc25_owned(t);
                      Rc::new(tab { tc0: v414, tc1: v419, tc2: a, tc3: v424, tc4: v429, tc5: v434, tc6: v439, tc7: v444, tc8: v449, tc9: v454, tc10: v459, tc11: v464, tc12: v469, tc13: v474, tc14: v479, tc15: v484, tc16: v489, tc17: v494, tc18: v499, tc19: v504, tc20: v509, tc21: v514, tc22: v519, tc23: v524, tc24: v529, tc25: v533 })
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 4u64) {
                true => {
                  let v609 = Rc::clone(&t);
                  let v610 = tc0_owned(v609);
                  let v614 = Rc::clone(&t);
                  let v615 = tc1_owned(v614);
                  let v619 = Rc::clone(&t);
                  let v620 = tc2_owned(v619);
                  let v624 = Rc::clone(&t);
                  let v625 = tc4_owned(v624);
                  let v629 = Rc::clone(&t);
                  let v630 = tc5_owned(v629);
                  let v634 = Rc::clone(&t);
                  let v635 = tc6_owned(v634);
                  let v639 = Rc::clone(&t);
                  let v640 = tc7_owned(v639);
                  let v644 = Rc::clone(&t);
                  let v645 = tc8_owned(v644);
                  let v649 = Rc::clone(&t);
                  let v650 = tc9_owned(v649);
                  let v654 = Rc::clone(&t);
                  let v655 = tc10_owned(v654);
                  let v659 = Rc::clone(&t);
                  let v660 = tc11_owned(v659);
                  let v664 = Rc::clone(&t);
                  let v665 = tc12_owned(v664);
                  let v669 = Rc::clone(&t);
                  let v670 = tc13_owned(v669);
                  let v674 = Rc::clone(&t);
                  let v675 = tc14_owned(v674);
                  let v679 = Rc::clone(&t);
                  let v680 = tc15_owned(v679);
                  let v684 = Rc::clone(&t);
                  let v685 = tc16_owned(v684);
                  let v689 = Rc::clone(&t);
                  let v690 = tc17_owned(v689);
                  let v694 = Rc::clone(&t);
                  let v695 = tc18_owned(v694);
                  let v699 = Rc::clone(&t);
                  let v700 = tc19_owned(v699);
                  let v704 = Rc::clone(&t);
                  let v705 = tc20_owned(v704);
                  let v709 = Rc::clone(&t);
                  let v710 = tc21_owned(v709);
                  let v714 = Rc::clone(&t);
                  let v715 = tc22_owned(v714);
                  let v719 = Rc::clone(&t);
                  let v720 = tc23_owned(v719);
                  let v724 = Rc::clone(&t);
                  let v725 = tc24_owned(v724);
                  let v729 = tc25_owned(t);
                  Rc::new(tab { tc0: v610, tc1: v615, tc2: v620, tc3: a, tc4: v625, tc5: v630, tc6: v635, tc7: v640, tc8: v645, tc9: v650, tc10: v655, tc11: v660, tc12: v665, tc13: v670, tc14: v675, tc15: v680, tc16: v685, tc17: v690, tc18: v695, tc19: v700, tc20: v705, tc21: v710, tc22: v715, tc23: v720, tc24: v725, tc25: v729 })
                },
                false => {
                  match ltb(c, 5u64) {
                    true => {
                      let v799 = Rc::clone(&t);
                      let v800 = tc0_owned(v799);
                      let v804 = Rc::clone(&t);
                      let v805 = tc1_owned(v804);
                      let v809 = Rc::clone(&t);
                      let v810 = tc2_owned(v809);
                      let v814 = Rc::clone(&t);
                      let v815 = tc3_owned(v814);
                      let v819 = Rc::clone(&t);
                      let v820 = tc5_owned(v819);
                      let v824 = Rc::clone(&t);
                      let v825 = tc6_owned(v824);
                      let v829 = Rc::clone(&t);
                      let v830 = tc7_owned(v829);
                      let v834 = Rc::clone(&t);
                      let v835 = tc8_owned(v834);
                      let v839 = Rc::clone(&t);
                      let v840 = tc9_owned(v839);
                      let v844 = Rc::clone(&t);
                      let v845 = tc10_owned(v844);
                      let v849 = Rc::clone(&t);
                      let v850 = tc11_owned(v849);
                      let v854 = Rc::clone(&t);
                      let v855 = tc12_owned(v854);
                      let v859 = Rc::clone(&t);
                      let v860 = tc13_owned(v859);
                      let v864 = Rc::clone(&t);
                      let v865 = tc14_owned(v864);
                      let v869 = Rc::clone(&t);
                      let v870 = tc15_owned(v869);
                      let v874 = Rc::clone(&t);
                      let v875 = tc16_owned(v874);
                      let v879 = Rc::clone(&t);
                      let v880 = tc17_owned(v879);
                      let v884 = Rc::clone(&t);
                      let v885 = tc18_owned(v884);
                      let v889 = Rc::clone(&t);
                      let v890 = tc19_owned(v889);
                      let v894 = Rc::clone(&t);
                      let v895 = tc20_owned(v894);
                      let v899 = Rc::clone(&t);
                      let v900 = tc21_owned(v899);
                      let v904 = Rc::clone(&t);
                      let v905 = tc22_owned(v904);
                      let v909 = Rc::clone(&t);
                      let v910 = tc23_owned(v909);
                      let v914 = Rc::clone(&t);
                      let v915 = tc24_owned(v914);
                      let v919 = tc25_owned(t);
                      Rc::new(tab { tc0: v800, tc1: v805, tc2: v810, tc3: v815, tc4: a, tc5: v820, tc6: v825, tc7: v830, tc8: v835, tc9: v840, tc10: v845, tc11: v850, tc12: v855, tc13: v860, tc14: v865, tc15: v870, tc16: v875, tc17: v880, tc18: v885, tc19: v890, tc20: v895, tc21: v900, tc22: v905, tc23: v910, tc24: v915, tc25: v919 })
                    },
                    false => {
                      let v980 = Rc::clone(&t);
                      let v981 = tc0_owned(v980);
                      let v985 = Rc::clone(&t);
                      let v986 = tc1_owned(v985);
                      let v990 = Rc::clone(&t);
                      let v991 = tc2_owned(v990);
                      let v995 = Rc::clone(&t);
                      let v996 = tc3_owned(v995);
                      let v1000 = Rc::clone(&t);
                      let v1001 = tc4_owned(v1000);
                      let v1005 = Rc::clone(&t);
                      let v1006 = tc6_owned(v1005);
                      let v1010 = Rc::clone(&t);
                      let v1011 = tc7_owned(v1010);
                      let v1015 = Rc::clone(&t);
                      let v1016 = tc8_owned(v1015);
                      let v1020 = Rc::clone(&t);
                      let v1021 = tc9_owned(v1020);
                      let v1025 = Rc::clone(&t);
                      let v1026 = tc10_owned(v1025);
                      let v1030 = Rc::clone(&t);
                      let v1031 = tc11_owned(v1030);
                      let v1035 = Rc::clone(&t);
                      let v1036 = tc12_owned(v1035);
                      let v1040 = Rc::clone(&t);
                      let v1041 = tc13_owned(v1040);
                      let v1045 = Rc::clone(&t);
                      let v1046 = tc14_owned(v1045);
                      let v1050 = Rc::clone(&t);
                      let v1051 = tc15_owned(v1050);
                      let v1055 = Rc::clone(&t);
                      let v1056 = tc16_owned(v1055);
                      let v1060 = Rc::clone(&t);
                      let v1061 = tc17_owned(v1060);
                      let v1065 = Rc::clone(&t);
                      let v1066 = tc18_owned(v1065);
                      let v1070 = Rc::clone(&t);
                      let v1071 = tc19_owned(v1070);
                      let v1075 = Rc::clone(&t);
                      let v1076 = tc20_owned(v1075);
                      let v1080 = Rc::clone(&t);
                      let v1081 = tc21_owned(v1080);
                      let v1085 = Rc::clone(&t);
                      let v1086 = tc22_owned(v1085);
                      let v1090 = Rc::clone(&t);
                      let v1091 = tc23_owned(v1090);
                      let v1095 = Rc::clone(&t);
                      let v1096 = tc24_owned(v1095);
                      let v1100 = tc25_owned(t);
                      Rc::new(tab { tc0: v981, tc1: v986, tc2: v991, tc3: v996, tc4: v1001, tc5: a, tc6: v1006, tc7: v1011, tc8: v1016, tc9: v1021, tc10: v1026, tc11: v1031, tc12: v1036, tc13: v1041, tc14: v1046, tc15: v1051, tc16: v1056, tc17: v1061, tc18: v1066, tc19: v1071, tc20: v1076, tc21: v1081, tc22: v1086, tc23: v1091, tc24: v1096, tc25: v1100 })
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c, 9u64) {
            true => {
              match ltb(c, 7u64) {
                true => {
                  let v1188 = Rc::clone(&t);
                  let v1189 = tc0_owned(v1188);
                  let v1193 = Rc::clone(&t);
                  let v1194 = tc1_owned(v1193);
                  let v1198 = Rc::clone(&t);
                  let v1199 = tc2_owned(v1198);
                  let v1203 = Rc::clone(&t);
                  let v1204 = tc3_owned(v1203);
                  let v1208 = Rc::clone(&t);
                  let v1209 = tc4_owned(v1208);
                  let v1213 = Rc::clone(&t);
                  let v1214 = tc5_owned(v1213);
                  let v1218 = Rc::clone(&t);
                  let v1219 = tc7_owned(v1218);
                  let v1223 = Rc::clone(&t);
                  let v1224 = tc8_owned(v1223);
                  let v1228 = Rc::clone(&t);
                  let v1229 = tc9_owned(v1228);
                  let v1233 = Rc::clone(&t);
                  let v1234 = tc10_owned(v1233);
                  let v1238 = Rc::clone(&t);
                  let v1239 = tc11_owned(v1238);
                  let v1243 = Rc::clone(&t);
                  let v1244 = tc12_owned(v1243);
                  let v1248 = Rc::clone(&t);
                  let v1249 = tc13_owned(v1248);
                  let v1253 = Rc::clone(&t);
                  let v1254 = tc14_owned(v1253);
                  let v1258 = Rc::clone(&t);
                  let v1259 = tc15_owned(v1258);
                  let v1263 = Rc::clone(&t);
                  let v1264 = tc16_owned(v1263);
                  let v1268 = Rc::clone(&t);
                  let v1269 = tc17_owned(v1268);
                  let v1273 = Rc::clone(&t);
                  let v1274 = tc18_owned(v1273);
                  let v1278 = Rc::clone(&t);
                  let v1279 = tc19_owned(v1278);
                  let v1283 = Rc::clone(&t);
                  let v1284 = tc20_owned(v1283);
                  let v1288 = Rc::clone(&t);
                  let v1289 = tc21_owned(v1288);
                  let v1293 = Rc::clone(&t);
                  let v1294 = tc22_owned(v1293);
                  let v1298 = Rc::clone(&t);
                  let v1299 = tc23_owned(v1298);
                  let v1303 = Rc::clone(&t);
                  let v1304 = tc24_owned(v1303);
                  let v1308 = tc25_owned(t);
                  Rc::new(tab { tc0: v1189, tc1: v1194, tc2: v1199, tc3: v1204, tc4: v1209, tc5: v1214, tc6: a, tc7: v1219, tc8: v1224, tc9: v1229, tc10: v1234, tc11: v1239, tc12: v1244, tc13: v1249, tc14: v1254, tc15: v1259, tc16: v1264, tc17: v1269, tc18: v1274, tc19: v1279, tc20: v1284, tc21: v1289, tc22: v1294, tc23: v1299, tc24: v1304, tc25: v1308 })
                },
                false => {
                  match ltb(c, 8u64) {
                    true => {
                      let v1378 = Rc::clone(&t);
                      let v1379 = tc0_owned(v1378);
                      let v1383 = Rc::clone(&t);
                      let v1384 = tc1_owned(v1383);
                      let v1388 = Rc::clone(&t);
                      let v1389 = tc2_owned(v1388);
                      let v1393 = Rc::clone(&t);
                      let v1394 = tc3_owned(v1393);
                      let v1398 = Rc::clone(&t);
                      let v1399 = tc4_owned(v1398);
                      let v1403 = Rc::clone(&t);
                      let v1404 = tc5_owned(v1403);
                      let v1408 = Rc::clone(&t);
                      let v1409 = tc6_owned(v1408);
                      let v1413 = Rc::clone(&t);
                      let v1414 = tc8_owned(v1413);
                      let v1418 = Rc::clone(&t);
                      let v1419 = tc9_owned(v1418);
                      let v1423 = Rc::clone(&t);
                      let v1424 = tc10_owned(v1423);
                      let v1428 = Rc::clone(&t);
                      let v1429 = tc11_owned(v1428);
                      let v1433 = Rc::clone(&t);
                      let v1434 = tc12_owned(v1433);
                      let v1438 = Rc::clone(&t);
                      let v1439 = tc13_owned(v1438);
                      let v1443 = Rc::clone(&t);
                      let v1444 = tc14_owned(v1443);
                      let v1448 = Rc::clone(&t);
                      let v1449 = tc15_owned(v1448);
                      let v1453 = Rc::clone(&t);
                      let v1454 = tc16_owned(v1453);
                      let v1458 = Rc::clone(&t);
                      let v1459 = tc17_owned(v1458);
                      let v1463 = Rc::clone(&t);
                      let v1464 = tc18_owned(v1463);
                      let v1468 = Rc::clone(&t);
                      let v1469 = tc19_owned(v1468);
                      let v1473 = Rc::clone(&t);
                      let v1474 = tc20_owned(v1473);
                      let v1478 = Rc::clone(&t);
                      let v1479 = tc21_owned(v1478);
                      let v1483 = Rc::clone(&t);
                      let v1484 = tc22_owned(v1483);
                      let v1488 = Rc::clone(&t);
                      let v1489 = tc23_owned(v1488);
                      let v1493 = Rc::clone(&t);
                      let v1494 = tc24_owned(v1493);
                      let v1498 = tc25_owned(t);
                      Rc::new(tab { tc0: v1379, tc1: v1384, tc2: v1389, tc3: v1394, tc4: v1399, tc5: v1404, tc6: v1409, tc7: a, tc8: v1414, tc9: v1419, tc10: v1424, tc11: v1429, tc12: v1434, tc13: v1439, tc14: v1444, tc15: v1449, tc16: v1454, tc17: v1459, tc18: v1464, tc19: v1469, tc20: v1474, tc21: v1479, tc22: v1484, tc23: v1489, tc24: v1494, tc25: v1498 })
                    },
                    false => {
                      let v1559 = Rc::clone(&t);
                      let v1560 = tc0_owned(v1559);
                      let v1564 = Rc::clone(&t);
                      let v1565 = tc1_owned(v1564);
                      let v1569 = Rc::clone(&t);
                      let v1570 = tc2_owned(v1569);
                      let v1574 = Rc::clone(&t);
                      let v1575 = tc3_owned(v1574);
                      let v1579 = Rc::clone(&t);
                      let v1580 = tc4_owned(v1579);
                      let v1584 = Rc::clone(&t);
                      let v1585 = tc5_owned(v1584);
                      let v1589 = Rc::clone(&t);
                      let v1590 = tc6_owned(v1589);
                      let v1594 = Rc::clone(&t);
                      let v1595 = tc7_owned(v1594);
                      let v1599 = Rc::clone(&t);
                      let v1600 = tc9_owned(v1599);
                      let v1604 = Rc::clone(&t);
                      let v1605 = tc10_owned(v1604);
                      let v1609 = Rc::clone(&t);
                      let v1610 = tc11_owned(v1609);
                      let v1614 = Rc::clone(&t);
                      let v1615 = tc12_owned(v1614);
                      let v1619 = Rc::clone(&t);
                      let v1620 = tc13_owned(v1619);
                      let v1624 = Rc::clone(&t);
                      let v1625 = tc14_owned(v1624);
                      let v1629 = Rc::clone(&t);
                      let v1630 = tc15_owned(v1629);
                      let v1634 = Rc::clone(&t);
                      let v1635 = tc16_owned(v1634);
                      let v1639 = Rc::clone(&t);
                      let v1640 = tc17_owned(v1639);
                      let v1644 = Rc::clone(&t);
                      let v1645 = tc18_owned(v1644);
                      let v1649 = Rc::clone(&t);
                      let v1650 = tc19_owned(v1649);
                      let v1654 = Rc::clone(&t);
                      let v1655 = tc20_owned(v1654);
                      let v1659 = Rc::clone(&t);
                      let v1660 = tc21_owned(v1659);
                      let v1664 = Rc::clone(&t);
                      let v1665 = tc22_owned(v1664);
                      let v1669 = Rc::clone(&t);
                      let v1670 = tc23_owned(v1669);
                      let v1674 = Rc::clone(&t);
                      let v1675 = tc24_owned(v1674);
                      let v1679 = tc25_owned(t);
                      Rc::new(tab { tc0: v1560, tc1: v1565, tc2: v1570, tc3: v1575, tc4: v1580, tc5: v1585, tc6: v1590, tc7: v1595, tc8: a, tc9: v1600, tc10: v1605, tc11: v1610, tc12: v1615, tc13: v1620, tc14: v1625, tc15: v1630, tc16: v1635, tc17: v1640, tc18: v1645, tc19: v1650, tc20: v1655, tc21: v1660, tc22: v1665, tc23: v1670, tc24: v1675, tc25: v1679 })
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 11u64) {
                true => {
                  match ltb(c, 10u64) {
                    true => {
                      let v1764 = Rc::clone(&t);
                      let v1765 = tc0_owned(v1764);
                      let v1769 = Rc::clone(&t);
                      let v1770 = tc1_owned(v1769);
                      let v1774 = Rc::clone(&t);
                      let v1775 = tc2_owned(v1774);
                      let v1779 = Rc::clone(&t);
                      let v1780 = tc3_owned(v1779);
                      let v1784 = Rc::clone(&t);
                      let v1785 = tc4_owned(v1784);
                      let v1789 = Rc::clone(&t);
                      let v1790 = tc5_owned(v1789);
                      let v1794 = Rc::clone(&t);
                      let v1795 = tc6_owned(v1794);
                      let v1799 = Rc::clone(&t);
                      let v1800 = tc7_owned(v1799);
                      let v1804 = Rc::clone(&t);
                      let v1805 = tc8_owned(v1804);
                      let v1809 = Rc::clone(&t);
                      let v1810 = tc10_owned(v1809);
                      let v1814 = Rc::clone(&t);
                      let v1815 = tc11_owned(v1814);
                      let v1819 = Rc::clone(&t);
                      let v1820 = tc12_owned(v1819);
                      let v1824 = Rc::clone(&t);
                      let v1825 = tc13_owned(v1824);
                      let v1829 = Rc::clone(&t);
                      let v1830 = tc14_owned(v1829);
                      let v1834 = Rc::clone(&t);
                      let v1835 = tc15_owned(v1834);
                      let v1839 = Rc::clone(&t);
                      let v1840 = tc16_owned(v1839);
                      let v1844 = Rc::clone(&t);
                      let v1845 = tc17_owned(v1844);
                      let v1849 = Rc::clone(&t);
                      let v1850 = tc18_owned(v1849);
                      let v1854 = Rc::clone(&t);
                      let v1855 = tc19_owned(v1854);
                      let v1859 = Rc::clone(&t);
                      let v1860 = tc20_owned(v1859);
                      let v1864 = Rc::clone(&t);
                      let v1865 = tc21_owned(v1864);
                      let v1869 = Rc::clone(&t);
                      let v1870 = tc22_owned(v1869);
                      let v1874 = Rc::clone(&t);
                      let v1875 = tc23_owned(v1874);
                      let v1879 = Rc::clone(&t);
                      let v1880 = tc24_owned(v1879);
                      let v1884 = tc25_owned(t);
                      Rc::new(tab { tc0: v1765, tc1: v1770, tc2: v1775, tc3: v1780, tc4: v1785, tc5: v1790, tc6: v1795, tc7: v1800, tc8: v1805, tc9: a, tc10: v1810, tc11: v1815, tc12: v1820, tc13: v1825, tc14: v1830, tc15: v1835, tc16: v1840, tc17: v1845, tc18: v1850, tc19: v1855, tc20: v1860, tc21: v1865, tc22: v1870, tc23: v1875, tc24: v1880, tc25: v1884 })
                    },
                    false => {
                      let v1945 = Rc::clone(&t);
                      let v1946 = tc0_owned(v1945);
                      let v1950 = Rc::clone(&t);
                      let v1951 = tc1_owned(v1950);
                      let v1955 = Rc::clone(&t);
                      let v1956 = tc2_owned(v1955);
                      let v1960 = Rc::clone(&t);
                      let v1961 = tc3_owned(v1960);
                      let v1965 = Rc::clone(&t);
                      let v1966 = tc4_owned(v1965);
                      let v1970 = Rc::clone(&t);
                      let v1971 = tc5_owned(v1970);
                      let v1975 = Rc::clone(&t);
                      let v1976 = tc6_owned(v1975);
                      let v1980 = Rc::clone(&t);
                      let v1981 = tc7_owned(v1980);
                      let v1985 = Rc::clone(&t);
                      let v1986 = tc8_owned(v1985);
                      let v1990 = Rc::clone(&t);
                      let v1991 = tc9_owned(v1990);
                      let v1995 = Rc::clone(&t);
                      let v1996 = tc11_owned(v1995);
                      let v2000 = Rc::clone(&t);
                      let v2001 = tc12_owned(v2000);
                      let v2005 = Rc::clone(&t);
                      let v2006 = tc13_owned(v2005);
                      let v2010 = Rc::clone(&t);
                      let v2011 = tc14_owned(v2010);
                      let v2015 = Rc::clone(&t);
                      let v2016 = tc15_owned(v2015);
                      let v2020 = Rc::clone(&t);
                      let v2021 = tc16_owned(v2020);
                      let v2025 = Rc::clone(&t);
                      let v2026 = tc17_owned(v2025);
                      let v2030 = Rc::clone(&t);
                      let v2031 = tc18_owned(v2030);
                      let v2035 = Rc::clone(&t);
                      let v2036 = tc19_owned(v2035);
                      let v2040 = Rc::clone(&t);
                      let v2041 = tc20_owned(v2040);
                      let v2045 = Rc::clone(&t);
                      let v2046 = tc21_owned(v2045);
                      let v2050 = Rc::clone(&t);
                      let v2051 = tc22_owned(v2050);
                      let v2055 = Rc::clone(&t);
                      let v2056 = tc23_owned(v2055);
                      let v2060 = Rc::clone(&t);
                      let v2061 = tc24_owned(v2060);
                      let v2065 = tc25_owned(t);
                      Rc::new(tab { tc0: v1946, tc1: v1951, tc2: v1956, tc3: v1961, tc4: v1966, tc5: v1971, tc6: v1976, tc7: v1981, tc8: v1986, tc9: v1991, tc10: a, tc11: v1996, tc12: v2001, tc13: v2006, tc14: v2011, tc15: v2016, tc16: v2021, tc17: v2026, tc18: v2031, tc19: v2036, tc20: v2041, tc21: v2046, tc22: v2051, tc23: v2056, tc24: v2061, tc25: v2065 })
                    },
                  }
                },
                false => {
                  match ltb(c, 12u64) {
                    true => {
                      let v2138 = Rc::clone(&t);
                      let v2139 = tc0_owned(v2138);
                      let v2143 = Rc::clone(&t);
                      let v2144 = tc1_owned(v2143);
                      let v2148 = Rc::clone(&t);
                      let v2149 = tc2_owned(v2148);
                      let v2153 = Rc::clone(&t);
                      let v2154 = tc3_owned(v2153);
                      let v2158 = Rc::clone(&t);
                      let v2159 = tc4_owned(v2158);
                      let v2163 = Rc::clone(&t);
                      let v2164 = tc5_owned(v2163);
                      let v2168 = Rc::clone(&t);
                      let v2169 = tc6_owned(v2168);
                      let v2173 = Rc::clone(&t);
                      let v2174 = tc7_owned(v2173);
                      let v2178 = Rc::clone(&t);
                      let v2179 = tc8_owned(v2178);
                      let v2183 = Rc::clone(&t);
                      let v2184 = tc9_owned(v2183);
                      let v2188 = Rc::clone(&t);
                      let v2189 = tc10_owned(v2188);
                      let v2193 = Rc::clone(&t);
                      let v2194 = tc12_owned(v2193);
                      let v2198 = Rc::clone(&t);
                      let v2199 = tc13_owned(v2198);
                      let v2203 = Rc::clone(&t);
                      let v2204 = tc14_owned(v2203);
                      let v2208 = Rc::clone(&t);
                      let v2209 = tc15_owned(v2208);
                      let v2213 = Rc::clone(&t);
                      let v2214 = tc16_owned(v2213);
                      let v2218 = Rc::clone(&t);
                      let v2219 = tc17_owned(v2218);
                      let v2223 = Rc::clone(&t);
                      let v2224 = tc18_owned(v2223);
                      let v2228 = Rc::clone(&t);
                      let v2229 = tc19_owned(v2228);
                      let v2233 = Rc::clone(&t);
                      let v2234 = tc20_owned(v2233);
                      let v2238 = Rc::clone(&t);
                      let v2239 = tc21_owned(v2238);
                      let v2243 = Rc::clone(&t);
                      let v2244 = tc22_owned(v2243);
                      let v2248 = Rc::clone(&t);
                      let v2249 = tc23_owned(v2248);
                      let v2253 = Rc::clone(&t);
                      let v2254 = tc24_owned(v2253);
                      let v2258 = tc25_owned(t);
                      Rc::new(tab { tc0: v2139, tc1: v2144, tc2: v2149, tc3: v2154, tc4: v2159, tc5: v2164, tc6: v2169, tc7: v2174, tc8: v2179, tc9: v2184, tc10: v2189, tc11: a, tc12: v2194, tc13: v2199, tc14: v2204, tc15: v2209, tc16: v2214, tc17: v2219, tc18: v2224, tc19: v2229, tc20: v2234, tc21: v2239, tc22: v2244, tc23: v2249, tc24: v2254, tc25: v2258 })
                    },
                    false => {
                      let v2319 = Rc::clone(&t);
                      let v2320 = tc0_owned(v2319);
                      let v2324 = Rc::clone(&t);
                      let v2325 = tc1_owned(v2324);
                      let v2329 = Rc::clone(&t);
                      let v2330 = tc2_owned(v2329);
                      let v2334 = Rc::clone(&t);
                      let v2335 = tc3_owned(v2334);
                      let v2339 = Rc::clone(&t);
                      let v2340 = tc4_owned(v2339);
                      let v2344 = Rc::clone(&t);
                      let v2345 = tc5_owned(v2344);
                      let v2349 = Rc::clone(&t);
                      let v2350 = tc6_owned(v2349);
                      let v2354 = Rc::clone(&t);
                      let v2355 = tc7_owned(v2354);
                      let v2359 = Rc::clone(&t);
                      let v2360 = tc8_owned(v2359);
                      let v2364 = Rc::clone(&t);
                      let v2365 = tc9_owned(v2364);
                      let v2369 = Rc::clone(&t);
                      let v2370 = tc10_owned(v2369);
                      let v2374 = Rc::clone(&t);
                      let v2375 = tc11_owned(v2374);
                      let v2379 = Rc::clone(&t);
                      let v2380 = tc13_owned(v2379);
                      let v2384 = Rc::clone(&t);
                      let v2385 = tc14_owned(v2384);
                      let v2389 = Rc::clone(&t);
                      let v2390 = tc15_owned(v2389);
                      let v2394 = Rc::clone(&t);
                      let v2395 = tc16_owned(v2394);
                      let v2399 = Rc::clone(&t);
                      let v2400 = tc17_owned(v2399);
                      let v2404 = Rc::clone(&t);
                      let v2405 = tc18_owned(v2404);
                      let v2409 = Rc::clone(&t);
                      let v2410 = tc19_owned(v2409);
                      let v2414 = Rc::clone(&t);
                      let v2415 = tc20_owned(v2414);
                      let v2419 = Rc::clone(&t);
                      let v2420 = tc21_owned(v2419);
                      let v2424 = Rc::clone(&t);
                      let v2425 = tc22_owned(v2424);
                      let v2429 = Rc::clone(&t);
                      let v2430 = tc23_owned(v2429);
                      let v2434 = Rc::clone(&t);
                      let v2435 = tc24_owned(v2434);
                      let v2439 = tc25_owned(t);
                      Rc::new(tab { tc0: v2320, tc1: v2325, tc2: v2330, tc3: v2335, tc4: v2340, tc5: v2345, tc6: v2350, tc7: v2355, tc8: v2360, tc9: v2365, tc10: v2370, tc11: v2375, tc12: a, tc13: v2380, tc14: v2385, tc15: v2390, tc16: v2395, tc17: v2400, tc18: v2405, tc19: v2410, tc20: v2415, tc21: v2420, tc22: v2425, tc23: v2430, tc24: v2435, tc25: v2439 })
                    },
                  }
                },
              }
            },
          }
        },
      }
    },
    false => {
      match ltb(c, 19u64) {
        true => {
          match ltb(c, 16u64) {
            true => {
              match ltb(c, 14u64) {
                true => {
                  let v2539 = Rc::clone(&t);
                  let v2540 = tc0_owned(v2539);
                  let v2544 = Rc::clone(&t);
                  let v2545 = tc1_owned(v2544);
                  let v2549 = Rc::clone(&t);
                  let v2550 = tc2_owned(v2549);
                  let v2554 = Rc::clone(&t);
                  let v2555 = tc3_owned(v2554);
                  let v2559 = Rc::clone(&t);
                  let v2560 = tc4_owned(v2559);
                  let v2564 = Rc::clone(&t);
                  let v2565 = tc5_owned(v2564);
                  let v2569 = Rc::clone(&t);
                  let v2570 = tc6_owned(v2569);
                  let v2574 = Rc::clone(&t);
                  let v2575 = tc7_owned(v2574);
                  let v2579 = Rc::clone(&t);
                  let v2580 = tc8_owned(v2579);
                  let v2584 = Rc::clone(&t);
                  let v2585 = tc9_owned(v2584);
                  let v2589 = Rc::clone(&t);
                  let v2590 = tc10_owned(v2589);
                  let v2594 = Rc::clone(&t);
                  let v2595 = tc11_owned(v2594);
                  let v2599 = Rc::clone(&t);
                  let v2600 = tc12_owned(v2599);
                  let v2604 = Rc::clone(&t);
                  let v2605 = tc14_owned(v2604);
                  let v2609 = Rc::clone(&t);
                  let v2610 = tc15_owned(v2609);
                  let v2614 = Rc::clone(&t);
                  let v2615 = tc16_owned(v2614);
                  let v2619 = Rc::clone(&t);
                  let v2620 = tc17_owned(v2619);
                  let v2624 = Rc::clone(&t);
                  let v2625 = tc18_owned(v2624);
                  let v2629 = Rc::clone(&t);
                  let v2630 = tc19_owned(v2629);
                  let v2634 = Rc::clone(&t);
                  let v2635 = tc20_owned(v2634);
                  let v2639 = Rc::clone(&t);
                  let v2640 = tc21_owned(v2639);
                  let v2644 = Rc::clone(&t);
                  let v2645 = tc22_owned(v2644);
                  let v2649 = Rc::clone(&t);
                  let v2650 = tc23_owned(v2649);
                  let v2654 = Rc::clone(&t);
                  let v2655 = tc24_owned(v2654);
                  let v2659 = tc25_owned(t);
                  Rc::new(tab { tc0: v2540, tc1: v2545, tc2: v2550, tc3: v2555, tc4: v2560, tc5: v2565, tc6: v2570, tc7: v2575, tc8: v2580, tc9: v2585, tc10: v2590, tc11: v2595, tc12: v2600, tc13: a, tc14: v2605, tc15: v2610, tc16: v2615, tc17: v2620, tc18: v2625, tc19: v2630, tc20: v2635, tc21: v2640, tc22: v2645, tc23: v2650, tc24: v2655, tc25: v2659 })
                },
                false => {
                  match ltb(c, 15u64) {
                    true => {
                      let v2729 = Rc::clone(&t);
                      let v2730 = tc0_owned(v2729);
                      let v2734 = Rc::clone(&t);
                      let v2735 = tc1_owned(v2734);
                      let v2739 = Rc::clone(&t);
                      let v2740 = tc2_owned(v2739);
                      let v2744 = Rc::clone(&t);
                      let v2745 = tc3_owned(v2744);
                      let v2749 = Rc::clone(&t);
                      let v2750 = tc4_owned(v2749);
                      let v2754 = Rc::clone(&t);
                      let v2755 = tc5_owned(v2754);
                      let v2759 = Rc::clone(&t);
                      let v2760 = tc6_owned(v2759);
                      let v2764 = Rc::clone(&t);
                      let v2765 = tc7_owned(v2764);
                      let v2769 = Rc::clone(&t);
                      let v2770 = tc8_owned(v2769);
                      let v2774 = Rc::clone(&t);
                      let v2775 = tc9_owned(v2774);
                      let v2779 = Rc::clone(&t);
                      let v2780 = tc10_owned(v2779);
                      let v2784 = Rc::clone(&t);
                      let v2785 = tc11_owned(v2784);
                      let v2789 = Rc::clone(&t);
                      let v2790 = tc12_owned(v2789);
                      let v2794 = Rc::clone(&t);
                      let v2795 = tc13_owned(v2794);
                      let v2799 = Rc::clone(&t);
                      let v2800 = tc15_owned(v2799);
                      let v2804 = Rc::clone(&t);
                      let v2805 = tc16_owned(v2804);
                      let v2809 = Rc::clone(&t);
                      let v2810 = tc17_owned(v2809);
                      let v2814 = Rc::clone(&t);
                      let v2815 = tc18_owned(v2814);
                      let v2819 = Rc::clone(&t);
                      let v2820 = tc19_owned(v2819);
                      let v2824 = Rc::clone(&t);
                      let v2825 = tc20_owned(v2824);
                      let v2829 = Rc::clone(&t);
                      let v2830 = tc21_owned(v2829);
                      let v2834 = Rc::clone(&t);
                      let v2835 = tc22_owned(v2834);
                      let v2839 = Rc::clone(&t);
                      let v2840 = tc23_owned(v2839);
                      let v2844 = Rc::clone(&t);
                      let v2845 = tc24_owned(v2844);
                      let v2849 = tc25_owned(t);
                      Rc::new(tab { tc0: v2730, tc1: v2735, tc2: v2740, tc3: v2745, tc4: v2750, tc5: v2755, tc6: v2760, tc7: v2765, tc8: v2770, tc9: v2775, tc10: v2780, tc11: v2785, tc12: v2790, tc13: v2795, tc14: a, tc15: v2800, tc16: v2805, tc17: v2810, tc18: v2815, tc19: v2820, tc20: v2825, tc21: v2830, tc22: v2835, tc23: v2840, tc24: v2845, tc25: v2849 })
                    },
                    false => {
                      let v2910 = Rc::clone(&t);
                      let v2911 = tc0_owned(v2910);
                      let v2915 = Rc::clone(&t);
                      let v2916 = tc1_owned(v2915);
                      let v2920 = Rc::clone(&t);
                      let v2921 = tc2_owned(v2920);
                      let v2925 = Rc::clone(&t);
                      let v2926 = tc3_owned(v2925);
                      let v2930 = Rc::clone(&t);
                      let v2931 = tc4_owned(v2930);
                      let v2935 = Rc::clone(&t);
                      let v2936 = tc5_owned(v2935);
                      let v2940 = Rc::clone(&t);
                      let v2941 = tc6_owned(v2940);
                      let v2945 = Rc::clone(&t);
                      let v2946 = tc7_owned(v2945);
                      let v2950 = Rc::clone(&t);
                      let v2951 = tc8_owned(v2950);
                      let v2955 = Rc::clone(&t);
                      let v2956 = tc9_owned(v2955);
                      let v2960 = Rc::clone(&t);
                      let v2961 = tc10_owned(v2960);
                      let v2965 = Rc::clone(&t);
                      let v2966 = tc11_owned(v2965);
                      let v2970 = Rc::clone(&t);
                      let v2971 = tc12_owned(v2970);
                      let v2975 = Rc::clone(&t);
                      let v2976 = tc13_owned(v2975);
                      let v2980 = Rc::clone(&t);
                      let v2981 = tc14_owned(v2980);
                      let v2985 = Rc::clone(&t);
                      let v2986 = tc16_owned(v2985);
                      let v2990 = Rc::clone(&t);
                      let v2991 = tc17_owned(v2990);
                      let v2995 = Rc::clone(&t);
                      let v2996 = tc18_owned(v2995);
                      let v3000 = Rc::clone(&t);
                      let v3001 = tc19_owned(v3000);
                      let v3005 = Rc::clone(&t);
                      let v3006 = tc20_owned(v3005);
                      let v3010 = Rc::clone(&t);
                      let v3011 = tc21_owned(v3010);
                      let v3015 = Rc::clone(&t);
                      let v3016 = tc22_owned(v3015);
                      let v3020 = Rc::clone(&t);
                      let v3021 = tc23_owned(v3020);
                      let v3025 = Rc::clone(&t);
                      let v3026 = tc24_owned(v3025);
                      let v3030 = tc25_owned(t);
                      Rc::new(tab { tc0: v2911, tc1: v2916, tc2: v2921, tc3: v2926, tc4: v2931, tc5: v2936, tc6: v2941, tc7: v2946, tc8: v2951, tc9: v2956, tc10: v2961, tc11: v2966, tc12: v2971, tc13: v2976, tc14: v2981, tc15: a, tc16: v2986, tc17: v2991, tc18: v2996, tc19: v3001, tc20: v3006, tc21: v3011, tc22: v3016, tc23: v3021, tc24: v3026, tc25: v3030 })
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 17u64) {
                true => {
                  let v3106 = Rc::clone(&t);
                  let v3107 = tc0_owned(v3106);
                  let v3111 = Rc::clone(&t);
                  let v3112 = tc1_owned(v3111);
                  let v3116 = Rc::clone(&t);
                  let v3117 = tc2_owned(v3116);
                  let v3121 = Rc::clone(&t);
                  let v3122 = tc3_owned(v3121);
                  let v3126 = Rc::clone(&t);
                  let v3127 = tc4_owned(v3126);
                  let v3131 = Rc::clone(&t);
                  let v3132 = tc5_owned(v3131);
                  let v3136 = Rc::clone(&t);
                  let v3137 = tc6_owned(v3136);
                  let v3141 = Rc::clone(&t);
                  let v3142 = tc7_owned(v3141);
                  let v3146 = Rc::clone(&t);
                  let v3147 = tc8_owned(v3146);
                  let v3151 = Rc::clone(&t);
                  let v3152 = tc9_owned(v3151);
                  let v3156 = Rc::clone(&t);
                  let v3157 = tc10_owned(v3156);
                  let v3161 = Rc::clone(&t);
                  let v3162 = tc11_owned(v3161);
                  let v3166 = Rc::clone(&t);
                  let v3167 = tc12_owned(v3166);
                  let v3171 = Rc::clone(&t);
                  let v3172 = tc13_owned(v3171);
                  let v3176 = Rc::clone(&t);
                  let v3177 = tc14_owned(v3176);
                  let v3181 = Rc::clone(&t);
                  let v3182 = tc15_owned(v3181);
                  let v3186 = Rc::clone(&t);
                  let v3187 = tc17_owned(v3186);
                  let v3191 = Rc::clone(&t);
                  let v3192 = tc18_owned(v3191);
                  let v3196 = Rc::clone(&t);
                  let v3197 = tc19_owned(v3196);
                  let v3201 = Rc::clone(&t);
                  let v3202 = tc20_owned(v3201);
                  let v3206 = Rc::clone(&t);
                  let v3207 = tc21_owned(v3206);
                  let v3211 = Rc::clone(&t);
                  let v3212 = tc22_owned(v3211);
                  let v3216 = Rc::clone(&t);
                  let v3217 = tc23_owned(v3216);
                  let v3221 = Rc::clone(&t);
                  let v3222 = tc24_owned(v3221);
                  let v3226 = tc25_owned(t);
                  Rc::new(tab { tc0: v3107, tc1: v3112, tc2: v3117, tc3: v3122, tc4: v3127, tc5: v3132, tc6: v3137, tc7: v3142, tc8: v3147, tc9: v3152, tc10: v3157, tc11: v3162, tc12: v3167, tc13: v3172, tc14: v3177, tc15: v3182, tc16: a, tc17: v3187, tc18: v3192, tc19: v3197, tc20: v3202, tc21: v3207, tc22: v3212, tc23: v3217, tc24: v3222, tc25: v3226 })
                },
                false => {
                  match ltb(c, 18u64) {
                    true => {
                      let v3296 = Rc::clone(&t);
                      let v3297 = tc0_owned(v3296);
                      let v3301 = Rc::clone(&t);
                      let v3302 = tc1_owned(v3301);
                      let v3306 = Rc::clone(&t);
                      let v3307 = tc2_owned(v3306);
                      let v3311 = Rc::clone(&t);
                      let v3312 = tc3_owned(v3311);
                      let v3316 = Rc::clone(&t);
                      let v3317 = tc4_owned(v3316);
                      let v3321 = Rc::clone(&t);
                      let v3322 = tc5_owned(v3321);
                      let v3326 = Rc::clone(&t);
                      let v3327 = tc6_owned(v3326);
                      let v3331 = Rc::clone(&t);
                      let v3332 = tc7_owned(v3331);
                      let v3336 = Rc::clone(&t);
                      let v3337 = tc8_owned(v3336);
                      let v3341 = Rc::clone(&t);
                      let v3342 = tc9_owned(v3341);
                      let v3346 = Rc::clone(&t);
                      let v3347 = tc10_owned(v3346);
                      let v3351 = Rc::clone(&t);
                      let v3352 = tc11_owned(v3351);
                      let v3356 = Rc::clone(&t);
                      let v3357 = tc12_owned(v3356);
                      let v3361 = Rc::clone(&t);
                      let v3362 = tc13_owned(v3361);
                      let v3366 = Rc::clone(&t);
                      let v3367 = tc14_owned(v3366);
                      let v3371 = Rc::clone(&t);
                      let v3372 = tc15_owned(v3371);
                      let v3376 = Rc::clone(&t);
                      let v3377 = tc16_owned(v3376);
                      let v3381 = Rc::clone(&t);
                      let v3382 = tc18_owned(v3381);
                      let v3386 = Rc::clone(&t);
                      let v3387 = tc19_owned(v3386);
                      let v3391 = Rc::clone(&t);
                      let v3392 = tc20_owned(v3391);
                      let v3396 = Rc::clone(&t);
                      let v3397 = tc21_owned(v3396);
                      let v3401 = Rc::clone(&t);
                      let v3402 = tc22_owned(v3401);
                      let v3406 = Rc::clone(&t);
                      let v3407 = tc23_owned(v3406);
                      let v3411 = Rc::clone(&t);
                      let v3412 = tc24_owned(v3411);
                      let v3416 = tc25_owned(t);
                      Rc::new(tab { tc0: v3297, tc1: v3302, tc2: v3307, tc3: v3312, tc4: v3317, tc5: v3322, tc6: v3327, tc7: v3332, tc8: v3337, tc9: v3342, tc10: v3347, tc11: v3352, tc12: v3357, tc13: v3362, tc14: v3367, tc15: v3372, tc16: v3377, tc17: a, tc18: v3382, tc19: v3387, tc20: v3392, tc21: v3397, tc22: v3402, tc23: v3407, tc24: v3412, tc25: v3416 })
                    },
                    false => {
                      let v3477 = Rc::clone(&t);
                      let v3478 = tc0_owned(v3477);
                      let v3482 = Rc::clone(&t);
                      let v3483 = tc1_owned(v3482);
                      let v3487 = Rc::clone(&t);
                      let v3488 = tc2_owned(v3487);
                      let v3492 = Rc::clone(&t);
                      let v3493 = tc3_owned(v3492);
                      let v3497 = Rc::clone(&t);
                      let v3498 = tc4_owned(v3497);
                      let v3502 = Rc::clone(&t);
                      let v3503 = tc5_owned(v3502);
                      let v3507 = Rc::clone(&t);
                      let v3508 = tc6_owned(v3507);
                      let v3512 = Rc::clone(&t);
                      let v3513 = tc7_owned(v3512);
                      let v3517 = Rc::clone(&t);
                      let v3518 = tc8_owned(v3517);
                      let v3522 = Rc::clone(&t);
                      let v3523 = tc9_owned(v3522);
                      let v3527 = Rc::clone(&t);
                      let v3528 = tc10_owned(v3527);
                      let v3532 = Rc::clone(&t);
                      let v3533 = tc11_owned(v3532);
                      let v3537 = Rc::clone(&t);
                      let v3538 = tc12_owned(v3537);
                      let v3542 = Rc::clone(&t);
                      let v3543 = tc13_owned(v3542);
                      let v3547 = Rc::clone(&t);
                      let v3548 = tc14_owned(v3547);
                      let v3552 = Rc::clone(&t);
                      let v3553 = tc15_owned(v3552);
                      let v3557 = Rc::clone(&t);
                      let v3558 = tc16_owned(v3557);
                      let v3562 = Rc::clone(&t);
                      let v3563 = tc17_owned(v3562);
                      let v3567 = Rc::clone(&t);
                      let v3568 = tc19_owned(v3567);
                      let v3572 = Rc::clone(&t);
                      let v3573 = tc20_owned(v3572);
                      let v3577 = Rc::clone(&t);
                      let v3578 = tc21_owned(v3577);
                      let v3582 = Rc::clone(&t);
                      let v3583 = tc22_owned(v3582);
                      let v3587 = Rc::clone(&t);
                      let v3588 = tc23_owned(v3587);
                      let v3592 = Rc::clone(&t);
                      let v3593 = tc24_owned(v3592);
                      let v3597 = tc25_owned(t);
                      Rc::new(tab { tc0: v3478, tc1: v3483, tc2: v3488, tc3: v3493, tc4: v3498, tc5: v3503, tc6: v3508, tc7: v3513, tc8: v3518, tc9: v3523, tc10: v3528, tc11: v3533, tc12: v3538, tc13: v3543, tc14: v3548, tc15: v3553, tc16: v3558, tc17: v3563, tc18: a, tc19: v3568, tc20: v3573, tc21: v3578, tc22: v3583, tc23: v3588, tc24: v3593, tc25: v3597 })
                    },
                  }
                },
              }
            },
          }
        },
        false => {
          match ltb(c, 22u64) {
            true => {
              match ltb(c, 20u64) {
                true => {
                  let v3685 = Rc::clone(&t);
                  let v3686 = tc0_owned(v3685);
                  let v3690 = Rc::clone(&t);
                  let v3691 = tc1_owned(v3690);
                  let v3695 = Rc::clone(&t);
                  let v3696 = tc2_owned(v3695);
                  let v3700 = Rc::clone(&t);
                  let v3701 = tc3_owned(v3700);
                  let v3705 = Rc::clone(&t);
                  let v3706 = tc4_owned(v3705);
                  let v3710 = Rc::clone(&t);
                  let v3711 = tc5_owned(v3710);
                  let v3715 = Rc::clone(&t);
                  let v3716 = tc6_owned(v3715);
                  let v3720 = Rc::clone(&t);
                  let v3721 = tc7_owned(v3720);
                  let v3725 = Rc::clone(&t);
                  let v3726 = tc8_owned(v3725);
                  let v3730 = Rc::clone(&t);
                  let v3731 = tc9_owned(v3730);
                  let v3735 = Rc::clone(&t);
                  let v3736 = tc10_owned(v3735);
                  let v3740 = Rc::clone(&t);
                  let v3741 = tc11_owned(v3740);
                  let v3745 = Rc::clone(&t);
                  let v3746 = tc12_owned(v3745);
                  let v3750 = Rc::clone(&t);
                  let v3751 = tc13_owned(v3750);
                  let v3755 = Rc::clone(&t);
                  let v3756 = tc14_owned(v3755);
                  let v3760 = Rc::clone(&t);
                  let v3761 = tc15_owned(v3760);
                  let v3765 = Rc::clone(&t);
                  let v3766 = tc16_owned(v3765);
                  let v3770 = Rc::clone(&t);
                  let v3771 = tc17_owned(v3770);
                  let v3775 = Rc::clone(&t);
                  let v3776 = tc18_owned(v3775);
                  let v3780 = Rc::clone(&t);
                  let v3781 = tc20_owned(v3780);
                  let v3785 = Rc::clone(&t);
                  let v3786 = tc21_owned(v3785);
                  let v3790 = Rc::clone(&t);
                  let v3791 = tc22_owned(v3790);
                  let v3795 = Rc::clone(&t);
                  let v3796 = tc23_owned(v3795);
                  let v3800 = Rc::clone(&t);
                  let v3801 = tc24_owned(v3800);
                  let v3805 = tc25_owned(t);
                  Rc::new(tab { tc0: v3686, tc1: v3691, tc2: v3696, tc3: v3701, tc4: v3706, tc5: v3711, tc6: v3716, tc7: v3721, tc8: v3726, tc9: v3731, tc10: v3736, tc11: v3741, tc12: v3746, tc13: v3751, tc14: v3756, tc15: v3761, tc16: v3766, tc17: v3771, tc18: v3776, tc19: a, tc20: v3781, tc21: v3786, tc22: v3791, tc23: v3796, tc24: v3801, tc25: v3805 })
                },
                false => {
                  match ltb(c, 21u64) {
                    true => {
                      let v3875 = Rc::clone(&t);
                      let v3876 = tc0_owned(v3875);
                      let v3880 = Rc::clone(&t);
                      let v3881 = tc1_owned(v3880);
                      let v3885 = Rc::clone(&t);
                      let v3886 = tc2_owned(v3885);
                      let v3890 = Rc::clone(&t);
                      let v3891 = tc3_owned(v3890);
                      let v3895 = Rc::clone(&t);
                      let v3896 = tc4_owned(v3895);
                      let v3900 = Rc::clone(&t);
                      let v3901 = tc5_owned(v3900);
                      let v3905 = Rc::clone(&t);
                      let v3906 = tc6_owned(v3905);
                      let v3910 = Rc::clone(&t);
                      let v3911 = tc7_owned(v3910);
                      let v3915 = Rc::clone(&t);
                      let v3916 = tc8_owned(v3915);
                      let v3920 = Rc::clone(&t);
                      let v3921 = tc9_owned(v3920);
                      let v3925 = Rc::clone(&t);
                      let v3926 = tc10_owned(v3925);
                      let v3930 = Rc::clone(&t);
                      let v3931 = tc11_owned(v3930);
                      let v3935 = Rc::clone(&t);
                      let v3936 = tc12_owned(v3935);
                      let v3940 = Rc::clone(&t);
                      let v3941 = tc13_owned(v3940);
                      let v3945 = Rc::clone(&t);
                      let v3946 = tc14_owned(v3945);
                      let v3950 = Rc::clone(&t);
                      let v3951 = tc15_owned(v3950);
                      let v3955 = Rc::clone(&t);
                      let v3956 = tc16_owned(v3955);
                      let v3960 = Rc::clone(&t);
                      let v3961 = tc17_owned(v3960);
                      let v3965 = Rc::clone(&t);
                      let v3966 = tc18_owned(v3965);
                      let v3970 = Rc::clone(&t);
                      let v3971 = tc19_owned(v3970);
                      let v3975 = Rc::clone(&t);
                      let v3976 = tc21_owned(v3975);
                      let v3980 = Rc::clone(&t);
                      let v3981 = tc22_owned(v3980);
                      let v3985 = Rc::clone(&t);
                      let v3986 = tc23_owned(v3985);
                      let v3990 = Rc::clone(&t);
                      let v3991 = tc24_owned(v3990);
                      let v3995 = tc25_owned(t);
                      Rc::new(tab { tc0: v3876, tc1: v3881, tc2: v3886, tc3: v3891, tc4: v3896, tc5: v3901, tc6: v3906, tc7: v3911, tc8: v3916, tc9: v3921, tc10: v3926, tc11: v3931, tc12: v3936, tc13: v3941, tc14: v3946, tc15: v3951, tc16: v3956, tc17: v3961, tc18: v3966, tc19: v3971, tc20: a, tc21: v3976, tc22: v3981, tc23: v3986, tc24: v3991, tc25: v3995 })
                    },
                    false => {
                      let v4056 = Rc::clone(&t);
                      let v4057 = tc0_owned(v4056);
                      let v4061 = Rc::clone(&t);
                      let v4062 = tc1_owned(v4061);
                      let v4066 = Rc::clone(&t);
                      let v4067 = tc2_owned(v4066);
                      let v4071 = Rc::clone(&t);
                      let v4072 = tc3_owned(v4071);
                      let v4076 = Rc::clone(&t);
                      let v4077 = tc4_owned(v4076);
                      let v4081 = Rc::clone(&t);
                      let v4082 = tc5_owned(v4081);
                      let v4086 = Rc::clone(&t);
                      let v4087 = tc6_owned(v4086);
                      let v4091 = Rc::clone(&t);
                      let v4092 = tc7_owned(v4091);
                      let v4096 = Rc::clone(&t);
                      let v4097 = tc8_owned(v4096);
                      let v4101 = Rc::clone(&t);
                      let v4102 = tc9_owned(v4101);
                      let v4106 = Rc::clone(&t);
                      let v4107 = tc10_owned(v4106);
                      let v4111 = Rc::clone(&t);
                      let v4112 = tc11_owned(v4111);
                      let v4116 = Rc::clone(&t);
                      let v4117 = tc12_owned(v4116);
                      let v4121 = Rc::clone(&t);
                      let v4122 = tc13_owned(v4121);
                      let v4126 = Rc::clone(&t);
                      let v4127 = tc14_owned(v4126);
                      let v4131 = Rc::clone(&t);
                      let v4132 = tc15_owned(v4131);
                      let v4136 = Rc::clone(&t);
                      let v4137 = tc16_owned(v4136);
                      let v4141 = Rc::clone(&t);
                      let v4142 = tc17_owned(v4141);
                      let v4146 = Rc::clone(&t);
                      let v4147 = tc18_owned(v4146);
                      let v4151 = Rc::clone(&t);
                      let v4152 = tc19_owned(v4151);
                      let v4156 = Rc::clone(&t);
                      let v4157 = tc20_owned(v4156);
                      let v4161 = Rc::clone(&t);
                      let v4162 = tc22_owned(v4161);
                      let v4166 = Rc::clone(&t);
                      let v4167 = tc23_owned(v4166);
                      let v4171 = Rc::clone(&t);
                      let v4172 = tc24_owned(v4171);
                      let v4176 = tc25_owned(t);
                      Rc::new(tab { tc0: v4057, tc1: v4062, tc2: v4067, tc3: v4072, tc4: v4077, tc5: v4082, tc6: v4087, tc7: v4092, tc8: v4097, tc9: v4102, tc10: v4107, tc11: v4112, tc12: v4117, tc13: v4122, tc14: v4127, tc15: v4132, tc16: v4137, tc17: v4142, tc18: v4147, tc19: v4152, tc20: v4157, tc21: a, tc22: v4162, tc23: v4167, tc24: v4172, tc25: v4176 })
                    },
                  }
                },
              }
            },
            false => {
              match ltb(c, 24u64) {
                true => {
                  match ltb(c, 23u64) {
                    true => {
                      let v4261 = Rc::clone(&t);
                      let v4262 = tc0_owned(v4261);
                      let v4266 = Rc::clone(&t);
                      let v4267 = tc1_owned(v4266);
                      let v4271 = Rc::clone(&t);
                      let v4272 = tc2_owned(v4271);
                      let v4276 = Rc::clone(&t);
                      let v4277 = tc3_owned(v4276);
                      let v4281 = Rc::clone(&t);
                      let v4282 = tc4_owned(v4281);
                      let v4286 = Rc::clone(&t);
                      let v4287 = tc5_owned(v4286);
                      let v4291 = Rc::clone(&t);
                      let v4292 = tc6_owned(v4291);
                      let v4296 = Rc::clone(&t);
                      let v4297 = tc7_owned(v4296);
                      let v4301 = Rc::clone(&t);
                      let v4302 = tc8_owned(v4301);
                      let v4306 = Rc::clone(&t);
                      let v4307 = tc9_owned(v4306);
                      let v4311 = Rc::clone(&t);
                      let v4312 = tc10_owned(v4311);
                      let v4316 = Rc::clone(&t);
                      let v4317 = tc11_owned(v4316);
                      let v4321 = Rc::clone(&t);
                      let v4322 = tc12_owned(v4321);
                      let v4326 = Rc::clone(&t);
                      let v4327 = tc13_owned(v4326);
                      let v4331 = Rc::clone(&t);
                      let v4332 = tc14_owned(v4331);
                      let v4336 = Rc::clone(&t);
                      let v4337 = tc15_owned(v4336);
                      let v4341 = Rc::clone(&t);
                      let v4342 = tc16_owned(v4341);
                      let v4346 = Rc::clone(&t);
                      let v4347 = tc17_owned(v4346);
                      let v4351 = Rc::clone(&t);
                      let v4352 = tc18_owned(v4351);
                      let v4356 = Rc::clone(&t);
                      let v4357 = tc19_owned(v4356);
                      let v4361 = Rc::clone(&t);
                      let v4362 = tc20_owned(v4361);
                      let v4366 = Rc::clone(&t);
                      let v4367 = tc21_owned(v4366);
                      let v4371 = Rc::clone(&t);
                      let v4372 = tc23_owned(v4371);
                      let v4376 = Rc::clone(&t);
                      let v4377 = tc24_owned(v4376);
                      let v4381 = tc25_owned(t);
                      Rc::new(tab { tc0: v4262, tc1: v4267, tc2: v4272, tc3: v4277, tc4: v4282, tc5: v4287, tc6: v4292, tc7: v4297, tc8: v4302, tc9: v4307, tc10: v4312, tc11: v4317, tc12: v4322, tc13: v4327, tc14: v4332, tc15: v4337, tc16: v4342, tc17: v4347, tc18: v4352, tc19: v4357, tc20: v4362, tc21: v4367, tc22: a, tc23: v4372, tc24: v4377, tc25: v4381 })
                    },
                    false => {
                      let v4442 = Rc::clone(&t);
                      let v4443 = tc0_owned(v4442);
                      let v4447 = Rc::clone(&t);
                      let v4448 = tc1_owned(v4447);
                      let v4452 = Rc::clone(&t);
                      let v4453 = tc2_owned(v4452);
                      let v4457 = Rc::clone(&t);
                      let v4458 = tc3_owned(v4457);
                      let v4462 = Rc::clone(&t);
                      let v4463 = tc4_owned(v4462);
                      let v4467 = Rc::clone(&t);
                      let v4468 = tc5_owned(v4467);
                      let v4472 = Rc::clone(&t);
                      let v4473 = tc6_owned(v4472);
                      let v4477 = Rc::clone(&t);
                      let v4478 = tc7_owned(v4477);
                      let v4482 = Rc::clone(&t);
                      let v4483 = tc8_owned(v4482);
                      let v4487 = Rc::clone(&t);
                      let v4488 = tc9_owned(v4487);
                      let v4492 = Rc::clone(&t);
                      let v4493 = tc10_owned(v4492);
                      let v4497 = Rc::clone(&t);
                      let v4498 = tc11_owned(v4497);
                      let v4502 = Rc::clone(&t);
                      let v4503 = tc12_owned(v4502);
                      let v4507 = Rc::clone(&t);
                      let v4508 = tc13_owned(v4507);
                      let v4512 = Rc::clone(&t);
                      let v4513 = tc14_owned(v4512);
                      let v4517 = Rc::clone(&t);
                      let v4518 = tc15_owned(v4517);
                      let v4522 = Rc::clone(&t);
                      let v4523 = tc16_owned(v4522);
                      let v4527 = Rc::clone(&t);
                      let v4528 = tc17_owned(v4527);
                      let v4532 = Rc::clone(&t);
                      let v4533 = tc18_owned(v4532);
                      let v4537 = Rc::clone(&t);
                      let v4538 = tc19_owned(v4537);
                      let v4542 = Rc::clone(&t);
                      let v4543 = tc20_owned(v4542);
                      let v4547 = Rc::clone(&t);
                      let v4548 = tc21_owned(v4547);
                      let v4552 = Rc::clone(&t);
                      let v4553 = tc22_owned(v4552);
                      let v4557 = Rc::clone(&t);
                      let v4558 = tc24_owned(v4557);
                      let v4562 = tc25_owned(t);
                      Rc::new(tab { tc0: v4443, tc1: v4448, tc2: v4453, tc3: v4458, tc4: v4463, tc5: v4468, tc6: v4473, tc7: v4478, tc8: v4483, tc9: v4488, tc10: v4493, tc11: v4498, tc12: v4503, tc13: v4508, tc14: v4513, tc15: v4518, tc16: v4523, tc17: v4528, tc18: v4533, tc19: v4538, tc20: v4543, tc21: v4548, tc22: v4553, tc23: a, tc24: v4558, tc25: v4562 })
                    },
                  }
                },
                false => {
                  match ltb(c, 25u64) {
                    true => {
                      let v4635 = Rc::clone(&t);
                      let v4636 = tc0_owned(v4635);
                      let v4640 = Rc::clone(&t);
                      let v4641 = tc1_owned(v4640);
                      let v4645 = Rc::clone(&t);
                      let v4646 = tc2_owned(v4645);
                      let v4650 = Rc::clone(&t);
                      let v4651 = tc3_owned(v4650);
                      let v4655 = Rc::clone(&t);
                      let v4656 = tc4_owned(v4655);
                      let v4660 = Rc::clone(&t);
                      let v4661 = tc5_owned(v4660);
                      let v4665 = Rc::clone(&t);
                      let v4666 = tc6_owned(v4665);
                      let v4670 = Rc::clone(&t);
                      let v4671 = tc7_owned(v4670);
                      let v4675 = Rc::clone(&t);
                      let v4676 = tc8_owned(v4675);
                      let v4680 = Rc::clone(&t);
                      let v4681 = tc9_owned(v4680);
                      let v4685 = Rc::clone(&t);
                      let v4686 = tc10_owned(v4685);
                      let v4690 = Rc::clone(&t);
                      let v4691 = tc11_owned(v4690);
                      let v4695 = Rc::clone(&t);
                      let v4696 = tc12_owned(v4695);
                      let v4700 = Rc::clone(&t);
                      let v4701 = tc13_owned(v4700);
                      let v4705 = Rc::clone(&t);
                      let v4706 = tc14_owned(v4705);
                      let v4710 = Rc::clone(&t);
                      let v4711 = tc15_owned(v4710);
                      let v4715 = Rc::clone(&t);
                      let v4716 = tc16_owned(v4715);
                      let v4720 = Rc::clone(&t);
                      let v4721 = tc17_owned(v4720);
                      let v4725 = Rc::clone(&t);
                      let v4726 = tc18_owned(v4725);
                      let v4730 = Rc::clone(&t);
                      let v4731 = tc19_owned(v4730);
                      let v4735 = Rc::clone(&t);
                      let v4736 = tc20_owned(v4735);
                      let v4740 = Rc::clone(&t);
                      let v4741 = tc21_owned(v4740);
                      let v4745 = Rc::clone(&t);
                      let v4746 = tc22_owned(v4745);
                      let v4750 = Rc::clone(&t);
                      let v4751 = tc23_owned(v4750);
                      let v4755 = tc25_owned(t);
                      Rc::new(tab { tc0: v4636, tc1: v4641, tc2: v4646, tc3: v4651, tc4: v4656, tc5: v4661, tc6: v4666, tc7: v4671, tc8: v4676, tc9: v4681, tc10: v4686, tc11: v4691, tc12: v4696, tc13: v4701, tc14: v4706, tc15: v4711, tc16: v4716, tc17: v4721, tc18: v4726, tc19: v4731, tc20: v4736, tc21: v4741, tc22: v4746, tc23: v4751, tc24: a, tc25: v4755 })
                    },
                    false => {
                      let v4816 = Rc::clone(&t);
                      let v4817 = tc0_owned(v4816);
                      let v4821 = Rc::clone(&t);
                      let v4822 = tc1_owned(v4821);
                      let v4826 = Rc::clone(&t);
                      let v4827 = tc2_owned(v4826);
                      let v4831 = Rc::clone(&t);
                      let v4832 = tc3_owned(v4831);
                      let v4836 = Rc::clone(&t);
                      let v4837 = tc4_owned(v4836);
                      let v4841 = Rc::clone(&t);
                      let v4842 = tc5_owned(v4841);
                      let v4846 = Rc::clone(&t);
                      let v4847 = tc6_owned(v4846);
                      let v4851 = Rc::clone(&t);
                      let v4852 = tc7_owned(v4851);
                      let v4856 = Rc::clone(&t);
                      let v4857 = tc8_owned(v4856);
                      let v4861 = Rc::clone(&t);
                      let v4862 = tc9_owned(v4861);
                      let v4866 = Rc::clone(&t);
                      let v4867 = tc10_owned(v4866);
                      let v4871 = Rc::clone(&t);
                      let v4872 = tc11_owned(v4871);
                      let v4876 = Rc::clone(&t);
                      let v4877 = tc12_owned(v4876);
                      let v4881 = Rc::clone(&t);
                      let v4882 = tc13_owned(v4881);
                      let v4886 = Rc::clone(&t);
                      let v4887 = tc14_owned(v4886);
                      let v4891 = Rc::clone(&t);
                      let v4892 = tc15_owned(v4891);
                      let v4896 = Rc::clone(&t);
                      let v4897 = tc16_owned(v4896);
                      let v4901 = Rc::clone(&t);
                      let v4902 = tc17_owned(v4901);
                      let v4906 = Rc::clone(&t);
                      let v4907 = tc18_owned(v4906);
                      let v4911 = Rc::clone(&t);
                      let v4912 = tc19_owned(v4911);
                      let v4916 = Rc::clone(&t);
                      let v4917 = tc20_owned(v4916);
                      let v4921 = Rc::clone(&t);
                      let v4922 = tc21_owned(v4921);
                      let v4926 = Rc::clone(&t);
                      let v4927 = tc22_owned(v4926);
                      let v4931 = Rc::clone(&t);
                      let v4932 = tc23_owned(v4931);
                      let v4936 = tc24_owned(t);
                      Rc::new(tab { tc0: v4817, tc1: v4822, tc2: v4827, tc3: v4832, tc4: v4837, tc5: v4842, tc6: v4847, tc7: v4852, tc8: v4857, tc9: v4862, tc10: v4867, tc11: v4872, tc12: v4877, tc13: v4882, tc14: v4887, tc15: v4892, tc16: v4897, tc17: v4902, tc18: v4907, tc19: v4912, tc20: v4917, tc21: v4922, tc22: v4927, tc23: v4932, tc24: v4936, tc25: a })
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

// Rocq: Baza.baza_implem.tset
// Variant: uncurried
pub fn tset(t: Rc<tab>, c: u64, n: u64, v: u64) -> Rc<tab> {
  let v8 = Rc::clone(&t);
  let v12 = sel_owned(v8, c);
  let v18 = rocq_array::set::<u64>(v12, n, v);
  upd(t, c, v18)
}

// Rocq: Baza.baza_implem.ins_loop
// Variant: uncurried
pub fn ins_loop_1(w: Rc<rocq_string::RocqString>, L: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, sz: u64, i: u64, n: u64, s: u64) -> Rc<ires> {
  ins_loop(w, L, T, cnt, sz, i, n, s, ())
}

// Rocq: Baza.baza_implem.ins_loop (local: ins_loop)
// Variant: uncurried, lifted
pub fn ins_loop(w: Rc<rocq_string::RocqString>, L: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, sz: u64, i: u64, n: u64, s: u64, _H: ()) -> Rc<ires> {
  let v16 = ltb(i, L);
  match bdec(v16) {
    sumbool::left => {
      let v24 = Rc::clone(&w);
      let c = sub(get(v24, i), 97u64);
      let m = tget(&T, c, n);
      match eqb(m, 0u64) {
        true => {
          let v61 = tset(T, c, n, sz);
          let v70 = rocq_array::set::<u64>(cnt, sz, 1u64);
          ins_loop(w, L, v61, v70, add(sz, 1u64), add(i, 1u64), sz, add(s, 1u64), ())
        },
        false => {
          let v120 = &cnt;
          let v123 = rocq_array::get::<u64>(&v120, m);
          let k = add(v123, 1u64);
          let v137 = rocq_array::set::<u64>(cnt, m, k);
          ins_loop(w, L, T, v137, sz, add(i, 1u64), m, add(s, k), ())
        },
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
  let v3 = Rc::clone((&(&**&i).r_T));
  std::mem::drop(i);
  v3
}

// Rocq: Baza.baza_implem.r_cnt
pub fn r_cnt(i: Rc<ires>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&i).r_cnt));
  std::mem::drop(i);
  v3
}

// Rocq: Baza.baza_implem.r_n
// Variant: borrowed
pub fn r_n(i: &Rc<ires>) -> u64 {
  let v1 = i;
  Clone::clone((&(&**v1).r_n))
}

// Rocq: Baza.baza_implem.r_s
// Variant: borrowed
pub fn r_s(i: &Rc<ires>) -> u64 {
  let v1 = i;
  Clone::clone((&(&**v1).r_s))
}

// Rocq: Baza.baza_implem.r_sz
pub fn r_sz(i: Rc<ires>) -> u64 {
  let v3 = Clone::clone((&(&**&i).r_sz));
  std::mem::drop(i);
  v3
}

// Rocq: Baza.baza_implem.build
// Variant: uncurried
pub fn build_1(db: Rc<Array<Rc<rocq_string::RocqString>>>, N: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, sz: u64, j: u64) -> Rc<bres> {
  build(db, N, T, cnt, endv, sz, j, ())
}

// Rocq: Baza.baza_implem.build (local: build)
// Variant: uncurried, lifted
pub fn build(db: Rc<Array<Rc<rocq_string::RocqString>>>, N: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, sz: u64, j: u64, _H: ()) -> Rc<bres> {
  let v15 = ltb(j, N);
  match bdec(v15) {
    sumbool::left => {
      let v19 = &db;
      let w = rocq_array::get::<Rc<rocq_string::RocqString>>(&v19, j);
      let v27 = Rc::clone(&w);
      let r = ins_loop_1(w, length(v27), T, cnt, sz, 0u64, 0u64, 0u64);
      let v55 = Rc::clone(&r);
      let v56 = r_T(v55);
      let v60 = Rc::clone(&r);
      let v61 = r_cnt(v60);
      let v65 = r_n(&r);
      let v74 = add(j, 1u64);
      let v78 = r_s(&r);
      let v90 = rocq_array::set::<u64>(endv, v65, add(v74, v78));
      build(db, N, v56, v61, v90, r_sz(r), add(j, 1u64), ())
    },
    sumbool::right => {
      std::mem::drop(db);
      Rc::new(bres { b_T: T, b_cnt: cnt, b_end: endv })
    },
  }
}

// Rocq: Baza.baza_implem.mk_tab
pub fn mk_tab(cap: u64) -> Rc<tab> {
  let v7 = rocq_array::make::<u64>(cap, 0u64);
  let v14 = rocq_array::make::<u64>(cap, 0u64);
  let v21 = rocq_array::make::<u64>(cap, 0u64);
  let v28 = rocq_array::make::<u64>(cap, 0u64);
  let v35 = rocq_array::make::<u64>(cap, 0u64);
  let v42 = rocq_array::make::<u64>(cap, 0u64);
  let v49 = rocq_array::make::<u64>(cap, 0u64);
  let v56 = rocq_array::make::<u64>(cap, 0u64);
  let v63 = rocq_array::make::<u64>(cap, 0u64);
  let v70 = rocq_array::make::<u64>(cap, 0u64);
  let v77 = rocq_array::make::<u64>(cap, 0u64);
  let v84 = rocq_array::make::<u64>(cap, 0u64);
  let v91 = rocq_array::make::<u64>(cap, 0u64);
  let v98 = rocq_array::make::<u64>(cap, 0u64);
  let v105 = rocq_array::make::<u64>(cap, 0u64);
  let v112 = rocq_array::make::<u64>(cap, 0u64);
  let v119 = rocq_array::make::<u64>(cap, 0u64);
  let v126 = rocq_array::make::<u64>(cap, 0u64);
  let v133 = rocq_array::make::<u64>(cap, 0u64);
  let v140 = rocq_array::make::<u64>(cap, 0u64);
  let v147 = rocq_array::make::<u64>(cap, 0u64);
  let v154 = rocq_array::make::<u64>(cap, 0u64);
  let v161 = rocq_array::make::<u64>(cap, 0u64);
  let v168 = rocq_array::make::<u64>(cap, 0u64);
  let v175 = rocq_array::make::<u64>(cap, 0u64);
  let v182 = rocq_array::make::<u64>(cap, 0u64);
  Rc::new(tab { tc0: v7, tc1: v14, tc2: v21, tc3: v28, tc4: v35, tc5: v42, tc6: v49, tc7: v56, tc8: v63, tc9: v70, tc10: v77, tc11: v84, tc12: v91, tc13: v98, tc14: v105, tc15: v112, tc16: v119, tc17: v126, tc18: v133, tc19: v140, tc20: v147, tc21: v154, tc22: v161, tc23: v168, tc24: v175, tc25: v182 })
}

// Rocq: Baza.baza_implem.qwalk
// Variant: uncurried
pub fn qwalk_1(q: Rc<rocq_string::RocqString>, L: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, N: u64, i: u64, n: u64, s: u64) -> u64 {
  qwalk(q, L, T, cnt, endv, N, i, n, s, ())
}

// Rocq: Baza.baza_implem.qwalk (local: qwalk)
// Variant: uncurried, lifted
pub fn qwalk(q: Rc<rocq_string::RocqString>, L: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, N: u64, i: u64, n: u64, s: u64, _H: ()) -> u64 {
  let v17 = ltb(i, L);
  match bdec(v17) {
    sumbool::left => {
      let v25 = Rc::clone(&q);
      let v35 = sub(get(v25, i), 97u64);
      let m = tget(&T, v35, n);
      match eqb(m, 0u64) {
        true => {
          std::mem::drop(q);
          std::mem::drop(cnt);
          std::mem::drop(endv);
          std::mem::drop(T);
          add(N, s)
        },
        false => {
          let v68 = add(i, 1u64);
          let v70 = &cnt;
          let v73 = rocq_array::get::<u64>(&v70, m);
          qwalk(q, L, T, cnt, endv, N, v68, m, add(s, v73), ())
        },
      }
    },
    sumbool::right => {
      let v108 = &endv;
      let e = rocq_array::get::<u64>(&v108, n);
      match eqb(e, 0u64) {
        true => {
          std::mem::drop(q);
          std::mem::drop(T);
          std::mem::drop(cnt);
          std::mem::drop(endv);
          add(N, s)
        },
        false => {
          std::mem::drop(q);
          std::mem::drop(T);
          std::mem::drop(cnt);
          std::mem::drop(endv);
          e
        },
      }
    },
  }
}

// Rocq: Baza.baza_implem.query
// Variant: uncurried
pub fn query(q: Rc<rocq_string::RocqString>, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, N: u64) -> u64 {
  let v9 = Rc::clone(&q);
  qwalk_1(q, length(v9), T, cnt, endv, N, 0u64, 0u64, 0u64)
}

// Rocq: Baza.baza_implem.answer
// Variant: uncurried
pub fn answer_1(qs: Rc<Array<Rc<rocq_string::RocqString>>>, Q: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, N: u64, out: Rc<Array<u64>>, k: u64) -> Rc<Array<u64>> {
  answer(qs, Q, T, cnt, endv, N, out, k, ())
}

// Rocq: Baza.baza_implem.answer (local: answer)
// Variant: uncurried, lifted
pub fn answer(qs: Rc<Array<Rc<rocq_string::RocqString>>>, Q: u64, T: Rc<tab>, cnt: Rc<Array<u64>>, endv: Rc<Array<u64>>, N: u64, out: Rc<Array<u64>>, k: u64, _H: ()) -> Rc<Array<u64>> {
  let v16 = ltb(k, Q);
  match bdec(v16) {
    sumbool::left => {
      let v21 = &qs;
      let v25 = rocq_array::get::<Rc<rocq_string::RocqString>>(&v21, k);
      let v29 = Rc::clone(&T);
      let v32 = Rc::clone(&cnt);
      let v35 = Rc::clone(&endv);
      let v45 = rocq_array::set::<u64>(out, k, query(v25, v29, v32, v35, N));
      answer(qs, Q, T, cnt, endv, N, v45, add(k, 1u64), ())
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
pub fn b_T(b: Rc<bres>) -> Rc<tab> {
  let v3 = Rc::clone((&(&**&b).b_T));
  std::mem::drop(b);
  v3
}

// Rocq: Baza.baza_implem.b_cnt
pub fn b_cnt(b: Rc<bres>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_cnt));
  std::mem::drop(b);
  v3
}

// Rocq: Baza.baza_implem.b_end
pub fn b_end(b: Rc<bres>) -> Rc<Array<u64>> {
  let v3 = Rc::clone((&(&**&b).b_end));
  std::mem::drop(b);
  v3
}

// Rocq: Baza.baza_implem.baza_impl
// Variant: uncurried
pub fn baza_impl(db: Rc<Array<Rc<rocq_string::RocqString>>>, qs: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>> {
  let v2 = &db;
  let N = rocq_array::length::<Rc<rocq_string::RocqString>>(&v2);
  let v14 = Rc::clone(&db);
  let cap = add(1u64, total_1(v14, N, 0u64, 0u64));
  let v31 = mk_tab(cap);
  let v38 = rocq_array::make::<u64>(cap, 0u64);
  let v45 = rocq_array::make::<u64>(cap, 0u64);
  let b = build_1(db, N, v31, v38, v45, 1u64, 0u64);
  let v65 = &qs;
  let Q = rocq_array::length::<Rc<rocq_string::RocqString>>(&v65);
  let v71 = Rc::clone(&b);
  let v72 = b_T(v71);
  let v76 = Rc::clone(&b);
  let v77 = b_cnt(v76);
  let v81 = b_end(b);
  let v88 = rocq_array::make::<u64>(Q, 0u64);
  answer_1(qs, Q, v72, v77, v81, N, v88, 0u64)
}

// Rocq: Baza.baza_implem.baza_impl
pub fn baza_impl_curried(db: Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> {
  let v3 = {
    move |qs: Rc<Array<Rc<rocq_string::RocqString>>>| -> Rc<Array<u64>> {
      let v9 = Rc::clone(&db);
      baza_impl(v9, qs)
    }
  };
  let v15: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> = Rc::new(v3);
  v15
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

pub fn run() -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> {
  let v0: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> = __rocq_global_2350.with(Clone::clone);
  v0
}
std::thread_local! { static __rocq_global_2350: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>, Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>> = baza(); }
std::thread_local! { static __rocq_global_2353: Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<dyn Fn(Rc<Array<Rc<rocq_string::RocqString>>>) -> Rc<Array<u64>>>> = baza_curried(); }