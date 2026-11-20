#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use crate::rocq_reuse as __rocq_reuse;
use rocq_int63::{int63, Int63};
#[allow(unused_imports)] use rocq_array::{self as a, Array};

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<Int63>; };

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = Int63;

pub type char63 = Int63;

// Rocq: Cardhand.cardhand_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Cardhand.cardhand_implem.sidx_m
pub fn sidx_m(c: Int63) -> Int63 {
  if c == int63!(115) {
    int63!(0)
  } else {
    if c == int63!(104) {
      int63!(1)
    } else {
      if c == int63!(100) {
        int63!(2)
      } else {
        int63!(3)
      }
    }
  }
}

// Rocq: Corelib.Strings.PrimString.get
// Variant: uncurried
pub fn get(v0: rocq_string::RocqString, v1: Int63) -> Int63 {
  let tmp = v0.get(v1);
  std::mem::drop(v0);
  tmp
}

// Rocq: Cardhand.cardhand_implem.rank_m
pub fn rank_m(c: Int63) -> Int63 {
  if c <= int63!(57) {
    c - int63!(50)
  } else {
    if c == int63!(84) {
      int63!(8)
    } else {
      if c == int63!(74) {
        int63!(9)
      } else {
        if c == int63!(81) {
          int63!(10)
        } else {
          if c == int63!(75) {
            int63!(11)
          } else {
            int63!(12)
          }
        }
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.prep
// Variant: uncurried
pub fn prep_1(x: Array<rocq_string::RocqString>, n: Int63, i: Int63, SU: Array<Int63>, RK: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  prep(x, n, i, SU, RK, ())
}

// Rocq: Cardhand.cardhand_implem.prep (local: prep)
// Variant: uncurried, lifted
pub fn prep(x: Array<rocq_string::RocqString>, n: Int63, i: Int63, SU: Array<Int63>, RK: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let x_ref = &x;
      let w = x_ref.get_cloned(i);
      let tmp_1 = i + int63!(1);
      let w_clone = Clone::clone(&w);
      prep(x, n, tmp_1, SU.set(i, sidx_m(get(w_clone, int63!(1)))), RK.set(i, rank_m(get(w, int63!(0)))), ())
    },
    sumbool::right => {
      std::mem::drop(x);
      (SU, RK)
    },
  }
}

// Rocq: Cardhand.cardhand_implem.pw4
pub fn pw4(s: Int63) -> Int63 {
  if s == int63!(0) {
    int63!(1)
  } else {
    if s == int63!(1) {
      int63!(4)
    } else {
      if s == int63!(2) {
        int63!(16)
      } else {
        int63!(64)
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.sg_m
// Variant: uncurried
pub fn sg_m(t: Int63, s: Int63) -> Int63 {
  t / pw4(s) % int63!(4)
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

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Cardhand.cardhand_implem.inj_m
pub fn inj_m(t: Int63) -> bool {
  let a_1 = sg_m(t, int63!(0));
  let b_1 = sg_m(t, int63!(1));
  let c = sg_m(t, int63!(2));
  let d = sg_m(t, int63!(3));
  let tmp = andb(negb(a_1 == b_1), negb(a_1 == c));
  let tmp_1 = andb(tmp, negb(a_1 == d));
  let tmp_2 = andb(tmp_1, negb(b_1 == c));
  let tmp_3 = andb(tmp_2, negb(b_1 == d));
  andb(tmp_3, negb(c == d))
}

// Rocq: Cardhand.cardhand_implem.imax
// Variant: uncurried
pub fn imax(a_1: Int63, b_1: Int63) -> Int63 {
  if a_1 < b_1 {
    b_1
  } else {
    a_1
  }
}

// Rocq: Cardhand.cardhand_implem.pw2
pub fn pw2(s: Int63) -> Int63 {
  if s == int63!(0) {
    int63!(256)
  } else {
    if s == int63!(1) {
      int63!(512)
    } else {
      if s == int63!(2) {
        int63!(1024)
      } else {
        int63!(2048)
      }
    }
  }
}

// Rocq: Cardhand.cardhand_implem.dr_m
// Variant: uncurried
pub fn dr_m(t: Int63, s: Int63) -> Int63 {
  t / pw2(s) % int63!(2)
}

// Rocq: Cardhand.cardhand_implem.key_m
// Variant: uncurried
pub fn key_m(t: Int63, s: Int63, r: Int63) -> Int63 {
  let tmp = sg_m(t, s) * int63!(13);
  let tmp_1 = dr_m(t, s);
  let tmp_2 = int63!(1);
  let tmp_3 = if tmp_1 == tmp_2 {
    r
  } else {
    int63!(12) - r
  };
  tmp + tmp_3
}

// Rocq: Cardhand.cardhand_implem.keys
// Variant: uncurried
pub fn keys_1(t: Int63, SU: Array<Int63>, RK: Array<Int63>, n: Int63, i: Int63, K: Array<Int63>, P: Array<Int63>) -> (Array<Int63>, Array<Int63>) {
  keys(t, SU, RK, n, i, K, P, ())
}

// Rocq: Cardhand.cardhand_implem.keys (local: keys)
// Variant: uncurried, lifted
pub fn keys(t: Int63, SU: Array<Int63>, RK: Array<Int63>, n: Int63, i: Int63, K: Array<Int63>, P: Array<Int63>, _H: ()) -> (Array<Int63>, Array<Int63>) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = SU.get_cloned(i);
      let tmp_2 = RK.get_cloned(i);
      let k = key_m(t, tmp_1, tmp_2);
      keys(t, SU, RK, n, i + int63!(1), K.set(i, k), P.set(k, int63!(1)), ())
    },
    sumbool::right => {
      std::mem::drop(SU);
      std::mem::drop(RK);
      (K, P)
    },
  }
}

// Rocq: Cardhand.cardhand_implem.compact
// Variant: uncurried
pub fn compact_1(P: Array<Int63>, k: Int63, B: Array<Int63>, m: Int63) -> (Array<Int63>, Int63) {
  compact(P, k, B, m, ())
}

// Rocq: Cardhand.cardhand_implem.compact (local: compact)
// Variant: uncurried, lifted
pub fn compact(P: Array<Int63>, k: Int63, B: Array<Int63>, m: Int63, _H: ()) -> (Array<Int63>, Int63) {
  let tmp = k < int63!(52);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = P.get_cloned(k);
      if tmp_1 == int63!(1) {
        compact(P, k + int63!(1), B.set(m, k), m + int63!(1), ())
      } else {
        compact(P, k + int63!(1), B, m, ())
      }
    },
    sumbool::right => {
      std::mem::drop(P);
      (B, m)
    },
  }
}

// Rocq: Cardhand.cardhand_implem.dp
// Variant: uncurried
pub fn dp_1(K: Array<Int63>, B: Array<Int63>, m: Int63, w: Int63, q: Int63, T: Array<Int63>) -> Array<Int63> {
  dp(K, B, m, w, q, T, ())
}

// Rocq: Cardhand.cardhand_implem.dp (local: dp)
// Variant: uncurried, lifted
pub fn dp(K: Array<Int63>, B: Array<Int63>, m: Int63, w: Int63, q: Int63, T: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = int63!(0) < q;
  match bdec(tmp) {
    sumbool::left => {
      let q_ = q - int63!(1);
      let i = q_ / m;
      let j = q_ % m;
      let tmp_1 = K.get_cloned(i);
      let tmp_2 = B.get_cloned(j);
      let c = if tmp_1 == tmp_2 {
        let tmp_3 = T.get_cloned((i + int63!(1)) * w + (j + int63!(1)));
        tmp_3 + int63!(1)
      } else {
        let tmp_4 = T.get_cloned((i + int63!(1)) * w + j);
        let tmp_5 = T.get_cloned(i * w + (j + int63!(1)));
        imax(tmp_4, tmp_5)
      };
      let tmp_6 = i * w;
      dp(K, B, m, w, q_, T.set(tmp_6 + j, c), ())
    },
    sumbool::right => {
      std::mem::drop(K);
      std::mem::drop(B);
      T
    },
  }
}

// Rocq: Cardhand.cardhand_implem.lcs_for
// Variant: uncurried
pub fn lcs_for(t: Int63, SU: Array<Int63>, RK: Array<Int63>, n: Int63) -> Int63 {
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = keys_1(t, SU, RK, n, int63!(0), tmp, Array::<Int63>::make(int63!(52), int63!(0)));
  match tmp_1 {
    (v39, v41) => {
      let tmp_2 = compact_1(v41, int63!(0), Array::<Int63>::make(int63!(52), int63!(0)), int63!(0));
      match tmp_2 {
        (v67, v69) => {
          let w = v69 + int63!(1);
          let tmp_3 = n * v69;
          let tmp_4 = (n + int63!(1)) * w;
          let T = dp_1(v39, v67, v69, w, tmp_3, Array::<Int63>::make(tmp_4, int63!(0)));
          let tmp_5 = T.get_cloned(int63!(0));
          std::mem::drop(T);
          tmp_5
        },
      }
    },
  }
}

// Rocq: Cardhand.cardhand_implem.search
// Variant: uncurried
pub fn search_1(SU: Array<Int63>, RK: Array<Int63>, n: Int63, t: Int63, best: Int63) -> Int63 {
  search(SU, RK, n, t, best, ())
}

// Rocq: Cardhand.cardhand_implem.search (local: search)
// Variant: uncurried, lifted
pub fn search(SU: Array<Int63>, RK: Array<Int63>, n: Int63, t: Int63, best: Int63, _H: ()) -> Int63 {
  let tmp = t < int63!(4096);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = t + int63!(1);
      let tmp_2 = if inj_m(t) {
        let SU_clone = Clone::clone(&SU);
        let RK_clone = Clone::clone(&RK);
        imax(best, lcs_for(t, SU_clone, RK_clone, n))
      } else {
        best
      };
      search(SU, RK, n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(SU);
      std::mem::drop(RK);
      best
    },
  }
}

// Rocq: Cardhand.cardhand_implem.min_moves_impl
pub fn min_moves_impl(x: Array<rocq_string::RocqString>) -> Int63 {
  let n = x.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let tmp_1 = Array::<Int63>::make(n, int63!(0));
  let tmp_2 = prep_1(x, n, int63!(0), tmp, tmp_1);
  match tmp_2 {
    (v32, v34) => {
      let tmp_3 = search_1(v32, v34, n, int63!(0), int63!(0));
      n - tmp_3
    },
  }
}
