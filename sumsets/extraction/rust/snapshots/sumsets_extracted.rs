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

pub struct tbl {
  pub th: Rc<big>,
  pub tn: Rc<big>,
  pub tc: Rc<big>,
  pub tk: u64,
}

impl Clone for tbl {
  fn clone(&self) -> Self {
    match self {
      tbl { th: __field0, tn: __field1, tc: __field2, tk: __field3 } => tbl { th: Clone::clone(__field0), tn: Clone::clone(__field1), tc: Clone::clone(__field2), tk: Clone::clone(__field3) },
    }
  }
}

pub struct big {
  pub b0: Rc<Array<u64>>,
  pub b1: Rc<Array<u64>>,
  pub b2: Rc<Array<u64>>,
  pub b3: Rc<Array<u64>>,
}

impl Clone for big {
  fn clone(&self) -> Self {
    match self {
      big { b0: __field0, b1: __field1, b2: __field2, b3: __field3 } => big { b0: Clone::clone(__field0), b1: Clone::clone(__field1), b2: Clone::clone(__field2), b3: Clone::clone(__field3) },
    }
  }
}

pub type sint = u64;

// Rocq: Sumsets.sumsets_implem.HA
pub fn HA() -> u64 {
  2177342782468422677u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsr
// Variant: uncurried
pub fn lsr(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsr(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.mul
// Variant: uncurried
pub fn mul(v0: u64, v1: u64) -> u64 {
  rocq_int63::mul(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lsl
// Variant: uncurried
pub fn lsl(v0: u64, v1: u64) -> u64 {
  rocq_int63::lsl(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Sumsets.sumsets_implem.clen
// Variant: uncurried
pub fn clen(cap: u64, q: u64) -> u64 {
  let lo = lsl(q, 21u64);
  if leb(cap, lo) {
    0u64
  } else {
    let tmp = sub(cap, lo);
    if leb(tmp, 2097152u64) {
      sub(cap, lo)
    } else {
      2097152u64
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bmake
// Variant: uncurried
pub fn bmake(cap: u64, v: u64) -> Rc<big> {
  let tmp = rocq_array::make::<u64>(clen(cap, 0u64), v);
  let tmp_1 = rocq_array::make::<u64>(clen(cap, 1u64), v);
  let tmp_2 = rocq_array::make::<u64>(clen(cap, 2u64), v);
  let tmp_3 = rocq_array::make::<u64>(clen(cap, 3u64), v);
  Rc::new(big { b0: tmp, b1: tmp_1, b2: tmp_2, b3: tmp_3 })
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

// Rocq: Sumsets.sumsets_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Sumsets.sumsets_implem.tk
// Variant: borrowed
pub fn tk(t: &Rc<tbl>) -> u64 {
  let tmp = t;
  Clone::clone(&tmp.tk)
}

// Rocq: Sumsets.sumsets_implem.hash
// Variant: uncurried
pub fn hash(cap: u64, s: u64) -> u64 {
  let tmp = lsr(mul(s, __rocq_global_176), 40u64);
  lsr(mul(tmp, cap), 23u64)
}

// Rocq: Sumsets.sumsets_implem.b0
pub fn b0_owned(b: Rc<big>) -> Rc<Array<u64>> {
  let b_b0_clone = Rc::clone(&b.b0);
  std::mem::drop(b);
  b_b0_clone
}

// Rocq: Sumsets.sumsets_implem.b0
// Variant: borrowed
pub fn b0(b: &Rc<big>) -> Rc<Array<u64>> {
  let tmp = b;
  Rc::clone(&tmp.b0)
}

// Rocq: Sumsets.sumsets_implem.b1
pub fn b1_owned(b: Rc<big>) -> Rc<Array<u64>> {
  let b_b1_clone = Rc::clone(&b.b1);
  std::mem::drop(b);
  b_b1_clone
}

// Rocq: Sumsets.sumsets_implem.b1
// Variant: borrowed
pub fn b1(b: &Rc<big>) -> Rc<Array<u64>> {
  let tmp = b;
  Rc::clone(&tmp.b1)
}

// Rocq: Sumsets.sumsets_implem.b2
pub fn b2_owned(b: Rc<big>) -> Rc<Array<u64>> {
  let b_b2_clone = Rc::clone(&b.b2);
  std::mem::drop(b);
  b_b2_clone
}

// Rocq: Sumsets.sumsets_implem.b2
// Variant: borrowed
pub fn b2(b: &Rc<big>) -> Rc<Array<u64>> {
  let tmp = b;
  Rc::clone(&tmp.b2)
}

// Rocq: Sumsets.sumsets_implem.b3
pub fn b3_owned(b: Rc<big>) -> Rc<Array<u64>> {
  let b_b3_clone = Rc::clone(&b.b3);
  std::mem::drop(b);
  b_b3_clone
}

// Rocq: Sumsets.sumsets_implem.b3
// Variant: borrowed
pub fn b3(b: &Rc<big>) -> Rc<Array<u64>> {
  let tmp = b;
  Rc::clone(&tmp.b3)
}

// Rocq: Sumsets.sumsets_implem.chunk
// Variant: uncurried
pub fn chunk_owned(b: Rc<big>, q: u64) -> Rc<Array<u64>> {
  if eqb(q, 0u64) {
    b0_owned(b)
  } else {
    if eqb(q, 1u64) {
      b1_owned(b)
    } else {
      if eqb(q, 2u64) {
        b2_owned(b)
      } else {
        b3_owned(b)
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.chunk
// Variant: borrowed, uncurried
pub fn chunk(b: &Rc<big>, q: u64) -> Rc<Array<u64>> {
  let q_1 = q;
  if eqb(q_1, 0u64) {
    b0(b)
  } else {
    if eqb(q_1, 1u64) {
      b1(b)
    } else {
      if eqb(q_1, 2u64) {
        b2(b)
      } else {
        b3(b)
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bget
// Variant: uncurried
pub fn bget_owned(b: Rc<big>, k: u64) -> u64 {
  let q = lsr(k, 21u64);
  let tmp = chunk_owned(b, q);
  let tmp_1 = rocq_array::get::<u64>(&tmp, sub(k, lsl(q, 21u64)));
  std::mem::drop(tmp);
  tmp_1
}

// Rocq: Sumsets.sumsets_implem.bget
// Variant: borrowed, uncurried
pub fn bget(b: &Rc<big>, k: u64) -> u64 {
  let k_1 = k;
  let q = lsr(k_1, 21u64);
  let tmp = chunk(b, q);
  let tmp_1 = rocq_array::get::<u64>(&tmp, sub(k_1, lsl(q, 21u64)));
  std::mem::drop(tmp);
  tmp_1
}

// Rocq: Sumsets.sumsets_implem.th
pub fn th(t: Rc<tbl>) -> Rc<big> {
  let t_th_clone = Rc::clone(&t.th);
  std::mem::drop(t);
  t_th_clone
}

// Rocq: Sumsets.sumsets_implem.upd
// Variant: uncurried
pub fn upd(b: Rc<big>, q: u64, a: Rc<Array<u64>>) -> Rc<big> {
  if eqb(q, 0u64) {
    let b_clone = Rc::clone(&b);
    let tmp = b1_owned(b_clone);
    let b_clone_1 = Rc::clone(&b);
    let tmp_1 = b2_owned(b_clone_1);
    let tmp_2 = b3_owned(b);
    Rc::new(big { b0: a, b1: tmp, b2: tmp_1, b3: tmp_2 })
  } else {
    if eqb(q, 1u64) {
      let b_clone_2 = Rc::clone(&b);
      let tmp_3 = b0_owned(b_clone_2);
      let b_clone_3 = Rc::clone(&b);
      let tmp_4 = b2_owned(b_clone_3);
      let tmp_5 = b3_owned(b);
      Rc::new(big { b0: tmp_3, b1: a, b2: tmp_4, b3: tmp_5 })
    } else {
      if eqb(q, 2u64) {
        let b_clone_4 = Rc::clone(&b);
        let tmp_6 = b0_owned(b_clone_4);
        let b_clone_5 = Rc::clone(&b);
        let tmp_7 = b1_owned(b_clone_5);
        let tmp_8 = b3_owned(b);
        Rc::new(big { b0: tmp_6, b1: tmp_7, b2: a, b3: tmp_8 })
      } else {
        let b_clone_6 = Rc::clone(&b);
        let tmp_9 = b0_owned(b_clone_6);
        let b_clone_7 = Rc::clone(&b);
        let tmp_10 = b1_owned(b_clone_7);
        let tmp_11 = b2_owned(b);
        Rc::new(big { b0: tmp_9, b1: tmp_10, b2: tmp_11, b3: a })
      }
    }
  }
}

// Rocq: Sumsets.sumsets_implem.bset
// Variant: uncurried
pub fn bset(b: Rc<big>, k: u64, v: u64) -> Rc<big> {
  let q = lsr(k, 21u64);
  let b_clone = Rc::clone(&b);
  let tmp = chunk_owned(b_clone, q);
  let tmp_1 = rocq_array::set::<u64>(tmp, sub(k, lsl(q, 21u64)), v);
  upd(b, q, tmp_1)
}

// Rocq: Sumsets.sumsets_implem.tn
pub fn tn(t: Rc<tbl>) -> Rc<big> {
  let t_tn_clone = Rc::clone(&t.tn);
  std::mem::drop(t);
  t_tn_clone
}

// Rocq: Sumsets.sumsets_implem.tc
pub fn tc(t: Rc<tbl>) -> Rc<big> {
  let t_tc_clone = Rc::clone(&t.tc);
  std::mem::drop(t);
  t_tc_clone
}

// Rocq: Sumsets.sumsets_implem.code
// Variant: uncurried
pub fn code(i: u64, j: u64) -> u64 {
  add(lsl(i, 12u64), j)
}

// Rocq: Sumsets.sumsets_implem.ins
// Variant: uncurried
pub fn ins(x: Rc<Array<u64>>, cap: u64, i: u64, j: u64, T: Rc<tbl>) -> Rc<tbl> {
  let tmp = tk(&T);
  let e = add(tmp, 1u64);
  let tmp_1 = rocq_array::get::<u64>(&x, i);
  let tmp_2 = rocq_array::get::<u64>(&x, j);
  std::mem::drop(x);
  let h = hash(cap, add(tmp_1, tmp_2));
  let T_clone = Rc::clone(&T);
  let old = bget_owned(th(T_clone), h);
  let T_clone_1 = Rc::clone(&T);
  let nx = bset(tn(T_clone_1), e, old);
  let T_clone_2 = Rc::clone(&T);
  let cd = bset(tc(T_clone_2), e, code(i, j));
  let hd = bset(th(T), h, e);
  Rc::new(tbl { th: hd, tn: nx, tc: cd, tk: e })
}

// Rocq: Sumsets.sumsets_implem.build_in
// Variant: uncurried
pub fn build_in_1(x: Rc<Array<u64>>, cap: u64, n: u64, i: u64, j: u64, T: Rc<tbl>) -> Rc<tbl> {
  build_in(x, cap, n, i, j, T, ())
}

// Rocq: Sumsets.sumsets_implem.build_in (local: build_in)
// Variant: uncurried, lifted
pub fn build_in(x: Rc<Array<u64>>, cap: u64, n: u64, i: u64, j: u64, T: Rc<tbl>, _H: ()) -> Rc<tbl> {
  let tmp = ltb(j, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(j, 1u64);
      let x_clone = Rc::clone(&x);
      let tmp_2 = ins(x_clone, cap, i, j, T);
      build_in(x, cap, n, i, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      T
    },
  }
}

// Rocq: Sumsets.sumsets_implem.build_out
// Variant: uncurried
pub fn build_out_1(x: Rc<Array<u64>>, cap: u64, n: u64, i: u64, T: Rc<tbl>) -> Rc<tbl> {
  build_out(x, cap, n, i, T, ())
}

// Rocq: Sumsets.sumsets_implem.build_out (local: build_out)
// Variant: uncurried, lifted
pub fn build_out(x: Rc<Array<u64>>, cap: u64, n: u64, i: u64, T: Rc<tbl>, _H: ()) -> Rc<tbl> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = add(i, 1u64);
      let x_clone = Rc::clone(&x);
      let tmp_3 = build_in_1(x_clone, cap, n, i, tmp_2, T);
      build_out(x, cap, n, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(x);
      T
    },
  }
}

// Rocq: Corelib.Init.Datatypes.andb
// Variant: uncurried
pub fn andb(b1_1: bool, b2_1: bool) -> bool {
  if b1_1 {
    b2_1
  } else {
    false
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.lesb
// Variant: uncurried
pub fn lesb(v0: u64, v1: u64) -> bool {
  rocq_int63::lesb(v0, v1)
}

// Rocq: Corelib.Init.Datatypes.negb
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Sumsets.sumsets_implem.chk
// Variant: uncurried
pub fn chk(x: Rc<Array<u64>>, n: u64, k: u64, l: u64, t: u64, c: u64) -> bool {
  let i = lsr(c, 12u64);
  let j = sub(c, lsl(i, 12u64));
  let tmp = andb(ltb(i, n), ltb(j, n));
  let tmp_1 = andb(tmp, negb(eqb(i, j)));
  let tmp_2 = andb(tmp_1, negb(eqb(i, k)));
  let tmp_3 = andb(tmp_2, negb(eqb(i, l)));
  let tmp_4 = andb(tmp_3, negb(eqb(j, k)));
  let tmp_5 = andb(tmp_4, negb(eqb(j, l)));
  let tmp_6 = rocq_array::get::<u64>(&x, i);
  let tmp_7 = rocq_array::get::<u64>(&x, j);
  std::mem::drop(x);
  andb(tmp_5, eqb(add(tmp_6, tmp_7), t))
}

// Rocq: Sumsets.sumsets_implem.walk
// Variant: uncurried
pub fn walk_1(x: Rc<Array<u64>>, nx: Rc<big>, cd: Rc<big>, n: u64, k: u64, l: u64, t: u64, e: u64) -> bool {
  walk(x, nx, cd, n, k, l, t, e, ())
}

// Rocq: Sumsets.sumsets_implem.walk (local: walk)
// Variant: uncurried, lifted
pub fn walk(x: Rc<Array<u64>>, nx: Rc<big>, cd: Rc<big>, n: u64, k: u64, l: u64, t: u64, e: u64, _H: ()) -> bool {
  let tmp = eqb(e, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(x);
      std::mem::drop(nx);
      std::mem::drop(cd);
      false
    },
    sumbool::right => {
      let tmp_1 = bget(&cd, e);
      let x_clone = Rc::clone(&x);
      if chk(x_clone, n, k, l, t, tmp_1) {
        std::mem::drop(x);
        std::mem::drop(nx);
        std::mem::drop(cd);
        true
      } else {
        let e_ = bget(&nx, e);
        let tmp_2 = ltb(e_, e);
        match bdec(tmp_2) {
          sumbool::left => {
            walk(x, nx, cd, n, k, l, t, e_, ())
          },
          sumbool::right => {
            std::mem::drop(x);
            std::mem::drop(nx);
            std::mem::drop(cd);
            false
          },
        }
      }
    },
  }
}

// Rocq: Sumsets.sumsets_implem.query
// Variant: uncurried
pub fn query(x: Rc<Array<u64>>, T: Rc<tbl>, cap: u64, n: u64, k: u64, l: u64) -> bool {
  let tmp = rocq_array::get::<u64>(&x, k);
  let tmp_1 = rocq_array::get::<u64>(&x, l);
  let t = sub(tmp, tmp_1);
  let T_clone = Rc::clone(&T);
  let e = bget_owned(th(T_clone), hash(cap, t));
  let T_clone_1 = Rc::clone(&T);
  walk_1(x, tn(T_clone_1), tc(T), n, k, l, t, e)
}

// Rocq: Sumsets.sumsets_implem.any_l
// Variant: uncurried
pub fn any_l_1(x: Rc<Array<u64>>, T: Rc<tbl>, cap: u64, n: u64, k: u64, l: u64) -> bool {
  any_l(x, T, cap, n, k, l, ())
}

// Rocq: Sumsets.sumsets_implem.any_l (local: any_l)
// Variant: uncurried, lifted
pub fn any_l(x: Rc<Array<u64>>, T: Rc<tbl>, cap: u64, n: u64, k: u64, l: u64, _H: ()) -> bool {
  let tmp = ltb(l, n);
  match bdec(tmp) {
    sumbool::left => {
      if eqb(l, k) {
        any_l(x, T, cap, n, k, add(l, 1u64), ())
      } else {
        let x_clone = Rc::clone(&x);
        let T_clone = Rc::clone(&T);
        if query(x_clone, T_clone, cap, n, k, l) {
          std::mem::drop(x);
          std::mem::drop(T);
          true
        } else {
          any_l(x, T, cap, n, k, add(l, 1u64), ())
        }
      }
    },
    sumbool::right => {
      std::mem::drop(x);
      std::mem::drop(T);
      false
    },
  }
}

// Rocq: Sumsets.sumsets_implem.best_k
// Variant: uncurried
pub fn best_k_1(x: Rc<Array<u64>>, T: Rc<tbl>, cap: u64, n: u64, k: u64, found: bool, best: u64) -> Rc<option<u64>> {
  best_k(x, T, cap, n, k, found, best, ())
}

// Rocq: Sumsets.sumsets_implem.best_k (local: best_k)
// Variant: uncurried, lifted
pub fn best_k(x: Rc<Array<u64>>, T: Rc<tbl>, cap: u64, n: u64, k: u64, found: bool, best: u64, _H: ()) -> Rc<option<u64>> {
  let tmp = ltb(k, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&x, k);
      let tmp_2 = lesb(tmp_1, best);
      if andb(found, tmp_2) {
        best_k(x, T, cap, n, add(k, 1u64), found, best, ())
      } else {
        let x_clone = Rc::clone(&x);
        let T_clone = Rc::clone(&T);
        if any_l_1(x_clone, T_clone, cap, n, k, 0u64) {
          let tmp_3 = add(k, 1u64);
          let tmp_4 = rocq_array::get::<u64>(&x, k);
          best_k(x, T, cap, n, tmp_3, true, tmp_4, ())
        } else {
          best_k(x, T, cap, n, add(k, 1u64), found, best, ())
        }
      }
    },
    sumbool::right => {
      if found {
        std::mem::drop(x);
        std::mem::drop(T);
        Rc::new(option::<u64>::Some(best))
      } else {
        std::mem::drop(x);
        std::mem::drop(T);
        Rc::new(option::<u64>::None)
      }
    },
  }
}

// Rocq: Sumsets.sumsets_implem.sumsets_impl
pub fn sumsets_impl(x: Rc<Array<u64>>) -> Rc<option<u64>> {
  let n = rocq_array::length::<u64>(&x);
  let tmp = sub(n, 1u64);
  let cap = add(lsr(mul(n, tmp), 1u64), 1u64);
  let T0 = Rc::new(tbl { th: bmake(cap, 0u64), tn: bmake(cap, 0u64), tc: bmake(cap, 0u64), tk: 0u64 });
  let x_clone = Rc::clone(&x);
  let T = build_out_1(x_clone, cap, n, 0u64, T0);
  best_k_1(x, T, cap, n, 0u64, false, 0u64)
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
const __rocq_global_176: u64 = 2177342782468422677u64;