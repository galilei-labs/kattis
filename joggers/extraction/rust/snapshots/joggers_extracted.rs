#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct bst {
  pub vis: Rc<Array<bool>>,
  pub dst: Rc<Array<u64>>,
  pub par: Rc<Array<u64>>,
  pub pe: Rc<Array<u64>>,
  pub ord: Rc<Array<u64>>,
  pub tl: u64,
}

impl Clone for bst {
  fn clone(&self) -> Self {
    match self {
      bst { vis: __field0, dst: __field1, par: __field2, pe: __field3, ord: __field4, tl: __field5 } => bst { vis: Clone::clone(__field0), dst: Clone::clone(__field1), par: Clone::clone(__field2), pe: Clone::clone(__field3), ord: Clone::clone(__field4), tl: Clone::clone(__field5) },
    }
  }
}

#[derive(Clone, Copy)]
pub enum sumbool {
  left,
  right,
}

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<bool>; };

pub type uint = u64;

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.add
// Variant: uncurried
pub fn add(v0: u64, v1: u64) -> u64 {
  rocq_int63::add(v0, v1)
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.ltb
// Variant: uncurried
pub fn ltb(v0: u64, v1: u64) -> bool {
  rocq_int63::ltb(v0, v1)
}

// Rocq: Joggers.joggers_implem.bdec
pub fn bdec(b: bool) -> sumbool {
  if b {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Joggers.joggers_implem.lamp_loop
// Variant: uncurried
pub fn lamp_loop_1(xl: Rc<Array<u64>>, L: u64, i: u64, inl: Rc<Array<bool>>) -> Rc<Array<bool>> {
  lamp_loop(xl, L, i, inl, ())
}

// Rocq: Joggers.joggers_implem.lamp_loop (local: lamp_loop)
// Variant: uncurried, lifted
pub fn lamp_loop(xl: Rc<Array<u64>>, L: u64, i: u64, inl: Rc<Array<bool>>, _H: ()) -> Rc<Array<bool>> {
  let tmp = ltb(i, L);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&xl, i);
      let tmp_3 = rocq_array::set::<bool>(inl, tmp_2, true);
      lamp_loop(xl, L, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xl);
      inl
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Joggers.joggers_implem.ep
// Variant: uncurried
pub fn ep(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64) -> u64 {
  if ltb(k, m) {
    std::mem::drop(xb);
    let tmp = rocq_array::get::<u64>(&xa, k);
    std::mem::drop(xa);
    tmp
  } else {
    std::mem::drop(xa);
    let tmp_1 = rocq_array::get::<u64>(&xb, sub(k, m));
    std::mem::drop(xb);
    tmp_1
  }
}

// Rocq: Joggers.joggers_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cnt: Rc<Array<u64>>) -> Rc<Array<u64>> {
  cnt_loop(xa, xb, m, K, i, cnt, ())
}

// Rocq: Joggers.joggers_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cnt: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, K);
  match bdec(tmp) {
    sumbool::left => {
      let xa_clone = Rc::clone(&xa);
      let xb_clone = Rc::clone(&xb);
      let w = ep(xa_clone, xb_clone, m, i);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::get::<u64>(&cnt, w);
      let tmp_3 = rocq_array::set::<u64>(cnt, w, add(tmp_2, 1u64));
      cnt_loop(xa, xb, m, K, tmp_1, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      cnt
    },
  }
}

// Rocq: Joggers.joggers_implem.off_loop
// Variant: uncurried
pub fn off_loop_1(cnt: Rc<Array<u64>>, V: u64, v: u64, off: Rc<Array<u64>>, cur: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  off_loop(cnt, V, v, off, cur, ())
}

// Rocq: Joggers.joggers_implem.off_loop (local: off_loop)
// Variant: uncurried, lifted
pub fn off_loop(cnt: Rc<Array<u64>>, V: u64, v: u64, off: Rc<Array<u64>>, cur: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(v, V);
  match bdec(tmp) {
    sumbool::left => {
      let o = rocq_array::get::<u64>(&off, v);
      let tmp_1 = add(v, 1u64);
      let tmp_2 = add(v, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&cnt, v);
      let tmp_4 = rocq_array::set::<u64>(off, tmp_2, add(o, tmp_3));
      let tmp_5 = rocq_array::set::<u64>(cur, v, o);
      off_loop(cnt, V, tmp_1, tmp_4, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(cnt);
      (off, cur)
    },
  }
}

// Rocq: Joggers.joggers_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cur: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(xa, xb, m, K, i, cur, adj, ())
}

// Rocq: Joggers.joggers_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, K: u64, i: u64, cur: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, K);
  match bdec(tmp) {
    sumbool::left => {
      let xa_clone = Rc::clone(&xa);
      let xb_clone = Rc::clone(&xb);
      let w = ep(xa_clone, xb_clone, m, i);
      let c = rocq_array::get::<u64>(&cur, w);
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(cur, w, add(c, 1u64));
      let tmp_3 = rocq_array::set::<u64>(adj, c, i);
      fill_loop(xa, xb, m, K, tmp_1, tmp_2, tmp_3, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(cur);
      adj
    },
  }
}

// Rocq: Corelib.Init.Datatypes.snd
pub fn snd<A: 'static, B: Clone + 'static>(p: (A, B)) -> B {
  let p_1_clone = Clone::clone(&p.1);
  std::mem::drop(p);
  p_1_clone
}

// Rocq: Joggers.joggers_implem.tl
pub fn tl_owned(b: Rc<bst>) -> u64 {
  let b_tl_clone = Clone::clone(&b.tl);
  std::mem::drop(b);
  b_tl_clone
}

// Rocq: Joggers.joggers_implem.tl
// Variant: borrowed
pub fn tl(b: &Rc<bst>) -> u64 {
  let tmp = b;
  Clone::clone(&tmp.tl)
}

// Rocq: Joggers.joggers_implem.ord
pub fn ord(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_ord_clone = Rc::clone(&b.ord);
  std::mem::drop(b);
  b_ord_clone
}

// Rocq: Joggers.joggers_implem.oth
// Variant: uncurried
pub fn oth(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, m: u64, k: u64) -> u64 {
  if ltb(k, m) {
    std::mem::drop(xa);
    let tmp = rocq_array::get::<u64>(&xb, k);
    std::mem::drop(xb);
    tmp
  } else {
    std::mem::drop(xb);
    let tmp_1 = rocq_array::get::<u64>(&xa, sub(k, m));
    std::mem::drop(xa);
    tmp_1
  }
}

// Rocq: Joggers.joggers_implem.vis
pub fn vis(b: Rc<bst>) -> Rc<Array<bool>> {
  let b_vis_clone = Rc::clone(&b.vis);
  std::mem::drop(b);
  b_vis_clone
}

// Rocq: Joggers.joggers_implem.eid
// Variant: uncurried
pub fn eid(m: u64, k: u64) -> u64 {
  if ltb(k, m) {
    k
  } else {
    sub(k, m)
  }
}

// Rocq: Joggers.joggers_implem.dst
pub fn dst(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_dst_clone = Rc::clone(&b.dst);
  std::mem::drop(b);
  b_dst_clone
}

// Rocq: Joggers.joggers_implem.par
pub fn par(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_par_clone = Rc::clone(&b.par);
  std::mem::drop(b);
  b_par_clone
}

// Rocq: Joggers.joggers_implem.pe
pub fn pe(b: Rc<bst>) -> Rc<Array<u64>> {
  let b_pe_clone = Rc::clone(&b.pe);
  std::mem::drop(b);
  b_pe_clone
}

// Rocq: Joggers.joggers_implem.scan_loop
// Variant: uncurried
pub fn scan_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, u: u64, du: u64, hi: u64, i: u64, st: Rc<bst>) -> Rc<bst> {
  scan_loop(xa, xb, xd, m, adj, u, du, hi, i, st, ())
}

// Rocq: Joggers.joggers_implem.scan_loop (local: scan_loop)
// Variant: uncurried, lifted
pub fn scan_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, u: u64, du: u64, hi: u64, i: u64, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = ltb(i, hi);
  match bdec(tmp) {
    sumbool::left => {
      let k = rocq_array::get::<u64>(&adj, i);
      let xa_clone = Rc::clone(&xa);
      let xb_clone = Rc::clone(&xb);
      let w = oth(xa_clone, xb_clone, m, k);
      let st_clone = Rc::clone(&st);
      let tmp_1 = vis(st_clone);
      let tmp_2 = rocq_array::get::<bool>(&tmp_1, w);
      let st_ = if tmp_2 {
        std::mem::drop(tmp_1);
        st
      } else {
        std::mem::drop(tmp_1);
        let e = eid(m, k);
        let st_clone_1 = Rc::clone(&st);
        let tmp_3 = vis(st_clone_1);
        let tmp_4 = rocq_array::set::<bool>(tmp_3, w, true);
        let st_clone_2 = Rc::clone(&st);
        let tmp_5 = dst(st_clone_2);
        let tmp_6 = rocq_array::get::<u64>(&xd, e);
        let tmp_7 = rocq_array::set::<u64>(tmp_5, w, add(du, tmp_6));
        let st_clone_3 = Rc::clone(&st);
        let tmp_8 = par(st_clone_3);
        let tmp_9 = rocq_array::set::<u64>(tmp_8, w, u);
        let st_clone_4 = Rc::clone(&st);
        let tmp_10 = pe(st_clone_4);
        let tmp_11 = rocq_array::set::<u64>(tmp_10, w, e);
        let st_clone_5 = Rc::clone(&st);
        let tmp_12 = ord(st_clone_5);
        let tmp_13 = tl(&st);
        let tmp_14 = rocq_array::set::<u64>(tmp_12, tmp_13, w);
        Rc::new(bst { vis: tmp_4, dst: tmp_7, par: tmp_9, pe: tmp_11, ord: tmp_14, tl: add(tl_owned(st), 1u64) })
      };
      scan_loop(xa, xb, xd, m, adj, u, du, hi, add(i, 1u64), st_, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(xd);
      std::mem::drop(adj);
      st
    },
  }
}

// Rocq: Joggers.joggers_implem.bfs_loop
// Variant: uncurried
pub fn bfs_loop_1(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, off: Rc<Array<u64>>, h: u64, st: Rc<bst>) -> Rc<bst> {
  bfs_loop(xa, xb, xd, m, adj, off, h, st, ())
}

// Rocq: Joggers.joggers_implem.bfs_loop (local: bfs_loop)
// Variant: uncurried, lifted
pub fn bfs_loop(xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, m: u64, adj: Rc<Array<u64>>, off: Rc<Array<u64>>, h: u64, st: Rc<bst>, _H: ()) -> Rc<bst> {
  let tmp = ltb(h, tl(&st));
  match bdec(tmp) {
    sumbool::left => {
      let st_clone = Rc::clone(&st);
      let tmp_1 = ord(st_clone);
      let u = rocq_array::get::<u64>(&tmp_1, h);
      std::mem::drop(tmp_1);
      let st_clone_1 = Rc::clone(&st);
      let tmp_2 = dst(st_clone_1);
      let tmp_3 = rocq_array::get::<u64>(&tmp_2, u);
      std::mem::drop(tmp_2);
      let tmp_4 = rocq_array::get::<u64>(&off, add(u, 1u64));
      let tmp_5 = rocq_array::get::<u64>(&off, u);
      let xa_clone = Rc::clone(&xa);
      let xb_clone = Rc::clone(&xb);
      let xd_clone = Rc::clone(&xd);
      let adj_clone = Rc::clone(&adj);
      let st_ = scan_loop_1(xa_clone, xb_clone, xd_clone, m, adj_clone, u, tmp_3, tmp_4, tmp_5, st);
      bfs_loop(xa, xb, xd, m, adj, off, add(h, 1u64), st_, ())
    },
    sumbool::right => {
      std::mem::drop(xa);
      std::mem::drop(xb);
      std::mem::drop(xd);
      std::mem::drop(adj);
      std::mem::drop(off);
      st
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
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
pub fn negb(b: bool) -> bool {
  if b {
    false
  } else {
    true
  }
}

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
  }
}

// Rocq: Joggers.joggers_implem.sweep_loop
// Variant: uncurried
pub fn sweep_loop_1(s: u64, inl: Rc<Array<bool>>, ord_1: Rc<Array<u64>>, par_1: Rc<Array<u64>>, dst_1: Rc<Array<u64>>, i: u64, ch: Rc<Array<bool>>, c: u64) -> u64 {
  sweep_loop(s, inl, ord_1, par_1, dst_1, i, ch, c, ())
}

// Rocq: Joggers.joggers_implem.sweep_loop (local: sweep_loop)
// Variant: uncurried, lifted
pub fn sweep_loop(s: u64, inl: Rc<Array<bool>>, ord_1: Rc<Array<u64>>, par_1: Rc<Array<u64>>, dst_1: Rc<Array<u64>>, i: u64, ch: Rc<Array<bool>>, c: u64, _H: ()) -> u64 {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&ord_1, i);
      let p = rocq_array::get::<u64>(&par_1, v);
      let dp = rocq_array::get::<u64>(&dst_1, p);
      let tmp_1 = ltb(add(dp, dp), s);
      let tmp_2 = rocq_array::get::<bool>(&inl, v);
      let tmp_3 = rocq_array::get::<bool>(&ch, v);
      let tmp_4 = andb(tmp_1, negb(orb(tmp_2, tmp_3)));
      let tmp_5 = rocq_array::get::<bool>(&inl, p);
      let tmp_6 = rocq_array::get::<bool>(&ch, p);
      let tmp_7 = negb(orb(tmp_5, tmp_6));
      if andb(tmp_4, tmp_7) {
        let tmp_8 = sub(i, 1u64);
        let tmp_9 = rocq_array::set::<bool>(ch, p, true);
        sweep_loop(s, inl, ord_1, par_1, dst_1, tmp_8, tmp_9, add(c, 1u64), ())
      } else {
        sweep_loop(s, inl, ord_1, par_1, dst_1, sub(i, 1u64), ch, c, ())
      }
    },
    sumbool::right => {
      std::mem::drop(inl);
      std::mem::drop(ord_1);
      std::mem::drop(par_1);
      std::mem::drop(dst_1);
      std::mem::drop(ch);
      c
    },
  }
}

// Rocq: Joggers.joggers_implem.joggers_impl
// Variant: uncurried
pub fn joggers_impl(n: u64, s: u64, xa: Rc<Array<u64>>, xb: Rc<Array<u64>>, xd: Rc<Array<u64>>, xl: Rc<Array<u64>>) -> u64 {
  let m = rocq_array::length::<u64>(&xa);
  let K = add(m, m);
  let V = add(n, 1u64);
  let tmp = rocq_array::length::<u64>(&xl);
  let tmp_1 = rocq_array::make::<bool>(V, false);
  let inl = lamp_loop_1(xl, tmp, 0u64, tmp_1);
  let tmp_2 = rocq_array::make::<u64>(V, 0u64);
  let xa_clone = Rc::clone(&xa);
  let xb_clone = Rc::clone(&xb);
  let cnt = cnt_loop_1(xa_clone, xb_clone, m, K, 0u64, tmp_2);
  let tmp_3 = rocq_array::make::<u64>(add(V, 1u64), 0u64);
  let tmp_4 = rocq_array::make::<u64>(V, 0u64);
  let oc = off_loop_1(cnt, V, 0u64, tmp_3, tmp_4);
  let oc_clone = Clone::clone(&oc);
  let tmp_5 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(oc_clone);
  let tmp_6 = rocq_array::make::<u64>(K, 0u64);
  let xa_clone_1 = Rc::clone(&xa);
  let xb_clone_1 = Rc::clone(&xb);
  let adj = fill_loop_1(xa_clone_1, xb_clone_1, m, K, 0u64, tmp_5, tmp_6);
  let tmp_7 = rocq_array::make::<bool>(V, false);
  let tmp_8 = rocq_array::set::<bool>(tmp_7, 1u64, true);
  let tmp_9 = rocq_array::make::<u64>(V, 0u64);
  let tmp_10 = rocq_array::make::<u64>(V, 0u64);
  let tmp_11 = rocq_array::make::<u64>(V, 0u64);
  let tmp_12 = rocq_array::make::<u64>(n, 0u64);
  let tmp_13 = rocq_array::set::<u64>(tmp_12, 0u64, 1u64);
  let st0 = Rc::new(bst { vis: tmp_8, dst: tmp_9, par: tmp_10, pe: tmp_11, ord: tmp_13, tl: 1u64 });
  let tmp_14 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(oc);
  let st = bfs_loop_1(xa, xb, xd, m, adj, tmp_14, 0u64, st0);
  let st_clone = Rc::clone(&st);
  let tmp_15 = ord(st_clone);
  let st_clone_1 = Rc::clone(&st);
  let tmp_16 = par(st_clone_1);
  let st_clone_2 = Rc::clone(&st);
  let tmp_17 = dst(st_clone_2);
  let tmp_18 = sub(tl_owned(st), 1u64);
  let tmp_19 = rocq_array::make::<bool>(V, false);
  sweep_loop_1(s, inl, tmp_15, tmp_16, tmp_17, tmp_18, tmp_19, 0u64)
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
