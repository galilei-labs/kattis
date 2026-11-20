#[allow(unused_imports)] use std::rc::Rc;
#[allow(unused_imports)] use rocq_array::Array;

const _: () = { fn require_copy<T: Copy>() {} let _ = require_copy::<u64>; };

pub struct St {
  pub st_dist: Rc<Array<u64>>,
  pub st_hk: Rc<Array<u64>>,
  pub st_hv: Rc<Array<u64>>,
  pub st_sz: u64,
}

impl Clone for St {
  fn clone(&self) -> Self {
    match self {
      St { st_dist: __field0, st_hk: __field1, st_hv: __field2, st_sz: __field3 } => St { st_dist: Clone::clone(__field0), st_hk: Clone::clone(__field1), st_hv: Clone::clone(__field2), st_sz: Clone::clone(__field3) },
    }
  }
}

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

pub type uint = u64;

// Rocq: Shortestpath1.shortestpath1_implem.INF
pub fn INF() -> u64 {
  9223372036854775807u64
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.eqb
// Variant: uncurried
pub fn eqb(v0: u64, v1: u64) -> bool {
  rocq_int63::eqb(v0, v1)
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

// Rocq: Shortestpath1.shortestpath1_implem.bdec
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

// Rocq: Shortestpath1.shortestpath1_implem.count_loop
// Variant: uncurried
pub fn count_loop_1(us: Rc<Array<u64>>, m: u64, k: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  count_loop(us, m, k, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.count_loop (local: count_loop)
// Variant: uncurried, lifted
pub fn count_loop(us: Rc<Array<u64>>, m: u64, k: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&us, k);
      let u1 = add(tmp_1, 1u64);
      let tmp_2 = add(k, 1u64);
      let tmp_3 = rocq_array::get::<u64>(&c, u1);
      let tmp_4 = rocq_array::set::<u64>(c, u1, add(tmp_3, 1u64));
      count_loop(us, m, tmp_2, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(us);
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop
// Variant: uncurried
pub fn prefix_loop_1(n: u64, i: u64, c: Rc<Array<u64>>) -> Rc<Array<u64>> {
  prefix_loop(n, i, c, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.prefix_loop (local: prefix_loop)
// Variant: uncurried, lifted
pub fn prefix_loop(n: u64, i: u64, c: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let a = rocq_array::get::<u64>(&c, i);
      let b = rocq_array::get::<u64>(&c, add(i, 1u64));
      let tmp_1 = add(i, 1u64);
      let tmp_2 = rocq_array::set::<u64>(c, add(i, 1u64), add(b, a));
      prefix_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      c
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  fill_loop(us, vs, ws, m, k, pos, adj, wt, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, m: u64, k: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(k, m);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&us, k);
      let j = rocq_array::get::<u64>(&pos, u);
      let tmp_1 = add(k, 1u64);
      let tmp_2 = rocq_array::set::<u64>(pos, u, add(j, 1u64));
      let tmp_3 = rocq_array::get::<u64>(&vs, k);
      let tmp_4 = rocq_array::set::<u64>(adj, j, tmp_3);
      let tmp_5 = rocq_array::get::<u64>(&ws, k);
      let tmp_6 = rocq_array::set::<u64>(wt, j, tmp_5);
      fill_loop(us, vs, ws, m, tmp_1, tmp_2, tmp_4, tmp_6, ())
    },
    sumbool::right => {
      std::mem::drop(us);
      std::mem::drop(vs);
      std::mem::drop(ws);
      std::mem::drop(pos);
      (adj, wt)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
pub fn st_sz_owned(s: Rc<St>) -> u64 {
  let s_st_sz_clone = Clone::clone(&s.st_sz);
  std::mem::drop(s);
  s_st_sz_clone
}

// Rocq: Shortestpath1.shortestpath1_implem.st_sz
// Variant: borrowed
pub fn st_sz(s: &Rc<St>) -> u64 {
  let tmp = s;
  Clone::clone(&tmp.st_sz)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hv
// Variant: borrowed
pub fn st_hv(s: &Rc<St>) -> Rc<Array<u64>> {
  let tmp = s;
  Rc::clone(&tmp.st_hv)
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

// Rocq: Shortestpath1.shortestpath1_implem.child
// Variant: uncurried
pub fn child(hk: Rc<Array<u64>>, sz: u64, l: u64) -> u64 {
  let tmp = ltb(add(l, 1u64), sz);
  let tmp_1 = rocq_array::get::<u64>(&hk, add(l, 1u64));
  let tmp_2 = rocq_array::get::<u64>(&hk, l);
  let tmp_3 = ltb(tmp_1, tmp_2);
  if andb(tmp, tmp_3) {
    std::mem::drop(hk);
    add(l, 1u64)
  } else {
    std::mem::drop(hk);
    l
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down
// Variant: uncurried
pub fn sift_down_1(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, i: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sift_down(hk, hv, sz, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_down (local: sift_down)
// Variant: uncurried, lifted
pub fn sift_down(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, i: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = add(i, i);
  let l = add(tmp, 1u64);
  let tmp_1 = andb(ltb(l, sz), ltb(i, l));
  match bdec(tmp_1) {
    sumbool::left => {
      let hk_clone = Rc::clone(&hk);
      let c = child(hk_clone, sz, l);
      let ki = rocq_array::get::<u64>(&hk, i);
      let kc = rocq_array::get::<u64>(&hk, c);
      let tmp_2 = ltb(kc, ki);
      match bdec(tmp_2) {
        sumbool::left => {
          let vi = rocq_array::get::<u64>(&hv, i);
          let vc = rocq_array::get::<u64>(&hv, c);
          let tmp_3 = rocq_array::set::<u64>(hk, i, kc);
          let tmp_4 = rocq_array::set::<u64>(tmp_3, c, ki);
          let tmp_5 = rocq_array::set::<u64>(hv, i, vc);
          let tmp_6 = rocq_array::set::<u64>(tmp_5, c, vi);
          sift_down(tmp_4, tmp_6, sz, c, ())
        },
        sumbool::right => {
          (hk, hv)
        },
      }
    },
    sumbool::right => {
      (hk, hv)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.pop
// Variant: uncurried
pub fn pop(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let sz_ = sub(sz, 1u64);
  let k = rocq_array::get::<u64>(&hk, sz_);
  let v = rocq_array::get::<u64>(&hv, sz_);
  let tmp = rocq_array::set::<u64>(hk, 0u64, k);
  let tmp_1 = rocq_array::set::<u64>(hv, 0u64, v);
  sift_down_1(tmp, tmp_1, sz_, 0u64)
}

// Rocq: Shortestpath1.shortestpath1_implem.st_hk
// Variant: borrowed
pub fn st_hk(s: &Rc<St>) -> Rc<Array<u64>> {
  let tmp = s;
  Rc::clone(&tmp.st_hk)
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up
// Variant: uncurried
pub fn sift_up_1(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, i: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  sift_up(hk, hv, i, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.sift_up (local: sift_up)
// Variant: uncurried, lifted
pub fn sift_up(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, i: u64, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(0u64, i);
  match bdec(tmp) {
    sumbool::left => {
      let p = lsr(sub(i, 1u64), 1u64);
      let ki = rocq_array::get::<u64>(&hk, i);
      let kp = rocq_array::get::<u64>(&hk, p);
      let tmp_1 = ltb(ki, kp);
      match bdec(tmp_1) {
        sumbool::left => {
          let vi = rocq_array::get::<u64>(&hv, i);
          let vp = rocq_array::get::<u64>(&hv, p);
          let tmp_2 = rocq_array::set::<u64>(hk, i, kp);
          let tmp_3 = rocq_array::set::<u64>(tmp_2, p, ki);
          let tmp_4 = rocq_array::set::<u64>(hv, i, vp);
          let tmp_5 = rocq_array::set::<u64>(tmp_4, p, vi);
          sift_up(tmp_3, tmp_5, p, ())
        },
        sumbool::right => {
          (hk, hv)
        },
      }
    },
    sumbool::right => {
      (hk, hv)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.push
// Variant: uncurried
pub fn push(hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, k: u64, v: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = rocq_array::set::<u64>(hk, sz, k);
  let tmp_1 = rocq_array::set::<u64>(hv, sz, v);
  sift_up_1(tmp, tmp_1, sz)
}

// Rocq: Shortestpath1.shortestpath1_implem.scan
// Variant: uncurried
pub fn scan_1(adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, du: u64, hi: u64, j: u64, dist: Rc<Array<u64>>, hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64) -> Rc<St> {
  scan(adj, wt, du, hi, j, dist, hk, hv, sz, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.scan (local: scan)
// Variant: uncurried, lifted
pub fn scan(adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, du: u64, hi: u64, j: u64, dist: Rc<Array<u64>>, hk: Rc<Array<u64>>, hv: Rc<Array<u64>>, sz: u64, _H: ()) -> Rc<St> {
  let tmp = ltb(j, hi);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&adj, j);
      let tmp_1 = rocq_array::get::<u64>(&wt, j);
      let nd = add(du, tmp_1);
      let tmp_2 = rocq_array::get::<u64>(&dist, v);
      let tmp_3 = ltb(nd, tmp_2);
      match bdec(tmp_3) {
        sumbool::left => {
          let tmp_4 = push(hk, hv, sz, nd, v);
          match tmp_4 {
            (v63, v65) => {
              let tmp_5 = add(j, 1u64);
              let tmp_6 = rocq_array::set::<u64>(dist, v, nd);
              scan(adj, wt, du, hi, tmp_5, tmp_6, v63, v65, add(sz, 1u64), ())
            },
          }
        },
        sumbool::right => {
          scan(adj, wt, du, hi, add(j, 1u64), dist, hk, hv, sz, ())
        },
      }
    },
    sumbool::right => {
      std::mem::drop(adj);
      std::mem::drop(wt);
      Rc::new(St { st_dist: dist, st_hk: hk, st_hv: hv, st_sz: sz })
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.st_dist
pub fn st_dist(s: Rc<St>) -> Rc<Array<u64>> {
  let s_st_dist_clone = Rc::clone(&s.st_dist);
  std::mem::drop(s);
  s_st_dist_clone
}

// Rocq: Shortestpath1.shortestpath1_implem.main
// Variant: uncurried
pub fn main_2(off: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, done: Rc<Array<u64>>, st: Rc<St>) -> Rc<Array<u64>> {
  main_1(off, adj, wt, done, st, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.main (local: main)
// Variant: uncurried, lifted
pub fn main_1(off: Rc<Array<u64>>, adj: Rc<Array<u64>>, wt: Rc<Array<u64>>, done: Rc<Array<u64>>, st: Rc<St>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(0u64, st_sz(&st));
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = st_hv(&st);
      let u = rocq_array::get::<u64>(&tmp_1, 0u64);
      let tmp_2 = st_hk(&st);
      let tmp_3 = st_hv(&st);
      let tmp_4 = pop(tmp_2, tmp_3, st_sz(&st));
      match tmp_4 {
        (v54, v56) => {
          let tmp_5 = rocq_array::length::<u64>(&done);
          let tmp_6 = ltb(u, tmp_5);
          let tmp_7 = rocq_array::get::<u64>(&done, u);
          let tmp_8 = andb(tmp_6, eqb(tmp_7, 0u64));
          match bdec(tmp_8) {
            sumbool::left => {
              std::mem::drop(tmp_1);
              let st_clone = Rc::clone(&st);
              let tmp_9 = st_dist(st_clone);
              let tmp_10 = rocq_array::get::<u64>(&tmp_9, u);
              std::mem::drop(tmp_9);
              let tmp_11 = rocq_array::get::<u64>(&off, add(u, 1u64));
              let tmp_12 = rocq_array::get::<u64>(&off, u);
              let st_clone_1 = Rc::clone(&st);
              let tmp_13 = st_dist(st_clone_1);
              let tmp_14 = sub(st_sz_owned(st), 1u64);
              let adj_clone = Rc::clone(&adj);
              let wt_clone = Rc::clone(&wt);
              let st2 = scan_1(adj_clone, wt_clone, tmp_10, tmp_11, tmp_12, tmp_13, v54, v56, tmp_14);
              let tmp_15 = rocq_array::set::<u64>(done, u, 1u64);
              main_1(off, adj, wt, tmp_15, st2, ())
            },
            sumbool::right => {
              std::mem::drop(tmp_1);
              let st_clone_2 = Rc::clone(&st);
              let tmp_16 = st_dist(st_clone_2);
              main_1(off, adj, wt, done, Rc::new(St { st_dist: tmp_16, st_hk: v54, st_hv: v56, st_sz: sub(st_sz_owned(st), 1u64) }), ())
            },
          }
        },
      }
    },
    sumbool::right => {
      std::mem::drop(off);
      std::mem::drop(adj);
      std::mem::drop(wt);
      std::mem::drop(done);
      st_dist(st)
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.out_loop
// Variant: uncurried
pub fn out_loop_1(dist: Rc<Array<u64>>, n: u64, v: u64, out: Rc<Array<Rc<option<u64>>>>) -> Rc<Array<Rc<option<u64>>>> {
  out_loop(dist, n, v, out, ())
}

// Rocq: Shortestpath1.shortestpath1_implem.out_loop (local: out_loop)
// Variant: uncurried, lifted
pub fn out_loop(dist: Rc<Array<u64>>, n: u64, v: u64, out: Rc<Array<Rc<option<u64>>>>, _H: ()) -> Rc<Array<Rc<option<u64>>>> {
  let tmp = ltb(v, n);
  match bdec(tmp) {
    sumbool::left => {
      let d = rocq_array::get::<u64>(&dist, v);
      let tmp_1 = add(v, 1u64);
      let tmp_2 = __rocq_global_253;
      let tmp_3 = if eqb(d, tmp_2) {
        Rc::new(option::<u64>::None)
      } else {
        Rc::new(option::<u64>::Some(d))
      };
      let tmp_4 = rocq_array::set::<Rc<option<u64>>>(out, v, tmp_3);
      out_loop(dist, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(dist);
      out
    },
  }
}

// Rocq: Shortestpath1.shortestpath1_implem.dijkstra_impl
// Variant: uncurried
pub fn dijkstra_impl(n: u64, us: Rc<Array<u64>>, vs: Rc<Array<u64>>, ws: Rc<Array<u64>>, s: u64) -> Rc<Array<Rc<option<u64>>>> {
  let m = rocq_array::length::<u64>(&us);
  let tmp = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let us_clone = Rc::clone(&us);
  let c = count_loop_1(us_clone, m, 0u64, tmp);
  let off = prefix_loop_1(n, 0u64, c);
  let tmp_1 = rocq_array::copy::<u64>(&off);
  let tmp_2 = rocq_array::make::<u64>(m, 0u64);
  let tmp_3 = rocq_array::make::<u64>(m, 0u64);
  let tmp_4 = fill_loop_1(us, vs, ws, m, 0u64, tmp_1, tmp_2, tmp_3);
  match tmp_4 {
    (v82, v84) => {
      let tmp_5 = rocq_array::make::<u64>(n, __rocq_global_253);
      let dist0 = rocq_array::set::<u64>(tmp_5, s, 0u64);
      let hk0 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let tmp_6 = rocq_array::make::<u64>(add(m, 1u64), 0u64);
      let hv0 = rocq_array::set::<u64>(tmp_6, 0u64, s);
      let tmp_7 = rocq_array::make::<u64>(n, 0u64);
      let dist = main_2(off, v82, v84, tmp_7, Rc::new(St { st_dist: dist0, st_hk: hk0, st_hv: hv0, st_sz: 1u64 }));
      let tmp_8 = rocq_array::make::<Rc<option<u64>>>(n, Rc::new(option::<u64>::None));
      out_loop_1(dist, n, 0u64, tmp_8)
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
const __rocq_global_253: u64 = 9223372036854775807u64;