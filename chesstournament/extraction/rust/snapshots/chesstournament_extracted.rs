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

// Rocq: Chesstournament.chesstournament_implem.bdec
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

// Rocq: Chesstournament.chesstournament_implem.iota_loop
// Variant: uncurried
pub fn iota_loop_1(n: u64, x: u64, p: Rc<Array<u64>>) -> Rc<Array<u64>> {
  iota_loop(n, x, p, ())
}

// Rocq: Chesstournament.chesstournament_implem.iota_loop (local: iota_loop)
// Variant: uncurried, lifted
pub fn iota_loop(n: u64, x: u64, p: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(x, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(x, 1u64);
      let tmp_2 = rocq_array::set::<u64>(p, x, x);
      iota_loop(n, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.iota
pub fn iota(n: u64) -> Rc<Array<u64>> {
  let tmp = rocq_array::make::<u64>(n, 0u64);
  iota_loop_1(n, 0u64, tmp)
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

// Rocq: Chesstournament.chesstournament_implem.find
// Variant: uncurried
pub fn find_1(p: Rc<Array<u64>>, x: u64) -> (Rc<Array<u64>>, u64) {
  find(p, x, ())
}

// Rocq: Chesstournament.chesstournament_implem.find (local: find)
// Variant: uncurried, lifted
pub fn find(p: Rc<Array<u64>>, x: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let y = rocq_array::get::<u64>(&p, x);
  let tmp = eqb(y, x);
  match bdec(tmp) {
    sumbool::left => {
      (p, x)
    },
    sumbool::right => {
      let f = find(p, y, ());
      let f_clone = Clone::clone(&f);
      let tmp_1 = fst::<Rc<Array<u64>>, u64>(f_clone);
      let f_clone_1 = Clone::clone(&f);
      let tmp_2 = rocq_array::set::<u64>(tmp_1, x, snd::<Rc<Array<u64>>, u64>(f_clone_1));
      (tmp_2, snd::<Rc<Array<u64>>, u64>(f))
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.union
// Variant: uncurried
pub fn union(p: Rc<Array<u64>>, rk: Rc<Array<u64>>, a: u64, b: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  if eqb(a, b) {
    (p, rk)
  } else {
    let ra = rocq_array::get::<u64>(&rk, a);
    let rb = rocq_array::get::<u64>(&rk, b);
    if ltb(ra, rb) {
      let tmp = rocq_array::set::<u64>(p, a, b);
      (tmp, rk)
    } else {
      if ltb(rb, ra) {
        let tmp_1 = rocq_array::set::<u64>(p, b, a);
        (tmp_1, rk)
      } else {
        let tmp_2 = rocq_array::set::<u64>(p, b, a);
        let tmp_3 = rocq_array::set::<u64>(rk, a, add(ra, 1u64));
        (tmp_2, tmp_3)
      }
    }
  }
}

// Rocq: Chesstournament.chesstournament_implem.unite
// Variant: uncurried
pub fn unite(p: Rc<Array<u64>>, rk: Rc<Array<u64>>, k: u64, l: u64) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let f1 = find_1(p, k);
  let f1_clone = Clone::clone(&f1);
  let tmp = fst::<Rc<Array<u64>>, u64>(f1_clone);
  let f2 = find_1(tmp, l);
  let f2_clone = Clone::clone(&f2);
  let tmp_1 = fst::<Rc<Array<u64>>, u64>(f2_clone);
  union(tmp_1, rk, snd::<Rc<Array<u64>>, u64>(f1), snd::<Rc<Array<u64>>, u64>(f2))
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop
// Variant: uncurried
pub fn uf_loop_1(ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, p: Rc<Array<u64>>, rk: Rc<Array<u64>>) -> Rc<Array<u64>> {
  uf_loop(ks, wins, ls, m, j, p, rk, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.uf_loop (local: uf_loop)
// Variant: uncurried, lifted
pub fn uf_loop(ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, p: Rc<Array<u64>>, rk: Rc<Array<u64>>, _Hp: (), _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&wins, j);
      if tmp_1 {
        uf_loop(ks, wins, ls, m, add(j, 1u64), p, rk, (), ())
      } else {
        let tmp_2 = rocq_array::get::<u64>(&ks, j);
        let tmp_3 = rocq_array::get::<u64>(&ls, j);
        let u = unite(p, rk, tmp_2, tmp_3);
        let tmp_4 = add(j, 1u64);
        let u_clone = Clone::clone(&u);
        let tmp_5 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(u_clone);
        let tmp_6 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(u);
        uf_loop(ks, wins, ls, m, tmp_4, tmp_5, tmp_6, (), ())
      }
    },
    sumbool::right => {
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(rk);
      p
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop
// Variant: uncurried
pub fn rep_loop_1(n: u64, x: u64, p: Rc<Array<u64>>, rep: Rc<Array<u64>>) -> Rc<Array<u64>> {
  rep_loop(n, x, p, rep, (), ())
}

// Rocq: Chesstournament.chesstournament_implem.rep_loop (local: rep_loop)
// Variant: uncurried, lifted
pub fn rep_loop(n: u64, x: u64, p: Rc<Array<u64>>, rep: Rc<Array<u64>>, _Hp: (), _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(x, n);
  match bdec(tmp) {
    sumbool::left => {
      let f = find_1(p, x);
      let tmp_1 = add(x, 1u64);
      let f_clone = Clone::clone(&f);
      let tmp_2 = fst::<Rc<Array<u64>>, u64>(f_clone);
      let tmp_3 = rocq_array::set::<u64>(rep, x, snd::<Rc<Array<u64>>, u64>(f));
      rep_loop(n, tmp_1, tmp_2, tmp_3, (), ())
    },
    sumbool::right => {
      std::mem::drop(p);
      rep
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop
// Variant: uncurried
pub fn deg_loop_1(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, od: Rc<Array<u64>>, id: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  deg_loop(rep, ks, wins, ls, m, j, od, id, ())
}

// Rocq: Chesstournament.chesstournament_implem.deg_loop (local: deg_loop)
// Variant: uncurried, lifted
pub fn deg_loop(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, od: Rc<Array<u64>>, id: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&wins, j);
      if tmp_1 {
        let tmp_2 = rocq_array::get::<u64>(&ks, j);
        let a = rocq_array::get::<u64>(&rep, tmp_2);
        let tmp_3 = rocq_array::get::<u64>(&ls, j);
        let b = rocq_array::get::<u64>(&rep, tmp_3);
        let tmp_4 = add(j, 1u64);
        let tmp_5 = rocq_array::get::<u64>(&od, a);
        let tmp_6 = rocq_array::set::<u64>(od, a, add(tmp_5, 1u64));
        let tmp_7 = rocq_array::get::<u64>(&id, b);
        let tmp_8 = rocq_array::set::<u64>(id, b, add(tmp_7, 1u64));
        deg_loop(rep, ks, wins, ls, m, tmp_4, tmp_6, tmp_8, ())
      } else {
        deg_loop(rep, ks, wins, ls, m, add(j, 1u64), od, id, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      (od, id)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop
// Variant: uncurried
pub fn pre_loop_1(od: Rc<Array<u64>>, n: u64, u: u64, s: u64, st: Rc<Array<u64>>, pos: Rc<Array<u64>>) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  pre_loop(od, n, u, s, st, pos, ())
}

// Rocq: Chesstournament.chesstournament_implem.pre_loop (local: pre_loop)
// Variant: uncurried, lifted
pub fn pre_loop(od: Rc<Array<u64>>, n: u64, u: u64, s: u64, st: Rc<Array<u64>>, pos: Rc<Array<u64>>, _H: ()) -> (Rc<Array<u64>>, Rc<Array<u64>>) {
  let tmp = ltb(u, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&od, u);
      let s_ = add(s, tmp_1);
      let tmp_2 = add(u, 1u64);
      let tmp_3 = rocq_array::set::<u64>(st, add(u, 1u64), s_);
      let tmp_4 = rocq_array::set::<u64>(pos, u, s);
      pre_loop(od, n, tmp_2, s_, tmp_3, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(od);
      (st, pos)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop
// Variant: uncurried
pub fn fill_loop_1(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_loop(rep, ks, wins, ls, m, j, pos, adj, ())
}

// Rocq: Chesstournament.chesstournament_implem.fill_loop (local: fill_loop)
// Variant: uncurried, lifted
pub fn fill_loop(rep: Rc<Array<u64>>, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>, m: u64, j: u64, pos: Rc<Array<u64>>, adj: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(j, m);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<bool>(&wins, j);
      if tmp_1 {
        let tmp_2 = rocq_array::get::<u64>(&ks, j);
        let a = rocq_array::get::<u64>(&rep, tmp_2);
        let pa = rocq_array::get::<u64>(&pos, a);
        let tmp_3 = add(j, 1u64);
        let tmp_4 = rocq_array::set::<u64>(pos, a, add(pa, 1u64));
        let tmp_5 = rocq_array::get::<u64>(&ls, j);
        let tmp_6 = rocq_array::get::<u64>(&rep, tmp_5);
        let tmp_7 = rocq_array::set::<u64>(adj, pa, tmp_6);
        fill_loop(rep, ks, wins, ls, m, tmp_3, tmp_4, tmp_7, ())
      } else {
        fill_loop(rep, ks, wins, ls, m, add(j, 1u64), pos, adj, ())
      }
    },
    sumbool::right => {
      std::mem::drop(rep);
      std::mem::drop(ks);
      std::mem::drop(wins);
      std::mem::drop(ls);
      std::mem::drop(pos);
      adj
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.init_loop
// Variant: uncurried
pub fn init_loop_1(id: Rc<Array<u64>>, n: u64, v: u64, q: Rc<Array<u64>>, t: u64) -> (Rc<Array<u64>>, u64) {
  init_loop(id, n, v, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.init_loop (local: init_loop)
// Variant: uncurried, lifted
pub fn init_loop(id: Rc<Array<u64>>, n: u64, v: u64, q: Rc<Array<u64>>, t: u64, _H: ()) -> (Rc<Array<u64>>, u64) {
  let tmp = ltb(v, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = rocq_array::get::<u64>(&id, v);
      if eqb(tmp_1, 0u64) {
        let tmp_2 = add(v, 1u64);
        let tmp_3 = rocq_array::set::<u64>(q, t, v);
        init_loop(id, n, tmp_2, tmp_3, add(t, 1u64), ())
      } else {
        init_loop(id, n, add(v, 1u64), q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(id);
      (q, t)
    },
  }
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.sub
// Variant: uncurried
pub fn sub(v0: u64, v1: u64) -> u64 {
  rocq_int63::sub(v0, v1)
}

// Rocq: Chesstournament.chesstournament_implem.inner
// Variant: uncurried
pub fn inner_1(adj: Rc<Array<u64>>, hi: u64, e: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  inner(adj, hi, e, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.inner (local: inner)
// Variant: uncurried, lifted
pub fn inner(adj: Rc<Array<u64>>, hi: u64, e: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> ((Rc<Array<u64>>, Rc<Array<u64>>), u64) {
  let tmp = ltb(e, hi);
  match bdec(tmp) {
    sumbool::left => {
      let v = rocq_array::get::<u64>(&adj, e);
      let tmp_1 = rocq_array::get::<u64>(&d, v);
      let dv = sub(tmp_1, 1u64);
      if eqb(dv, 0u64) {
        let tmp_2 = add(e, 1u64);
        let tmp_3 = rocq_array::set::<u64>(d, v, dv);
        let tmp_4 = rocq_array::set::<u64>(q, t, v);
        inner(adj, hi, tmp_2, tmp_3, tmp_4, add(t, 1u64), ())
      } else {
        let tmp_5 = add(e, 1u64);
        let tmp_6 = rocq_array::set::<u64>(d, v, dv);
        inner(adj, hi, tmp_5, tmp_6, q, t, ())
      }
    },
    sumbool::right => {
      std::mem::drop(adj);
      ((d, q), t)
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.kahn
// Variant: uncurried
pub fn kahn_1(adj: Rc<Array<u64>>, st: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64) -> u64 {
  kahn(adj, st, h, d, q, t, ())
}

// Rocq: Chesstournament.chesstournament_implem.kahn (local: kahn)
// Variant: uncurried, lifted
pub fn kahn(adj: Rc<Array<u64>>, st: Rc<Array<u64>>, h: u64, d: Rc<Array<u64>>, q: Rc<Array<u64>>, t: u64, _H: ()) -> u64 {
  let tmp = ltb(h, t);
  match bdec(tmp) {
    sumbool::left => {
      let u = rocq_array::get::<u64>(&q, h);
      let tmp_1 = rocq_array::get::<u64>(&st, add(u, 1u64));
      let tmp_2 = rocq_array::get::<u64>(&st, u);
      let adj_clone = Rc::clone(&adj);
      let r = inner_1(adj_clone, tmp_1, tmp_2, d, q, t);
      let tmp_3 = add(h, 1u64);
      let r_clone = Clone::clone(&r);
      let tmp_4 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone));
      let r_clone_1 = Clone::clone(&r);
      let tmp_5 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(fst::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r_clone_1));
      kahn(adj, st, tmp_3, tmp_4, tmp_5, snd::<(Rc<Array<u64>>, Rc<Array<u64>>), u64>(r), ())
    },
    sumbool::right => {
      std::mem::drop(adj);
      std::mem::drop(st);
      std::mem::drop(d);
      std::mem::drop(q);
      t
    },
  }
}

// Rocq: Chesstournament.chesstournament_implem.chess_impl
// Variant: uncurried
pub fn chess_impl(n: u64, ks: Rc<Array<u64>>, wins: Rc<Array<bool>>, ls: Rc<Array<u64>>) -> bool {
  let m = rocq_array::length::<u64>(&ks);
  let p0 = iota(n);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let ks_clone = Rc::clone(&ks);
  let wins_clone = Rc::clone(&wins);
  let ls_clone = Rc::clone(&ls);
  let p1 = uf_loop_1(ks_clone, wins_clone, ls_clone, m, 0u64, p0, tmp);
  let tmp_1 = rocq_array::make::<u64>(n, 0u64);
  let rep = rep_loop_1(n, 0u64, p1, tmp_1);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  let tmp_3 = rocq_array::make::<u64>(n, 0u64);
  let rep_clone = Rc::clone(&rep);
  let ks_clone_1 = Rc::clone(&ks);
  let wins_clone_1 = Rc::clone(&wins);
  let ls_clone_1 = Rc::clone(&ls);
  let dg = deg_loop_1(rep_clone, ks_clone_1, wins_clone_1, ls_clone_1, m, 0u64, tmp_2, tmp_3);
  let dg_clone = Clone::clone(&dg);
  let tmp_4 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(dg_clone);
  let tmp_5 = rocq_array::make::<u64>(add(n, 1u64), 0u64);
  let tmp_6 = rocq_array::make::<u64>(n, 0u64);
  let sp = pre_loop_1(tmp_4, n, 0u64, 0u64, tmp_5, tmp_6);
  let sp_clone = Clone::clone(&sp);
  let tmp_7 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(sp_clone);
  let tmp_8 = rocq_array::make::<u64>(m, 0u64);
  let adj = fill_loop_1(rep, ks, wins, ls, m, 0u64, tmp_7, tmp_8);
  let dg_clone_1 = Clone::clone(&dg);
  let tmp_9 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(dg_clone_1);
  let tmp_10 = rocq_array::make::<u64>(n, 0u64);
  let qi = init_loop_1(tmp_9, n, 0u64, tmp_10, 0u64);
  let tmp_11 = fst::<Rc<Array<u64>>, Rc<Array<u64>>>(sp);
  let tmp_12 = snd::<Rc<Array<u64>>, Rc<Array<u64>>>(dg);
  let qi_clone = Clone::clone(&qi);
  let tmp_13 = fst::<Rc<Array<u64>>, u64>(qi_clone);
  let t = kahn_1(adj, tmp_11, 0u64, tmp_12, tmp_13, snd::<Rc<Array<u64>>, u64>(qi));
  eqb(t, n)
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
