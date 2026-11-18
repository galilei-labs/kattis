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

// Rocq: Basincity.basincity_implem.bdec
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

// Rocq: Basincity.basincity_implem.fill_dg
// Variant: uncurried
pub fn fill_dg_1(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, dg: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_dg(y, n, i, dg, ())
}

// Rocq: Basincity.basincity_implem.fill_dg (local: fill_dg)
// Variant: uncurried, lifted
pub fn fill_dg(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, dg: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let y_clone = Rc::clone(&y);
      let tmp_2 = rocq_array::get::<Rc<Array<u64>>>(&y_clone, i);
      std::mem::drop(y_clone);
      let tmp_3 = rocq_array::length::<u64>(&tmp_2);
      std::mem::drop(tmp_2);
      let tmp_4 = rocq_array::set::<u64>(dg, i, tmp_3);
      fill_dg(y, n, tmp_1, tmp_4, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      dg
    },
  }
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

// Rocq: Basincity.basincity_implem.put_slot
// Variant: uncurried
pub fn put_slot(row: Rc<Array<u64>>, b: u64, j: u64, nb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::length::<u64>(&row);
  if ltb(j, tmp) {
    let tmp_1 = add(b, j);
    let tmp_2 = rocq_array::get::<u64>(&row, j);
    std::mem::drop(row);
    rocq_array::set::<u64>(nb, tmp_1, sub(tmp_2, 1u64))
  } else {
    std::mem::drop(row);
    nb
  }
}

// Rocq: Basincity.basincity_implem.fill_nb
// Variant: uncurried
pub fn fill_nb_1(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, nb: Rc<Array<u64>>) -> Rc<Array<u64>> {
  fill_nb(y, n, i, nb, ())
}

// Rocq: Basincity.basincity_implem.fill_nb (local: fill_nb)
// Variant: uncurried, lifted
pub fn fill_nb(y: Rc<Array<Rc<Array<u64>>>>, n: u64, i: u64, nb: Rc<Array<u64>>, _H: ()) -> Rc<Array<u64>> {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let y_clone = Rc::clone(&y);
      let row = rocq_array::get::<Rc<Array<u64>>>(&y_clone, i);
      std::mem::drop(y_clone);
      let b = mul(4u64, i);
      let tmp_1 = add(i, 1u64);
      let row_clone = Rc::clone(&row);
      let tmp_2 = put_slot(row_clone, b, 0u64, nb);
      let row_clone_1 = Rc::clone(&row);
      let tmp_3 = put_slot(row_clone_1, b, 1u64, tmp_2);
      let row_clone_2 = Rc::clone(&row);
      let tmp_4 = put_slot(row_clone_2, b, 2u64, tmp_3);
      let tmp_5 = put_slot(row, b, 3u64, tmp_4);
      fill_nb(y, n, tmp_1, tmp_5, ())
    },
    sumbool::right => {
      std::mem::drop(y);
      nb
    },
  }
}

// Rocq: Corelib.Init.Datatypes.fst
pub fn fst<A: Clone + 'static, B: 'static>(p: (A, B)) -> A {
  let p_0_clone = Clone::clone(&p.0);
  std::mem::drop(p);
  p_0_clone
}

// Rocq: Corelib.Numbers.Cyclic.Int63.PrimInt63.leb
// Variant: uncurried
pub fn leb(v0: u64, v1: u64) -> bool {
  rocq_int63::leb(v0, v1)
}

// Rocq: Basincity.basincity_implem.alive
// Variant: uncurried
pub fn alive_owned(rm: Rc<Array<u64>>, x: u64) -> bool {
  let tmp = rocq_array::get::<u64>(&rm, x);
  std::mem::drop(rm);
  eqb(tmp, 0u64)
}

// Rocq: Basincity.basincity_implem.alive
// Variant: borrowed, uncurried
pub fn alive(rm: &Rc<Array<u64>>, x: u64) -> bool {
  let x_1 = x;
  eqb(rocq_array::get::<u64>(rm, x_1), 0u64)
}

// Rocq: Basincity.basincity_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(n: u64, rm: Rc<Array<u64>>, i: u64, acc: u64) -> u64 {
  cnt_loop(n, rm, i, acc, ())
}

// Rocq: Basincity.basincity_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(n: u64, rm: Rc<Array<u64>>, i: u64, acc: u64, _H: ()) -> u64 {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = add(i, 1u64);
      let rm_clone = Rc::clone(&rm);
      let tmp_2 = if alive_owned(rm_clone, i) {
        add(acc, 1u64)
      } else {
        acc
      };
      cnt_loop(n, rm, tmp_1, tmp_2, ())
    },
    sumbool::right => {
      std::mem::drop(rm);
      acc
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

// Rocq: Corelib.Init.Datatypes.orb
// Variant: uncurried
pub fn orb(b1: bool, b2: bool) -> bool {
  if b1 {
    true
  } else {
    b2
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

// Rocq: Basincity.basincity_implem.forall4
// Variant: uncurried
pub fn forall4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> bool {
  let tmp = negb(ltb(0u64, d));
  let f_ref: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_1 = f_ref(0u64);
  let tmp_2 = orb(tmp, tmp_1);
  let tmp_3 = negb(ltb(1u64, d));
  let f_ref_1: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_4 = f_ref_1(1u64);
  let tmp_5 = andb(tmp_2, orb(tmp_3, tmp_4));
  let tmp_6 = negb(ltb(2u64, d));
  let f_ref_2: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_7 = f_ref_2(2u64);
  let tmp_8 = andb(tmp_5, orb(tmp_6, tmp_7));
  let tmp_9 = negb(ltb(3u64, d));
  let f_ref_3: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_10 = f_ref_3(3u64);
  std::mem::drop(f);
  andb(tmp_8, orb(tmp_9, tmp_10))
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: uncurried
pub fn nbr_owned(nb: Rc<Array<u64>>, v: u64, j: u64) -> u64 {
  let tmp = rocq_array::get::<u64>(&nb, add(mul(4u64, v), j));
  std::mem::drop(nb);
  tmp
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: borrowed, uncurried
pub fn nbr(nb: &Rc<Array<u64>>, v: u64, j: u64) -> u64 {
  let v_1 = v;
  let j_1 = j;
  rocq_array::get::<u64>(nb, add(mul(4u64, v_1), j_1))
}

// Rocq: Basincity.basincity_implem.exists4
// Variant: uncurried
pub fn exists4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> bool {
  let tmp = ltb(0u64, d);
  let f_ref: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_1 = f_ref(0u64);
  let tmp_2 = andb(tmp, tmp_1);
  let tmp_3 = ltb(1u64, d);
  let f_ref_1: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_4 = f_ref_1(1u64);
  let tmp_5 = orb(tmp_2, andb(tmp_3, tmp_4));
  let tmp_6 = ltb(2u64, d);
  let f_ref_2: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_7 = f_ref_2(2u64);
  let tmp_8 = orb(tmp_5, andb(tmp_6, tmp_7));
  let tmp_9 = ltb(3u64, d);
  let f_ref_3: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_10 = f_ref_3(3u64);
  std::mem::drop(f);
  orb(tmp_8, andb(tmp_9, tmp_10))
}

// Rocq: Basincity.basincity_implem.adjb
// Variant: borrowed, uncurried
pub fn adjb(nb: &Rc<Array<u64>>, dg: &Rc<Array<u64>>, a: u64, x: u64) -> bool {
  let nb_clone = Rc::clone(nb);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_17 = a;
    move |j: u64| -> bool {
      let nb = &nb_clone;
      let a = &__anf_capture_17;
      let x = &x;
      let tmp = nbr(nb, Clone::clone(a), j);
      let x_clone = Clone::clone(x);
      eqb(x_clone, tmp)
    }
  });
  exists4(callback, rocq_array::get::<u64>(dg, a))
}

// Rocq: Basincity.basincity_implem.simp
// Variant: uncurried
pub fn simp(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, v: u64) -> bool {
  let d = rocq_array::get::<u64>(&dg, v);
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_22 = v;
    let __anf_capture_26 = dg;
    let __anf_capture_28 = d;
    move |j1: u64| -> bool {
      let rm = &rm;
      let v = &__anf_capture_22;
      let nb = &nb;
      let dg = &__anf_capture_26;
      let d = &__anf_capture_28;
      let rm_clone = Rc::clone(rm);
      let v_clone = Clone::clone(v);
      let nb_clone = Rc::clone(nb);
      let dg_clone = Rc::clone(dg);
      let callback_1: Rc<dyn Fn(u64) -> bool> = Rc::new({
        move |j2: u64| -> bool {
          let rm = &rm_clone;
          let j1 = &j1;
          let v = &v_clone;
          let nb = &nb_clone;
          let dg = &dg_clone;
          let tmp = orb(leb(j2, Clone::clone(j1)), negb(alive(rm, nbr(nb, Clone::clone(v), Clone::clone(j1)))));
          let tmp_1 = orb(tmp, negb(alive(rm, nbr(nb, Clone::clone(v), j2))));
          let tmp_2 = nbr(nb, Clone::clone(v), Clone::clone(j1));
          let v_clone_1 = Clone::clone(v);
          let tmp_3 = nb;
          let tmp_4 = adjb(nb, dg, tmp_2, nbr(tmp_3, v_clone_1, j2));
          orb(tmp_1, tmp_4)
        }
      });
      let d_clone = Clone::clone(d);
      forall4(callback_1, d_clone)
    }
  });
  forall4(callback, d)
}

// Rocq: Basincity.basincity_implem.b2i
pub fn b2i(b: bool) -> u64 {
  if b {
    1u64
  } else {
    0u64
  }
}

// Rocq: Basincity.basincity_implem.count4
// Variant: uncurried
pub fn count4(f: Rc<dyn Fn(u64) -> bool>, d: u64) -> u64 {
  let tmp = ltb(0u64, d);
  let f_ref: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_1 = f_ref(0u64);
  let tmp_2 = b2i(andb(tmp, tmp_1));
  let tmp_3 = ltb(1u64, d);
  let f_ref_1: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_4 = f_ref_1(1u64);
  let tmp_5 = add(tmp_2, b2i(andb(tmp_3, tmp_4)));
  let tmp_6 = ltb(2u64, d);
  let f_ref_2: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_7 = f_ref_2(2u64);
  let tmp_8 = add(tmp_5, b2i(andb(tmp_6, tmp_7)));
  let tmp_9 = ltb(3u64, d);
  let f_ref_3: &Rc<dyn Fn(u64) -> bool> = &f;
  let tmp_10 = f_ref_3(3u64);
  std::mem::drop(f);
  add(tmp_8, b2i(andb(tmp_9, tmp_10)))
}

// Rocq: Basincity.basincity_implem.deg
// Variant: uncurried
pub fn deg(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, v: u64) -> u64 {
  let callback: Rc<dyn Fn(u64) -> bool> = Rc::new({
    let __anf_capture_14 = v;
    move |j: u64| -> bool {
      let nb = &nb;
      let v = &__anf_capture_14;
      let rm = &rm;
      let tmp = nbr(nb, Clone::clone(v), j);
      alive(rm, tmp)
    }
  });
  let tmp_1 = rocq_array::get::<u64>(&dg, v);
  std::mem::drop(dg);
  count4(callback, tmp_1)
}

// Rocq: Basincity.basincity_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, i: u64, best: u64, bd: u64) -> (u64, bool) {
  sel_loop(n, nb, dg, rm, i, best, bd, ())
}

// Rocq: Basincity.basincity_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rm: Rc<Array<u64>>, i: u64, best: u64, bd: u64, _H: ()) -> (u64, bool) {
  let tmp = ltb(i, n);
  match bdec(tmp) {
    sumbool::left => {
      let rm_clone = Rc::clone(&rm);
      if alive_owned(rm_clone, i) {
        let nb_clone = Rc::clone(&nb);
        let dg_clone = Rc::clone(&dg);
        let rm_clone_1 = Rc::clone(&rm);
        if simp(nb_clone, dg_clone, rm_clone_1, i) {
          std::mem::drop(nb);
          std::mem::drop(dg);
          std::mem::drop(rm);
          (i, true)
        } else {
          let nb_clone_1 = Rc::clone(&nb);
          let dg_clone_1 = Rc::clone(&dg);
          let rm_clone_2 = Rc::clone(&rm);
          let d = deg(nb_clone_1, dg_clone_1, rm_clone_2, i);
          if ltb(d, bd) {
            sel_loop(n, nb, dg, rm, add(i, 1u64), i, d, ())
          } else {
            sel_loop(n, nb, dg, rm, add(i, 1u64), best, bd, ())
          }
        }
      } else {
        sel_loop(n, nb, dg, rm, add(i, 1u64), best, bd, ())
      }
    },
    sumbool::right => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      std::mem::drop(rm);
      (best, false)
    },
  }
}

// Rocq: Basincity.basincity_implem.mark1
// Variant: uncurried
pub fn mark1(w: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&rm, w);
  if eqb(tmp, 0u64) {
    rocq_array::set::<u64>(rm, w, k)
  } else {
    rm
  }
}

// Rocq: Basincity.basincity_implem.mark
// Variant: uncurried
pub fn mark(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, u: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let d = rocq_array::get::<u64>(&dg, u);
  let rm_1 = mark1(u, k, rm);
  let tmp = 0u64;
  let rm_2 = if ltb(tmp, d) {
    let nb_clone = Rc::clone(&nb);
    mark1(nbr_owned(nb_clone, u, 0u64), k, rm_1)
  } else {
    rm_1
  };
  let tmp_1 = 1u64;
  let rm_3 = if ltb(tmp_1, d) {
    let nb_clone_1 = Rc::clone(&nb);
    mark1(nbr_owned(nb_clone_1, u, 1u64), k, rm_2)
  } else {
    rm_2
  };
  let tmp_2 = 2u64;
  let rm_4 = if ltb(tmp_2, d) {
    let nb_clone_2 = Rc::clone(&nb);
    mark1(nbr_owned(nb_clone_2, u, 2u64), k, rm_3)
  } else {
    rm_3
  };
  if ltb(3u64, d) {
    std::mem::drop(dg);
    mark1(nbr_owned(nb, u, 3u64), k, rm_4)
  } else {
    std::mem::drop(nb);
    std::mem::drop(dg);
    rm_4
  }
}

// Rocq: Basincity.basincity_implem.unmark1
// Variant: uncurried
pub fn unmark1(w: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let tmp = rocq_array::get::<u64>(&rm, w);
  if eqb(tmp, k) {
    rocq_array::set::<u64>(rm, w, 0u64)
  } else {
    rm
  }
}

// Rocq: Basincity.basincity_implem.unmark
// Variant: uncurried
pub fn unmark(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, u: u64, k: u64, rm: Rc<Array<u64>>) -> Rc<Array<u64>> {
  let d = rocq_array::get::<u64>(&dg, u);
  let rm_1 = unmark1(u, k, rm);
  let tmp = 0u64;
  let rm_2 = if ltb(tmp, d) {
    let nb_clone = Rc::clone(&nb);
    unmark1(nbr_owned(nb_clone, u, 0u64), k, rm_1)
  } else {
    rm_1
  };
  let tmp_1 = 1u64;
  let rm_3 = if ltb(tmp_1, d) {
    let nb_clone_1 = Rc::clone(&nb);
    unmark1(nbr_owned(nb_clone_1, u, 1u64), k, rm_2)
  } else {
    rm_2
  };
  let tmp_2 = 2u64;
  let rm_4 = if ltb(tmp_2, d) {
    let nb_clone_2 = Rc::clone(&nb);
    unmark1(nbr_owned(nb_clone_2, u, 2u64), k, rm_3)
  } else {
    rm_3
  };
  if ltb(3u64, d) {
    std::mem::drop(dg);
    unmark1(nbr_owned(nb, u, 3u64), k, rm_4)
  } else {
    std::mem::drop(nb);
    std::mem::drop(dg);
    rm_4
  }
}

// Rocq: Basincity.basincity_implem.child
// Variant: uncurried
pub fn child(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, u: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  let nb_clone = Rc::clone(&nb);
  let dg_clone = Rc::clone(&dg);
  let rm1 = mark(nb_clone, dg_clone, u, k, rm);
  let rec_ref: &Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = &rec;
  let tmp = rec_ref(rm1);
  std::mem::drop(rec);
  match tmp {
    (v25, v27) => {
      let tmp_1 = unmark(nb, dg, u, k, v27);
      (v25, tmp_1)
    },
  }
}

// Rocq: Basincity.basincity_implem.try_slot
// Variant: uncurried
pub fn try_slot(nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, v: u64, j: u64, r: (bool, Rc<Array<u64>>)) -> (bool, Rc<Array<u64>>) {
  match r {
    (v8, v10) => {
      let b = &v10;
      if v8 {
        std::mem::drop(nb);
        std::mem::drop(dg);
        std::mem::drop(rec);
        (true, v10)
      } else {
        let tmp = rocq_array::get::<u64>(&dg, v);
        if ltb(j, tmp) {
          let nb_clone = Rc::clone(&nb);
          let u = nbr_owned(nb_clone, v, j);
          let b_clone = Rc::clone(b);
          if alive_owned(b_clone, u) {
            child(nb, dg, rec, k, u, v10)
          } else {
            std::mem::drop(nb);
            std::mem::drop(rec);
            std::mem::drop(dg);
            (false, v10)
          }
        } else {
          std::mem::drop(nb);
          std::mem::drop(rec);
          std::mem::drop(dg);
          (false, v10)
        }
      }
    },
  }
}

// Rocq: Basincity.basincity_implem.node
// Variant: uncurried
pub fn node(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, rec: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)>, k: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  let tmp = mul(5u64, k);
  let rm_clone = Rc::clone(&rm);
  let tmp_1 = cnt_loop_1(n, rm_clone, 0u64, 0u64);
  if leb(tmp, tmp_1) {
    std::mem::drop(nb);
    std::mem::drop(dg);
    std::mem::drop(rec);
    (true, rm)
  } else {
    let nb_clone = Rc::clone(&nb);
    let dg_clone = Rc::clone(&dg);
    let rm_clone_1 = Rc::clone(&rm);
    let tmp_2 = sel_loop_1(n, nb_clone, dg_clone, rm_clone_1, 0u64, n, 5u64);
    match tmp_2 {
      (v70, v72) => {
        if v72 {
          child(nb, dg, rec, k, v70, rm)
        } else {
          if ltb(v70, n) {
            let nb_clone_1 = Rc::clone(&nb);
            let dg_clone_1 = Rc::clone(&dg);
            let rec_clone: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
            let tmp_3 = child(nb_clone_1, dg_clone_1, rec_clone, k, v70, rm);
            let nb_clone_2 = Rc::clone(&nb);
            let dg_clone_2 = Rc::clone(&dg);
            let rec_clone_1: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
            let tmp_4 = try_slot(nb_clone_2, dg_clone_2, rec_clone_1, k, v70, 0u64, tmp_3);
            let nb_clone_3 = Rc::clone(&nb);
            let dg_clone_3 = Rc::clone(&dg);
            let rec_clone_2: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
            let tmp_5 = try_slot(nb_clone_3, dg_clone_3, rec_clone_2, k, v70, 1u64, tmp_4);
            let nb_clone_4 = Rc::clone(&nb);
            let dg_clone_4 = Rc::clone(&dg);
            let rec_clone_3: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::clone(&rec);
            let tmp_6 = try_slot(nb_clone_4, dg_clone_4, rec_clone_3, k, v70, 2u64, tmp_5);
            try_slot(nb, dg, rec, k, v70, 3u64, tmp_6)
          } else {
            std::mem::drop(nb);
            std::mem::drop(dg);
            std::mem::drop(rec);
            (false, rm)
          }
        }
      },
    }
  }
}

// Rocq: Basincity.basincity_implem.search
// Variant: uncurried
pub fn search_1(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, k: u64, rm: Rc<Array<u64>>) -> (bool, Rc<Array<u64>>) {
  search(n, nb, dg, k, rm, ())
}

// Rocq: Basincity.basincity_implem.search (local: search)
// Variant: uncurried, lifted
pub fn search(n: u64, nb: Rc<Array<u64>>, dg: Rc<Array<u64>>, k: u64, rm: Rc<Array<u64>>, _H: ()) -> (bool, Rc<Array<u64>>) {
  let tmp = eqb(k, 0u64);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      (true, rm)
    },
    sumbool::right => {
      let nb_clone = Rc::clone(&nb);
      let dg_clone = Rc::clone(&dg);
      let callback: Rc<dyn Fn(Rc<Array<u64>>) -> (bool, Rc<Array<u64>>)> = Rc::new({
        let __anf_capture_41 = k;
        let __anf_capture_43 = n;
        move |rm_: Rc<Array<u64>>| -> (bool, Rc<Array<u64>>) {
          let tmp_1 = 1u64;
          let tmp_2 = sub(Clone::clone(&__anf_capture_41), tmp_1);
          let tmp_3 = Clone::clone(&__anf_capture_43);
          let tmp_4 = Rc::clone(&nb_clone);
          let tmp_5 = Rc::clone(&dg_clone);
          search(tmp_3, tmp_4, tmp_5, tmp_2, rm_, ())
        }
      });
      node(n, nb, dg, callback, k, rm)
    },
  }
}

// Rocq: Basincity.basincity_implem.basincity_impl
// Variant: uncurried
pub fn basincity_impl(k: u64, y: Rc<Array<Rc<Array<u64>>>>) -> bool {
  let n = rocq_array::length::<Rc<Array<u64>>>(&y);
  let tmp = rocq_array::make::<u64>(n, 0u64);
  let y_clone = Rc::clone(&y);
  let dg = fill_dg_1(y_clone, n, 0u64, tmp);
  let tmp_1 = rocq_array::make::<u64>(mul(4u64, n), 0u64);
  let nb = fill_nb_1(y, n, 0u64, tmp_1);
  let tmp_2 = rocq_array::make::<u64>(n, 0u64);
  fst::<bool, Rc<Array<u64>>>(search_1(n, nb, dg, k, tmp_2))
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
