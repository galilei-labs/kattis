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

// Rocq: Basincity.basincity_implem.bdec
pub fn bdec(b_1: bool) -> sumbool {
  if b_1 {
    sumbool::left
  } else {
    sumbool::right
  }
}

// Rocq: Basincity.basincity_implem.fill_dg
// Variant: uncurried
pub fn fill_dg_1(y: Array<Array<Int63>>, n: Int63, i: Int63, dg: Array<Int63>) -> Array<Int63> {
  fill_dg(y, n, i, dg, ())
}

// Rocq: Basincity.basincity_implem.fill_dg (local: fill_dg)
// Variant: uncurried, lifted
pub fn fill_dg(y: Array<Array<Int63>>, n: Int63, i: Int63, dg: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let y_clone = Clone::clone(&y);
      let tmp_2 = &y_clone;
      let tmp_3 = tmp_2.get_cloned(i);
      std::mem::drop(y_clone);
      let tmp_4 = tmp_3.length();
      std::mem::drop(tmp_3);
      fill_dg(y, n, tmp_1, dg.set(i, tmp_4), ())
    },
    sumbool::right => {
      std::mem::drop(y);
      dg
    },
  }
}

// Rocq: Basincity.basincity_implem.put_slot
// Variant: uncurried
pub fn put_slot(row: Array<Int63>, b_1: Int63, j: Int63, nb: Array<Int63>) -> Array<Int63> {
  let tmp = row.length();
  if j < tmp {
    let tmp_1 = b_1 + j;
    let tmp_2 = row.get_cloned(j);
    std::mem::drop(row);
    nb.set(tmp_1, tmp_2 - int63!(1))
  } else {
    std::mem::drop(row);
    nb
  }
}

// Rocq: Basincity.basincity_implem.fill_nb
// Variant: uncurried
pub fn fill_nb_1(y: Array<Array<Int63>>, n: Int63, i: Int63, nb: Array<Int63>) -> Array<Int63> {
  fill_nb(y, n, i, nb, ())
}

// Rocq: Basincity.basincity_implem.fill_nb (local: fill_nb)
// Variant: uncurried, lifted
pub fn fill_nb(y: Array<Array<Int63>>, n: Int63, i: Int63, nb: Array<Int63>, _H: ()) -> Array<Int63> {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let y_clone = Clone::clone(&y);
      let tmp_1 = &y_clone;
      let row = tmp_1.get_cloned(i);
      std::mem::drop(y_clone);
      let b_1 = int63!(4) * i;
      let tmp_2 = i + int63!(1);
      let row_clone = Clone::clone(&row);
      let tmp_3 = put_slot(row_clone, b_1, int63!(0), nb);
      let row_clone_1 = Clone::clone(&row);
      let tmp_4 = put_slot(row_clone_1, b_1, int63!(1), tmp_3);
      let row_clone_2 = Clone::clone(&row);
      let tmp_5 = put_slot(row_clone_2, b_1, int63!(2), tmp_4);
      fill_nb(y, n, tmp_2, put_slot(row, b_1, int63!(3), tmp_5), ())
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

// Rocq: Basincity.basincity_implem.alive
// Variant: uncurried
pub fn alive_owned(rm: Array<Int63>, x: Int63) -> bool {
  let tmp = rm.get_cloned(x);
  std::mem::drop(rm);
  tmp == int63!(0)
}

// Rocq: Basincity.basincity_implem.alive
// Variant: borrowed, uncurried
pub fn alive(rm: &Array<Int63>, x: Int63) -> bool {
  let x_1 = x;
  rm.get_cloned(x_1) == int63!(0)
}

// Rocq: Basincity.basincity_implem.cnt_loop
// Variant: uncurried
pub fn cnt_loop_1(n: Int63, rm: Array<Int63>, i: Int63, acc: Int63) -> Int63 {
  cnt_loop(n, rm, i, acc, ())
}

// Rocq: Basincity.basincity_implem.cnt_loop (local: cnt_loop)
// Variant: uncurried, lifted
pub fn cnt_loop(n: Int63, rm: Array<Int63>, i: Int63, acc: Int63, _H: ()) -> Int63 {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let tmp_1 = i + int63!(1);
      let rm_clone = Clone::clone(&rm);
      let tmp_2 = if alive_owned(rm_clone, i) {
        acc + int63!(1)
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
pub fn negb(b_1: bool) -> bool {
  if b_1 {
    false
  } else {
    true
  }
}

// Rocq: Basincity.basincity_implem.forall4
// Variant: uncurried
pub fn forall4(f: Rc<dyn Fn(Int63) -> bool>, d: Int63) -> bool {
  let tmp = negb(int63!(0) < d);
  let f_ref: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_1 = f_ref(int63!(0));
  let tmp_2 = orb(tmp, tmp_1);
  let tmp_3 = negb(int63!(1) < d);
  let f_ref_1: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_4 = f_ref_1(int63!(1));
  let tmp_5 = andb(tmp_2, orb(tmp_3, tmp_4));
  let tmp_6 = negb(int63!(2) < d);
  let f_ref_2: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_7 = f_ref_2(int63!(2));
  let tmp_8 = andb(tmp_5, orb(tmp_6, tmp_7));
  let tmp_9 = negb(int63!(3) < d);
  let f_ref_3: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_10 = f_ref_3(int63!(3));
  std::mem::drop(f);
  andb(tmp_8, orb(tmp_9, tmp_10))
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: uncurried
pub fn nbr_owned(nb: Array<Int63>, v: Int63, j: Int63) -> Int63 {
  let tmp = nb.get_cloned(int63!(4) * v + j);
  std::mem::drop(nb);
  tmp
}

// Rocq: Basincity.basincity_implem.nbr
// Variant: borrowed, uncurried
pub fn nbr(nb: &Array<Int63>, v: Int63, j: Int63) -> Int63 {
  let v_1 = v;
  let j_1 = j;
  nb.get_cloned(int63!(4) * v_1 + j_1)
}

// Rocq: Basincity.basincity_implem.exists4
// Variant: uncurried
pub fn exists4(f: Rc<dyn Fn(Int63) -> bool>, d: Int63) -> bool {
  let tmp = int63!(0) < d;
  let f_ref: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_1 = f_ref(int63!(0));
  let tmp_2 = andb(tmp, tmp_1);
  let tmp_3 = int63!(1) < d;
  let f_ref_1: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_4 = f_ref_1(int63!(1));
  let tmp_5 = orb(tmp_2, andb(tmp_3, tmp_4));
  let tmp_6 = int63!(2) < d;
  let f_ref_2: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_7 = f_ref_2(int63!(2));
  let tmp_8 = orb(tmp_5, andb(tmp_6, tmp_7));
  let tmp_9 = int63!(3) < d;
  let f_ref_3: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_10 = f_ref_3(int63!(3));
  std::mem::drop(f);
  orb(tmp_8, andb(tmp_9, tmp_10))
}

// Rocq: Basincity.basincity_implem.adjb
// Variant: borrowed, uncurried
pub fn adjb(nb: &Array<Int63>, dg: &Array<Int63>, a_1: Int63, x: Int63) -> bool {
  let nb_clone = Clone::clone(nb);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_17 = a_1;
    move |j: Int63| -> bool {
      let nb = &nb_clone;
      let a_1 = &__anf_capture_17;
      let x = &x;
      let tmp = nbr(nb, Clone::clone(a_1), j);
      let x_clone = Clone::clone(x);
      x_clone == tmp
    }
  });
  exists4(callback, dg.get_cloned(a_1))
}

// Rocq: Basincity.basincity_implem.simp
// Variant: uncurried
pub fn simp(nb: Array<Int63>, dg: Array<Int63>, rm: Array<Int63>, v: Int63) -> bool {
  let d = dg.get_cloned(v);
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_22 = v;
    let __anf_capture_26 = dg;
    let __anf_capture_28 = d;
    move |j1: Int63| -> bool {
      let rm = &rm;
      let v = &__anf_capture_22;
      let nb = &nb;
      let dg = &__anf_capture_26;
      let d = &__anf_capture_28;
      let rm_clone = Clone::clone(rm);
      let v_clone = Clone::clone(v);
      let nb_clone = Clone::clone(nb);
      let dg_clone = Clone::clone(dg);
      let callback_1: Rc<dyn Fn(Int63) -> bool> = Rc::new({
        move |j2: Int63| -> bool {
          let rm = &rm_clone;
          let j1 = &j1;
          let v = &v_clone;
          let nb = &nb_clone;
          let dg = &dg_clone;
          let tmp = orb(j2 <= Clone::clone(j1), negb(alive(rm, nbr(nb, Clone::clone(v), Clone::clone(j1)))));
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
pub fn b2i(b_1: bool) -> Int63 {
  if b_1 {
    int63!(1)
  } else {
    int63!(0)
  }
}

// Rocq: Basincity.basincity_implem.count4
// Variant: uncurried
pub fn count4(f: Rc<dyn Fn(Int63) -> bool>, d: Int63) -> Int63 {
  let tmp = int63!(0) < d;
  let f_ref: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_1 = f_ref(int63!(0));
  let tmp_2 = b2i(andb(tmp, tmp_1));
  let tmp_3 = int63!(1) < d;
  let f_ref_1: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_4 = f_ref_1(int63!(1));
  let tmp_5 = tmp_2 + b2i(andb(tmp_3, tmp_4));
  let tmp_6 = int63!(2) < d;
  let f_ref_2: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_7 = f_ref_2(int63!(2));
  let tmp_8 = tmp_5 + b2i(andb(tmp_6, tmp_7));
  let tmp_9 = int63!(3) < d;
  let f_ref_3: &Rc<dyn Fn(Int63) -> bool> = &f;
  let tmp_10 = f_ref_3(int63!(3));
  std::mem::drop(f);
  tmp_8 + b2i(andb(tmp_9, tmp_10))
}

// Rocq: Basincity.basincity_implem.deg
// Variant: uncurried
pub fn deg(nb: Array<Int63>, dg: Array<Int63>, rm: Array<Int63>, v: Int63) -> Int63 {
  let callback: Rc<dyn Fn(Int63) -> bool> = Rc::new({
    let __anf_capture_14 = v;
    move |j: Int63| -> bool {
      let nb = &nb;
      let v = &__anf_capture_14;
      let rm = &rm;
      let tmp = nbr(nb, Clone::clone(v), j);
      alive(rm, tmp)
    }
  });
  let tmp_1 = dg.get_cloned(v);
  std::mem::drop(dg);
  count4(callback, tmp_1)
}

// Rocq: Basincity.basincity_implem.sel_loop
// Variant: uncurried
pub fn sel_loop_1(n: Int63, nb: Array<Int63>, dg: Array<Int63>, rm: Array<Int63>, i: Int63, best: Int63, bd: Int63) -> (Int63, bool) {
  sel_loop(n, nb, dg, rm, i, best, bd, ())
}

// Rocq: Basincity.basincity_implem.sel_loop (local: sel_loop)
// Variant: uncurried, lifted
pub fn sel_loop(n: Int63, nb: Array<Int63>, dg: Array<Int63>, rm: Array<Int63>, i: Int63, best: Int63, bd: Int63, _H: ()) -> (Int63, bool) {
  let tmp = i < n;
  match bdec(tmp) {
    sumbool::left => {
      let rm_clone = Clone::clone(&rm);
      if alive_owned(rm_clone, i) {
        let nb_clone = Clone::clone(&nb);
        let dg_clone = Clone::clone(&dg);
        let rm_clone_1 = Clone::clone(&rm);
        if simp(nb_clone, dg_clone, rm_clone_1, i) {
          std::mem::drop(nb);
          std::mem::drop(dg);
          std::mem::drop(rm);
          (i, true)
        } else {
          let nb_clone_1 = Clone::clone(&nb);
          let dg_clone_1 = Clone::clone(&dg);
          let rm_clone_2 = Clone::clone(&rm);
          let d = deg(nb_clone_1, dg_clone_1, rm_clone_2, i);
          if d < bd {
            sel_loop(n, nb, dg, rm, i + int63!(1), i, d, ())
          } else {
            sel_loop(n, nb, dg, rm, i + int63!(1), best, bd, ())
          }
        }
      } else {
        sel_loop(n, nb, dg, rm, i + int63!(1), best, bd, ())
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
pub fn mark1(w: Int63, k: Int63, rm: Array<Int63>) -> Array<Int63> {
  let tmp = rm.get_cloned(w);
  if tmp == int63!(0) {
    rm.set(w, k)
  } else {
    rm
  }
}

// Rocq: Basincity.basincity_implem.mark
// Variant: uncurried
pub fn mark(nb: Array<Int63>, dg: Array<Int63>, u: Int63, k: Int63, rm: Array<Int63>) -> Array<Int63> {
  let d = dg.get_cloned(u);
  let rm_1 = mark1(u, k, rm);
  let tmp = int63!(0);
  let rm_2 = if tmp < d {
    let nb_clone = Clone::clone(&nb);
    mark1(nbr_owned(nb_clone, u, int63!(0)), k, rm_1)
  } else {
    rm_1
  };
  let tmp_1 = int63!(1);
  let rm_3 = if tmp_1 < d {
    let nb_clone_1 = Clone::clone(&nb);
    mark1(nbr_owned(nb_clone_1, u, int63!(1)), k, rm_2)
  } else {
    rm_2
  };
  let tmp_2 = int63!(2);
  let rm_4 = if tmp_2 < d {
    let nb_clone_2 = Clone::clone(&nb);
    mark1(nbr_owned(nb_clone_2, u, int63!(2)), k, rm_3)
  } else {
    rm_3
  };
  if int63!(3) < d {
    std::mem::drop(dg);
    mark1(nbr_owned(nb, u, int63!(3)), k, rm_4)
  } else {
    std::mem::drop(nb);
    std::mem::drop(dg);
    rm_4
  }
}

// Rocq: Basincity.basincity_implem.unmark1
// Variant: uncurried
pub fn unmark1(w: Int63, k: Int63, rm: Array<Int63>) -> Array<Int63> {
  let tmp = rm.get_cloned(w);
  if tmp == k {
    rm.set(w, int63!(0))
  } else {
    rm
  }
}

// Rocq: Basincity.basincity_implem.unmark
// Variant: uncurried
pub fn unmark(nb: Array<Int63>, dg: Array<Int63>, u: Int63, k: Int63, rm: Array<Int63>) -> Array<Int63> {
  let d = dg.get_cloned(u);
  let rm_1 = unmark1(u, k, rm);
  let tmp = int63!(0);
  let rm_2 = if tmp < d {
    let nb_clone = Clone::clone(&nb);
    unmark1(nbr_owned(nb_clone, u, int63!(0)), k, rm_1)
  } else {
    rm_1
  };
  let tmp_1 = int63!(1);
  let rm_3 = if tmp_1 < d {
    let nb_clone_1 = Clone::clone(&nb);
    unmark1(nbr_owned(nb_clone_1, u, int63!(1)), k, rm_2)
  } else {
    rm_2
  };
  let tmp_2 = int63!(2);
  let rm_4 = if tmp_2 < d {
    let nb_clone_2 = Clone::clone(&nb);
    unmark1(nbr_owned(nb_clone_2, u, int63!(2)), k, rm_3)
  } else {
    rm_3
  };
  if int63!(3) < d {
    std::mem::drop(dg);
    unmark1(nbr_owned(nb, u, int63!(3)), k, rm_4)
  } else {
    std::mem::drop(nb);
    std::mem::drop(dg);
    rm_4
  }
}

// Rocq: Basincity.basincity_implem.child
// Variant: uncurried
pub fn child(nb: Array<Int63>, dg: Array<Int63>, rec: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)>, k: Int63, u: Int63, rm: Array<Int63>) -> (bool, Array<Int63>) {
  let nb_clone = Clone::clone(&nb);
  let dg_clone = Clone::clone(&dg);
  let rm1 = mark(nb_clone, dg_clone, u, k, rm);
  let rec_ref: &Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = &rec;
  let tmp = rec_ref(rm1);
  std::mem::drop(rec);
  match tmp {
    (v25, v27) => {
      (v25, unmark(nb, dg, u, k, v27))
    },
  }
}

// Rocq: Basincity.basincity_implem.try_slot
// Variant: uncurried
pub fn try_slot(nb: Array<Int63>, dg: Array<Int63>, rec: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)>, k: Int63, v: Int63, j: Int63, r: (bool, Array<Int63>)) -> (bool, Array<Int63>) {
  match r {
    (v8, v10) => {
      let b_1 = &v10;
      if v8 {
        std::mem::drop(nb);
        std::mem::drop(dg);
        std::mem::drop(rec);
        (true, v10)
      } else {
        let tmp = dg.get_cloned(v);
        if j < tmp {
          let nb_clone = Clone::clone(&nb);
          let u = nbr_owned(nb_clone, v, j);
          let b_clone = Clone::clone(b_1);
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
pub fn node(n: Int63, nb: Array<Int63>, dg: Array<Int63>, rec: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)>, k: Int63, rm: Array<Int63>) -> (bool, Array<Int63>) {
  let tmp = int63!(5) * k;
  let rm_clone = Clone::clone(&rm);
  let tmp_1 = cnt_loop_1(n, rm_clone, int63!(0), int63!(0));
  if tmp <= tmp_1 {
    std::mem::drop(nb);
    std::mem::drop(dg);
    std::mem::drop(rec);
    (true, rm)
  } else {
    let nb_clone = Clone::clone(&nb);
    let dg_clone = Clone::clone(&dg);
    let rm_clone_1 = Clone::clone(&rm);
    let tmp_2 = sel_loop_1(n, nb_clone, dg_clone, rm_clone_1, int63!(0), n, int63!(5));
    match tmp_2 {
      (v70, v72) => {
        if v72 {
          child(nb, dg, rec, k, v70, rm)
        } else {
          if v70 < n {
            let nb_clone_1 = Clone::clone(&nb);
            let dg_clone_1 = Clone::clone(&dg);
            let rec_clone: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = Rc::clone(&rec);
            let tmp_3 = child(nb_clone_1, dg_clone_1, rec_clone, k, v70, rm);
            let nb_clone_2 = Clone::clone(&nb);
            let dg_clone_2 = Clone::clone(&dg);
            let rec_clone_1: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = Rc::clone(&rec);
            let tmp_4 = try_slot(nb_clone_2, dg_clone_2, rec_clone_1, k, v70, int63!(0), tmp_3);
            let nb_clone_3 = Clone::clone(&nb);
            let dg_clone_3 = Clone::clone(&dg);
            let rec_clone_2: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = Rc::clone(&rec);
            let tmp_5 = try_slot(nb_clone_3, dg_clone_3, rec_clone_2, k, v70, int63!(1), tmp_4);
            let nb_clone_4 = Clone::clone(&nb);
            let dg_clone_4 = Clone::clone(&dg);
            let rec_clone_3: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = Rc::clone(&rec);
            let tmp_6 = try_slot(nb_clone_4, dg_clone_4, rec_clone_3, k, v70, int63!(2), tmp_5);
            try_slot(nb, dg, rec, k, v70, int63!(3), tmp_6)
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
pub fn search_1(n: Int63, nb: Array<Int63>, dg: Array<Int63>, k: Int63, rm: Array<Int63>) -> (bool, Array<Int63>) {
  search(n, nb, dg, k, rm, ())
}

// Rocq: Basincity.basincity_implem.search (local: search)
// Variant: uncurried, lifted
pub fn search(n: Int63, nb: Array<Int63>, dg: Array<Int63>, k: Int63, rm: Array<Int63>, _H: ()) -> (bool, Array<Int63>) {
  let tmp = k == int63!(0);
  match bdec(tmp) {
    sumbool::left => {
      std::mem::drop(nb);
      std::mem::drop(dg);
      (true, rm)
    },
    sumbool::right => {
      let nb_clone = Clone::clone(&nb);
      let dg_clone = Clone::clone(&dg);
      let callback: Rc<dyn Fn(Array<Int63>) -> (bool, Array<Int63>)> = Rc::new({
        let __anf_capture_41 = k;
        let __anf_capture_43 = n;
        move |rm_: Array<Int63>| -> (bool, Array<Int63>) {
          let tmp_1 = int63!(1);
          let tmp_2 = Clone::clone(&__anf_capture_41) - tmp_1;
          let tmp_3 = Clone::clone(&__anf_capture_43);
          let tmp_4 = Clone::clone(&nb_clone);
          let tmp_5 = Clone::clone(&dg_clone);
          search(tmp_3, tmp_4, tmp_5, tmp_2, rm_, ())
        }
      });
      node(n, nb, dg, callback, k, rm)
    },
  }
}

// Rocq: Basincity.basincity_implem.basincity_impl
// Variant: uncurried
pub fn basincity_impl(k: Int63, y: Array<Array<Int63>>) -> bool {
  let n = y.length();
  let tmp = Array::<Int63>::make(n, int63!(0));
  let y_clone = Clone::clone(&y);
  let dg = fill_dg_1(y_clone, n, int63!(0), tmp);
  let tmp_1 = int63!(4) * n;
  let nb = fill_nb_1(y, n, int63!(0), Array::<Int63>::make(tmp_1, int63!(0)));
  let tmp_2 = Array::<Int63>::make(n, int63!(0));
  fst::<bool, Array<Int63>>(search_1(n, nb, dg, k, tmp_2))
}
