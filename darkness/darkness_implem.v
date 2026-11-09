(* Executable implementation and its required termination dependencies.
   Correctness proofs are in darkness_proofs.v. *)
(* Implementation of darkness (darkness.spec). *)

From Darkness.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  QArith Relations Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma half_dec : forall x : int, (x =? 0) = false -> Zwf 0 (φ (x / 2)) (φ x).
Proof.
  intros x H. rewrite eqb_false_spec in H.
  assert ((φ x) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  unfold Zwf. rewrite div_spec. change (φ 2) with 2%Z.
  pose proof (to_Z_bounded x). split; [lia|].
  apply Z.div_lt; lia.
Qed.

Lemma dist_dec : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a).
  unfold Zwf. lia.
Qed.

Lemma flow_dec : forall B F F' : int,
  ((F <? F') && (F' <=? B)) = true -> Zwf 0 (gap B F') (gap B F).
Proof.
  intros B F F' H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1. rewrite leb_spec in H2. unfold Zwf, gap.
  pose proof (to_Z_bounded F). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The grid in row-major order: f u i j for every cell u = i*C + j < n. *)
Fixpoint gloop {A : Type} (C n : int) (f : int -> int -> int -> A -> A)
    (u i j : int) (a : A) (H : Acc (Zwf 0) (gap n u)) {struct H} : A :=
  match bdec (u <? n) with
  | left Hu =>
      let a' := f u i j a in
      let j1 := j + 1 in
      let e := j1 =? C in
      gloop C n f (u + 1) (if e then i + 1 else i) (if e then 0 else j1) a'
        (Acc_inv H (dec_step n u Hu))
  | right _ => a
  end.

Definition grid_fold {A : Type} (C n : int) (f : int -> int -> int -> A -> A)
    (a : A) : A :=
  gloop C n f 0 0 0 a (Zwf_well_founded 0 (gap n 0)).

(* Light levels. *)
Definition M48 : int := 281474976710656.

Definition absdiff (a b : int) : int := if a <? b then b - a else a - b.

Definition denom (hh i j i' j' : int) : int :=
  let di := absdiff i i' in let dj := absdiff j j' in di * di + dj * dj + hh.

(* sum of floor (M48 * s / d) over all bulbs *)
Definition lo_sum (s : array int) (C n hh i j : int) : int :=
  grid_fold C n (fun u i' j' acc => acc + (M48 * s.[u]) / denom hh i j i' j') 0.

Fixpoint zofint_aux (x : int) (H : Acc (Zwf 0) (φ x)) {struct H} : Z :=
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      let r := zofint_aux (x / 2) (Acc_inv H (half_dec x Hx)) in
      if x mod 2 =? 0 then (2 * r)%Z else (2 * r + 1)%Z
  end.

Definition zofint (x : int) : Z := zofint_aux x (Zwf_well_founded 0 (φ x)).

(* the exact light level, as the fraction p / q *)
Definition exact_sum (s : array int) (C n hh i j : int) : Z * Z :=
  grid_fold C n (fun u i' j' (pq : Z * Z) =>
    let d := zofint (denom hh i j i' j') in
    let sv := zofint s.[u] in
    ((fst pq * d + sv * snd pq)%Z, (snd pq * d)%Z)) (0%Z, 1%Z).

Definition lit_cell (s : array int) (C n b hh i j : int) : bool :=
  let lo := lo_sum s C n hh i j in
  let mb := M48 * b in
  if mb <=? lo then true
  else if lo + n <? mb then false
  else let pq := exact_sum s C n hh i j in
       Z.leb (zofint b * snd pq) (fst pq).

Definition lit_arr (s : array int) (C n b hh : int) : array bool :=
  grid_fold C n (fun u i j a => a.[u <- lit_cell s C n b hh i j])
    (PArray.make n false).

Definition flat (xg : array (array int)) (C n : int) : array int :=
  grid_fold C n (fun u i j a => a.[u <- xg.[i].[j]]) (PArray.make n 0).

(* Capacities and residuals.  res.[2u] is the residual capacity from u to
   its right neighbour, res.[2u+1] from u to its lower neighbour; the
   residual in the opposite direction is twice the capacity minus it.
   Directions: 0 right, 1 left, 2 down, 3 up. *)
Definition capf (x y : bool) : int := if x && y then 43 else 11.

Definition init_res (lt : array bool) (C n : int) : array int :=
  grid_fold C n (fun u i j r =>
    let c1 := capf lt.[u] lt.[u + 1] in
    let c2 := capf lt.[u] lt.[u + C] in
    r.[2 * u <- c1].[2 * u + 1 <- c2]) (PArray.make (2 * n) 0).

Definition nbr (C p d : int) : int :=
  if d =? 0 then p + 1 else if d =? 1 then p - 1
  else if d =? 2 then p + C else p - C.

Definition opp (d : int) : int :=
  if d =? 0 then 1 else if d =? 1 then 0 else if d =? 2 then 3 else 2.

Definition slot (C p d : int) : int :=
  if d =? 0 then 2 * p else if d =? 1 then 2 * (p - 1)
  else if d =? 2 then 2 * p + 1 else 2 * (p - C) + 1.

Definition fwd (d : int) : bool := (d =? 0) || (d =? 2).

Definition resid (lt : array bool) (res : array int) (C p d : int) : int :=
  let k := slot C p d in
  if fwd d then res.[k] else 2 * capf lt.[p] lt.[nbr C p d] - res.[k].

Definition aug (res : array int) (C p d dl : int) : array int :=
  let k := slot C p d in
  if fwd d then res.[k <- res.[k] - dl] else res.[k <- res.[k] + dl].

(* Breadth-first search from all the dark cells at once (the implicit
   source) in the residual graph. *)
Record bst := { bd : array int; bp : array int; bq : array int; bt : int }.

Definition visit (lt : array bool) (res : array int) (C : int) (st : bst)
    (v dv d : int) (ok : bool) : bst :=
  if ok then
    let w := nbr C v d in
    if 0 <? resid lt res C v d then
      if (bd st).[w] =? 0 then
        {| bd := (bd st).[w <- dv + 1]; bp := (bp st).[w <- d];
           bq := (bq st).[bt st <- w]; bt := bt st + 1 |}
      else st
    else st
  else st.

Fixpoint bfs_loop (lt : array bool) (res : array int) (C n head : int)
    (st : bst) (H : Acc (Zwf 0) (gap n head)) {struct H} : bst :=
  match bdec (head <? n) with
  | left Hh =>
      if head <? bt st then
        let v := (bq st).[head] in
        let dv := (bd st).[v] in
        let j := v mod C in
        let st1 := visit lt res C st v dv 0 (j + 1 <? C) in
        let st2 := visit lt res C st1 v dv 1 (0 <? j) in
        let st3 := visit lt res C st2 v dv 2 (v + C <? n) in
        let st4 := visit lt res C st3 v dv 3 (C <=? v) in
        bfs_loop lt res C n (head + 1) st4 (Acc_inv H (dec_step n head Hh))
      else st
  | right _ => st
  end.

Definition root_step (lt : array bool) (u i j : int) (st : bst) : bst :=
  if lt.[u] then st
  else {| bd := (bd st).[u <- 1]; bp := (bp st).[u <- 4];
          bq := (bq st).[bt st <- u]; bt := bt st + 1 |}.

Definition roots (lt : array bool) (C n : int) : bst :=
  grid_fold C n (root_step lt)
    {| bd := PArray.make n 0; bp := PArray.make n 0;
       bq := PArray.make n 0; bt := 0 |}.

Definition bfs (lt : array bool) (res : array int) (C n : int) : bst :=
  bfs_loop lt res C n 0 (roots lt C n) (Zwf_well_founded 0 (gap n 0)).

Definition is_border (R C i j : int) : bool :=
  (i =? 0) || (i =? R - 1) || (j =? 0) || (j =? C - 1).

(* a reached border cell of least distance, n when there is none *)
Definition fb_step (dist : array int) (R C n u i j acc : int) : int :=
  if is_border R C i j && negb (dist.[u] =? 0)
     && ((acc =? n) || (dist.[u] <? dist.[acc]))
  then u else acc.

Definition find_border (dist : array int) (R C n : int) : int :=
  grid_fold C n (fb_step dist R C n) n.

(* The augmenting path, followed back from a border cell. *)
Fixpoint tmin (lt : array bool) (res : array int) (C : int) (par dist : array int)
    (v dl : int) (H : Acc (Zwf 0) (φ (dist.[v]))) {struct H} : int :=
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlt =>
        let r := resid lt res C p d in
        tmin lt res C par dist p (if r <? dl then r else dl)
          (Acc_inv H (dist_dec _ _ Hlt))
    | right _ => dl
    end
  else dl.

Fixpoint tapp (C : int) (par dist : array int) (dl v : int) (res : array int)
    (H : Acc (Zwf 0) (φ (dist.[v]))) {struct H} : array int :=
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlt =>
        tapp C par dist dl p (aug res C p d dl) (Acc_inv H (dist_dec _ _ Hlt))
    | right _ => res
    end
  else res.

Fixpoint flow_loop (lt : array bool) (R C n B : int) (res : array int) (F : int)
    (H : Acc (Zwf 0) (gap B F)) {struct H} : int :=
  let st := bfs lt res C n in
  let w := find_border (bd st) R C n in
  if w =? n then F
  else
    let dl := tmin lt res C (bp st) (bd st) w 1000
                (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let res' := tapp C (bp st) (bd st) dl w res
                  (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let F' := F + dl in
    match bdec ((F <? F') && (F' <=? B)) with
    | left Hg => flow_loop lt R C n B res' F' (Acc_inv H (flow_dec B F F' Hg))
    | right _ => F
    end.

Definition darkness_impl (xb xh : uint) (xg : array (array uint)) : uint :=
  let R := PArray.length xg in
  let C := PArray.length xg.[0] in
  let n := R * C in
  let s := flat xg C n in
  let lt := lit_arr s C n xb (xh * xh) in
  let res := init_res lt C n in
  let B := 86 * n in
  flow_loop lt R C n B res 0 (Zwf_well_founded 0 (gap B 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition darkness : uint -> uint -> array (array uint) -> uint := darkness_impl.
