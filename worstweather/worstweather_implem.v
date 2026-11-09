(* Executable implementation and its required termination dependencies.
   Correctness proofs are in worstweather_proofs.v. *)
(* Implementation of worstweather (worstweather.spec): a sparse table
   for range maxima of the rain, two binary searches per query.

   Code.  [worstweather_impl ys rs qy qx] with n = |ys|:
   - L = floor(log2 n) + 1 levels; one flat table T of L*n cells, cell
     k*n + i holding max rs[i .. i + 2^k) (row 0 copied from rs, row k
     built from row k-1, [build]);
   - for each query (Y, X): i, j = the first indices with ys >= Y, X
     (signed binary searches, [lower_bound]); Y is known iff ys[i] = Y,
     X iff ys[j] = X; the known years strictly between are the indices
     [lo, j) with lo = i+1 or i; their maximum rain is one O(1) lookup in
     T ([rmq], k = floor(log2 (j - lo)) by a halving loop); then
       both known:  rx <= ry and max < rx  ->  true if j - i = X - Y
                    (every year in between known) else maybe; else false
       Y only:      max < ry -> maybe, else false
       X only:      max < rx -> maybe, else false
       neither:     maybe;
   - the result array is filled in place, one [set] per query.
   Everything is Uint63 [int]; years are compared through Sint63.ltb.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof (the template's device); no nat, no fuel.

   Proof.  [tbl_ok] (each cell is the maximum of its range) is the table
   invariant; [lb_loop_spec] the binary-search invariant; the Math section
   reduces [answers] to the four cases above ([ans_of_correct]), using the
   assignment [ext g] (the known rain, g elsewhere) as the witness of
   might_be_true, and [count_iff] (strictly increasing integers fill
   [ys_i, ys_j] iff j - i = ys_j - ys_i) for the "true" case. *)

From Worstweather.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
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

Lemma lb_dec_r : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap hi (lo + (hi - lo) / 2 + 1)) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma lb_dec_l : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma lg_dec : forall x : int, (1 <? x) = true -> Zwf 0 (φ (x / 2)) (φ x).
Proof. intros x H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The first index p in [lo, hi) with key <= ys.[p] (signed), or hi. *)
Fixpoint lb_loop (ys : array int) (key lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      if Sint63.ltb ys.[mid] key
      then lb_loop ys key (mid + 1) hi (Acc_inv H (lb_dec_r lo hi Hlt))
      else lb_loop ys key lo mid (Acc_inv H (lb_dec_l lo hi Hlt))
  | right _ => lo
  end.

Definition lower_bound (ys : array int) (n key : int) : int :=
  lb_loop ys key 0 n (Zwf_well_founded 0 (gap n 0)).

(* k + floor(log2 x), for x >= 1. *)
Fixpoint lg_loop (x k : int) (H : Acc (Zwf 0) (φ x)) {struct H} : int :=
  match bdec (1 <? x) with
  | left Hx => lg_loop (x / 2) (k + 1) (Acc_inv H (lg_dec x Hx))
  | right _ => k
  end.

Definition lg (x : int) : int := lg_loop x 0 (Zwf_well_founded 0 (φ x)).

Definition imax (a b : int) : int := if a <? b then b else a.

(* Row 0 of the sparse table: the rain itself. *)
Fixpoint copy_loop (rs : array int) (n i : int) (T : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => copy_loop rs n (i + 1) T.[i <- rs.[i]] (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

(* Row k (base = k*n): cell i is the max of the two halves of row k-1. *)
Fixpoint row_loop (base prev half lim i : int) (T : array int)
    (H : Acc (Zwf 0) (gap lim i)) {struct H} : array int :=
  match bdec (i <? lim) with
  | left Hi =>
      row_loop base prev half lim (i + 1)
        T.[base + i <- imax T.[prev + i] T.[prev + i + half]]
        (Acc_inv H (dec_step lim i Hi))
  | right _ => T
  end.

Fixpoint rows_loop (n L k : int) (T : array int)
    (H : Acc (Zwf 0) (gap L k)) {struct H} : array int :=
  match bdec (k <? L) with
  | left Hk =>
      rows_loop n L (k + 1)
        (row_loop (k * n) ((k - 1) * n) (1 << (k - 1)) (n - (1 << k) + 1) 0 T
           (Zwf_well_founded 0 (gap (n - (1 << k) + 1) 0)))
        (Acc_inv H (dec_step L k Hk))
  | right _ => T
  end.

Definition build (rs : array int) (n L : int) : array int :=
  rows_loop n L 1
    (copy_loop rs n 0 (PArray.make (L * n) 0) (Zwf_well_founded 0 (gap n 0)))
    (Zwf_well_founded 0 (gap L 1)).

(* max of the rain over [l, r), l < r. *)
Definition rmq (T : array int) (n l r : int) : int :=
  let k := lg (r - l) in
  imax T.[k * n + l] T.[k * n + (r - (1 << k))].

(* every known year in [lo, j) had less rain than v *)
Definition below (T : array int) (n lo j v : int) : bool :=
  if lo <? j then rmq T n lo j <? v else true.

Definition answer_query (ys rs T : array int) (n Y X : int) : answer :=
  let i := lower_bound ys n Y in
  let j := lower_bound ys n X in
  let yk := if i <? n then ys.[i] =? Y else false in
  let xk := if j <? n then ys.[j] =? X else false in
  let lo := if yk then i + 1 else i in
  if yk then
    if xk then
      if rs.[j] <=? rs.[i] then
        if below T n lo j rs.[j] then
          (if j - i =? X - Y then Ans_true else Ans_maybe)
        else Ans_false
      else Ans_false
    else if below T n lo j rs.[i] then Ans_maybe else Ans_false
  else if xk then (if below T n lo j rs.[j] then Ans_maybe else Ans_false)
  else Ans_maybe.

Fixpoint q_loop (ys rs T qy qx : array int) (n m k : int) (out : array answer)
    (H : Acc (Zwf 0) (gap m k)) {struct H} : array answer :=
  match bdec (k <? m) with
  | left Hk =>
      q_loop ys rs T qy qx n m (k + 1)
        out.[k <- answer_query ys rs T n qy.[k] qx.[k]]
        (Acc_inv H (dec_step m k Hk))
  | right _ => out
  end.

Definition worstweather_impl (ys : array int) (rs : array int)
    (qy qx : array int) : array answer :=
  let n := PArray.length ys in
  let m := PArray.length qy in
  let L := lg n + 1 in
  let T := build rs n L in
  q_loop ys rs T qy qx n m 0 (PArray.make m Ans_false)
    (Zwf_well_founded 0 (gap m 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition worstweather :
  array sint -> array uint -> array sint -> array sint -> array answer :=
  worstweather_impl.
