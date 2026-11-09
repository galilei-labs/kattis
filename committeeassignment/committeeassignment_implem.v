(* Executable implementation and its required termination dependencies.
   Correctness proofs are in committeeassignment_proofs.v. *)
From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require PrimString PString String Ascii.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Notation pstr := PrimString.string.

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

Lemma dec_down : forall t j : int,
  (t <? j) = true -> Zwf 0 (gap (j - 1) t) (gap j t).
Proof.
  intros t j H. rewrite ltb_spec in H.
  assert (H1 : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Definition midp (lo hi : int) : int := lo + (hi - lo) / 2.

Lemma midp_spec : forall lo hi : int, ((φ lo) < (φ hi))%Z ->
  (φ (midp lo hi)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z /\
  ((φ lo) <= (φ (midp lo hi)) < (φ hi))%Z.
Proof.
  intros lo hi H. unfold midp.
  pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E1 : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  assert (E2 : (φ ((hi - lo) / 2)) = (((φ hi) - (φ lo)) / 2)%Z)
    by (rewrite div_spec, E1; reflexivity).
  assert (B : (0 <= ((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z)
    by (split; [apply Z.div_pos | apply Z.div_lt]; lia).
  assert (E3 : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z).
  { rewrite add_spec, E2. apply Z.mod_small. lia. }
  rewrite E3. lia.
Qed.

Lemma dec_lo : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap hi (midp lo hi + 1)) (gap hi lo).
Proof.
  intros lo hi H. rewrite ltb_spec in H.
  destruct (midp_spec lo hi H) as [_ B].
  assert (H1 : (φ (midp lo hi + 1)) = ((φ (midp lo hi)) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_hi : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap (midp lo hi) lo) (gap hi lo).
Proof.
  intros lo hi H. rewrite ltb_spec in H.
  destruct (midp_spec lo hi H) as [_ B].
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program: naming                                                 *)
(* ------------------------------------------------------------------ *)

(* The first index t in [lo, hi] such that K.[t] is not below s (K sorted). *)
Fixpoint lb (K : array pstr) (s : pstr) (lo hi : int)
    (H : Acc (Zwf 0) (gap hi lo)) {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      match PrimString.compare K.[midp lo hi] s with
      | Lt => lb K s (midp lo hi + 1) hi (Acc_inv H (dec_lo lo hi Hlt))
      | _ => lb K s lo (midp lo hi) (Acc_inv H (dec_hi lo hi Hlt))
      end
  | right _ => lo
  end.

Definition look (K : array pstr) (p : int) (s : pstr) : int :=
  lb K s 0 p (Zwf_well_founded 0 (gap p 0)).

(* Cells t+1 .. j receive the cells t .. j-1. *)
Fixpoint shift (K : array pstr) (t j : int)
    (H : Acc (Zwf 0) (gap j t)) {struct H} : array pstr :=
  match bdec (t <? j) with
  | left Hlt => shift K.[j <- K.[j - 1]] t (j - 1) (Acc_inv H (dec_down t j Hlt))
  | right _ => K
  end.

Definition is_eq (c : comparison) : bool :=
  match c with Eq => true | _ => false end.

(* Insert s into the sorted table K.[0 .. p-1] unless it is there. *)
Definition insert (K : array pstr) (p : int) (s : pstr) : array pstr * int :=
  let t := look K p s in
  if andb (t <? p) (is_eq (PrimString.compare K.[t] s)) then (K, p)
  else ((shift K t p (Zwf_well_founded 0 (gap p t))).[t <- s], p + 1).

Fixpoint build (y z : array pstr) (m i : int) (K : array pstr) (p : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array pstr * int :=
  match bdec (i <? m) with
  | left Hi =>
      let (K1, p1) := insert K p y.[i] in
      let (K2, p2) := insert K1 p1 z.[i] in
      build y z m (i + 1) K2 p2 (Acc_inv H (dec_step m i Hi))
  | right _ => (K, p)
  end.

(* The conflict graph, a flat p*p table. *)
Fixpoint fill (y z K : array pstr) (p m i : int) (tbl : array bool)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array bool :=
  match bdec (i <? m) with
  | left Hi =>
      let u := look K p y.[i] in
      let v := look K p z.[i] in
      fill y z K p m (i + 1) tbl.[u * p + v <- true].[v * p + u <- true]
        (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.

(* ------------------------------------------------------------------ *)
(* The program: colouring                                              *)
(* ------------------------------------------------------------------ *)

(* No member u = w .. v-1 adjacent to v has colour c. *)
Fixpoint okc (tbl : array bool) (p v c : int) (col : array int) (u : int)
    (H : Acc (Zwf 0) (gap v u)) {struct H} : bool :=
  match bdec (u <? v) with
  | left Hu =>
      if andb tbl.[u * p + v] (col.[u] =? c) then false
      else okc tbl p v c col (u + 1) (Acc_inv H (dec_step v u Hu))
  | right _ => true
  end.

(* One past the largest colour member v may take. *)
Definition lim (used k : int) : int := if used <? k then used + 1 else k.

Definition meas (p k v c : int) : Z :=
  (((φ p) - (φ v)) * ((φ k) + 1) + ((φ k) - (φ c)))%Z.

Lemma lim_le : forall used k c : int,
  (c <? lim used k) = true -> ((φ c) < (φ k))%Z.
Proof.
  intros used k c H. unfold lim in H. rewrite ltb_spec in H.
  destruct (used <? k) eqn:E; [rewrite ltb_spec in E|]; sia.
Qed.

Lemma dec_v : forall p k v c used : int,
  (v <? p) = true -> (c <? lim used k) = true ->
  Zwf 0 (meas p k (v + 1) 0) (meas p k v c).
Proof.
  intros p k v c used Hv Hc. pose proof (lim_le _ _ _ Hc) as Hck.
  rewrite ltb_spec in Hv.
  assert (H1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded k).
  unfold Zwf, meas. rewrite H1. change (φ 0) with 0%Z. nia.
Qed.

Lemma dec_c : forall p k v c used : int,
  (v <? p) = true -> (c <? lim used k) = true ->
  Zwf 0 (meas p k v (c + 1)) (meas p k v c).
Proof.
  intros p k v c used Hv Hc. pose proof (lim_le _ _ _ Hc) as Hck.
  rewrite ltb_spec in Hv.
  assert (H1 : (φ (c + 1)) = ((φ c) + 1)%Z) by sia.
  pose proof (to_Z_bounded c). pose proof (to_Z_bounded k).
  unfold Zwf, meas. rewrite H1. nia.
Qed.

Definition bump (used c : int) : int := if used <? c + 1 then c + 1 else used.

(* Backtracking: colour members v .. p-1 with colours below k, member v
   taking a colour in [c, lim used k), where used is one past the largest
   colour of members 0 .. v-1. *)
Fixpoint srch (tbl : array bool) (p k v c used : int) (col : array int)
    (H : Acc (Zwf 0) (meas p k v c)) {struct H} : bool * array int :=
  match bdec (v <? p) with
  | right _ => (true, col)
  | left Hv =>
      match bdec (c <? lim used k) with
      | right _ => (false, col)
      | left Hc =>
          if okc tbl p v c col 0 (Zwf_well_founded 0 (gap v 0)) then
            match srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                    (Acc_inv H (dec_v p k v c used Hv Hc)) with
            | (true, col2) => (true, col2)
            | (false, col2) =>
                srch tbl p k v (c + 1) used col2 (Acc_inv H (dec_c p k v c used Hv Hc))
            end
          else srch tbl p k v (c + 1) used col (Acc_inv H (dec_c p k v c used Hv Hc))
      end
  end.

(* Iterative deepening on the number of committees. *)
Fixpoint deepen (tbl : array bool) (p P k : int) (col : array int)
    (H : Acc (Zwf 0) (gap P k)) {struct H} : int :=
  match bdec (k <? P) with
  | left Hk =>
      let (r, col2) := srch tbl p k 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0)) in
      if r then k else deepen tbl p P (k + 1) col2 (Acc_inv H (dec_step P k Hk))
  | right _ => P
  end.

Definition committees_impl (n : uint) (y z : array pstr) : uint :=
  let m := PArray.length y in
  let (K, p) := build y z m 0 (PArray.make (m + m) (PrimString.make 0 0)) 0
                  (Zwf_well_founded 0 (gap m 0)) in
  let tbl := fill y z K p m 0 (PArray.make (p * p) false)
               (Zwf_well_founded 0 (gap m 0)) in
  let P := if p <? 1 then 1 else p in
  deepen tbl p P 1 (PArray.make P 0) (Zwf_well_founded 0 (gap P 1)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition committees : uint -> array PrimString.string -> array PrimString.string -> uint :=
  committees_impl.
