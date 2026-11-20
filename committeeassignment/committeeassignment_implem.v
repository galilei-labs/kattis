From Committeeassignment.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require PrimString PString String Ascii Finite.
From KattisLib Require Import Cost.
Import PrimString.PStringNotations.
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
Elpi complexity sumbool.
Elpi complexity bdec.

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
Elpi complexity midp.
Arguments midp_cost : simpl never.

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
Elpi complexity lb.
Arguments lb_cost : simpl never.

Definition look (K : array pstr) (p : int) (s : pstr) : int :=
  lb K s 0 p (Zwf_well_founded 0 (gap p 0)).
Elpi complexity look.
Arguments look_cost : simpl never.

(* Cells t+1 .. j receive the cells t .. j-1. *)
Fixpoint shift (K : array pstr) (t j : int)
    (H : Acc (Zwf 0) (gap j t)) {struct H} : array pstr :=
  match bdec (t <? j) with
  | left Hlt => shift K.[j <- K.[j - 1]] t (j - 1) (Acc_inv H (dec_down t j Hlt))
  | right _ => K
  end.
Elpi complexity shift.
Arguments shift_cost : simpl never.

Definition is_eq (c : comparison) : bool :=
  match c with Eq => true | _ => false end.
Elpi complexity is_eq.
Arguments is_eq_cost : simpl never.
Elpi complexity andb.
Arguments andb_cost : simpl never.

(* Insert s into the sorted table K.[0 .. p-1] unless it is there. *)
Definition insert (K : array pstr) (p : int) (s : pstr) : array pstr * int :=
  let t := look K p s in
  if andb (t <? p) (is_eq (PrimString.compare K.[t] s)) then (K, p)
  else ((shift K t p (Zwf_well_founded 0 (gap p t))).[t <- s], p + 1).
Elpi complexity insert.
Arguments insert_cost : simpl never.

Fixpoint build (y z : array pstr) (m i : int) (K : array pstr) (p : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array pstr * int :=
  match bdec (i <? m) with
  | left Hi =>
      let (K1, p1) := insert K p y.[i] in
      let (K2, p2) := insert K1 p1 z.[i] in
      build y z m (i + 1) K2 p2 (Acc_inv H (dec_step m i Hi))
  | right _ => (K, p)
  end.
Elpi complexity build.
Arguments build_cost : simpl never.

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
Elpi complexity fill.
Arguments fill_cost : simpl never.

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
Elpi complexity okc.
Arguments okc_cost : simpl never.

(* One past the largest colour member v may take. *)
Definition lim (used k : int) : int := if used <? k then used + 1 else k.
Elpi complexity lim.
Arguments lim_cost : simpl never.

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
Elpi complexity bump.
Arguments bump_cost : simpl never.

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
Elpi complexity srch.
Arguments srch_cost : simpl never.

(* Iterative deepening on the number of committees. *)
Fixpoint deepen (tbl : array bool) (p P k : int) (col : array int)
    (H : Acc (Zwf 0) (gap P k)) {struct H} : int :=
  match bdec (k <? P) with
  | left Hk =>
      let (r, col2) := srch tbl p k 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0)) in
      if r then k else deepen tbl p P (k + 1) col2 (Acc_inv H (dec_step P k Hk))
  | right _ => P
  end.
Elpi complexity deepen.
Arguments deepen_cost : simpl never.

Definition committees_impl (n : uint) (y z : array pstr) : uint :=
  let m := PArray.length y in
  let (K, p) := build y z m 0 (PArray.make (m + m) ""%pstring) 0
                  (Zwf_well_founded 0 (gap m 0)) in
  let tbl := fill y z K p m 0 (PArray.make (p * p) false)
               (Zwf_well_founded 0 (gap m 0)) in
  let P := if p <? 1 then 1 else p in
  deepen tbl p P 1 (PArray.make P 0) (Zwf_well_founded 0 (gap P 1)).
Elpi complexity committees_impl.
Arguments committees_impl_cost : simpl never.

(* ================================================================== *)
(* Prop side                                                           *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Unfolding equations                                                 *)
(* ------------------------------------------------------------------ *)

Lemma lb_eq : forall K s lo hi H, lb K s lo hi H =
  match bdec (lo <? hi) with
  | left Hlt =>
      match PrimString.compare K.[midp lo hi] s with
      | Lt => lb K s (midp lo hi + 1) hi (Acc_inv H (dec_lo lo hi Hlt))
      | _ => lb K s lo (midp lo hi) (Acc_inv H (dec_hi lo hi Hlt))
      end
  | right _ => lo
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma shift_eq : forall K t j H, shift K t j H =
  match bdec (t <? j) with
  | left Hlt => shift K.[j <- K.[j - 1]] t (j - 1) (Acc_inv H (dec_down t j Hlt))
  | right _ => K
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_eq : forall y z m i K p H, build y z m i K p H =
  match bdec (i <? m) with
  | left Hi =>
      let (K1, p1) := insert K p y.[i] in
      let (K2, p2) := insert K1 p1 z.[i] in
      build y z m (i + 1) K2 p2 (Acc_inv H (dec_step m i Hi))
  | right _ => (K, p)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_eq : forall y z K p m i tbl H, fill y z K p m i tbl H =
  match bdec (i <? m) with
  | left Hi =>
      let u := look K p y.[i] in
      let v := look K p z.[i] in
      fill y z K p m (i + 1) tbl.[u * p + v <- true].[v * p + u <- true]
        (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma okc_eq : forall tbl p v c col u H, okc tbl p v c col u H =
  match bdec (u <? v) with
  | left Hu =>
      if andb tbl.[u * p + v] (col.[u] =? c) then false
      else okc tbl p v c col (u + 1) (Acc_inv H (dec_step v u Hu))
  | right _ => true
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma srch_eq : forall tbl p k v c used col H, srch tbl p k v c used col H =
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
Proof. intros. destruct H. reflexivity. Qed.

Lemma deepen_eq : forall tbl p P k col H, deepen tbl p P k col H =
  match bdec (k <? P) with
  | left Hk =>
      let (r, col2) := srch tbl p k 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0)) in
      if r then k else deepen tbl p P (k + 1) col2 (Acc_inv H (dec_step P k Hk))
  | right _ => P
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Arrays and machine words                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alen_bound : forall {A : Set} (t : array@{Set} A), ((φ (PArray.length@{Set} t)) <= 4194303)%Z.
Proof.
  intros A t. pose proof (leb_length A t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alen_set : forall {A : Set} (t : array@{Set} A) i b,
  PArray.length@{Set} (PArray.set@{Set} t i b) = PArray.length@{Set} t.
Proof. intros A t i b. exact (length_set A t i b). Qed.

Lemma aget_same : forall {A : Set} (t : array@{Set} A) i b,
  ((φ i) < (φ (PArray.length@{Set} t)))%Z -> PArray.get@{Set} (PArray.set@{Set} t i b) i = b.
Proof. intros A t i b H. rewrite <- ltb_spec in H. exact (get_set_same A t i b H). Qed.

Lemma aget_other : forall {A : Set} (t : array@{Set} A) i j b, i <> j ->
  PArray.get@{Set} (PArray.set@{Set} t i b) j = PArray.get@{Set} t j.
Proof. intros A t i j b H. exact (get_set_other A t i j b H). Qed.

Lemma aget_make : forall {A : Set} (n i : int) (b : A),
  PArray.get@{Set} (PArray.make@{Set} n b) i = b.
Proof. intros A n i b. exact (get_make A b n i). Qed.

Lemma alen_make : forall {A : Set} (n : int) (b : A), ((φ n) <= 4194303)%Z ->
  PArray.length@{Set} (PArray.make@{Set} n b) = n.
Proof.
  intros A n b H. pose proof (length_make A n b) as E.
  replace (n <=? max_length) with true in E; [exact E|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma int_eq : forall i j : int, (φ i) = (φ j) -> i = j.
Proof. intros i j H. apply to_Z_inj. exact H. Qed.

Lemma int_neq : forall i j : int, (φ i) <> (φ j) -> i <> j.
Proof. intros i j H E. subst. apply H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* String comparison                                                   *)
(* ------------------------------------------------------------------ *)

Definition sorted (K : array pstr) (p : int) : Prop :=
  forall i j : int, ((φ i) < (φ j) < (φ p))%Z -> PrimString.compare K.[i] K.[j] = Lt.

Definition mem (K : array pstr) (p : int) (s : pstr) : Prop :=
  exists t : int, ((φ t) < (φ p))%Z /\ K.[t] = s.

Lemma cmp_refl : forall s, PrimString.compare s s = Eq.
Proof. intros s. apply PString.compare_eq. reflexivity. Qed.

Lemma cmp_lt_gt : forall s t, PrimString.compare s t = Lt -> PrimString.compare t s = Gt.
Proof. intros s t H. rewrite PString.compare_antisym, H. reflexivity. Qed.

Lemma cmp_gt_lt : forall s t, PrimString.compare s t = Gt -> PrimString.compare t s = Lt.
Proof. intros s t H. rewrite PString.compare_antisym, H. reflexivity. Qed.

Lemma lb_spec : forall (K : array pstr) (s : pstr) (p : int), sorted K p ->
  forall (z : Z) (lo hi : int) (H : Acc (Zwf 0) (gap hi lo)),
  gap hi lo = z -> ((φ lo) <= (φ hi) <= (φ p))%Z ->
  (forall i, ((φ i) < (φ lo))%Z -> PrimString.compare K.[i] s = Lt) ->
  (forall i, ((φ hi) <= (φ i) < (φ p))%Z -> PrimString.compare K.[i] s <> Lt) ->
  let t := lb K s lo hi H in
  ((φ t) <= (φ hi))%Z /\
  (forall i, ((φ i) < (φ t))%Z -> PrimString.compare K.[i] s = Lt) /\
  (forall i, ((φ t) <= (φ i) < (φ p))%Z -> PrimString.compare K.[i] s <> Lt).
Proof.
  intros K s p Hs z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H Hz Hb Hlo Hhi. cbv zeta.
  rewrite lb_eq. destruct (bdec (lo <? hi)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    destruct (midp_spec lo hi Hlt') as [_ Bm].
    destruct (PrimString.compare K.[midp lo hi] s) eqn:Ec.
    + edestruct (IH (gap (midp lo hi) lo) ltac:(rewrite <- Hz; apply dec_hi; exact Hlt)
                  lo (midp lo hi) (Acc_inv H (dec_hi lo hi Hlt)) eq_refl) as (R1 & R2 & R3);
        [lia | exact Hlo | | ].
      * intros i Hi. destruct (Z.eq_dec (φ i) (φ (midp lo hi))) as [E|E].
        -- rewrite (int_eq _ _ E), Ec. discriminate.
        -- intros F. assert (G := PString.compare_trans Lt _ _ _ (Hs (midp lo hi) i ltac:(lia)) F).
           rewrite Ec in G. discriminate.
      * split; [lia|]. split; assumption.
    + assert (H1 : (φ (midp lo hi + 1)) = ((φ (midp lo hi)) + 1)%Z) by sia.
      edestruct (IH (gap hi (midp lo hi + 1)) ltac:(rewrite <- Hz; apply dec_lo; exact Hlt)
                  (midp lo hi + 1) hi (Acc_inv H (dec_lo lo hi Hlt)) eq_refl) as (R1 & R2 & R3);
        [lia | | exact Hhi | ].
      * intros i Hi. destruct (Z.eq_dec (φ i) (φ (midp lo hi))) as [E|E].
        -- rewrite (int_eq _ _ E). exact Ec.
        -- destruct (Z_lt_le_dec (φ i) (φ lo)) as [L|L]; [apply Hlo; exact L|].
           apply (PString.compare_trans Lt _ _ _ (Hs i (midp lo hi) ltac:(lia)) Ec).
      * split; [lia|]. split; assumption.
    + edestruct (IH (gap (midp lo hi) lo) ltac:(rewrite <- Hz; apply dec_hi; exact Hlt)
                  lo (midp lo hi) (Acc_inv H (dec_hi lo hi Hlt)) eq_refl) as (R1 & R2 & R3);
        [lia | exact Hlo | | ].
      * intros i Hi. destruct (Z.eq_dec (φ i) (φ (midp lo hi))) as [E|E].
        -- rewrite (int_eq _ _ E), Ec. discriminate.
        -- intros F. assert (G := PString.compare_trans Lt _ _ _ (Hs (midp lo hi) i ltac:(lia)) F).
           rewrite Ec in G. discriminate.
      * split; [lia|]. split; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [lia|]. split; [exact Hlo|].
    intros i Hi. apply Hhi. lia.
Qed.

Lemma look_spec : forall (K : array pstr) (p : int) (s : pstr), sorted K p ->
  ((φ (look K p s)) <= (φ p))%Z /\
  (forall i, ((φ i) < (φ (look K p s)))%Z -> PrimString.compare K.[i] s = Lt) /\
  (forall i, ((φ (look K p s)) <= (φ i) < (φ p))%Z -> PrimString.compare K.[i] s <> Lt).
Proof.
  intros K p s Hs. unfold look.
  pose proof (to_Z_bounded p).
  apply (lb_spec K s p Hs _ 0 p _ eq_refl).
  - change (φ 0) with 0%Z. lia.
  - intros i Hi. change (φ 0) with 0%Z in Hi. pose proof (to_Z_bounded i). lia.
  - intros i Hi. lia.
Qed.

Lemma look_found : forall (K : array pstr) (p : int) (s : pstr), sorted K p ->
  mem K p s -> ((φ (look K p s)) < (φ p))%Z /\ K.[look K p s] = s.
Proof.
  intros K p s Hs [j [Hj Ej]].
  destruct (look_spec K p s Hs) as (R1 & R2 & R3).
  set (t := look K p s) in *.
  pose proof (to_Z_bounded j).
  destruct (Z_lt_le_dec (φ j) (φ t)) as [L|L].
  - specialize (R2 j L). rewrite Ej, cmp_refl in R2. discriminate.
  - destruct (Z.eq_dec (φ j) (φ t)) as [E|E].
    + rewrite <- (int_eq _ _ E). split; [lia | exact Ej].
    + exfalso. apply (R3 t). { pose proof (to_Z_bounded t); lia. }
      rewrite <- Ej. apply Hs. pose proof (to_Z_bounded t). lia.
Qed.

Lemma shift_spec : forall (z : Z) (K : array pstr) (t j : int) (H : Acc (Zwf 0) (gap j t)),
  gap j t = z -> ((φ t) <= (φ j))%Z -> ((φ j) < (φ (PArray.length K)))%Z ->
  PArray.length (shift K t j H) = PArray.length K /\
  (forall i, ((φ t) < (φ i) <= (φ j))%Z -> (shift K t j H).[i] = K.[i - 1]) /\
  (forall i, ~ ((φ t) < (φ i) <= (φ j))%Z -> (shift K t j H).[i] = K.[i]).
Proof.
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros K t j H Hz Htj Hj.
  rewrite shift_eq. destruct (bdec (t <? j)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Ej : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
    destruct (IH (gap (j - 1) t) ltac:(rewrite <- Hz; apply dec_down; exact Hlt)
                 K.[j <- K.[j - 1]] t (j - 1) (Acc_inv H (dec_down t j Hlt)) eq_refl
                 ltac:(lia) ltac:(rewrite alen_set; lia)) as (R1 & R2 & R3).
    split; [rewrite R1; apply alen_set|]. split.
    + intros i Hi. destruct (Z.eq_dec (φ i) (φ j)) as [E|E].
      * rewrite R3 by lia. rewrite (int_eq _ _ E). apply aget_same. exact Hj.
      * rewrite R2 by lia. apply aget_other. apply int_neq.
        assert ((φ (i - 1)) = ((φ i) - 1)%Z) by sia. lia.
    + intros i Hi. rewrite R3 by lia. apply aget_other. apply int_neq. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [reflexivity|]. split.
    + intros i Hi. lia.
    + intros i Hi. reflexivity.
Qed.

Lemma insert_spec : forall (K : array pstr) (p : int) (s : pstr) K' p',
  sorted K p -> ((φ p) < (φ (PArray.length K)))%Z ->
  insert K p s = (K', p') ->
  PArray.length K' = PArray.length K /\
  ((φ p) <= (φ p') <= (φ p) + 1)%Z /\
  sorted K' p' /\ mem K' p' s /\
  (forall x, mem K p x -> mem K' p' x).
Proof.
  intros K p s K' p' Hs Hp Hins. unfold insert in Hins.
  destruct (look_spec K p s Hs) as (R1 & R2 & R3).
  set (t := look K p s) in *.
  pose proof (to_Z_bounded t) as Bt. pose proof (to_Z_bounded p) as Bp.
  destruct (andb (t <? p) (is_eq (PrimString.compare K.[t] s))) eqn:Ef.
  - injection Hins as <- <-.
    apply andb_prop in Ef as [Ef1 Ef2]. rewrite ltb_spec in Ef1.
    split; [reflexivity|]. split; [lia|]. split; [exact Hs|]. split; [|tauto].
    exists t. split; [exact Ef1|].
    apply PString.compare_eq. destruct (PrimString.compare K.[t] s); [reflexivity|discriminate|discriminate].
  - injection Hins as <- <-.
    assert (Hp1 : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
    (* every cell from t on is above s *)
    assert (Hgt : forall i, ((φ t) <= (φ i) < (φ p))%Z -> PrimString.compare K.[i] s = Gt).
    { intros i Hi. pose proof (R3 i Hi) as R3i.
      destruct (PrimString.compare K.[i] s) eqn:Ec; [|tauto|reflexivity].
      exfalso. destruct (Z.eq_dec (φ i) (φ t)) as [E|E].
      - rewrite (int_eq _ _ E) in Ec.
        assert (Et : (t <? p) = true) by (rewrite ltb_spec; lia).
        rewrite Et, Ec in Ef. discriminate.
      - apply PString.compare_eq in Ec.
        apply (R3 t); [lia|]. rewrite <- Ec. apply Hs. lia. }
    destruct (shift_spec _ K t p (Zwf_well_founded 0 (gap p t)) eq_refl ltac:(lia) Hp)
      as (S1 & S2 & S3).
    set (K1 := shift K t p (Zwf_well_founded 0 (gap p t))) in *.
    assert (G1 : forall i, ((φ i) < (φ t))%Z -> K1.[t <- s].[i] = K.[i]).
    { intros i Hi. rewrite aget_other by (apply int_neq; lia). apply S3. lia. }
    assert (G2 : K1.[t <- s].[t] = s) by (apply aget_same; rewrite S1; lia).
    assert (G3 : forall i, ((φ t) < (φ i) <= (φ p))%Z -> K1.[t <- s].[i] = K.[i - 1]).
    { intros i Hi. rewrite aget_other by (apply int_neq; lia). apply S2. lia. }
    split; [rewrite alen_set; exact S1|]. split; [lia|]. split; [|split].
    + intros i j Hij. rewrite Hp1 in Hij.
      destruct (Z_lt_le_dec (φ j) (φ t)) as [Lj|Lj].
      * rewrite !G1 by lia. apply Hs. lia.
      * destruct (Z.eq_dec (φ j) (φ t)) as [Ej|Ej].
        -- rewrite (int_eq _ _ Ej), G2, G1 by lia. apply R2. lia.
        -- assert (Ej1 : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
           rewrite (G3 j) by lia.
           destruct (Z_lt_le_dec (φ i) (φ t)) as [Li|Li].
           ++ rewrite G1 by lia. apply Hs. lia.
           ++ destruct (Z.eq_dec (φ i) (φ t)) as [Ei|Ei].
              ** rewrite (int_eq _ _ Ei), G2. apply cmp_gt_lt. apply Hgt. lia.
              ** assert (Ei1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
                 rewrite (G3 i) by lia. apply Hs. lia.
    + exists t. split; [lia | exact G2].
    + intros x [i [Hi <-]].
      destruct (Z_lt_le_dec (φ i) (φ t)) as [Li|Li].
      * exists i. split; [lia|]. apply G1. exact Li.
      * exists (i + 1). assert (Ei1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
        split; [lia|]. rewrite G3 by lia. f_equal. apply int_eq. sia.
Qed.

Lemma build_spec : forall (y z : array pstr) (m : int),
  ((φ m) <= 4194303)%Z ->
  forall (zz : Z) (i : int) (K : array pstr) (p : int) (H : Acc (Zwf 0) (gap m i)) K' p',
  gap m i = zz -> ((φ i) <= (φ m))%Z ->
  (φ (PArray.length K)) = (2 * (φ m))%Z -> ((φ p) <= 2 * (φ i))%Z -> sorted K p ->
  (forall j, ((φ j) < (φ i))%Z -> mem K p y.[j] /\ mem K p z.[j]) ->
  build y z m i K p H = (K', p') ->
  (φ (PArray.length K')) = (2 * (φ m))%Z /\ ((φ p') <= 2 * (φ m))%Z /\ sorted K' p' /\
  (forall j, ((φ j) < (φ m))%Z -> mem K' p' y.[j] /\ mem K' p' z.[j]).
Proof.
  intros y z m Hm zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i K p H K' p' Hz Him HK Hp Hs Hmem Hb.
  rewrite build_eq in Hb. destruct (bdec (i <? m)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Ei : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (insert K p y.[i]) as [K1 p1] eqn:E1.
    destruct (insert K1 p1 z.[i]) as [K2 p2] eqn:E2.
    destruct (insert_spec K p y.[i] K1 p1 Hs ltac:(lia) E1) as (A1 & A2 & A3 & A4 & A5).
    destruct (insert_spec K1 p1 z.[i] K2 p2 A3 ltac:(rewrite A1; lia) E2)
      as (B1 & B2 & B3 & B4 & B5).
    refine (IH (gap m (i + 1)) _ (i + 1) K2 p2 _ K' p' eq_refl _ _ _ B3 _ Hb);
      [rewrite <- Hz; apply dec_step; exact Hi | lia | rewrite B1, A1; exact HK | lia | ].
    intros j Hj. destruct (Z.eq_dec (φ j) (φ i)) as [E|E].
    + rewrite (int_eq _ _ E). split; [apply B5; exact A4 | exact B4].
    + destruct (Hmem j ltac:(lia)) as [M1 M2]. split; apply B5, A5; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    injection Hb as <- <-.
    split; [exact HK|]. split; [lia|]. split; [exact Hs|].
    intros j Hj. apply Hmem. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The conflict table                                                  *)
(* ------------------------------------------------------------------ *)

Lemma idx_inj : forall u v u' v' p : Z,
  (0 <= u < p -> 0 <= v < p -> 0 <= u' < p -> 0 <= v' < p ->
   u * p + v = u' * p + v' -> u = u' /\ v = v')%Z.
Proof.
  intros u v u' v' p Hu Hv Hu' Hv' E.
  assert (u = u') by nia. subst. lia.
Qed.

Lemma idx_spec : forall p u v : int, ((φ p) * (φ p) <= 4194303)%Z ->
  ((φ u) < (φ p))%Z -> ((φ v) < (φ p))%Z ->
  (φ (u * p + v)) = ((φ u) * (φ p) + (φ v))%Z /\ ((φ u) * (φ p) + (φ v) < (φ p) * (φ p))%Z.
Proof.
  intros p u v Hp Hu Hv.
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded v). pose proof (to_Z_bounded p).
  assert (B : ((φ u) * (φ p) + (φ v) < (φ p) * (φ p))%Z) by nia.
  split; [|exact B].
  rewrite add_spec, mul_spec.
  rewrite (Z.mod_small ((φ u) * (φ p))) by (rewrite wB_val; nia).
  apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma bool_set : forall (t : array bool) (a w : int),
  ((φ a) < (φ (PArray.length t)))%Z ->
  (t.[a <- true].[w] = true <-> a = w \/ t.[w] = true).
Proof.
  intros t a w Ha. destruct (Uint63.eqb_spec a w) as [E _].
  destruct (a =? w) eqn:Eq.
  - rewrite <- (E eq_refl). rewrite aget_same by exact Ha. tauto.
  - assert (N : a <> w) by (intro F; rewrite <- Uint63.eqb_spec in F; congruence).
    rewrite aget_other by exact N. tauto.
Qed.

Definition edge (y z K : array pstr) (p : int) (i u v : int) : Prop :=
  exists j : int, ((φ j) < (φ i))%Z /\
    ((u = look K p y.[j] /\ v = look K p z.[j]) \/
     (u = look K p z.[j] /\ v = look K p y.[j])).

Lemma fill_spec : forall (y z K : array pstr) (p m : int),
  ((φ p) * (φ p) <= 4194303)%Z ->
  (forall j, ((φ j) < (φ m))%Z ->
     ((φ (look K p y.[j])) < (φ p))%Z /\ ((φ (look K p z.[j])) < (φ p))%Z) ->
  forall (zz : Z) (i : int) (tbl : array bool) (H : Acc (Zwf 0) (gap m i)),
  gap m i = zz -> ((φ i) <= (φ m))%Z ->
  (φ (PArray.length tbl)) = ((φ p) * (φ p))%Z ->
  (forall u v, ((φ u) < (φ p))%Z -> ((φ v) < (φ p))%Z ->
     (tbl.[u * p + v] = true <-> edge y z K p i u v)) ->
  (φ (PArray.length (fill y z K p m i tbl H))) = ((φ p) * (φ p))%Z /\
  (forall u v, ((φ u) < (φ p))%Z -> ((φ v) < (φ p))%Z ->
     ((fill y z K p m i tbl H).[u * p + v] = true <-> edge y z K p m u v)).
Proof.
  intros y z K p m Hp Hid zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i tbl H Hz Him Hlen Hinv.
  rewrite fill_eq. destruct (bdec (i <? m)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Ei : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    cbv zeta.
    destruct (Hid i Hi') as [HU HV].
    set (U := look K p y.[i]) in *. set (V := look K p z.[i]) in *.
    destruct (idx_spec p U V Hp HU HV) as [I1 B1].
    destruct (idx_spec p V U Hp HV HU) as [I2 B2].
    apply (IH (gap m (i + 1))); [rewrite <- Hz; apply dec_step; exact Hi | reflexivity
      | lia | rewrite !alen_set; exact Hlen | ].
    intros u v Hu Hv.
    destruct (idx_spec p u v Hp Hu Hv) as [I3 B3].
    pose proof (to_Z_bounded u). pose proof (to_Z_bounded v).
    pose proof (to_Z_bounded U). pose proof (to_Z_bounded V).
    rewrite bool_set by (rewrite alen_set; lia).
    rewrite bool_set by lia.
    rewrite Hinv by assumption.
    split.
    + intros [E | [E | E]].
      * apply (f_equal to_Z) in E. rewrite I2, I3 in E.
        destruct (idx_inj (φ V) (φ U) (φ u) (φ v) (φ p) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E) as [E1 E2].
        exists i. split; [lia|]. right. split; apply int_eq; lia.
      * apply (f_equal to_Z) in E. rewrite I1, I3 in E.
        destruct (idx_inj (φ U) (φ V) (φ u) (φ v) (φ p) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E) as [E1 E2].
        exists i. split; [lia|]. left. split; apply int_eq; lia.
      * destruct E as [j [Hj Hj']]. exists j. split; [lia | exact Hj'].
    + intros [j [Hj Hj']]. destruct (Z.eq_dec (φ j) (φ i)) as [E|E].
      * rewrite (int_eq _ _ E) in Hj'. fold U V in Hj'.
        destruct Hj' as [[-> ->] | [-> ->]]; [right; left | left]; reflexivity.
      * right. right. exists j. split; [lia | exact Hj'].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    replace m with i by (apply int_eq; lia).
    split; [exact Hlen | exact Hinv].
Qed.

(* ------------------------------------------------------------------ *)
(* The colouring search                                                *)
(* ------------------------------------------------------------------ *)

Section Colour.

Variable tbl : array bool.
Variable p : int.

Definition adj (u v : int) : Prop := tbl.[u * p + v] = true.

Definition proper (g : int -> int) (q : int) : Prop :=
  forall u v, ((φ u) < (φ q))%Z -> ((φ v) < (φ q))%Z -> adj u v -> g u <> g v.

Definition bounded (g : int -> int) (k : int) : Prop :=
  forall u, ((φ u) < (φ p))%Z -> ((φ (g u)) < (φ k))%Z.

Definition colorable (k : int) : Prop :=
  exists g, proper g p /\ bounded g k.

Definition agree (g : int -> int) (col : array int) (v : int) : Prop :=
  forall u, ((φ u) < (φ v))%Z -> g u = col.[u].

Hypothesis Hsym : forall u v, ((φ u) < (φ p))%Z -> ((φ v) < (φ p))%Z -> adj u v -> adj v u.
Hypothesis Hnl : forall u, ((φ u) < (φ p))%Z -> ~ adj u u.

Lemma okc_true : forall (v c : int) (col : array int) (zz : Z) (u : int)
  (H : Acc (Zwf 0) (gap v u)), gap v u = zz ->
  okc tbl p v c col u H = true ->
  forall w, ((φ u) <= (φ w) < (φ v))%Z -> adj w v -> col.[w] <> c.
Proof.
  intros v c col zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u H Hz Ho w Hw Ha.
  rewrite okc_eq in Ho. destruct (bdec (u <? v)) as [Hu | Hu].
  - assert (Eu : (φ (u + 1)) = ((φ u) + 1)%Z) by (pose proof Hu as Hu'; rewrite ltb_spec in Hu'; sia).
    pose proof Hu as Hu'; rewrite ltb_spec in Hu'.
    destruct (andb tbl.[u * p + v] (col.[u] =? c)) eqn:Ea; [discriminate|].
    destruct (Z.eq_dec (φ w) (φ u)) as [E|E].
    + rewrite (int_eq _ _ E) in Ha |- *. unfold adj in Ha. rewrite Ha in Ea. simpl in Ea.
      intro F. rewrite <- Uint63.eqb_spec in F. congruence.
    + apply (IH (gap v (u + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hu)
               (u + 1) _ eq_refl Ho); [lia | exact Ha].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hu. lia.
Qed.

Lemma okc_complete : forall (v c : int) (col : array int) (zz : Z) (u : int)
  (H : Acc (Zwf 0) (gap v u)), gap v u = zz ->
  (forall w, ((φ u) <= (φ w) < (φ v))%Z -> adj w v -> col.[w] <> c) ->
  okc tbl p v c col u H = true.
Proof.
  intros v c col zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u H Hz Hall.
  rewrite okc_eq. destruct (bdec (u <? v)) as [Hu | Hu].
  - pose proof Hu as Hu'. rewrite ltb_spec in Hu'.
    assert (Eu : (φ (u + 1)) = ((φ u) + 1)%Z) by sia.
    destruct (andb tbl.[u * p + v] (col.[u] =? c)) eqn:Ea.
    + exfalso. apply andb_prop in Ea as [Ea1 Ea2]. rewrite Uint63.eqb_spec in Ea2.
      apply (Hall u); [lia | exact Ea1 | exact Ea2].
    + apply (IH (gap v (u + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hu)
               (u + 1) _ eq_refl).
      intros w Hw. apply Hall. lia.
  - reflexivity.
Qed.

Lemma lim_spec : forall used k : int,
  (((φ used) < (φ k))%Z /\ (φ (lim used k)) = ((φ used) + 1)%Z) \/
  (((φ k) <= (φ used))%Z /\ lim used k = k).
Proof.
  intros used k. unfold lim. destruct (used <? k) eqn:E.
  - left. rewrite ltb_spec in E. split; [exact E|]. sia.
  - right. rewrite <- Bool.not_true_iff_false, ltb_spec in E. split; [lia | reflexivity].
Qed.

Lemma bump_spec : forall used c k : int, ((φ c) < (φ k))%Z ->
  (φ (bump used c)) = Z.max (φ used) ((φ c) + 1).
Proof.
  intros used c k H. unfold bump.
  assert (E : (φ (c + 1)) = ((φ c) + 1)%Z) by sia.
  destruct (used <? c + 1) eqn:F;
    [rewrite ltb_spec in F | rewrite <- Bool.not_true_iff_false, ltb_spec in F]; lia.
Qed.

Lemma srch_frame : forall (k : int) (zz : Z) (v c used : int) (col : array int)
  (H : Acc (Zwf 0) (meas p k v c)), meas p k v c = zz ->
  PArray.length (snd (srch tbl p k v c used col H)) = PArray.length col /\
  (forall u, ((φ u) < (φ v))%Z -> (snd (srch tbl p k v c used col H)).[u] = col.[u]).
Proof.
  intros k zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v c used col H Hz.
  rewrite srch_eq. destruct (bdec (v <? p)) as [Hv | Hv]; [|split; reflexivity].
  destruct (bdec (c <? lim used k)) as [Hc | Hc]; [|split; reflexivity].
  pose proof Hv as Hv'. rewrite ltb_spec in Hv'.
  assert (Ev : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  destruct (okc tbl p v c col 0 (Zwf_well_founded 0 (gap v 0))).
  - destruct (IH _ ltac:(rewrite <- Hz; apply (dec_v p k v c used Hv Hc))
                (v + 1) 0 (bump used c) col.[v <- c] (Acc_inv H (dec_v p k v c used Hv Hc))
                eq_refl) as [F1 F2].
    destruct (srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                (Acc_inv H (dec_v p k v c used Hv Hc))) as [[|] col2]; simpl in F1, F2.
    + simpl. split; [rewrite F1; apply alen_set|].
      intros u Hu. rewrite F2 by lia. apply aget_other. apply int_neq. lia.
    + destruct (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
                  v (c + 1) used col2 (Acc_inv H (dec_c p k v c used Hv Hc)) eq_refl)
        as [G1 G2].
      split; [rewrite G1, F1; apply alen_set|].
      intros u Hu. rewrite G2, F2 by lia. apply aget_other. apply int_neq. lia.
  - destruct (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
                v (c + 1) used col (Acc_inv H (dec_c p k v c used Hv Hc)) eq_refl)
      as [G1 G2].
    split; [exact G1 | exact G2].
Qed.

Lemma proper_mono : forall g q q', ((φ q') <= (φ q))%Z -> proper g q -> proper g q'.
Proof. intros g q q' Hq Hg u v Hu Hv Ha. apply Hg; [lia | lia | exact Ha]. Qed.

Definition swap (a b x : int) : int := if x =? a then b else if x =? b then a else x.

Lemma eqb_dec : forall x y : int,
  ((x =? y) = true /\ x = y) \/ ((x =? y) = false /\ x <> y).
Proof.
  intros x y. destruct (x =? y) eqn:E.
  - left. split; [reflexivity|]. apply Uint63.eqb_spec. exact E.
  - right. split; [reflexivity|]. apply eqb_false_spec. exact E.
Qed.

Lemma swap_inj : forall a b x y, swap a b x = swap a b y -> x = y.
Proof.
  intros a b x y. unfold swap.
  destruct (eqb_dec x a) as [[R1 E1]|[R1 E1]]; destruct (eqb_dec y a) as [[R2 E2]|[R2 E2]];
  destruct (eqb_dec x b) as [[R3 E3]|[R3 E3]]; destruct (eqb_dec y b) as [[R4 E4]|[R4 E4]];
  rewrite ?R1, ?R2, ?R3, ?R4; intros F; congruence.
Qed.

Lemma normalize : forall (g : int -> int) (col : array int) (v used k : int),
  ((φ v) < (φ p))%Z -> proper g p -> bounded g k -> agree g col v ->
  (forall u, ((φ u) < (φ v))%Z -> ((φ (col.[u])) < (φ used))%Z) -> ((φ used) <= (φ k))%Z ->
  exists g', proper g' p /\ bounded g' k /\ agree g' col v /\
             ((φ (g' v)) < (φ (lim used k)))%Z.
Proof.
  intros g col v used k Hv Hp Hb Ha Hc Hu.
  destruct (Z_lt_le_dec (φ (g v)) (φ (lim used k))) as [L|L].
  { exists g. tauto. }
  pose proof (Hb v Hv) as Bv.
  destruct (lim_spec used k) as [[U1 U2] | [U1 U2]]; [| rewrite U2 in L; lia].
  rewrite U2 in L.
  exists (fun w => swap (g v) used (g w)).
  split; [|split; [|split]].
  - intros u w Hu' Hw' Hadj F. apply swap_inj in F. exact (Hp u w Hu' Hw' Hadj F).
  - intros u Hu'. unfold swap.
    destruct (g u =? g v); [lia|]. destruct (g u =? used); [lia|]. apply Hb. exact Hu'.
  - intros u Hu'. unfold swap. rewrite <- (Ha u Hu').
    pose proof (Hc u Hu') as Cu. rewrite <- (Ha u Hu') in Cu.
    destruct (g u =? g v) eqn:E1; [rewrite Uint63.eqb_spec in E1; rewrite E1 in Cu; lia|].
    destruct (g u =? used) eqn:E2; [rewrite Uint63.eqb_spec in E2; rewrite E2 in Cu; lia|].
    reflexivity.
  - unfold swap. rewrite Uint63.eqb_refl. rewrite U2. lia.
Qed.

Lemma srch_sound : forall (k : int) (zz : Z) (v c used : int) (col : array int)
  (H : Acc (Zwf 0) (meas p k v c)), meas p k v c = zz ->
  ((φ v) <= (φ p))%Z -> ((φ p) <= (φ (PArray.length col)))%Z ->
  (forall u, ((φ u) < (φ v))%Z -> ((φ (col.[u])) < (φ k))%Z) ->
  proper (fun u => col.[u]) v ->
  fst (srch tbl p k v c used col H) = true ->
  proper (fun u => (snd (srch tbl p k v c used col H)).[u]) p /\
  bounded (fun u => (snd (srch tbl p k v c used col H)).[u]) k.
Proof.
  intros k zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v c used col H Hz Hvp Hlen Hbd Hpr Hr.
  rewrite srch_eq in Hr |- *. destruct (bdec (v <? p)) as [Hv | Hv].
  2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hv. simpl.
      replace p with v by (apply int_eq; lia). split; [exact Hpr|].
      intros u Hu. apply Hbd. lia. }
  destruct (bdec (c <? lim used k)) as [Hc | Hc]; [|discriminate].
  pose proof Hv as Hv'. rewrite ltb_spec in Hv'.
  assert (Ev : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  pose proof (lim_le _ _ _ Hc) as Hck.
  destruct (okc tbl p v c col 0 (Zwf_well_founded 0 (gap v 0))) eqn:Eo.
  - pose proof (okc_true v c col _ 0 _ eq_refl Eo) as Ok.
    assert (Hpr1 : proper (fun u => col.[v <- c].[u]) (v + 1)).
    { intros u w Hu Hw Hadj.
      destruct (Z.eq_dec (φ u) (φ v)) as [Eu|Eu]; destruct (Z.eq_dec (φ w) (φ v)) as [Ew|Ew].
      - rewrite (int_eq _ _ Eu) in Hadj. rewrite (int_eq _ _ Ew) in Hadj.
        exfalso. exact (Hnl v Hv' Hadj).
      - rewrite (int_eq _ _ Eu) in Hadj |- *.
        rewrite aget_same by lia. rewrite aget_other by (apply int_neq; lia).
        intro F. apply (Ok w); [change (φ 0) with 0%Z; pose proof (to_Z_bounded w); lia | |].
        + apply Hsym; [lia | lia | exact Hadj].
        + symmetry. exact F.
      - rewrite (int_eq _ _ Ew) in Hadj |- *.
        rewrite aget_same by lia. rewrite aget_other by (apply int_neq; lia).
        apply (Ok u); [change (φ 0) with 0%Z; pose proof (to_Z_bounded u); lia | exact Hadj].
      - rewrite !aget_other by (apply int_neq; lia). apply Hpr; [lia | lia | exact Hadj]. }
    assert (Hbd1 : forall u, ((φ u) < (φ (v + 1)))%Z -> ((φ (col.[v <- c].[u])) < (φ k))%Z).
    { intros u Hu. destruct (Z.eq_dec (φ u) (φ v)) as [Eu|Eu].
      - rewrite (int_eq _ _ Eu), aget_same by lia. exact Hck.
      - rewrite aget_other by (apply int_neq; lia). apply Hbd. lia. }
    pose proof (IH _ ltac:(rewrite <- Hz; apply (dec_v p k v c used Hv Hc))
                (v + 1) 0 (bump used c) col.[v <- c] (Acc_inv H (dec_v p k v c used Hv Hc))
                eq_refl ltac:(lia) ltac:(rewrite alen_set; exact Hlen) Hbd1 Hpr1) as IH1.
    destruct (srch_frame k _ (v + 1) 0 (bump used c) col.[v <- c]
                (Acc_inv H (dec_v p k v c used Hv Hc)) eq_refl) as [F1 F2].
    destruct (srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                (Acc_inv H (dec_v p k v c used Hv Hc))) as [[|] col2]; simpl in IH1, F1, F2.
    + apply IH1. reflexivity.
    + apply (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
               v (c + 1) used col2 _ eq_refl ltac:(lia)).
      * rewrite F1, alen_set. exact Hlen.
      * intros u Hu. rewrite F2 by lia. rewrite aget_other by (apply int_neq; lia).
        apply Hbd. exact Hu.
      * intros u w Hu Hw Hadj. rewrite !F2 by lia. rewrite !aget_other by (apply int_neq; lia).
        apply Hpr; assumption.
      * exact Hr.
  - apply (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
             v (c + 1) used col _ eq_refl Hvp Hlen Hbd Hpr Hr).
Qed.

Lemma srch_complete : forall (k : int) (zz : Z) (v c used : int) (col : array int)
  (H : Acc (Zwf 0) (meas p k v c)), meas p k v c = zz ->
  ((φ v) <= (φ p))%Z -> ((φ p) <= (φ (PArray.length col)))%Z -> ((φ used) <= (φ k))%Z ->
  (forall u, ((φ u) < (φ v))%Z -> ((φ (col.[u])) < (φ used))%Z) ->
  (exists g, proper g p /\ bounded g k /\ agree g col v /\
     (((φ v) < (φ p))%Z -> ((φ c) <= (φ (g v)) < (φ (lim used k)))%Z)) ->
  fst (srch tbl p k v c used col H) = true.
Proof.
  intros k zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v c used col H Hz Hvp Hlen Hu Hcu [g (Gp & Gb & Ga & Gv)].
  rewrite srch_eq. destruct (bdec (v <? p)) as [Hv | Hv]; [|reflexivity].
  pose proof Hv as Hv'. rewrite ltb_spec in Hv'.
  specialize (Gv Hv').
  destruct (bdec (c <? lim used k)) as [Hc | Hc].
  2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hc. lia. }
  assert (Ev : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  pose proof (lim_le _ _ _ Hc) as Hck.
  assert (Ec1 : (φ (c + 1)) = ((φ c) + 1)%Z) by sia.
  assert (Hgc : g v = c -> okc tbl p v c col 0 (Zwf_well_founded 0 (gap v 0)) = true).
  { intros Eg. apply (okc_complete v c col _ 0 _ eq_refl).
    intros w Hw Hadj. rewrite <- (Ga w ltac:(lia)), <- Eg.
    apply Gp; [lia | lia | exact Hadj]. }
  destruct (okc tbl p v c col 0 (Zwf_well_founded 0 (gap v 0))) eqn:Eo.
  - destruct (srch_frame k _ (v + 1) 0 (bump used c) col.[v <- c]
                (Acc_inv H (dec_v p k v c used Hv Hc)) eq_refl) as [F1 F2].
    destruct (Z.eq_dec (φ (g v)) (φ c)) as [Eg|Eg].
    + pose proof (int_eq _ _ Eg) as Eg'.
      pose proof (bump_spec used c k Hck) as Eb.
      assert (Hag1 : agree g col.[v <- c] (v + 1)).
      { intros u Hu'. destruct (Z.eq_dec (φ u) (φ v)) as [Eu|Eu].
        - rewrite (int_eq _ _ Eu), aget_same by lia. exact Eg'.
        - rewrite aget_other by (apply int_neq; lia). apply Ga. lia. }
      assert (Hcu1 : forall u, ((φ u) < (φ (v + 1)))%Z -> ((φ (col.[v <- c].[u])) < (φ (bump used c)))%Z).
      { intros u Hu'. destruct (Z.eq_dec (φ u) (φ v)) as [Eu|Eu].
        - rewrite (int_eq _ _ Eu), aget_same by lia. lia.
        - rewrite aget_other by (apply int_neq; lia). pose proof (Hcu u ltac:(lia)). lia. }
      assert (R : fst (srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                     (Acc_inv H (dec_v p k v c used Hv Hc))) = true).
      { apply (IH _ ltac:(rewrite <- Hz; apply (dec_v p k v c used Hv Hc))
                 (v + 1) 0 (bump used c) col.[v <- c] _ eq_refl ltac:(lia)
                 ltac:(rewrite alen_set; exact Hlen) ltac:(lia) Hcu1).
        destruct (Z_lt_le_dec (φ (v + 1)) (φ p)) as [L|L].
        - destruct (normalize g col.[v <- c] (v + 1) (bump used c) k L Gp Gb Hag1 Hcu1
                      ltac:(lia)) as [g' (G1 & G2 & G3 & G4)].
          exists g'. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
          intros _. change (φ 0) with 0%Z. pose proof (to_Z_bounded (g' (v + 1))). lia.
        - exists g. split; [exact Gp|]. split; [exact Gb|]. split; [exact Hag1|].
          intros F. lia. }
      destruct (srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                  (Acc_inv H (dec_v p k v c used Hv Hc))) as [[|] col2];
        simpl in R; [reflexivity | discriminate].
    + destruct (srch tbl p k (v + 1) 0 (bump used c) col.[v <- c]
                  (Acc_inv H (dec_v p k v c used Hv Hc))) as [[|] col2];
        simpl in F1, F2; [reflexivity|].
      apply (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
               v (c + 1) used col2 _ eq_refl Hvp).
      * rewrite F1, alen_set. exact Hlen.
      * exact Hu.
      * intros u Hu'. rewrite F2 by lia. rewrite aget_other by (apply int_neq; lia).
        apply Hcu. exact Hu'.
      * exists g. split; [exact Gp|]. split; [exact Gb|]. split.
        -- intros u Hu'. rewrite F2 by lia. rewrite aget_other by (apply int_neq; lia).
           apply Ga. exact Hu'.
        -- intros _. lia.
  - assert (Eg : g v <> c) by (intro F; specialize (Hgc F); discriminate).
    apply (IH _ ltac:(rewrite <- Hz; apply (dec_c p k v c used Hv Hc))
             v (c + 1) used col _ eq_refl Hvp Hlen Hu Hcu).
    exists g. split; [exact Gp|]. split; [exact Gb|]. split; [exact Ga|].
    intros _. assert ((φ (g v)) <> (φ c)) by (intro F; apply Eg; apply int_eq; exact F). lia.
Qed.

Lemma colorable_id : forall P : int, ((φ p) <= (φ P))%Z -> colorable P.
Proof.
  intros P HP. exists (fun u => u). split.
  - intros u v Hu Hv Hadj E. subst v. exact (Hnl u Hu Hadj).
  - intros u Hu. lia.
Qed.

Lemma deepen_spec : forall (P : int) (zz : Z) (k : int) (col : array int)
  (H : Acc (Zwf 0) (gap P k)), gap P k = zz ->
  (1 <= (φ k) <= (φ P))%Z -> ((φ p) <= (φ P))%Z -> ((φ p) <= (φ (PArray.length col)))%Z ->
  (forall k', (1 <= (φ k') < (φ k))%Z -> ~ colorable k') ->
  (1 <= (φ (deepen tbl p P k col H)))%Z /\ colorable (deepen tbl p P k col H) /\
  (forall k', (1 <= (φ k') < (φ (deepen tbl p P k col H)))%Z -> ~ colorable k').
Proof.
  intros P zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k col H Hz Hk HpP Hlen Hmin.
  rewrite deepen_eq. destruct (bdec (k <? P)) as [Hk' | Hk'].
  - pose proof Hk' as Hk''. rewrite ltb_spec in Hk''.
    assert (Ek : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    pose proof (srch_sound k _ 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded p); lia) Hlen
                  ltac:(intros u Hu; change (φ 0) with 0%Z in Hu; pose proof (to_Z_bounded u); lia)
                  ltac:(intros u v Hu; change (φ 0) with 0%Z in Hu; pose proof (to_Z_bounded u); lia))
      as So.
    assert (Co : colorable k ->
                 fst (srch tbl p k 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0))) = true).
    { intros [g [Gp Gb]].
      apply (srch_complete k _ 0 0 0 col _ eq_refl
               ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded p); lia) Hlen
               ltac:(change (φ 0) with 0%Z; lia)
               ltac:(intros u Hu; change (φ 0) with 0%Z in Hu; pose proof (to_Z_bounded u); lia)).
      destruct (Z_lt_le_dec 0 (φ p)) as [L|L].
      - destruct (normalize g col 0 0 k L Gp Gb
                    ltac:(intros u Hu; change (φ 0) with 0%Z in Hu; pose proof (to_Z_bounded u); lia)
                    ltac:(intros u Hu; change (φ 0) with 0%Z in Hu; pose proof (to_Z_bounded u); lia)
                    ltac:(change (φ 0) with 0%Z; lia)) as [g' (G1 & G2 & G3 & G4)].
        exists g'. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
        intros _. change (φ 0) with 0%Z. pose proof (to_Z_bounded (g' 0)). lia.
      - exists g. split; [exact Gp|]. split; [exact Gb|]. split.
        + intros u Hu. change (φ 0) with 0%Z in Hu. pose proof (to_Z_bounded u). lia.
        + intros F. change (φ 0) with 0%Z in F. lia. }
    destruct (srch_frame k _ 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0)) eq_refl) as [F1 _].
    destruct (srch tbl p k 0 0 0 col (Zwf_well_founded 0 (meas p k 0 0))) as [[|] col2];
      simpl in So, Co, F1.
    + split; [lia|]. split; [|exact Hmin].
      exists (fun u => col2.[u]). apply So. reflexivity.
    + apply (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hk') (k + 1) col2 _ eq_refl
               ltac:(lia) HpP ltac:(rewrite F1; exact Hlen)).
      intros k' Hk1. destruct (Z.eq_dec (φ k') (φ k)) as [E|E].
      * rewrite (int_eq _ _ E). intros C. specialize (Co C). discriminate.
      * apply Hmin. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk'.
    replace P with k in * by (apply int_eq; lia).
    split; [lia|]. split; [apply colorable_id; exact HpP | exact Hmin].
Qed.

End Colour.

(* ------------------------------------------------------------------ *)
(* Strings and arrays: the machine side against the math side          *)
(* ------------------------------------------------------------------ *)

Lemma arr_len : forall (y : array@{Set} pstr) (a : list String.string), repr y a ->
  (φ (PArray.length@{Set} y)) = Z.of_nat (List.length a).
Proof. intros y a [Hl _]. symmetry. exact Hl. Qed.

Lemma arr_get : forall (y : array@{Set} pstr) (a : list String.string), repr y a ->
  forall j : int, ((φ j) < Z.of_nat (List.length a))%Z ->
  repr (PArray.get@{Set} y j) (nth (Z.to_nat (φ j)) a String.EmptyString).
Proof.
  intros y a [Hl Hc] j Hj.
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hr).
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded j); lia).
  rewrite of_to_Z in Hr. rewrite (nth_error_nth _ _ _ Hm). exact Hr.
Qed.

Lemma repr_inj_r : forall (x x' : pstr) (s : String.string),
  repr x s -> repr x' s -> x = x'.
Proof.
  intros x x' s [L1 C1] [L2 C2].
  apply PString.string_eq_ext. split.
  - apply int_eq. lia.
  - intros i Hi. pose proof (to_Z_bounded i) as Bi.
    destruct (C1 (Z.to_nat (φ i)) ltac:(lia)) as (c1 & G1 & R1).
    destruct (C2 (Z.to_nat (φ i)) ltac:(lia)) as (c2 & G2 & R2).
    rewrite G1 in G2. injection G2 as <-.
    unfold repr, repr_uint in R1, R2.
    rewrite Z2Nat.id, of_to_Z in R1, R2 by lia.
    apply int_eq. rewrite <- R2 in R1.
    pose proof (to_Z_bounded (PrimString.get x i)).
    pose proof (to_Z_bounded (PrimString.get x' i)).
    apply Z2N.inj; [lia | lia | exact R1].
Qed.

Definition toS (x : pstr) : String.string :=
  String.string_of_list_ascii
    (map (fun ch => Ascii.ascii_of_N (Z.to_N (φ ch))) (PrimStringAxioms.to_list x)).

Lemma get_sola : forall (l : list Ascii.ascii) (n : nat),
  String.get n (String.string_of_list_ascii l) = nth_error l n.
Proof. induction l as [|h t IH]; intros [|n]; simpl; try reflexivity. apply IH. Qed.

Lemma get_beyond : forall (s : String.string) (n : nat),
  (String.length s <= n)%nat -> String.get n s = None.
Proof.
  induction s as [|h t IH]; intros [|n] Hn; simpl in *; try reflexivity; [lia|].
  apply IH. lia.
Qed.

Lemma repr_toS : forall (x : pstr) (s : String.string), repr x s -> toS x = s.
Proof.
  intros x s [L C]. apply String.get_correct. intros n.
  unfold toS. rewrite get_sola, nth_error_map.
  pose proof (PrimStringAxioms.length_spec x) as Ls.
  destruct (Nat.lt_ge_cases n (String.length s)) as [Hn|Hn].
  - destruct (C n Hn) as (c & G & R). rewrite G.
    unfold repr, repr_uint in R.
    assert (Hi : (φ (of_Z (Z.of_nat n))) = Z.of_nat n).
    { rewrite of_Z_spec. apply Z.mod_small. pose proof (to_Z_bounded (PrimString.length x)). lia. }
    destruct (PString.get_spec_in_bounds x (of_Z (Z.of_nat n)) ltac:(lia)) as [_ E].
    rewrite Hi, Nat2Z.id in E.
    assert (E' : @nth_error PrimInt63.int (PrimStringAxioms.to_list x) n
                 = Some (PrimString.get x (of_Z (Z.of_nat n)))) by exact E.
    rewrite E'. simpl. rewrite R. f_equal.
    apply Ascii.ascii_N_embedding.
  - rewrite get_beyond by exact Hn.
    assert (E' : @nth_error PrimInt63.int (PrimStringAxioms.to_list x) n = None)
      by (assert (Ls' : to_nat (PrimString.length x)
                        = @Datatypes.length PrimInt63.int (PrimStringAxioms.to_list x)) by exact Ls;
          apply nth_error_None; lia).
    rewrite E'. reflexivity.
Qed.

Fixpoint idx_of (x : String.string) (l : list String.string) : option nat :=
  match l with
  | [] => None
  | h :: t => if String.eqb h x then Some O else option_map S (idx_of x t)
  end.

Lemma idx_of_some : forall x l j, idx_of x l = Some j ->
  (j < List.length l)%nat /\ nth j l String.EmptyString = x.
Proof.
  intros x l. induction l as [|h t IH]; intros j E; simpl in E; [discriminate|].
  destruct (String.eqb h x) eqn:Eh.
  - injection E as <-. apply String.eqb_eq in Eh. simpl. split; [lia | exact Eh].
  - destruct (idx_of x t) as [j'|] eqn:E'; simpl in E; [|discriminate].
    injection E as <-. destruct (IH j' eq_refl) as [A B]. simpl. split; [lia | exact B].
Qed.

Lemma idx_of_in : forall x l, In x l -> exists j, idx_of x l = Some j.
Proof.
  intros x l. induction l as [|h t IH]; intros Hin; [destruct Hin|].
  simpl. destruct (String.eqb h x) eqn:Eh; [eexists; reflexivity|].
  destruct Hin as [<- | Hin]; [rewrite String.eqb_refl in Eh; discriminate|].
  destruct (IH Hin) as [j Ej]. rewrite Ej. eexists. reflexivity.
Qed.

(* The committee of a name, read off the colour of the member it denotes. *)
Definition pick (a b : list String.string) (y z : array pstr) (F : pstr -> N)
    (x : String.string) : N :=
  match idx_of x a with
  | Some j => F (y.[of_Z (Z.of_nat j)])
  | None =>
      match idx_of x b with
      | Some j => F (z.[of_Z (Z.of_nat j)])
      | None => 0%N
      end
  end.

Lemma of_nat_small : forall j : nat, (Z.of_nat j <= 4194303)%Z ->
  (φ (of_Z (Z.of_nat j))) = Z.of_nat j.
Proof. intros j H. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma pick_spec : forall a b (y z : array pstr) (F : pstr -> N),
  repr y a -> repr z b ->
  (forall j : int, ((φ j) < Z.of_nat (List.length a))%Z ->
     pick a b y z F (nth (Z.to_nat (φ j)) a String.EmptyString) = F (y.[j])) /\
  (forall j : int, ((φ j) < Z.of_nat (List.length b))%Z ->
     pick a b y z F (nth (Z.to_nat (φ j)) b String.EmptyString) = F (z.[j])).
Proof.
  intros a b y z F Hy Hz.
  pose proof (arr_len y a Hy) as Ly. pose proof (arr_len z b Hz) as Lz.
  pose proof (alen_bound y). pose proof (alen_bound z).
  assert (Ka : forall x (j' : nat), idx_of x a = Some j' ->
     repr (y.[of_Z (Z.of_nat j')]) x).
  { intros x j' E. destruct (idx_of_some _ _ _ E) as [A B].
    assert (Q : (φ (of_Z (Z.of_nat j'))) = Z.of_nat j') by (apply of_nat_small; lia).
    pose proof (arr_get y a Hy (of_Z (Z.of_nat j')) ltac:(rewrite Q; lia)) as R.
    rewrite Q, Nat2Z.id, B in R. exact R. }
  assert (Kb : forall x (j' : nat), idx_of x b = Some j' ->
     repr (z.[of_Z (Z.of_nat j')]) x).
  { intros x j' E. destruct (idx_of_some _ _ _ E) as [A B].
    assert (Q : (φ (of_Z (Z.of_nat j'))) = Z.of_nat j') by (apply of_nat_small; lia).
    pose proof (arr_get z b Hz (of_Z (Z.of_nat j')) ltac:(rewrite Q; lia)) as R.
    rewrite Q, Nat2Z.id, B in R. exact R. }
  split.
  - intros j Hj. pose proof (arr_get y a Hy j Hj) as R. pose proof (to_Z_bounded j).
    unfold pick.
    assert (Hin : In (nth (Z.to_nat (φ j)) a String.EmptyString) a) by (apply nth_In; lia).
    destruct (idx_of_in _ a Hin) as [j' E].
    rewrite E. f_equal. exact (repr_inj_r _ _ _ (Ka _ _ E) R).
  - intros j Hj. pose proof (arr_get z b Hz j Hj) as R. pose proof (to_Z_bounded j).
    unfold pick.
    destruct (idx_of (nth (Z.to_nat (φ j)) b String.EmptyString) a) as [j'|] eqn:E.
    + f_equal. exact (repr_inj_r _ _ _ (Ka _ _ E) R).
    + assert (Hin : In (nth (Z.to_nat (φ j)) b String.EmptyString) b) by (apply nth_In; lia).
      destruct (idx_of_in _ b Hin) as [j' E'].
      rewrite E'. f_equal. exact (repr_inj_r _ _ _ (Kb _ _ E') R).
Qed.

Lemma Forall2_nth' : forall {A B} (R : A -> B -> Prop) l1 l2 d1 d2,
  Forall2 R l1 l2 -> forall k, (k < List.length l1)%nat -> R (nth k l1 d1) (nth k l2 d2).
Proof.
  intros A B R l1 l2 d1 d2 H. induction H as [|x y l1 l2 Hxy H IH]; intros k Hk;
    simpl in Hk; [lia|].
  destruct k as [|k]; simpl; [exact Hxy | apply IH; lia].
Qed.

Lemma Forall2_of_nth : forall {A B} (R : A -> B -> Prop) l1 l2 d1 d2,
  List.length l1 = List.length l2 ->
  (forall k, (k < List.length l1)%nat -> R (nth k l1 d1) (nth k l2 d2)) ->
  Forall2 R l1 l2.
Proof.
  intros A B R l1. induction l1 as [|x l1 IH]; intros [|y l2] d1 d2 Hl Hn;
    simpl in Hl; try discriminate; constructor.
  - apply (Hn O). simpl. lia.
  - apply (IH l2 d1 d2); [lia|]. intros k Hk. apply (Hn (S k)). simpl. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma committees_impl_correct : forall (n : N) (a b : list String.string)
  (x : uint) (y z : array PrimString.string),
  valid_input n a b -> repr x n -> repr y a -> repr z b ->
  exists k : N, repr (committees_impl x y z) k /\ committees_spec n a b k.
Proof.
  intros n a b x y z Hv _ Hy Hz.
  destruct Hv as [Vn Vm Vp Vd _ _ _].
  unfold len in Vm, Vp.
  assert (Hm105 : (N.of_nat (List.length a) <= 105)%N).
  { assert (n * (n - 1) <= 15 * 14)%N by (apply N.mul_le_mono; lia).
    assert (n * (n - 1) / 2 <= 105)%N by (apply N.div_le_upper_bound; lia).
    lia. }
  pose proof (arr_len y a Hy) as Ly. pose proof (arr_len z b Hz) as Lz.
  assert (Lab : List.length b = List.length a) by lia.
  unfold committees_impl.
  set (m := PArray.length y).
  assert (Hm : (φ m) = Z.of_nat (List.length a)) by exact Ly.
  assert (Hmz : (φ (PArray.length z)) = (φ m)) by lia.
  assert (Hm' : ((φ m) <= 105)%Z) by lia.
  pose proof (to_Z_bounded m) as Bm.
  assert (Hmm : (φ (m + m)) = (2 * (φ m))%Z) by sia.
  (* naming *)
  destruct (build y z m 0 (PArray.make (m + m) ""%pstring) 0
              (Zwf_well_founded 0 (gap m 0))) as [K p] eqn:Eb.
  destruct (build_spec y z m ltac:(lia) _ 0 (PArray.make (m + m) ""%pstring) 0
              (Zwf_well_founded 0 (gap m 0)) K p eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alen_make by lia; exact Hmm)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros i j Hij; change (φ 0) with 0%Z in Hij; pose proof (to_Z_bounded i); lia)
              ltac:(intros j Hj; change (φ 0) with 0%Z in Hj; pose proof (to_Z_bounded j); lia)
              Eb) as (BK & Bp & Bs & Bmem).
  pose proof (to_Z_bounded p) as Bp0.
  assert (Hpp : ((φ p) * (φ p) <= 4194303)%Z) by nia.
  assert (Epp : (φ (p * p)) = ((φ p) * (φ p))%Z)
    by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; nia).
  assert (Hfy : forall j, ((φ j) < (φ m))%Z ->
            ((φ (look K p y.[j])) < (φ p))%Z /\ K.[look K p y.[j]] = y.[j])
    by (intros j Hj; apply look_found; [exact Bs | apply Bmem; exact Hj]).
  assert (Hfz : forall j, ((φ j) < (φ m))%Z ->
            ((φ (look K p z.[j])) < (φ p))%Z /\ K.[look K p z.[j]] = z.[j])
    by (intros j Hj; apply look_found; [exact Bs | apply Bmem; exact Hj]).
  assert (Hid : forall j, ((φ j) < (φ m))%Z ->
            ((φ (look K p y.[j])) < (φ p))%Z /\ ((φ (look K p z.[j])) < (φ p))%Z)
    by (intros j Hj; split; [apply Hfy | apply Hfz]; exact Hj).
  (* the math names of pair j *)
  assert (Ta : forall j, ((φ j) < (φ m))%Z ->
            toS y.[j] = nth (Z.to_nat (φ j)) a String.EmptyString)
    by (intros j Hj; apply repr_toS; apply arr_get; [exact Hy | lia]).
  assert (Tb : forall j, ((φ j) < (φ m))%Z ->
            toS z.[j] = nth (Z.to_nat (φ j)) b String.EmptyString)
    by (intros j Hj; apply repr_toS; apply arr_get; [exact Hz | lia]).
  assert (Sep : forall j, ((φ j) < (φ m))%Z ->
            nth (Z.to_nat (φ j)) a String.EmptyString <>
            nth (Z.to_nat (φ j)) b String.EmptyString).
  { intros j Hj. apply (Forall2_nth' _ a b _ _ Vd). lia. }
  cbv beta iota zeta.
  (* the conflict table *)
  destruct (fill_spec y z K p m Hpp Hid _ 0 (PArray.make (p * p) false)
              (Zwf_well_founded 0 (gap m 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alen_make by lia; exact Epp)) as [Tl Ti].
  { intros u v Hu Hv. rewrite aget_make. split; [discriminate|].
    intros [j [Hj _]]. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia. }
  set (tbl := fill y z K p m 0 (PArray.make (p * p) false) (Zwf_well_founded 0 (gap m 0))) in *.
  assert (Hsym : forall u v, ((φ u) < (φ p))%Z -> ((φ v) < (φ p))%Z -> adj tbl p u v -> adj tbl p v u).
  { intros u v Hu Hv. unfold adj. rewrite !Ti by assumption.
    intros [j [Hj [[-> ->] | [-> ->]]]]; exists j; split; auto. }
  assert (Hnl : forall u, ((φ u) < (φ p))%Z -> ~ adj tbl p u u).
  { intros u Hu. unfold adj. rewrite Ti by assumption.
    intros [j [Hj Hor]].
    assert (E : look K p y.[j] = look K p z.[j]) by (destruct Hor as [[E1 E2]|[E1 E2]]; congruence).
    destruct (Hfy j Hj) as [_ Ky]. destruct (Hfz j Hj) as [_ Kz].
    apply (Sep j Hj). rewrite <- (Ta j Hj), <- (Tb j Hj), <- Ky, <- Kz, E. reflexivity. }
  (* the colouring *)
  set (P := if p <? 1 then 1 else p) in *.
  assert (HP : (1 <= (φ P))%Z /\ ((φ p) <= (φ P))%Z /\ ((φ P) <= 210)%Z).
  { unfold P. destruct (p <? 1) eqn:E; [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E];
      change (φ 1) with 1%Z in *; lia. }
  destruct HP as (HP1 & HP2 & HP3).
  destruct (deepen_spec tbl p Hsym Hnl P _ 1 (PArray.make P 0) (Zwf_well_founded 0 (gap P 1))
              eq_refl ltac:(change (φ 1) with 1%Z; lia) HP2
              ltac:(rewrite alen_make by lia; exact HP2)
              ltac:(intros k' Hk'; change (φ 1) with 1%Z in Hk'; lia)) as (D1 & D2 & D3).
  set (r := deepen tbl p P 1 (PArray.make P 0) (Zwf_well_founded 0 (gap P 1))) in *.
  assert (Hr : ((φ r) <= 210)%Z).
  { destruct (Z_le_gt_dec (φ r) (φ P)) as [L|L]; [lia|].
    exfalso. apply (D3 P); [lia|]. apply colorable_id; [exact Hnl | lia]. }
  exists (Z.to_N (φ r)). split; [reflexivity|].
  split.
  - (* r committees suffice *)
    destruct D2 as [g [Gp Gb]].
    set (F := fun s : pstr => Z.to_N (φ (g (look K p s)))).
    destruct (pick_spec a b y z F Hy Hz) as [Pa Pb].
    assert (Hk : forall k : nat, (k < List.length a)%nat ->
              exists j : int, ((φ j) < (φ m))%Z /\ Z.to_nat (φ j) = k).
    { intros k Hk. exists (of_Z (Z.of_nat k)). rewrite of_nat_small by lia. split; lia. }
    exists (pick a b y z F). split; [split|].
    + change 0%N with (Z.to_N 0). apply Z2N.inj_lt; lia.
    + intros s [Hin|Hin]; apply (In_nth _ _ String.EmptyString) in Hin as [k [Hk' <-]].
      * destruct (Hk k Hk') as [j [Hj <-]]. rewrite Pa by lia. unfold F.
        pose proof (Gb _ (proj1 (Hfy j Hj))) as H. match goal with |- (Z.to_N (φ ?X) < _)%N => pose proof (to_Z_bounded X) end.
        apply Z2N.inj_lt; [lia | lia | exact H].
      * rewrite Lab in Hk'. destruct (Hk k Hk') as [j [Hj <-]]. rewrite Pb by lia. unfold F.
        pose proof (Gb _ (proj1 (Hfz j Hj))) as H. match goal with |- (Z.to_N (φ ?X) < _)%N => pose proof (to_Z_bounded X) end.
        apply Z2N.inj_lt; [lia | lia | exact H].
    + apply (Forall2_of_nth _ _ _ String.EmptyString String.EmptyString); [lia|].
      intros k Hk'. destruct (Hk k Hk') as [j [Hj <-]].
      rewrite Pa, Pb by lia. unfold F. intros E.
      assert (Ad : adj tbl p (look K p y.[j]) (look K p z.[j])).
      { unfold adj. rewrite Ti by (apply Hid; exact Hj).
        exists j. split; [exact Hj|]. left. split; reflexivity. }
      apply (Gp _ _ (proj1 (Hfy j Hj)) (proj1 (Hfz j Hj)) Ad).
      pose proof (to_Z_bounded (g (look K p y.[j]))).
      pose proof (to_Z_bounded (g (look K p z.[j]))).
      apply int_eq. apply Z2N.inj; [lia | lia | exact E].
  - (* no fewer *)
    intros k' [c [[Hk0 Hc] Hsep]].
    destruct (N.le_gt_cases (Z.to_N (φ r)) k') as [Le|Gt]; [exact Le|]. exfalso.
    assert (Gt' : (Z.of_N k' < (φ r))%Z)
      by (rewrite <- (Z2N.id (φ r)) by lia; apply N2Z.inj_lt; exact Gt).
    clear Gt.
    assert (EK : (φ (of_Z (Z.of_N k'))) = Z.of_N k')
      by (rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
    apply (D3 (of_Z (Z.of_N k'))); [lia|].
    assert (Small : forall v : N, (v < k')%N -> (φ (of_Z (Z.of_N v))) = Z.of_N v)
      by (intros v Hv'; rewrite of_Z_spec; apply Z.mod_small; rewrite wB_val; lia).
    exists (fun u => if (c (toS K.[u]) <? k')%N then of_Z (Z.of_N (c (toS K.[u]))) else 0).
    split.
    + intros u v Hu Hv Hadj. unfold adj in Hadj. rewrite Ti in Hadj by assumption.
      destruct Hadj as [j [Hj Hor]].
      destruct (Hfy j Hj) as [_ Ky]. destruct (Hfz j Hj) as [_ Kz].
      assert (Ca : (c (nth (Z.to_nat (φ j)) a String.EmptyString) < k')%N)
        by (apply Hc; left; apply nth_In; lia).
      assert (Cb : (c (nth (Z.to_nat (φ j)) b String.EmptyString) < k')%N)
        by (apply Hc; right; apply nth_In; lia).
      assert (Cs : c (nth (Z.to_nat (φ j)) a String.EmptyString) <>
                   c (nth (Z.to_nat (φ j)) b String.EmptyString))
        by (apply (Forall2_nth' _ a b _ _ Hsep); lia).
      pose proof (proj2 (N.ltb_lt _ _) Ca) as Ca'. pose proof (proj2 (N.ltb_lt _ _) Cb) as Cb'.
      destruct Hor as [[-> ->] | [-> ->]];
        rewrite ?Ky, ?Kz, (Ta j Hj), (Tb j Hj), Ca', Cb'; intros E;
        apply (f_equal to_Z) in E; rewrite !Small in E by assumption; lia.
    + intros u Hu. rewrite EK.
      destruct (c (toS K.[u]) <? k')%N eqn:E.
      * apply N.ltb_lt in E. rewrite Small by exact E. lia.
      * change (φ 0) with 0%Z. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition committees : uint -> array PrimString.string -> array PrimString.string -> uint :=
  committees_impl.
Elpi complexity committees.

Definition committees_correct : forall (n : N) (a b : list String.string)
         (x : uint) (y z : array PrimString.string),
  valid_input n a b -> repr x n -> repr y a -> repr z b ->
  exists k : N, repr (committees x y z) k /\ committees_spec n a b k
  := committees_impl_correct.

(* ================================================================== *)
(* Cost: the bound committees_time                                     *)
(* ================================================================== *)

(* The cost translation is the Elpi complexity lines next to the
   program (sumbool, bdec, midp, lb, look, shift, is_eq, andb, insert,
   build, fill, okc, lim, bump, srch, deepen, committees_impl) and the
   one after committees.  One lemma per loop, by induction on a nat bound
   of its Z measure.  The naming phase is bounded through the size p of
   the names table, which never shrinks (build_mono) and holds only
   listed names, so p <= n (build_extra, table_le_n: a pigeonhole on the
   department's NoDup member list).  The colouring search srch is bounded
   by SB/GB: at member v with R = p - v members left and colour c,
   at most (k - c) * (M + GB R-1) + M steps, M = 50 p + 300 the work of
   one node (okc scans the v earlier members); GB R + M <= 2 M (k+1)^R. *)

Lemma build_mono : forall (y z : array pstr) (m : int),
  forall (zz : Z) (i : int) (K : array pstr) (p : int) (H : Acc (Zwf 0) (gap m i)),
  gap m i = zz -> ((φ i) <= (φ m))%Z ->
  (φ (PArray.length K)) = (2 * (φ m))%Z -> ((φ p) <= 2 * (φ i))%Z -> sorted K p ->
  ((φ p) <= (φ (snd (build y z m i K p H))))%Z.
Proof.
  intros y z m zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i K p H Hz Him HK Hp Hs.
  rewrite build_eq. destruct (bdec (i <? m)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Ei : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (insert K p y.[i]) as [K1 p1] eqn:E1.
    destruct (insert K1 p1 z.[i]) as [K2 p2] eqn:E2.
    destruct (insert_spec K p y.[i] K1 p1 Hs ltac:(lia) E1) as (A1 & A2 & A3 & A4 & A5).
    destruct (insert_spec K1 p1 z.[i] K2 p2 A3 ltac:(rewrite A1; lia) E2)
      as (B1 & B2 & B3 & B4 & B5).
    pose proof (IH (gap m (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hi) (i + 1) K2 p2 (Acc_inv H (dec_step m i Hi)) eq_refl
       ltac:(lia) ltac:(rewrite B1, A1; exact HK) ltac:(lia) B3). lia.
  - cbn. lia.
Qed.

Lemma build_unfold : forall y z m i K p H (e : (i <? m) = true) K1 p1 K2 p2,
  insert K p y.[i] = (K1, p1) -> insert K1 p1 z.[i] = (K2, p2) ->
  build y z m i K p H = build y z m (i + 1) K2 p2 (Acc_inv H (dec_step m i e)).
Proof.
  intros y z m i K p H e K1 p1 K2 p2 E1 E2. rewrite build_eq.
  destruct (bdec (i <? m)) as [e'|e']; [|congruence].
  assert (e' = e) by apply Eqdep_dec.UIP_dec, Bool.bool_dec. subst e'.
  rewrite E1, E2. reflexivity.
Qed.

(* Prop side for the cost: the names table only grows, and holds only listed names. *)

Lemma insert_src : forall (K : array pstr) (p : int) (s : pstr) K' p',
  sorted K p -> ((φ p) < (φ (PArray.length K)))%Z ->
  insert K p s = (K', p') ->
  forall t, ((φ t) < (φ p'))%Z ->
  K'.[t] = s \/ exists t0, ((φ t0) < (φ p))%Z /\ K'.[t] = K.[t0].
Proof.
  intros K p s K' p' Hs Hp Hins. unfold insert in Hins.
  destruct (look_spec K p s Hs) as (R1 & R2 & R3).
  set (t := look K p s) in *.
  pose proof (to_Z_bounded t) as Bt. pose proof (to_Z_bounded p) as Bp.
  destruct (andb (t <? p) (is_eq (PrimString.compare K.[t] s))) eqn:Ef.
  - injection Hins as <- <-. intros i Hi. right. exists i. split; [exact Hi | reflexivity].
  - injection Hins as <- <-.
    assert (Hp1 : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
    destruct (shift_spec _ K t p (Zwf_well_founded 0 (gap p t)) eq_refl ltac:(lia) Hp)
      as (S1 & S2 & S3).
    set (K1 := shift K t p (Zwf_well_founded 0 (gap p t))) in *.
    intros i Hi. rewrite Hp1 in Hi. pose proof (to_Z_bounded i) as Bi.
    destruct (Z.eq_dec (φ i) (φ t)) as [E|E].
    + left. rewrite (int_eq _ _ E). apply aget_same. rewrite S1. lia.
    + right. rewrite aget_other by (apply int_neq; lia).
      destruct (Z_lt_le_dec (φ i) (φ t)) as [L|L].
      * exists i. split; [lia|]. apply S3. lia.
      * exists (i - 1). assert (Ei1 : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
        split; [lia|]. apply S2. lia.
Qed.

Definition src (y z K : array pstr) (i p : int) : Prop :=
  forall t, ((φ t) < (φ p))%Z -> exists j, ((φ j) < (φ i))%Z /\ (K.[t] = y.[j] \/ K.[t] = z.[j]).

Lemma build_extra : forall (y z : array pstr) (m : int),
  ((φ m) <= 4194303)%Z ->
  forall (zz : Z) (i : int) (K : array pstr) (p : int) (H : Acc (Zwf 0) (gap m i)) K' p',
  gap m i = zz -> ((φ i) <= (φ m))%Z ->
  (φ (PArray.length K)) = (2 * (φ m))%Z -> ((φ p) <= 2 * (φ i))%Z -> sorted K p ->
  src y z K i p ->
  build y z m i K p H = (K', p') ->
  ((φ p) <= (φ p'))%Z /\ src y z K' m p'.
Proof.
  intros y z m Hm zz.
  induction zz as [zz IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i K p H K' p' Hz Him HK Hp Hs Hsrc Hb.
  rewrite build_eq in Hb. destruct (bdec (i <? m)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Ei : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (insert K p y.[i]) as [K1 p1] eqn:E1.
    destruct (insert K1 p1 z.[i]) as [K2 p2] eqn:E2.
    destruct (insert_spec K p y.[i] K1 p1 Hs ltac:(lia) E1) as (A1 & A2 & A3 & A4 & A5).
    destruct (insert_spec K1 p1 z.[i] K2 p2 A3 ltac:(rewrite A1; lia) E2)
      as (B1 & B2 & B3 & B4 & B5).
    pose proof (insert_src K p y.[i] K1 p1 Hs ltac:(lia) E1) as C1.
    pose proof (insert_src K1 p1 z.[i] K2 p2 A3 ltac:(rewrite A1; lia) E2) as C2.
    destruct (IH (gap m (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hi) (i + 1) K2 p2 (Acc_inv H (dec_step m i Hi)) K' p' eq_refl
       ltac:(lia) ltac:(rewrite B1, A1; exact HK) ltac:(lia) B3) as [D1 D2]; [| exact Hb |].
    + intros t Ht. destruct (C2 t Ht) as [Q | (t1 & Ht1 & Q)].
      * exists i. split; [lia|]. right. exact Q.
      * destruct (C1 t1 Ht1) as [Q1 | (t0 & Ht0 & Q1)].
        -- exists i. split; [lia|]. left. congruence.
        -- destruct (Hsrc t0 Ht0) as (j & Hj & Q2). exists j. split; [lia|]. rewrite Q, Q1. exact Q2.
    + split; [lia | exact D2].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    injection Hb as <- <-. split; [lia|].
    intros t Ht. destruct (Hsrc t Ht) as (j & Hj & Q). exists j. split; [lia | exact Q].
Qed.

Lemma ztn x : (match x with Z.pos q => PosDef.Pos.to_nat q | _ => 0%nat end) = Z.to_nat x.
Proof. reflexivity. Qed.
Ltac refold := unfold Uint63.to_nat in *; repeat (rewrite ztn in * ).
(* The names table holds at most n names: p <= n. *)
Lemma table_le_n : forall (n : N) (a b : list String.string) (y z : array pstr) (K : array pstr) (p : int),
  valid_input n a b -> repr y a -> repr z b ->
  sorted K p -> src y z K (PArray.length y) p ->
  ((φ p) <= Z.of_N n)%Z.
Proof.
  intros n a b y z K p Hv Hy Hz Hs Hsrc.
  destruct Hv as [_ _ Vp _ _ _ Vmem].
  destruct Vmem as (members & Lm & ND & Hin).
  unfold len in Vp, Lm.
  assert (Ly : φ (PArray.length y) = Z.of_nat (List.length a)) by exact (arr_len y a Hy).
  assert (Lz : φ (PArray.length z) = Z.of_nat (List.length b)) by exact (arr_len z b Hz).
  (* each cell of the table is a represented listed name *)
  assert (Hcell : forall t, ((φ t) < (φ p))%Z ->
            repr K.[t] (toS K.[t]) /\ In (toS K.[t]) members).
  { intros t Ht. destruct (Hsrc t Ht) as (j & Hj & [Q | Q]).
    all: assert (Hj' : (φ j < Z.of_nat (List.length a))%Z) by (rewrite <- Ly; exact Hj).
    all: assert (Hj'' : (φ j < Z.of_nat (List.length b))%Z) by lia.
    - assert (R : repr y.[j] (nth (Z.to_nat (φ j)) a String.EmptyString))
        by (apply arr_get; [exact Hy | lia]).
      rewrite Q. rewrite (repr_toS _ _ R). split; [exact R|].
      apply Hin. left. apply nth_In. lia.
    - assert (R : repr z.[j] (nth (Z.to_nat (φ j)) b String.EmptyString))
        by (apply arr_get; [exact Hz | lia]).
      rewrite Q. rewrite (repr_toS _ _ R). split; [exact R|].
      apply Hin. right. apply nth_In. lia. }
  pose proof (to_Z_bounded p) as Bp.
  set (f := fun t : nat => toS K.[of_Z (Z.of_nat t)]).
  assert (Hof : forall t : nat, (Z.of_nat t < φ p)%Z -> φ (of_Z (Z.of_nat t)) = Z.of_nat t).
  { intros t Ht. rewrite of_Z_spec. apply Z.mod_small. lia. }
  assert (ND' : NoDup (map f (seq 0 (Z.to_nat (φ p))))).
  { apply Finite.Injective_map_NoDup_in; [| apply seq_NoDup].
    intros t1 t2 H1 H2 E. apply in_seq in H1, H2. unfold f in E.
    destruct (Hcell (of_Z (Z.of_nat t1)) ltac:(rewrite Hof; lia)) as [R1 _].
    destruct (Hcell (of_Z (Z.of_nat t2)) ltac:(rewrite Hof; lia)) as [R2 _].
    rewrite E in R1. pose proof (repr_inj_r _ _ _ R1 R2) as EK.
    destruct (Nat.lt_trichotomy t1 t2) as [L|[L|L]]; [|exact L|].
    - exfalso. assert (C : PrimString.compare K.[of_Z (Z.of_nat t1)] K.[of_Z (Z.of_nat t2)] = Lt)
        by (apply Hs; rewrite !Hof; lia).
      rewrite EK, cmp_refl in C. discriminate.
    - exfalso. assert (C : PrimString.compare K.[of_Z (Z.of_nat t2)] K.[of_Z (Z.of_nat t1)] = Lt)
        by (apply Hs; rewrite !Hof; lia).
      rewrite EK, cmp_refl in C. discriminate. }
  assert (Inc : incl (map f (seq 0 (Z.to_nat (φ p)))) members).
  { intros s Hs'. apply in_map_iff in Hs' as (t & <- & Ht). apply in_seq in Ht.
    unfold f. apply (Hcell (of_Z (Z.of_nat t))). rewrite Hof; lia. }
  pose proof (NoDup_incl_length ND' Inc) as Le.
  rewrite length_map, length_seq in Le. lia.
Qed.

Lemma build_le_n : forall (n : N) (a b : list String.string) (x : uint) (y z : array pstr) K p,
  valid_input n a b -> repr x n -> repr y a -> repr z b ->
  build y z (PArray.length y) 0 (PArray.make (PArray.length y + PArray.length y) ""%pstring) 0
    (Zwf_well_founded 0 (gap (PArray.length y) 0)) = (K, p) ->
  ((φ p) <= (φ x))%Z.
Proof.
  intros n a b x y z K p Hv Hx Hy Hz Eb.
  pose proof Hv as Hv'.
  destruct Hv' as [Vn Vm Vp Vd _ _ _].
  unfold len in Vm, Vp.
  assert (Hm105 : (N.of_nat (List.length a) <= 105)%N).
  { assert (n * (n - 1) <= 15 * 14)%N by (apply N.mul_le_mono; lia).
    assert (n * (n - 1) / 2 <= 105)%N by (apply N.Div0.div_le_upper_bound; lia).
    lia. }
  assert (Ly : φ (PArray.length y) = Z.of_nat (List.length a)) by exact (arr_len y a Hy).
  set (m := PArray.length y) in *.
  pose proof (to_Z_bounded m) as Bm.
  assert (Hmm : (φ (m + m)) = (2 * (φ m))%Z) by sia.
  destruct (build_spec y z m ltac:(lia) _ 0 (PArray.make (m + m) ""%pstring) 0
              (Zwf_well_founded 0 (gap m 0)) K p eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alen_make by lia; exact Hmm)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros i j Hij; change (φ 0) with 0%Z in Hij; pose proof (to_Z_bounded i); lia)
              ltac:(intros j Hj; change (φ 0) with 0%Z in Hj; pose proof (to_Z_bounded j); lia)
              Eb) as (BK & Bp & Bs & Bmem).
  destruct (build_extra y z m ltac:(lia) _ 0 (PArray.make (m + m) ""%pstring) 0
              (Zwf_well_founded 0 (gap m 0)) K p eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alen_make by lia; exact Hmm)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros i j Hij; change (φ 0) with 0%Z in Hij; pose proof (to_Z_bounded i); lia)
              ltac:(intros t Ht; change (φ 0) with 0%Z in Ht; pose proof (to_Z_bounded t); lia)
              Eb) as [_ Src].
  pose proof (table_le_n n a b y z K p Hv Hy Hz Bs Src) as L.
  unfold repr, repr_uint in Hx. pose proof (to_Z_bounded x). lia.
Qed.

From Stdlib Require Import ssreflect.

Arguments gap : simpl never.
#[local] Arguments Uint63.to_Z : simpl never.
#[local] Arguments Z.to_nat : simpl never.
Arguments meas : simpl never.
Arguments midp : simpl never.
Arguments lim : simpl never.
Arguments bump : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma zwf_nat a b : Zwf 0 a b -> (0 < b)%Z -> (Z.to_nat a < Z.to_nat b)%nat.
Proof. unfold Zwf. lia. Qed.

Lemma gap_pos m i : (i <? m) = true -> (0 < gap m i)%Z.
Proof. intros H. rewrite ltb_spec in H. unfold gap. lia. Qed.

Lemma gap_stop m i : (i <? m) = false -> Z.to_nat (gap m i) = 0%nat.
Proof. intros H. assert (~ (φ i < φ m)%Z) by (rewrite <- Uint63.ltb_spec; congruence). unfold gap. lia. Qed.

Ltac absfix := match goal with |- context [?f] => is_fix f; let F := fresh "F" in set (F := f) in *; clearbody F end.
Ltac csimpl := cbn; cost_reduce; fold_cost; repeat (cost_rewrite; cost_reduce); cbn; fold_cost.
Ltac cstart := cost_unfold_fix; try absfix; csimpl.

Ltac dbdec := match goal with |- context [cost (bdec_cost stepsCM ?b ?w)] =>
  let HB := fresh "HB" in pose proof (bdec_time b w) as HB; cost_destruct (bdec b) end.
Ltac dif := match goal with |- context [if ?b then _ else _] => cost_destruct b end.

Lemma midp_time lo loC hi hiC : (cost (extract (midp_cost stepsCM lo loC) hi hiC) <= 20)%nat.
Proof. unfold midp_cost. csimpl. lia. Qed.

Ltac z0 f := repeat match goal with |- context [cost (f ?a ?b ?c)] => change (cost (f a b c)) with 0%nat end.
Ltac z1 f := repeat match goal with |- context [cost (extract (f ?a ?b ?c) ?d ?e)] =>
  change (cost (extract (f a b c) d e)) with 0%nat end.
Ltac z2 f := repeat match goal with |- context [cost (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1)] =>
  change (cost (extract (extract (f a b c) d e) d1 e1)) with 0%nat end.
Ltac z3 f := repeat match goal with |- context [cost (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2)] =>
  change (cost (extract (extract (extract (f a b c) d e) d1 e1) d2 e2)) with 0%nat end.
Ltac z4 f := repeat match goal with |- context [cost (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3)] =>
  change (cost (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3)) with 0%nat end.
Ltac z5 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4)] =>
  change (cost (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4)) with 0%nat end.
Ltac z6 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5)] =>
  change (cost (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5)) with 0%nat end.
Ltac z7 f := repeat match goal with |- context [cost (extract (extract (extract (extract (extract (extract (extract (f ?a ?b ?c) ?d ?e) ?d1 ?e1) ?d2 ?e2) ?d3 ?e3) ?d4 ?e4) ?d5 ?e5) ?d6 ?e6)] =>
  change (cost (extract (extract (extract (extract (extract (extract (extract (f a b c) d e) d1 e1) d2 e2) d3 e3) d4 e4) d5 e5) d6 e6)) with 0%nat end.
Ltac zall f := z0 f; z1 f; z2 f; z3 f; z4 f; z5 f; z6 f; z7 f.
Ltac set_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
      change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (set_cost a b c) d e) f g)) with 0%nat
  | |- context [cost (extract (set_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (set_cost a b c) d e)) with 0%nat
  | |- context [cost (set_cost ?a ?b ?c)] =>
      change (cost (set_cost a b c)) with 0%nat
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  | |- context [cost (extract (make_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (make_cost a b c) d e)) with 0%nat
  | |- context [cost (make_cost ?a ?b ?c)] =>
      change (cost (make_cost a b c)) with 0%nat
  end.
Ltac genc X lem :=
  let Hc := fresh "Hc" in
  match goal with |- context [@cost ?T X] =>
    have Hc := (lem : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end.
Ltac gen_midp := z0 midp_cost; repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (midp_cost stepsCM ?a ?aC) ?b ?bC => genc X (midp_time a aC b bC) end end.

Lemma lb_time K KC s sC lo loC hi hiC H HC :
  (cost (extract (extract (extract (extract (lb_cost stepsCM K KC) s sC) lo loC) hi hiC) H HC)
     <= Z.to_nat (gap hi lo) * 100 + 20)%nat.
Proof.
  unfold lb_cost. cbn.
  match goal with |- context [@cost ?T (?G K KC s sC lo loC hi hiC H HC)] =>
    assert (HG : forall m lo loC hi hiC H HC, (Z.to_nat (gap hi lo) <= m)%nat ->
       (cost (G K KC s sC lo loC hi hiC H HC) <= Z.to_nat (gap hi lo) * 100 + 20)%nat) end.
  { induction m as [|m IH]; intros lo' loC' hi' hiC' [g] HC' Hm;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_lo _ _ e)); lia).
    - lia.
    - gen_midp.
      cost_destruct (PrimString.compare K.[midp lo' hi'] s); csimpl.
      all: match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?a1 ?b1 ?a2 ?b2 ?h ?hc)] =>
        is_var G';
        have HI := (IH a1 b1 a2 b2 h hc ltac:(pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_lo _ _ e)); pose proof (zwf_nat _ _ (dec_hi _ _ e)); lia) : (@cost T (G' x1 x2 x3 x4 a1 b1 a2 b2 h hc) <= _)%nat) end.
      all: pose proof (gap_pos _ _ e).
      all: pose proof (zwf_nat _ _ (dec_lo _ _ e)); pose proof (zwf_nat _ _ (dec_hi _ _ e)); lia.
    - lia. }
  match goal with |- context [@cost ?T (?G K KC s sC lo loC hi hiC H HC)] =>
    exact (HG _ lo loC hi hiC H HC (le_n _) : (@cost T (G K KC s sC lo loC hi hiC H HC) <= _)%nat) end.
Qed.

Lemma gap0 a : Z.to_nat (gap a 0) = Z.to_nat (φ a).
Proof. unfold gap. change (φ 0) with 0%Z. lia. Qed.

Ltac gen_lb := zall lb_cost; repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (lb_cost stepsCM ?K ?KC) ?s ?sC) ?lo ?loC) ?hi ?hiC) ?H ?HC =>
    genc X (lb_time K KC s sC lo loC hi hiC H HC) end end.

Lemma look_time K KC p pC s sC :
  (cost (extract (extract (look_cost stepsCM K KC) p pC) s sC) <= Z.to_nat (φ p) * 100 + 40)%nat.
Proof.
  unfold look_cost. csimpl. gen_lb. rewrite gap0 in Hc. lia.
Qed.

Lemma shift_time K KC t tC j jC H HC :
  (cost (extract (extract (extract (shift_cost stepsCM K KC) t tC) j jC) H HC)
     <= Z.to_nat (gap j t) * 100 + 20)%nat.
Proof.
  unfold shift_cost. cbn.
  match goal with |- context [@cost ?T (?G K KC t tC j jC H HC)] =>
    assert (HG : forall m K KC j jC H HC, (Z.to_nat (gap j t) <= m)%nat ->
       (cost (G K KC t tC j jC H HC) <= Z.to_nat (gap j t) * 100 + 20)%nat) end.
  { induction m as [|m IH]; intros K' KC' j' jC' [g] HC' Hm;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_down _ _ e)); lia).
    - lia.
    - set_simpl.
      match goal with |- context [@cost ?T (?G' ?a1 ?b1 ?x1 ?x2 ?a2 ?b2 ?h ?hc)] =>
        is_var G';
        have HI := (IH a1 b1 a2 b2 h hc ltac:(pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_down _ _ e)); lia) : (@cost T (G' a1 b1 x1 x2 a2 b2 h hc) <= _)%nat) end.
      pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_down _ _ e)); lia.
    - lia. }
  match goal with |- context [@cost ?T (?G K KC t tC j jC H HC)] =>
    exact (HG _ K KC j jC H HC (le_n _) : (@cost T (G K KC t tC j jC H HC) <= _)%nat) end.
Qed.

Lemma is_eq_time c cC : (cost (is_eq_cost stepsCM c cC) <= 5)%nat.
Proof. unfold is_eq_cost. csimpl. destruct c; csimpl; lia. Qed.

Lemma andb_time a aC b bC : (cost (extract (andb_cost stepsCM a aC) b bC) <= 5)%nat.
Proof. unfold andb_cost. csimpl. destruct a; csimpl; lia. Qed.

Ltac gen_small := z0 andb_cost; zall look_cost; zall shift_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (andb_cost stepsCM ?a ?aC) ?b ?bC => genc X (andb_time a aC b bC)
  | is_eq_cost stepsCM ?a ?aC => genc X (is_eq_time a aC)
  | extract (extract (look_cost stepsCM ?K ?KC) ?p ?pC) ?s ?sC => genc X (look_time K KC p pC s sC)
  | extract (extract (extract (shift_cost stepsCM ?K ?KC) ?t ?tC) ?j ?jC) ?H ?HC => genc X (shift_time K KC t tC j jC H HC)
  end end.

Lemma gap_le p t : (Z.to_nat (gap p t) <= Z.to_nat (φ p))%nat.
Proof. unfold gap. pose proof (to_Z_bounded t). lia. Qed.

Lemma insert_time K KC p pC s sC :
  (cost (extract (extract (insert_cost stepsCM K KC) p pC) s sC) <= Z.to_nat (φ p) * 200 + 200)%nat.
Proof.
  unfold insert_cost. csimpl. gen_small.
  pose proof (gap_le p (look K p s)).
  dif; csimpl; set_simpl. 
  all: unfold Uint63.to_nat in *; lia.
Qed.

Ltac gen_ins := zall insert_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (insert_cost stepsCM ?K ?KC) ?p ?pC) ?s ?sC => genc X (insert_time K KC p pC s sC)
  end end.

Lemma build_time y yC z zC m mC i iC K KC p pC H HC :
  ((φ m) <= 4194303)%Z -> ((φ i) <= (φ m))%Z ->
  (φ (PArray.length K)) = (2 * (φ m))%Z -> ((φ p) <= 2 * (φ i))%Z -> sorted K p ->
  (cost (extract (extract (extract (extract (extract (extract (build_cost stepsCM y yC) z zC) m mC) i iC) K KC) p pC) H HC)
     <= Z.to_nat (gap m i) * (Z.to_nat (φ (snd (build y z m i K p H))) * 400 + 500) + 20)%nat.
Proof.
  intros Hm0. unfold build_cost. cbn.
  match goal with |- context [@cost ?T (?G y yC z zC m mC i iC K KC p pC H HC)] =>
    assert (HG : forall mm i iC K KC p pC H HC, (Z.to_nat (gap m i) <= mm)%nat ->
       ((φ i) <= (φ m))%Z ->
       (φ (PArray.length K)) = (2 * (φ m))%Z -> ((φ p) <= 2 * (φ i))%Z -> sorted K p ->
       (cost (G y yC z zC m mC i iC K KC p pC H HC) <= Z.to_nat (gap m i) * (Z.to_nat (φ (snd (build y z m i K p H))) * 400 + 500) + 20)%nat) end.
  { induction mm as [|mm IH]; intros i' iC' K' KC' p' pC' [g] HC' Hmm Him HK Hp Hs;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia).
    - lia.
    - gen_ins.
      cost_destruct_witness (insert K' p' y.[i']) as [K1 KC1 p1 pC1] eqn:E1.
      csimpl. gen_ins.
      cost_destruct_witness (insert K1 p1 z.[i']) as [K2 KC2 p2 pC2] eqn:E2.
      csimpl.
      pose proof Hp as Hp0. pose proof e as e0. rewrite ltb_spec in e0.
      assert (Ei : (φ (i' + 1)) = ((φ i') + 1)%Z) by sia.
      destruct (insert_spec K' p' y.[i'] K1 p1 Hs ltac:(lia) E1) as (A1 & A2 & A3 & A4 & A5).
      destruct (insert_spec K1 p1 z.[i'] K2 p2 A3 ltac:(rewrite A1; lia) E2)
        as (B1 & B2 & B3 & B4 & B5).
      match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?h ?hc)] =>
        is_var G';
        have HI := (IH a1 b1 a2 b2 a3 b3 h hc ltac:(pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia)
          ltac:(lia) ltac:(rewrite B1 A1; exact HK) ltac:(lia) B3 : (@cost T (G' x1 x2 x3 x4 x5 x6 a1 b1 a2 b2 a3 b3 h hc) <= _)%nat) end.
      pose proof (build_mono y z m _ (i' + 1) K2 p2 (g (gap m (i' + 1)) (dec_step m i' e)) eq_refl
        ltac:(lia) ltac:(rewrite B1 A1; exact HK) ltac:(lia) B3) as Mo.
      assert (EP : (φ (snd (build y z m (i' + 1) K2 p2 (g (gap m (i' + 1)) (dec_step m i' e)))))
                 = (φ (snd (build y z m i' K' p' (Acc_intro _ g))))).
      { rewrite (build_unfold y z m i' K' p' (Acc_intro _ g) e K1 p1 K2 p2 E1 E2). reflexivity. }
      refold.
      pose proof (gap_pos _ _ e) as Gp. pose proof (zwf_nat _ _ (dec_step _ _ e)) as Gd.
      clear -HI Mo Gp Gd Hc Hc0 B2 A2 HB.
      match goal with |- context [(Z.to_nat (gap m i') * ?X)%nat] => set (XX := X) in * end.
      match type of HI with context [(Z.to_nat (gap m (i' + 1)) * ?X)%nat] => change X with XX in HI end.
      assert (Hq : (Z.to_nat (φ p') * 200 + 200 + (Z.to_nat (φ p1) * 200 + 200) + 100 <= XX)%nat) by (subst XX; lia).
      assert (Hg : (Z.to_nat (gap m (i' + 1)) * XX + XX <= Z.to_nat (gap m i') * XX)%nat) by nia.
      lia.
    - lia. }
  intros Him HK Hp Hs.
  match goal with |- context [@cost ?T (?G y yC z zC m mC i iC K KC p pC H HC)] =>
    exact (HG _ i iC K KC p pC H HC (le_n _) Him HK Hp Hs : (@cost T (G y yC z zC m mC i iC K KC p pC H HC) <= _)%nat) end.
Qed.


Lemma fill_time y yC z zC K KC p pC m mC i iC tbl tblC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (fill_cost stepsCM y yC) z zC) K KC) p pC) m mC) i iC) tbl tblC) H HC)
     <= Z.to_nat (gap m i) * (Z.to_nat (φ p) * 200 + 200) + 20)%nat.
Proof.
  unfold fill_cost. cbn.
  match goal with |- context [@cost ?T (?G y yC z zC K KC p pC m mC i iC tbl tblC H HC)] =>
    assert (HG : forall mm i iC tbl tblC H HC, (Z.to_nat (gap m i) <= mm)%nat ->
       (cost (G y yC z zC K KC p pC m mC i iC tbl tblC H HC) <= Z.to_nat (gap m i) * (Z.to_nat (φ p) * 200 + 200) + 20)%nat) end.
  { induction mm as [|mm IH]; intros i' iC' t' tC' [g] HC' Hmm;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia).
    - lia.
    - gen_small. set_simpl.
      match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?a1 ?b1 ?a2 ?b2 ?h ?hc)] =>
        is_var G';
        have HI := (IH a1 b1 a2 b2 h hc ltac:(pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia)
          : (@cost T (G' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a1 b1 a2 b2 h hc) <= _)%nat) end.
      pose proof (gap_pos _ _ e) as Gp. pose proof (zwf_nat _ _ (dec_step _ _ e)) as Gd.
      refold.
      match goal with |- context [(Z.to_nat (gap m i') * ?X)%nat] => set (XX := X) in * end.
      assert (Hq : (Z.to_nat (φ p) * 100 + 40 + (Z.to_nat (φ p) * 100 + 40) + 100 <= XX)%nat) by (subst XX; lia).
      assert (Hg : (Z.to_nat (gap m (i' + 1)) * XX + XX <= Z.to_nat (gap m i') * XX)%nat) by nia.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G y yC z zC K KC p pC m mC i iC tbl tblC H HC)] =>
    exact (HG _ i iC tbl tblC H HC (le_n _) : (@cost T (G y yC z zC K KC p pC m mC i iC tbl tblC H HC) <= _)%nat) end.
Qed.

Lemma okc_time tbl tblC p pC v vC c cC col colC u uC H HC :
  (cost (extract (extract (extract (extract (extract (extract (okc_cost stepsCM tbl tblC) p pC) v vC) c cC) col colC) u uC) H HC)
     <= Z.to_nat (gap v u) * 50 + 20)%nat.
Proof.
  unfold okc_cost. cbn.
  match goal with |- context [@cost ?T (?G tbl tblC p pC v vC c cC col colC u uC H HC)] =>
    assert (HG : forall mm u uC H HC, (Z.to_nat (gap v u) <= mm)%nat ->
       (cost (G tbl tblC p pC v vC c cC col colC u uC H HC) <= Z.to_nat (gap v u) * 50 + 20)%nat) end.
  { induction mm as [|mm IH]; intros u' uC' [g] HC' Hmm;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia).
    - lia.
    - gen_small. set_simpl.
      dif; csimpl.
      + pose proof (gap_pos _ _ e). refold. lia.
      + match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?a1 ?b1 ?h ?hc)] =>
          is_var G';
          have HI := (IH a1 b1 h hc ltac:(pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia)
            : (@cost T (G' x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a1 b1 h hc) <= _)%nat) end.
        pose proof (gap_pos _ _ e) as Gp. pose proof (zwf_nat _ _ (dec_step _ _ e)) as Gd.
        refold. lia.
    - lia. }
  match goal with |- context [@cost ?T (?G tbl tblC p pC v vC c cC col colC u uC H HC)] =>
    exact (HG _ u uC H HC (le_n _) : (@cost T (G tbl tblC p pC v vC c cC col colC u uC H HC) <= _)%nat) end.
Qed.


Lemma lim_time u uC k kC : (cost (extract (lim_cost stepsCM u uC) k kC) <= 20)%nat.
Proof. unfold lim_cost. csimpl. dif; csimpl; lia. Qed.

Lemma bump_time u uC c cC : (cost (extract (bump_cost stepsCM u uC) c cC) <= 20)%nat.
Proof. unfold bump_cost. csimpl. dif; csimpl; lia. Qed.

Fixpoint GB (kn M r : nat) : nat :=
  match r with O => M | S r' => kn * (M + GB kn M r') + M end.

Definition SB (kn M R cn : nat) : nat :=
  match R with O => M | S r => (kn - cn) * (M + GB kn M r) + M end.

Lemma SB0 kn M R : SB kn M R 0 = GB kn M R.
Proof. destruct R; [reflexivity | cbn [SB GB]; rewrite Nat.sub_0_r; reflexivity]. Qed.

Lemma meas_pos p k v c : (φ v < φ p)%Z -> (φ c < φ k)%Z -> (0 < meas p k v c)%Z.
Proof. intros. unfold meas. nia. Qed.

Lemma meas_v p k v c used (Hv : (v <? p) = true) (Hc : (c <? lim used k) = true) :
  (Z.to_nat (meas p k (v + 1) 0) < Z.to_nat (meas p k v c))%nat.
Proof.
  apply zwf_nat; [apply (dec_v p k v c used Hv Hc)|]. apply meas_pos.
  - rewrite ltb_spec in Hv. exact Hv.
  - exact (lim_le _ _ _ Hc).
Qed.

Lemma meas_c p k v c used (Hv : (v <? p) = true) (Hc : (c <? lim used k) = true) :
  (Z.to_nat (meas p k v (c + 1)) < Z.to_nat (meas p k v c))%nat.
Proof.
  apply zwf_nat; [apply (dec_c p k v c used Hv Hc)|]. apply meas_pos.
  - rewrite ltb_spec in Hv. exact Hv.
  - exact (lim_le _ _ _ Hc).
Qed.

Lemma SB_ge kn M R cn : (M <= SB kn M R cn)%nat.
Proof. destruct R; cbn [SB]; [lia | apply Nat.le_add_l]. Qed.

Lemma R_stop p v : (v <? p) = false -> Z.to_nat (φ p - φ v) = 0%nat.
Proof. intros H. assert (~ (φ v < φ p)%Z) by (rewrite <- Uint63.ltb_spec; congruence). lia. Qed.

Lemma R_succ p v : (v <? p) = true -> Z.to_nat (φ p - φ v) = S (Z.to_nat (φ p - φ (v + 1))).
Proof. intros H. rewrite ltb_spec in H. assert (φ (v + 1) = φ v + 1)%Z by sia. lia. Qed.

Lemma C_succ k c used : (c <? lim used k) = true -> Z.to_nat (φ (c + 1)) = S (Z.to_nat (φ c)) /\ (Z.to_nat (φ c) < Z.to_nat (φ k))%nat.
Proof. intros H. pose proof (lim_le _ _ _ H). assert (φ (c + 1) = φ c + 1)%Z by sia. pose proof (to_Z_bounded c). lia. Qed.

Lemma okc_le v p : (v <? p) = true -> (Z.to_nat (gap v 0) <= Z.to_nat (φ p))%nat.
Proof. intros H. rewrite ltb_spec in H. unfold gap. change (φ 0) with 0%Z. pose proof (to_Z_bounded v). lia. Qed.

Lemma srch_arith kn cn M r c1 c2 : (cn < kn)%nat ->
  (c1 <= GB kn M r)%nat -> (c2 <= SB kn M (S r) (S cn))%nat ->
  (c1 + c2 + M <= SB kn M (S r) cn)%nat.
Proof.
  intros H1 H3 H4. cbn [SB] in *.
  replace (kn - cn)%nat with (S (kn - S cn)) by lia. rewrite Nat.mul_succ_l. lia.
Qed.
Arguments SB : simpl never.
Arguments GB : simpl never.

Ltac gen_okc := zall okc_cost; zall lim_cost; zall bump_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (lim_cost stepsCM ?a ?aC) ?b ?bC => genc X (lim_time a aC b bC)
  | extract (bump_cost stepsCM ?a ?aC) ?b ?bC => genc X (bump_time a aC b bC)
  | extract (extract (extract (extract (extract (extract (okc_cost stepsCM ?t ?tC) ?p ?pC) ?v ?vC) ?c ?cC) ?col ?colC) ?u ?uC) ?H ?HC =>
      genc X (okc_time t tC p pC v vC c cC col colC u uC H HC)
  end end.

Lemma srch_time tbl tblC p pC k kC v vC c cC used usedC col colC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (srch_cost stepsCM tbl tblC) p pC) k kC) v vC) c cC) used usedC) col colC) H HC)
     <= SB (Z.to_nat (φ k)) (Z.to_nat (φ p) * 50 + 300) (Z.to_nat (φ p - φ v)) (Z.to_nat (φ c)))%nat.
Proof.
  unfold srch_cost. cbn.
  remember (Z.to_nat (φ p) * 50 + 300)%nat as M eqn:EM.
  remember (Z.to_nat (φ k)) as kn eqn:Ekn.
  match goal with |- context [@cost ?T (?G tbl tblC p pC k kC v vC c cC used usedC col colC H HC)] =>
    assert (HG : forall mm v vC c cC used usedC col colC H HC, (Z.to_nat (meas p k v c) <= mm)%nat ->
       (cost (G tbl tblC p pC k kC v vC c cC used usedC col colC H HC) <= SB kn M (Z.to_nat (φ p - φ v)) (Z.to_nat (φ c)))%nat) end.
  { induction mm as [|mm IH]; intros v' vC' c' cC' u' uC' col' colC' [g] HC' Hmm;
      cstart; dbdec; csimpl.
    all: try (rewrite (R_stop p v' e); unfold SB; subst M; lia).
    all: gen_okc; dbdec; csimpl.
    all: try (exfalso; pose proof (meas_c p k v' c' u' e e0); lia).
    all: try (pose proof (SB_ge kn M (Z.to_nat (φ p - φ v')) (Z.to_nat (φ c'))); subst M; lia).
    all: gen_okc.
    all: pose proof (okc_le v' p e) as Hok.
    all: rewrite (R_succ p v' e).
    all: destruct (C_succ k c' u' e0) as [Cs Ck].
    all: pose proof (meas_c p k v' c' u' e e0) as Mc; pose proof (meas_v p k v' c' u' e e0) as Mv.
    all: dif; csimpl.
    - match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?h ?hc)] =>
        is_var G';
        have HI1 := (IH a1 b1 a2 b2 a3 b3 a4 b4 h hc ltac:(lia)
          : (@cost T (G' x1 x2 x3 x4 x5 x6 a1 b1 a2 b2 a3 b3 a4 b4 h hc) <= _)%nat) end.
      match goal with |- context [srch tbl p k (v' + 1) 0 ?a ?b ?h] =>
        cost_destruct_witness (srch tbl p k (v' + 1) 0 a b h) as [r rC col2 col2C] eqn:Er end.
      csimpl.
      change (Z.to_nat (φ 0)) with 0%nat in HI1. rewrite SB0 in HI1.
      cost_destruct r; csimpl.
      + pose proof (srch_arith kn (Z.to_nat (φ c')) M (Z.to_nat (φ p - φ (v' + 1))) _ 0 ltac:(lia) HI1 ltac:(lia)).
        set_simpl. refold. subst M. lia.
      + match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?h ?hc)] =>
          is_var G';
          have HI2 := (IH a1 b1 a2 b2 a3 b3 a4 b4 h hc ltac:(lia)
            : (@cost T (G' x1 x2 x3 x4 x5 x6 a1 b1 a2 b2 a3 b3 a4 b4 h hc) <= _)%nat) end.
        rewrite (R_succ p v' e) Cs in HI2.
        pose proof (srch_arith kn (Z.to_nat (φ c')) M (Z.to_nat (φ p - φ (v' + 1))) _ _ ltac:(lia) HI1 HI2).
        set_simpl. refold. subst M. lia.
    - match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?a1 ?b1 ?a2 ?b2 ?a3 ?b3 ?a4 ?b4 ?h ?hc)] =>
        is_var G';
        have HI2 := (IH a1 b1 a2 b2 a3 b3 a4 b4 h hc ltac:(lia)
          : (@cost T (G' x1 x2 x3 x4 x5 x6 a1 b1 a2 b2 a3 b3 a4 b4 h hc) <= _)%nat) end.
      rewrite (R_succ p v' e) Cs in HI2.
      pose proof (srch_arith kn (Z.to_nat (φ c')) M (Z.to_nat (φ p - φ (v' + 1))) 0 _ ltac:(lia) ltac:(lia) HI2).
      set_simpl. refold. subst M. lia. }
  match goal with |- context [@cost ?T (?G tbl tblC p pC k kC v vC c cC used usedC col colC H HC)] =>
    exact (HG _ v vC c cC used usedC col colC H HC (le_n _) : (@cost T (G tbl tblC p pC k kC v vC c cC used usedC col colC H HC) <= _)%nat) end.
Qed.


Lemma GB_pow kn M r : (GB kn M r + M <= 2 * M * (kn + 1) ^ r)%nat.
Proof.
  induction r as [|r IH].
  - unfold GB. cbn. lia.
  - change (GB kn M (S r)) with (kn * (M + GB kn M r) + M)%nat.
    rewrite Nat.pow_succ_r'.
    remember ((kn + 1) ^ r)%nat as x eqn:Ex.
    assert (1 <= x)%nat by (subst x; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
    remember (GB kn M r) as G. nia.
Qed.

Lemma srch0_time tbl tblC p pC k kC vC cC used usedC col colC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (srch_cost stepsCM tbl tblC) p pC) k kC) 0%uint63 vC) 0%uint63 cC) used usedC) col colC) H HC)
     <= 2 * (Z.to_nat (φ p) * 50 + 300) * (Z.to_nat (φ k) + 1) ^ Z.to_nat (φ p))%nat.
Proof.
  pose proof (srch_time tbl tblC p pC k kC 0%uint63 vC 0%uint63 cC used usedC col colC H HC) as T.
  change (φ 0) with 0%Z in T. rewrite Z.sub_0_r in T. change (Z.to_nat 0) with 0%nat in T.
  rewrite SB0 in T. pose proof (GB_pow (Z.to_nat (φ k)) (Z.to_nat (φ p) * 50 + 300) (Z.to_nat (φ p))). lia.
Qed.

Ltac gen_srch := zall srch_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (extract (extract (extract (extract (extract (srch_cost stepsCM ?t ?tC) ?p ?pC) ?k ?kC) 0%uint63 ?vC) 0%uint63 ?cC) ?u ?uC) ?col ?colC) ?H ?HC =>
      genc X (srch0_time t tC p pC k kC vC cC u uC col colC H HC)
  end end.

Lemma pow_mono k P e : (k <? P) = true -> ((Z.to_nat (φ k) + 1) ^ e <= Z.to_nat (φ P) ^ e)%nat.
Proof. intros H. rewrite ltb_spec in H. apply Nat.pow_le_mono_l. pose proof (to_Z_bounded k). lia. Qed.

Lemma deepen_time tbl tblC p pC P PC k kC col colC H HC :
  (cost (extract (extract (extract (extract (extract (deepen_cost stepsCM tbl tblC) p pC) P PC) k kC) col colC) H HC)
     <= Z.to_nat (gap P k) * (2 * (Z.to_nat (φ p) * 50 + 300) * Z.to_nat (φ P) ^ Z.to_nat (φ p) + 100) + 20)%nat.
Proof.
  unfold deepen_cost. cbn.
  remember (2 * (Z.to_nat (φ p) * 50 + 300) * Z.to_nat (φ P) ^ Z.to_nat (φ p) + 100)%nat as XX eqn:EXX.
  match goal with |- context [@cost ?T (?G tbl tblC p pC P PC k kC col colC H HC)] =>
    assert (HG : forall mm k kC col colC H HC, (Z.to_nat (gap P k) <= mm)%nat ->
       (cost (G tbl tblC p pC P PC k kC col colC H HC) <= Z.to_nat (gap P k) * XX + 20)%nat) end.
  { induction mm as [|mm IH]; intros k' kC' col' colC' [g] HC' Hmm;
      cstart; dbdec; csimpl.
    all: try (exfalso; pose proof (gap_pos _ _ e); pose proof (zwf_nat _ _ (dec_step _ _ e)); lia).
    - lia.
    - gen_srch.
      match goal with |- context [srch tbl p k' 0 0 0 col' ?h] =>
        cost_destruct_witness (srch tbl p k' 0 0 0 col' h) as [r rC col2 col2C] eqn:Er end.
      csimpl.
      pose proof (pow_mono k' P (Z.to_nat (φ p)) e) as Pm.
      pose proof (gap_pos _ _ e) as Gp. pose proof (zwf_nat _ _ (dec_step _ _ e)) as Gd.
      cost_destruct r; csimpl.
      + refold.
        assert (Hq : (2 * (Z.to_nat (φ p) * 50 + 300) * (Z.to_nat (φ k') + 1) ^ Z.to_nat (φ p) + 100 <= XX)%nat)
          by (subst XX; nia).
        assert (Hg : (XX <= Z.to_nat (gap P k') * XX)%nat) by nia.
        set_simpl. lia.
      + match goal with |- context [@cost ?T (?G' ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?a1 ?b1 ?a2 ?b2 ?h ?hc)] =>
          is_var G';
          have HI := (IH a1 b1 a2 b2 h hc ltac:(lia)
            : (@cost T (G' x1 x2 x3 x4 x5 x6 a1 b1 a2 b2 h hc) <= _)%nat) end.
        refold.
        assert (Hq : (2 * (Z.to_nat (φ p) * 50 + 300) * (Z.to_nat (φ k') + 1) ^ Z.to_nat (φ p) + 100 <= XX)%nat)
          by (subst XX; nia).
        assert (Hg : (Z.to_nat (gap P (k' + 1)) * XX + XX <= Z.to_nat (gap P k') * XX)%nat) by nia.
        set_simpl. lia.
    - lia. }
  subst XX.
  match goal with |- context [@cost ?T (?G tbl tblC p pC P PC k kC col colC H HC)] =>
    exact (HG _ k kC col colC H HC (le_n _) : (@cost T (G tbl tblC p pC P PC k kC col colC H HC) <= _)%nat) end.
Qed.


Ltac gen_main := zall build_cost; zall fill_cost; zall deepen_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with
  | extract (extract (extract (extract (extract (extract (extract (fill_cost stepsCM ?y ?yC) ?z ?zC) ?K ?KC) ?p ?pC) ?m ?mC) ?i ?iC) ?t ?tC) ?H ?HC =>
      genc X (fill_time y yC z zC K KC p pC m mC i iC t tC H HC)
  | extract (extract (extract (extract (extract (deepen_cost stepsCM ?t ?tC) ?p ?pC) ?P ?PC) ?k ?kC) ?col ?colC) ?H ?HC =>
      genc X (deepen_time t tC p pC P PC k kC col colC H HC)
  end end.

Lemma make_len (m : int) : ((φ m) <= 105)%Z ->
  φ (PArray.length (PArray.make (m + m) ""%pstring)) = (2 * φ m)%Z.
Proof.
  intros H. pose proof (to_Z_bounded m).
  assert (E : φ (m + m) = (2 * φ m)%Z) by sia.
  rewrite -E. exact (f_equal to_Z (alen_make (m + m) ""%pstring ltac:(lia))).
Qed.

Lemma sorted_make (m : int) : sorted (PArray.make (m + m) ""%pstring) 0.
Proof. intros i j H. change (φ 0) with 0%Z in H. pose proof (to_Z_bounded i). lia. Qed.

Lemma m_small n a b (y : array pstr) : valid_input n a b -> repr y a -> (φ (PArray.length y) <= 105)%Z.
Proof.
  intros Hv Hy. destruct Hv as [Vn Vm _ _ _ _ _]. unfold len in Vm.
  assert (Hm105 : (N.of_nat (List.length a) <= 105)%N).
  { assert (n * (n - 1) <= 15 * 14)%N by (apply N.mul_le_mono; lia).
    assert (n * (n - 1) / 2 <= 105)%N by (apply N.Div0.div_le_upper_bound; lia).
    lia. }
  match goal with |- (φ ?L <= _)%Z => assert (Ly : φ L = Z.of_nat (List.length a)) by exact (arr_len y a Hy) end.
  lia.
Qed.

Lemma zero_le (m : int) : (φ 0 <= φ m)%Z.
Proof. change (φ 0) with 0%Z. pose proof (to_Z_bounded m). lia. Qed.
Lemma zero_le2 : (φ 0 <= 2 * φ 0)%Z.
Proof. change (φ 0) with 0%Z. lia. Qed.

Lemma mono_bound nb G A X : (nb <= G * (A * 400 + 500) + 20)%nat -> (A <= X)%nat ->
  (nb <= G * (X * 400 + 500) + 20)%nat.
Proof. intros H1 H2. assert (G * (A * 400 + 500) <= G * (X * 400 + 500))%nat by nia. lia. Qed.

Lemma deepen_arith n2 g pp w N : (n2 <= g * (2 * (pp * 50 + 300) * w + 100) + 20)%nat ->
  (g <= N)%nat -> (pp <= N)%nat -> (w <= N ^ N)%nat ->
  (n2 <= N * (2 * (N * 50 + 300) * N ^ N + 100) + 20)%nat.
Proof.
  intros H1 H2 H3 H4.
  assert (A : (2 * (pp * 50 + 300) * w + 100 <= 2 * (N * 50 + 300) * N ^ N + 100)%nat).
  { assert (pp * 50 + 300 <= N * 50 + 300)%nat by lia.
    assert ((pp * 50 + 300) * w <= (N * 50 + 300) * N ^ N)%nat by (apply Nat.mul_le_mono; lia).
    lia. }
  assert (g * (2 * (pp * 50 + 300) * w + 100) <= N * (2 * (N * 50 + 300) * N ^ N + 100))%nat
    by (apply Nat.mul_le_mono; lia).
  lia.
Qed.

Lemma fill_arith n1 g pp N : (n1 <= g * (pp * 200 + 200) + 20)%nat -> (pp <= N)%nat ->
  (n1 <= g * (N * 200 + 200) + 20)%nat.
Proof. intros H1 H2. assert (g * (pp * 200 + 200) <= g * (N * 200 + 200))%nat by (apply Nat.mul_le_mono; lia). lia. Qed.

Lemma pow_arith P p N : (1 <= N)%nat -> (P <= N)%nat -> (p <= N)%nat -> (P ^ p <= N ^ N)%nat.
Proof.
  intros H1 H2 H3. transitivity (N ^ p)%nat; [apply Nat.pow_le_mono_l; lia|].
  apply Nat.pow_le_mono_r; lia.
Qed.

Opaque PArray.make.
Lemma committees_impl_time n a b x xC y yC z zC :
  valid_input n a b -> repr x n -> repr y a -> repr z b ->
  (cost (extract (extract (committees_impl_cost stepsCM x xC) y yC) z zC)
     <= Z.to_nat (φ (PArray.length y)) * (Z.to_nat (φ x) * 600 + 700)
        + Z.to_nat (φ x) * (2 * (Z.to_nat (φ x) * 50 + 300) * Z.to_nat (φ x) ^ Z.to_nat (φ x) + 100) + 300)%nat.
Proof.
  intros Hv Hx Hy Hz.
  pose proof (m_small n a b y Hv Hy) as Hm.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  unfold committees_impl_cost. csimpl. set_simpl. gen_main.
  match goal with |- context [extract (extract (build_cost stepsCM y yC) z zC) ?m ?mC] =>
    assert (Hm' : (φ m <= 105)%Z) by exact Hm end.
  clear Hm. rename Hm' into Hm.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with
    | extract (extract (extract (extract (extract (extract (build_cost stepsCM ?y ?yC) ?z ?zC) ?m ?mC) ?i ?iC) ?K ?KC) ?p ?pC) ?H ?HC =>
      genc X (build_time y yC z zC m mC i iC K KC p pC H HC ltac:(lia) (zero_le m)
                (make_len _ Hm) zero_le2 (sorted_make _))
    end end.
  match type of Hc with context [snd ?B] =>
    assert (Hpn : (φ (snd B) <= φ x)%Z) by (destruct B as [K0 p0] eqn:E0; exact (build_le_n n a b x y z K0 p0 Hv Hx Hy Hz E0)) end.
  match type of Hc with (?nb <= ?G * (Z.to_nat (φ (snd ?B)) * 400 + 500) + 20)%nat =>
    have Hc' := mono_bound nb G _ (Z.to_nat (φ x)) Hc ltac:(lia) end.
  clear Hc Hpn.
  match goal with |- context [build y z ?m ?i ?K0 ?p0 ?h] =>
    cost_destruct_witness (build y z m i K0 p0 h) as [K KC p pC] eqn:Eb end.
  csimpl. set_simpl. gen_main.
  have Hpx := build_le_n n a b x y z K p Hv Hx Hy Hz Eb.
  assert (HN : (1 <= φ x <= 15)%Z).
  { destruct Hv as [Vn _ _ _ _ _ _]. unfold repr, repr_uint in Hx. pose proof (to_Z_bounded x). lia. }
  pose proof (to_Z_bounded p) as Bp.
  match goal with H : (?n1 <= Z.to_nat (gap ?m 0) * (to_nat p * 200 + 200) + 20)%nat |- _ =>
    have Hf := fill_arith n1 _ _ (Z.to_nat (φ x)) H ltac:(lia); clear H end.
  set (P := if (p <? 1)%uint63 then 1%uint63 else p) in *.
  assert (HP : (1 <= φ P <= φ x)%Z).
  { subst P. destruct (p <? 1) eqn:Ep; [change (φ 1) with 1%Z; lia|].
    rewrite <- Bool.not_true_iff_false, ltb_spec in Ep. change (φ 1) with 1%Z in Ep. lia. }
  assert (GP : (Z.to_nat (gap P 1) <= Z.to_nat (φ x))%nat) by (unfold gap; change (φ 1) with 1%Z; lia).
  have Pw := pow_arith (Z.to_nat (φ P)) (Z.to_nat (φ p)) (Z.to_nat (φ x)) ltac:(lia) ltac:(lia) ltac:(lia).
  match goal with H : (?n2 <= Z.to_nat (gap P 1) * _ + 20)%nat |- _ =>
    have Hd := deepen_arith n2 _ _ _ (Z.to_nat (φ x)) H GP ltac:(lia) Pw; clear H end.
  rewrite gap0 in Hc' Hf.
  clear -Hc' Hf Hd ER pC. destruct (p <? 1); cbn; subst RHS; lia.
Qed.


Lemma final_arith N Mm L c :
  (c <= Mm * (N * 600 + 700) + N * (2 * (N * 50 + 300) * N ^ N + 100) + 1000)%nat ->
  (c <= 1500 * ((N + 1) ^ (N + 3) + (Mm + 1) * (N + L + 1)) + 1000)%nat.
Proof.
  intros H.
  assert (Q1 : (N ^ N <= (N + 1) ^ N)%nat) by (apply Nat.pow_le_mono_l; lia).
  assert (Q2 : (1 <= (N + 1) ^ N)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  rewrite Nat.pow_add_r in H |- *.
  remember ((N + 1) ^ N)%nat as Q eqn:EQ. remember (N ^ N)%nat as R eqn:ER.
  assert (A : (2 * (N * 50 + 300) * R <= 2 * (N * 50 + 300) * Q)%nat) by (apply Nat.mul_le_mono_l; lia).
  assert (B : (N * (2 * (N * 50 + 300) * R + 100) <= Q * (N + 1) ^ 3 * 800)%nat).
  { change ((N + 1) ^ 3)%nat with ((N + 1) * ((N + 1) * ((N + 1) * 1)))%nat. nia. }
  assert (C : (Mm * (N * 600 + 700) <= 700 * ((Mm + 1) * (N + L + 1)))%nat) by nia.
  lia.
Qed.

Theorem committees_time : exists c1 c2 : nat,
  forall (member_count : N)
  (first_names second_names : list String.string)
  (member_count_int : uint)
  (first_names_arr second_names_arr : array
  PrimString.string),
  valid_input member_count first_names second_names ->
  repr member_count_int member_count
  -> repr first_names_arr first_names ->
  repr second_names_arr second_names ->
  (cost3 committees_cost member_count_int first_names_arr second_names_arr <= c1 * ((size member_count_int + 1) ^ (size member_count_int + 3) + (size first_names_arr + 1) * (size member_count_int + Nat.log2 (size first_names_arr) + 1)) + c2)%nat.
Proof.
  exists 1500%nat, 1000%nat. intros n a b x y z Hv Hx Hy Hz.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  unfold cost3, committees_cost. csimpl.
  z0 committees_impl_cost. z1 committees_impl_cost.
  match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (committees_impl_cost stepsCM x ?xC) y ?yC) z ?zC =>
      genc X (committees_impl_time n a b x xC y yC z zC Hv Hx Hy Hz) end end.
  subst RHS.
  change (size x) with (Z.to_nat (φ x)).
  change (size y) with (Z.to_nat (φ (PArray.length@{Set} y))).
  apply final_arith. lia.
Qed.


Transparent PArray.make.
