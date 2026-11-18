(* Implementation of xormax (xormax.spec): a linear basis over GF(2).

   Code.  [xormax x] makes a flat basis [b = PArray.make 63 0], cell k
   holding 0 or a vector whose leading bit is k.  One pass over x inserts
   every number ([reduce]: from bit 62 down, a set bit k is cleared by
   xoring b.[k], or the number is stored in b.[k] when that cell is empty),
   then [greedy] walks the basis from bit 62 down and keeps r lxor b.[k]
   whenever it is larger than r.  All values are 63-bit [int]s; x is only
   read and b is threaded linearly.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) _] proof (template/polymul1), on the measure gap n j for
   the pass over x and on to_Z i for the two downward loops over the bits.

   Proof.  The math side has two spans: [inspan l] (the xor-sums of
   sublists of l, equivalent to the spec's [subset_xor]) and [cspan f n]
   (the xor-sums of subsets of f 0, ..., f (n-1)); both are the smallest
   xor-closed sets containing their generators ([*_closed], [*_min]).  The
   basis invariant [binv] says that each cell is in the span of the prefix
   read so far and each element of the prefix in the span of the cells,
   and that every nonzero cell k lies in [2^k, 2^(k+1)).  The greedy pass
   is the function [gm]; [gm_in] puts its result in the span and
   [gm_max] bounds every element of the span by it (comparison through
   the quotients by 2^k).

   Cost: [Elpi complexity] translates sumbool, bdec, reduce, build,
   greedy, xormax_impl and xormax (callee first); xormax_time bounds
   cost1 xormax_cost x by 2600 * (size x + 1) + 3000 (section Cost at
   the end). *)

From Xormax.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From KattisLib Require Import Cost.
Import ListNotations.

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
Elpi complexity sumbool.
Elpi complexity bdec.

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall m i : int,
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : to_Z (i + 1)%uint63 = (to_Z i + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_down : forall i : int,
  (0 <? i)%uint63 = true -> Zwf 0 (to_Z (i - 1)%uint63) (to_Z i).
Proof.
  intros i H. rewrite ltb_spec in H. change (to_Z 0%uint63) with 0%Z in H.
  assert (H1 : to_Z (i - 1)%uint63 = (to_Z i - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Code.
Local Open Scope uint63_scope.

(* Insert c, whose bits at i and above are clear, into the basis b. *)
Fixpoint reduce (b : array int) (c i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H}
    : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      if (c >> (i - 1)) =? 0 then reduce b c (i - 1) (Acc_inv H (dec_down i Hi))
      else
        let bk := b.[i - 1] in
        if bk =? 0 then b.[i - 1 <- c]
        else reduce b (c lxor bk) (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => b
  end.
Elpi complexity reduce.
#[global] Arguments reduce_cost : simpl never.

(* Insert x.[j], ..., x.[n-1]. *)
Fixpoint build (x : array uint) (n j : int) (b : array int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int :=
  match bdec (j <? n) with
  | left Hj =>
      build x n (j + 1) (reduce b x.[j] 63 (Zwf_well_founded 0 _))
        (Acc_inv H (dec_step n j Hj))
  | right _ => b
  end.
Elpi complexity build.
#[global] Arguments build_cost : simpl never.

(* Greedy maximum over the cells i-1, ..., 0, starting from r. *)
Fixpoint greedy (b : array int) (r i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H}
    : int :=
  match bdec (0 <? i) with
  | left Hi =>
      let r' := r lxor b.[i - 1] in
      greedy b (if r <? r' then r' else r) (i - 1) (Acc_inv H (dec_down i Hi))
  | right _ => r
  end.
Elpi complexity greedy.
#[global] Arguments greedy_cost : simpl never.

Definition xormax_impl (x : array uint) : uint :=
  let b := build x (PArray.length x) 0 (PArray.make 63 0)
             (Zwf_well_founded 0 _) in
  greedy b 0 63 (Zwf_well_founded 0 _).
Elpi complexity xormax_impl.
#[global] Arguments xormax_impl_cost : simpl never.

End Code.

Lemma reduce_eq : forall b c i H, reduce b c i H =
  match bdec (0 <? i)%uint63 with
  | left Hi =>
      if ((c >> (i - 1)) =? 0)%uint63 then reduce b c (i - 1)%uint63 (Acc_inv H (dec_down i Hi))
      else
        let bk := b.[(i - 1)%uint63] in
        if (bk =? 0)%uint63 then b.[(i - 1)%uint63 <- c]
        else reduce b (c lxor bk)%uint63 (i - 1)%uint63 (Acc_inv H (dec_down i Hi))
  | right _ => b
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_eq : forall x n j b H, build x n j b H =
  match bdec (j <? n)%uint63 with
  | left Hj =>
      build x n (j + 1)%uint63 (reduce b x.[j] 63%uint63 (Zwf_well_founded 0 _))
        (Acc_inv H (dec_step n j Hj))
  | right _ => b
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma greedy_eq : forall b r i H, greedy b r i H =
  match bdec (0 <? i)%uint63 with
  | left Hi =>
      let r' := (r lxor b.[(i - 1)%uint63])%uint63 in
      greedy b (if (r <? r')%uint63 then r' else r) (i - 1)%uint63
        (Acc_inv H (dec_down i Hi))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Math side: spans                                                    *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

Ltac xsolve :=
  apply N.bits_inj; intro;
  rewrite ?N.lxor_spec, ?N.bits_0;
  repeat match goal with |- context [N.testbit ?a ?n] => destruct (N.testbit a n) end;
  reflexivity.

Definition closed (S : N -> Prop) : Prop :=
  S 0 /\ forall u w, S u -> S w -> S (N.lxor u w).

Lemma closed_xor_l : forall S x v, closed S -> S x -> S (N.lxor v x) -> S v.
Proof.
  intros S x v [_ HS] Hx Hv.
  replace v with (N.lxor (N.lxor v x) x) by xsolve. auto.
Qed.

(* the xor-sums of the sublists of l *)
Fixpoint inspan (l : list N) (v : N) : Prop :=
  match l with
  | [] => v = 0
  | x :: r => inspan r v \/ inspan r (N.lxor v x)
  end.

Lemma inspan_closed : forall l, closed (inspan l).
Proof.
  induction l as [|x r [H0 Hx]]; split; simpl.
  - reflexivity.
  - intros u w -> ->. reflexivity.
  - left; exact H0.
  - intros u w [Hu|Hu] [Hw|Hw].
    + left; auto.
    + right. replace (N.lxor (N.lxor u w) x) with (N.lxor u (N.lxor w x)) by xsolve. auto.
    + right. replace (N.lxor (N.lxor u w) x) with (N.lxor (N.lxor u x) w) by xsolve. auto.
    + left. replace (N.lxor u w) with (N.lxor (N.lxor u x) (N.lxor w x)) by xsolve. auto.
Qed.

Lemma inspan_in : forall l x, In x l -> inspan l x.
Proof.
  induction l as [|a r IH]; simpl; intros x Hx; [contradiction|].
  destruct Hx as [<-|Hx].
  - right. rewrite N.lxor_nilpotent. exact (proj1 (inspan_closed r)).
  - left. auto.
Qed.

Lemma inspan_min : forall S, closed S -> forall l, (forall x, In x l -> S x) ->
  forall v, inspan l v -> S v.
Proof.
  intros S HS l. induction l as [|a r IH]; simpl; intros Hl v Hv.
  - subst. exact (proj1 HS).
  - destruct Hv as [Hv|Hv].
    + apply IH; auto.
    + apply (closed_xor_l S a v HS); [apply Hl; left; reflexivity|].
      apply IH; auto.
Qed.

Lemma inspan_app : forall l m v, inspan l v -> inspan (l ++ [m]) v.
Proof.
  intros l m. apply inspan_min; [apply inspan_closed|].
  intros x Hx. apply inspan_in. apply in_or_app. left; exact Hx.
Qed.

Lemma subset_inspan : forall a v, subset_xor a v <-> inspan a v.
Proof.
  unfold subset_xor, len. induction a as [|x r IH]; intros v; split.
  - intros [m [_ Hv]]. simpl. destruct m; simpl in Hv; symmetry; exact Hv.
  - simpl. intros ->. exists []. split; reflexivity.
  - intros [m [Hm Hv]]. destruct m as [|bb m]; [simpl in Hm; lia|].
    simpl in Hm. simpl in Hv. simpl. destruct bb.
    + right. apply IH. exists m. split; [lia|].
      rewrite <- Hv. simpl. xsolve.
    + left. apply IH. exists m. split; [lia|exact Hv].
  - simpl. intros [Hv|Hv]; apply IH in Hv; destruct Hv as [m [Hm Hv]].
    + exists (false :: m). simpl. split; [lia|exact Hv].
    + exists (true :: m). simpl. split; [lia|].
      rewrite Hv. xsolve.
Qed.

(* the xor-sums of the subsets of f 0, ..., f (n-1) *)
Fixpoint cspan (f : nat -> N) (n : nat) (v : N) : Prop :=
  match n with
  | O => v = 0
  | S n => cspan f n v \/ cspan f n (N.lxor v (f n))
  end.

Lemma cspan_closed : forall f n, closed (cspan f n).
Proof.
  intros f. induction n as [|n [H0 Hx]]; split; simpl.
  - reflexivity.
  - intros u w -> ->. reflexivity.
  - left; exact H0.
  - set (x := f n). intros u w [Hu|Hu] [Hw|Hw].
    + left; auto.
    + right. replace (N.lxor (N.lxor u w) x) with (N.lxor u (N.lxor w x)) by xsolve. auto.
    + right. replace (N.lxor (N.lxor u w) x) with (N.lxor (N.lxor u x) w) by xsolve. auto.
    + left. replace (N.lxor u w) with (N.lxor (N.lxor u x) (N.lxor w x)) by xsolve. auto.
Qed.

Lemma cspan_gen : forall f n k, (k < n)%nat -> cspan f n (f k).
Proof.
  intros f n. induction n as [|n IH]; intros k Hk; [lia|]. simpl.
  destruct (Nat.eq_dec k n) as [->|Hne].
  - right. rewrite N.lxor_nilpotent. exact (proj1 (cspan_closed f n)).
  - left. apply IH. lia.
Qed.

Lemma cspan_min : forall S, closed S -> forall f n, (forall k, (k < n)%nat -> S (f k)) ->
  forall v, cspan f n v -> S v.
Proof.
  intros S HS f n. induction n as [|n IH]; simpl; intros Hf v Hv.
  - subst. exact (proj1 HS).
  - destruct Hv as [Hv|Hv].
    + apply IH; auto.
    + apply (closed_xor_l S (f n) v HS); [apply Hf; lia|].
      apply IH; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: bits                                                     *)
(* ------------------------------------------------------------------ *)

(* a cell of index k is empty or has leading bit k *)
Definition ok_cell (k : nat) (v : N) : Prop :=
  v = 0 \/ (2 ^ N.of_nat k <= v < 2 * 2 ^ N.of_nat k).

Definition okf (f : nat -> N) (n : nat) : Prop :=
  forall k, (k < n)%nat -> ok_cell k (f k).

Lemma pow2_nz : forall p, 2 ^ p <> 0.
Proof. intros p. apply N.pow_nonzero. discriminate. Qed.

Lemma div_lxor : forall a b p, N.lxor a b / 2 ^ p = N.lxor (a / 2 ^ p) (b / 2 ^ p).
Proof. intros. rewrite <- !N.shiftr_div_pow2. apply N.shiftr_lxor. Qed.

Lemma lxor_lt_pow : forall a b p, a < 2 ^ p -> b < 2 ^ p -> N.lxor a b < 2 ^ p.
Proof.
  intros a b p Ha Hb.
  apply (N.div_small_iff _ _ (pow2_nz p)). rewrite div_lxor.
  rewrite (proj2 (N.div_small_iff _ _ (pow2_nz p)) Ha).
  rewrite (proj2 (N.div_small_iff _ _ (pow2_nz p)) Hb). reflexivity.
Qed.

Lemma cell_div : forall c p, 2 ^ p <= c < 2 * 2 ^ p -> c / 2 ^ p = 1.
Proof.
  intros c p [H1 H2]. pose proof (pow2_nz p) as Hp.
  assert (1 <= c / 2 ^ p).
  { rewrite <- (N.div_same (2 ^ p)) by exact Hp. apply N.Div0.div_le_mono. exact H1. }
  assert (c / 2 ^ p < 2).
  { apply N.Div0.div_lt_upper_bound. rewrite N.mul_comm. exact H2. }
  lia.
Qed.

Lemma lxor_1_neq : forall h, N.lxor h 1 <> h.
Proof.
  intros h E.
  assert (Hb : N.testbit (N.lxor h 1) 0 = N.testbit h 0) by (rewrite E; reflexivity).
  rewrite N.lxor_spec in Hb. destruct (N.testbit h 0); discriminate.
Qed.

Lemma lt_of_div : forall a b p, a / 2 ^ p < b / 2 ^ p -> a < b.
Proof.
  intros a b p H. destruct (N.lt_ge_cases a b) as [Hl|Hg]; [exact Hl|].
  apply (N.Div0.div_le_mono _ _ (2 ^ p)) in Hg. lia.
Qed.

Lemma flip_lt : forall r c p, c / 2 ^ p = 1 -> r <= N.lxor r c ->
  r / 2 ^ p < N.lxor (r / 2 ^ p) 1.
Proof.
  intros r c p Hc H. apply (N.Div0.div_le_mono _ _ (2 ^ p)) in H.
  rewrite div_lxor, Hc in H. pose proof (lxor_1_neq (r / 2 ^ p)). lia.
Qed.

Lemma flip_gt : forall r c p, c / 2 ^ p = 1 -> N.lxor r c <= r ->
  N.lxor (r / 2 ^ p) 1 < r / 2 ^ p.
Proof.
  intros r c p Hc H. apply (N.Div0.div_le_mono _ _ (2 ^ p)) in H.
  rewrite div_lxor, Hc in H. pose proof (lxor_1_neq (r / 2 ^ p)). lia.
Qed.

Lemma pow_S : forall n, 2 ^ N.of_nat (S n) = 2 * 2 ^ N.of_nat n.
Proof. intros n. rewrite Nat2N.inj_succ. apply N.pow_succ_r'. Qed.

Lemma cspan_lt : forall f n, okf f n -> forall t, cspan f n t -> t < 2 ^ N.of_nat n.
Proof.
  intros f n. induction n as [|n IH]; cbn [cspan]; intros Hok t Ht.
  - subst. simpl. lia.
  - assert (Hok' : okf f n) by (intros k Hk; apply Hok; lia).
    assert (Hc : f n < 2 * 2 ^ N.of_nat n).
    { destruct (Hok n ltac:(lia)) as [E|[_ E]]; [|exact E].
      rewrite E. pose proof (pow2_nz (N.of_nat n)). lia. }
    rewrite pow_S.
    destruct Ht as [Ht|Ht].
    + apply IH in Ht; [lia|exact Hok'].
    + apply IH in Ht; [|exact Hok'].
      replace t with (N.lxor (N.lxor t (f n)) (f n)) by xsolve.
      rewrite <- pow_S. apply lxor_lt_pow; rewrite pow_S; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Math side: the greedy pass                                          *)
(* ------------------------------------------------------------------ *)

Definition gstep (r c : N) : N := if r <? N.lxor r c then N.lxor r c else r.

Fixpoint gm (f : nat -> N) (n : nat) (r : N) : N :=
  match n with
  | O => r
  | S n => gm f n (gstep r (f n))
  end.

Lemma gm_in : forall f n r, exists t, cspan f n t /\ gm f n r = N.lxor r t.
Proof.
  intros f n. induction n as [|n IH]; intros r; simpl.
  - exists 0. split; [reflexivity|]. rewrite N.lxor_0_r. reflexivity.
  - destruct (IH (gstep r (f n))) as [t [Ht E]]. rewrite E. unfold gstep.
    destruct (r <? N.lxor r (f n)).
    + exists (N.lxor t (f n)). split.
      * right. replace (N.lxor (N.lxor t (f n)) (f n)) with t by xsolve. exact Ht.
      * xsolve.
    + exists t. split; [left; exact Ht|reflexivity].
Qed.

Lemma gm_max : forall f n, okf f n -> forall r t, cspan f n t -> N.lxor r t <= gm f n r.
Proof.
  intros f n. induction n as [|n IH]; intros Hok r t Ht; simpl in *.
  - subst. rewrite N.lxor_0_r. lia.
  - assert (Hok' : okf f n) by (intros k Hk; apply Hok; lia).
    assert (Hc : ok_cell n (f n)) by (apply Hok; lia).
    set (p := N.of_nat n) in *.
    unfold gstep.
    destruct Ht as [Ht|Ht].
    + pose proof (cspan_lt f n Hok' t Ht) as Htl.
      destruct (N.ltb_spec r (N.lxor r (f n))) as [Hlt|Hge].
      * destruct Hc as [Hc0|Hcb]; [rewrite Hc0, N.lxor_0_r in Hlt; lia|].
        apply cell_div in Hcb. change (N.of_nat n) with p in Hcb.
        eapply N.le_trans; [| apply IH; [exact Hok'| exact Ht]].
        apply N.lt_le_incl. apply (lt_of_div _ _ p).
        rewrite !div_lxor, (proj2 (N.div_small_iff _ _ (pow2_nz p)) Htl), Hcb, !N.lxor_0_r.
        apply (flip_lt r (f n) p Hcb). lia.
      * apply IH; assumption.
    + pose proof (cspan_lt f n Hok' _ Ht) as Htl.
      destruct (N.ltb_spec r (N.lxor r (f n))) as [Hlt|Hge].
      * replace (N.lxor r t) with (N.lxor (N.lxor r (f n)) (N.lxor t (f n))) by xsolve.
        apply IH; assumption.
      * destruct Hc as [Hc0|Hcb].
        -- rewrite Hc0, N.lxor_0_r in Ht. apply IH; assumption.
        -- apply cell_div in Hcb. change (N.of_nat n) with p in Hcb.
           pose proof (IH Hok' r 0 (proj1 (cspan_closed f n))) as H0.
           rewrite N.lxor_0_r in H0.
           apply N.lt_le_incl in H0 || idtac.
           eapply N.le_trans; [|exact H0].
           apply N.lt_le_incl. apply (lt_of_div _ _ p).
           replace (N.lxor r t) with (N.lxor (N.lxor r (f n)) (N.lxor t (f n))) by xsolve.
           rewrite div_lxor, (proj2 (N.div_small_iff _ _ (pow2_nz p)) Htl), N.lxor_0_r,
             div_lxor, Hcb.
           apply (flip_gt r (f n) p Hcb). exact Hge.
Qed.

(* ------------------------------------------------------------------ *)
(* Machine words                                                       *)
(* ------------------------------------------------------------------ *)

Definition nv (x : int) : N := Z.to_N (to_Z x).

Lemma nv_Z : forall x, Z.of_N (nv x) = to_Z x.
Proof. intros x. unfold nv. rewrite Z2N.id; [reflexivity|apply to_Z_bounded]. Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma nv_lt : forall x, nv x < 2 ^ 63.
Proof.
  intros x. pose proof (to_Z_bounded x) as B. rewrite <- nv_Z in B.
  change (2 ^ 63) with 9223372036854775808. lia.
Qed.

Lemma nv_lxor : forall x y, nv (x lxor y)%uint63 = N.lxor (nv x) (nv y).
Proof.
  intros x y. apply N2Z.inj. rewrite N2Z.inj_lxor, !nv_Z. apply lxor_spec'.
Qed.

Lemma nv_lsr : forall x y, nv (x >> y)%uint63 = nv x / 2 ^ nv y.
Proof.
  intros x y. apply N2Z.inj. rewrite N2Z.inj_div, N2Z.inj_pow, !nv_Z. apply lsr_spec.
Qed.

Lemma nv_eqb : forall x y, (x =? y)%uint63 = true <-> nv x = nv y.
Proof.
  intros x y. rewrite eqb_spec. split; intro E; [subst; reflexivity|].
  apply to_Z_inj. rewrite <- !nv_Z, E. reflexivity.
Qed.

Lemma nv_ltb : forall x y, (x <? y)%uint63 = (nv x <? nv y).
Proof.
  intros x y. apply Bool.eq_iff_eq_true.
  rewrite ltb_spec, N.ltb_lt, <- !nv_Z. lia.
Qed.

Lemma of_nat_to_nat : forall k : int, of_nat (Z.to_nat (to_Z k)) = k.
Proof.
  intros k. rewrite Z2Nat.id by apply to_Z_bounded. apply of_to_Z.
Qed.

Lemma to_Z_of_nat_small : forall k : nat, (k < 63)%nat -> to_Z (of_nat k) = Z.of_nat k.
Proof.
  intros k Hk. rewrite of_Z_spec, wB_val. apply Z.mod_small. lia.
Qed.

(* the cells of the basis, as a function on nat *)
Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Definition cf (b : array int) (k : nat) : N := nv b.[of_nat k].

Lemma cf_int : forall b (k : int), cf b (Z.to_nat (to_Z k)) = nv b.[k].
Proof. intros b k. unfold cf. rewrite of_nat_to_nat. reflexivity. Qed.

Lemma cf_set : forall (b : array int) (k : int) (c : int) (k' : nat),
  PArray.length b = 63%uint63 -> (to_Z k < 63)%Z -> (k' < 63)%nat ->
  cf (b.[k <- c]) k' = if Nat.eqb k' (Z.to_nat (to_Z k)) then nv c else cf b k'.
Proof.
  intros b k c k' Hl Hk Hk'. unfold cf.
  destruct (Nat.eqb_spec k' (Z.to_nat (to_Z k))) as [->|Hne].
  - rewrite of_nat_to_nat. rewrite aget_set_same; [reflexivity|].
    rewrite Hl, ltb_spec. change (to_Z 63%uint63) with 63%Z. exact Hk.
  - rewrite aget_set_other; [reflexivity|].
    intro E. apply Hne. rewrite E. rewrite to_Z_of_nat_small by exact Hk'. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* reduce                                                              *)
(* ------------------------------------------------------------------ *)

Lemma reduce_spec : forall (b : array int) (x : N),
  PArray.length b = 63%uint63 -> okf (cf b) 63 ->
  forall z (i c : int) (H : Acc (Zwf 0) (to_Z i)), to_Z i = z -> (to_Z i <= 63)%Z ->
  nv c < 2 ^ Z.to_N (to_Z i) -> cspan (cf b) 63 (N.lxor x (nv c)) ->
  (reduce b c i H = b /\ cspan (cf b) 63 x) \/
  (exists (k c' : int), (to_Z k < 63)%Z /\ reduce b c i H = b.[k <- c'] /\
     nv b.[k] = 0 /\ ok_cell (Z.to_nat (to_Z k)) (nv c') /\
     cspan (cf b) 63 (N.lxor x (nv c'))).
Proof.
  intros b x Hl Hok z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c H Hz Hi63 Hc Hs.
  rewrite reduce_eq. destruct (bdec (0 <? i)%uint63) as [Hi|Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'. change (to_Z 0%uint63) with 0%Z in Hi'.
    assert (Hk : to_Z (i - 1)%uint63 = (to_Z i - 1)%Z) by sia.
    assert (Hdec : Zwf 0 (to_Z (i - 1)%uint63) z) by (rewrite <- Hz; apply dec_down; exact Hi).
    set (k := (i - 1)%uint63) in *.
    set (p := Z.to_N (to_Z k)).
    assert (Hpk : 2 ^ Z.to_N (to_Z i) = 2 * 2 ^ p).
    { unfold p. rewrite Hk. replace (Z.to_N (to_Z i)) with (N.succ (Z.to_N (to_Z i - 1))) by lia.
      apply N.pow_succ_r'. }
    destruct ((c >> k) =? 0)%uint63 eqn:E.
    + apply nv_eqb in E. rewrite nv_lsr in E. change (nv 0%uint63) with 0 in E.
      apply (N.div_small_iff _ _ (pow2_nz _)) in E.
      apply (IH (to_Z k) Hdec k c _ eq_refl); [lia| exact E| exact Hs].
    + assert (Hcge : 2 ^ p <= nv c).
      { destruct (N.lt_ge_cases (nv c) (2 ^ p)) as [Hlt|Hge]; [|exact Hge].
        exfalso. assert (E' : (c >> k =? 0)%uint63 = true); [|rewrite E' in E; discriminate].
        apply nv_eqb. rewrite nv_lsr. apply (N.div_small_iff _ _ (pow2_nz _)). exact Hlt. }
      cbv zeta.
      destruct (b.[k] =? 0)%uint63 eqn:E2.
      * right. exists k, c. split; [lia|]. split; [reflexivity|]. split.
        { apply nv_eqb in E2. exact E2. }
        split; [|exact Hs].
        right. replace (N.of_nat (Z.to_nat (to_Z k))) with p by (unfold p; lia). lia.
      * assert (Hbk : ok_cell (Z.to_nat (to_Z k)) (nv b.[k])).
        { rewrite <- cf_int. apply Hok. lia. }
        destruct Hbk as [Hbk|Hbk].
        { exfalso. assert (E' : (b.[k] =? 0)%uint63 = true) by (apply nv_eqb; exact Hbk).
          rewrite E' in E2. discriminate. }
        replace (N.of_nat (Z.to_nat (to_Z k))) with p in Hbk by (unfold p; lia).
        apply (IH (to_Z k) Hdec k (c lxor b.[k])%uint63 _ eq_refl); [lia| |].
        -- rewrite nv_lxor. fold p. apply (N.div_small_iff _ _ (pow2_nz _)).
           rewrite div_lxor, (cell_div (nv c) p), (cell_div (nv b.[k]) p) by lia.
           reflexivity.
        -- rewrite nv_lxor.
           replace (N.lxor x (N.lxor (nv c) (nv b.[k])))
             with (N.lxor (N.lxor x (nv c)) (nv b.[k])) by xsolve.
           apply (proj2 (cspan_closed (cf b) 63)); [exact Hs|].
           rewrite <- cf_int. apply cspan_gen. lia.
  - left. split; [reflexivity|].
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. change (to_Z 0%uint63) with 0%Z in Hi.
    assert (Hi0 : to_Z i = 0%Z) by (pose proof (to_Z_bounded i); lia).
    rewrite Hi0 in Hc. simpl in Hc. assert (Hc0 : nv c = 0) by lia.
    rewrite Hc0, N.lxor_0_r in Hs. exact Hs.
Qed.

(* ------------------------------------------------------------------ *)
(* build                                                               *)
(* ------------------------------------------------------------------ *)

Definition binv (a : list N) (j : nat) (b : array int) : Prop :=
  PArray.length b = 63%uint63 /\ okf (cf b) 63 /\
  (forall k, (k < 63)%nat -> inspan (firstn j a) (cf b k)) /\
  (forall y, In y (firstn j a) -> cspan (cf b) 63 y).

Lemma firstn_snoc : forall (l : list N) j m, nth_error l j = Some m ->
  firstn (S j) l = firstn j l ++ [m].
Proof.
  induction l as [|h l IH]; intros j m E; destruct j; simpl in *; try discriminate.
  - injection E as ->. reflexivity.
  - f_equal. apply IH. exact E.
Qed.

Lemma repr_len : forall (x : array uint) (a : list N), repr x a ->
  to_Z (PArray.length x) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_get : forall (x : array uint) (a : list N), repr x a ->
  forall i : int, (to_Z i < Z.of_nat (List.length a))%Z ->
  nth_error a (Z.to_nat (to_Z i)) = Some (nv x.[i]).
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (to_Z i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite of_nat_to_nat in Hr.
  unfold nv. rewrite Hr. exact Hm.
Qed.

Lemma binv_step : forall a j m b b', nth_error a j = Some m -> binv a j b ->
  (b' = b /\ cspan (cf b) 63 m) \/
  (exists (k c' : int), (to_Z k < 63)%Z /\ b' = b.[k <- c'] /\
     nv b.[k] = 0 /\ ok_cell (Z.to_nat (to_Z k)) (nv c') /\
     cspan (cf b) 63 (N.lxor m (nv c'))) ->
  binv a (S j) b'.
Proof.
  intros a j m b b' Hm [Hl [Hok [Hg Hy]]] Hr.
  unfold binv. rewrite (firstn_snoc a j m Hm).
  set (l := firstn j a) in *.
  assert (Hsub : forall v, cspan (cf b) 63 v -> inspan l v).
  { apply cspan_min; [apply inspan_closed|exact Hg]. }
  destruct Hr as [[-> Hs]|(k & c' & Hk & -> & Hb0 & Hc' & Hs)].
  - split; [exact Hl|]. split; [exact Hok|]. split.
    + intros k' Hk'. apply inspan_app. apply Hg. exact Hk'.
    + intros y Hy'. apply in_app_or in Hy'. destruct Hy' as [Hy'|[<-|[]]].
      * apply Hy. exact Hy'.
      * exact Hs.
  - assert (Hcf : forall k', (k' < 63)%nat ->
      cf (b.[k <- c']) k' = if Nat.eqb k' (Z.to_nat (to_Z k)) then nv c' else cf b k')
      by (intros; apply cf_set; assumption).
    assert (Hsub2 : forall v, cspan (cf b) 63 v -> cspan (cf (b.[k <- c'])) 63 v).
    { apply cspan_min; [apply cspan_closed|]. intros k' Hk'.
      destruct (Nat.eqb_spec k' (Z.to_nat (to_Z k))) as [->|Hne].
      - rewrite cf_int, Hb0. exact (proj1 (cspan_closed _ _)).
      - assert (E : cf (b.[k <- c']) k' = cf b k')
          by (rewrite Hcf by exact Hk'; destruct (Nat.eqb_spec k' (Z.to_nat (to_Z k))); [lia|reflexivity]).
        rewrite <- E. apply cspan_gen. exact Hk'. }
    assert (Hnew : cspan (cf (b.[k <- c'])) 63 (nv c')).
    { replace (nv c') with (cf (b.[k <- c']) (Z.to_nat (to_Z k))).
      - apply cspan_gen. lia.
      - rewrite Hcf by lia. rewrite Nat.eqb_refl. reflexivity. }
    split; [rewrite alength_set; exact Hl|]. split; [|split].
    + intros k' Hk'. rewrite Hcf by exact Hk'.
      destruct (Nat.eqb_spec k' (Z.to_nat (to_Z k))) as [->|Hne]; [exact Hc'|].
      apply Hok. exact Hk'.
    + intros k' Hk'. rewrite Hcf by exact Hk'.
      destruct (Nat.eqb_spec k' (Z.to_nat (to_Z k))) as [->|Hne].
      * replace (nv c') with (N.lxor m (N.lxor m (nv c'))) by xsolve.
        apply (proj2 (inspan_closed _)).
        -- apply inspan_in. apply in_or_app. right. left. reflexivity.
        -- apply inspan_app. apply Hsub. exact Hs.
      * apply inspan_app. apply Hg. exact Hk'.
    + intros y Hy'. apply in_app_or in Hy'. destruct Hy' as [Hy'|[->|[]]].
      * apply Hsub2. apply Hy. exact Hy'.
      * replace y with (N.lxor (nv c') (N.lxor y (nv c'))) by xsolve.
        apply (proj2 (cspan_closed _ _)); [exact Hnew|].
        apply Hsub2. exact Hs.
Qed.

Lemma build_spec : forall (a : list N) (x : array uint), repr x a ->
  forall z (j : int) (b : array int) (H : Acc (Zwf 0) (gap (PArray.length x) j)),
  gap (PArray.length x) j = z -> (to_Z j <= to_Z (PArray.length x))%Z ->
  binv a (Z.to_nat (to_Z j)) b ->
  binv a (List.length a) (build x (PArray.length x) j b H).
Proof.
  intros a x Ha z.
  pose proof (repr_len x a Ha) as Lx.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j b H Hz Hj Hb.
  rewrite build_eq. destruct (bdec (j <? PArray.length x)%uint63) as [Hlt|Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hj1 : to_Z (j + 1)%uint63 = (to_Z j + 1)%Z) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    rewrite Hj1, Z2Nat.inj_add by (try lia; apply to_Z_bounded).
    rewrite Nat.add_1_r.
    pose proof (repr_get x a Ha j ltac:(lia)) as Hm.
    destruct Hb as (Hl & Hok & Hg & Hy).
    apply (binv_step a _ _ b _ Hm (conj Hl (conj Hok (conj Hg Hy)))).
    apply (reduce_spec b (nv x.[j]) Hl Hok _ 63%uint63 x.[j] _ eq_refl).
    + change (to_Z 63%uint63) with 63%Z. lia.
    + change (Z.to_N (to_Z 63%uint63)) with 63%N. apply nv_lt.
    + rewrite N.lxor_nilpotent. exact (proj1 (cspan_closed _ _)).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    replace (List.length a) with (Z.to_nat (to_Z j)) by lia. exact Hb.
Qed.

(* ------------------------------------------------------------------ *)
(* greedy                                                              *)
(* ------------------------------------------------------------------ *)

Lemma greedy_spec : forall (b : array int) z (r i : int) (H : Acc (Zwf 0) (to_Z i)),
  to_Z i = z -> (to_Z i <= 63)%Z ->
  nv (greedy b r i H) = gm (cf b) (Z.to_nat (to_Z i)) (nv r).
Proof.
  intros b z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r i H Hz Hi63.
  rewrite greedy_eq. destruct (bdec (0 <? i)%uint63) as [Hi|Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'. change (to_Z 0%uint63) with 0%Z in Hi'.
    assert (Hk : to_Z (i - 1)%uint63 = (to_Z i - 1)%Z) by sia.
    assert (Hdec : Zwf 0 (to_Z (i - 1)%uint63) z) by (rewrite <- Hz; apply dec_down; exact Hi).
    cbv zeta.
    rewrite (IH _ Hdec _ _ _ eq_refl) by lia.
    replace (Z.to_nat (to_Z i)) with (S (Z.to_nat (to_Z (i - 1)%uint63))) by lia.
    simpl. f_equal. unfold gstep. rewrite cf_int, <- nv_lxor, nv_ltb.
    destruct (nv r <? nv (r lxor b.[(i - 1)%uint63])%uint63); reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. change (to_Z 0%uint63) with 0%Z in Hi.
    replace (Z.to_nat (to_Z i)) with O by (pose proof (to_Z_bounded i); lia).
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma xormax_impl_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists o : N, repr (xormax_impl x) o /\ xormax_spec a o.
Proof.
  intros a x _ Ha.
  pose proof (repr_len x a Ha) as Lx.
  set (b := build x (PArray.length x) 0%uint63 (PArray.make 63 0%uint63)
              (Zwf_well_founded 0 _)).
  assert (Hb : binv a (List.length a) b).
  { apply (build_spec a x Ha _ 0%uint63 _ _ eq_refl).
    - change (to_Z 0%uint63) with 0%Z. pose proof (to_Z_bounded (PArray.length x)). lia.
    - change (to_Z 0%uint63) with 0%Z. unfold binv. change (Z.to_nat 0) with O.
      cbn [firstn]. split; [reflexivity|]. split; [|split].
      + intros k Hk. left. unfold cf. rewrite aget_make. reflexivity.
      + intros k Hk. cbn [inspan]. unfold cf. rewrite aget_make. reflexivity.
      + intros y [] . }
  destruct Hb as (Hl & Hok & Hg & Hy).
  rewrite firstn_all in Hg, Hy.
  assert (Hspan : forall v, cspan (cf b) 63 v <-> subset_xor a v).
  { intros v. rewrite subset_inspan. split.
    - apply cspan_min; [apply inspan_closed|exact Hg].
    - apply inspan_min; [apply cspan_closed|exact Hy]. }
  exists (nv (xormax_impl x)). split; [reflexivity|].
  assert (E : nv (xormax_impl x) = gm (cf b) 63 0).
  { unfold xormax_impl. cbv zeta. rewrite (greedy_spec _ _ 0%uint63 63%uint63 _ eq_refl).
    - reflexivity.
    - change (to_Z 63%uint63) with 63%Z. lia. }
  rewrite E. split.
  - destruct (gm_in (cf b) 63 0) as [t [Ht Et]]. rewrite Et, N.lxor_0_l.
    exact (proj1 (Hspan t) Ht).
  - intros v Hv. apply (proj2 (Hspan v)) in Hv.
    pose proof (gm_max (cf b) 63 Hok 0 v Hv) as Hm. rewrite N.lxor_0_l in Hm. exact Hm.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition xormax : array uint -> uint := xormax_impl.
Elpi complexity xormax.

Definition xormax_correct : forall (a : list N) (x : array uint),
  valid_input a -> repr x a ->
  exists o : N, repr (xormax x) o /\ xormax_spec a o
  := xormax_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

(* One lemma per loop, by induction on a nat bound of its measure:
   reduce from i <= 40 * i + 20 and greedy from i <= 40 * i + 20 (at
   most i bits each), build from j <= 2600 * (n - j) + 20 (one reduce
   from bit 63, <= 2540, per entry); xormax costs at most
   2600 * (n + 1) + 3000.  cbn must not unfold φ (the Acc index of
   reduce and greedy): to_Z is made simpl never for this section. *)

From Stdlib Require Import ssreflect.
Open Scope uint63_scope.
Local Arguments Uint63.to_Z : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

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
  end.

Lemma reduce_time b bC c cC i iC H HC :
  (cost (extract (extract (extract (reduce_cost stepsCM b bC) c cC) i iC) H HC)
     <= Z.to_nat (φ i) * 40 + 20)%nat.
Proof.
  unfold reduce_cost. cbn.
  match goal with |- context [@cost ?T (?G b bC c cC i iC H HC)] =>
    assert (HG : forall k b bC c cC i iC H HC, (Z.to_nat (φ i) <= k)%nat ->
       (cost (G b bC c cC i iC H HC) <= k * 40 + 20)%nat) end.
  { induction k as [|k IH]; intros b' bC' c' cC' i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (0 <? i') (bool_w (0 <? i'))) as HB;
      cost_destruct (bdec (0 <? i')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). change (φ 0) with 0%Z in H0. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt. change (φ 0) with 0%Z in Hlt.
      assert (Hk' : (Z.to_nat (φ (i' - 1)) <= k)%nat).
      { assert (φ (i' - 1) = φ i' - 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      cost_destruct (c' >> (i' - 1) =? 0); cost_simpl.
      + match goal with |- context [@cost ?T (?G' ?bb ?bw ?cc ?cw (i' - 1)%uint63 ?w ?h ?e)] =>
          have HI := (IH bb bw cc cw (i' - 1)%uint63 w h e Hk' : (@cost T (G' bb bw cc cw (i' - 1)%uint63 w h e) <= _)%nat) end.
        lia.
      + cost_destruct (b'.[i' - 1] =? 0); cost_simpl.
        * set_simpl. lia.
        * match goal with |- context [@cost ?T (?G' ?bb ?bw ?cc ?cw (i' - 1)%uint63 ?w ?h ?e)] =>
            have HI := (IH bb bw cc cw (i' - 1)%uint63 w h e Hk' : (@cost T (G' bb bw cc cw (i' - 1)%uint63 w h e) <= _)%nat) end.
          lia.
    - lia. }
  match goal with |- context [@cost ?T (?G b bC c cC i iC H HC)] =>
    exact (HG _ b bC c cC i iC H HC (le_n _) : (@cost T (G b bC c cC i iC H HC) <= _)%nat) end.
Qed.


Lemma greedy_time b bC r rC i iC H HC :
  (cost (extract (extract (extract (greedy_cost stepsCM b bC) r rC) i iC) H HC)
     <= Z.to_nat (φ i) * 40 + 20)%nat.
Proof.
  unfold greedy_cost. cbn.
  match goal with |- context [@cost ?T (?G b bC r rC i iC H HC)] =>
    assert (HG : forall k b bC r rC i iC H HC, (Z.to_nat (φ i) <= k)%nat ->
       (cost (G b bC r rC i iC H HC) <= k * 40 + 20)%nat) end.
  { induction k as [|k IH]; intros b' bC' r' rC' i' iC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (0 <? i') (bool_w (0 <? i'))) as HB;
      cost_destruct (bdec (0 <? i')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). change (φ 0) with 0%Z in H0. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt. change (φ 0) with 0%Z in Hlt.
      assert (Hk' : (Z.to_nat (φ (i' - 1)) <= k)%nat).
      { assert (φ (i' - 1) = φ i' - 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      cost_destruct (r' <? r' lxor b'.[i' - 1]); cost_simpl.
      + match goal with |- context [@cost ?T (?G' ?bb ?bw ?cc ?cw (i' - 1)%uint63 ?w ?h ?e)] =>
          have HI := (IH bb bw cc cw (i' - 1)%uint63 w h e Hk' : (@cost T (G' bb bw cc cw (i' - 1)%uint63 w h e) <= _)%nat) end.
        lia.
      + match goal with |- context [@cost ?T (?G' ?bb ?bw ?cc ?cw (i' - 1)%uint63 ?w ?h ?e)] =>
          have HI := (IH bb bw cc cw (i' - 1)%uint63 w h e Hk' : (@cost T (G' bb bw cc cw (i' - 1)%uint63 w h e) <= _)%nat) end.
        lia.
    - lia. }
  match goal with |- context [@cost ?T (?G b bC r rC i iC H HC)] =>
    exact (HG _ b bC r rC i iC H HC (le_n _) : (@cost T (G b bC r rC i iC H HC) <= _)%nat) end.
Qed.

Lemma build_time x xC n nC j jC b bC H HC :
  (cost (extract (extract (extract (extract (build_cost stepsCM x xC) n nC) j jC) b bC) H HC)
     <= Z.to_nat (gap n j) * 2600 + 20)%nat.
Proof.
  unfold build_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC n nC j jC b bC H HC)] =>
    assert (HG : forall k j jC b bC H HC, (Z.to_nat (gap n j) <= k)%nat ->
       (cost (G x xC n nC j jC b bC H HC) <= k * 2600 + 20)%nat) end.
  { induction k as [|k IH]; intros j' jC' b' bC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (j' <? n) (bool_w (j' <? n))) as HB;
      cost_destruct (bdec (j' <? n)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hk' : (Z.to_nat (gap n (j' + 1)) <= k)%nat).
      { unfold gap in *. assert (φ (j' + 1) = φ j' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      change (cost (reduce_cost stepsCM b' bC')) with 0%nat.
      change (cost (extract (reduce_cost stepsCM b' bC') x.[j'] (array_elems xC j'))) with 0%nat.
      change (cost (extract (extract (reduce_cost stepsCM b' bC') x.[j'] (array_elems xC j')) 63%uint63 (int_val stepsCM 63))) with 0%nat.
      match goal with |- context [@cost ?T (extract (extract (extract (reduce_cost stepsCM b' bC') ?xx ?xw) ?ii ?iw) ?hh ?hw)] =>
        let Hc := fresh "Hc" in
        have Hc := (reduce_time b' bC' xx xw ii iw hh hw : (@cost T (extract (extract (extract (reduce_cost stepsCM b' bC') xx xw) ii iw) hh hw) <= _)%nat);
        revert Hc; generalize (@cost T (extract (extract (extract (reduce_cost stepsCM b' bC') xx xw) ii iw) hh hw)); intros ? Hc end.
      change (Z.to_nat (φ 63)) with 63%nat in Hc.
      match goal with |- context [@cost ?T (?G' x xC n nC (j' + 1)%uint63 ?w ?bb ?bw ?h ?e)] =>
          have HI := (IH (j' + 1)%uint63 w bb bw h e Hk' : (@cost T (G' x xC n nC (j' + 1)%uint63 w bb bw h e) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC n nC j jC b bC H HC)] =>
    exact (HG _ j jC b bC H HC (le_n _) : (@cost T (G x xC n nC j jC b bC H HC) <= _)%nat) end.
Qed.

Lemma xormax_impl_time x xC :
  (cost (xormax_impl_cost stepsCM x xC) <= size x * 2600 + 3000)%nat.
Proof.
  unfold xormax_impl_cost. cost_simpl.
  match goal with |- context [@cost ?T (extract (extract (extract (extract (build_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h) ?i ?j)] =>
    let X := constr:(extract (extract (extract (extract (build_cost stepsCM a b) c d) e f) g h) i j) in
    let Hc := fresh "Hb" in
    have Hc := (build_time a b c d e f g h i j : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end.
  match goal with |- context [@cost ?T (extract (extract (extract (greedy_cost stepsCM ?a ?b) ?c ?d) ?e ?f) ?g ?h)] =>
    let X := constr:(extract (extract (extract (greedy_cost stepsCM a b) c d) e f) g h) in
    let Hc := fresh "Hg" in
    have Hc := (greedy_time a b c d e f g h : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end.
  repeat match goal with |- context [@cost ?T ?X] =>
    let v := eval vm_compute in (@cost T X) in change (@cost T X) with v end.
  change (Z.to_nat (φ 63)) with 63%nat in Hg.
  assert (E : Z.to_nat (gap (length x) 0) = size x).
  { unfold gap. change (φ 0) with 0%Z. rewrite Z.sub_0_r. reflexivity. }
  rewrite E in Hb. lia.
Qed.

Theorem xormax_time : exists c1 c2 : nat, forall numbers_arr : array uint,
  (cost1 xormax_cost numbers_arr <= c1 * (size numbers_arr + 1) + c2)%nat.
Proof.
  exists 2600%nat, 3000%nat. intros x.
  match goal with |- (_ <= ?r)%nat => remember r as R eqn:ER end.
  unfold cost1, xormax_cost. cost_simpl.
  match goal with |- (@cost ?T ?X <= _)%nat =>
    have HX := (xormax_impl_time x (witness x) : (@cost T X <= _)%nat) end.
  subst R. lia.
Qed.
Print Assumptions xormax_time.
