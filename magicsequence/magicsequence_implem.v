(* Implementation of magicsequence (magicsequence.spec). *)

From Magicsequence.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.
Open Scope nat_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

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
  (i <? m)%uint63 = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1))%uint63 = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

Section Program.
Local Open Scope uint63_scope.

(* Number of buckets of a counting-sort pass: 16-bit digits. *)
Definition K : int := 65536.
Definition mask : int := 65535.

(* Cells i .. n-1 of arr receive S[i] .. S[n-1], t being S[i]; m is the
   running maximum of the terms written; lo and hi are the histograms of
   the low and high 16-bit digits of the terms written.  The digit
   expressions are written inline (no helper call in the loop body). *)
Fixpoint gen_loop (a b c n i t m : int) (arr lo hi : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H}
    : array int * int * array int * array int :=
  match bdec (i <? n) with
  | left Hi =>
      let dl := t land mask in
      let dh := (t >> 16) land mask in
      let kl := lo.[dl] in
      let kh := hi.[dh] in
      gen_loop a b c n (i + 1) ((t * b + a) mod c)
        (if m <? t then t else m) arr.[i <- t]
        lo.[dl <- kl + 1] hi.[dh <- kh + 1]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (arr, m, lo, hi)
  end.

(* Exclusive prefix sums of cnt, in place. *)
Fixpoint prefix_loop (e acc : int) (cnt : array int)
    (H : Acc (Zwf 0) (gap K e)) {struct H} : array int :=
  match bdec (e <? K) with
  | left He =>
      let k := cnt.[e] in
      prefix_loop (e + 1) (acc + k) cnt.[e <- acc]
        (Acc_inv H (dec_step K e He))
  | right _ => cnt
  end.

(* Stable placement: src[i] goes to the next free slot of its bucket; the
   digit (e >> s) land mask is written inline. *)
Fixpoint place_loop (s n : int) (src : array int) (i : int) (cnt dst : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let e := src.[i] in
      let d := (e >> s) land mask in
      let p := cnt.[d] in
      place_loop s n src (i + 1) cnt.[d <- p + 1] dst.[p <- e]
        (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.

(* One stable counting-sort pass on the digit at bit s, src into dst, cnt
   being the histogram of that digit over src (taken during generation). *)
Definition pass (s n : int) (src cnt dst : array int) : array int :=
  let cnt := prefix_loop 0 0 cnt (Zwf_well_founded 0 (gap K 0)) in
  place_loop s n src 0 cnt dst (Zwf_well_founded 0 (gap n 0)).

(* The Horner hash of r[i] .. r[n-1], from v. *)
Fixpoint hash_loop (x y n i v : int) (r : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : int :=
  match bdec (i <? n) with
  | left Hi =>
      hash_loop x y n (i + 1) ((v * x + r.[i]) mod y) r
        (Acc_inv H (dec_step n i Hi))
  | right _ => v
  end.

Definition magic_impl (n a b c x y : int) : int :=
  match gen_loop a b c n 0 a 0 (PArray.make n 0) (PArray.make K 0) (PArray.make K 0)
          (Zwf_well_founded 0 (gap n 0)) with
  | (g, m, lo, hi) =>
      let r1 := pass 0 n g lo (PArray.make n 0) in
      let r := if m <? K then r1 else pass 16 n r1 hi g in
      hash_loop x y n 0 0 r (Zwf_well_founded 0 (gap n 0))
  end.

End Program.

(* Proof side only: the 16-bit digit of e at bit s, the expression the
   loops write inline.  The program never calls it. *)
Definition digit (s e : int) : int := ((e >> s) land mask)%uint63.

Lemma gen_loop_eq : forall a b c n i t m arr lo hi H,
  gen_loop a b c n i t m arr lo hi H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      gen_loop a b c n (i + 1)%uint63 ((t * b + a) mod c)%uint63
        (if (m <? t)%uint63 then t else m) arr.[i <- t]
        lo.[digit 0 t <- (lo.[digit 0 t] + 1)%uint63]
        hi.[digit 16 t <- (hi.[digit 16 t] + 1)%uint63]
        (Acc_inv H (dec_step n i Hi))
  | right _ => (arr, m, lo, hi)
  end.
Proof.
  intros. destruct H. cbn [gen_loop].
  replace (t land mask)%uint63 with (digit 0 t); [reflexivity|].
  unfold digit. f_equal. apply to_Z_inj. rewrite lsr_spec. change (φ 0) with 0%Z.
  rewrite Z.pow_0_r, Z.div_1_r. reflexivity.
Qed.

Lemma prefix_loop_eq : forall e acc cnt H,
  prefix_loop e acc cnt H =
  match bdec (e <? K)%uint63 with
  | left He =>
      prefix_loop (e + 1)%uint63 (acc + cnt.[e])%uint63 cnt.[e <- acc]
        (Acc_inv H (dec_step K e He))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma place_loop_eq : forall s n src i cnt dst H,
  place_loop s n src i cnt dst H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      place_loop s n src (i + 1)%uint63
        cnt.[digit s src.[i] <- (cnt.[digit s src.[i]] + 1)%uint63]
        dst.[cnt.[digit s src.[i]] <- src.[i]]
        (Acc_inv H (dec_step n i Hi))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma hash_loop_eq : forall x y n i v r H,
  hash_loop x y n i v r H =
  match bdec (i <? n)%uint63 with
  | left Hi =>
      hash_loop x y n (i + 1)%uint63 ((v * x + r.[i]) mod y)%uint63 r
        (Acc_inv H (dec_step n i Hi))
  | right _ => v
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The list model of a counting-sort pass                              *)
(* ------------------------------------------------------------------ *)

(* The number of buckets, as an opaque nat (no unary 65536 in proofs). *)
Definition KN : nat := N.to_nat 65536.
Lemma KN_Z : Z.of_nat KN = 65536%Z.
Proof. reflexivity. Qed.
Global Opaque KN.

(* The 16-bit digit of e at bit s. *)
Definition keyN (s e : N) : N := ((e / 2 ^ s) mod 65536)%N.

(* Bucket d: the elements of L of digit d, in order. *)
Definition blk (s : N) (L : list N) (d : nat) : list N :=
  filter (fun e => N.eqb (keyN s e) (N.of_nat d)) L.
Arguments blk : simpl never.

(* The stable counting sort of L on the digit at bit s. *)
Definition csort (s : N) (L : list N) : list N := flat_map (blk s L) (seq 0 KN).

(* Where bucket d starts in csort s L. *)
Definition start (s : N) (L : list N) (d : nat) : nat :=
  List.length (flat_map (blk s L) (seq 0 d)).

Lemma keyN_lt : forall s e, (keyN s e < 65536)%N.
Proof. intros. unfold keyN. apply N.mod_lt. discriminate. Qed.

Lemma blk_nil : forall s d, blk s [] d = [].
Proof. reflexivity. Qed.

Lemma blk_cons : forall s a L d,
  blk s (a :: L) d =
  if N.eqb (keyN s a) (N.of_nat d) then a :: blk s L d else blk s L d.
Proof. reflexivity. Qed.

Lemma blk_app : forall s l1 l2 d, blk s (l1 ++ l2) d = blk s l1 d ++ blk s l2 d.
Proof. intros. unfold blk. apply filter_app. Qed.

Lemma blk_In : forall s L d x, In x (blk s L d) <-> In x L /\ keyN s x = N.of_nat d.
Proof.
  intros. unfold blk. rewrite filter_In, N.eqb_eq. reflexivity.
Qed.

Lemma blk_length : forall s L d, List.length (blk s L d) <= List.length L.
Proof.
  intros s L d. induction L as [|a L IH]; [simpl; lia|].
  rewrite blk_cons. destruct (N.eqb _ _); simpl; lia.
Qed.

Lemma fm_out : forall s a L k,
  k <= N.to_nat (keyN s a) ->
  flat_map (blk s (a :: L)) (seq 0 k) = flat_map (blk s L) (seq 0 k).
Proof.
  intros s a L k. induction k as [|k IH]; intros Hk; [reflexivity|].
  rewrite seq_S, !flat_map_app, IH by lia. simpl. rewrite blk_cons.
  destruct (N.eqb_spec (keyN s a) (N.of_nat k)); [lia|reflexivity].
Qed.

Lemma fm_in : forall s a L k,
  N.to_nat (keyN s a) < k ->
  Permutation (flat_map (blk s (a :: L)) (seq 0 k))
              (a :: flat_map (blk s L) (seq 0 k)).
Proof.
  intros s a L k. induction k as [|k IH]; intros Hk; [lia|].
  rewrite seq_S, !flat_map_app. simpl. rewrite !app_nil_r, blk_cons.
  destruct (N.eqb_spec (keyN s a) (N.of_nat k)) as [E|E].
  - rewrite fm_out by lia. apply Permutation_sym, Permutation_middle.
  - rewrite app_comm_cons. apply Permutation_app_tail. apply IH. lia.
Qed.

Lemma csort_perm : forall s L, Permutation (csort s L) L.
Proof.
  intros s L. unfold csort. induction L as [|a L IH].
  - induction (seq 0 KN) as [|d l IHl]; [constructor|].
    simpl. try rewrite blk_nil. exact IHl.
  - eapply perm_trans; [apply fm_in|].
    + pose proof (keyN_lt s a). pose proof KN_Z. lia.
    + constructor. exact IH.
Qed.

Lemma csort_length : forall s L, List.length (csort s L) = List.length L.
Proof. intros. apply Permutation_length, csort_perm. Qed.

(* Sortedness on the low s bits. *)
Definition Rm (s : N) (x y : N) : Prop := (x mod 2 ^ s <= y mod 2 ^ s)%N.

Lemma SS_app {A} (R : A -> A -> Prop) : forall l1 l2,
  StronglySorted R l1 -> StronglySorted R l2 ->
  (forall x y, In x l1 -> In y l2 -> R x y) -> StronglySorted R (l1 ++ l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 H1 H2 H12; simpl; [exact H2|].
  inversion H1 as [|? ? Hs Hf]; subst. constructor.
  - apply IH; auto. intros x y Hx Hy. apply H12; simpl; auto.
  - apply Forall_app. split; [assumption|].
    apply Forall_forall. intros y Hy. apply H12; simpl; auto.
Qed.

Lemma SS_filter {A} (R : A -> A -> Prop) (p : A -> bool) : forall l,
  StronglySorted R l -> StronglySorted R (filter p l).
Proof.
  induction l as [|a l IH]; intros H; simpl; [constructor|].
  inversion H as [|? ? Hs Hf]; subst. destruct (p a); [constructor|]; auto.
  apply Forall_forall. intros y Hy. apply filter_In in Hy.
  rewrite Forall_forall in Hf. apply Hf. apply Hy.
Qed.

Lemma SS_weaken {A} (R R' : A -> A -> Prop) : forall l,
  StronglySorted R l -> (forall x y, In x l -> In y l -> R x y -> R' x y) ->
  StronglySorted R' l.
Proof.
  induction l as [|a l IH]; intros H HR; [constructor|].
  inversion H as [|? ? Hs Hf]; subst. constructor.
  - apply IH; auto. intros x y Hx Hy. apply HR; simpl; auto.
  - rewrite Forall_forall in *. intros y Hy. apply HR; simpl; auto.
Qed.

Lemma SS_all {A} (R : A -> A -> Prop) : forall l,
  (forall x y, R x y) -> StronglySorted R l.
Proof.
  induction l as [|a l IH]; intros HR; constructor; auto.
  apply Forall_forall. auto.
Qed.

Lemma SS_flat_map_seq {A} (R : A -> A -> Prop) (f : nat -> list A) : forall k,
  (forall d, StronglySorted R (f d)) ->
  (forall d1 d2 x y, d1 < d2 -> In x (f d1) -> In y (f d2) -> R x y) ->
  StronglySorted R (flat_map f (seq 0 k)).
Proof.
  induction k as [|k IH]; intros Hs Hc; [constructor|].
  rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r.
  apply SS_app; auto.
  intros x y Hx Hy. apply in_flat_map in Hx. destruct Hx as (d & Hd & Hx).
  apply in_seq in Hd. apply (Hc d k); auto. lia.
Qed.

Lemma mod_split : forall s x,
  (x mod 2 ^ (s + 16) = x mod 2 ^ s + 2 ^ s * keyN s x)%N.
Proof.
  intros. unfold keyN. rewrite N.pow_add_r. apply N.Div0.mod_mul_r.
Qed.

Lemma csort_sorted : forall s L,
  StronglySorted (Rm s) L -> StronglySorted (Rm (s + 16)) (csort s L).
Proof.
  intros s L H. unfold csort. apply SS_flat_map_seq.
  - intros d. apply (SS_weaken (Rm s)).
    + unfold blk. apply SS_filter. exact H.
    + intros x y Hx Hy Hxy. apply blk_In in Hx as [_ Hx].
      apply blk_In in Hy as [_ Hy]. unfold Rm in *. rewrite !mod_split. lia.
  - intros d1 d2 x y Hd Hx Hy. apply blk_In in Hx as [_ Hx].
    apply blk_In in Hy as [_ Hy]. unfold Rm. rewrite !mod_split, Hx, Hy.
    assert (HP : (2 ^ s <> 0)%N) by (apply N.pow_nonzero; discriminate).
    pose proof (N.mod_lt x (2 ^ s) HP).
    set (P := (2 ^ s)%N) in *.
    assert (P * N.of_nat d1 + P <= P * N.of_nat d2)%N by nia.
    lia.
Qed.

Lemma start_S : forall s L d, start s L (S d) = start s L d + List.length (blk s L d).
Proof.
  intros. unfold start. rewrite seq_S, flat_map_app, length_app. simpl.
  rewrite app_nil_r. reflexivity.
Qed.

Lemma start_mono : forall s L d1 d2, d1 <= d2 -> start s L d1 <= start s L d2.
Proof.
  intros s L d1 d2 H. induction H as [|d2 H IH]; [lia|].
  rewrite start_S. lia.
Qed.

Lemma start_le : forall s L d, d <= KN -> start s L d <= List.length L.
Proof.
  intros s L d Hd. rewrite <- (csort_length s L). unfold csort, start.
  replace KN with (d + (KN - d)) by lia.
  rewrite seq_app, flat_map_app, length_app. lia.
Qed.

Lemma start_KN : forall s L, start s L KN = List.length L.
Proof. intros. unfold start. fold (csort s L). apply csort_length. Qed.

(* ------------------------------------------------------------------ *)
(* Arrays read as lists of N                                           *)
(* ------------------------------------------------------------------ *)

Definition val (t : array int) (j : int) : N := Z.to_N (φ (t.[j])).

(* Cells a .. a+b-1 of t. *)
Definition contf (t : array int) (a b : nat) : list N :=
  map (fun j => val t (of_nat j)) (seq a b).
(* Cells 0 .. i-1 of t. *)
Definition cont (t : array int) (i : nat) : list N := contf t 0 i.

Lemma cont_S : forall t i, cont t (S i) = cont t i ++ [val t (of_nat i)].
Proof. intros. unfold cont, contf. rewrite seq_S, map_app. reflexivity. Qed.

Lemma cont_add : forall t a b, cont t (a + b) = cont t a ++ contf t a b.
Proof. intros. unfold cont, contf. rewrite seq_app, map_app. reflexivity. Qed.

Lemma contf_length : forall t a b, List.length (contf t a b) = b.
Proof. intros. unfold contf. rewrite length_map, length_seq. reflexivity. Qed.

Lemma cont_length : forall t i, List.length (cont t i) = i.
Proof. intros. apply contf_length. Qed.

Lemma contf_nth : forall t a b j, j < b ->
  nth j (contf t a b) 0%N = val t (of_nat (a + j)).
Proof.
  intros t a b j Hj. unfold contf.
  rewrite (nth_indep _ _ ((fun j => val t (of_nat j)) 0))
    by (rewrite length_map, length_seq; lia).
  change (val t (of_nat 0)) with ((fun j => val t (of_nat j)) 0).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

Lemma cont_nth : forall t i j, j < i -> nth j (cont t i) 0%N = val t (of_nat j).
Proof. intros. unfold cont. rewrite contf_nth by lia. reflexivity. Qed.

Lemma cont_In : forall t i x, In x (cont t i) -> exists j, j < i /\ x = val t (of_nat j).
Proof.
  intros t i x Hx. unfold cont, contf in Hx. apply in_map_iff in Hx.
  destruct Hx as (j & Hj & Hin). apply in_seq in Hin. exists j. split; [lia|auto].
Qed.

Lemma cont_ext : forall t1 t2 i,
  (forall j, j < i -> t1.[of_nat j] = t2.[of_nat j]) -> cont t1 i = cont t2 i.
Proof.
  intros t1 t2 i H. unfold cont, contf. apply map_ext_in. intros j Hj.
  apply in_seq in Hj. unfold val. rewrite H by lia. reflexivity.
Qed.

Lemma of_nat_to : forall i : int, of_nat (Z.to_nat (φ i)) = i.
Proof.
  intros i. rewrite Z2Nat.id by (pose proof (to_Z_bounded i); lia). apply of_to_Z.
Qed.

Lemma phi_of_nat : forall j, (Z.of_nat j < wB)%Z -> (φ (of_nat j)) = Z.of_nat j.
Proof. intros j Hj. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma of_nat_inj : forall j1 j2, (Z.of_nat j1 < wB)%Z -> (Z.of_nat j2 < wB)%Z ->
  j1 <> j2 -> of_nat j1 <> of_nat j2.
Proof.
  intros j1 j2 H1 H2 H E. apply H.
  assert (E' : (φ (of_nat j1)) = (φ (of_nat j2))) by (rewrite E; reflexivity).
  rewrite !phi_of_nat in E' by assumption. lia.
Qed.

Lemma cont_step : forall t (i : int),
  cont t (Z.to_nat (φ (i + 1))%uint63) = cont t (Z.to_nat (φ i)) ++ [val t i]
  \/ ((φ i) + 1 = wB)%Z.
Proof.
  intros t i. pose proof (to_Z_bounded i).
  destruct (Z.eq_dec ((φ i) + 1) wB) as [E|E]; [right; exact E|left].
  replace (Z.to_nat (φ (i + 1))%uint63) with (S (Z.to_nat (φ i))) by sia.
  rewrite cont_S, of_nat_to. reflexivity.
Qed.

Lemma cont_succ : forall t (i : int), ((φ i) < 4194303)%Z ->
  cont t (Z.to_nat (φ (i + 1))%uint63) = cont t (Z.to_nat (φ i)) ++ [val t i].
Proof.
  intros t i Hi. destruct (cont_step t i) as [E|E]; [exact E|].
  rewrite wB_val in E. lia.
Qed.

(* The digit, on the machine. *)
Lemma digit_spec : forall s e : int,
  Z.to_N (φ (digit s e)) = keyN (Z.to_N (φ s)) (Z.to_N (φ e)).
Proof.
  intros s e. unfold digit, keyN. rewrite land_spec', lsr_spec.
  change (φ mask) with (Z.ones 16). rewrite Z.land_ones by lia.
  pose proof (to_Z_bounded e). pose proof (to_Z_bounded s).
  apply N2Z.inj. rewrite N2Z.inj_mod, N2Z.inj_div, N2Z.inj_pow, !Z2N.id by lia.
  reflexivity.
Qed.

Lemma digit_lt : forall s e : int, ((φ (digit s e)) < 65536)%Z.
Proof.
  intros s e. pose proof (digit_spec s e). pose proof (keyN_lt (Z.to_N (φ s)) (Z.to_N (φ e))).
  pose proof (to_Z_bounded (digit s e)). lia.
Qed.

Lemma K_val : (φ K) = 65536%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The counting loop                                                   *)
(* ------------------------------------------------------------------ *)

(* One histogram increment: the table of the counts over L becomes the
   table of the counts over L ++ [e]. *)
Lemma cnt_step : forall (s : N) (L : list N) (e : N) (cnt : array int) (dg : int),
  (Z.of_nat (List.length L) < 4194303)%Z ->
  PArray.length cnt = K -> ((φ dg) < 65536)%Z -> Z.to_N (φ dg) = keyN s e ->
  (forall d, d < KN -> val cnt (of_nat d) = N.of_nat (List.length (blk s L d))) ->
  PArray.length cnt.[dg <- (cnt.[dg] + 1)%uint63] = K /\
  forall d, d < KN -> val cnt.[dg <- (cnt.[dg] + 1)%uint63] (of_nat d)
     = N.of_nat (List.length (blk s (L ++ [e]) d)).
Proof.
  intros s L e cnt dg HL Hlen Hdg Edg Hinv.
  pose proof (to_Z_bounded dg) as Bdg. pose proof KN_Z as HKN.
  split; [rewrite alength_set; exact Hlen|].
  intros d Hd. rewrite blk_app, length_app.
  unfold blk at 2. cbn [filter].
  destruct (Nat.eq_dec d (Z.to_nat (φ dg))) as [E|E].
  - subst d. rewrite of_nat_to in *.
    unfold val at 1. rewrite aget_set_same by (rewrite Hlen, ltb_spec, K_val; lia).
    replace (N.eqb _ _) with true.
    2:{ symmetry. apply N.eqb_eq. rewrite <- Edg. lia. }
    specialize (Hinv (Z.to_nat (φ dg)) Hd). rewrite of_nat_to in Hinv.
    unfold val in Hinv.
    pose proof (blk_length s L (Z.to_nat (φ dg))) as Hbl.
    pose proof (to_Z_bounded cnt.[dg]).
    cbn [List.length]. rewrite add_spec. change (φ 1) with 1%Z.
    rewrite Z.mod_small by (rewrite wB_val; lia). lia.
  - unfold val at 1. rewrite aget_set_other.
    2:{ intro F. apply E. rewrite <- (of_nat_to dg) in F.
        destruct (Nat.eq_dec d (Z.to_nat (φ dg))) as [E'|E']; [exact E'|].
        exfalso. revert F. apply of_nat_inj; rewrite ?wB_val; lia. }
    replace (N.eqb _ _) with false.
    2:{ symmetry. apply N.eqb_neq. rewrite <- Edg. lia. }
    pose proof (Hinv d Hd) as Hd'. unfold val in Hd'. rewrite Hd'.
    cbn [List.length]. lia.
Qed.

Lemma blk_perm_length : forall s L L' d, Permutation L L' ->
  List.length (blk s L d) = List.length (blk s L' d).
Proof.
  intros s L L' d HP. induction HP as [|a l l' _ IH|a b' l|l l' l'' _ IH1 _ IH2].
  - reflexivity.
  - rewrite !blk_cons. destruct (N.eqb _ _); simpl; lia.
  - rewrite !blk_cons. destruct (N.eqb (keyN s a) _), (N.eqb (keyN s b') _); simpl; lia.
  - lia.
Qed.

Lemma idx_neq : forall (i : int) d, (Z.of_nat d < wB)%Z ->
  d <> Z.to_nat (φ i) -> i <> of_nat d.
Proof.
  intros i d Hd E F. rewrite <- (of_nat_to i) in F. revert F.
  apply of_nat_inj; [pose proof (to_Z_bounded i); lia | exact Hd | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The prefix-sum loop                                                 *)
(* ------------------------------------------------------------------ *)

Lemma prefix_loop_spec : forall (s : N) (L : list N),
  (Z.of_nat (List.length L) <= 4194303)%Z ->
  forall (z : Z) (e acc : int) (cnt : array int) (H : Acc (Zwf 0) (gap K e)),
  gap K e = z -> ((φ e) <= 65536)%Z ->
  PArray.length cnt = K ->
  (φ acc) = Z.of_nat (start s L (Z.to_nat (φ e))) ->
  (forall d, d < Z.to_nat (φ e) -> val cnt (of_nat d) = N.of_nat (start s L d)) ->
  (forall d, Z.to_nat (φ e) <= d < KN ->
     val cnt (of_nat d) = N.of_nat (List.length (blk s L d))) ->
  PArray.length (prefix_loop e acc cnt H) = K /\
  forall d, d < KN -> val (prefix_loop e acc cnt H) (of_nat d) = N.of_nat (start s L d).
Proof.
  intros s L HL z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros e acc cnt H Hz He Hlen Hacc Hlo Hhi.
  pose proof KN_Z as HKN.
  rewrite prefix_loop_eq.
  destruct (bdec (e <? K)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec, K_val in Hi'.
    assert (Hi1 : (φ (e + 1))%uint63 = ((φ e) + 1)%Z) by sia.
    assert (Ee : Z.to_nat (φ (e + 1))%uint63 = S (Z.to_nat (φ e))) by lia.
    pose proof (Hhi (Z.to_nat (φ e)) ltac:(lia)) as Hce.
    rewrite of_nat_to in Hce. unfold val in Hce.
    pose proof (start_le s L (S (Z.to_nat (φ e))) ltac:(lia)) as Hs.
    rewrite start_S in Hs.
    eapply IH; [ | reflexivity | lia | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite alength_set. exact Hlen.
    + rewrite Ee, start_S, add_spec. pose proof (to_Z_bounded cnt.[e]).
      rewrite Z.mod_small; [lia|]. rewrite wB_val. lia.
    + intros d Hd. rewrite Ee in Hd. unfold val.
      destruct (Nat.eq_dec d (Z.to_nat (φ e))) as [E|E].
      * subst d. rewrite of_nat_to, aget_set_same by (rewrite Hlen, ltb_spec, K_val; lia).
        lia.
      * rewrite aget_set_other by (apply idx_neq; [rewrite wB_val; lia | exact E]).
        pose proof (Hlo d ltac:(lia)) as X. unfold val in X. exact X.
    + intros d Hd. rewrite Ee in Hd. unfold val.
      rewrite aget_set_other by (apply idx_neq; [rewrite wB_val; lia | lia]).
      pose proof (Hhi d ltac:(lia)) as X. unfold val in X. exact X.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, K_val in Hi.
    split; [exact Hlen|]. intros d Hd. apply Hlo. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The placement loop                                                  *)
(* ------------------------------------------------------------------ *)

Lemma of_nat_neq_small : forall j1 j2 m, j1 < m -> j2 < m ->
  (Z.of_nat m <= 4194303)%Z -> j1 <> j2 -> of_nat j1 <> of_nat j2.
Proof. intros. apply of_nat_inj; rewrite ?wB_val; lia. Qed.

Lemma nth_middle : forall (l r : list N) (e : N),
  nth (List.length l) ((l ++ [e]) ++ r) 0%N = e.
Proof.
  intros. rewrite <- app_assoc, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma place_loop_spec : forall (s n : int) (src : array int) (sN : N) (L : list N),
  ((φ n) <= 4194303)%Z ->
  sN = Z.to_N (φ s) -> L = cont src (Z.to_nat (φ n)) ->
  forall (z : Z) (i : int) (cnt dst : array int) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> ((φ i) <= (φ n))%Z ->
  PArray.length cnt = K -> PArray.length dst = n ->
  (forall d, d < KN -> val cnt (of_nat d)
     = N.of_nat (start sN L d + List.length (blk sN (cont src (Z.to_nat (φ i))) d))) ->
  (forall d j, d < KN -> j < List.length (blk sN (cont src (Z.to_nat (φ i))) d) ->
     val dst (of_nat (start sN L d + j)) = nth j (blk sN L d) 0%N) ->
  PArray.length (place_loop s n src i cnt dst H) = n /\
  forall d j, d < KN -> j < List.length (blk sN L d) ->
     val (place_loop s n src i cnt dst H) (of_nat (start sN L d + j))
     = nth j (blk sN L d) 0%N.
Proof.
  intros s n src sN L Hn HsN HL z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i cnt dst H Hz Hin Hlc Hld Hinv Hdst.
  pose proof KN_Z as HKN.
  rewrite place_loop_eq.
  destruct (bdec (i <? n)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1))%uint63 = ((φ i) + 1)%Z) by sia.
    set (i' := Z.to_nat (φ i)) in *.
    set (nn := Z.to_nat (φ n)) in *.
    set (e := val src i).
    set (dg := digit s src.[i]).
    pose proof (digit_lt s src.[i]) as Hdg. fold dg in Hdg.
    pose proof (digit_spec s src.[i]) as Edg. fold dg in Edg.
    pose proof (to_Z_bounded dg) as Bdg.
    set (dn := Z.to_nat (φ dg)).
    assert (Hdn : dn < KN) by lia.
    assert (Hkey : keyN sN e = N.of_nat dn) by (subst sN; unfold e, val, dn; rewrite <- Edg; lia).
    assert (Hc : blk sN (cont src i' ++ [e]) dn = blk sN (cont src i') dn ++ [e]).
    { rewrite blk_app. unfold blk at 2. cbn [filter].
      rewrite Hkey, N.eqb_refl. reflexivity. }
    assert (HcO : forall d, d <> dn -> blk sN (cont src i' ++ [e]) d = blk sN (cont src i') d).
    { intros d Hd. rewrite blk_app. unfold blk at 2. cbn [filter].
      replace (N.eqb (keyN sN e) (N.of_nat d)) with false by
        (symmetry; apply N.eqb_neq; rewrite Hkey; lia).
      apply app_nil_r. }
    assert (HS : cont src (S i') = cont src i' ++ [e]).
    { rewrite cont_S. unfold i'. rewrite of_nat_to. reflexivity. }
    assert (HLd : forall d, blk sN L d
                  = blk sN (cont src i' ++ [e]) d ++ blk sN (contf src (S i') (nn - S i')) d).
    { intros d. rewrite <- HS, <- blk_app, <- cont_add. subst L. f_equal. f_equal. lia. }
    assert (HLl : forall d, List.length (blk sN (cont src i') d)
                   <= List.length (blk sN (cont src i' ++ [e]) d)
                   <= List.length (blk sN L d)).
    { intros d. rewrite HLd, !length_app, blk_app, length_app. lia. }
    assert (HnL : List.length L = nn) by (subst L; apply cont_length).
    assert (Hsl : forall d, d < KN -> start sN L d + List.length (blk sN L d) <= nn).
    { intros d Hd. rewrite <- start_S, <- HnL. apply start_le. lia. }
    set (ci := fun d => List.length (blk sN (cont src i') d)).
    assert (Hcdn : ci dn + 1 <= List.length (blk sN L dn)).
    { pose proof (HLl dn) as X. rewrite Hc, length_app in X. cbn [List.length] in X.
      unfold ci. lia. }
    pose proof (Hsl dn Hdn) as Hsdn.
    assert (Hnn : (Z.of_nat nn <= 4194303)%Z) by (unfold nn; lia).
    assert (Hpnn : start sN L dn + ci dn < nn) by (clear - Hcdn Hsdn; lia).
    pose proof (Hinv dn Hdn) as Hp. unfold dn in Hp at 1. rewrite of_nat_to in Hp.
    fold dn in Hp. unfold val in Hp.
    set (p := cnt.[dg]) in *.
    assert (Hpz : (φ p) = Z.of_nat (start sN L dn + ci dn)).
    { pose proof (to_Z_bounded p). unfold ci. lia. }
    assert (Hpn : p = of_nat (start sN L dn + ci dn)).
    { apply to_Z_inj. rewrite Hpz, phi_of_nat; [reflexivity|]. rewrite wB_val. lia. }
    eapply IH; [ | reflexivity | lia | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite alength_set. exact Hlc.
    + rewrite alength_set. exact Hld.
    + intros d Hd. rewrite cont_succ by lia. fold i' e.
      unfold val.
      destruct (Nat.eq_dec d dn) as [E|E].
      * subst d. unfold dn at 1. rewrite of_nat_to.
        rewrite aget_set_same by (rewrite Hlc, ltb_spec, K_val; lia).
        rewrite Hc, length_app. cbn [List.length].
        rewrite add_spec. change (φ 1) with 1%Z.
        rewrite Z.mod_small by (rewrite wB_val; lia). rewrite Hpz. unfold ci. lia.
      * rewrite aget_set_other by (apply idx_neq; [rewrite wB_val; lia | exact E]).
        rewrite HcO by exact E.
        pose proof (Hinv d Hd) as X. unfold val in X. exact X.
    + intros d j Hd Hj. rewrite cont_succ in Hj by lia. fold i' e in Hj.
      unfold val.
      destruct (Nat.eq_dec d dn) as [E|E];
        [destruct (Nat.eq_dec j (ci dn)) as [Ej|Ej] |].
      * subst d j. rewrite <- Hpn.
        rewrite aget_set_same by (rewrite Hld, ltb_spec, Hpz; unfold nn in Hpnn; clear - Hpnn; lia).
        rewrite HLd, Hc. unfold ci. rewrite nth_middle. reflexivity.
      * subst d. rewrite Hc, length_app in Hj. cbn [List.length] in Hj.
        assert (Hj' : j < ci dn) by (clear - Hj Ej; unfold ci in *; lia).
        rewrite aget_set_other.
        2:{ rewrite Hpn. apply (of_nat_neq_small _ _ nn); [exact Hpnn | | exact Hnn | ].
            - clear - Hj' Hcdn Hsdn. lia.
            - clear - Ej. lia. }
        pose proof (Hdst dn j Hdn Hj') as X. unfold val in X. exact X.
      * rewrite HcO in Hj by exact E.
        pose proof (HLl d) as Hld'. pose proof (Hsl d Hd) as Hsd.
        assert (Hne : start sN L d + j <> start sN L dn + ci dn).
        { destruct (Nat.lt_ge_cases d dn) as [Lt|Ge].
          - pose proof (start_mono sN L (S d) dn ltac:(lia)) as M.
            rewrite start_S in M. clear - M Hj Hld'. unfold ci. lia.
          - pose proof (start_mono sN L (S dn) d ltac:(lia)) as M.
            rewrite start_S in M. clear - M Hcdn. unfold ci in *. lia. }
        assert (Hq : start sN L d + j < nn).
        { unfold ci in *. clear - Hj Hld' Hsd. lia. }
        rewrite aget_set_other.
        2:{ rewrite Hpn. apply (of_nat_neq_small _ _ nn); [exact Hpnn | exact Hq | exact Hnn | ].
            apply not_eq_sym. exact Hne. }
        pose proof (Hdst d j Hd Hj) as X. unfold val in X. exact X.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    assert (Ei : Z.to_nat (φ i) = Z.to_nat (φ n)) by lia.
    rewrite Ei in Hinv, Hdst. rewrite <- HL in Hdst.
    split; [exact Hld | exact Hdst].
Qed.

(* ------------------------------------------------------------------ *)
(* One pass                                                            *)
(* ------------------------------------------------------------------ *)

Lemma contf_blk : forall t s L d,
  (forall j, j < List.length (blk s L d) ->
     val t (of_nat (start s L d + j)) = nth j (blk s L d) 0%N) ->
  contf t (start s L d) (List.length (blk s L d)) = blk s L d.
Proof.
  intros t s L d H. apply nth_ext with (d := 0%N) (d' := 0%N).
  - apply contf_length.
  - intros j Hj. rewrite contf_length in Hj. rewrite contf_nth by exact Hj. auto.
Qed.

Lemma cont_start : forall t s L,
  (forall d j, d < KN -> j < List.length (blk s L d) ->
     val t (of_nat (start s L d + j)) = nth j (blk s L d) 0%N) ->
  forall k, k <= KN -> cont t (start s L k) = flat_map (blk s L) (seq 0 k).
Proof.
  intros t s L Hd k. induction k as [|k IH]; intros Hk; [reflexivity|].
  rewrite start_S, cont_add, IH by lia.
  rewrite contf_blk by (intros; apply Hd; [lia | assumption]).
  rewrite seq_S, flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma pass_spec : forall (s n : int) (src cnt dst : array int),
  ((φ n) <= 4194303)%Z -> PArray.length dst = n -> PArray.length cnt = K ->
  (forall d, d < KN -> val cnt (of_nat d)
     = N.of_nat (List.length (blk (Z.to_N (φ s)) (cont src (Z.to_nat (φ n))) d))) ->
  PArray.length (pass s n src cnt dst) = n /\
  cont (pass s n src cnt dst) (Z.to_nat (φ n))
  = csort (Z.to_N (φ s)) (cont src (Z.to_nat (φ n))).
Proof.
  intros s n src cnt1 dst Hn Hd Hc1 Hc2.
  pose proof KN_Z as HKN. pose proof (to_Z_bounded n) as Bn.
  set (L := cont src (Z.to_nat (φ n))) in *.
  set (sN := Z.to_N (φ s)) in *.
  assert (HLl : List.length L = Z.to_nat (φ n)) by apply cont_length.
  unfold pass.
  destruct (prefix_loop_spec sN L ltac:(lia) _ 0 0 cnt1
              (Zwf_well_founded 0 (gap K 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) Hc1 eq_refl
              ltac:(intros d Hd'; change (Z.to_nat (φ 0)) with 0 in Hd'; lia)
              ltac:(intros d Hd'; apply Hc2; lia)) as [Hp1 Hp2].
  set (cnt2 := prefix_loop 0 0 cnt1 (Zwf_well_founded 0 (gap K 0))) in *.
  assert (Hinv : forall d, d < KN -> val cnt2 (of_nat d)
     = N.of_nat (start sN L d + List.length (blk sN (cont src (Z.to_nat (φ 0))) d))).
  { intros d Hd'. rewrite Hp2 by exact Hd'.
    change (blk sN (cont src (Z.to_nat (φ 0))) d) with (@nil N).
    cbn [List.length]. rewrite Nat.add_0_r. reflexivity. }
  destruct (place_loop_spec s n src sN L Hn eq_refl eq_refl _ 0 cnt2 dst
              (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) Hp1 Hd Hinv
              ltac:(intros d j Hd' Hj; change (blk sN (cont src (Z.to_nat (φ 0))) d)
                      with (@nil N) in Hj; cbn [List.length] in Hj; lia)) as [Hl Hv].
  split; [exact Hl|].
  rewrite <- HLl, <- (start_KN sN L). apply cont_start; [exact Hv | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Generation and hash                                                 *)
(* ------------------------------------------------------------------ *)

Lemma term_le : forall a b c i, (a <= 1000000000)%N -> (1 <= c <= 1000000000)%N ->
  (term a b c i <= 1000000000)%N.
Proof.
  intros a b c i Ha Hc. destruct i as [|i]; simpl; [lia|].
  pose proof (N.mod_lt (term a b c i * b + a) c ltac:(lia)). lia.
Qed.

(* The terms S[0] .. S[i-1], as a list. *)
Definition terms (aN bN cN : N) (i : nat) : list N := map (term aN bN cN) (seq 0 i).

Lemma terms_S : forall aN bN cN i, terms aN bN cN (S i) = terms aN bN cN i ++ [term aN bN cN i].
Proof. intros. unfold terms. rewrite seq_S, map_app. reflexivity. Qed.

Lemma terms_length : forall aN bN cN i, List.length (terms aN bN cN i) = i.
Proof. intros. unfold terms. rewrite length_map, length_seq. reflexivity. Qed.

Lemma gen_loop_spec : forall (a b c n : int) (aN bN cN : N),
  Z.to_N (φ a) = aN -> Z.to_N (φ b) = bN -> Z.to_N (φ c) = cN ->
  (1 <= aN <= 1000000000)%N -> (1 <= bN <= 1000000000)%N ->
  (1 <= cN <= 1000000000)%N -> ((φ n) <= 4194303)%Z ->
  forall (z : Z) (i t m : int) (arr lo hi : array int) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> ((φ i) <= (φ n))%Z -> PArray.length arr = n ->
  PArray.length lo = K -> PArray.length hi = K ->
  Z.to_N (φ t) = term aN bN cN (Z.to_nat (φ i)) ->
  (forall j, j < Z.to_nat (φ i) -> val arr (of_nat j) = term aN bN cN j /\
     (term aN bN cN j <= Z.to_N (φ m))%N) ->
  (forall d, d < KN -> val lo (of_nat d)
     = N.of_nat (List.length (blk 0 (terms aN bN cN (Z.to_nat (φ i))) d))) ->
  (forall d, d < KN -> val hi (of_nat d)
     = N.of_nat (List.length (blk 16 (terms aN bN cN (Z.to_nat (φ i))) d))) ->
  match gen_loop a b c n i t m arr lo hi H with (g, m', lo', hi') =>
  PArray.length g = n /\
  (forall j, j < Z.to_nat (φ n) ->
    val g (of_nat j) = term aN bN cN j /\ (term aN bN cN j <= Z.to_N (φ m'))%N) /\
  PArray.length lo' = K /\
  (forall d, d < KN -> val lo' (of_nat d)
     = N.of_nat (List.length (blk 0 (terms aN bN cN (Z.to_nat (φ n))) d))) /\
  PArray.length hi' = K /\
  (forall d, d < KN -> val hi' (of_nat d)
     = N.of_nat (List.length (blk 16 (terms aN bN cN (Z.to_nat (φ n))) d)))
  end.
Proof.
  intros a b c n aN bN cN Ha Hb Hc Va Vb Vc Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i t m arr lo hi H Hz Hin Hlen Hllo Hlhi Ht Hinv Hlo Hhi.
  rewrite gen_loop_eq.
  destruct (bdec (i <? n)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1))%uint63 = ((φ i) + 1)%Z) by sia.
    assert (Ei : Z.to_nat (φ (i + 1))%uint63 = S (Z.to_nat (φ i))) by lia.
    pose proof (term_le aN bN cN (Z.to_nat (φ i)) ltac:(lia) Vc) as Tb.
    pose proof (to_Z_bounded t). pose proof (to_Z_bounded a).
    pose proof (to_Z_bounded b). pose proof (to_Z_bounded c).
    pose proof (to_Z_bounded m).
    assert (HtL : (Z.of_nat (List.length (terms aN bN cN (Z.to_nat (φ i)))) < 4194303)%Z)
      by (rewrite terms_length; lia).
    destruct (cnt_step 0 _ (term aN bN cN (Z.to_nat (φ i))) lo (digit 0 t) HtL Hllo
                (digit_lt 0 t) ltac:(rewrite digit_spec, Ht; reflexivity) Hlo)
      as [Hllo' Hlo'].
    destruct (cnt_step 16 _ (term aN bN cN (Z.to_nat (φ i))) hi (digit 16 t) HtL Hlhi
                (digit_lt 16 t) ltac:(rewrite digit_spec, Ht; reflexivity) Hhi)
      as [Hlhi' Hhi'].
    rewrite <- terms_S, <- Ei in Hlo', Hhi'.
    eapply IH; [ | reflexivity | lia | | exact Hllo' | exact Hlhi' | | | exact Hlo'
               | exact Hhi' ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite alength_set. exact Hlen.
    + rewrite Ei. simpl term. rewrite <- Ht, <- Ha, <- Hb, <- Hc.
      assert (Hm : (φ ((t * b + a) mod c))%uint63 = (((φ t) * (φ b) + (φ a)) mod (φ c))%Z).
      { rewrite mod_spec, add_spec, mul_spec.
        rewrite (Z.mod_small ((φ t) * (φ b))) by (rewrite wB_val; nia).
        rewrite (Z.mod_small ((φ t) * (φ b) + (φ a))) by (rewrite wB_val; nia).
        reflexivity. }
      rewrite Hm. apply N2Z.inj.
      rewrite N2Z.inj_mod, N2Z.inj_add, N2Z.inj_mul, !Z2N.id; try lia.
    + intros j Hj. rewrite Ei in Hj.
      assert (Hmm : (Z.to_N (φ m) <= Z.to_N (φ (if (m <? t)%uint63 then t else m)))%N
                    /\ (Z.to_N (φ t) <= Z.to_N (φ (if (m <? t)%uint63 then t else m)))%N).
      { destruct (m <? t)%uint63 eqn:E;
          [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E];
          lia. }
      unfold val.
      destruct (Nat.eq_dec j (Z.to_nat (φ i))) as [E|E].
      * subst j. rewrite of_nat_to, aget_set_same by (rewrite Hlen, ltb_spec; lia).
        split; [exact Ht | lia].
      * rewrite aget_set_other by (apply idx_neq; [rewrite wB_val; lia | exact E]).
        destruct (Hinv j ltac:(lia)) as [X1 X2]. split; [exact X1 | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    assert (Ei : Z.to_nat (φ i) = Z.to_nat (φ n)) by lia.
    rewrite Ei in Hinv, Hlo, Hhi. cbv iota.
    exact (conj Hlen (conj Hinv (conj Hllo (conj Hlo (conj Hlhi Hhi))))).
Qed.

Lemma hash_step : forall x y l e, hash x y (l ++ [e]) = ((hash x y l * x + e) mod y)%N.
Proof. intros. unfold hash. rewrite fold_left_app. reflexivity. Qed.

Lemma hash_loop_spec : forall (x y n : int) (r : array int),
  (1 <= (φ x) <= 1000000000)%Z -> (1 <= (φ y) <= 1000000000)%Z -> ((φ n) <= 4194303)%Z ->
  (forall j, j < Z.to_nat (φ n) -> (val r (of_nat j) <= 1000000000)%N) ->
  forall (z : Z) (i v : int) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> ((φ i) <= (φ n))%Z -> ((φ v) < (φ y))%Z ->
  Z.to_N (φ v) = hash (Z.to_N (φ x)) (Z.to_N (φ y)) (cont r (Z.to_nat (φ i))) ->
  Z.to_N (φ (hash_loop x y n i v r H))
  = hash (Z.to_N (φ x)) (Z.to_N (φ y)) (cont r (Z.to_nat (φ n))).
Proof.
  intros x y n r Hx Hy Hn Hr z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i v H Hz Hin Hvy Hv.
  rewrite hash_loop_eq.
  destruct (bdec (i <? n)%uint63) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1))%uint63 = ((φ i) + 1)%Z) by sia.
    pose proof (Hr (Z.to_nat (φ i)) ltac:(lia)) as Hri. rewrite of_nat_to in Hri.
    unfold val in Hri.
    pose proof (to_Z_bounded v). pose proof (to_Z_bounded r.[i]).
    assert (Hm : (φ ((v * x + r.[i]) mod y))%uint63 = (((φ v) * (φ x) + (φ (r.[i]))) mod (φ y))%Z).
    { rewrite mod_spec, add_spec, mul_spec.
      rewrite (Z.mod_small ((φ v) * (φ x))) by (rewrite wB_val; nia).
      rewrite (Z.mod_small ((φ v) * (φ x) + (φ (r.[i])))) by (rewrite wB_val; nia).
      reflexivity. }
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite Hm. apply Z.mod_pos_bound. lia.
    + rewrite cont_succ by lia. rewrite hash_step, <- Hv, Hm. unfold val.
      apply N2Z.inj.
      rewrite N2Z.inj_mod, N2Z.inj_add, N2Z.inj_mul, !Z2N.id; try lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    assert (Ei : Z.to_nat (φ i) = Z.to_nat (φ n)) by lia.
    rewrite <- Ei. exact Hv.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma alength_make_small : forall k : int, ((φ k) <= 4194303)%Z ->
  PArray.length (PArray.make k 0%uint63) = k.
Proof.
  intros k Hk. rewrite alength_make.
  replace (k <=? PArray.max_length)%uint63 with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact Hk.
Qed.

Lemma magic_impl_correct : forall (n a b c x y : N) (n' a' b' c' x' y' : int),
  valid_input n a b c x y ->
  Z.to_N (φ n') = n -> Z.to_N (φ a') = a -> Z.to_N (φ b') = b -> Z.to_N (φ c') = c ->
  Z.to_N (φ x') = x -> Z.to_N (φ y') = y ->
  exists v : N, Z.to_N (φ (magic_impl n' a' b' c' x' y')) = v /\ magic_spec n a b c x y v.
Proof.
  intros n a b c x y n' a' b' c' x' y' Hv Hn Ha Hb Hc Hx Hy.
  destruct Hv as [Vn Va Vb Vc Vx Vy].
  change (10 ^ 6)%N with 1000000%N in Vn.
  change (10 ^ 9)%N with 1000000000%N in Va, Vb, Vc, Vx, Vy.
  pose proof (to_Z_bounded n'). pose proof (to_Z_bounded x').
  pose proof (to_Z_bounded y').
  assert (Bn : (1 <= (φ n') <= 1000000)%Z) by lia.
  assert (Bx : (1 <= (φ x') <= 1000000000)%Z) by lia.
  assert (By : (1 <= (φ y') <= 1000000000)%Z) by lia.
  set (nn := Z.to_nat (φ n')).
  assert (Hnn : N.to_nat n = nn) by (unfold nn; lia).
  assert (HmK : PArray.length (PArray.make K 0%uint63) = K)
    by (rewrite alength_make; reflexivity).
  assert (Hm0 : forall s, forall d, d < KN -> val (PArray.make K 0%uint63) (of_nat d)
     = N.of_nat (List.length (blk s (terms a b c (Z.to_nat (φ 0))) d))).
  { intros s d _. unfold val. rewrite aget_make. reflexivity. }
  unfold magic_impl.
  (* generation *)
  pose proof (gen_loop_spec a' b' c' n' a b c Ha Hb Hc Va Vb Vc ltac:(lia)
              _ 0 a' 0 (PArray.make n' 0%uint63) (PArray.make K 0%uint63)
              (PArray.make K 0%uint63) (Zwf_well_founded 0 (gap n' 0))
              eq_refl ltac:(change (φ 0) with 0%Z; lia)
              (alength_make_small n' ltac:(lia)) HmK HmK Ha
              ltac:(intros j Hj; change (Z.to_nat (φ 0)) with 0 in Hj; lia)
              (Hm0 0%N) (Hm0 16%N)) as G.
  destruct (gen_loop a' b' c' n' 0 a' 0 (PArray.make n' 0%uint63) (PArray.make K 0%uint63)
              (PArray.make K 0%uint63) (Zwf_well_founded 0 (gap n' 0)))
    as [[[g m] lo] hi].
  destruct G as (Hgl & Hgv & Hlol & Hlov & Hhil & Hhiv).
  cbv zeta.
  set (L0 := cont g nn).
  assert (HL0 : L0 = sequence n a b c).
  { unfold L0, sequence, cont, contf. rewrite Hnn. apply map_ext_in.
    intros j Hj. apply in_seq in Hj. apply Hgv. fold nn. lia. }
  assert (HT0 : terms a b c (Z.to_nat (φ n')) = L0).
  { rewrite HL0. unfold terms, sequence. fold nn. rewrite Hnn. reflexivity. }
  rewrite HT0 in Hlov, Hhiv.
  assert (HB0 : forall v, In v L0 -> (v <= Z.to_N (φ m))%N /\ (v <= 1000000000)%N).
  { intros v Hv. apply cont_In in Hv. destruct Hv as (j & Hj & ->).
    destruct (Hgv j Hj) as [X1 X2]. rewrite X1. split; [exact X2|].
    apply term_le; lia. }
  (* the final hash, for any sorted permutation of L0 *)
  assert (Final : forall r : array int, PArray.length r = n' ->
            Permutation (cont r nn) L0 -> Sorted N.le (cont r nn) ->
            exists v, Z.to_N (φ (hash_loop x' y' n' 0 0 r (Zwf_well_founded 0 (gap n' 0)))) = v
                      /\ magic_spec n a b c x y v).
  { intros r Hrl Hperm Hsort.
    assert (Hr : forall j, j < nn -> (val r (of_nat j) <= 1000000000)%N).
    { intros j Hj. rewrite <- (cont_nth r nn j Hj).
      apply HB0. apply (Permutation_in _ Hperm). apply nth_In.
      rewrite cont_length. exact Hj. }
    exists (hash x y (cont r nn)). split.
    - rewrite <- Hx, <- Hy.
      apply (hash_loop_spec x' y' n' r Bx By ltac:(lia) Hr _ 0 0 _ eq_refl);
        [change (φ 0) with 0%Z; lia | change (φ 0) with 0%Z; lia | reflexivity].
    - exists (cont r nn). split; [|reflexivity]. split; [|exact Hsort].
      rewrite <- HL0. exact Hperm. }
  (* first pass *)
  destruct (pass_spec 0 n' g lo (PArray.make n' 0%uint63) ltac:(lia)
              (alength_make_small n' ltac:(lia)) Hlol Hlov) as [Hr1l Hr1c].
  set (r1 := pass 0 n' g lo (PArray.make n' 0%uint63)) in *.
  change (Z.to_N (φ 0)) with 0%N in Hr1c. fold nn L0 in Hr1c.
  assert (P1 : Permutation (cont r1 nn) L0) by (rewrite Hr1c; apply csort_perm).
  assert (S1 : StronglySorted (Rm 16) (cont r1 nn)).
  { rewrite Hr1c. apply (csort_sorted 0%N L0). apply SS_all.
    intros x0 y0. unfold Rm. rewrite N.pow_0_r, !N.mod_1_r. lia. }
  destruct (m <? K)%uint63 eqn:Em.
  - apply Final; [exact Hr1l | exact P1 |].
    rewrite ltb_spec, K_val in Em.
    apply StronglySorted_Sorted. apply (SS_weaken (Rm 16)); [exact S1|].
    intros x0 y0 Hx0 Hy0 Hxy. unfold Rm in Hxy.
    pose proof (HB0 x0 (Permutation_in _ P1 Hx0)).
    pose proof (HB0 y0 (Permutation_in _ P1 Hy0)).
    change (2 ^ 16)%N with 65536%N in Hxy.
    rewrite !N.mod_small in Hxy by lia. exact Hxy.
  - assert (Hhiv' : forall d, d < KN -> val hi (of_nat d)
       = N.of_nat (List.length (blk (Z.to_N (φ 16)) (cont r1 (Z.to_nat (φ n'))) d))).
    { intros d Hd. rewrite Hhiv by exact Hd. change (Z.to_N (φ 16)) with 16%N. f_equal. fold nn.
      apply blk_perm_length. apply Permutation_sym. exact P1. }
    destruct (pass_spec 16 n' r1 hi g ltac:(lia) Hgl Hhil Hhiv') as [Hr2l Hr2c].
    set (r2 := pass 16 n' r1 hi g) in *.
    change (Z.to_N (φ 16)) with 16%N in Hr2c. fold nn in Hr2c.
    assert (P2 : Permutation (cont r2 nn) L0).
    { rewrite Hr2c. eapply perm_trans; [apply csort_perm | exact P1]. }
    apply Final; [exact Hr2l | exact P2 |].
    assert (S2 : StronglySorted (Rm (16 + 16)) (cont r2 nn))
      by (rewrite Hr2c; apply csort_sorted; exact S1).
    apply StronglySorted_Sorted. apply (SS_weaken (Rm (16 + 16))); [exact S2|].
    intros x0 y0 Hx0 Hy0 Hxy. unfold Rm in Hxy.
    pose proof (HB0 x0 (Permutation_in _ P2 Hx0)).
    pose proof (HB0 y0 (Permutation_in _ P2 Hy0)).
    change (2 ^ (16 + 16))%N with 4294967296%N in Hxy.
    rewrite !N.mod_small in Hxy by lia. exact Hxy.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition magic : uint -> uint -> uint -> uint -> uint -> uint -> uint :=
  magic_impl.

Definition magic_correct :
  forall (n a b c x y : N) (n' a' b' c' x' y' : uint),
  valid_input n a b c x y ->
  repr n' n -> repr a' a -> repr b' b -> repr c' c -> repr x' x -> repr y' y ->
  exists v : N, repr (magic n' a' b' c' x' y') v /\ magic_spec n a b c x y v
  := magic_impl_correct.
