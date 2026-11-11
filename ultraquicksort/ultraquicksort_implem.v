(* Implementation of ultraquicksort (ultraquicksort.spec): the number of
   inversions of an array of distinct values, counted by a top-down merge
   sort.

   Code.  [inversions a] makes the two working arrays of the run: w, the
   one copy of the input ([PArray.copy a]), and s, a scratch array
   ([PArray.make n 0]); the caller's array is only read by that copy.
   [msort b lo hi w s c] sorts the segment [lo, hi) of w and leaves the
   sorted segment in w when b = true, in s when b = false (ping-pong: the
   two halves are sorted into the other array, then merged back, so no
   copy-back pass).  [merge src dst mid hi i j k c] merges the sorted runs
   src[i, mid) and src[j, hi) into dst from position k; when the head of the
   right run is strictly smaller it is taken and the mid - i elements left
   in the left run are added to the counter (ties go left).  The counter is
   a 63-bit int; the arrays are threaded linearly (every [set] on the latest
   version).

   Termination: both functions recurse structurally on an erased
   [Acc (Zwf 0) _] proof: the wrapped difference [φ (hi - lo)] for msort,
   [max 0 (mid - i) + max 0 (hi - j)] for merge.

   Proof.  On the math side, [seg t i n] reads n cells of t from i as a list
   of N; [mergec] is the list merge with its count, proven to return a
   sorted permutation of its arguments and, on sorted arguments, the number
   of cross inversions [cross l r].  [merge] simulates [mergec] step by
   step (merge_spec); [msort] returns a sorted permutation of its segment
   and adds its [inv_list] (msort_spec), by
   [inv_list (l1 ++ l2) = inv_list l1 + inv_list l2 + cross l1 l2] and the
   invariance of [cross] under permutation of either argument.  The count
   is exact because it is below n^2 < 2^63. *)

From Ultraquicksort.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorted Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

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
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_copy : forall (t : array int),
  PArray.length (PArray.copy t) = PArray.length t.
Proof. intros t. exact (length_copy int t). Qed.

Lemma aget_copy : forall (t : array int) (i : int), (PArray.copy t).[i] = t.[i].
Proof. intros t i. exact (get_copy int t i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The termination device                                              *)
(* ------------------------------------------------------------------ *)

Definition bdec (b : bool) : {b = true} + {b = false} :=
  match b as b0 return {b0 = true} + {b0 = false} with
  | true => left eq_refl
  | false => right eq_refl
  end.

(* the merge measure: what is left of the two runs *)
Definition mm (mid hi i j : int) : Z :=
  (Z.max 0 ((φ mid) - (φ i)) + Z.max 0 ((φ hi) - (φ j)))%Z.

Lemma mm_dec_i : forall mid hi i j,
  (i <? mid) = true -> Zwf 0 (mm mid hi (i + 1) j) (mm mid hi i j).
Proof.
  intros mid hi i j H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, mm. lia.
Qed.

Lemma mm_dec_j : forall mid hi i j,
  (j <? hi) = true -> Zwf 0 (mm mid hi i (j + 1)) (mm mid hi i j).
Proof.
  intros mid hi i j H. rewrite ltb_spec in H.
  assert (H1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
  unfold Zwf, mm. lia.
Qed.

Lemma dec_left : forall lo hi,
  (1 <? hi - lo) = true -> Zwf 0 (φ (lo + (hi - lo) / 2 - lo)) (φ (hi - lo)).
Proof.
  intros lo hi H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (lo + (hi - lo) / 2 - lo)) = ((φ (hi - lo)) / 2)%Z) by sia.
  rewrite E. unfold Zwf. split; [lia | apply Z.div_lt; lia].
Qed.

Lemma dec_right : forall lo hi,
  (1 <? hi - lo) = true -> Zwf 0 (φ (hi - (lo + (hi - lo) / 2))) (φ (hi - lo)).
Proof.
  intros lo hi H. rewrite ltb_spec in H. change (φ 1) with 1%Z in H.
  assert (E : (φ (hi - (lo + (hi - lo) / 2))) = ((φ (hi - lo)) - (φ (hi - lo)) / 2)%Z)
    by sia.
  rewrite E. unfold Zwf.
  assert (1 <= (φ (hi - lo)) / 2)%Z by (apply Z.div_le_lower_bound; lia).
  assert ((φ (hi - lo)) / 2 <= (φ (hi - lo)))%Z by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Merges src[i, mid) and src[j, hi) into dst from k; c counts the pairs
   (left element, right element) with the right one strictly smaller. *)
Fixpoint merge (src dst : array int) (mid hi i j k c : int)
    (H : Acc (Zwf 0) (mm mid hi i j)) {struct H} : array int * int :=
  match bdec (i <? mid) with
  | left Hi =>
      match bdec (j <? hi) with
      | left Hj =>
          let x := src.[i] in
          let y := src.[j] in
          if y <? x then
            merge src dst.[k <- y] mid hi i (j + 1) (k + 1) (c + (mid - i))
              (Acc_inv H (mm_dec_j mid hi i j Hj))
          else
            merge src dst.[k <- x] mid hi (i + 1) j (k + 1) c
              (Acc_inv H (mm_dec_i mid hi i j Hi))
      | right _ =>
          merge src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1) c
            (Acc_inv H (mm_dec_i mid hi i j Hi))
      end
  | right _ =>
      match bdec (j <? hi) with
      | left Hj =>
          merge src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1) c
            (Acc_inv H (mm_dec_j mid hi i j Hj))
      | right _ => (dst, c)
      end
  end.

Lemma merge_eq : forall src dst mid hi i j k c H,
  merge src dst mid hi i j k c H =
  match bdec (i <? mid) with
  | left Hi =>
      match bdec (j <? hi) with
      | left Hj =>
          let x := src.[i] in
          let y := src.[j] in
          if y <? x then
            merge src dst.[k <- y] mid hi i (j + 1) (k + 1) (c + (mid - i))
              (Acc_inv H (mm_dec_j mid hi i j Hj))
          else
            merge src dst.[k <- x] mid hi (i + 1) j (k + 1) c
              (Acc_inv H (mm_dec_i mid hi i j Hi))
      | right _ =>
          merge src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1) c
            (Acc_inv H (mm_dec_i mid hi i j Hi))
      end
  | right _ =>
      match bdec (j <? hi) with
      | left Hj =>
          merge src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1) c
            (Acc_inv H (mm_dec_j mid hi i j Hj))
      | right _ => (dst, c)
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Sorts the segment [lo, hi) of w (lo < hi), the result landing in w when
   b = true and in s when b = false; adds its inversions to c. *)
Fixpoint msort (b : bool) (lo hi : int) (w s : array int) (c : int)
    (H : Acc (Zwf 0) (φ (hi - lo))) {struct H} : array int * array int * int :=
  match bdec (1 <? hi - lo) with
  | left Hd =>
      let mid := lo + (hi - lo) / 2 in
      match msort (negb b) lo mid w s c (Acc_inv H (dec_left lo hi Hd)) with
      | (w1, s1, c1) =>
          match msort (negb b) mid hi w1 s1 c1 (Acc_inv H (dec_right lo hi Hd)) with
          | (w2, s2, c2) =>
              if b then
                match merge s2 w2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (w3, c3) => (w3, s2, c3)
                end
              else
                match merge w2 s2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (s3, c3) => (w2, s3, c3)
                end
          end
      end
  | right _ => if b then (w, s, c) else (w, s.[lo <- w.[lo]], c)
  end.

Lemma msort_eq : forall b lo hi w s c H,
  msort b lo hi w s c H =
  match bdec (1 <? hi - lo) with
  | left Hd =>
      let mid := lo + (hi - lo) / 2 in
      match msort (negb b) lo mid w s c (Acc_inv H (dec_left lo hi Hd)) with
      | (w1, s1, c1) =>
          match msort (negb b) mid hi w1 s1 c1 (Acc_inv H (dec_right lo hi Hd)) with
          | (w2, s2, c2) =>
              if b then
                match merge s2 w2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (w3, c3) => (w3, s2, c3)
                end
              else
                match merge w2 s2 mid hi lo mid lo c2
                        (Zwf_well_founded 0 (mm mid hi lo mid)) with
                | (s3, c3) => (w2, s3, c3)
                end
          end
      end
  | right _ => if b then (w, s, c) else (w, s.[lo <- w.[lo]], c)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition inversions_impl (a : array uint) : uint :=
  let n := PArray.length a in
  snd (msort true 0 n (PArray.copy a) (PArray.make n 0) 0
         (Zwf_well_founded 0 (φ (n - 0)))).

(* ------------------------------------------------------------------ *)
(* Math side: counting                                                 *)
(* ------------------------------------------------------------------ *)

Lemma count_lt_nil : forall x, count_lt x [] = 0%nat.
Proof. reflexivity. Qed.

Lemma count_lt_cons : forall x y r,
  count_lt x (y :: r) = ((if (y <? x)%N then 1 else 0) + count_lt x r)%nat.
Proof. intros. unfold count_lt. simpl. destruct (y <? x)%N; reflexivity. Qed.

Lemma count_lt_app : forall x l r,
  count_lt x (l ++ r) = (count_lt x l + count_lt x r)%nat.
Proof. intros. unfold count_lt. rewrite filter_app, length_app. reflexivity. Qed.

Lemma count_lt_perm : forall x r r', Permutation r r' -> count_lt x r = count_lt x r'.
Proof. intros x r r' P. induction P; rewrite ?count_lt_cons; lia. Qed.

Lemma count_lt_le : forall x l, (count_lt x l <= List.length l)%nat.
Proof.
  intros x l. induction l as [|y l IH]; [rewrite count_lt_nil; simpl; lia|].
  rewrite count_lt_cons. simpl. destruct (y <? x)%N; lia.
Qed.

Lemma count_lt_zero : forall x r, Forall (fun z => (x <= z)%N) r -> count_lt x r = 0%nat.
Proof.
  intros x r H. induction H as [|a r Ha Hr IH]; [reflexivity|].
  rewrite count_lt_cons, IH.
  replace (a <? x)%N with false by (symmetry; apply N.ltb_ge; exact Ha).
  reflexivity.
Qed.

(* The pairs (x in l, y in r) with y < x. *)
Fixpoint cross (l r : list N) : nat :=
  match l with
  | [] => 0%nat
  | x :: l' => (count_lt x r + cross l' r)%nat
  end.

Lemma inv_app : forall l1 l2,
  inv_list (l1 ++ l2) = (inv_list l1 + inv_list l2 + cross l1 l2)%nat.
Proof.
  induction l1 as [|x l1 IH]; intros l2; simpl; [lia|].
  rewrite count_lt_app, IH. lia.
Qed.

Lemma cross_perm_l : forall l l' r, Permutation l l' -> cross l r = cross l' r.
Proof. intros l l' r P. induction P; simpl; lia. Qed.

Lemma cross_perm_r : forall l r r', Permutation r r' -> cross l r = cross l r'.
Proof.
  intros l r r' P. induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite (count_lt_perm x r r' P). lia.
Qed.

Lemma cross_nil_r : forall l, cross l [] = 0%nat.
Proof. induction l as [|x l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma cross_cons_r_all : forall l y r, Forall (fun x => (y < x)%N) l ->
  cross l (y :: r) = (List.length l + cross l r)%nat.
Proof.
  intros l y r H. induction H as [|a l Ha Hl IH]; [reflexivity|].
  simpl. rewrite count_lt_cons, IH.
  replace (y <? a)%N with true by (symmetry; apply N.ltb_lt; exact Ha).
  lia.
Qed.

Lemma inv_le : forall l, (inv_list l <= List.length l * List.length l)%nat.
Proof.
  induction l as [|x l IH]; simpl; [lia|].
  pose proof (count_lt_le x l). nia.
Qed.

Lemma Forall_perm' : forall (P : N -> Prop) l l', Permutation l l' -> Forall P l' -> Forall P l.
Proof.
  intros P l l' Hp HF. rewrite Forall_forall in *. intros x Hx. apply HF.
  exact (Permutation_in x Hp Hx).
Qed.

(* The list merge, with the number of cross inversions it meets. *)
Fixpoint mergec (l : list N) : list N -> list N * nat :=
  match l with
  | [] => fun r => (r, 0%nat)
  | x :: l' =>
      fix inner (r : list N) : list N * nat :=
        match r with
        | [] => (x :: l', 0%nat)
        | y :: r' =>
            if (y <? x)%N then (y :: fst (inner r'), (snd (inner r') + S (List.length l'))%nat)
            else (x :: fst (mergec l' r), snd (mergec l' r))
        end
  end.

Lemma mergec_nil_l : forall r, mergec [] r = (r, 0%nat).
Proof. reflexivity. Qed.

Lemma mergec_nil_r : forall l, mergec l [] = (l, 0%nat).
Proof. intros [|x l]; reflexivity. Qed.

Lemma mergec_cons : forall x l y r,
  mergec (x :: l) (y :: r) =
  if (y <? x)%N then (y :: fst (mergec (x :: l) r),
                      (snd (mergec (x :: l) r) + S (List.length l))%nat)
  else (x :: fst (mergec l (y :: r)), snd (mergec l (y :: r))).
Proof. reflexivity. Qed.

Lemma mergec_spec : forall l r,
  StronglySorted N.le l -> StronglySorted N.le r ->
  Permutation (fst (mergec l r)) (l ++ r) /\
  StronglySorted N.le (fst (mergec l r)) /\
  snd (mergec l r) = cross l r.
Proof.
  induction l as [|x l IHl]; intros r Hl Hr.
  - rewrite mergec_nil_l. simpl. split; [apply Permutation_refl | split; auto].
  - induction r as [|y r IHr].
    + rewrite mergec_nil_r. cbn [fst snd]. rewrite app_nil_r.
      split; [apply Permutation_refl | split; [exact Hl | symmetry; apply cross_nil_r]].
    + rewrite mergec_cons.
      destruct (StronglySorted_inv Hl) as [Hl1 Hl2].
      destruct (StronglySorted_inv Hr) as [Hr1 Hr2].
      destruct (y <? x)%N eqn:E.
      * apply N.ltb_lt in E.
        destruct (IHr Hr1) as (P & S & C). cbn [fst snd].
        assert (Fx : Forall (fun z => (y < z)%N) (x :: l)).
        { constructor; [exact E|]. eapply Forall_impl; [|exact Hl2].
          intros a Ha; simpl in Ha; lia. }
        split; [|split].
        -- eapply perm_trans; [apply perm_skip, P|]. apply Permutation_middle.
        -- constructor; [exact S|].
           apply (Forall_perm' _ _ _ P).
           apply Forall_app. split; [|exact Hr2].
           eapply Forall_impl; [|exact Fx]. intros a Ha; simpl in Ha; lia.
        -- rewrite C, cross_cons_r_all by exact Fx. simpl. lia.
      * apply N.ltb_ge in E.
        destruct (IHl (y :: r) Hl1 Hr) as (P & S & C). cbn [fst snd].
        assert (Fy : Forall (fun z => (x <= z)%N) (y :: r)).
        { constructor; [exact E|]. eapply Forall_impl; [|exact Hr2].
          intros a Ha; simpl in Ha; lia. }
        split; [|split].
        -- simpl. apply perm_skip, P.
        -- constructor; [exact S|].
           apply (Forall_perm' _ _ _ P).
           apply Forall_app. split; [exact Hl2 | exact Fy].
        -- rewrite C. simpl. rewrite (count_lt_zero x (y :: r) Fy). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading arrays as lists                                             *)
(* ------------------------------------------------------------------ *)

Definition tn (v : int) : N := Z.to_N (φ v).

(* n cells of t, from i *)
Fixpoint seg (t : array int) (i : int) (n : nat) : list N :=
  match n with
  | O => []
  | S n' => tn t.[i] :: seg t (i + 1) n'
  end.

Lemma seg_S : forall t i n, seg t i (S n) = tn t.[i] :: seg t (i + 1) n.
Proof. reflexivity. Qed.

Lemma seg_length : forall n t i, List.length (seg t i n) = n.
Proof. induction n as [|n IH]; intros; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma seg_frame : forall n t t' i,
  ((φ i) + Z.of_nat n <= 4194303)%Z ->
  (forall p, ((φ i) <= (φ p) < (φ i) + Z.of_nat n)%Z -> t'.[p] = t.[p]) ->
  seg t' i n = seg t i n.
Proof.
  induction n as [|n IH]; intros t t' i Hb Hf; [reflexivity|].
  rewrite !seg_S.
  assert (Hi : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  rewrite Hf by lia. f_equal. apply IH; [lia|].
  intros p Hp. apply Hf. lia.
Qed.

Lemma seg_app : forall n1 n2 t i i',
  (φ i') = ((φ i) + Z.of_nat n1)%Z ->
  seg t i (n1 + n2) = seg t i n1 ++ seg t i' n2.
Proof.
  induction n1 as [|n1 IH]; intros n2 t i i' Hi'.
  - simpl. replace i' with i by (apply to_Z_inj; lia). reflexivity.
  - simpl. pose proof (to_Z_bounded i').
    assert (Hi : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    f_equal. apply IH. lia.
Qed.

Lemma seg_of_list : forall (l : list N) (t : array int) (i : int),
  ((φ i) + Z.of_nat (List.length l) <= 4194303)%Z ->
  (forall (k : nat) (p : int), (k < List.length l)%nat ->
     (φ p) = ((φ i) + Z.of_nat k)%Z -> nth_error l k = Some (tn t.[p])) ->
  seg t i (List.length l) = l.
Proof.
  induction l as [|x l IH]; intros t i Hb Hn; [reflexivity|].
  simpl List.length in *. rewrite seg_S.
  assert (Hi : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  f_equal.
  - specialize (Hn 0%nat i ltac:(lia) ltac:(lia)). simpl in Hn.
    inversion Hn. reflexivity.
  - apply IH; [lia|]. intros k p Hk Hp.
    apply (Hn (S k) p); [lia | lia].
Qed.

Lemma ltb_tn : forall x y : int, (tn y <? tn x)%N = (y <? x).
Proof.
  intros x y. unfold tn. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  destruct (y <? x) eqn:E.
  - rewrite ltb_spec in E. apply N.ltb_lt. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. apply N.ltb_ge. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The merge                                                           *)
(* ------------------------------------------------------------------ *)

Lemma step_post : forall (r dst : array int) (k hi v : int) (m : nat),
  ((φ k) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length dst)))%Z ->
  Z.to_nat ((φ hi) - (φ (k + 1))) = m ->
  PArray.length r = PArray.length (dst.[k <- v]) ->
  (forall p, ((φ p) < (φ (k + 1)) \/ (φ hi) <= (φ p))%Z -> r.[p] = (dst.[k <- v]).[p]) ->
  PArray.length r = PArray.length dst /\
  (forall p, ((φ p) < (φ k) \/ (φ hi) <= (φ p))%Z -> r.[p] = dst.[p]) /\
  seg r k (Z.to_nat ((φ hi) - (φ k))) = tn v :: seg r (k + 1) m.
Proof.
  intros r dst k hi v m Hk Hh Hm Hl Hf.
  pose proof (alength_bound dst).
  assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
  split; [rewrite Hl; apply alength_set|]. split.
  - intros p Hp. rewrite Hf by lia. apply aget_set_other.
    intro E; subst p; lia.
  - replace (Z.to_nat ((φ hi) - (φ k))) with (S m) by lia. rewrite seg_S. f_equal.
    rewrite Hf by lia. rewrite aget_set_same; [reflexivity|].
    rewrite ltb_spec. lia.
Qed.

Lemma merge_spec : forall (src dst : array int) (mid hi : int) (z : Z)
    (i j k c : int) (H : Acc (Zwf 0) (mm mid hi i j)),
  mm mid hi i j = z ->
  ((φ i) <= (φ mid) <= (φ j))%Z -> ((φ j) <= (φ hi))%Z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  ((φ k) + ((φ mid) - (φ i)) + ((φ hi) - (φ j)) = (φ hi))%Z ->
  PArray.length (fst (merge src dst mid hi i j k c H)) = PArray.length dst /\
  (forall p, ((φ p) < (φ k) \/ (φ hi) <= (φ p))%Z ->
     (fst (merge src dst mid hi i j k c H)).[p] = dst.[p]) /\
  seg (fst (merge src dst mid hi i j k c H)) k (Z.to_nat ((φ hi) - (φ k)))
  = fst (mergec (seg src i (Z.to_nat ((φ mid) - (φ i))))
                (seg src j (Z.to_nat ((φ hi) - (φ j))))) /\
  (φ (snd (merge src dst mid hi i j k c H)))
  = (((φ c) + Z.of_nat (snd (mergec (seg src i (Z.to_nat ((φ mid) - (φ i))))
                                  (seg src j (Z.to_nat ((φ hi) - (φ j))))))) mod wB)%Z.
Proof.
  intros src dst mid hi z. revert dst.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros dst i j k c H Hz Hij Hjh Hhd Hk.
  pose proof (alength_bound dst) as Bd.
  pose proof (to_Z_bounded c) as Bc.
  rewrite merge_eq.
  destruct (bdec (i <? mid)) as [Hi | Hi];
    [pose proof Hi as Hi'; rewrite ltb_spec in Hi'
    | pose proof Hi as Hi'; rewrite <- Bool.not_true_iff_false, ltb_spec in Hi'];
  (destruct (bdec (j <? hi)) as [Hj | Hj];
    [pose proof Hj as Hj'; rewrite ltb_spec in Hj'
    | pose proof Hj as Hj'; rewrite <- Bool.not_true_iff_false, ltb_spec in Hj']).
  - (* both runs non-empty *)
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Ei : seg src i (Z.to_nat ((φ mid) - (φ i)))
                 = tn src.[i] :: seg src (i + 1) (Z.to_nat ((φ mid) - (φ (i + 1)))))
      by (replace (Z.to_nat ((φ mid) - (φ i))) with (S (Z.to_nat ((φ mid) - (φ (i + 1)))))
            by lia; reflexivity).
    assert (Ej : seg src j (Z.to_nat ((φ hi) - (φ j)))
                 = tn src.[j] :: seg src (j + 1) (Z.to_nat ((φ hi) - (φ (j + 1)))))
      by (replace (Z.to_nat ((φ hi) - (φ j))) with (S (Z.to_nat ((φ hi) - (φ (j + 1)))))
            by lia; reflexivity).
    cbv zeta. rewrite Ei, Ej, mergec_cons, ltb_tn.
    destruct (src.[j] <? src.[i]) eqn:E; cbn [fst snd].
    + specialize (IH (mm mid hi i (j + 1))
                    ltac:(rewrite <- Hz; apply mm_dec_j; exact Hj)
                    (dst.[k <- src.[j]]) i (j + 1) (k + 1) (c + (mid - i))
                    (Acc_inv H (mm_dec_j mid hi i j Hj)) eq_refl
                    ltac:(lia) ltac:(lia)
                    ltac:(rewrite alength_set; lia) ltac:(lia)).
      rewrite Ei in IH. destruct IH as (L & F & S & C).
      destruct (step_post _ dst k hi src.[j] _ ltac:(lia) Hhd eq_refl L F)
        as (L' & F' & S').
      split; [exact L'|]. split; [exact F'|]. split.
      * rewrite S', S. reflexivity.
      * rewrite C, add_spec, sub_spec, seg_length.
        rewrite (Z.mod_small ((φ mid) - (φ i))) by (pose proof (to_Z_bounded mid); lia).
        rewrite Zplus_mod_idemp_l. f_equal. lia.
    + specialize (IH (mm mid hi (i + 1) j)
                    ltac:(rewrite <- Hz; apply mm_dec_i; exact Hi)
                    (dst.[k <- src.[i]]) (i + 1) j (k + 1) c
                    (Acc_inv H (mm_dec_i mid hi i j Hi)) eq_refl
                    ltac:(lia) ltac:(lia)
                    ltac:(rewrite alength_set; lia) ltac:(lia)).
      rewrite Ej in IH. destruct IH as (L & F & S & C).
      destruct (step_post _ dst k hi src.[i] _ ltac:(lia) Hhd eq_refl L F)
        as (L' & F' & S').
      split; [exact L'|]. split; [exact F'|]. split.
      * rewrite S', S. reflexivity.
      * exact C.
  - (* the right run is exhausted: copy the left one *)
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    assert (Ei : seg src i (Z.to_nat ((φ mid) - (φ i)))
                 = tn src.[i] :: seg src (i + 1) (Z.to_nat ((φ mid) - (φ (i + 1)))))
      by (replace (Z.to_nat ((φ mid) - (φ i))) with (S (Z.to_nat ((φ mid) - (φ (i + 1)))))
            by lia; reflexivity).
    assert (Ej : Z.to_nat ((φ hi) - (φ j)) = 0%nat) by lia.
    specialize (IH (mm mid hi (i + 1) j)
                  ltac:(rewrite <- Hz; apply mm_dec_i; exact Hi)
                  (dst.[k <- src.[i]]) (i + 1) j (k + 1) c
                  (Acc_inv H (mm_dec_i mid hi i j Hi)) eq_refl
                  ltac:(lia) ltac:(lia)
                  ltac:(rewrite alength_set; lia) ltac:(lia)).
    rewrite Ej in IH |- *. rewrite Ei. simpl seg in IH |- *.
    rewrite !mergec_nil_r in *. cbn [fst snd] in *.
    destruct IH as (L & F & S & C).
    destruct (step_post _ dst k hi src.[i] _ ltac:(lia) Hhd eq_refl L F)
      as (L' & F' & S').
    split; [exact L'|]. split; [exact F'|]. split.
    + rewrite S', S. reflexivity.
    + exact C.
  - (* the left run is exhausted: copy the right one *)
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Ej : seg src j (Z.to_nat ((φ hi) - (φ j)))
                 = tn src.[j] :: seg src (j + 1) (Z.to_nat ((φ hi) - (φ (j + 1)))))
      by (replace (Z.to_nat ((φ hi) - (φ j))) with (S (Z.to_nat ((φ hi) - (φ (j + 1)))))
            by lia; reflexivity).
    assert (Ei : Z.to_nat ((φ mid) - (φ i)) = 0%nat) by lia.
    specialize (IH (mm mid hi i (j + 1))
                  ltac:(rewrite <- Hz; apply mm_dec_j; exact Hj)
                  (dst.[k <- src.[j]]) i (j + 1) (k + 1) c
                  (Acc_inv H (mm_dec_j mid hi i j Hj)) eq_refl
                  ltac:(lia) ltac:(lia)
                  ltac:(rewrite alength_set; lia) ltac:(lia)).
    rewrite Ei in IH |- *. rewrite Ej. simpl seg in IH |- *.
    rewrite !mergec_nil_l in *. cbn [fst snd] in *.
    destruct IH as (L & F & S & C).
    destruct (step_post _ dst k hi src.[j] _ ltac:(lia) Hhd eq_refl L F)
      as (L' & F' & S').
    split; [exact L'|]. split; [exact F'|]. split.
    + rewrite S', S. reflexivity.
    + exact C.
  - (* both exhausted *)
    cbn [fst snd].
    replace (Z.to_nat ((φ hi) - (φ k))) with 0%nat by lia.
    replace (Z.to_nat ((φ mid) - (φ i))) with 0%nat by lia.
    replace (Z.to_nat ((φ hi) - (φ j))) with 0%nat by lia.
    simpl. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    rewrite Z.add_0_r, Z.mod_small by (rewrite wB_val; lia). reflexivity.
Qed.

(* Merging two sorted halves into dst: a sorted permutation of their
   union, and the cross inversions added to the counter. *)
Lemma combine : forall (src dst : array int) (lo mid hi c c2 : int) (L1 L2 : list N)
    (H : Acc (Zwf 0) (mm mid hi lo mid)) (d : array int) (c3 : int),
  ((φ lo) < (φ mid) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length dst)))%Z ->
  Permutation (seg src lo (Z.to_nat ((φ mid) - (φ lo)))) L1 ->
  Permutation (seg src mid (Z.to_nat ((φ hi) - (φ mid)))) L2 ->
  StronglySorted N.le (seg src lo (Z.to_nat ((φ mid) - (φ lo)))) ->
  StronglySorted N.le (seg src mid (Z.to_nat ((φ hi) - (φ mid)))) ->
  (φ c2) = (((φ c) + Z.of_nat (inv_list L1) + Z.of_nat (inv_list L2)) mod wB)%Z ->
  merge src dst mid hi lo mid lo c2 H = (d, c3) ->
  PArray.length d = PArray.length dst /\
  (forall p, ((φ p) < (φ lo) \/ (φ hi) <= (φ p))%Z -> d.[p] = dst.[p]) /\
  Permutation (seg d lo (Z.to_nat ((φ hi) - (φ lo)))) (L1 ++ L2) /\
  StronglySorted N.le (seg d lo (Z.to_nat ((φ hi) - (φ lo)))) /\
  (φ c3) = (((φ c) + Z.of_nat (inv_list (L1 ++ L2))) mod wB)%Z.
Proof.
  intros src dst lo mid hi c c2 L1 L2 H d c3 Hlmh Hhd P1 P2 S1 S2 Hc2 E.
  destruct (merge_spec src dst mid hi _ lo mid lo c2 H eq_refl
              ltac:(lia) ltac:(lia) Hhd ltac:(lia)) as (L & F & S & C).
  rewrite E in L, F, S, C. cbn [fst snd] in L, F, S, C.
  destruct (mergec_spec _ _ S1 S2) as (P & SS & X).
  split; [exact L|]. split; [exact F|].
  rewrite S. split; [|split; [exact SS|]].
  - eapply perm_trans; [exact P|]. apply Permutation_app; assumption.
  - rewrite C, X, Hc2, Zplus_mod_idemp_l, inv_app.
    rewrite (cross_perm_l _ _ _ P1), (cross_perm_r _ _ _ P2).
    f_equal. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The sort                                                            *)
(* ------------------------------------------------------------------ *)

Lemma msort_spec : forall (z : Z) (b : bool) (lo hi : int) (w s : array int) (c : int)
    (H : Acc (Zwf 0) (φ (hi - lo))) (w' s' : array int) (c' : int),
  (φ (hi - lo)) = z ->
  ((φ lo) < (φ hi))%Z -> ((φ hi) <= (φ (PArray.length w)))%Z ->
  PArray.length s = PArray.length w ->
  msort b lo hi w s c H = (w', s', c') ->
  PArray.length w' = PArray.length w /\ PArray.length s' = PArray.length w /\
  (forall p, ((φ p) < (φ lo) \/ (φ hi) <= (φ p))%Z -> w'.[p] = w.[p] /\ s'.[p] = s.[p]) /\
  Permutation (seg (if b then w' else s') lo (Z.to_nat ((φ hi) - (φ lo))))
              (seg w lo (Z.to_nat ((φ hi) - (φ lo)))) /\
  StronglySorted N.le (seg (if b then w' else s') lo (Z.to_nat ((φ hi) - (φ lo)))) /\
  (φ c') = (((φ c) + Z.of_nat (inv_list (seg w lo (Z.to_nat ((φ hi) - (φ lo)))))) mod wB)%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros b lo hi w s c H w' s' c' Hz Hlh Hhw Hsw.
  pose proof (alength_bound w) as Bw.
  pose proof (to_Z_bounded c) as Bc.
  pose proof (to_Z_bounded lo) as Blo.
  assert (Hd : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
  rewrite msort_eq.
  destruct (bdec (1 <? hi - lo)) as [Hb | Hb].
  - pose proof Hb as Hb'. rewrite ltb_spec in Hb'. change (φ 1) with 1%Z in Hb'.
    cbv zeta.
    destruct (msort (negb b) lo (lo + (hi - lo) / 2) w s c (Acc_inv H (dec_left lo hi Hb)))
      as [[w1 s1] c1] eqn:E1.
    destruct (msort (negb b) (lo + (hi - lo) / 2) hi w1 s1 c1 (Acc_inv H (dec_right lo hi Hb)))
      as [[w2 s2] c2] eqn:E2.
    set (mid := lo + (hi - lo) / 2) in *.
    assert (Hmid : (φ mid) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z) by (unfold mid; sia).
    assert (Hm1 : ((φ lo) < (φ mid) < (φ hi))%Z).
    { rewrite Hmid.
      assert (1 <= ((φ hi) - (φ lo)) / 2)%Z by (apply Z.div_le_lower_bound; lia).
      assert (2 * (((φ hi) - (φ lo)) / 2) <= (φ hi) - (φ lo))%Z by (apply Z.mul_div_le; lia).
      lia. }
    assert (Hml : (φ (mid - lo)) = ((φ mid) - (φ lo))%Z) by sia.
    assert (Hhm : (φ (hi - mid)) = ((φ hi) - (φ mid))%Z) by sia.
    destruct (IH (φ (mid - lo)) ltac:(rewrite <- Hz; exact (dec_left lo hi Hb))
                (negb b) lo mid w s c _ w1 s1 c1 eq_refl ltac:(lia) ltac:(lia) Hsw E1)
      as (Lw1 & Ls1 & F1 & P1 & S1 & C1).
    destruct (IH (φ (hi - mid)) ltac:(rewrite <- Hz; exact (dec_right lo hi Hb))
                (negb b) mid hi w1 s1 c1 _ w2 s2 c2 eq_refl ltac:(lia) ltac:(lia)
                ltac:(rewrite Ls1, Lw1; reflexivity) E2)
      as (Lw2 & Ls2 & F2 & P2 & S2 & C2).
    rewrite Lw1 in Lw2, Ls2.
    set (n1 := Z.to_nat ((φ mid) - (φ lo))) in *.
    set (n2 := Z.to_nat ((φ hi) - (φ mid))) in *.
    (* the left half of the input, read in w1 *)
    assert (Ew1 : seg w1 mid n2 = seg w mid n2).
    { apply seg_frame; [unfold n2; lia|]. intros p Hp. apply F1. unfold n2 in Hp; lia. }
    (* the input segment is the two halves *)
    assert (Eseg : seg w lo (Z.to_nat ((φ hi) - (φ lo))) = seg w lo n1 ++ seg w mid n2).
    { replace (Z.to_nat ((φ hi) - (φ lo))) with (n1 + n2)%nat by (unfold n1, n2; lia).
      apply seg_app. unfold n1; lia. }
    rewrite Ew1 in P2, C2. rewrite Eseg.
    assert (Hc2 : (φ c2) = (((φ c) + Z.of_nat (inv_list (seg w lo n1))
                           + Z.of_nat (inv_list (seg w mid n2))) mod wB)%Z)
      by (rewrite C2, C1, Zplus_mod_idemp_l; reflexivity).
    (* the sorted left half survives the second call *)
    assert (Fr : forall t2 t1 : array int,
              (forall p, ((φ p) < (φ mid) \/ (φ hi) <= (φ p))%Z -> t2.[p] = t1.[p]) ->
              seg t2 lo n1 = seg t1 lo n1).
    { intros t2 t1 Ft. apply seg_frame; [unfold n1; lia|].
      intros p Hp. apply Ft. unfold n1 in Hp; lia. }
    destruct b; simpl in P1, S1, P2, S2.
    + destruct (merge s2 w2 mid hi lo mid lo c2 (Zwf_well_founded 0 (mm mid hi lo mid)))
        as [w3 c3] eqn:E3.
      intros Heq. cbv iota in Heq. injection Heq as <- <- <-.
      assert (Es : seg s2 lo n1 = seg s1 lo n1)
        by (apply Fr; intros p Hp; apply (F2 p Hp)).
      destruct (combine s2 w2 lo mid hi c c2 (seg w lo n1) (seg w mid n2) _ w3 c3
                  Hm1 ltac:(rewrite Lw2; lia)
                  ltac:(rewrite <- Es in P1; exact P1) P2
                  ltac:(rewrite <- Es in S1; exact S1) S2 Hc2 E3)
        as (L3 & F3 & P3 & S3 & C3).
      split; [lia|]. split; [exact Ls2|]. split; [|split; [exact P3 | split; assumption]].
      intros p Hp. rewrite F3 by exact Hp.
      destruct (F2 p ltac:(lia)) as [G1 G2]. destruct (F1 p ltac:(lia)) as [G3 G4].
      rewrite G1, G2, G3, G4. split; reflexivity.
    + destruct (merge w2 s2 mid hi lo mid lo c2 (Zwf_well_founded 0 (mm mid hi lo mid)))
        as [s3 c3] eqn:E3.
      intros Heq. cbv iota in Heq. injection Heq as <- <- <-.
      assert (Es : seg w2 lo n1 = seg w1 lo n1)
        by (apply Fr; intros p Hp; apply (F2 p Hp)).
      destruct (combine w2 s2 lo mid hi c c2 (seg w lo n1) (seg w mid n2) _ s3 c3
                  Hm1 ltac:(rewrite Ls2; lia)
                  ltac:(rewrite <- Es in P1; exact P1) P2
                  ltac:(rewrite <- Es in S1; exact S1) S2 Hc2 E3)
        as (L3 & F3 & P3 & S3 & C3).
      split; [exact Lw2|]. split; [lia|]. split; [|split; [exact P3 | split; assumption]].
      intros p Hp. rewrite F3 by exact Hp.
      destruct (F2 p ltac:(lia)) as [G1 G2]. destruct (F1 p ltac:(lia)) as [G3 G4].
      rewrite G1, G2, G3, G4. split; reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hb. change (φ 1) with 1%Z in Hb.
    replace (Z.to_nat ((φ hi) - (φ lo))) with 1%nat by lia.
    assert (Cc : (φ c) = (((φ c) + Z.of_nat (inv_list (seg w lo 1))) mod wB)%Z).
    { simpl. rewrite Z.add_0_r, Z.mod_small by (rewrite wB_val; lia).
      reflexivity. }
    destruct b; intros Heq; cbv iota in Heq; injection Heq as <- <- <-.
    + split; [reflexivity|]. split; [exact Hsw|]. split; [intros; split; reflexivity|].
      split; [apply Permutation_refl|]. split; [|exact Cc].
      simpl. repeat constructor.
    + split; [reflexivity|]. split; [rewrite alength_set; exact Hsw|].
      split.
      * intros p Hp. split; [reflexivity|]. apply aget_set_other. intro E; subst p; lia.
      * simpl. rewrite aget_set_same by (rewrite ltb_spec, Hsw; lia).
        split; [apply Permutation_refl|]. split; [|exact Cc]. repeat constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma inversions_impl_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists c : N, repr (inversions_impl a) c /\ inversions_spec l c.
Proof.
  intros l a Hv Ha.
  destruct Hv as [Hlen0 _ _]. unfold len in Hlen0.
  assert (Hlen : (1 <= Z.of_nat (List.length l) <= 500000)%Z)
    by (change (5 * 10 ^ 5)%N with 500000%N in Hlen0; lia).
  clear Hlen0.
  destruct Ha as [HaL0 HaC0].
  assert (HaL : (φ (PArray.length a)) = Z.of_nat (List.length l)) by exact (eq_sym HaL0).
  assert (HaC : forall k : nat, (k < List.length l)%nat ->
            exists m, nth_error l k = Some m /\ Z.to_N (φ (a.[of_Z (Z.of_nat k)])) = m)
    by exact HaC0.
  clear HaL0 HaC0.
  exists (N.of_nat (inv_list l)). split; [|reflexivity].
  pose proof (alength_bound a) as Ba.
  assert (Ea : seg a 0 (List.length l) = l).
  { apply seg_of_list; [change (φ 0) with 0%Z; lia|].
    intros k p Hk Hp. change (φ 0) with 0%Z in Hp.
    destruct (HaC k Hk) as (m & Hm & Hr).
    replace p with (of_Z (Z.of_nat k)) by
      (apply to_Z_inj; rewrite of_Z_spec, Hp; apply Z.mod_small; rewrite wB_val; lia).
    rewrite Hm. f_equal. unfold tn. symmetry. exact Hr. }
  unfold inversions_impl. cbv zeta.
  assert (Lm : PArray.length (PArray.make (PArray.length a) 0)
               = PArray.length (PArray.copy a)).
  { rewrite alength_make, length_copy.
    replace (PArray.length a <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (msort true 0 (PArray.length a) (PArray.copy a)
              (PArray.make (PArray.length a) 0) 0
              (Zwf_well_founded 0 (φ (PArray.length a - 0))))
    as [[w' s'] c'] eqn:E.
  destruct (msort_spec _ true 0 (PArray.length a) (PArray.copy a)
              (PArray.make (PArray.length a) 0) 0 _ w' s' c' eq_refl
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(exact (Z.eq_le_incl _ _ (f_equal to_Z (eq_sym (alength_copy a))))) Lm E)
    as (_ & _ & _ & _ & _ & C).
  change (φ 0) with 0%Z in C.
  replace (Z.to_nat ((φ (PArray.length a)) - 0)) with (List.length l) in C by lia.
  rewrite (seg_frame _ a (PArray.copy a) 0) in C;
    [| change (φ 0) with 0%Z; lia | intros p _; apply aget_copy].
  rewrite Ea in C.
  pose proof (inv_le l) as Hi.
  assert (Hz : (Z.of_nat (inv_list l) <= Z.of_nat (List.length l) * Z.of_nat (List.length l))%Z)
    by lia.
  cbn [snd]. change (Z.to_N (φ c') = N.of_nat (inv_list l)).
  rewrite C, Z.add_0_l, Z.mod_small by (rewrite wB_val; nia).
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition inversions : array uint -> uint := inversions_impl.

Definition inversions_correct : forall (l : list N) (a : array uint),
  valid_input l -> repr a l ->
  exists c : N, repr (inversions a) c /\ inversions_spec l c
  := inversions_impl_correct.
