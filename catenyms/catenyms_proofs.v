(* Correctness proofs for catenyms_implem.v. *)
(* Implementation of catenyms (catenyms.spec): Hierholzer's algorithm on
   the letter multigraph, out-edges taken in increasing word order.

   Code (Part 3).  The word indices 0..n-1 are sorted by
   PrimString.compare with a top-down merge sort over one int array and
   one scratch array.  Scanning the sorted order from its end builds, for
   each first letter c (a byte code, 256 letters), a linked list head[c]
   -> nxt[..] of the words starting with c, in increasing order (flat int
   tables, n is the end of a list).  The out- and in-degrees of the
   letters are counted; the degree condition is checked letter by letter
   (no letter off by more than one, as many +1 as -1 letters, at most
   one).  The start letter is the +1 letter, or the first letter of the
   smallest word.  Hierholzer then runs iteratively: an explicit stack of
   edges stk[0..sp), ptr[c] the next unused out-edge of c; an edge is
   popped when its head letter has no unused out-edge and is written into
   the result from the end.  The answer is the result when all n edges
   were popped, otherwise None (this count replaces a separate
   reachability DFS: with the degree condition, every edge is consumed
   exactly when all are reachable from the start).  The words are never
   copied: the result holds the input strings.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] (template/polymul1); the Hierholzer measure is
   2 (n - pushes) + sp, the push being guarded by pushes < n.  No nat in
   the code.

   Proof.  Part 1 states Hierholzer recursively ([Hrel]: at x take the
   smallest unused out-edge e, run from its head (trail A), run from x
   again (trail B), output B ++ e :: A) over an abstract graph, and proves:
   under the degree condition the output is a trail ([Hrel_trail]); it
   covers every edge reachable from the start ([Hrel_covers]); it is
   lexicographically at most every trail from the start through as many
   remaining edges ([Hrel_lex], by induction on Hrel: when B is not empty
   it lives on letters the first run never reaches, so any competing
   trail splits the same way); in a balanced graph it starts with the
   smallest out-edge ([Hrel_circuit]); and the iterative stack machine
   reproduces it ([Hrel_mstar]).  Part 2 relates PrimString.compare to
   String.compare and the order of the printed line to the order of word
   sequences ([text_lt]).  Part 4 proves each loop against its math
   model ([merge_loop_spec], [msort_spec], [build_loop_spec],
   [deg_loop_spec], [chk_loop_spec], [hier_sim]); [main_run] and
   [catenyms_impl_correct] assemble the contract. *)

From Speck Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii Permutation Sorted.
From Stdlib Require PrimString PString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Require Export catenyms_implem.
Open Scope uint63_scope.
Open Scope array_scope.


Ltac eqbs := unfold ind in *;
  repeat match goal with
  | |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b)
  | H : context [Nat.eqb ?a ?b] |- _ => destruct (Nat.eqb_spec a b)
  end; lia.

(* ================================================================== *)
(* Part 2. Strings : the primitive comparison is String.compare, and   *)
(* the printed line orders as the word sequence.                       *)
(* ================================================================== *)

Lemma sapp_nil_r : forall s : string, String.append s EmptyString = s.
Proof. induction s as [|c s IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma sapp_assoc : forall s1 s2 s3 : string,
  String.append (String.append s1 s2) s3 = String.append s1 (String.append s2 s3).
Proof. induction s1 as [|c s IH]; intros; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma ascii_compare_refl : forall c, Ascii.compare c c = Eq.
Proof. intros c. unfold Ascii.compare. apply N.compare_refl. Qed.

Lemma scompare_refl : forall s, String.compare s s = Eq.
Proof. induction s as [|c s IH]; simpl; [reflexivity|rewrite ascii_compare_refl; exact IH]. Qed.

Lemma scompare_app_l : forall u s1 s2,
  String.compare (String.append u s1) (String.append u s2) = String.compare s1 s2.
Proof. induction u as [|c u IH]; intros; simpl; [reflexivity|rewrite ascii_compare_refl; apply IH]. Qed.

Definition tailok (t : string) : Prop := t = EmptyString \/ exists u, t = String "."%char u.

Lemma lowercase_tail : forall c b, lowercase (String c b) -> lowercase b.
Proof. intros c b H k d Hk. apply (H (S k) d). exact Hk. Qed.

Lemma cmp_lt_app : forall a b t1 t2, String.compare a b = Lt -> lowercase b -> tailok t1 ->
  String.compare (String.append a t1) (String.append b t2) = Lt.
Proof.
  induction a as [|c a IH]; intros b t1 t2 H Hb Ht.
  - destruct b as [|d b]; [discriminate|]. simpl.
    destruct Ht as [->|(u & ->)]; [reflexivity|]. simpl.
    assert (Hd := Hb 0%nat d eq_refl). unfold Ascii.compare.
    change (N_of_ascii "."%char) with 46%N.
    destruct (N.compare_spec 46 (N_of_ascii d)); [lia|reflexivity|lia].
  - destruct b as [|d b]; [discriminate|]. simpl in H |- *.
    destruct (Ascii.compare c d); [|reflexivity|discriminate].
    apply IH; [exact H|apply (lowercase_tail d b Hb)|exact Ht].
Qed.

Definition pfx (p : list string) : string :=
  fold_right (fun x acc => String.append x (String.append "." acc)) EmptyString p.

Definition tl_of (r : list string) : string :=
  match r with [] => EmptyString | _ :: _ => String.append "." (String.concat "." r) end.

Lemma concat_cons : forall a r, String.concat "." (a :: r) = String.append a (tl_of r).
Proof. intros a [|b r]; simpl; [rewrite sapp_nil_r; reflexivity|reflexivity]. Qed.

Lemma concat_app : forall p a r,
  String.concat "." (p ++ a :: r) = String.append (pfx p) (String.concat "." (a :: r)).
Proof.
  induction p as [|x p IH]; intros a r; [reflexivity|].
  change ((x :: p) ++ a :: r) with (x :: (p ++ a :: r)).
  rewrite concat_cons. simpl pfx. rewrite sapp_assoc. f_equal.
  destruct p as [|y p]; [reflexivity|].
  change (tl_of ((y :: p) ++ a :: r)) with (String.append "." (String.concat "." ((y :: p) ++ a :: r))).
  rewrite IH. reflexivity.
Qed.

Lemma text_lt : forall p a b r1 r2, String.compare a b = Lt -> lowercase b ->
  String.compare (text (p ++ a :: r1)) (text (p ++ b :: r2)) = Lt.
Proof.
  intros p a b r1 r2 H Hb. unfold text. rewrite !concat_app, scompare_app_l, !concat_cons.
  apply cmp_lt_app; auto. destruct r1; [left; reflexivity|right; eexists; reflexivity].
Qed.

(* the primitive string and the math string *)
Definition chr (c : ascii) : int := of_Z (Z.of_N (N_of_ascii c)).

Lemma chr_spec : forall c, (φ (chr c)) = Z.of_N (N_of_ascii c).
Proof.
  intros c. unfold chr. rewrite of_Z_spec. apply Z.mod_small.
  pose proof (N_ascii_bounded c). split; [lia|]. change wB with 9223372036854775808%Z. lia.
Qed.

Lemma list_compare_chr : forall L1 L2,
  list_compare PrimInt63.compare (map chr L1) (map chr L2)
  = String.compare (string_of_list_ascii L1) (string_of_list_ascii L2).
Proof.
  induction L1 as [|a L1 IH]; intros [|b L2]; simpl; try reflexivity.
  replace (PrimInt63.compare (chr a) (chr b)) with (Ascii.compare a b).
  - destruct (Ascii.compare a b); auto.
  - change (PrimInt63.compare (chr a) (chr b)) with (Uint63.compare (chr a) (chr b)).
    rewrite Uint63.compare_spec, !chr_spec, N2Z.inj_compare. reflexivity.
Qed.

Lemma length_list_ascii : forall w, List.length (list_ascii_of_string w) = String.length w.
Proof. induction w as [|c w IH]; simpl; [reflexivity|rewrite IH; reflexivity]. Qed.

Lemma get_list_ascii : forall w k, (k < String.length w)%nat ->
  String.get k w = Some (nth k (list_ascii_of_string w) Ascii.zero).
Proof.
  induction w as [|c w IH]; intros k Hk; simpl in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma repr_str_len : forall (p : PrimString.string) (w : string), repr p w ->
  (φ (PrimString.length p)) = Z.of_nat (String.length w).
Proof. intros p w [H _]. symmetry. exact H. Qed.

Lemma repr_str_get : forall (p : PrimString.string) (w : string), repr p w ->
  forall k c, String.get k w = Some c -> (φ (PrimString.get p (of_Z (Z.of_nat k)))) = Z.of_N (N_of_ascii c).
Proof.
  intros p w [Hl Hg] k c Hk.
  assert (Hlt : (k < String.length w)%nat).
  { destruct (Nat.lt_ge_cases k (String.length w)) as [H|H]; [exact H|].
    exfalso. clear -Hk H. revert k Hk H. induction w as [|d w IH]; intros k Hk H; [discriminate|].
    destruct k; simpl in *; [lia|]. apply (IH k Hk). lia. }
  destruct (Hg k Hlt) as (c' & Hc' & Hr). rewrite Hk in Hc'. injection Hc' as <-.
  unfold repr, repr_uint in Hr. rewrite <- Hr. pose proof (to_Z_bounded (PrimString.get p (of_Z (Z.of_nat k)))). lia.
Qed.

Lemma to_list_repr : forall (p : PrimString.string) (w : string), repr p w ->
  PrimStringAxioms.to_list p = map chr (list_ascii_of_string w).
Proof.
  intros p w Hr. pose proof (repr_str_len p w Hr) as Hl.
  apply (nth_ext _ _ 0 0).
  - rewrite length_map, length_list_ascii, <- PrimStringAxioms.length_spec. lia.
  - intros k Hk. rewrite <- PrimStringAxioms.length_spec in Hk.
    assert (Hk' : (k < String.length w)%nat) by lia.
    assert (E1 : nth k (PrimStringAxioms.to_list p) 0 = PrimString.get p (of_Z (Z.of_nat k))).
    { rewrite PrimStringAxioms.get_spec. f_equal. rewrite of_Z_spec, Z.mod_small; [lia|].
      split; [lia|]. pose proof (to_Z_bounded (PrimString.length p)). lia. }
    etransitivity; [exact E1|]. rewrite (nth_indep _ 0 (chr Ascii.zero)) by (rewrite length_map, length_list_ascii; exact Hk').
    rewrite map_nth. apply to_Z_inj. rewrite chr_spec.
    apply (repr_str_get p w Hr). apply get_list_ascii. exact Hk'.
Qed.

Lemma repr_str_compare : forall (p q : PrimString.string) (w v : string), repr p w -> repr q v ->
  PrimString.compare p q = String.compare w v.
Proof.
  intros p q w v Hp Hq. rewrite PrimStringAxioms.compare_spec, (to_list_repr p w Hp), (to_list_repr q v Hq).
  rewrite list_compare_chr, !string_of_list_ascii_of_string. reflexivity.
Qed.

Lemma repr_str_inj : forall (p : PrimString.string) (w w' : string), repr p w -> repr p w' -> w = w'.
Proof.
  intros p w w' H1 H2. apply String.compare_eq_iff.
  rewrite <- (repr_str_compare p p w w' H1 H2). apply PString.compare_refl.
Qed.

(* ================================================================== *)
(* Part 4. Proofs of the loops.                                        *)
(* ================================================================== *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma slength_bound : forall (t : array PrimString.string), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length PrimString.string t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma alength_make : forall (n : int) (v : int), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. pose proof (length_make int n v) as E. etransitivity; [exact E|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma slength_make : forall (n : int) (v : PrimString.string), ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H. pose proof (length_make PrimString.string n v) as E. etransitivity; [exact E|].
  replace (n <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Definition ix (k : nat) : int := of_Z (Z.of_nat k).
Definition nt (i : int) : nat := Z.to_nat (φ i).

Lemma ix_spec : forall k, (Z.of_nat k <= 4194304)%Z -> (φ (ix k)) = Z.of_nat k.
Proof. intros k H. unfold ix. rewrite of_Z_spec, wB_val. apply Z.mod_small. lia. Qed.

Lemma ix_nt : forall i, ix (nt i) = i.
Proof.
  intros i. unfold ix, nt. pose proof (to_Z_bounded i). rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

Lemma nt_spec : forall i, Z.of_nat (nt i) = (φ i).
Proof. intros i. unfold nt. pose proof (to_Z_bounded i). lia. Qed.

Lemma ix_inj : forall k l, (Z.of_nat k <= 4194304)%Z -> (Z.of_nat l <= 4194304)%Z -> ix k = ix l -> k = l.
Proof.
  intros k l Hk Hl E. apply (f_equal to_Z) in E. rewrite !ix_spec in E by lia. lia.
Qed.

Lemma ix_succ : forall i, ((φ i) < 4194304)%Z -> i + 1 = ix (S (nt i)).
Proof.
  intros i H. apply to_Z_inj. rewrite ix_spec by (pose proof (nt_spec i); lia).
  rewrite Nat2Z.inj_succ, nt_spec. sia.
Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (v : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. rewrite <- ltb_spec in H. exact (get_set_same int t i v H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma sget_set_same : forall (t : array PrimString.string) (i : int) (v : PrimString.string),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. rewrite <- ltb_spec in H. exact (get_set_same PrimString.string t i v H). Qed.

Lemma sget_set_other : forall (t : array PrimString.string) (i j : int) (v : PrimString.string),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other PrimString.string t i j v H). Qed.

Lemma slength_set : forall (t : array PrimString.string) (i : int) (v : PrimString.string),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set PrimString.string t i v). Qed.

Lemma ix_neq : forall k l, (Z.of_nat k <= 4194304)%Z -> (Z.of_nat l <= 4194304)%Z -> k <> l -> ix k <> ix l.
Proof. intros k l Hk Hl H E. apply H. apply ix_inj; auto. Qed.

(* ------------------------------------------------------------------ *)
(* init_loop                                                           *)
(* ------------------------------------------------------------------ *)

Lemma init_loop_eq : forall a n k H, init_loop a n k H =
  match bdec (k <? n) with
  | left Hk => init_loop a.[k <- k] n (k + 1) (Acc_inv H (dec_step n k Hk))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_loop_spec : forall n z k (a : array int) H, pgap n k = z ->
  PArray.length a = n -> ((φ k) <= (φ n))%Z ->
  (forall j, ((φ j) < (φ k))%Z -> a.[j] = j) ->
  PArray.length (init_loop a n k H) = n /\
  forall j, ((φ j) < (φ n))%Z -> (init_loop a n k H).[j] = j.
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k a H Hz Hl Hk Ha. rewrite init_loop_eq.
  destruct (bdec (k <? n)) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    assert ((φ (k + 1)) = (φ k) + 1)%Z by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| |lia|].
    + rewrite alength_set. exact Hl.
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ k)) as [E|E].
      * apply to_Z_inj in E. subst j. apply aget_set_same. rewrite Hl. exact Hc'.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    split; [exact Hl|]. intros j Hj. apply Ha. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* the order on word indices                                           *)
(* ------------------------------------------------------------------ *)

Lemma merge_loop_eq : forall x src dst iend jend i j k H,
  merge_loop x src dst iend jend i j k H =
  match bdec (i <? iend) with
  | left Hi =>
      match bdec (j <? jend) with
      | left Hj =>
          if cmpw x src.[i] src.[j]
          then merge_loop x src dst.[k <- src.[i]] iend jend (i + 1) j (k + 1)
                 (Acc_inv H (dec_mi iend i jend j Hi))
          else merge_loop x src dst.[k <- src.[j]] iend jend i (j + 1) (k + 1)
                 (Acc_inv H (dec_mj iend i jend j Hj))
      | right _ =>
          merge_loop x src dst.[k <- src.[i]] iend jend (i + 1) j (k + 1)
            (Acc_inv H (dec_mi iend i jend j Hi))
      end
  | right _ =>
      match bdec (j <? jend) with
      | left Hj =>
          merge_loop x src dst.[k <- src.[j]] iend jend i (j + 1) (k + 1)
            (Acc_inv H (dec_mj iend i jend j Hj))
      | right _ => dst
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Sort.

Variable x : array PrimString.string.

Definition le (u v : int) : Prop := cmpw x u v = true.

Lemma le_refl : forall u, le u u.
Proof. intros u. unfold le, cmpw. rewrite PString.compare_refl. reflexivity. Qed.

Lemma le_trans : forall u v w, le u v -> le v w -> le u w.
Proof.
  unfold le, cmpw. intros u v w H1 H2.
  destruct (PrimString.compare x.[u] x.[v]) eqn:E1; try discriminate;
  destruct (PrimString.compare x.[v] x.[w]) eqn:E2; try discriminate.
  - apply PString.compare_eq in E1, E2. rewrite E1, E2, PString.compare_refl. reflexivity.
  - apply PString.compare_eq in E1. rewrite E1, E2. reflexivity.
  - apply PString.compare_eq in E2. rewrite <- E2, E1. reflexivity.
  - rewrite (PString.compare_trans Lt _ _ _ E1 E2). reflexivity.
Qed.

Lemma le_total : forall u v, cmpw x u v = false -> le v u.
Proof.
  unfold le, cmpw. intros u v H.
  destruct (PrimString.compare x.[u] x.[v]) eqn:E1; try discriminate.
  rewrite PString.compare_antisym, E1. reflexivity.
Qed.

Local Open Scope nat_scope.

Definition seg (a : array int) (lo hi : nat) : list int :=
  map (fun k => a.[ix k]) (seq lo (hi - lo)).

Definition sorted (a : array int) (lo hi : nat) : Prop :=
  forall p q, lo <= p -> p <= q -> q < hi -> le a.[ix p] a.[ix q].

Lemma seg_split : forall a lo mid hi, lo <= mid <= hi ->
  seg a lo hi = seg a lo mid ++ seg a mid hi.
Proof.
  intros a lo mid hi H. unfold seg. rewrite <- map_app.
  replace (hi - lo) with ((mid - lo) + (hi - mid)) by lia.
  rewrite seq_app. f_equal. f_equal. f_equal. lia.
Qed.

Lemma seg_snoc : forall a lo k, lo <= k -> seg a lo (S k) = seg a lo k ++ [a.[ix k]].
Proof.
  intros a lo k H. rewrite (seg_split a lo k (S k)) by lia. f_equal.
  unfold seg. replace (S k - k) with 1 by lia. reflexivity.
Qed.

Lemma seg_ext : forall a b lo hi, (forall k, lo <= k < hi -> a.[ix k] = b.[ix k]) ->
  seg a lo hi = seg b lo hi.
Proof.
  intros a b lo hi H. unfold seg. apply map_ext_in. intros k Hk. apply in_seq in Hk. apply H. lia.
Qed.

Lemma seg_empty : forall a lo, seg a lo lo = [].
Proof. intros. unfold seg. rewrite Nat.sub_diag. reflexivity. Qed.

(* the invariant of the merge *)
Definition MInv (src dst : array int) (lo mid hi ni nj : nat) : Prop :=
  Permutation (seg dst lo (ni + nj - mid)) (seg src lo ni ++ seg src mid nj) /\
  sorted dst lo (ni + nj - mid) /\
  (forall p, lo <= p < ni + nj - mid ->
     (forall q, ni <= q < mid -> le dst.[ix p] src.[ix q]) /\
     (forall q, nj <= q < hi -> le dst.[ix p] src.[ix q])).

Lemma MInv_step : forall src dst lo mid hi ni nj c ni' nj',
  lo <= ni <= mid -> mid <= nj <= hi -> (Z.of_nat hi <= 4194303)%Z ->
  (Z.of_nat hi <= (φ (PArray.length dst)))%Z ->
  sorted src lo mid -> sorted src mid hi ->
  MInv src dst lo mid hi ni nj ->
  ((c = ni /\ ni < mid /\ ni' = S ni /\ nj' = nj /\ (nj < hi -> le src.[ix ni] src.[ix nj])) \/
   (c = nj /\ nj < hi /\ ni' = ni /\ nj' = S nj /\ (ni < mid -> le src.[ix nj] src.[ix ni]))) ->
  MInv src dst.[ix (ni + nj - mid) <- src.[ix c]] lo mid hi ni' nj'.
Proof.
  intros src dst lo mid hi ni nj c ni' nj' Hi Hj Hh Hl Hs1 Hs2 (HP & HS & HB) Hc.
  set (K := ni + nj - mid) in *.
  set (dst' := dst.[ix K <- src.[ix c]]).
  assert (HK : ni' + nj' - mid = S K) by (unfold K; lia).
  assert (Hlt : K < hi) by (unfold K; lia).
  assert (Hd'K : dst'.[ix K] = src.[ix c]).
  { unfold dst'. apply aget_set_same. rewrite ix_spec by lia. lia. }
  assert (Hd'p : forall p, p < K -> dst'.[ix p] = dst.[ix p]).
  { intros p Hp. unfold dst'. apply aget_set_other. apply ix_neq; lia. }
  assert (Hseg : seg dst' lo K = seg dst lo K).
  { apply seg_ext. intros k Hk. apply Hd'p. lia. }
  unfold MInv. rewrite HK. split; [|split].
  - rewrite seg_snoc by lia. rewrite Hseg, Hd'K.
    destruct Hc as [(-> & Hni & -> & -> & _)|(-> & Hnj & -> & -> & _)].
    + rewrite (seg_snoc src lo ni) by lia.
      eapply perm_trans; [apply Permutation_app_tail, HP|].
      rewrite <- !app_assoc. apply Permutation_app_head. apply Permutation_app_comm.
    + rewrite (seg_snoc src mid nj) by lia.
      eapply perm_trans; [apply Permutation_app_tail, HP|].
      rewrite <- !app_assoc. apply Permutation_refl.
  - intros p q Hp Hpq Hq.
    destruct (Nat.eq_dec q K) as [->|Hq'].
    + rewrite Hd'K. destruct (Nat.eq_dec p K) as [->|Hp'].
      * rewrite Hd'K. apply le_refl.
      * rewrite Hd'p by lia. destruct (HB p ltac:(lia)) as [HB1 HB2].
        destruct Hc as [(-> & Hni & _)|(-> & Hnj & _)]; [apply HB1|apply HB2]; lia.
    + rewrite !Hd'p by lia. apply HS; lia.
  - intros p Hp. destruct (Nat.eq_dec p K) as [->|Hp'].
    + rewrite Hd'K.
      destruct Hc as [(-> & Hni & -> & -> & Hc)|(-> & Hnj & -> & -> & Hc)]; split; intros q Hq.
      * apply Hs1; lia.
      * apply le_trans with src.[ix nj]; [apply Hc; lia|apply Hs2; lia].
      * apply le_trans with src.[ix ni]; [apply Hc; lia|apply Hs1; lia].
      * apply Hs2; lia.
    + rewrite Hd'p by lia. destruct (HB p ltac:(lia)) as [HB1 HB2].
      destruct Hc as [(-> & Hni & -> & -> & _)|(-> & Hnj & -> & -> & _)];
        split; intros q Hq; [apply HB1|apply HB2|apply HB1|apply HB2]; lia.
Qed.


Lemma merge_loop_spec : forall src lo mid hi, lo <= mid <= hi -> (Z.of_nat hi <= 4194303)%Z ->
  sorted src lo mid -> sorted src mid hi ->
  forall z i j k dst H, mg (ix mid) i (ix hi) j = z ->
  lo <= nt i <= mid -> mid <= nt j <= hi -> nt k = nt i + nt j - mid ->
  (Z.of_nat hi <= (φ (PArray.length dst)))%Z ->
  MInv src dst lo mid hi (nt i) (nt j) ->
  let r := merge_loop x src dst (ix mid) (ix hi) i j k H in
  PArray.length r = PArray.length dst /\ Permutation (seg r lo hi) (seg src lo hi) /\ sorted r lo hi.
Proof.
  intros src lo mid hi Hlmh Hh Hs1 Hs2 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i j k dst H Hz Hi Hj Hk Hl HM. cbv zeta. rewrite merge_loop_eq.
  assert (Hmid : (φ (ix mid)) = Z.of_nat mid) by (apply ix_spec; lia).
  assert (Hhi : (φ (ix hi)) = Z.of_nat hi) by (apply ix_spec; lia).
  pose proof (nt_spec i) as Ei. pose proof (nt_spec j) as Ej. pose proof (nt_spec k) as Ek.
  assert (Hki : k = ix (nt i + nt j - mid)) by (rewrite <- Hk, ix_nt; reflexivity).
  assert (Hi1 : forall (Hc : (i <? ix mid)%uint63 = true), nt (i + 1)%uint63 = S (nt i)).
  { intros Hc. rewrite ltb_spec in Hc. unfold nt. sia. }
  assert (Hj1 : forall (Hc : (j <? ix hi)%uint63 = true), nt (j + 1)%uint63 = S (nt j)).
  { intros Hc. rewrite ltb_spec in Hc. unfold nt. sia. }
  assert (Hk1 : nt (k + 1)%uint63 = S (nt k)) by (unfold nt; pose proof (to_Z_bounded k); sia).
  assert (Hgi : i = ix (nt i)) by (rewrite ix_nt; reflexivity).
  assert (Hgj : j = ix (nt j)) by (rewrite ix_nt; reflexivity).
  destruct (bdec (i <? ix mid)%uint63) as [Hc1|Hc1].
  - pose proof Hc1 as Hc1'. rewrite ltb_spec in Hc1'.
    destruct (bdec (j <? ix hi)%uint63) as [Hc2|Hc2].
    + pose proof Hc2 as Hc2'. rewrite ltb_spec in Hc2'.
      destruct (cmpw x src.[i] src.[j]) eqn:Ecmp.
      * edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mi; exact Hc1) (i + 1)%uint63 j (k + 1)%uint63 dst.[k <- src.[i]] (Acc_inv H (dec_mi (ix mid) i (ix hi) j Hc1)) eq_refl) as (R1 & R2 & R3);
          [rewrite (Hi1 Hc1); lia|lia|rewrite (Hi1 Hc1), Hk1; lia|rewrite alength_set; exact Hl| |].
        { rewrite (Hi1 Hc1). replace (dst.[k <- src.[i]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt i)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt i)); auto; try lia.
          left. repeat split; try lia. intros _. rewrite <- Hgi, <- Hgj. exact Ecmp. }
        { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
      * edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mj; exact Hc2) i (j + 1)%uint63 (k + 1)%uint63 dst.[k <- src.[j]] (Acc_inv H (dec_mj (ix mid) i (ix hi) j Hc2)) eq_refl) as (R1 & R2 & R3);
          [lia|rewrite (Hj1 Hc2); lia|rewrite (Hj1 Hc2), Hk1; lia|rewrite alength_set; exact Hl| |].
        { rewrite (Hj1 Hc2). replace (dst.[k <- src.[j]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt j)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt j)); auto; try lia.
          right. repeat split; try lia. intros _. rewrite <- Hgi, <- Hgj. apply le_total. exact Ecmp. }
        { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Hc2.
      edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mi; exact Hc1) (i + 1)%uint63 j (k + 1)%uint63 dst.[k <- src.[i]] (Acc_inv H (dec_mi (ix mid) i (ix hi) j Hc1)) eq_refl) as (R1 & R2 & R3);
        [rewrite (Hi1 Hc1); lia|lia|rewrite (Hi1 Hc1), Hk1; lia|rewrite alength_set; exact Hl| |].
      { rewrite (Hi1 Hc1). replace (dst.[k <- src.[i]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt i)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt i)); auto; try lia; left; repeat split; lia. }
      { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc1.
    destruct (bdec (j <? ix hi)%uint63) as [Hc2|Hc2].
    + pose proof Hc2 as Hc2'. rewrite ltb_spec in Hc2'.
      edestruct (IH _ ltac:(rewrite <- Hz; apply dec_mj; exact Hc2) i (j + 1)%uint63 (k + 1)%uint63 dst.[k <- src.[j]] (Acc_inv H (dec_mj (ix mid) i (ix hi) j Hc2)) eq_refl) as (R1 & R2 & R3);
        [lia|rewrite (Hj1 Hc2); lia|rewrite (Hj1 Hc2), Hk1; lia|rewrite alength_set; exact Hl| |].
      { rewrite (Hj1 Hc2). replace (dst.[k <- src.[j]]) with (dst.[ix (nt i + nt j - mid) <- src.[ix (nt j)]]) by (rewrite ix_nt, <- Hki; reflexivity). apply (MInv_step src dst lo mid hi (nt i) (nt j) (nt j)); auto; try lia; right; repeat split; lia. }
      { split; [rewrite R1, alength_set; reflexivity|split; assumption]. }
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Hc2.
      assert (nt i = mid) by lia. assert (nt j = hi) by lia.
      destruct HM as (HP & HS & _). rewrite H0, H1 in HP, HS.
      replace (mid + hi - mid) with hi in HP, HS by lia.
      split; [reflexivity|split; [|exact HS]].
      rewrite (seg_split src lo mid hi) by lia. exact HP.
Qed.

End Sort.


Lemma merge_loop_spec2 : forall x src lo iend jend, (lo <= nt iend <= nt jend)%nat ->
  (Z.of_nat (nt jend) <= 4194303)%Z ->
  sorted x src lo (nt iend) -> sorted x src (nt iend) (nt jend) ->
  forall i j k dst H,
  (lo <= nt i <= nt iend)%nat -> (nt iend <= nt j <= nt jend)%nat -> nt k = (nt i + nt j - nt iend)%nat ->
  (Z.of_nat (nt jend) <= (φ (PArray.length dst)))%Z ->
  MInv x src dst lo (nt iend) (nt jend) (nt i) (nt j) ->
  let r := merge_loop x src dst iend jend i j k H in
  PArray.length r = PArray.length dst /\ Permutation (seg r lo (nt jend)) (seg src lo (nt jend)) /\
  sorted x r lo (nt jend).
Proof.
  intros x src lo iend jend.
  generalize (ix_nt iend) (ix_nt jend). generalize (nt iend) (nt jend). intros mid hi E1 E2.
  subst iend jend. intros. eapply merge_loop_spec; eauto.
Qed.

Lemma copy_loop_eq : forall src dst hi k H, copy_loop src dst hi k H =
  match bdec (k <? hi) with
  | left Hk => copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_loop_spec : forall src hi z k dst H, pgap hi k = z ->
  ((φ hi) <= (φ (PArray.length dst)))%Z ->
  let r := copy_loop src dst hi k H in
  PArray.length r = PArray.length dst /\
  (forall j, ((φ k) <= (φ j) < (φ hi))%Z -> r.[j] = src.[j]) /\
  (forall j, ((φ j) < (φ k) \/ (φ hi) <= (φ j))%Z -> r.[j] = dst.[j]).
Proof.
  intros src hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k dst H Hz Hl. cbv zeta. rewrite copy_loop_eq.
  destruct (bdec (k <? hi)) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec in Hc'.
    assert (Hk1 : ((φ (k + 1)) = (φ k) + 1)%Z) by sia.
    edestruct (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hc) (k + 1) dst.[k <- src.[k]]
                 (Acc_inv H (dec_step hi k Hc)) eq_refl) as (R1 & R2 & R3);
      [rewrite alength_set; exact Hl|].
    split; [rewrite R1, alength_set; reflexivity|split].
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ k)) as [E|E].
      * rewrite R3 by lia. apply to_Z_inj in E. subst j. apply aget_set_same. lia.
      * apply R2. lia.
    + intros j Hj. rewrite R3 by lia. apply aget_set_other.
      intro F. subst j. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc.
    split; [reflexivity|split; [intros j Hj; lia|intros; reflexivity]].
Qed.

Lemma msort_eq : forall x a t lo hi H, msort x a t lo hi H =
  match bdec (splitc lo hi) with
  | left Hs =>
      match msort x a t lo (midp lo hi) (Acc_inv H (dec_ms1 lo hi Hs)) with
      | (a1, t1) =>
          match msort x a1 t1 (midp lo hi) hi (Acc_inv H (dec_ms2 lo hi Hs)) with
          | (a2, t2) =>
              let t3 := merge_loop x a2 t2 (midp lo hi) hi lo (midp lo hi) lo
                          (Zwf_well_founded 0 _) in
              (copy_loop t3 a2 hi lo (Zwf_well_founded 0 _), t3)
          end
      end
  | right _ => (a, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sorted_ext : forall x a b lo hi, (forall k, (lo <= k < hi)%nat -> a.[ix k] = b.[ix k]) ->
  sorted x a lo hi -> sorted x b lo hi.
Proof. intros x a b lo hi E H p q Hp Hpq Hq. rewrite <- !E by lia. apply H; lia. Qed.

Lemma msort_spec : forall x z lo hi a t H a' t', pgap hi lo = z ->
  ((φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z -> PArray.length t = PArray.length a ->
  msort x a t lo hi H = (a', t') ->
  PArray.length a' = PArray.length a /\ PArray.length t' = PArray.length t /\
  (forall j, ((φ j) < (φ lo) \/ (φ hi) <= (φ j))%Z -> a'.[j] = a.[j]) /\
  Permutation (seg a' (nt lo) (nt hi)) (seg a (nt lo) (nt hi)) /\
  sorted x a' (nt lo) (nt hi).
Proof.
  intros x z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi a t H a' t' Hz Hlh Hha Hta Hm. rewrite msort_eq in Hm.
  pose proof (alength_bound a) as Ba.
  pose proof (nt_spec lo) as Elo. pose proof (nt_spec hi) as Ehi.
  destruct (bdec (splitc lo hi)) as [Hs|Hs].
  - pose proof (splitc_spec lo hi Hs) as (S1 & S2 & S3 & S4).
    set (mid := midp lo hi) in *.
    pose proof (nt_spec mid) as Emid.
    revert Hm.
    lazymatch goal with |- context [msort x a t lo ?m ?P] => destruct (msort x a t lo m P) as [a1 t1] eqn:E1 end.
    destruct (IH _ ltac:(rewrite <- Hz; apply dec_ms1; exact Hs) lo mid a t _ a1 t1 eq_refl
               ltac:(lia) ltac:(lia) Hta E1) as (A1 & A2 & A3 & A4 & A5).
    lazymatch goal with |- context [msort x a1 t1 ?m hi ?P] => destruct (msort x a1 t1 m hi P) as [a2 t2] eqn:E2 end.
    destruct (IH _ ltac:(rewrite <- Hz; apply dec_ms2; exact Hs) mid hi a1 t1 _ a2 t2 eq_refl
               ltac:(lia) ltac:(rewrite A1; lia) ltac:(rewrite A2, A1; exact Hta) E2) as (B1 & B2 & B3 & B4 & B5).
    intros Hm. cbv zeta in Hm. injection Hm as <- <-.
    set (t3 := merge_loop x a2 t2 mid hi lo mid lo (Zwf_well_founded 0 _)).
    (* the left run is untouched by the second sort *)
    assert (L2 : forall k, (nt lo <= k < nt mid)%nat -> a2.[ix k] = a1.[ix k]).
    { intros k Hk. apply B3. rewrite ix_spec by lia. lia. }
    assert (R1 : forall k, (nt mid <= k < nt hi)%nat -> a1.[ix k] = a.[ix k]).
    { intros k Hk. apply A3. rewrite ix_spec by lia. lia. }
    assert (Hsl : sorted x a2 (nt lo) (nt mid)).
    { apply (sorted_ext x a1); [intros k Hk; symmetry; apply L2; exact Hk|exact A5]. }
    assert (HM : PArray.length t3 = PArray.length t2 /\
                 Permutation (seg t3 (nt lo) (nt hi)) (seg a2 (nt lo) (nt hi)) /\
                 sorted x t3 (nt lo) (nt hi)).
    { unfold t3.
      apply (merge_loop_spec2 x a2 (nt lo) mid hi); try lia.
      - exact Hsl.
      - exact B5.
      - unfold MInv.
        replace (nt lo + nt mid - nt mid)%nat with (nt lo) by lia.
        rewrite !seg_empty. split; [apply Permutation_refl|split].
        + intros p q Hp Hpq Hq. lia.
        + intros p Hp. lia. }
    destruct HM as (M1 & M2 & M3).
    destruct (copy_loop_spec t3 hi _ lo a2 (Zwf_well_founded 0 (pgap hi lo)) eq_refl
               ltac:(rewrite B1, A1; lia)) as (C1 & C2 & C3).
    set (r := copy_loop t3 a2 hi lo (Zwf_well_founded 0 (pgap hi lo))) in *.
    assert (Hr : forall k, (nt lo <= k < nt hi)%nat -> r.[ix k] = t3.[ix k]).
    { intros k Hk. apply C2. rewrite ix_spec by lia. lia. }
    split; [rewrite C1, B1, A1; reflexivity|].
    split; [rewrite M1, B2, A2; reflexivity|].
    split; [intros j Hj; rewrite C3, B3, A3 by lia; reflexivity|].
    split.
    + rewrite (seg_ext r t3) by exact Hr.
      eapply perm_trans; [exact M2|].
      rewrite (seg_split a2 (nt lo) (nt mid) (nt hi)) by lia.
      rewrite (seg_split a (nt lo) (nt mid) (nt hi)) by lia.
      rewrite (seg_ext a2 a1 (nt lo) (nt mid)) by exact L2.
      apply Permutation_app; [exact A4|].
      eapply perm_trans; [exact B4|].
      rewrite (seg_ext a1 a (nt mid) (nt hi)) by exact R1. apply Permutation_refl.
    + apply (sorted_ext x t3); [intros k Hk; symmetry; apply Hr; exact Hk|exact M3].
  - injection Hm as <- <-.
    unfold splitc in Hs. apply Bool.andb_false_iff in Hs.
    assert (Hsm : ((φ hi) - (φ lo) <= 1)%Z).
    { destruct Hs as [Hs|Hs]; rewrite <- Bool.not_true_iff_false, ltb_spec in Hs; [lia|].
      assert ((φ (hi - lo)) = (φ hi) - (φ lo))%Z by sia. lia. }
    split; [reflexivity|split; [reflexivity|split; [reflexivity|split; [apply Permutation_refl|]]]].
    intros p q Hp Hpq Hq. assert (p = q) by lia. subst q. apply le_refl.
Qed.

Lemma aget_make : forall (n v i : int), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make int v n i). Qed.

Lemma sget_make : forall (n i : int) (v : PrimString.string), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make PrimString.string v n i). Qed.

(* the linked list of nodes from p *)
Fixpoint chain (nx : array int) (nI : int) (p : int) (l : list nat) : Prop :=
  match l with
  | [] => p = nI
  | e :: l' => p = ix e /\ chain nx nI nx.[p] l'
  end.

Lemma chain_upd : forall nx nI i v l p, (forall f, In f l -> ix f <> i) ->
  chain nx.[i <- v] nI p l <-> chain nx nI p l.
Proof.
  intros nx nI i v l. induction l as [|e l IH]; intros p Hl; simpl; [reflexivity|].
  split; intros [Hp Hc]; split; auto.
  - rewrite aget_set_other in Hc by (subst p; intro E; apply (Hl e (or_introl eq_refl)); symmetry; exact E).
    apply IH; [intros f Hf; apply Hl; right; exact Hf|exact Hc].
  - rewrite aget_set_other by (subst p; intro E; apply (Hl e (or_introl eq_refl)); symmetry; exact E).
    apply IH; [intros f Hf; apply Hl; right; exact Hf|exact Hc].
Qed.

Definition code (o : option ascii) : nat :=
  match o with Some c => N.to_nat (N_of_ascii c) | None => 0%nat end.

Lemma code_lt : forall o, (code o < 256)%nat.
Proof. intros [c|]; simpl; [pose proof (N_ascii_bounded c); lia|lia]. Qed.

Lemma code_inj : forall c d, code (Some c) = code (Some d) -> c = d.
Proof.
  intros c d H. simpl in H. rewrite <- (ascii_N_embedding c), <- (ascii_N_embedding d).
  f_equal. lia.
Qed.


Lemma skipn_cons_nth : forall (L : list nat) m, (m < List.length L)%nat ->
  skipn m L = nth m L 0%nat :: skipn (S m) L.
Proof.
  induction L as [|a L IH]; intros m Hm; simpl in Hm; [lia|].
  destruct m as [|m]; [reflexivity|]. simpl. apply IH. lia.
Qed.

Lemma in_skipn_l : forall (L : list nat) k a, In a (skipn k L) -> In a L.
Proof. intros L k a H. rewrite <- (firstn_skipn k L). apply in_or_app. right. exact H. Qed.


Lemma cnt_le : forall f v l, (cnt f v l <= Z.of_nat (List.length l))%Z.
Proof.
  intros f v l. induction l as [|e l IH]; [unfold cnt; simpl; lia|].
  rewrite cnt_cons, length_cons. unfold ind. destruct (Nat.eqb (f e) v); lia.
Qed.

Lemma filter_len1_uniq : forall (p : nat -> bool) l a b, NoDup l -> List.length (filter p l) = 1%nat ->
  In a l -> p a = true -> In b l -> p b = true -> a = b.
Proof.
  intros p l a b Hn Hl Ha Hpa Hb Hpb.
  assert (Ha' : In a (filter p l)) by (apply filter_In; auto).
  assert (Hb' : In b (filter p l)) by (apply filter_In; auto).
  destruct (filter p l) as [|y [|y' r]]; simpl in Hl; try lia.
  destruct Ha' as [<-|[]]; destruct Hb' as [<-|[]]; reflexivity.
Qed.

Lemma filter_len1_ex : forall (p : nat -> bool) l, List.length (filter p l) = 1%nat ->
  exists a, In a l /\ p a = true.
Proof.
  intros p l Hl. destruct (filter p l) as [|y r] eqn:E; simpl in Hl; [lia|].
  exists y. apply filter_In. rewrite E. left. reflexivity.
Qed.

Lemma filter_len0 : forall (p : nat -> bool) l a, List.length (filter p l) = 0%nat ->
  In a l -> p a = false.
Proof.
  intros p l a Hl Ha. destruct (p a) eqn:E; [|reflexivity].
  assert (In a (filter p l)) by (apply filter_In; auto).
  destruct (filter p l); [destruct H|simpl in Hl; lia].
Qed.

Lemma filter_len_exact1 : forall (p : nat -> bool) l a, NoDup l -> In a l -> p a = true ->
  (forall c, In c l -> p c = true -> c = a) -> List.length (filter p l) = 1%nat.
Proof.
  intros p l a Hn Ha Hpa Hu.
  assert (Hnd : NoDup (filter p l)) by (apply NoDup_filter; exact Hn).
  assert (Hin : In a (filter p l)) by (apply filter_In; auto).
  destruct (filter p l) as [|y [|y' r]] eqn:E; [destruct Hin|reflexivity|].
  exfalso. assert (Hy : In y (filter p l)) by (rewrite E; left; reflexivity).
  assert (Hy' : In y' (filter p l)) by (rewrite E; right; left; reflexivity).
  apply filter_In in Hy as [Hy1 Hy2]. apply filter_In in Hy' as [Hy1' Hy2'].
  apply NoDup_cons_iff in Hnd as [Hnd _]. apply Hnd. left.
  rewrite (Hu y Hy1 Hy2), (Hu y' Hy1' Hy2'). reflexivity.
Qed.

Lemma filter_len_exact0 : forall (p : nat -> bool) l, (forall c, In c l -> p c = false) ->
  List.length (filter p l) = 0%nat.
Proof.
  intros p l H. induction l as [|a l IH]; [reflexivity|]. simpl.
  rewrite (H a (or_introl eq_refl)). apply IH. intros c Hc. apply H. right. exact Hc.
Qed.


Lemma filter_snoc : forall (p : nat -> bool) l a,
  Z.of_nat (List.length (filter p (l ++ [a]))) = (Z.of_nat (List.length (filter p l)) + if p a then 1 else 0)%Z.
Proof. intros. rewrite filter_app, length_app. simpl. destruct (p a); simpl; lia. Qed.

Lemma existsb_snoc : forall (p : nat -> bool) l a, existsb p (l ++ [a]) = orb (existsb p l) (p a).
Proof. intros. rewrite existsb_app. simpl. rewrite Bool.orb_false_r. reflexivity. Qed.


Lemma add1_small : forall a, ((φ a) < 4194304)%Z -> (φ (a + 1)) = ((φ a) + 1)%Z.
Proof. intros a H. rewrite add_spec, Z.mod_small; [reflexivity|]. change (φ 1) with 1%Z. rewrite wB_val. pose proof (to_Z_bounded a). lia. Qed.

Lemma int_ix : forall (a : int) k, (φ a) = Z.of_nat k -> (Z.of_nat k <= 4194304)%Z -> a = ix k.
Proof. intros a k H1 H2. apply to_Z_inj. rewrite ix_spec by exact H2. exact H1. Qed.


Lemma flat_map_filter_perm : forall (f : nat -> nat) (cs L : list nat), NoDup cs ->
  (forall e, In e L -> In (f e) cs) ->
  Permutation (flat_map (fun c => filter (fun e => Nat.eqb (f e) c) L) cs) L.
Proof.
  intros f cs L Hnd. induction L as [|e L IH]; intros HL.
  - clear HL. induction cs as [|c cs IHc]; [reflexivity|]. simpl. apply IHc.
    apply NoDup_cons_iff in Hnd. apply Hnd.
  - set (rem := fun c => filter (fun e0 => Nat.eqb (f e0) c) (e :: L)).
    change (flat_map (fun c => filter (fun e0 => Nat.eqb (f e0) c) (e :: L)) cs) with (flat_map rem cs).
    assert (Hx : rem (f e) = e :: filter (fun e0 => Nat.eqb (f e0) (f e)) L)
      by (unfold rem; simpl; rewrite Nat.eqb_refl; reflexivity).
    eapply perm_trans; [apply (flat_map_upd cs rem (f e) e _ Hnd (HL e (or_introl eq_refl)) Hx)|].
    apply perm_skip.
    rewrite (flat_map_ext _ (fun c => filter (fun e0 => Nat.eqb (f e0) c) L)).
    + apply IH. intros g Hg. apply HL. right. exact Hg.
    + intros c. unfold upd, rem. destruct (Nat.eqb_spec c (f e)) as [->|Hne]; [reflexivity|].
      simpl. destruct (Nat.eqb_spec (f e) c); [congruence|reflexivity].
Qed.

Lemma SS_filter : forall (R : nat -> nat -> Prop) (p : nat -> bool) l,
  StronglySorted R l -> StronglySorted R (filter p l).
Proof.
  intros R p l H. induction H as [|a l Hl IH Hf]; simpl; [constructor|].
  destruct (p a); [|exact IH]. constructor; [exact IH|].
  rewrite Forall_forall in Hf |- *. intros y Hy. apply filter_In in Hy as [Hy _]. apply Hf. exact Hy.
Qed.

Lemma SS_of_nth : forall (R : nat -> nat -> Prop) l,
  (forall p q, (p < q < List.length l)%nat -> R (nth p l 0%nat) (nth q l 0%nat)) -> StronglySorted R l.
Proof.
  intros R l. induction l as [|a l IH]; intros H; constructor.
  - apply IH. intros p q Hpq. apply (H (S p) (S q)). simpl. lia.
  - rewrite Forall_forall. intros y Hy. apply In_nth with (d := 0%nat) in Hy as (j & Hj & <-).
    apply (H 0%nat (S j)). simpl. lia.
Qed.

Lemma nth_map_seq : forall (A : Type) (f : nat -> A) k m d, (k < m)%nat -> nth k (map f (seq 0 m)) d = f k.
Proof.
  intros A f k m d H. rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

Section Main.

Variable W : list string.
Variable x : array PrimString.string.
Hypothesis HV : valid_input W.
Hypothesis HR : repr x W.

Local Open Scope nat_scope.

Definition n := List.length W.
Definition word (e : nat) : string := nth e W EmptyString.
Definition tlW (e : nat) : nat := code (String.get 0 (word e)).
Definition hdW (e : nat) : nat := code (String.get (String.length (word e) - 1) (word e)).
Definition nI : int := PArray.length x.

Lemma tlW_lt : forall e, tlW e < 256.
Proof. intros. apply code_lt. Qed.
Lemma hdW_lt : forall e, hdW e < 256.
Proof. intros. apply code_lt. Qed.

Lemma n_bounds : 3 <= n <= 1000.
Proof. destruct HV as [Hn _ _ _]. unfold len in Hn. unfold n. lia. Qed.

Lemma nI_spec : (φ nI) = Z.of_nat n.
Proof. destruct HR as [HL _]. symmetry. exact HL. Qed.

Lemma x_repr : forall e, e < n -> repr x.[ix e] (word e).
Proof.
  intros e He. destruct HR as [_ Hc]. destruct (Hc e He) as (m & Hm & Hr).
  unfold word. rewrite (nth_error_nth _ _ _ Hm). exact Hr.
Qed.

Lemma word_in : forall e, e < n -> In (word e) W.
Proof. intros e He. apply nth_In. exact He. Qed.

Lemma word_len : forall e, e < n -> 1 <= String.length (word e) <= 20.
Proof.
  intros e He. destruct HV as [_ Hw _ _]. rewrite Forall_forall in Hw.
  specialize (Hw _ (word_in e He)). unfold slen in Hw. lia.
Qed.

Lemma word_lower : forall e, e < n -> lowercase (word e).
Proof.
  intros e He. destruct HV as [_ _ Hw _]. rewrite Forall_forall in Hw. apply Hw, word_in, He.
Qed.

Lemma fst_ch_spec : forall e, e < n -> (φ (fst_ch x.[ix e])) = Z.of_nat (tlW e).
Proof.
  intros e He. pose proof (word_len e He) as Hl.
  unfold tlW. rewrite (get_list_ascii (word e) 0) by lia. simpl code.
  unfold fst_ch. pose proof (repr_str_get _ _ (x_repr e He) 0 _ (get_list_ascii (word e) 0 ltac:(lia))) as E.
  change (of_Z (Z.of_nat 0)) with 0%uint63 in E. rewrite E. lia.
Qed.

Lemma lst_ch_spec : forall e, e < n -> (φ (lst_ch x.[ix e])) = Z.of_nat (hdW e).
Proof.
  intros e He. pose proof (word_len e He) as Hl. unfold hdW.
  set (k := String.length (word e) - 1).
  rewrite (get_list_ascii (word e) k) by lia. simpl code.
  unfold lst_ch.
  replace (PrimString.length x.[ix e] - 1)%uint63 with (of_Z (Z.of_nat k)).
  - rewrite (repr_str_get _ _ (x_repr e He) k _ (get_list_ascii (word e) k ltac:(lia))). lia.
  - apply to_Z_inj. pose proof (repr_str_len _ _ (x_repr e He)) as E.
    rewrite of_Z_spec, sub_spec, E. change (φ 1) with 1%Z.
    unfold k. rewrite !Z.mod_small by (rewrite wB_val; lia). lia.
Qed.

Lemma fst_ch_ix : forall e, e < n -> fst_ch x.[ix e] = ix (tlW e).
Proof. intros e He. apply to_Z_inj. rewrite fst_ch_spec by exact He. rewrite ix_spec by (pose proof (tlW_lt e); lia). reflexivity. Qed.

Lemma lst_ch_ix : forall e, e < n -> lst_ch x.[ix e] = ix (hdW e).
Proof. intros e He. apply to_Z_inj. rewrite lst_ch_spec by exact He. rewrite ix_spec by (pose proof (hdW_lt e); lia). reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* build_loop                                                          *)
(* ------------------------------------------------------------------ *)

Lemma build_loop_eq : forall ord nn nxt head k H, build_loop x ord nn nxt head k H =
  match bdec (k <? nn)%uint63 with
  | left Hk =>
      let e := ord.[nn - 1 - k] in
      let c := fst_ch x.[e] in
      let h := head.[c] in
      build_loop x ord nn nxt.[e <- h] head.[c <- e] (k + 1) (Acc_inv H (dec_step nn k Hk))
  | right _ => (nxt, head)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_loop_spec : forall (ord : array int) (L : list nat),
  List.length L = n -> NoDup L -> (forall e, In e L -> e < n) ->
  (forall k, k < n -> ord.[ix k] = ix (nth k L 0)) ->
  forall z k nxt head H nxt' head', pgap nI k = z ->
  ((φ k) <= Z.of_nat n)%Z -> (φ (PArray.length nxt)) = Z.of_nat n -> (φ (PArray.length head)) = 256%Z ->
  (forall c, c < 256 -> chain nxt nI head.[ix c] (filter (fun e => Nat.eqb (tlW e) c) (skipn (n - nt k) L))) ->
  build_loop x ord nI nxt head k H = (nxt', head') ->
  (φ (PArray.length nxt')) = Z.of_nat n /\ (φ (PArray.length head')) = 256%Z /\
  forall c, c < 256 -> chain nxt' nI head'.[ix c] (filter (fun e => Nat.eqb (tlW e) c) L).
Proof.
  intros ord L HL HnL HbL Hord z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k nxt head H nxt' head' Hz Hk Hln Hlh Hch Hb.
  rewrite build_loop_eq in Hb. pose proof nI_spec as EN. pose proof n_bounds as NB.
  destruct (bdec (k <? nI)%uint63) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, EN in Hc'.
    pose proof (nt_spec k) as Ek.
    set (m := n - 1 - nt k) in *.
    assert (Hm : (nI - 1 - k)%uint63 = ix m).
    { apply to_Z_inj. rewrite ix_spec by lia. unfold m. rewrite !sub_spec, EN. change (φ 1) with 1%Z.
      rewrite (Z.mod_small (_ - 1)) by (rewrite wB_val; lia). rewrite Z.mod_small by (rewrite wB_val; lia). lia. }
    set (e := nth m L 0) in *.
    assert (HeL : In e L) by (apply nth_In; lia).
    assert (Hen : e < n) by (apply HbL; exact HeL).
    rewrite Hm, (Hord m) in Hb by lia. fold e in Hb. cbv zeta in Hb.
    rewrite (fst_ch_ix e Hen) in Hb.
    assert (Hk1 : nt (k + 1)%uint63 = S (nt k)) by (unfold nt; sia).
    assert (Hsk : skipn (n - nt (k + 1)%uint63) L = e :: skipn (n - nt k) L).
    { rewrite Hk1. replace (n - S (nt k)) with m by lia. replace (n - nt k) with (S m) by lia.
      apply skipn_cons_nth. lia. }
    assert (Hnd : ~ In e (skipn (n - nt k) L)).
    { replace (n - nt k) with (S m) by lia.
      assert (HN : NoDup (skipn m L)) by (rewrite <- (firstn_skipn m L) in HnL; apply (NoDup_app_remove_l _ _ HnL)).
      rewrite (skipn_cons_nth L m) in HN by lia. apply NoDup_cons_iff in HN. apply HN. }
    assert (Hnot : forall c, forall f, In f (filter (fun e0 => Nat.eqb (tlW e0) c) (skipn (n - nt k) L)) -> ix f <> ix e).
    { intros c f Hf. apply filter_In in Hf as [Hf _].
      assert (Hfn : f < n) by (apply HbL; apply (in_skipn_l _ _ _ Hf)).
      apply ix_neq; try lia. intro E. subst f. contradiction. }
    assert (Hte : ix (tlW e) <> ix (tlW e) -> False) by auto.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| | | | |exact Hb].
    + assert ((φ (k + 1)) = (φ k) + 1)%Z by sia. lia.
    + rewrite alength_set. exact Hln.
    + rewrite alength_set. exact Hlh.
    + intros c Hc0. rewrite Hsk. simpl filter.
      pose proof (tlW_lt e) as Hte'.
      destruct (Nat.eqb_spec (tlW e) c) as [<-|Hne].
      * simpl. rewrite aget_set_same by (rewrite Hlh, ix_spec; lia).
        split; [reflexivity|].
        rewrite aget_set_same by (rewrite Hln, ix_spec; lia).
        apply chain_upd; [apply Hnot|]. apply Hch. exact Hc0.
      * rewrite aget_set_other by (apply ix_neq; lia).
        apply chain_upd; [apply Hnot|]. apply Hch. exact Hc0.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, EN in Hc. injection Hb as <- <-.
    split; [exact Hln|split; [exact Hlh|]].
    intros c Hc0. specialize (Hch c Hc0). replace (n - nt k) with 0 in Hch by (pose proof (nt_spec k); lia).
    exact Hch.
Qed.


(* ------------------------------------------------------------------ *)
(* deg_loop                                                            *)
(* ------------------------------------------------------------------ *)

Lemma deg_loop_eq : forall nn outd ind k H, deg_loop x nn outd ind k H =
  match bdec (k <? nn)%uint63 with
  | left Hk =>
      let a := fst_ch x.[k] in
      let b := lst_ch x.[k] in
      let oa := outd.[a] in
      let ib := ind.[b] in
      deg_loop x nn outd.[a <- (oa + 1)%uint63] ind.[b <- (ib + 1)%uint63] (k + 1)%uint63 (Acc_inv H (dec_step nn k Hk))
  | right _ => (outd, ind)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition dO (c : nat) : Z := cnt tlW c (seq 0 n).
Definition dI (c : nat) : Z := cnt hdW c (seq 0 n).

Lemma deg_loop_spec : forall z k outd ini H outd' ini', pgap nI k = z ->
  ((φ k) <= Z.of_nat n)%Z -> (φ (PArray.length outd)) = 256%Z -> (φ (PArray.length ini)) = 256%Z ->
  (forall c, c < 256 -> (φ (outd.[ix c])) = cnt tlW c (seq 0 (nt k)) /\ (φ (ini.[ix c])) = cnt hdW c (seq 0 (nt k))) ->
  deg_loop x nI outd ini k H = (outd', ini') ->
  (φ (PArray.length outd')) = 256%Z /\ (φ (PArray.length ini')) = 256%Z /\
  forall c, c < 256 -> (φ (outd'.[ix c])) = dO c /\ (φ (ini'.[ix c])) = dI c.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k outd ini H outd' ini' Hz Hk Ho Hi Hinv Hd.
  rewrite deg_loop_eq in Hd. pose proof nI_spec as EN.
  destruct (bdec (k <? nI)%uint63) as [Hc|Hc].
  - pose proof Hc as Hc'. rewrite ltb_spec, EN in Hc'.
    pose proof (nt_spec k) as Ek. set (e := nt k) in *.
    assert (He : e < n) by lia.
    assert (Hke : k = ix e) by (unfold e; rewrite ix_nt; reflexivity).
    replace (x.[k]) with (x.[ix e]) in Hd by (rewrite <- Hke; reflexivity).
    rewrite (fst_ch_ix e He), (lst_ch_ix e He) in Hd. cbv zeta in Hd.
    pose proof (tlW_lt e) as T1. pose proof (hdW_lt e) as T2.
    assert (Hk1 : nt (k + 1)%uint63 = S e) by (unfold e, nt; sia).
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hc|reflexivity| | | | |exact Hd].
    + assert ((φ (k + 1)) = (φ k) + 1)%Z by sia. lia.
    + rewrite alength_set. exact Ho.
    + rewrite alength_set. exact Hi.
    + intros c Hc0. rewrite Hk1, seq_S, !cnt_app, !cnt_cons. unfold cnt at 2 4. simpl filter. rewrite ?Nat.add_0_l.
      destruct (Hinv c Hc0) as [I1 I2].
      pose proof (cnt_le tlW c (seq 0 e)) as B1. pose proof (cnt_le hdW c (seq 0 e)) as B2.
      rewrite length_seq in B1, B2.
      split.
      * destruct (Nat.eqb_spec (tlW e) c) as [<-|Hne].
        -- rewrite aget_set_same by (rewrite Ho, ix_spec; lia).
           pose proof n_bounds. rewrite add1_small by lia. rewrite I1. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [|congruence] end. cbv iota beta. simpl Datatypes.length. lia.

        -- rewrite aget_set_other by (apply ix_neq; lia). rewrite I1. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [congruence|] end. cbv iota beta. simpl Datatypes.length. lia.
      * destruct (Nat.eqb_spec (hdW e) c) as [<-|Hne].
        -- rewrite aget_set_same by (rewrite Hi, ix_spec; lia).
           pose proof n_bounds. rewrite add1_small by lia. rewrite I2. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [|congruence] end. cbv iota beta. simpl Datatypes.length. lia.

        -- rewrite aget_set_other by (apply ix_neq; lia). rewrite I2. unfold ind. repeat match goal with |- context [Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); [congruence|] end. cbv iota beta. simpl Datatypes.length. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, EN in Hc. injection Hd as <- <-.
    split; [exact Ho|split; [exact Hi|]].
    intros c Hc0. unfold dO, dI. replace n with (nt k) by (pose proof (nt_spec k); lia). apply Hinv. exact Hc0.
Qed.

(* ------------------------------------------------------------------ *)
(* chk_loop                                                            *)
(* ------------------------------------------------------------------ *)

Lemma chk_loop_eq : forall outd ini c plus minus sv bad H,
  chk_loop outd ini c plus minus sv bad H =
  match bdec (c <? 256)%uint63 with
  | left Hc =>
      let o := outd.[c] in
      let i := ini.[c] in
      (if (o =? i)%uint63 then chk_loop outd ini (c + 1) plus minus sv bad (Acc_inv H (dec_step 256 c Hc))
      else if (o =? i + 1)%uint63 then chk_loop outd ini (c + 1) (plus + 1) minus c bad (Acc_inv H (dec_step 256 c Hc))
      else if (i =? o + 1)%uint63 then chk_loop outd ini (c + 1) plus (minus + 1) sv bad (Acc_inv H (dec_step 256 c Hc))
      else chk_loop outd ini (c + 1) plus minus sv true (Acc_inv H (dec_step 256 c Hc)))%uint63
  | right _ => (plus, minus, sv, bad)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition dd (c : nat) : Z := (dO c - dI c)%Z.
Definition isP (c : nat) : bool := Z.eqb (dd c) 1.
Definition isM (c : nat) : bool := Z.eqb (dd c) (-1).
Definition isB (c : nat) : bool := orb (Z.ltb (dd c) (-1)) (Z.ltb 1 (dd c)).

Lemma dO_bound : forall c, (0 <= dO c <= 1000)%Z.
Proof. intros c. unfold dO. pose proof (cnt_le tlW c (seq 0 n)). pose proof (cnt_nonneg tlW c (seq 0 n)). rewrite length_seq in H. pose proof n_bounds. lia. Qed.
Lemma dI_bound : forall c, (0 <= dI c <= 1000)%Z.
Proof. intros c. unfold dI. pose proof (cnt_le hdW c (seq 0 n)). pose proof (cnt_nonneg hdW c (seq 0 n)). rewrite length_seq in H. pose proof n_bounds. lia. Qed.

Lemma chk_loop_spec : forall outd ini, (φ (PArray.length outd)) = 256%Z -> (φ (PArray.length ini)) = 256%Z ->
  (forall c, c < 256 -> (φ (outd.[ix c])) = dO c /\ (φ (ini.[ix c])) = dI c) ->
  forall z c plus minus sv bad H plus' minus' sv' bad', pgap 256 c = z ->
  ((φ c) <= 256)%Z ->
  (φ plus) = Z.of_nat (List.length (filter isP (seq 0 (nt c)))) ->
  (φ minus) = Z.of_nat (List.length (filter isM (seq 0 (nt c)))) ->
  bad = existsb isB (seq 0 (nt c)) ->
  ((1 <= (φ plus))%Z -> nt sv < nt c /\ isP (nt sv) = true) ->
  chk_loop outd ini c plus minus sv bad H = (plus', minus', sv', bad') ->
  (φ plus') = Z.of_nat (List.length (filter isP (seq 0 256))) /\
  (φ minus') = Z.of_nat (List.length (filter isM (seq 0 256))) /\
  bad' = existsb isB (seq 0 256) /\
  ((1 <= (φ plus'))%Z -> nt sv' < 256 /\ isP (nt sv') = true).
Proof.
  intros outd ini Ho Hi Hv z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros c plus minus sv bad H plus' minus' sv' bad' Hz Hc Hp Hm Hb Hs Hl.
  rewrite chk_loop_eq in Hl.
  destruct (bdec (c <? 256)%uint63) as [Hc0|Hc0].
  - pose proof Hc0 as Hc0'. rewrite ltb_spec in Hc0'. change (φ 256) with 256%Z in Hc0'.
    pose proof (nt_spec c) as Ec. set (v := nt c) in *.
    assert (Hcv : c = ix v) by (unfold v; rewrite ix_nt; reflexivity).
    destruct (Hv v ltac:(lia)) as [Ov Iv]. rewrite <- Hcv in Ov, Iv.
    pose proof (dO_bound v). pose proof (dI_bound v).
    assert (Hc1 : nt (c + 1)%uint63 = S v) by (unfold v, nt; sia).
    assert (Hseq : seq 0 (S v) = seq 0 v ++ [v]) by (apply seq_S).
    assert (Hlen1 : forall l, List.length (filter isP l) <= List.length l) by (intros; apply filter_length_le).
    pose proof (Hlen1 (seq 0 v)) as LP. rewrite length_seq in LP.
    assert (LM : List.length (filter isM (seq 0 v)) <= v) by (rewrite <- (length_seq v 0) at 2; apply filter_length_le).
    cbv zeta in Hl.
    assert (Hc1z : ((φ (c + 1)) = (φ c) + 1)%Z) by sia.
    assert (Hz' : Zwf 0 (pgap 256 (c + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hc0).
    assert (Hi1 : ((φ (ini.[c] + 1)) = (φ (ini.[c])) + 1)%Z) by (apply add1_small; rewrite Iv; pose proof (dI_bound v) as Bv; clear - Bv; lia).
    assert (Ho1 : ((φ (outd.[c] + 1)) = (φ (outd.[c])) + 1)%Z) by (apply add1_small; rewrite Ov; pose proof (dO_bound v) as Bv; clear - Bv; lia).
    assert (Hp1 : ((φ (plus + 1)) = (φ (plus)) + 1)%Z) by (apply add1_small; rewrite Hp; clear - LP Ec Hc0'; lia).
    assert (Hm1 : ((φ (minus + 1)) = (φ (minus)) + 1)%Z) by (apply add1_small; rewrite Hm; clear - LM Ec Hc0'; lia).
    destruct (outd.[c] =? ini.[c])%uint63 eqn:E1.
    { apply Uint63.eqb_spec in E1. assert (Hd : dd v = 0%Z) by (unfold dd; rewrite <- Ov, <- Iv, E1; lia).
      assert (HP : isP v = false) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = false) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 plus minus sv bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
    destruct (outd.[c] =? ini.[c] + 1)%uint63 eqn:E2.
    { apply Uint63.eqb_spec in E2. apply Uint63.eqb_false_spec in E1.
      assert (Hd : dd v = 1%Z) by (unfold dd; rewrite <- Ov, <- Iv, E2, Hi1; lia).
      assert (HP : isP v = true) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = false) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 (plus + 1)%uint63 minus c bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP, Hp1. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros _. split; [lia|exact HP]. }
    destruct (ini.[c] =? outd.[c] + 1)%uint63 eqn:E3.
    { apply Uint63.eqb_spec in E3.
      assert (Hd : dd v = (-1)%Z) by (unfold dd; rewrite <- Ov, <- Iv, E3, Ho1; lia).
      assert (HP : isP v = false) by (unfold isP; rewrite Hd; reflexivity).
      assert (HM : isM v = true) by (unfold isM; rewrite Hd; reflexivity).
      assert (HB : isB v = false) by (unfold isB; rewrite Hd; reflexivity).
      apply (IH _ Hz' (c + 1)%uint63 plus (minus + 1)%uint63 sv bad (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM, Hm1. lia.
      - rewrite existsb_snoc, HB, Hb. symmetry. apply Bool.orb_false_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
    { apply Uint63.eqb_false_spec in E1. apply Uint63.eqb_false_spec in E2. apply Uint63.eqb_false_spec in E3.
      assert (Hd1 : dd v <> 0%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E1, to_Z_inj; lia).
      assert (Hd2 : dd v <> 1%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E2, to_Z_inj; lia).
      assert (Hd3 : dd v <> (-1)%Z) by (unfold dd; rewrite <- Ov, <- Iv; intro F; apply E3, to_Z_inj; lia).
      assert (HP : isP v = false) by (unfold isP; apply Z.eqb_neq; exact Hd2).
      assert (HM : isM v = false) by (unfold isM; apply Z.eqb_neq; exact Hd3).
      assert (HB : isB v = true) by (unfold isB; apply Bool.orb_true_iff; lia).
      apply (IH _ Hz' (c + 1)%uint63 plus minus sv true (Acc_inv H (dec_step 256 c Hc0)) plus' minus' sv' bad' eq_refl); [lia| | | | |exact Hl];
        rewrite ?Hc1, ?Hseq; clear IH Hl Hv Hz' Hlen1.
      - rewrite filter_snoc, HP. lia.
      - rewrite filter_snoc, HM. lia.
      - rewrite existsb_snoc, HB. symmetry. apply Bool.orb_true_r.
      - intros Hq. destruct (Hs Hq). split; [lia|assumption]. }
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hc0. change (φ 256) with 256%Z in Hc0.
    assert (Hv256 : nt c = 256) by (unfold nt; lia). rewrite Hv256 in Hp, Hm, Hb, Hs.
    injection Hl as <- <- <- <-. auto.
Qed.


(* ------------------------------------------------------------------ *)
(* hier_loop : it runs the iterative procedure of Part 1               *)
(* ------------------------------------------------------------------ *)

Lemma hier_loop_eq : forall nxt nn sI ptr stk sp q res cnt H,
  hier_loop x nxt nn sI ptr stk sp q res cnt H =
  let v := if (sp =? 0)%uint63 then sI else lst_ch x.[stk.[(sp - 1)%uint63]] in
  let p := ptr.[v] in
  match bdec (andb (p <? nn) (q <? nn))%uint63 with
  | left Hp =>
      let np := nxt.[p] in
      hier_loop x nxt nn sI ptr.[v <- np] stk.[sp <- p] (sp + 1)%uint63 (q + 1)%uint63 res cnt
        (Acc_inv H (dec_push nn q sp p Hp))
  | right _ =>
      match bdec (0 <? sp)%uint63 with
      | left Hs =>
          let e := stk.[(sp - 1)%uint63] in
          hier_loop x nxt nn sI ptr stk (sp - 1)%uint63 q res.[(nn - 1 - cnt)%uint63 <- x.[e]] (cnt + 1)%uint63
            (Acc_inv H (dec_pop nn q sp Hs))
      | right _ => (res, cnt)
      end
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Hier.

Variable nxt : array int.
Variable s : nat.
Hypothesis Hs256 : s < 256.

Definition sI : int := ix s.

Definition corr (ptr stk : array int) (sp q : int) (res : array PrimString.string) (cnt : int)
    (rem : nat -> list nat) (K O : list nat) : Prop :=
  (φ (PArray.length ptr)) = 256%Z /\
  (forall c, c < 256 -> chain nxt nI ptr.[ix c] (rem c)) /\
  Inv tlW rem /\
  (φ (PArray.length stk)) = Z.of_nat n /\
  (φ sp) = Z.of_nat (List.length K) /\
  (forall i, i < List.length K -> stk.[ix i] = ix (nth (List.length K - 1 - i) K 0)) /\
  (φ (PArray.length res)) = Z.of_nat n /\
  (φ cnt) = Z.of_nat (List.length O) /\
  (forall i, i < List.length O -> res.[ix (n - 1 - i)] = x.[ix (nth (List.length O - 1 - i) O 0)]) /\
  (φ q) = Z.of_nat (List.length K + List.length O) /\
  List.length K + List.length O + List.length (E 256 rem) = n /\
  (forall e, In e (E 256 rem) -> e < n) /\
  (forall e, In e K -> e < n).

Lemma cur_lt : forall K, cur hdW s K < 256.
Proof. intros [|e K]; simpl; [exact Hs256|apply hdW_lt]. Qed.

Lemma corr_v : forall ptr stk sp q res cnt rem K O, corr ptr stk sp q res cnt rem K O ->
  (if (sp =? 0)%uint63 then sI else lst_ch x.[stk.[(sp - 1)%uint63]]) = ix (cur hdW s K).
Proof.
  intros ptr stk sp q res cnt rem K O (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  pose proof n_bounds as NB.
  destruct K as [|e K'].
  - simpl in C5. assert (sp = 0%uint63) as -> by (apply to_Z_inj; exact C5). reflexivity.
  - cbn [Datatypes.length] in *. assert (Hsp : (sp =? 0)%uint63 = false) by (apply Uint63.eqb_false_spec; intro F; subst sp; change (φ 0) with 0%Z in C5; lia).
    rewrite Hsp. assert (Hs1 : (sp - 1)%uint63 = ix (List.length K')).
    { apply int_ix; [|lia]. rewrite sub_spec, C5. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|rewrite wB_val; lia]. }
    rewrite Hs1, C6 by lia. replace (S (List.length K') - 1 - List.length K') with 0 by lia.
    simpl. apply lst_ch_ix. apply C13. left. reflexivity.
Qed.

Lemma hier_sim : forall rem K O rem2 K2 O2, mstar hdW s rem K O rem2 K2 O2 ->
  forall ptr stk sp q res cnt H, corr ptr stk sp q res cnt rem K O ->
  exists ptr' stk' sp' q' res' cnt' H', corr ptr' stk' sp' q' res' cnt' rem2 K2 O2 /\
  hier_loop x nxt nI sI ptr stk sp q res cnt H = hier_loop x nxt nI sI ptr' stk' sp' q' res' cnt' H'.
Proof.
  intros rem K O rem2 K2 O2 HM.
  induction HM as [rem K O|rem K O e r rem2 K2 O2 Hx HM IH|rem e K O rem2 K2 O2 Hx HM IH];
    intros ptr stk sp q res cnt H HC.
  - exists ptr, stk, sp, q, res, cnt, H. split; [exact HC|reflexivity].
  - pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof n_bounds as NB. pose proof (cur_lt K) as Hcl.
    set (vv := cur hdW s K) in *.
    pose proof (C2 vv Hcl) as Hch0. rewrite Hx in Hch0. simpl in Hch0. destruct Hch0 as [Hpv Hch]. rewrite Hpv in Hch.
    assert (HeE : In e (E 256 rem)) by (apply (E_In 256 tlW tlW_lt rem vv); [exact C3|rewrite Hx; left; reflexivity]).
    assert (Hen : e < n) by (apply C12; exact HeE).
    assert (HP1 : Permutation (E 256 rem) (e :: E 256 (upd rem vv r))) by (apply E_upd; [exact Hx|exact Hcl]).
    pose proof (Permutation_length HP1) as HL1. simpl in HL1.
    rewrite hier_loop_eq. cbv zeta. rewrite Hv.
    destruct (bdec (andb (ptr.[ix vv] <? nI) (q <? nI))%uint63) as [Hb|Hb].
    2:{ exfalso. rewrite Hpv in Hb. apply Bool.andb_false_iff in Hb as [Hb|Hb];
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hb; apply Hb; rewrite nI_spec;
        [rewrite ix_spec by lia; lia|rewrite C10; lia]. }
    assert (Hsp : sp = ix (List.length K)) by (apply int_ix; [exact C5|lia]).
    edestruct (IH (ptr.[ix vv <- nxt.[ptr.[ix vv]]]) (stk.[sp <- ptr.[ix vv]]) (sp + 1)%uint63 (q + 1)%uint63 res cnt)
      as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
    2:{ exists ptr', stk', sp', q', res', cnt', H'. split; [exact HC'|]. rewrite <- Heq. reflexivity. }
    rewrite Hpv. unfold corr.
    split; [rewrite alength_set; exact C1|].
    split.
    { intros c Hc. unfold upd. destruct (Nat.eqb_spec c vv) as [->|Hne].
      - rewrite aget_set_same by (rewrite C1, ix_spec; lia). exact Hch.
      - rewrite aget_set_other by (apply ix_neq; lia). apply C2. exact Hc. }
    split; [apply (Inv_upd tlW rem vv e r C3 Hx)|].
    split; [rewrite alength_set; exact C4|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C5; lia|rewrite C5; lia]|].
    split.
    { intros i Hi. cbn [Datatypes.length] in Hi. rewrite Hsp. destruct (Nat.eq_dec i (List.length K)) as [->|Hne].
      - rewrite aget_set_same by (rewrite C4, ix_spec; lia).
        cbn [Datatypes.length]. replace (S (List.length K) - 1 - List.length K) with 0 by lia. reflexivity.
      - rewrite aget_set_other by (apply ix_neq; lia). rewrite C6 by lia.
        cbn [Datatypes.length]. replace (S (List.length K) - 1 - i) with (S (List.length K - 1 - i)) by lia. reflexivity. }
    split; [exact C7|].
    split; [exact C8|].
    split; [exact C9|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C10; lia|rewrite C10; lia]|].
    split; [cbn [Datatypes.length]; lia|].
    split; [intros f Hf; apply C12; apply (Permutation_in _ (Permutation_sym HP1)); right; exact Hf|].
    intros f [<-|Hf]; [exact Hen|apply C13; exact Hf].
  - pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv.
    destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    pose proof n_bounds as NB. simpl cur in Hv.
    pose proof (hdW_lt e) as Hhe.
    pose proof (C2 (hdW e) Hhe) as Hpv. rewrite Hx in Hpv. simpl in Hpv.
    cbn [Datatypes.length] in *.
    assert (Hen : e < n) by (apply C13; left; reflexivity).
    rewrite hier_loop_eq. cbv zeta. rewrite Hv, Hpv.
    destruct (bdec (andb (nI <? nI) (q <? nI))%uint63) as [Hb|Hb].
    { exfalso. apply andb_prop in Hb as [Hb _]. rewrite ltb_spec in Hb. lia. }
    destruct (bdec (0 <? sp)%uint63) as [Hs|Hs].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hs. change (φ 0) with 0%Z in Hs. lia. }
    assert (Hs1 : (sp - 1)%uint63 = ix (List.length K)).
    { apply int_ix; [|lia]. rewrite sub_spec, C5. change (φ 1) with 1%Z. rewrite Z.mod_small; [lia|rewrite wB_val; lia]. }
    assert (Hse : stk.[(sp - 1)%uint63] = ix e).
    { rewrite Hs1, C6 by lia. cbn [Datatypes.length]. replace (S (List.length K) - 1 - List.length K) with 0 by lia. reflexivity. }
    assert (Hci : (nI - 1 - cnt)%uint63 = ix (n - 1 - List.length O)).
    { apply int_ix; [|lia]. rewrite !sub_spec, nI_spec, C8. change (φ 1) with 1%Z.
      rewrite (Z.mod_small (_ - 1)) by (rewrite wB_val; lia). rewrite Z.mod_small by (rewrite wB_val; lia). lia. }
    edestruct (IH ptr stk (sp - 1)%uint63 q (res.[(nI - 1 - cnt)%uint63 <- x.[stk.[(sp - 1)%uint63]]]) (cnt + 1)%uint63)
      as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
    2:{ exists ptr', stk', sp', q', res', cnt', H'. split; [exact HC'|]. rewrite <- Heq. reflexivity. }
    rewrite Hse, Hci. unfold corr.
    split; [exact C1|]. split; [exact C2|]. split; [exact C3|]. split; [exact C4|].
    split; [rewrite Hs1, ix_spec by lia; reflexivity|].
    split.
    { intros i Hi. rewrite C6 by lia. cbn [Datatypes.length]. replace (S (List.length K) - 1 - i) with (S (List.length K - 1 - i)) by lia. reflexivity. }
    split; [rewrite slength_set; exact C7|].
    split; [cbn [Datatypes.length]; rewrite add1_small; [rewrite C8; lia|rewrite C8; lia]|].
    split.
    { intros i Hi. cbn [Datatypes.length] in Hi. destruct (Nat.eq_dec i (List.length O)) as [->|Hne].
      - rewrite sget_set_same by (rewrite C7, ix_spec; lia).
        cbn [Datatypes.length]. replace (S (List.length O) - 1 - List.length O) with 0 by lia. reflexivity.
      - rewrite sget_set_other by (apply ix_neq; lia). rewrite C9 by lia.
        cbn [Datatypes.length]. replace (S (List.length O) - 1 - i) with (S (List.length O - 1 - i)) by lia. reflexivity. }
    split; [cbn [Datatypes.length]; rewrite C10; lia|].
    split; [cbn [Datatypes.length]; lia|].
    split; [exact C12|].
    intros f Hf. apply C13. right. exact Hf.
Qed.

Lemma hier_stop : forall ptr stk sp q res cnt rem O H, corr ptr stk sp q res cnt rem [] O ->
  rem s = [] -> hier_loop x nxt nI sI ptr stk sp q res cnt H = (res, cnt).
Proof.
  intros ptr stk sp q res cnt rem O H HC Hs.
  pose proof (corr_v _ _ _ _ _ _ _ _ _ HC) as Hv. simpl cur in Hv.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  pose proof (C2 s Hs256) as Hpv. rewrite Hs in Hpv. simpl in Hpv.
  rewrite hier_loop_eq. cbv zeta. rewrite Hv, Hpv.
  destruct (bdec (andb (nI <? nI) (q <? nI))%uint63) as [Hb|Hb].
  { exfalso. apply andb_prop in Hb as [Hb _]. rewrite ltb_spec in Hb. lia. }
  destruct (bdec (0 <? sp)%uint63) as [Hs'|Hs'].
  { exfalso. rewrite ltb_spec in Hs'. simpl in C5. change (φ 0) with 0%Z in Hs'. lia. }
  reflexivity.
Qed.

End Hier.


(* ------------------------------------------------------------------ *)
(* the math side of the answer                                         *)
(* ------------------------------------------------------------------ *)

Lemma W_map : W = map word (seq 0 n).
Proof.
  apply (nth_ext _ _ EmptyString EmptyString).
  - rewrite length_map, length_seq. reflexivity.
  - intros k Hk. rewrite nth_map_seq by exact Hk. reflexivity.
Qed.

Lemma catenym_iff : forall a b, a < n -> b < n ->
  (forms_catenym (word a) (word b) <-> hdW a = tlW b).
Proof.
  intros a b Ha Hb. pose proof (word_len a Ha). pose proof (word_len b Hb).
  unfold forms_catenym, hdW, tlW.
  rewrite (get_list_ascii (word a) (String.length (word a) - 1)) by lia.
  rewrite (get_list_ascii (word b) 0) by lia.
  split; [intros E; rewrite E; reflexivity|intros E; f_equal; apply code_inj; exact E].
Qed.

Lemma chain_of_trail : forall v T y, trail tlW hdW v T y ->
  forall j, S j < List.length T -> hdW (nth j T 0) = tlW (nth (S j) T 0).
Proof.
  intros v T y H. induction H as [v|v e l w He Hl IH]; intros j Hj; cbn [Datatypes.length] in Hj; [lia|].
  destruct j as [|j].
  - destruct l as [|f l]; cbn [Datatypes.length] in Hj; [lia|].
    apply trail_cons_inv in Hl as [Hf _]. simpl. symmetry. exact Hf.
  - simpl. apply IH. lia.
Qed.

Lemma trail_of_chain : forall T, T <> [] ->
  (forall j, S j < List.length T -> hdW (nth j T 0) = tlW (nth (S j) T 0)) ->
  exists y, trail tlW hdW (tlW (nth 0 T 0)) T y.
Proof.
  induction T as [|e T IH]; intros Hne H; [congruence|].
  destruct T as [|f T].
  - exists (hdW e). constructor; [reflexivity|constructor].
  - destruct (IH ltac:(discriminate)) as (y & Hy).
    + intros j Hj. apply (H (S j)). cbn [Datatypes.length] in *. lia.
    + exists y. constructor; [reflexivity|]. simpl.
      replace (hdW e) with (tlW f) by (symmetry; apply (H 0); cbn [Datatypes.length]; lia). exact Hy.
Qed.

(* an answer is a trail through all the word indices *)
Lemma answer_trail : forall c, is_answer W c ->
  exists T, c = map word T /\ Permutation (seq 0 n) T /\ T <> [] /\
  exists y, trail tlW hdW (tlW (nth 0 T 0)) T y.
Proof.
  intros c [[Hl Hch] HP]. rewrite W_map in HP.
  destruct (Permutation_map_inv _ _ HP) as (T & -> & HT).
  pose proof (Permutation_length HT) as HTl. rewrite length_seq in HTl.
  assert (HTb : forall e, In e T -> e < n) by (intros e He; apply (Permutation_in _ (Permutation_sym HT)) in He; apply in_seq in He; lia).
  pose proof n_bounds.
  exists T. split; [reflexivity|]. split; [exact HT|].
  split; [destruct T; [simpl in HTl; lia|discriminate]|].
  apply trail_of_chain; [destruct T; [simpl in HTl; lia|discriminate]|].
  intros j Hj. rewrite length_map in Hch.
  specialize (Hch j Hj).
  rewrite (nth_indep _ EmptyString (word 0)), map_nth in Hch by (rewrite length_map; lia).
  rewrite (nth_indep _ EmptyString (word 0)), map_nth in Hch by (rewrite length_map; lia).
  apply catenym_iff in Hch; [exact Hch| |]; apply HTb, nth_In; lia.
Qed.

Definition wlt (a b : nat) : Prop := PrimString.compare x.[ix a] x.[ix b] = Lt.

Lemma lexle_text : forall P T, lexle wlt P T -> (forall e, In e P -> e < n) -> (forall e, In e T -> e < n) ->
  String.compare (text (map word P)) (text (map word T)) <> Gt.
Proof.
  intros P T [<-|(p & a & b & r1 & r2 & E1 & E2 & Hab)] HP HT.
  - rewrite scompare_refl. discriminate.
  - subst P T. rewrite !map_app. simpl.
    assert (Ha : a < n) by (apply HP; apply in_or_app; right; left; reflexivity).
    assert (Hb : b < n) by (apply HT; apply in_or_app; right; left; reflexivity).
    unfold wlt in Hab. rewrite (repr_str_compare _ _ _ _ (x_repr a Ha) (x_repr b Hb)) in Hab.
    rewrite (text_lt _ _ _ _ _ Hab (word_lower b Hb)). discriminate.
Qed.

Lemma word_inj : forall a b, a < n -> b < n -> word a = word b -> a = b.
Proof.
  intros a b Ha Hb E. destruct HV as [_ _ _ Hnd].
  apply (proj1 (NoDup_nth W EmptyString) Hnd a b Ha Hb E).
Qed.

Lemma dd_dg : forall v, dd v = dg tlW hdW (seq 0 n) v.
Proof. reflexivity. Qed.

Lemma dd_out : forall v, 256 <= v -> dd v = 0%Z.
Proof.
  intros v Hv. unfold dd, dO, dI. rewrite !cnt_none; [reflexivity| |];
    intros e _; [pose proof (hdW_lt e)|pose proof (tlW_lt e)]; lia.
Qed.

(* the degree check accepts every input with an Euler trail *)
Lemma D_check : forall s t, D tlW hdW (seq 0 n) s t ->
  existsb isB (seq 0 256) = false /\
  List.length (filter isP (seq 0 256)) = List.length (filter isM (seq 0 256)) /\
  List.length (filter isP (seq 0 256)) <= 1.
Proof.
  intros s t HD.
  assert (Hd : forall v, dd v = (ind (Nat.eqb v s) - ind (Nat.eqb v t))%Z) by (intros v; rewrite dd_dg; apply HD).
  split.
  { apply Bool.not_true_iff_false. intro H. apply existsb_exists in H as (v & _ & Hv).
    unfold isB in Hv. rewrite Hd in Hv. apply Bool.orb_true_iff in Hv. rewrite !Z.ltb_lt in Hv. revert Hv. eqbs. }
  destruct (Nat.eq_dec s t) as [<-|Hst].
  - assert (H0 : forall v, dd v = 0%Z) by (intros v; rewrite Hd; eqbs).
    rewrite !filter_len_exact0; [lia| |]; intros c _; [unfold isM|unfold isP]; rewrite H0; reflexivity.
  - assert (Hs : dd s = 1%Z) by (rewrite Hd; eqbs).
    assert (Ht : dd t = (-1)%Z) by (rewrite Hd; eqbs).
    assert (Hs2 : s < 256) by (destruct (Nat.lt_ge_cases s 256); [assumption|rewrite dd_out in Hs by assumption; lia]).
    assert (Ht2 : t < 256) by (destruct (Nat.lt_ge_cases t 256); [assumption|rewrite dd_out in Ht by assumption; lia]).
    rewrite (filter_len_exact1 isP _ s), (filter_len_exact1 isM _ t); try lia.
    + apply seq_NoDup.
    + apply in_seq. lia.
    + unfold isM. rewrite Ht. reflexivity.
    + intros c _ Hc. unfold isM in Hc. apply Z.eqb_eq in Hc. rewrite Hd in Hc. revert Hc. eqbs.
    + apply seq_NoDup.
    + apply in_seq. lia.
    + unfold isP. rewrite Hs. reflexivity.
    + intros c _ Hc. unfold isP in Hc. apply Z.eqb_eq in Hc. rewrite Hd in Hc. revert Hc. eqbs.
Qed.

(* and what it accepts has one *)
Lemma check_D1 : forall sv, existsb isB (seq 0 256) = false ->
  List.length (filter isP (seq 0 256)) = 1 -> List.length (filter isM (seq 0 256)) = 1 ->
  sv < 256 -> isP sv = true -> exists t, D tlW hdW (seq 0 n) sv t.
Proof.
  intros sv HB HP HM Hsv Hp.
  destruct (filter_len1_ex isM _ HM) as (t & Ht & Hmt).
  exists t. intros v. rewrite <- dd_dg.
  unfold isP in Hp. unfold isM in Hmt. apply Z.eqb_eq in Hp, Hmt.
  apply in_seq in Ht.
  destruct (Nat.lt_ge_cases v 256) as [Hv|Hv]; [|rewrite dd_out by exact Hv; eqbs].
  assert (HvB : isB v = false).
  { destruct (isB v) eqn:E; [|reflexivity]. exfalso.
    assert (existsb isB (seq 0 256) = true) by (apply existsb_exists; exists v; split; [apply in_seq; lia|exact E]).
    congruence. }
  unfold isB in HvB. apply Bool.orb_false_iff in HvB as [B1 B2]. rewrite Z.ltb_ge in B1, B2.
  assert (U1 : dd v = 1%Z -> v = sv).
  { intros E. apply (filter_len1_uniq isP (seq 0 256) v sv (seq_NoDup _ _) HP);
      [apply in_seq; lia|unfold isP; rewrite E; reflexivity|apply in_seq; lia|unfold isP; rewrite Hp; reflexivity]. }
  assert (U2 : dd v = (-1)%Z -> v = t).
  { intros E. apply (filter_len1_uniq isM (seq 0 256) v t (seq_NoDup _ _) HM);
      [apply in_seq; lia|unfold isM; rewrite E; reflexivity|apply in_seq; lia|unfold isM; rewrite Hmt; reflexivity]. }
  assert (dd v = 1 \/ dd v = 0 \/ dd v = -1)%Z as [E|[E|E]] by lia.
  - pose proof (U1 E). subst v. destruct (Nat.eqb_spec sv t) as [E'|E']; [subst t; lia|]. rewrite E. eqbs.
  - rewrite E. destruct (Nat.eqb_spec v sv) as [->|H1]; [lia|]. destruct (Nat.eqb_spec v t) as [->|H2]; [lia|].
    unfold ind. lia.
  - pose proof (U2 E). subst v. destruct (Nat.eqb_spec t sv) as [E'|E']; [subst t; lia|]. rewrite E. eqbs.
Qed.

Lemma check_D0 : existsb isB (seq 0 256) = false ->
  List.length (filter isP (seq 0 256)) = 0 -> List.length (filter isM (seq 0 256)) = 0 ->
  forall s, D tlW hdW (seq 0 n) s s.
Proof.
  intros HB HP HM s v. rewrite <- dd_dg.
  destruct (Nat.lt_ge_cases v 256) as [Hv|Hv]; [|rewrite dd_out by exact Hv; eqbs].
  assert (HvB : isB v = false).
  { destruct (isB v) eqn:E; [|reflexivity]. exfalso.
    assert (existsb isB (seq 0 256) = true) by (apply existsb_exists; exists v; split; [apply in_seq; lia|exact E]).
    congruence. }
  pose proof (filter_len0 isP _ v HP ltac:(apply in_seq; lia)) as H1.
  pose proof (filter_len0 isM _ v HM ltac:(apply in_seq; lia)) as H2.
  unfold isB in HvB. apply Bool.orb_false_iff in HvB as [B1 B2]. rewrite Z.ltb_ge in B1, B2.
  unfold isP in H1. unfold isM in H2. apply Z.eqb_neq in H1, H2. eqbs.
Qed.


(* ------------------------------------------------------------------ *)
(* the run of Hierholzer meets the contract                            *)
(* ------------------------------------------------------------------ *)

Lemma main_run : forall (L : list nat) (nxt head : array int) s t,
  Permutation L (seq 0 n) -> StronglySorted wlt L ->
  s < 256 -> (φ (PArray.length head)) = 256%Z ->
  (forall c, c < 256 -> chain nxt nI head.[ix c] (filter (fun e => Nat.eqb (tlW e) c) L)) ->
  D tlW hdW (seq 0 n) s t ->
  (forall T y, Permutation (seq 0 n) T -> trail tlW hdW (tlW (nth 0 T 0)) T y -> T <> [] ->
     tlW (nth 0 T 0) = s \/ (t = s /\ s = tlW (nth 0 L 0))) ->
  forall H, exists o,
  repr (match hier_loop x nxt nI (ix s) head (PArray.make nI 0%uint63) 0%uint63 0%uint63
                (PArray.make nI (PrimString.make 0%uint63 0%uint63)) 0%uint63 H with
        | (res, cnt) => if (cnt =? nI)%uint63 then Some res else None
        end) o /\ catenyms_spec W o.
Proof.
  intros L nxt head s t HLp HLs Hs Hhl Hch HD Hstart H.
  pose proof n_bounds as NB. pose proof nI_spec as EN.
  set (rem0 := fun c => filter (fun e => Nat.eqb (tlW e) c) L).
  assert (HLb : forall e, In e L -> e < n) by (intros e He; apply (Permutation_in _ HLp), in_seq in He; lia).
  assert (HE0 : Permutation (E 256 rem0) L).
  { unfold E, rem0. apply flat_map_filter_perm; [apply seq_NoDup|]. intros e _. apply in_seq. pose proof (tlW_lt e). lia. }
  assert (HE0' : Permutation (E 256 rem0) (seq 0 n)) by (eapply perm_trans; [exact HE0|exact HLp]).
  assert (HEb : forall e, In e (E 256 rem0) -> e < n) by (intros e He; apply HLb; apply (Permutation_in _ HE0); exact He).
  assert (HInv0 : Inv tlW rem0).
  { intros c e He. unfold rem0 in He. apply filter_In in He as [_ He]. apply Nat.eqb_eq. exact He. }
  assert (HSrt0 : Srt wlt rem0) by (intros c; apply SS_filter; exact HLs).
  assert (HD0 : D tlW hdW (E 256 rem0) s t) by (apply (D_perm tlW hdW (seq 0 n)); [apply Permutation_sym; exact HE0'|exact HD]).
  pose proof (Permutation_length HE0') as HLE. rewrite length_seq in HLE.
  destruct (Hrel_exists 256 tlW hdW tlW_lt n rem0 s HInv0 ltac:(lia)) as (P & rem'' & HH).
  pose proof (Hrel_perm 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0) as HPm.
  pose proof (Permutation_length HPm) as HPl. rewrite length_app in HPl.
  pose proof (Hrel_trail 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 t HD0) as Htr.
  destruct (Hrel_done hdW rem0 s P rem'' HH) as [Hd1 _].
  pose proof (Hrel_mstar hdW s rem0 s P rem'' HH [] [] eq_refl) as HMs. rewrite app_nil_r in HMs.
  assert (HPb : forall e, In e P -> e < n).
  { intros e He. apply HEb. apply (Permutation_in _ (Permutation_sym HPm)). apply in_or_app. left. exact He. }
  assert (HC0 : corr nxt head (PArray.make nI 0%uint63) 0%uint63 0%uint63 (PArray.make nI (PrimString.make 0%uint63 0%uint63)) 0%uint63 rem0 [] []).
  { unfold corr. split; [exact Hhl|]. split; [exact Hch|]. split; [exact HInv0|].
    split; [rewrite alength_make; lia|]. split; [reflexivity|]. split; [intros i Hi; simpl in Hi; lia|].
    split; [rewrite slength_make; lia|]. split; [reflexivity|]. split; [intros i Hi; simpl in Hi; lia|].
    split; [reflexivity|]. split; [simpl; lia|]. split; [exact HEb|]. intros e []. }
  destruct (hier_sim nxt s Hs _ _ _ _ _ _ HMs _ _ _ _ _ _ H HC0)
    as (ptr' & stk' & sp' & q' & res' & cnt' & H' & HC' & Heq).
  pose proof (hier_stop nxt s Hs _ _ _ _ _ _ _ _ H' HC' Hd1) as Hst.
  unfold sI in Heq, Hst. rewrite Heq, Hst.
  destruct HC' as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
  (* a trail of all the words from s is covered by the run *)
  assert (Hcov : forall T y, Permutation (seq 0 n) T -> trail tlW hdW s T y -> List.length P = n).
  { intros T y HT HTr.
    assert (Hi : incl T P).
    { apply (Hrel_covers 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 T s y HTr); [left; reflexivity|].
      intros g Hg. apply (Permutation_in _ (Permutation_sym HE0')). apply (Permutation_in _ (Permutation_sym HT)). exact Hg. }
    pose proof (NoDup_incl_length (Permutation_NoDup HT (seq_NoDup n 0)) Hi) as Hle.
    rewrite <- (Permutation_length HT), length_seq in Hle. lia. }
  destruct (cnt' =? nI)%uint63 eqn:Ecn.
  - apply Uint63.eqb_spec in Ecn. rewrite Ecn, EN in C8.
    assert (HPn : List.length P = n) by lia.
    assert (HR0 : E 256 rem'' = []) by (destruct (E 256 rem''); [reflexivity|simpl in HPl; lia]).
    rewrite HR0, app_nil_r in HPm.
    assert (HPs : Permutation (seq 0 n) P) by (eapply perm_trans; [apply Permutation_sym, HE0'|exact HPm]).
    exists (Some (map word P)). split.
    + split.
      * rewrite length_map, HPn. symmetry. exact C7.
      * intros k Hk. rewrite length_map in Hk. exists (word (nth k P 0)). split.
        -- rewrite nth_error_map, (nth_error_nth' P 0 Hk). reflexivity.
        -- assert (Hres : res'.[ix k] = x.[ix (nth k P 0)]).
           { rewrite HPn in C9. replace k with (n - 1 - (n - 1 - k)) at 1 by lia.
             rewrite C9 by lia. f_equal. f_equal. f_equal. lia. }
           pose proof (x_repr (nth k P 0) (HPb _ (nth_In _ _ Hk))) as Hx. rewrite <- Hres in Hx. exact Hx.
    + split.
      { split.
        - split; [unfold len; rewrite length_map, HPn; lia|].
          intros j Hj. rewrite length_map in Hj.
          rewrite (nth_indep _ EmptyString (word 0)), map_nth by (rewrite length_map; lia).
          rewrite (nth_indep _ EmptyString (word 0)), map_nth by (rewrite length_map; lia).
          apply catenym_iff; [apply HPb, nth_In; lia|apply HPb, nth_In; lia|].
          apply (chain_of_trail _ _ _ Htr). exact Hj.
        - rewrite W_map. apply Permutation_map. apply Permutation_sym. exact HPs. }
      intros c' Hc'. destruct (answer_trail c' Hc') as (T & -> & HT & Hne & y & HTr).
      assert (HTb : forall e, In e T -> e < n) by (intros e He; apply (Permutation_in _ (Permutation_sym HT)), in_seq in He; lia).
      apply lexle_text; [|exact HPb|exact HTb].
      assert (HTnd : NoDup T) by (apply (Permutation_NoDup HT), seq_NoDup).
      assert (HTi : incl T (E 256 rem0)) by (intros g Hg; apply (Permutation_in _ (Permutation_sym HE0')), (Permutation_in _ (Permutation_sym HT)); exact Hg).
      assert (HTl : List.length T = List.length P) by (rewrite <- (Permutation_length HT), length_seq; lia).
      destruct (Nat.eq_dec (tlW (nth 0 T 0)) s) as [Es|Es].
      * rewrite Es in HTr. exact (Hrel_lex 256 tlW hdW tlW_lt wlt rem0 s P rem'' HH HInv0 HSrt0 t HD0 T y HTr HTnd HTi HTl).
      * destruct (Hstart T y HT HTr Hne) as [E1|[Et Es0]]; [contradiction|]. subst t.
        destruct L as [|l0 L']; [apply Permutation_length in HLp; rewrite length_seq in HLp; simpl in HLp; lia|].
        simpl in Es0.
        assert (Hr0 : rem0 s = l0 :: filter (fun e => Nat.eqb (tlW e) s) L')
          by (unfold rem0; simpl; rewrite <- Es0, Nat.eqb_refl; reflexivity).
        destruct (Hrel_circuit 256 tlW hdW tlW_lt rem0 s P rem'' HH HInv0 HD0 _ _ Hr0) as (A & ->).
        destruct T as [|f T']; [congruence|]. simpl in Es.
        apply lexle_head.
        assert (Hf : In f (l0 :: L')) by (apply (Permutation_in _ (Permutation_sym HLp)), (Permutation_in _ (Permutation_sym HT)); left; reflexivity).
        destruct Hf as [<-|Hf]; [rewrite <- Es0 in Es; congruence|].
        apply StronglySorted_inv in HLs as [_ HF]. rewrite Forall_forall in HF. apply HF. exact Hf.
  - exists None. split; [exact I|]. intros (c' & Hc').
    destruct (answer_trail c' Hc') as (T & -> & HT & Hne & y & HTr).
    assert (HPn : List.length P = n).
    { destruct (Nat.eq_dec (tlW (nth 0 T 0)) s) as [Es|Es]; [rewrite Es in HTr; apply (Hcov T y HT HTr)|].
      destruct (Hstart T y HT HTr Hne) as [E1|[Et Es0]]; [contradiction|]. subst t.
      set (s0 := tlW (nth 0 T 0)) in *.
      assert (HDT : D tlW hdW (seq 0 n) s0 y) by (apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)]).
      assert (Hy : y = s0) by (specialize (HDT s0); specialize (HD s0); rewrite HD in HDT; revert HDT; eqbs).
      subst y.
      assert (Hl0 : In (nth 0 L 0) T).
      { apply (Permutation_in _ HT), (Permutation_in _ HLp), nth_In.
        rewrite (Permutation_length HLp), length_seq. lia. }
      apply in_split in Hl0 as (T1 & T3 & ET).
      rewrite ET in HTr. destruct (trail_app_inv tlW hdW _ _ _ _ HTr) as (z & HT1 & HT3).
      apply trail_cons_inv in HT3 as [Hz HT3]. rewrite <- Es0 in Hz. subst z.
      apply (Hcov ((nth 0 L 0 :: T3) ++ T1) s).
      + rewrite ET in HT. eapply perm_trans; [exact HT|]. apply Permutation_app_comm.
      + apply (trail_app tlW hdW _ _ s0); [|exact HT1]. constructor; [symmetry; exact Es0|exact HT3]. }
    assert (cnt' = nI) by (apply to_Z_inj; rewrite C8, EN; lia).
    rewrite H0, Uint63.eqb_refl in Ecn. discriminate.
Qed.


(* ------------------------------------------------------------------ *)
(* the whole program                                                   *)
(* ------------------------------------------------------------------ *)

Lemma answer_D : forall c, is_answer W c -> exists s' t', D tlW hdW (seq 0 n) s' t'.
Proof.
  intros c Hc. destruct (answer_trail c Hc) as (T & _ & HT & _ & y & HTr).
  exists (tlW (nth 0 T 0)), y. apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)].
Qed.

Theorem catenyms_impl_correct : exists o, repr (catenyms_impl x) o /\ catenyms_spec W o.
Proof.
  pose proof n_bounds as NB. pose proof nI_spec as EN.
  unfold catenyms_impl. cbv zeta. fold nI.
  (* the identity permutation *)
  lazymatch goal with |- context [init_loop ?a ?nn ?k ?H] => set (ord0 := init_loop a nn k H) in * end.
  assert (HI : PArray.length ord0 = nI /\ forall j, ((φ j) < (φ nI))%Z -> ord0.[j] = j).
  { unfold ord0. apply init_loop_spec with (z := pgap nI 0); [reflexivity|apply alength_make; lia|change (φ 0) with 0%Z; lia|].
    intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia. }
  destruct HI as [I1 I2].
  (* the sort *)
  lazymatch goal with |- context [msort x ord0 ?t ?lo ?hi ?H] => destruct (msort x ord0 t lo hi H) as [ord tmp] eqn:Ems end.
  destruct (msort_spec x _ 0%uint63 nI ord0 (PArray.make nI 0%uint63) _ ord tmp eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite I1; lia) ltac:(rewrite alength_make, I1 by lia; reflexivity) Ems) as (M1 & M2 & M3 & M4 & M5).
  replace (nt 0%uint63) with 0 in M4, M5 by reflexivity.
  replace (nt nI) with n in M4, M5 by (unfold nt; rewrite EN; lia).
  set (L := map nt (seg ord 0 n)).
  assert (HLn : forall k, k < n -> nth k L 0 = nt ord.[ix k]).
  { intros k Hk. unfold L, seg. rewrite Nat.sub_0_r, map_map. apply nth_map_seq. exact Hk. }
  assert (Hseg0 : seg ord0 0 n = map ix (seq 0 n)).
  { unfold seg. rewrite Nat.sub_0_r. apply map_ext_in. intros k Hk. apply in_seq in Hk.
    apply I2. rewrite EN, ix_spec by lia. lia. }
  assert (HLp : Permutation L (seq 0 n)).
  { unfold L. eapply perm_trans; [apply Permutation_map, M4|]. rewrite Hseg0, map_map.
    rewrite (map_ext_in _ (fun k => k)); [rewrite map_id; apply Permutation_refl|].
    intros k Hk. apply in_seq in Hk. unfold nt. rewrite ix_spec by lia. lia. }
  assert (HLl : List.length L = n) by (rewrite (Permutation_length HLp), length_seq; reflexivity).
  assert (HLnd : NoDup L) by (apply (Permutation_NoDup (Permutation_sym HLp)), seq_NoDup).
  assert (HLb : forall e, In e L -> e < n) by (intros e He; apply (Permutation_in _ HLp), in_seq in He; lia).
  assert (HLo : forall k, k < n -> ord.[ix k] = ix (nth k L 0)) by (intros k Hk; rewrite HLn, ix_nt by exact Hk; reflexivity).
  assert (HLs : StronglySorted wlt L).
  { apply SS_of_nth. intros p q Hpq. rewrite HLl in Hpq.
    pose proof (M5 p q ltac:(lia) ltac:(lia) ltac:(lia)) as Hle. unfold le, cmpw in Hle.
    rewrite !HLo in Hle by lia.
    assert (Hp : nth p L 0 < n) by (apply HLb, nth_In; lia).
    assert (Hq : nth q L 0 < n) by (apply HLb, nth_In; lia).
    unfold wlt. destruct (PrimString.compare x.[ix (nth p L 0)] x.[ix (nth q L 0)]) eqn:Ec;
      [|reflexivity|discriminate].
    exfalso. apply PString.compare_eq in Ec.
    pose proof (x_repr _ Hp) as Rp. rewrite Ec in Rp.
    pose proof (word_inj _ _ Hp Hq (repr_str_inj x.[ix (nth q L 0)] (word (nth p L 0)) (word (nth q L 0)) Rp (x_repr _ Hq))) as E.
    apply (proj1 (NoDup_nth L 0) HLnd p q ltac:(lia) ltac:(lia)) in E. lia. }
  (* the adjacency *)
  lazymatch goal with |- context [build_loop x ord ?nn ?nx ?hd ?k ?H] => destruct (build_loop x ord nn nx hd k H) as [nxt head] eqn:Eb end.
  destruct (build_loop_spec ord L HLl HLnd HLb HLo _ 0%uint63 (PArray.make nI 0%uint63) (PArray.make 256 nI) _ nxt head eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite alength_make; lia) ltac:(rewrite alength_make; reflexivity || lia)
              ltac:(intros c Hc; replace (n - nt 0%uint63) with n by (unfold nt; change (φ 0) with 0%Z; lia);
                    rewrite skipn_all2 by lia; exact (aget_make 256 nI (ix c))) Eb) as (B1 & B2 & B3).
  (* the degrees *)
  lazymatch goal with |- context [deg_loop x ?nn ?o ?i ?k ?H] => destruct (deg_loop x nn o i k H) as [outd ind0] eqn:Ed end.
  destruct (deg_loop_spec _ 0%uint63 (PArray.make 256 0%uint63) (PArray.make 256 0%uint63) _ outd ind0 eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(rewrite alength_make; reflexivity || lia) ltac:(rewrite alength_make; reflexivity || lia)
              ltac:(intros c _; rewrite !aget_make; split; reflexivity) Ed) as (D1 & D2 & D3).
  lazymatch goal with |- context [chk_loop outd ind0 ?c ?p ?m ?v ?b ?H] =>
    destruct (chk_loop outd ind0 c p m v b H) as [[[plus minus] sv] bad] eqn:Ec end.
  destruct (chk_loop_spec outd ind0 D1 D2 D3 _ 0%uint63 0%uint63 0%uint63 0%uint63 false _ plus minus sv bad eq_refl
              ltac:(change (φ 0) with 0%Z; lia) eq_refl eq_refl eq_refl
              ltac:(intros Hq; change (φ 0) with 0%Z in Hq; lia) Ec) as (K1 & K2 & K3 & K4).
  pose proof (filter_length_le isP (seq 0 256)) as LP. rewrite length_seq in LP.
  destruct bad.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (X1 & _ & _). congruence. }
  destruct (negb (plus =? minus)%uint63) eqn:Epm.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (_ & X2 & _).
    apply Bool.negb_true_iff, Uint63.eqb_false_spec in Epm. apply Epm, to_Z_inj. rewrite K1, K2, X2. reflexivity. }
  destruct (negb (plus <=? 1)%uint63) eqn:Ep1.
  { exists None. split; [exact I|]. intros (c & Hc). destruct (answer_D c Hc) as (s' & t' & HD).
    destruct (D_check _ _ HD) as (_ & _ & X3).
    apply Bool.negb_true_iff in Ep1. rewrite <- Bool.not_true_iff_false, leb_spec in Ep1. apply Ep1.
    rewrite K1. change (φ 1) with 1%Z. lia. }
  apply Bool.negb_false_iff, Uint63.eqb_spec in Epm. apply Bool.negb_false_iff in Ep1. rewrite leb_spec in Ep1.
  change (φ 1) with 1%Z in Ep1.
  assert (HPM : List.length (filter isP (seq 0 256)) = List.length (filter isM (seq 0 256))) by (rewrite Epm in K1; lia).
  assert (HL0 : nth 0 L 0 < n) by (apply HLb, nth_In; lia).
  destruct (plus =? 1)%uint63 eqn:Eq1.
  - (* an Euler path : it starts at the letter with one more out-edge *)
    apply Uint63.eqb_spec in Eq1. assert (Hpl : (φ plus) = 1%Z) by (rewrite Eq1; reflexivity).
    destruct (K4 ltac:(lia)) as [Hsv HPs].
    destruct (check_D1 (nt sv) (eq_sym K3) ltac:(lia) ltac:(lia) Hsv HPs) as (t & HD).
    rewrite <- (ix_nt sv).
    apply (main_run L nxt head (nt sv) t HLp HLs Hsv B2 B3 HD).
    intros T y HT HTr Hne. left.
    assert (HDT : D tlW hdW (seq 0 n) (tlW (nth 0 T 0)) y)
      by (apply (D_perm tlW hdW T); [apply Permutation_sym, HT|apply (trail_D _ _ _ _ _ HTr)]).
    unfold isP in HPs. apply Z.eqb_eq in HPs. rewrite dd_dg in HPs.
    rewrite HDT in HPs. revert HPs. eqbs.
  - (* an Euler circuit : it starts with the smallest word *)
    assert (Hp0 : (φ plus) = 0%Z).
    { apply Uint63.eqb_false_spec in Eq1. pose proof (to_Z_bounded plus).
      destruct (Z.eq_dec (φ plus) 1) as [E|E]; [exfalso; apply Eq1, to_Z_inj; exact E|lia]. }
    assert (Hs : fst_ch x.[ord.[0%uint63]] = ix (tlW (nth 0 L 0))).
    { change 0%uint63 with (ix 0). rewrite HLo by lia. apply fst_ch_ix. exact HL0. }
    rewrite Hs.
    pose proof (check_D0 (eq_sym K3) ltac:(lia) ltac:(lia) (tlW (nth 0 L 0))) as HD.
    apply (main_run L nxt head (tlW (nth 0 L 0)) (tlW (nth 0 L 0)) HLp HLs (tlW_lt _) B2 B3 HD).
    intros T y HT HTr Hne. right. split; reflexivity.
Qed.

End Main.

Definition catenyms_correct :
  forall (words : list string) (x : array PrimString.string),
  valid_input words -> repr x words ->
  exists o : option (list string), repr (catenyms x) o /\ catenyms_spec words o
  := fun words x Hv Hr => catenyms_impl_correct words x Hv Hr.
