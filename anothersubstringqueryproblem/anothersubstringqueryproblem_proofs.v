(* Correctness proofs for anothersubstringqueryproblem_implem.v. *)
(* Implementation of anothersubstringqueryproblem
   (anothersubstringqueryproblem.spec).

   Code.  [kth_occurrences x ts ks]:
   1. suffix array of x by prefix doubling ([rounds]): round h sorts the
      identity permutation with a top-down merge sort ([msort]) by the key
      (rank of p, rank of p+h + 1 or 0), then recomputes the ranks from the
      sorted order ([rank_loop]); it stops when 2h >= n or when the ranks
      are pairwise distinct;
   2. a persistent segment tree over the values [0, 2^D) (2^D >= n, D least),
      in three flat arrays (left child, right child, count), node 0 the
      empty tree: version i+1 inserts sa.[i] into version i ([build], [ins]);
   3. per query (t, k): two binary searches ([bs]) over the suffix array for
      the interval [lo, hi) of suffixes that start with t (comparison of t
      with the first |t| characters of a suffix, [cmpt]), then the k-th
      smallest value of versions hi minus lo ([qry]), +1; -1 when
      hi - lo < k.
   Every loop terminates on an erased [Acc (Zwf 0) _] proof; no nat, no Z
   in the code.  See README.md, "Implementation". *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString Sint63.
Import ListNotations.

Open Scope Z_scope.

Unset Lia Cache.

Require Export anothersubstringqueryproblem_implem.
Open Scope Z_scope.


(* ================================================================== *)
(* Lexicographic comparison of lists of codes                          *)
(* ================================================================== *)

Fixpoint lexcmp (a b : list Z) : comparison :=
  match a, b with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: a', y :: b' =>
      match Z.compare x y with Eq => lexcmp a' b' | c => c end
  end.

Definition lexle (a b : list Z) : Prop := lexcmp a b <> Gt.

Lemma lexcmp_refl : forall a, lexcmp a a = Eq.
Proof. induction a as [|x a IH]; simpl; [reflexivity|]. rewrite Z.compare_refl. exact IH. Qed.

Lemma lexcmp_eq : forall a b, lexcmp a b = Eq -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; try discriminate; auto.
  destruct (Z.compare_spec x y); try discriminate. intros H'. subst. f_equal. auto.
Qed.

Lemma lexcmp_opp : forall a b, lexcmp b a = CompOpp (lexcmp a b).
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; auto.
  rewrite (Z.compare_antisym x y). destruct (x ?= y); simpl; auto.
Qed.

Lemma lexle_refl : forall a, lexle a a.
Proof. intros a. unfold lexle. rewrite lexcmp_refl. discriminate. Qed.

Lemma lexle_trans : forall a b c, lexle a b -> lexle b c -> lexle a c.
Proof.
  unfold lexle. induction a as [|x a IH]; intros [|y b] [|z c]; simpl;
    try congruence;
    destruct (Z.compare_spec x y), (Z.compare_spec y z), (Z.compare_spec x z);
    try congruence; try lia; subst; eauto.
Qed.

Lemma lexle_total : forall a b, lexle a b \/ lexle b a.
Proof.
  intros a b. unfold lexle. rewrite (lexcmp_opp a b).
  destruct (lexcmp a b); simpl; [left|left|right]; congruence.
Qed.

Lemma lexle_antisym : forall a b, lexle a b -> lexle b a -> a = b.
Proof.
  unfold lexle. intros a b H1 H2. rewrite (lexcmp_opp a b) in H2.
  apply lexcmp_eq. destruct (lexcmp a b); simpl in *; congruence.
Qed.

Lemma lexcmp_lt_iff : forall a b, lexcmp a b = Lt <-> ~ lexle b a.
Proof.
  unfold lexle. intros a b. rewrite (lexcmp_opp a b).
  destruct (lexcmp a b); simpl; split; intros H; try discriminate;
    try reflexivity; try (intros H'; apply H'; reflexivity);
    exfalso; apply H; discriminate.
Qed.

Lemma lexcmp_firstn : forall m a b,
  lexcmp (firstn m a) (firstn m b) <> Eq ->
  lexcmp (firstn m a) (firstn m b) = lexcmp a b.
Proof.
  induction m as [|m IH]; intros a b H; simpl in *; [congruence|].
  destruct a as [|x a], b as [|y b]; simpl in *; try congruence.
  destruct (x ?= y); auto.
Qed.

Lemma lexle_firstn : forall m a b, lexle a b -> lexle (firstn m a) (firstn m b).
Proof.
  unfold lexle. intros m a b H.
  intros E. rewrite lexcmp_firstn in E by congruence. exact (H E).
Qed.

Lemma lexcmp_app : forall a1 b1 a2 b2,
  ((List.length a1 < List.length b1)%nat -> a2 = []) ->
  ((List.length b1 < List.length a1)%nat -> b2 = []) ->
  lexcmp (a1 ++ a2) (b1 ++ b2) =
  match lexcmp a1 b1 with Eq => lexcmp a2 b2 | c => c end.
Proof.
  induction a1 as [|x a1 IH]; intros [|y b1] a2 b2 H1 H2; simpl in *.
  - reflexivity.
  - rewrite H1 by lia. reflexivity.
  - rewrite H2 by lia. destruct a1, a2; reflexivity.
  - destruct (x ?= y); auto. apply IH; intros; [apply H1 | apply H2]; lia.
Qed.

Lemma firstn_add : forall (a b : nat) (l : list Z),
  firstn (a + b) l = firstn a l ++ firstn b (skipn a l).
Proof.
  induction a as [|a IH]; intros b l; simpl; [reflexivity|].
  destruct l as [|x l]; simpl; [destruct b; reflexivity|]. f_equal. apply IH.
Qed.

(* ================================================================== *)
(* Strings as lists of codes                                           *)
(* ================================================================== *)

Definition code (c : ascii) : Z := Z.of_N (N_of_ascii c).
Definition codes (s : string) : list Z := map code (list_ascii_of_string s).

Lemma length_codes : forall s, List.length (codes s) = String.length s.
Proof. induction s as [|c s IH]; simpl; auto. Qed.

Lemma get_codes : forall s k, String.get k s = nth_error (list_ascii_of_string s) k.
Proof. induction s as [|c s IH]; intros [|k]; simpl; auto. Qed.

Lemma codes_substring : forall s p m,
  codes (substring p m s) = firstn m (skipn p (codes s)).
Proof.
  induction s as [|c s IH]; intros [|p] [|m]; unfold codes in *; simpl; auto;
    try (destruct m; reflexivity); rewrite IH; reflexivity.
Qed.

Lemma code_inj : forall c d, code c = code d -> c = d.
Proof.
  intros c d H. unfold code in H. apply N2Z.inj in H.
  rewrite <- (ascii_N_embedding c), <- (ascii_N_embedding d), H. reflexivity.
Qed.

Lemma codes_inj : forall a b, codes a = codes b -> a = b.
Proof.
  induction a as [|c a IH]; intros [|d b]; simpl; try discriminate; auto.
  intros H. injection H as H1 H2. f_equal; [apply code_inj | apply IH]; auto.
Qed.

Lemma starts_at_iff : forall s t p, (0 < String.length t)%nat ->
  starts_at s t p = true <->
  firstn (String.length t) (skipn p (codes s)) = codes t.
Proof.
  intros s t p Ht. unfold starts_at. rewrite Bool.andb_true_iff, Nat.leb_le, String.eqb_eq.
  split.
  - intros [_ H]. rewrite <- codes_substring, H. reflexivity.
  - intros H. split.
    + assert (E := f_equal (@List.length Z) H).
      rewrite length_firstn, length_skipn, !length_codes in E. lia.
    + apply codes_inj. rewrite codes_substring. exact H.
Qed.

Lemma skipn_cons_nth : forall (l : list Z) k, (k < List.length l)%nat ->
  skipn k l = nth k l 0 :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros [|k] Hk; simpl in *; try lia; auto.
  apply IH. lia.
Qed.

(* ================================================================== *)
(* Uint63 / PArray plumbing                                            *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

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

Lemma alength_make : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H. assert (E := length_make int n b).
  replace (n <=? PArray.max_length) with true in E; [exact E|].
  symmetry. rewrite leb_spec, max_length_val. exact H.
Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma aget_set : forall (t : array int) (i j : int) (b : int),
  (i <? PArray.length t) = true ->
  t.[i <- b].[j] = if i =? j then b else t.[j].
Proof.
  intros t i j b H. destruct (i =? j) eqn:E.
  - rewrite Uint63.eqb_spec in E. subst. apply aget_set_same. exact H.
  - rewrite Uint63.eqb_false_spec in E. apply aget_set_other. exact E.
Qed.

(* ================================================================== *)
(* Reading the strings                                                 *)
(* ================================================================== *)

Lemma repr_str_len : forall (x : PrimString.string) (s : string), repr x s ->
  (φ (PrimString.length x)) = Z.of_nat (String.length s).
Proof. intros x s [H _]. symmetry. exact H. Qed.

Lemma repr_str_get : forall (x : PrimString.string) (s : string), repr x s ->
  forall i : int, ((φ i) < Z.of_nat (String.length s))%Z ->
  (φ (PrimString.get x i)) = nth (Z.to_nat (φ i)) (codes s) 0%Z.
Proof.
  intros x s [_ Hc] i Hi.
  pose proof (to_Z_bounded i) as Bi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (c & Hg & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  rewrite get_codes in Hg.
  assert (E : nth_error (codes s) (Z.to_nat (φ i)) = Some (code c))
    by (unfold codes; rewrite nth_error_map, Hg; reflexivity).
  rewrite (nth_error_nth _ _ _ E). unfold code. rewrite <- Hr.
  pose proof (to_Z_bounded (PrimString.get x i)). lia.
Qed.

Lemma codes_bound : forall s k, (0 <= nth k (codes s) 0 < 256)%Z.
Proof.
  intros s k. unfold codes. destruct (Nat.lt_ge_cases k (List.length (list_ascii_of_string s))).
  - rewrite (nth_indep _ _ (code "000"%char)) by (rewrite length_map; lia).
    rewrite map_nth. unfold code. pose proof (N_ascii_bounded (nth k (list_ascii_of_string s) "000"%char)). lia.
  - rewrite nth_overflow by (rewrite length_map; lia). lia.
Qed.

Lemma cmpt_eq : forall x t n m p k H,
  cmpt x t n m p k H =
  match bdec (k <? m) with
  | left Hk =>
      if p + k <? n then
        let a := PrimString.get t k in
        let b := PrimString.get x (p + k) in
        if a <? b then Lt
        else if b <? a then Gt
        else cmpt x t n m p (k + 1) (Acc_inv H (dec_step m k Hk))
      else Gt
  | right _ => Eq
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma cmpt_spec : forall (x t : PrimString.string) (s tt : string),
  repr x s -> repr t tt ->
  forall n m p : int,
  (φ n) = Z.of_nat (String.length s) -> (φ m) = Z.of_nat (String.length tt) ->
  ((φ n) <= 1000000)%Z -> ((φ m) <= 1000000)%Z -> ((φ p) <= (φ n))%Z ->
  forall (z : Z) (k : int) (H : Acc (Zwf 0) (gap m k)),
  gap m k = z -> ((φ k) <= (φ m))%Z ->
  cmpt x t n m p k H =
  lexcmp (skipn (Z.to_nat (φ k)) (codes tt))
         (firstn (Z.to_nat ((φ m) - (φ k))) (skipn (Z.to_nat ((φ p) + (φ k))) (codes s))).
Proof.
  intros x t s tt Hx Ht n m p Hn Hm Bn Bm Hp z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k H Hz Hk. rewrite cmpt_eq.
  pose proof (to_Z_bounded k) as Bk. pose proof (to_Z_bounded p) as Bp.
  destruct (bdec (k <? m)) as [Hkm | Hkm].
  - pose proof Hkm as Hkm'. rewrite ltb_spec in Hkm'.
    assert (Hpk : (φ (p + k)) = ((φ p) + (φ k))%Z) by sia.
    rewrite (skipn_cons_nth (codes tt)) by (rewrite length_codes; lia).
    replace (Z.to_nat ((φ m) - (φ k))) with (S (Z.to_nat ((φ m) - ((φ k) + 1)))) by lia.
    destruct (p + k <? n) eqn:E.
    + rewrite ltb_spec, Hpk in E.
      rewrite (skipn_cons_nth (codes s)) by (rewrite length_codes; lia).
      simpl firstn. cbn [lexcmp].
      assert (Ha : (φ (PrimString.get t k)) = nth (Z.to_nat (φ k)) (codes tt) 0%Z)
        by (apply repr_str_get; [exact Ht | lia]).
      assert (Hb : (φ (PrimString.get x (p + k))) = nth (Z.to_nat ((φ p) + (φ k))) (codes s) 0%Z)
        by (rewrite <- Hpk; rewrite (repr_str_get x s Hx) by lia; rewrite Hpk; reflexivity).
      cbv zeta.
      destruct (PrimString.get t k <? PrimString.get x (p + k)) eqn:E1.
      * rewrite ltb_spec, Ha, Hb in E1. rewrite (proj2 (Z.compare_lt_iff _ _) E1). reflexivity.
      * rewrite <- Bool.not_true_iff_false, ltb_spec, Ha, Hb in E1.
        destruct (PrimString.get x (p + k) <? PrimString.get t k) eqn:E2.
        -- rewrite ltb_spec, Ha, Hb in E2. rewrite (proj2 (Z.compare_gt_iff _ _) E2). reflexivity.
        -- rewrite <- Bool.not_true_iff_false, ltb_spec, Ha, Hb in E2.
           replace (nth (Z.to_nat (φ k)) (codes tt) 0%Z ?= nth (Z.to_nat ((φ p) + (φ k))) (codes s) 0%Z)%Z
             with Eq by (symmetry; apply Z.compare_eq_iff; lia).
           assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
           rewrite (IH (gap m (k + 1))); [ | rewrite <- Hz; apply dec_step; exact Hkm | reflexivity | lia].
           rewrite Hk1.
           replace (Z.to_nat ((φ k) + 1)) with (S (Z.to_nat (φ k))) by lia.
           replace (Z.to_nat ((φ p) + ((φ k) + 1))) with (S (Z.to_nat ((φ p) + (φ k)))) by lia.
           reflexivity.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, Hpk in E.
      rewrite (skipn_all2 (codes s)) by (rewrite length_codes; lia).
      destruct (Z.to_nat ((φ m) - ((φ k) + 1))); reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkm.
    replace (Z.to_nat ((φ m) - (φ k))) with O by lia.
    rewrite (skipn_all2 (codes tt)) by (rewrite length_codes; lia). reflexivity.
Qed.

Lemma copy_eq : forall a b hi k H,
  copy a b hi k H =
  match bdec (k <? hi) with
  | left Hk => copy a b.[k <- a.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => b
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma merge_eq : forall le src dst mid hi i j k H,
  merge le src dst mid hi i j k H =
  match bdec (k <? hi) with
  | left Hk =>
      if ((i <? mid) && ((hi <=? j) || le src.[i] src.[j]))%bool then
        merge le src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1)
          (Acc_inv H (dec_step hi k Hk))
      else
        merge le src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma msort_eq : forall le a b lo hi H,
  msort le a b lo hi H =
  match bdec ((lo <? hi) && (1 <? hi - lo))%bool with
  | left C =>
      let mid := midp lo hi in
      let (a1, b1) := msort le a b lo mid (Acc_inv H (dec_ml lo hi C)) in
      let (a2, b2) := msort le a1 b1 mid hi (Acc_inv H (dec_mr lo hi C)) in
      let b3 := copy a2 b2 hi lo (Zwf_well_founded 0 (gap hi lo)) in
      (merge le b3 a2 mid hi lo mid lo (Zwf_well_founded 0 (gap hi lo)), b3)
  | right _ => (a, b)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* --- counting the occurrences of a value in a segment --- *)

Fixpoint cnt (a : array int) (v : int) (lo : Z) (len : nat) : Z :=
  match len with
  | O => 0%Z
  | S l => (cnt a v lo l + (if Uint63.eqb a.[of_Z (lo + Z.of_nat l)] v then 1 else 0))%Z
  end.

Lemma idx_of : forall lo k : int, ((φ lo) <= (φ k))%Z ->
  of_Z ((φ lo) + Z.of_nat (Z.to_nat ((φ k) - (φ lo)))) = k.
Proof.
  intros lo k H. rewrite Z2Nat.id by lia.
  replace ((φ lo) + ((φ k) - (φ lo)))%Z with (φ k) by lia. apply of_to_Z.
Qed.

Lemma phi_of_Z : forall z : Z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. exact H. Qed.

Lemma cnt_ext : forall a b v (lo : int) len,
  ((φ lo) + Z.of_nat len <= 4194303)%Z ->
  (forall y : int, ((φ lo) <= (φ y) < (φ lo) + Z.of_nat len)%Z -> a.[y] = b.[y]) ->
  cnt a v (φ lo) len = cnt b v (φ lo) len.
Proof.
  intros a b v lo len. induction len as [|l IH]; intros Hb Hy; simpl; [reflexivity|].
  pose proof (to_Z_bounded lo).
  rewrite IH by (intros; try apply Hy; lia).
  rewrite Hy; [reflexivity|]. rewrite phi_of_Z by (rewrite wB_val; lia). lia.
Qed.

Lemma cnt_split : forall a v lo l1 l2,
  cnt a v lo (l1 + l2) = (cnt a v lo l1 + cnt a v (lo + Z.of_nat l1) l2)%Z.
Proof.
  intros a v lo l1 l2. induction l2 as [|l2 IH]; simpl.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. simpl. rewrite IH.
    replace (lo + Z.of_nat (l1 + l2))%Z with (lo + Z.of_nat l1 + Z.of_nat l2)%Z by lia. lia.
Qed.

Lemma cnt_snoc : forall a v (lo k : int), ((φ lo) <= (φ k))%Z ->
  cnt a v (φ lo) (S (Z.to_nat ((φ k) - (φ lo)))) =
  (cnt a v (φ lo) (Z.to_nat ((φ k) - (φ lo))) + (if Uint63.eqb a.[k] v then 1 else 0))%Z.
Proof. intros a v lo k H. simpl. rewrite idx_of by exact H. reflexivity. Qed.

Lemma cnt_nonneg : forall a v lo len, (0 <= cnt a v lo len)%Z.
Proof.
  intros a v lo len. induction len; simpl; [lia|]. destruct (Uint63.eqb _ v); lia.
Qed.

Lemma cnt_le : forall a v lo len, (cnt a v lo len <= Z.of_nat len)%Z.
Proof.
  intros a v lo len. induction len; simpl; [lia|]. destruct (Uint63.eqb _ v); lia.
Qed.

Lemma succ_phi : forall k m : int, ((φ k) < (φ m))%Z -> (φ (k + 1)) = ((φ k) + 1)%Z.
Proof. intros k m H. pose proof (to_Z_bounded m). sia. Qed.

Lemma add1_sub1 : forall k : int, k + 1 - 1 = k.
Proof. intros k. apply to_Z_inj. pose proof (to_Z_bounded k). sia. Qed.

Definition sorted (le : int -> int -> bool) (a : array int) (lo hi : int) : Prop :=
  forall i : int, ((φ lo) <= (φ i))%Z -> ((φ i) + 1 < (φ hi))%Z -> le a.[i] a.[i + 1] = true.

Section Sorting.
  Variable le : int -> int -> bool.
  Hypothesis le_total : forall x y, le x y = true \/ le y x = true.
  Hypothesis le_trans : forall x y z, le x y = true -> le y z = true -> le x z = true.

  Lemma copy_spec : forall a hi z k b H, gap hi k = z ->
    ((φ hi) <= (φ (PArray.length b)))%Z ->
    PArray.length (copy a b hi k H) = PArray.length b /\
    (forall y : int, ((φ k) <= (φ y) < (φ hi))%Z -> (copy a b hi k H).[y] = a.[y]) /\
    (forall y : int, ~ ((φ k) <= (φ y) < (φ hi))%Z -> (copy a b hi k H).[y] = b.[y]).
  Proof.
    intros a hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros k b H Hz Hb. rewrite copy_eq.
    destruct (bdec (k <? hi)) as [Hk | Hk].
    - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
      assert (Hk1 := succ_phi k hi Hk').
      assert (Hkb : (k <? PArray.length b) = true) by (rewrite ltb_spec; lia).
      destruct (IH (gap hi (k + 1))) with (k := k + 1) (b := b.[k <- a.[k]])
        (H := Acc_inv H (dec_step hi k Hk)) as (L1 & E1 & E2);
        [ rewrite <- Hz; apply dec_step; exact Hk | reflexivity
        | rewrite alength_set; exact Hb | ].
      rewrite alength_set in L1. split; [exact L1|]. split.
      + intros y Hy. destruct (Z.eq_dec (φ y) (φ k)) as [E | E].
        * apply to_Z_inj in E. subst y. rewrite E2 by lia. apply aget_set_same. exact Hkb.
        * apply E1. lia.
      + intros y Hy. rewrite E2 by lia. apply aget_set_other.
        intros F. subst. lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
      split; [reflexivity|]. split; [intros y Hy; lia | reflexivity].
  Qed.

  Lemma push_sorted : forall dst lo k e,
    ((φ lo) <= (φ k))%Z -> ((φ k) < (φ (PArray.length dst)))%Z ->
    sorted le dst lo k ->
    (((φ lo) < (φ k))%Z -> le dst.[k - 1] e = true) ->
    sorted le dst.[k <- e] lo (k + 1).
  Proof.
    intros dst lo k e H1 H2 Hs Hl i Hi1 Hi2.
    pose proof (to_Z_bounded (PArray.length dst)).
    rewrite (succ_phi k (PArray.length dst) H2) in Hi2.
    assert (Hkb : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
    assert (Hi1' := succ_phi i k ltac:(lia)).
    destruct (Z.eq_dec ((φ i) + 1) (φ k)) as [E | E].
    - assert (Ei : i + 1 = k) by (apply to_Z_inj; lia). rewrite Ei.
      rewrite aget_set_same by exact Hkb.
      rewrite aget_set_other by (intro F; subst; lia).
      assert (Ei' : i = k - 1) by (rewrite <- Ei, add1_sub1; reflexivity).
      rewrite Ei'. apply Hl. lia.
    - rewrite !aget_set_other by (intro F; subst; lia). apply Hs; lia.
  Qed.

  Definition merge_post (src dst : array int) (lo mid hi k : int) (r : array int) : Prop :=
    PArray.length r = PArray.length dst /\
    (forall y : int, ((φ y) < (φ k) \/ (φ hi) <= (φ y))%Z -> r.[y] = dst.[y]) /\
    sorted le r lo hi /\
    (forall v, cnt r v (φ lo) (Z.to_nat ((φ hi) - (φ lo))) =
       (cnt src v (φ lo) (Z.to_nat ((φ mid) - (φ lo))) +
        cnt src v (φ mid) (Z.to_nat ((φ hi) - (φ mid))))%Z).

  Lemma merge_spec : forall src lo mid hi,
    ((φ lo) <= (φ mid))%Z -> ((φ mid) <= (φ hi))%Z -> ((φ hi) <= 4194303)%Z ->
    sorted le src lo mid -> sorted le src mid hi ->
    forall z i j k dst H, gap hi k = z ->
    ((φ hi) <= (φ (PArray.length dst)))%Z ->
    ((φ lo) <= (φ i) <= (φ mid))%Z -> ((φ mid) <= (φ j) <= (φ hi))%Z ->
    (φ k) = ((φ i) + (φ j) - (φ mid))%Z ->
    sorted le dst lo k ->
    (((φ lo) < (φ k))%Z ->
       (((φ i) < (φ mid))%Z -> le dst.[k - 1] src.[i] = true) /\
       (((φ j) < (φ hi))%Z -> le dst.[k - 1] src.[j] = true)) ->
    (forall v, cnt dst v (φ lo) (Z.to_nat ((φ k) - (φ lo))) =
       (cnt src v (φ lo) (Z.to_nat ((φ i) - (φ lo))) +
        cnt src v (φ mid) (Z.to_nat ((φ j) - (φ mid))))%Z) ->
    merge_post src dst lo mid hi k (merge le src dst mid hi i j k H).
  Proof.
    intros src lo mid hi Hlm Hmh Hhb Ss1 Ss2 z.
    induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i j k dst H Hz Hdl Hi Hj Hk Sd Hlast Hc.
    rewrite merge_eq.
    destruct (bdec (k <? hi)) as [Hkh | Hkh].
    - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
      assert (Hk1 := succ_phi k hi Hkh').
      assert (Hkb : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
      assert (Hdec : Zwf 0 (gap hi (k + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hkh).
      assert (Hcell : forall e y, ((φ y) < (φ k))%Z -> dst.[k <- e].[y] = dst.[y])
        by (intros e y Hy; apply aget_set_other; intro F; subst; lia).
      assert (Hcnt : forall e v, cnt dst.[k <- e] v (φ lo) (Z.to_nat ((φ (k + 1)) - (φ lo))) =
                 (cnt dst v (φ lo) (Z.to_nat ((φ k) - (φ lo))) + (if Uint63.eqb e v then 1 else 0))%Z).
      { intros e v. rewrite Hk1.
        replace (Z.to_nat ((φ k) + 1 - (φ lo))) with (S (Z.to_nat ((φ k) - (φ lo)))) by lia.
        rewrite cnt_snoc by lia. rewrite aget_set_same by exact Hkb.
        f_equal. apply cnt_ext; [rewrite Z2Nat.id; lia|].
        intros y Hy. rewrite Z2Nat.id in Hy by lia. apply Hcell. lia. }
      destruct ((i <? mid) && ((hi <=? j) || le src.[i] src.[j]))%bool eqn:Ec.
      + apply andb_prop in Ec. destruct Ec as [Ei Ec]. rewrite ltb_spec in Ei.
        assert (Hi1 := succ_phi i mid Ei).
        assert (Hp : merge_post src dst.[k <- src.[i]] lo mid hi (k + 1)
                   (merge le src dst.[k <- src.[i]] mid hi (i + 1) j (k + 1)
                      (Acc_inv H (dec_step hi k Hkh)))).
        { apply (IH (gap hi (k + 1)) Hdec); auto.
          - rewrite alength_set. exact Hdl.
          - lia.
          - lia.
          - apply push_sorted; try lia; auto; intros Hlk; apply (proj1 (Hlast Hlk)); lia.
          - intros _. rewrite add1_sub1, aget_set_same by exact Hkb. split.
            + intros Hi'. apply Ss1; lia.
            + intros Hj'. apply Bool.orb_prop in Ec. destruct Ec as [Ec | Ec]; [|exact Ec].
              rewrite leb_spec in Ec. lia.
          - intros v. rewrite Hcnt, Hc, Hi1.
            replace (Z.to_nat ((φ i) + 1 - (φ lo))) with (S (Z.to_nat ((φ i) - (φ lo)))) by lia.
            rewrite (cnt_snoc src v lo i) by lia. lia. }
        destruct Hp as (P1 & P2 & P3 & P4).
        split; [rewrite P1, alength_set; reflexivity|]. split; [|split; assumption].
        intros y Hy. rewrite P2 by lia. apply aget_set_other. intro F; subst; lia.
      + assert (Ej : ((φ j) < (φ hi))%Z).
        { destruct (Z.lt_ge_cases (φ j) (φ hi)) as [E|E]; [exact E|].
          exfalso. assert (Ei : ((φ i) < (φ mid))%Z) by lia.
          rewrite <- ltb_spec in Ei. rewrite <- leb_spec in E. rewrite Ei, E in Ec. discriminate. }
        assert (Hj1 := succ_phi j hi Ej).
        assert (Hle : ((φ i) < (φ mid))%Z -> le src.[j] src.[i] = true).
        { intros Ei. rewrite <- ltb_spec in Ei. rewrite Ei in Ec.
          assert (E : (hi <=? j) = false) by (apply Bool.not_true_iff_false; rewrite leb_spec; lia).
          rewrite E in Ec. simpl in Ec.
          destruct (le_total src.[i] src.[j]) as [T|T]; [congruence | exact T]. }
        assert (Hp : merge_post src dst.[k <- src.[j]] lo mid hi (k + 1)
                   (merge le src dst.[k <- src.[j]] mid hi i (j + 1) (k + 1)
                      (Acc_inv H (dec_step hi k Hkh)))).
        { apply (IH (gap hi (k + 1)) Hdec); auto.
          - rewrite alength_set. exact Hdl.
          - lia.
          - lia.
          - apply push_sorted; try lia; auto; intros Hlk; apply (proj2 (Hlast Hlk)); lia.
          - intros _. rewrite add1_sub1, aget_set_same by exact Hkb. split.
            + exact Hle.
            + intros Hj'. apply Ss2; lia.
          - intros v. rewrite Hcnt, Hc, Hj1.
            replace (Z.to_nat ((φ j) + 1 - (φ mid))) with (S (Z.to_nat ((φ j) - (φ mid)))) by lia.
            rewrite (cnt_snoc src v mid j) by lia. lia. }
        destruct Hp as (P1 & P2 & P3 & P4).
        split; [rewrite P1, alength_set; reflexivity|]. split; [|split; assumption].
        intros y Hy. rewrite P2 by lia. apply aget_set_other. intro F; subst; lia.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
      assert ((φ i) = (φ mid) /\ (φ j) = (φ hi))%Z as [E1 E2] by lia.
      split; [reflexivity|]. split; [reflexivity|]. split.
      + intros y Hy1 Hy2. apply Sd; lia.
      + intros v. replace (Z.to_nat ((φ hi) - (φ lo))) with (Z.to_nat ((φ k) - (φ lo))) by lia.
        rewrite Hc, E1, E2. reflexivity.
  Qed.

  Definition msort_post (a : array int) (lo hi : int) (r : array int * array int) : Prop :=
    PArray.length (fst r) = PArray.length a /\
    (forall y : int, ((φ y) < (φ lo) \/ (φ hi) <= (φ y))%Z -> (fst r).[y] = a.[y]) /\
    sorted le (fst r) lo hi /\
    (forall v, cnt (fst r) v (φ lo) (Z.to_nat ((φ hi) - (φ lo))) =
               cnt a v (φ lo) (Z.to_nat ((φ hi) - (φ lo)))).

  Lemma msort_spec : forall z lo hi a b H, gap hi lo = z ->
    ((φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ (PArray.length a)))%Z ->
    PArray.length b = PArray.length a ->
    PArray.length (snd (msort le a b lo hi H)) = PArray.length a /\
    msort_post a lo hi (msort le a b lo hi H).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros lo hi a b H Hz Hlh Hha Hb.
    pose proof (alength_bound a) as Ba.
    rewrite msort_eq.
    destruct (bdec ((lo <? hi) && (1 <? hi - lo))%bool) as [C | C].
    - pose proof C as C'. apply andb_prop in C'. destruct C' as [C1 C2].
      rewrite ltb_spec in C1. rewrite ltb_spec in C2.
      assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia. rewrite E in C2. change (φ 1) with 1%Z in C2.
      pose proof (midp_spec lo hi C1) as Hm.
      assert (0 < ((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z
        by (split; [apply Z.div_str_pos | apply Z.div_lt]; lia).
      cbv zeta.
      destruct (IH (gap (midp lo hi) lo)) with (lo := lo) (hi := midp lo hi) (a := a) (b := b)
        (H := Acc_inv H (dec_ml lo hi C)) as [Lb1 (La1 & Fa1 & Sa1 & Ca1)];
        [rewrite <- Hz; apply dec_ml; exact C | reflexivity | lia | lia | exact Hb | ].
      destruct (msort le a b lo (midp lo hi) (Acc_inv H (dec_ml lo hi C))) as [a1 b1] eqn:E1.
      simpl in La1, Fa1, Sa1, Ca1, Lb1.
      destruct (IH (gap hi (midp lo hi))) with (lo := midp lo hi) (hi := hi) (a := a1) (b := b1)
        (H := Acc_inv H (dec_mr lo hi C)) as [Lb2 (La2 & Fa2 & Sa2 & Ca2)];
        [rewrite <- Hz; apply dec_mr; exact C | reflexivity | lia | lia | congruence | ].
      destruct (msort le a1 b1 (midp lo hi) hi (Acc_inv H (dec_mr lo hi C))) as [a2 b2] eqn:E2.
      simpl in La2, Fa2, Sa2, Ca2, Lb2.
      destruct (copy_spec a2 hi (gap hi lo) lo b2 (Zwf_well_founded 0 (gap hi lo)) eq_refl
                  ltac:(lia)) as (Lb3 & Cb3 & Ob3).
      set (b3 := copy a2 b2 hi lo (Zwf_well_founded 0 (gap hi lo))) in *.
      (* a2 on [lo, mid) is a1 *)
      assert (A21 : forall y : int, ((φ y) < (φ (midp lo hi)))%Z -> a2.[y] = a1.[y])
        by (intros y Hy; apply Fa2; lia).
      assert (Hsrc1 : sorted le b3 lo (midp lo hi)).
      { intros i Hi1 Hi2. assert (Hi := succ_phi i (midp lo hi) ltac:(lia)).
        rewrite !Cb3 by lia. rewrite !A21 by lia. apply Sa1; lia. }
      assert (Hsrc2 : sorted le b3 (midp lo hi) hi).
      { intros i Hi1 Hi2. assert (Hi := succ_phi i hi ltac:(lia)).
        rewrite !Cb3 by lia. apply Sa2; lia. }
      destruct (merge_spec b3 lo (midp lo hi) hi ltac:(lia) ltac:(lia) ltac:(lia) Hsrc1 Hsrc2
                  (gap hi lo) lo (midp lo hi) lo a2 (Zwf_well_founded 0 (gap hi lo)) eq_refl
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(intros i Hi1 Hi2; lia) ltac:(intros Hl; lia)
                  ltac:(intros v; replace (Z.to_nat ((φ lo) - (φ lo))) with O by lia;
                        replace (Z.to_nat ((φ (midp lo hi)) - (φ (midp lo hi)))) with O by lia;
                        reflexivity))
        as (Lr & Fr & Sr & Cr).
      simpl. split; [rewrite Lb3, Lb2; exact La1|].
      unfold msort_post; simpl.
      split; [rewrite Lr, La2; exact La1|]. split.
      + intros y Hy. rewrite Fr by lia. rewrite Fa2 by lia. apply Fa1. lia.
      + split; [exact Sr|].
        intros v. rewrite Cr.
        rewrite (cnt_ext b3 a2) by (try (rewrite Z2Nat.id; lia); intros y Hy;
                                    rewrite Z2Nat.id in Hy by lia; apply Cb3; lia).
        rewrite (cnt_ext b3 a2) by (try (rewrite Z2Nat.id; lia); intros y Hy;
                                    rewrite Z2Nat.id in Hy by lia; apply Cb3; lia).
        rewrite Ca2.
        rewrite (cnt_ext a2 a1) by (try (rewrite Z2Nat.id; lia); intros y Hy;
                                    rewrite Z2Nat.id in Hy by lia; apply A21; lia).
        rewrite Ca1.
        rewrite (cnt_ext a1 a v (midp lo hi)) by (try (rewrite Z2Nat.id; lia); intros y Hy;
                                    rewrite Z2Nat.id in Hy by lia; apply Fa1; lia).
        replace (Z.to_nat ((φ hi) - (φ lo))) with
          (Z.to_nat ((φ (midp lo hi)) - (φ lo)) + Z.to_nat ((φ hi) - (φ (midp lo hi))))%nat by lia.
        rewrite cnt_split. f_equal. f_equal. rewrite Z2Nat.id by lia. lia.
    - unfold msort_post; simpl. split; [exact Hb|]. split; [reflexivity|].
      split; [intros y Hy; reflexivity|]. split; [|intros v; reflexivity].
      intros i Hi1 Hi2. exfalso.
      assert (Hlt : ((φ lo) < (φ hi))%Z) by lia.
      assert (E : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by sia.
      rewrite <- ltb_spec in Hlt. rewrite Hlt in C. simpl in C.
      rewrite <- Bool.not_true_iff_false, ltb_spec, E in C. change (φ 1) with 1%Z in C. lia.
  Qed.

  Lemma sorted_all : forall a lo hi, sorted le a lo hi ->
    forall i j : int, ((φ lo) <= (φ i))%Z -> ((φ i) <= (φ j))%Z -> ((φ j) < (φ hi))%Z ->
    le a.[i] a.[j] = true.
  Proof.
    intros a lo hi Hs i j Hi Hij Hj.
    remember (Z.to_nat ((φ j) - (φ i))) as d eqn:Ed. revert j Hij Hj Ed.
    induction d as [|d IH]; intros j Hij Hj Ed.
    - assert (i = j) by (apply to_Z_inj; lia). subst.
      destruct (le_total a.[j] a.[j]); assumption.
    - assert (Hj1 : (φ (j - 1)) = ((φ j) - 1)%Z) by sia.
      apply le_trans with (a.[j - 1]).
      + apply IH; lia.
      + assert (E : j - 1 + 1 = j) by (apply to_Z_inj; sia).
        pose proof (Hs (j - 1) ltac:(lia) ltac:(lia)) as T. rewrite E in T. exact T.
  Qed.
End Sorting.

(* ================================================================== *)
(* Permutations of [0, n), read through cnt                            *)
(* ================================================================== *)

Definition at_ (a : array int) (j : nat) : int := a.[of_Z (Z.of_nat j)].

Lemma at_idx : forall (a : array int) (i : int), at_ a (Z.to_nat (φ i)) = a.[i].
Proof.
  intros a i. unfold at_. pose proof (to_Z_bounded i). rewrite Z2Nat.id by lia.
  rewrite of_to_Z. reflexivity.
Qed.

Definition perm (sa : array int) (n : Z) : Prop :=
  forall v : int, cnt sa v 0 (Z.to_nat n) = if ((φ v) <? n)%Z then 1%Z else 0%Z.

Lemma cnt0_hit : forall a v len j, (j < len)%nat -> at_ a j = v -> (1 <= cnt a v 0 len)%Z.
Proof.
  intros a v len. induction len as [|l IH]; intros j Hj Ha; [lia|]. simpl.
  pose proof (cnt_nonneg a v 0 l).
  destruct (Nat.eq_dec j l) as [E|E].
  - subst j. unfold at_ in Ha. rewrite Ha, Uint63.eqb_refl. lia.
  - pose proof (IH j ltac:(lia) Ha). destruct (Uint63.eqb _ v); lia.
Qed.

Lemma cnt0_two : forall a v len j1 j2, (j1 < len)%nat -> (j2 < len)%nat -> j1 <> j2 ->
  at_ a j1 = v -> at_ a j2 = v -> (2 <= cnt a v 0 len)%Z.
Proof.
  intros a v len. induction len as [|l IH]; intros j1 j2 H1 H2 Hne A1 A2; [lia|]. simpl.
  pose proof (cnt_nonneg a v 0 l).
  destruct (Nat.eq_dec j1 l) as [E|E]; [|destruct (Nat.eq_dec j2 l) as [E'|E']].
  - subst j1. pose proof (cnt0_hit a v l j2 ltac:(lia) A2).
    unfold at_ in A1. rewrite A1, Uint63.eqb_refl. lia.
  - subst j2. pose proof (cnt0_hit a v l j1 ltac:(lia) A1).
    unfold at_ in A2. rewrite A2, Uint63.eqb_refl. lia.
  - pose proof (IH j1 j2 ltac:(lia) ltac:(lia) Hne A1 A2). destruct (Uint63.eqb _ v); lia.
Qed.

Lemma cnt0_exists : forall a v len, (1 <= cnt a v 0 len)%Z ->
  exists j, (j < len)%nat /\ at_ a j = v.
Proof.
  intros a v len. induction len as [|l IH]; simpl; intros H; [lia|].
  destruct (Uint63.eqb a.[of_Z (Z.of_nat l)] v) eqn:E.
  - exists l. split; [lia|]. rewrite Uint63.eqb_spec in E. exact E.
  - destruct IH as (j & Hj & Hv); [lia|]. exists j. split; [lia | exact Hv].
Qed.

Section Perm.
  Variable sa : array int.
  Variable n : Z.
  Hypothesis Hp : perm sa n.
  Lemma perm_range : forall j, (Z.of_nat j < n)%Z -> ((φ (at_ sa j)) < n)%Z.
  Proof.
    intros j Hj. pose proof (cnt0_hit sa (at_ sa j) (Z.to_nat n) j ltac:(lia) eq_refl) as H.
    rewrite Hp in H. destruct ((φ (at_ sa j)) <? n)%Z eqn:E; [rewrite Z.ltb_lt in E; exact E | lia].
  Qed.

  Lemma perm_surj : forall v : int, ((φ v) < n)%Z ->
    exists j, (Z.of_nat j < n)%Z /\ at_ sa j = v.
  Proof.
    intros v Hv. destruct (cnt0_exists sa v (Z.to_nat n)) as (j & Hj & E).
    - rewrite Hp. replace ((φ v) <? n)%Z with true by (symmetry; apply Z.ltb_lt; exact Hv). lia.
    - exists j. split; [lia | exact E].
  Qed.

  Lemma perm_inj : forall j1 j2, (Z.of_nat j1 < n)%Z -> (Z.of_nat j2 < n)%Z ->
    at_ sa j1 = at_ sa j2 -> j1 = j2.
  Proof.
    intros j1 j2 H1 H2 E. destruct (Nat.eq_dec j1 j2) as [|Hne]; [assumption|].
    pose proof (cnt0_two sa (at_ sa j2) (Z.to_nat n) j1 j2 ltac:(lia) ltac:(lia) Hne E eq_refl) as H.
    rewrite Hp in H. destruct (_ <? n)%Z; lia.
  Qed.
End Perm.

Lemma iota_loop_eq : forall a n i H,
  iota_loop a n i H =
  match bdec (i <? n) with
  | left Hi => iota_loop a.[i <- i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma iota_spec : forall n z i a H, gap n i = z ->
  PArray.length a = n -> ((φ i) <= (φ n))%Z ->
  (forall y : int, ((φ y) < (φ i))%Z -> a.[y] = y) ->
  PArray.length (iota_loop a n i H) = n /\
  forall y : int, ((φ y) < (φ n))%Z -> (iota_loop a n i H).[y] = y.
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i a H Hz Hl Hi Ha. rewrite iota_loop_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 := succ_phi i n Hin').
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
          | rewrite alength_set; exact Hl | lia | ].
    intros y Hy. destruct (Z.eq_dec (φ y) (φ i)) as [E|E].
    + apply to_Z_inj in E. subst y. apply aget_set_same. rewrite Hl. exact Hin.
    + rewrite aget_set_other by (intro F; subst; lia). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hl|]. intros y Hy. apply Ha. lia.
Qed.

Lemma cnt_iota : forall (a : array int) v len,
  (Z.of_nat len <= 4194303)%Z ->
  (forall j, (j < len)%nat -> at_ a j = of_Z (Z.of_nat j)) ->
  cnt a v 0 len = if ((φ v) <? Z.of_nat len)%Z then 1%Z else 0%Z.
Proof.
  intros a v len. induction len as [|l IH]; intros Hb Ha.
  - simpl. pose proof (to_Z_bounded v). destruct ((φ v) <? 0)%Z eqn:E; [rewrite Z.ltb_lt in E|]; lia.
  - cbn [cnt]. rewrite IH by (intros; try apply Ha; lia).
    pose proof (Ha l ltac:(lia)) as E. unfold at_ in E. rewrite ?Z.add_0_l, E.
    rewrite Nat2Z.inj_succ.
    destruct (Uint63.eqb (of_Z (Z.of_nat l)) v) eqn:Ev.
    + rewrite Uint63.eqb_spec in Ev. subst v. rewrite phi_of_Z by (rewrite wB_val; lia).
      destruct (Z.ltb_spec (Z.of_nat l) (Z.of_nat l)), (Z.ltb_spec (Z.of_nat l) (Z.succ (Z.of_nat l))); lia.
    + rewrite Uint63.eqb_false_spec in Ev.
      assert ((φ v) <> Z.of_nat l) by (intro F; apply Ev; apply to_Z_inj; rewrite F, phi_of_Z by (rewrite wB_val; lia); reflexivity).
      destruct (Z.ltb_spec (φ v) (Z.of_nat l)), (Z.ltb_spec (φ v) (Z.succ (Z.of_nat l))); lia.
Qed.

Lemma rank_loop_eq : forall le sa nr n i H,
  rank_loop le sa nr n i H =
  match bdec (i <? n) with
  | left Hi =>
      let p := sa.[i] in
      let q := sa.[i - 1] in
      rank_loop le sa nr.[p <- nr.[q] + (if le p q then 0 else 1)] n (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => nr
  end.
Proof. intros. destruct H. reflexivity. Qed.

Fixpoint gsteps (le : int -> int -> bool) (sa : array int) (i : nat) : Z :=
  match i with
  | O => 0%Z
  | S i' => (gsteps le sa i' + (if le (at_ sa (S i')) (at_ sa i') then 0 else 1))%Z
  end.

Section Ranks.
  Variable le : int -> int -> bool.
  Hypothesis le_total : forall x y, le x y = true \/ le y x = true.
  Hypothesis le_trans : forall x y z, le x y = true -> le y z = true -> le x z = true.
  Variable sa : array int.
  Variable n : int.
  Hypothesis Hn : (1 <= (φ n) <= 4194303)%Z.
  Hypothesis Hsa : PArray.length sa = n.
  Hypothesis Hp : perm sa (φ n).
  Hypothesis Hs : sorted le sa 0 n.

  Lemma gsteps_bound : forall i, (0 <= gsteps le sa i <= Z.of_nat i)%Z.
  Proof. induction i; simpl; [lia|]. destruct (le _ _); lia. Qed.

  Lemma gsteps_lip : forall i d, (gsteps le sa i <= gsteps le sa (i + d) <= gsteps le sa i + Z.of_nat d)%Z.
  Proof.
    intros i d. induction d; [rewrite Nat.add_0_r; lia|].
    rewrite Nat.add_succ_r. simpl. destruct (le _ _); lia.
  Qed.

  Lemma at_sorted : forall i j, (i <= j)%nat -> (Z.of_nat j < (φ n))%Z ->
    le (at_ sa i) (at_ sa j) = true.
  Proof.
    intros i j Hij Hj. unfold at_.
    apply (sorted_all le le_total le_trans sa 0 n Hs);
      rewrite ?phi_of_Z by (rewrite wB_val; lia); change (φ 0) with 0%Z; lia.
  Qed.

  Lemma gsteps_eq_le : forall j d, (Z.of_nat (j + d) < (φ n))%Z ->
    gsteps le sa (j + d) = gsteps le sa j -> le (at_ sa (j + d)) (at_ sa j) = true.
  Proof.
    intros j d. induction d as [|d IH]; intros Hb E.
    - rewrite Nat.add_0_r. destruct (le_total (at_ sa j) (at_ sa j)); assumption.
    - rewrite Nat.add_succ_r in *. simpl in E.
      pose proof (gsteps_lip j d).
      destruct (le (at_ sa (S (j + d))) (at_ sa (j + d))) eqn:Ed; [|lia].
      apply le_trans with (at_ sa (j + d)); [exact Ed|]. apply IH; lia.
  Qed.

  Lemma le_gsteps_eq : forall j d, (Z.of_nat (j + d) < (φ n))%Z ->
    le (at_ sa (j + d)) (at_ sa j) = true -> gsteps le sa (j + d) = gsteps le sa j.
  Proof.
    intros j d. induction d as [|d IH]; intros Hb E; [rewrite Nat.add_0_r; reflexivity|].
    rewrite Nat.add_succ_r in *. simpl.
    assert (E1 : le (at_ sa (S (j + d))) (at_ sa (j + d)) = true).
    { apply le_trans with (at_ sa j); [exact E|]. apply at_sorted; lia. }
    rewrite E1, IH; [lia|lia|].
    apply le_trans with (at_ sa (S (j + d))); [apply at_sorted; lia | exact E].
  Qed.

  Lemma gsteps_iff : forall i j, (Z.of_nat i < (φ n))%Z -> (Z.of_nat j < (φ n))%Z ->
    ((gsteps le sa i <= gsteps le sa j)%Z <-> le (at_ sa i) (at_ sa j) = true).
  Proof.
    intros i j Hi Hj. destruct (Nat.le_gt_cases i j) as [Hij | Hij].
    - split; intros _; [apply at_sorted; lia|].
      replace j with (i + (j - i))%nat by lia. apply gsteps_lip.
    - replace i with (j + (i - j))%nat in * by lia.
      pose proof (gsteps_lip j (i - j)).
      split; intros Hg.
      + apply gsteps_eq_le; [lia|]. lia.
      + rewrite le_gsteps_eq by assumption. lia.
  Qed.

  Lemma rank_loop_spec : forall z i nr H, gap n i = z ->
    (1 <= (φ i) <= (φ n))%Z -> PArray.length nr = n ->
    (forall j, (Z.of_nat j < (φ i))%Z -> (φ (nr.[at_ sa j])) = gsteps le sa j) ->
    PArray.length (rank_loop le sa nr n i H) = n /\
    (forall j, (Z.of_nat j < (φ n))%Z -> (φ ((rank_loop le sa nr n i H).[at_ sa j])) = gsteps le sa j).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros i nr H Hz Hi Hl Hr. rewrite rank_loop_eq.
    destruct (bdec (i <? n)) as [Hin | Hin].
    - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
      assert (Hi1 := succ_phi i n Hin').
      cbv zeta.
      set (ii := Z.to_nat (φ i)).
      assert (Hii : Z.of_nat ii = (φ i)) by (unfold ii; pose proof (to_Z_bounded i); lia).
      assert (Ei : at_ sa ii = sa.[i]) by apply at_idx.
      assert (Ei1 : at_ sa (ii - 1) = sa.[i - 1]).
      { unfold at_. f_equal. apply to_Z_inj. rewrite phi_of_Z by (rewrite wB_val; lia). sia. }
      pose proof (perm_range sa (φ n) Hp ii ltac:(lia)) as Bp.
      rewrite Ei in Bp.
      assert (Hpb : (sa.[i] <? PArray.length nr) = true) by (rewrite Hl, ltb_spec; exact Bp).
      apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
            | lia | rewrite alength_set; exact Hl | ].
      intros j Hj. rewrite Hi1 in Hj.
      destruct (Nat.eq_dec j ii) as [E|E].
      + subst j. rewrite Ei, aget_set_same by exact Hpb.
        assert (Hq := Hr (ii - 1)%nat ltac:(lia)). rewrite Ei1 in Hq.
        assert (Eg : gsteps le sa ii =
                     (gsteps le sa (ii - 1) + (if le sa.[i] sa.[i - 1] then 0 else 1))%Z).
        { replace ii with (S (ii - 1)) at 1 by lia. simpl gsteps.
          replace (S (ii - 1)) with ii by lia. rewrite Ei, Ei1. reflexivity. }
        rewrite Eg. pose proof (gsteps_bound (ii - 1)).
        destruct (le sa.[i] sa.[i - 1]); rewrite add_spec, Z.mod_small, Hq;
          change (φ 0) with 0%Z; change (φ 1) with 1%Z; rewrite ?wB_val; lia.
      + rewrite aget_set_other.
        * apply Hr. lia.
        * rewrite <- Ei. intro F. apply E. symmetry.
          apply (perm_inj sa (φ n) Hp); [lia | lia | exact F].
    - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
      split; [exact Hl|]. intros j Hj. apply Hr. lia.
  Qed.
End Ranks.

Lemma rounds_eq : forall n rk h H,
  rounds n rk h H =
  let sa := sort_round rk h n in
  let nr := rank_loop (keyle rk h n) sa (PArray.make n 0) n 1
              (Zwf_well_founded 0 (gap n 1)) in
  match bdec (((0 <? h) && (h <? n)) &&
              ((h <? n - h) && negb (nr.[sa.[n - 1]] =? n - 1)))%bool with
  | left C => rounds n nr (h + h) (Acc_inv H (dec_dbl n h _ C))
  | right _ => sa
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_rk_eq : forall x rk n i H,
  init_rk x rk n i H =
  match bdec (i <? n) with
  | left Hi => init_rk x rk.[i <- PrimString.get x i] n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => rk
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* --- proofs --- *)

Lemma keyle_iff : forall rk h n p q,
  keyle rk h n p q = true <->
  ((φ (rk.[p])) < (φ (rk.[q])) \/
   ((φ (rk.[p])) = (φ (rk.[q])) /\ (φ (r2 rk h n p)) <= (φ (r2 rk h n q))))%Z.
Proof.
  intros rk h n p q. unfold keyle.
  rewrite Bool.orb_true_iff, Bool.andb_true_iff, ltb_spec, leb_spec, Uint63.eqb_spec.
  split; intros [H | [H1 H2]].
  - left. exact H.
  - right. split; [rewrite H1; reflexivity | exact H2].
  - left. exact H.
  - right. split; [apply to_Z_inj; exact H1 | exact H2].
Qed.

Lemma keyle_total : forall rk h n x y, keyle rk h n x y = true \/ keyle rk h n y x = true.
Proof. intros. rewrite !keyle_iff. lia. Qed.

Lemma keyle_trans : forall rk h n x y z,
  keyle rk h n x y = true -> keyle rk h n y z = true -> keyle rk h n x z = true.
Proof. intros rk h n x y z. rewrite !keyle_iff. lia. Qed.

Lemma sort_round_spec : forall rk h n, (1 <= (φ n) <= 4194303)%Z ->
  PArray.length (sort_round rk h n) = n /\
  perm (sort_round rk h n) (φ n) /\
  sorted (keyle rk h n) (sort_round rk h n) 0 n.
Proof.
  intros rk h n Hn. unfold sort_round.
  destruct (iota_spec n (gap n 0) 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) eq_refl
              (alength_make n 0 ltac:(lia)) ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia))
    as [La Ca].
  set (a0 := iota_loop (PArray.make n 0) n 0 (Zwf_well_founded 0 (gap n 0))) in *.
  destruct (msort_spec (keyle rk h n) (keyle_total rk h n)
              (gap n 0) 0 n a0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(rewrite La; lia)
              ltac:(rewrite La; apply alength_make; lia))
    as [_ (L & _ & S & C)].
  split; [rewrite L; exact La|]. split; [|exact S].
  intros v. change (φ 0) with 0%Z in C. rewrite Z.sub_0_r in C. rewrite C.
  rewrite <- (Z2Nat.id (φ n)) at 2 by lia.
  apply cnt_iota; [lia|]. intros j Hj. unfold at_. apply Ca.
  rewrite phi_of_Z by (rewrite wB_val; lia). lia.
Qed.

Section Doubling.
  Variable str : list Z.
  Variable n : int.
  Hypothesis HnS : (φ n) = Z.of_nat (List.length str).
  Hypothesis Hn : (1 <= (φ n) <= 1000000)%Z.

  Definition preZ (h p : Z) : list Z := firstn (Z.to_nat h) (skipn (Z.to_nat p) str).
  Definition sufZ (p : Z) : list Z := skipn (Z.to_nat p) str.

  Definition sufle (p q : int) : bool :=
    match lexcmp (sufZ (φ p)) (sufZ (φ q)) with Gt => false | _ => true end.

  Lemma sufle_total : forall x y, sufle x y = true \/ sufle y x = true.
  Proof.
    intros x y. unfold sufle. rewrite (lexcmp_opp (sufZ (φ x))).
    destruct (lexcmp (sufZ (φ x)) (sufZ (φ y))); simpl; auto.
  Qed.

  Lemma sufle_trans : forall x y z, sufle x y = true -> sufle y z = true -> sufle x z = true.
  Proof.
    intros x y z. unfold sufle.
    assert (Hb : forall a b, (match lexcmp a b with Gt => false | _ => true end = true) <-> lexle a b)
      by (intros a b; unfold lexle; destruct (lexcmp a b); split; congruence).
    rewrite !Hb. apply lexle_trans.
  Qed.

  Definition RI (rk : array int) (h : Z) : Prop :=
    (forall p q : int, ((φ p) < (φ n))%Z -> ((φ q) < (φ n))%Z ->
       (((φ (rk.[p])) <= (φ (rk.[q])))%Z <-> lexle (preZ h (φ p)) (preZ h (φ q)))) /\
    (forall p : int, ((φ p) < (φ n))%Z -> ((φ (rk.[p])) < 1099511627776)%Z).

  Lemma preZ_nil : forall h p, (Z.of_nat (List.length str) <= p)%Z -> preZ h p = [].
  Proof.
    intros h p H. unfold preZ. rewrite (skipn_all2 str) by lia. destruct (Z.to_nat h); reflexivity.
  Qed.

  Lemma preZ_cons : forall h p, (1 <= h)%Z -> (0 <= p < Z.of_nat (List.length str))%Z ->
    exists x l, preZ h p = x :: l.
  Proof.
    intros h p Hh Hp. unfold preZ. rewrite (skipn_cons_nth str) by lia.
    replace (Z.to_nat h) with (S (Z.to_nat h - 1)) by lia. simpl. eauto.
  Qed.

  Lemma length_preZ : forall h p, (0 <= h)%Z -> (0 <= p)%Z ->
    Z.of_nat (List.length (preZ h p)) = Z.min h (Z.max 0 (Z.of_nat (List.length str) - p)).
  Proof.
    intros h p Hh Hp. unfold preZ. rewrite length_firstn, length_skipn. lia.
  Qed.

  Lemma pre_double : forall h p, (0 <= h)%Z -> (0 <= p)%Z ->
    preZ (h + h) p = preZ h p ++ preZ h (p + h).
  Proof.
    intros h p Hh Hp. unfold preZ.
    replace (Z.to_nat (h + h)) with (Z.to_nat h + Z.to_nat h)%nat by lia.
    rewrite firstn_add, skipn_skipn. f_equal. f_equal. f_equal. lia.
  Qed.

  Lemma lexle_nil_l : forall l, lexle [] l.
  Proof. intros [|x l]; unfold lexle; simpl; discriminate. Qed.

  Lemma r2_iff : forall rk h p q, RI rk (φ h) -> (1 <= (φ h) <= (φ n))%Z ->
    ((φ p) < (φ n))%Z -> ((φ q) < (φ n))%Z ->
    (((φ (r2 rk h n p)) <= (φ (r2 rk h n q)))%Z <->
     lexle (preZ (φ h) ((φ p) + (φ h))) (preZ (φ h) ((φ q) + (φ h)))).
  Proof.
    intros rk h p q [R1 R2] Hh Hp Hq. unfold r2.
    pose proof (to_Z_bounded p). pose proof (to_Z_bounded q).
    assert (Ep : (φ (p + h)) = ((φ p) + (φ h))%Z) by sia.
    assert (Eq : (φ (q + h)) = ((φ q) + (φ h))%Z) by sia.
    destruct (p + h <? n) eqn:E1; destruct (q + h <? n) eqn:E2;
      rewrite ?ltb_spec in E1, E2; rewrite <- ?Bool.not_true_iff_false, ?ltb_spec in E1, E2;
      rewrite ?Ep in E1; rewrite ?Eq in E2.
    - pose proof (R2 (p + h) ltac:(lia)). pose proof (R2 (q + h) ltac:(lia)).
      rewrite !add_spec, !Z.mod_small; change (φ 1) with 1%Z; rewrite ?wB_val; try lia.
      rewrite <- Ep, <- Eq. rewrite <- R1 by lia. lia.
    - pose proof (R2 (p + h) ltac:(lia)).
      rewrite (preZ_nil _ ((φ q) + (φ h))) by lia.
      destruct (preZ_cons (φ h) ((φ p) + (φ h))) as (x & l & E); [lia | lia |].
      rewrite E. unfold lexle. simpl.
      rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; change (φ 0) with 0%Z; rewrite ?wB_val; try lia.
      split; [lia | intros F; exfalso; apply F; reflexivity].
    - rewrite (preZ_nil _ ((φ p) + (φ h))) by lia. change (φ 0) with 0%Z.
      split; intros _; [apply lexle_nil_l | pose proof (to_Z_bounded (rk.[q + h] + 1)); lia].
    - rewrite (preZ_nil _ ((φ p) + (φ h))) by lia. change (φ 0) with 0%Z.
      split; intros _; [apply lexle_nil_l | lia].
  Qed.

  Lemma keyle_pre : forall rk h p q, RI rk (φ h) -> (1 <= (φ h) <= (φ n))%Z ->
    ((φ p) < (φ n))%Z -> ((φ q) < (φ n))%Z ->
    (keyle rk h n p q = true <-> lexle (preZ ((φ h) + (φ h)) (φ p)) (preZ ((φ h) + (φ h)) (φ q))).
  Proof.
    intros rk h p q HR Hh Hp Hq.
    pose proof (to_Z_bounded p). pose proof (to_Z_bounded q).
    rewrite keyle_iff, (r2_iff rk h p q HR Hh Hp Hq).
    rewrite !pre_double by lia.
    unfold lexle at 2. rewrite lexcmp_app.
    2:{ intros Hlt. apply preZ_nil.
        pose proof (length_preZ (φ h) (φ p) ltac:(lia) ltac:(lia)).
        pose proof (length_preZ (φ h) (φ q) ltac:(lia) ltac:(lia)). lia. }
    2:{ intros Hlt. apply preZ_nil.
        pose proof (length_preZ (φ h) (φ p) ltac:(lia) ltac:(lia)).
        pose proof (length_preZ (φ h) (φ q) ltac:(lia) ltac:(lia)). lia. }
    destruct HR as [R1 _].
    pose proof (R1 p q Hp Hq) as Rpq. pose proof (R1 q p Hq Hp) as Rqp.
    destruct (lexcmp (preZ (φ h) (φ p)) (preZ (φ h) (φ q))) eqn:E.
    - apply lexcmp_eq in E. rewrite E in Rpq, Rqp.
      pose proof (proj2 Rpq (lexle_refl _)). pose proof (proj2 Rqp (lexle_refl _)).
      split; [intros [F | [_ F]]; [lia | exact F] | intros F; right; split; [lia | exact F]].
    - assert (L1 : lexle (preZ (φ h) (φ p)) (preZ (φ h) (φ q))) by (unfold lexle; congruence).
      assert (L2 := proj1 (lexcmp_lt_iff _ _) E).
      assert (L3 : ~ ((φ (rk.[q])) <= (φ (rk.[p])))%Z) by (rewrite Rqp; exact L2).
      assert ((φ (rk.[p])) < (φ (rk.[q])))%Z by lia.
      split; [intros _; discriminate | intros _; left; assumption].
    - assert (L1 : ~ lexle (preZ (φ h) (φ p)) (preZ (φ h) (φ q))) by (unfold lexle; congruence).
      split; [intros [F | [F _]]; exfalso; apply L1; apply Rpq; lia | intros F; congruence].
  Qed.

  Definition sa_ok (sa : array int) : Prop :=
    PArray.length sa = n /\ perm sa (φ n) /\ sorted sufle sa 0 n.

  Lemma rounds_spec : forall z h rk H, gap n h = z ->
    (1 <= (φ h) <= (φ n))%Z -> RI rk (φ h) -> sa_ok (rounds n rk h H).
  Proof.
    intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
    intros h rk H Hz Hh HR. rewrite rounds_eq. cbv zeta.
    destruct (sort_round_spec rk h n ltac:(lia)) as (Ls & Ps & Ss).
    set (sa := sort_round rk h n) in *.
    set (le := keyle rk h n) in *.
    assert (Ltot := keyle_total rk h n). assert (Ltr := keyle_trans rk h n).
    fold le in Ltot, Ltr.
    destruct (rank_loop_spec le sa n ltac:(lia) Ls Ps (gap n 1) 1 (PArray.make n 0)
                (Zwf_well_founded 0 (gap n 1)) eq_refl ltac:(change (φ 1) with 1%Z; lia)
                (alength_make n 0 ltac:(lia))
                ltac:(intros j Hj; change (φ 1) with 1%Z in Hj; replace j with O by lia;
                      rewrite aget_make; reflexivity))
      as [Lr Cr].
    set (nr := rank_loop le sa (PArray.make n 0) n 1 (Zwf_well_founded 0 (gap n 1))) in *.
    (* nr is a rank array for the 2h-prefixes *)
    assert (HR2 : RI nr ((φ h) + (φ h))).
    { split.
      - intros p q Hp Hq.
        destruct (perm_surj sa (φ n) Ps p Hp) as (i & Hi & Ei).
        destruct (perm_surj sa (φ n) Ps q Hq) as (j & Hj & Ej).
        rewrite <- Ei, <- Ej, !Cr by assumption.
        rewrite (gsteps_iff le Ltot Ltr sa n ltac:(lia) Ls Ss i j Hi Hj).
        rewrite Ei, Ej. apply keyle_pre; assumption.
      - intros p Hp.
        destruct (perm_surj sa (φ n) Ps p Hp) as (i & Hi & Ei).
        rewrite <- Ei, Cr by assumption. pose proof (gsteps_bound le sa n Ls i). lia. }
    destruct (bdec _) as [C | C].
    - pose proof C as C'. apply andb_prop in C'. destruct C' as [_ C2].
      apply andb_prop in C2. destruct C2 as [C2 _]. rewrite ltb_spec in C2.
      assert (E : (φ (n - h)) = ((φ n) - (φ h))%Z) by sia. rewrite E in C2.
      assert (Hhh : (φ (h + h)) = ((φ h) + (φ h))%Z) by sia.
      apply (IH (gap n (h + h))); [rewrite <- Hz; exact (dec_dbl n h _ C) | reflexivity | lia |].
      rewrite Hhh. exact HR2.
    - split; [exact Ls|]. split; [exact Ps|].
      intros i Hi1 Hi2. change (φ 0) with 0%Z in Hi1.
      pose proof (to_Z_bounded i).
      assert (Hi1' := succ_phi i n ltac:(lia)).
      assert (Bi : ((φ (sa.[i])) < (φ n))%Z)
        by (rewrite <- at_idx; apply perm_range with (n := (φ n)); [exact Ps | lia]).
      assert (Bi1 : ((φ (sa.[i + 1])) < (φ n))%Z)
        by (rewrite <- at_idx; apply perm_range with (n := (φ n)); [exact Ps | lia]).
      pose proof (to_Z_bounded (sa.[i])). pose proof (to_Z_bounded (sa.[i + 1])).
      assert (Hk : keyle rk h n sa.[i] sa.[i + 1] = true) by (apply Ss; change (φ 0) with 0%Z; lia).
      rewrite (keyle_pre rk h _ _ HR ltac:(lia) Bi Bi1) in Hk.
      destruct (Z_lt_le_dec ((φ h) + (φ h)) (φ n)) as [Hlt | Hge].
      + (* all ranks distinct *)
        assert (Edist : nr.[sa.[n - 1]] = n - 1).
        { destruct (nr.[sa.[n - 1]] =? n - 1) eqn:Ee; [apply Uint63.eqb_spec; exact Ee|].
          exfalso. assert (E : (φ (n - h)) = ((φ n) - (φ h))%Z) by sia.
          assert (T : ((((0 <? h) && (h <? n)) && ((h <? n - h) &&
                         negb (nr.[sa.[n - 1]] =? n - 1)))%bool = true)).
          { rewrite Ee.
            replace (0 <? h) with true by (symmetry; apply ltb_spec; change (φ 0) with 0%Z; lia).
            replace (h <? n) with true by (symmetry; apply ltb_spec; lia).
            replace (h <? n - h) with true by (symmetry; apply ltb_spec; rewrite E; lia).
            reflexivity. }
          congruence. }
        assert (En1 : (φ (n - 1)) = ((φ n) - 1)%Z) by sia.
        assert (Gn : gsteps le sa (Z.to_nat ((φ n) - 1)) = ((φ n) - 1)%Z).
        { rewrite <- Cr by lia. rewrite <- En1, at_idx, Edist. reflexivity. }
        set (ii := Z.to_nat (φ i)).
        assert (Hii : Z.of_nat ii = (φ i)) by (unfold ii; lia).
        assert (Step : le (at_ sa (S ii)) (at_ sa ii) = false).
        { destruct (le (at_ sa (S ii)) (at_ sa ii)) eqn:Es; [|reflexivity]. exfalso.
          pose proof (gsteps_lip le sa n Ls (S ii) (Z.to_nat ((φ n) - 1) - S ii)) as G.
          replace (S ii + (Z.to_nat ((φ n) - 1) - S ii))%nat with (Z.to_nat ((φ n) - 1)) in G by lia.
          pose proof (gsteps_bound le sa n Ls ii). simpl gsteps in G. rewrite Es in G. lia. }
        assert (Eii1 : at_ sa (S ii) = sa.[i + 1]).
        { unfold at_. f_equal. apply to_Z_inj. rewrite phi_of_Z by (rewrite wB_val; lia). lia. }
        assert (Eii : at_ sa ii = sa.[i]) by apply at_idx.
        rewrite Eii1, Eii in Step. fold le in Step.
        assert (Hnk : ~ lexle (preZ ((φ h) + (φ h)) (φ (sa.[i + 1]))) (preZ ((φ h) + (φ h)) (φ (sa.[i])))).
        { intros F. apply (proj2 (keyle_pre rk h _ _ HR ltac:(lia) Bi1 Bi)) in F.
          fold le in F. congruence. }
        apply lexcmp_lt_iff in Hnk. unfold preZ in Hnk.
        rewrite lexcmp_firstn in Hnk by congruence.
        unfold sufle, sufZ. rewrite Hnk. reflexivity.
      + (* 2h >= n: the 2h-prefixes are the suffixes *)
        unfold preZ in Hk. rewrite !firstn_all2 in Hk by (rewrite length_skipn; lia).
        unfold sufle, sufZ. unfold lexle in Hk. destruct (lexcmp _ _); congruence.
  Qed.
End Doubling.

Lemma init_rk_spec : forall x n z i (rk : array int) H, gap n i = z ->
  PArray.length rk = n -> ((φ i) <= (φ n))%Z ->
  (forall y : int, ((φ y) < (φ i))%Z -> rk.[y] = PrimString.get x y) ->
  PArray.length (init_rk x rk n i H) = n /\
  forall y : int, ((φ y) < (φ n))%Z -> (init_rk x rk n i H).[y] = PrimString.get x y.
Proof.
  intros x n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i rk H Hz Hl Hi Ha. rewrite init_rk_eq.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 := succ_phi i n Hin').
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
          | rewrite alength_set; exact Hl | lia | ].
    intros y Hy. destruct (Z.eq_dec (φ y) (φ i)) as [E|E].
    + apply to_Z_inj in E. subst y. apply aget_set_same. rewrite Hl. exact Hin.
    + rewrite aget_set_other by (intro F; subst; lia). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hl|]. intros y Hy. apply Ha. lia.
Qed.

Lemma build_sa_spec : forall (x : PrimString.string) (s : string) (n : int),
  repr x s -> (φ n) = Z.of_nat (String.length s) -> (1 <= (φ n) <= 1000000)%Z ->
  sa_ok (codes s) n (build_sa x n).
Proof.
  intros x s n Hx Hn Bn. unfold build_sa.
  assert (HnS : (φ n) = Z.of_nat (List.length (codes s))) by (rewrite length_codes; exact Hn).
  destruct (init_rk_spec x n (gap n 0) 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)) eq_refl
              (alength_make n 0 ltac:(lia)) ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy; pose proof (to_Z_bounded y); lia))
    as [Lk Ck].
  apply (rounds_spec (codes s) n HnS Bn (gap n 1)); [reflexivity | change (φ 1) with 1%Z; lia |].
  change (φ 1) with 1%Z.
  assert (Hpre : forall p : int, ((φ p) < (φ n))%Z ->
            preZ (codes s) 1 (φ p) = [nth (Z.to_nat (φ p)) (codes s) 0%Z]).
  { intros p Hp. unfold preZ. pose proof (to_Z_bounded p).
    rewrite (skipn_cons_nth (codes s)) by lia. reflexivity. }
  split.
  - intros p q Hp Hq. rewrite !Ck by assumption. rewrite !Hpre by assumption.
    rewrite !(repr_str_get x s Hx) by lia.
    unfold lexle. simpl.
    destruct (Z.compare_spec (nth (Z.to_nat (φ p)) (codes s) 0%Z) (nth (Z.to_nat (φ q)) (codes s) 0%Z));
      split; intros; try congruence; try lia.
  - intros p Hp. rewrite Ck by assumption. rewrite (repr_str_get x s Hx) by lia.
    pose proof (codes_bound s (Z.to_nat (φ p))). lia.
Qed.

Lemma bs_eq : forall P lo hi H,
  bs P lo hi H =
  match bdec (lo <? hi) with
  | left Hl =>
      if P (midp lo hi) then bs P lo (midp lo hi) (Acc_inv H (dec_bl lo hi Hl))
      else bs P (midp lo hi + 1) hi (Acc_inv H (dec_br lo hi Hl))
  | right _ => lo
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bs_spec : forall (P : int -> bool) (N : int),
  (forall i j : int, ((φ i) <= (φ j) < (φ N))%Z -> P i = true -> P j = true) ->
  forall z lo hi H, gap hi lo = z -> ((φ lo) <= (φ hi) <= (φ N))%Z ->
  (forall i : int, ((φ i) < (φ lo))%Z -> P i = false) ->
  (forall i : int, ((φ hi) <= (φ i) < (φ N))%Z -> P i = true) ->
  ((φ (bs P lo hi H)) <= (φ N))%Z /\
  forall i : int, ((φ i) < (φ N))%Z -> (P i = true <-> ((φ (bs P lo hi H)) <= (φ i))%Z).
Proof.
  intros P N Hm z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H Hz Hlh Hlo Hhi. rewrite bs_eq.
  destruct (bdec (lo <? hi)) as [Hl | Hl].
  - pose proof Hl as Hl'. rewrite ltb_spec in Hl'.
    pose proof (midp_spec lo hi Hl') as Em.
    assert (0 <= ((φ hi) - (φ lo)) / 2 < (φ hi) - (φ lo))%Z
      by (split; [apply Z.div_pos | apply Z.div_lt]; lia).
    destruct (P (midp lo hi)) eqn:Ep.
    + apply (IH (gap (midp lo hi) lo)); [rewrite <- Hz; apply dec_bl; exact Hl | reflexivity
            | lia | exact Hlo | ].
      intros i Hi. destruct (Z_lt_le_dec (φ i) (φ hi)).
      * apply (Hm (midp lo hi)); [lia | exact Ep].
      * apply Hhi. lia.
    + assert (E1 : (φ (midp lo hi + 1)) = ((φ (midp lo hi)) + 1)%Z)
        by (apply (succ_phi _ hi); lia).
      apply (IH (gap hi (midp lo hi + 1))); [rewrite <- Hz; apply dec_br; exact Hl | reflexivity
            | lia | | exact Hhi].
      intros i Hi. destruct (Z_lt_le_dec (φ i) (φ lo)).
      * apply Hlo. lia.
      * destruct (P i) eqn:Ei; [|reflexivity].
        rewrite (Hm i (midp lo hi)) in Ep by lia. discriminate.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hl.
    split; [lia|]. intros i Hi. split.
    + intros Hp. destruct (Z_lt_le_dec (φ i) (φ lo)); [|lia]. rewrite Hlo in Hp by lia. discriminate.
    + intros Hle. apply Hhi. lia.
Qed.

Lemma ins_eq : forall L R C nx x d v H,
  ins L R C nx x d v H =
  match bdec (0 <? d) with
  | left Hd =>
      let half := 1 << (d - 1) in
      let y := nx + d in
      if v <? half then
        let '(Lq, Rq, Cq) := ins L R C nx L.[x] (d - 1) v (Acc_inv H (dec_d d Hd)) in
        (Lq.[y <- nx + (d - 1)], Rq.[y <- Rq.[x]], Cq.[y <- Cq.[x] + 1])
      else
        let '(Lq, Rq, Cq) := ins L R C nx R.[x] (d - 1) (v - half) (Acc_inv H (dec_d d Hd)) in
        (Lq.[y <- Lq.[x]], Rq.[y <- nx + (d - 1)], Cq.[y <- Cq.[x] + 1])
  | right _ => (L, R, C.[nx <- C.[x] + 1])
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qry_eq : forall L R C a b d k H,
  qry L R C a b d k H =
  match bdec (0 <? d) with
  | left Hd =>
      let cl := C.[L.[b]] - C.[L.[a]] in
      if k <=? cl then qry L R C L.[a] L.[b] (d - 1) k (Acc_inv H (dec_d d Hd))
      else (1 << (d - 1)) + qry L R C R.[a] R.[b] (d - 1) (k - cl) (Acc_inv H (dec_d d Hd))
  | right _ => 0
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* --- the meaning of a node --- *)

Fixpoint mult (L R C : array int) (x : int) (d : nat) (w : Z) : Z :=
  match d with
  | O => (φ (C.[x]))
  | S d' => if (w <? 2 ^ Z.of_nat d')%Z then mult L R C (L.[x]) d' w
            else mult L R C (R.[x]) d' (w - 2 ^ Z.of_nat d')
  end.

Fixpoint good (L R C : array int) (x : int) (d : nat) (b : Z) : Prop :=
  ((φ x) < b)%Z /\
  match d with
  | O => True
  | S d' => (φ (C.[x])) = ((φ (C.[L.[x]])) + (φ (C.[R.[x]])))%Z /\
            good L R C (L.[x]) d' b /\ good L R C (R.[x]) d' b
  end.

Definition agree (L R C L' R' C' : array int) (b : Z) : Prop :=
  forall y : int, ((φ y) < b)%Z -> L'.[y] = L.[y] /\ R'.[y] = R.[y] /\ C'.[y] = C.[y].

Lemma good_lt : forall L R C x d b, good L R C x d b -> ((φ x) < b)%Z.
Proof. intros L R C x [|d] b H; simpl in H; tauto. Qed.

Lemma good_mono : forall L R C d x b b', good L R C x d b -> (b <= b')%Z -> good L R C x d b'.
Proof.
  intros L R C d. induction d as [|d IH]; intros x b b' H Hb; simpl in *.
  - split; [lia | exact I].
  - destruct H as (Hx & Hc & GL & GR). split; [lia|]. split; [exact Hc|].
    split; eapply IH; eauto.
Qed.

Lemma good_frame : forall L R C L' R' C' bnd d x b,
  agree L R C L' R' C' bnd -> (b <= bnd)%Z -> good L R C x d b ->
  good L' R' C' x d b /\ forall w, mult L' R' C' x d w = mult L R C x d w.
Proof.
  intros L R C L' R' C' bnd d. induction d as [|d IH]; intros x b Hag Hb Hg; simpl in Hg |- *.
  - destruct Hg as [Hx _]. destruct (Hag x ltac:(lia)) as (_ & _ & EC).
    split; [split; [exact Hx | exact I] | intros w; rewrite EC; reflexivity].
  - destruct Hg as (Hx & Hc & GL & GR). destruct (Hag x ltac:(lia)) as (EL & ER & EC).
    rewrite EL, ER, EC.
    destruct (IH _ _ Hag Hb GL) as [GL' ML]. destruct (IH _ _ Hag Hb GR) as [GR' MR].
    pose proof (good_lt _ _ _ _ _ _ GL). pose proof (good_lt _ _ _ _ _ _ GR).
    destruct (Hag (L.[x]) ltac:(lia)) as (_ & _ & ECL).
    destruct (Hag (R.[x]) ltac:(lia)) as (_ & _ & ECR).
    rewrite ECL, ECR. split; [repeat split; auto|]. intros w. rewrite ML, MR. reflexivity.
Qed.

Lemma agree_refl : forall L R C b, agree L R C L R C b.
Proof. intros L R C b y _. auto. Qed.

Lemma agree_trans : forall L R C La Ra Ca Lb Rb Cb b,
  agree L R C La Ra Ca b -> agree La Ra Ca Lb Rb Cb b -> agree L R C Lb Rb Cb b.
Proof.
  intros L R C La Ra Ca Lb Rb Cb b H1 H2 y Hy.
  destruct (H1 y Hy) as (A1 & B1 & Ca'). destruct (H2 y Hy) as (A2 & B2 & Cb').
  rewrite A2, B2, Cb'. auto.
Qed.

Lemma agree_weaken : forall L R C L' R' C' b b',
  agree L R C L' R' C' b -> (b' <= b)%Z -> agree L R C L' R' C' b'.
Proof. intros L R C L' R' C' b b' H Hb y Hy. apply H. lia. Qed.

Lemma agree_set : forall L R C (y : int) a1 a2 a3 b, (b <= (φ y))%Z ->
  agree L R C L.[y <- a1] R.[y <- a2] C.[y <- a3] b.
Proof.
  intros L R C y a1 a2 a3 b Hb y0 Hy0.
  rewrite !aget_set_other by (intro F; subst; lia). auto.
Qed.

Fixpoint sumz (f : Z -> Z) (m : nat) : Z :=
  match m with
  | O => 0%Z
  | S m' => (sumz f m' + f (Z.of_nat m'))%Z
  end.

Lemma sumz_ext : forall f g m, (forall j, (j < m)%nat -> f (Z.of_nat j) = g (Z.of_nat j)) ->
  sumz f m = sumz g m.
Proof.
  intros f g m. induction m as [|m IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumz_split : forall f a b,
  sumz f (a + b) = (sumz f a + sumz (fun w => f (w + Z.of_nat a)%Z) b)%Z.
Proof.
  intros f a b. induction b as [|b IH]; simpl.
  - rewrite Nat.add_0_r. lia.
  - rewrite Nat.add_succ_r. simpl. rewrite IH.
    replace (Z.of_nat (a + b)) with (Z.of_nat b + Z.of_nat a)%Z by lia. lia.
Qed.

Lemma sumz_nonneg : forall f m, (forall j, (j < m)%nat -> (0 <= f (Z.of_nat j))%Z) ->
  (0 <= sumz f m)%Z.
Proof.
  intros f m. induction m as [|m IH]; intros H; simpl; [lia|].
  pose proof (H m ltac:(lia)). pose proof (IH ltac:(intros; apply H; lia)). lia.
Qed.

Lemma sumz_sub : forall f g m,
  sumz (fun w => f w - g w)%Z m = (sumz f m - sumz g m)%Z.
Proof. intros f g m. induction m as [|m IH]; simpl; lia. Qed.

Lemma pow2_nat : forall d, Z.of_nat (2 ^ d)%nat = (2 ^ Z.of_nat d)%Z.
Proof. intros d. rewrite Nat2Z.inj_pow. reflexivity. Qed.

Lemma pow2_S : forall d, (2 ^ Z.of_nat (S d) = 2 ^ Z.of_nat d + 2 ^ Z.of_nat d)%Z.
Proof. intros d. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

Lemma good_sum : forall L R C d x b, good L R C x d b ->
  (φ (C.[x])) = sumz (mult L R C x d) (2 ^ d)%nat.
Proof.
  intros L R C d. induction d as [|d IH]; intros x b Hg; simpl in Hg.
  - reflexivity.
  - destruct Hg as (_ & Hc & GL & GR).
    replace (2 ^ S d)%nat with (2 ^ d + 2 ^ d)%nat by (simpl; lia).
    rewrite sumz_split, Hc, (IH _ _ GL), (IH _ _ GR). f_equal.
    + apply sumz_ext. intros j Hj. simpl.
      replace (Z.of_nat j <? 2 ^ Z.of_nat d)%Z with true; [reflexivity|].
      symmetry. apply Z.ltb_lt. rewrite <- pow2_nat. lia.
    + apply sumz_ext. intros j Hj. simpl. rewrite pow2_nat.
      replace (Z.of_nat j + 2 ^ Z.of_nat d <? 2 ^ Z.of_nat d)%Z with false
        by (symmetry; apply Z.ltb_ge; lia).
      f_equal. lia.
Qed.

Lemma good_zero : forall L R C b, L.[0] = 0 -> R.[0] = 0 -> C.[0] = 0 -> (1 <= b)%Z ->
  forall d, good L R C 0 d b /\ forall w, mult L R C 0 d w = 0%Z.
Proof.
  intros L R C b HL HR HC Hb d. induction d as [|d IH]; simpl.
  - rewrite HC. split; [split; [change (φ 0) with 0%Z; lia | exact I] | reflexivity].
  - rewrite HL, HR, HC. destruct IH as [IG IM].
    split; [repeat split; auto; change (φ 0) with 0%Z; lia|].
    intros w. destruct (_ <? _)%Z; apply IM.
Qed.

Lemma good_child_le : forall L R C x d b, good L R C x (S d) b ->
  ((φ (C.[L.[x]])) <= (φ (C.[x])) /\ (φ (C.[R.[x]])) <= (φ (C.[x])))%Z.
Proof.
  intros L R C x d b [_ [Hc _]].
  pose proof (to_Z_bounded (C.[L.[x]])). pose proof (to_Z_bounded (C.[R.[x]])). lia.
Qed.

Lemma half_spec : forall d : int, (1 <= (φ d) <= 30)%Z -> (φ (1 << (d - 1))) = (2 ^ ((φ d) - 1))%Z.
Proof.
  intros d H. rewrite lsl_spec. change (φ 1) with 1%Z.
  assert (E : (φ (d - 1)) = ((φ d) - 1)%Z) by sia. rewrite E, Z.mul_1_l.
  apply Z.mod_small. split; [apply Z.pow_nonneg; lia|].
  assert (2 ^ ((φ d) - 1) <= 2 ^ 29)%Z by (apply Z.pow_le_mono_r; lia).
  rewrite wB_val. lia.
Qed.

Lemma ins_spec : forall dn L R C nx x d v H,
  (φ d) = Z.of_nat dn -> (dn <= 20)%nat ->
  PArray.length R = PArray.length L -> PArray.length C = PArray.length L ->
  (1 <= (φ nx))%Z -> ((φ nx) + Z.of_nat dn < (φ (PArray.length L)))%Z ->
  good L R C x dn (φ nx) -> (0 <= (φ v) < 2 ^ Z.of_nat dn)%Z ->
  ((φ (C.[x])) < 1099511627776)%Z ->
  match ins L R C nx x d v H with
  | (L', R', C') =>
    PArray.length L' = PArray.length L /\ PArray.length R' = PArray.length L /\
    PArray.length C' = PArray.length L /\
    agree L R C L' R' C' (φ nx) /\
    good L' R' C' (nx + d) dn ((φ nx) + Z.of_nat dn + 1) /\
    (φ (C'.[nx + d])) = ((φ (C.[x])) + 1)%Z /\
    (forall w, (0 <= w < 2 ^ Z.of_nat dn)%Z ->
       mult L' R' C' (nx + d) dn w =
       (mult L R C x dn w + (if (w =? (φ v))%Z then 1 else 0))%Z)
  end.
Proof.
  induction dn as [|dn IH]; intros L R C nx x d v H Hd Hdn HRL HCL Hnx Hlen Hg Hv Hc;
    rewrite ins_eq; pose proof (alength_bound L) as BL.
  - assert (Ed : d = 0) by (apply to_Z_inj; rewrite Hd; reflexivity). subst d.
    destruct (bdec (0 <? 0)) as [F | _]; [discriminate|].
    simpl Z.of_nat in *.
    replace (nx + 0) with nx by (apply to_Z_inj; sia).
    assert (Hnb : (nx <? PArray.length C) = true) by (rewrite ltb_spec, HCL; lia).
    assert (EC : (φ ((C.[nx <- C.[x] + 1]).[nx])) = ((φ (C.[x])) + 1)%Z).
    { rewrite aget_set_same by exact Hnb. rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z;
        rewrite ?wB_val; lia. }
    split; [reflexivity|]. split; [exact HRL|]. split; [rewrite alength_set; exact HCL|].
    split.
    { intros y0 Hy0. split; [reflexivity|]. split; [reflexivity|].
      apply aget_set_other. intro F; subst; lia. }
    split; [split; [lia | exact I]|]. split; [exact EC|].
    intros w Hw. cbn [mult]. rewrite EC.
    change (2 ^ 0)%Z with 1%Z in Hv, Hw.
    replace (w =? (φ v))%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - assert (Hdd0 : (0 <? d) = true) by (rewrite ltb_spec; change (φ 0) with 0%Z; lia).
    destruct (bdec (0 <? d)) as [Hdd | F]; [|congruence].
    cbv zeta.
    assert (Hhalf : (φ (1 << (d - 1))) = (2 ^ Z.of_nat dn)%Z)
      by (rewrite half_spec by lia; f_equal; lia).
    assert (Ed1 : (φ (d - 1)) = Z.of_nat dn) by sia.
    assert (Ey : (φ (nx + d)) = ((φ nx) + Z.of_nat dn + 1)%Z) by sia.
    assert (Ey' : (φ (nx + (d - 1))) = ((φ nx) + Z.of_nat dn)%Z) by sia.
    assert (Hp2 := pow2_S dn).
    cbn [good] in Hg. destruct Hg as (Hx & Hcx & GL & GR).
    pose proof (good_lt _ _ _ _ _ _ GL) as BLx. pose proof (good_lt _ _ _ _ _ _ GR) as BRx.
    pose proof (to_Z_bounded (C.[L.[x]])). pose proof (to_Z_bounded (C.[R.[x]])).
    assert (Hny : ((φ (nx + (d - 1))) < (φ (nx + d)))%Z) by lia.
    destruct (v <? 1 << (d - 1)) eqn:Ev.
    + rewrite ltb_spec, Hhalf in Ev.
      specialize (IH L R C nx (L.[x]) (d - 1) v (Acc_inv H (dec_d d Hdd)) Ed1 ltac:(lia)
                     HRL HCL Hnx ltac:(lia) GL ltac:(lia) ltac:(lia)).
      destruct (ins L R C nx L.[x] (d - 1) v (Acc_inv H (dec_d d Hdd))) as [[Lq Rq] Cq].
      destruct IH as (L1 & R1' & C1' & Ag1 & G1 & EC1 & M1).
      destruct (Ag1 x Hx) as (Ex1 & Ex2 & Ex3).
      destruct (Ag1 (R.[x]) BRx) as (_ & _ & ExR).
      assert (Hyb : forall (A : array int), PArray.length A = PArray.length L ->
                 (nx + d <? PArray.length A) = true)
        by (intros A HA; rewrite ltb_spec, HA; lia).
      assert (Ag2 : agree Lq Rq Cq (Lq.[nx + d <- nx + (d - 1)]) (Rq.[nx + d <- Rq.[x]])
                       (Cq.[nx + d <- Cq.[x] + 1]) ((φ nx) + Z.of_nat dn + 1))
        by (apply agree_set; lia).
      assert (EL : (Lq.[nx + d <- nx + (d - 1)]).[nx + d] = nx + (d - 1))
        by (apply aget_set_same, Hyb, L1).
      assert (ER : (Rq.[nx + d <- Rq.[x]]).[nx + d] = R.[x])
        by (rewrite aget_set_same by (apply Hyb; exact R1'); exact Ex2).
      assert (ECy : (φ ((Cq.[nx + d <- Cq.[x] + 1]).[nx + d])) = ((φ (C.[x])) + 1)%Z).
      { rewrite aget_set_same by (apply Hyb; exact C1'). rewrite Ex3.
        rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia. }
      destruct (good_frame _ _ _ _ _ _ _ _ _ ((φ nx) + Z.of_nat dn + 1)%Z Ag2 ltac:(lia) G1) as [G1' M1'].
      destruct (good_frame _ _ _ _ _ _ _ _ _ (φ nx) Ag1 ltac:(lia) GR) as [GR1 MR1].
      destruct (good_frame _ _ _ _ _ _ _ _ _ (φ nx) Ag2 ltac:(lia) GR1) as [GR2 MR2].
      split; [rewrite alength_set; exact L1|].
      split; [rewrite alength_set; exact R1'|].
      split; [rewrite alength_set; exact C1'|].
      split; [apply agree_trans with Lq Rq Cq; [exact Ag1 | apply agree_weaken with ((φ nx) + Z.of_nat dn + 1)%Z; [exact Ag2 | lia]]|].
      split.
      * cbn [good]. rewrite EL, ER. split; [lia|]. split.
        -- rewrite ECy. destruct (Ag2 (nx + (d - 1)) ltac:(lia)) as (_ & _ & E1).
           destruct (Ag2 (R.[x]) ltac:(lia)) as (_ & _ & E2).
           rewrite E1, E2, EC1, ExR. lia.
        -- split; eapply good_mono; eauto; lia.
      * split; [exact ECy|].
        intros w Hw. cbn [mult]. rewrite EL, ER.
        destruct (w <? 2 ^ Z.of_nat dn)%Z eqn:Ew.
        -- rewrite Z.ltb_lt in Ew. rewrite M1', M1 by lia. reflexivity.
        -- rewrite Z.ltb_ge in Ew. rewrite MR2, MR1.
           replace (w =? (φ v))%Z with false by (symmetry; apply Z.eqb_neq; lia). lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, Hhalf in Ev.
      assert (Hv' : (φ (v - (1 << (d - 1)))) = ((φ v) - 2 ^ Z.of_nat dn)%Z)
        by (rewrite sub_spec, Hhalf, Z.mod_small; rewrite ?wB_val; lia).
      specialize (IH L R C nx (R.[x]) (d - 1) (v - (1 << (d - 1))) (Acc_inv H (dec_d d Hdd)) Ed1
                     ltac:(lia) HRL HCL Hnx ltac:(lia) GR ltac:(lia) ltac:(lia)).
      destruct (ins L R C nx R.[x] (d - 1) (v - (1 << (d - 1))) (Acc_inv H (dec_d d Hdd)))
        as [[Lq Rq] Cq].
      destruct IH as (L1 & R1' & C1' & Ag1 & G1 & EC1 & M1).
      destruct (Ag1 x Hx) as (Ex1 & Ex2 & Ex3).
      destruct (Ag1 (L.[x]) BLx) as (_ & _ & ExL).
      assert (Hyb : forall (A : array int), PArray.length A = PArray.length L ->
                 (nx + d <? PArray.length A) = true)
        by (intros A HA; rewrite ltb_spec, HA; lia).
      assert (Ag2 : agree Lq Rq Cq (Lq.[nx + d <- Lq.[x]]) (Rq.[nx + d <- nx + (d - 1)])
                       (Cq.[nx + d <- Cq.[x] + 1]) ((φ nx) + Z.of_nat dn + 1))
        by (apply agree_set; lia).
      assert (EL : (Lq.[nx + d <- Lq.[x]]).[nx + d] = L.[x])
        by (rewrite aget_set_same by (apply Hyb; exact L1); exact Ex1).
      assert (ER : (Rq.[nx + d <- nx + (d - 1)]).[nx + d] = nx + (d - 1))
        by (apply aget_set_same, Hyb, R1').
      assert (ECy : (φ ((Cq.[nx + d <- Cq.[x] + 1]).[nx + d])) = ((φ (C.[x])) + 1)%Z).
      { rewrite aget_set_same by (apply Hyb; exact C1'). rewrite Ex3.
        rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia. }
      destruct (good_frame _ _ _ _ _ _ _ _ _ ((φ nx) + Z.of_nat dn + 1)%Z Ag2 ltac:(lia) G1) as [G1' M1'].
      destruct (good_frame _ _ _ _ _ _ _ _ _ (φ nx) Ag1 ltac:(lia) GL) as [GL1 ML1].
      destruct (good_frame _ _ _ _ _ _ _ _ _ (φ nx) Ag2 ltac:(lia) GL1) as [GL2 ML2].
      split; [rewrite alength_set; exact L1|].
      split; [rewrite alength_set; exact R1'|].
      split; [rewrite alength_set; exact C1'|].
      split; [apply agree_trans with Lq Rq Cq; [exact Ag1 | apply agree_weaken with ((φ nx) + Z.of_nat dn + 1)%Z; [exact Ag2 | lia]]|].
      split.
      * cbn [good]. rewrite EL, ER. split; [lia|]. split.
        -- rewrite ECy. destruct (Ag2 (nx + (d - 1)) ltac:(lia)) as (_ & _ & E1).
           destruct (Ag2 (L.[x]) ltac:(lia)) as (_ & _ & E2).
           rewrite E1, E2, EC1, ExL. lia.
        -- split; eapply good_mono; eauto; lia.
      * split; [exact ECy|].
        intros w Hw. cbn [mult]. rewrite EL, ER.
        destruct (w <? 2 ^ Z.of_nat dn)%Z eqn:Ew.
        -- rewrite Z.ltb_lt in Ew. rewrite ML2, ML1.
           replace (w =? (φ v))%Z with false by (symmetry; apply Z.eqb_neq; lia). lia.
        -- rewrite Z.ltb_ge in Ew. rewrite M1', M1 by lia. rewrite Hv'.
           destruct (Z.eqb_spec (w - 2 ^ Z.of_nat dn) ((φ v) - 2 ^ Z.of_nat dn)),
                    (Z.eqb_spec w (φ v)); lia.
Qed.

Definition qpost (L R C : array int) (a b : int) (dn : nat) (k r : int) : Prop :=
  (0 <= (φ r) < 2 ^ Z.of_nat dn)%Z /\
  (sumz (fun w => mult L R C b dn w - mult L R C a dn w)%Z (Z.to_nat (φ r)) < (φ k) <=
   sumz (fun w => mult L R C b dn w - mult L R C a dn w)%Z (S (Z.to_nat (φ r))))%Z.

Lemma diff_sum : forall L R C a b dn bnd, good L R C a dn bnd -> good L R C b dn bnd ->
  ((φ (C.[b])) - (φ (C.[a])))%Z =
  sumz (fun w => mult L R C b dn w - mult L R C a dn w)%Z (2 ^ dn)%nat.
Proof.
  intros L R C a b dn bnd Ga Gb. rewrite sumz_sub, <- (good_sum _ _ _ _ _ _ Ga),
    <- (good_sum _ _ _ _ _ _ Gb). reflexivity.
Qed.

Lemma qry_spec : forall dn L R C a b d k H bnd,
  (φ d) = Z.of_nat dn -> (dn <= 20)%nat ->
  good L R C a dn bnd -> good L R C b dn bnd ->
  (forall w, (0 <= w < 2 ^ Z.of_nat dn)%Z -> mult L R C a dn w <= mult L R C b dn w)%Z ->
  (1 <= (φ k) <= (φ (C.[b])) - (φ (C.[a])))%Z ->
  qpost L R C a b dn k (qry L R C a b d k H).
Proof.
  induction dn as [|dn IH]; intros L R C a b d k H bnd Hd Hdn Ga Gb Hle Hk; rewrite qry_eq.
  - assert (Ed : d = 0) by (apply to_Z_inj; rewrite Hd; reflexivity). subst d.
    destruct (bdec (0 <? 0)) as [F | _]; [discriminate|].
    unfold qpost. change (φ 0) with 0%Z. simpl. lia.
  - assert (Hdd0 : (0 <? d) = true) by (rewrite ltb_spec; change (φ 0) with 0%Z; lia).
    destruct (bdec (0 <? d)) as [Hdd | F]; [|congruence].
    cbv zeta.
    assert (Hhalf : (φ (1 << (d - 1))) = (2 ^ Z.of_nat dn)%Z)
      by (rewrite half_spec by lia; f_equal; lia).
    assert (Ed1 : (φ (d - 1)) = Z.of_nat dn) by sia.
    assert (Hp2 := pow2_S dn).
    assert (Hp2n := pow2_nat dn).
    assert (Hpos : (0 < 2 ^ Z.of_nat dn)%Z) by (apply Z.pow_pos_nonneg; lia).
    assert (Hp20 : (2 ^ Z.of_nat dn <= 2 ^ 20)%Z) by (apply Z.pow_le_mono_r; lia).
    pose proof Ga as Ga'. pose proof Gb as Gb'.
    cbn [good] in Ga', Gb'.
    destruct Ga' as (_ & Hca & GLa & GRa). destruct Gb' as (_ & Hcb & GLb & GRb).
    set (f := fun w => (mult L R C b (S dn) w - mult L R C a (S dn) w)%Z).
    set (fL := fun w => (mult L R C (L.[b]) dn w - mult L R C (L.[a]) dn w)%Z).
    set (fR := fun w => (mult L R C (R.[b]) dn w - mult L R C (R.[a]) dn w)%Z).
    assert (EfL : forall j, (j < 2 ^ dn)%nat -> f (Z.of_nat j) = fL (Z.of_nat j)).
    { intros j Hj. unfold f, fL. cbn [mult].
      replace (Z.of_nat j <? 2 ^ Z.of_nat dn)%Z with true by (symmetry; apply Z.ltb_lt; lia).
      reflexivity. }
    assert (EfR : forall j, (Z.of_nat j < 2 ^ Z.of_nat dn)%Z ->
              f (Z.of_nat j + Z.of_nat (2 ^ dn))%Z = fR (Z.of_nat j)).
    { intros j Hj. unfold f, fR. cbn [mult]. rewrite Hp2n.
      replace (Z.of_nat j + 2 ^ Z.of_nat dn <? 2 ^ Z.of_nat dn)%Z with false
        by (symmetry; apply Z.ltb_ge; lia).
      replace (Z.of_nat j + 2 ^ Z.of_nat dn - 2 ^ Z.of_nat dn)%Z with (Z.of_nat j) by lia.
      reflexivity. }
    assert (SL := diff_sum L R C (L.[a]) (L.[b]) dn bnd GLa GLb). fold fL in SL.
    assert (SR := diff_sum L R C (R.[a]) (R.[b]) dn bnd GRa GRb). fold fR in SR.
    assert (HleL : forall w, (0 <= w < 2 ^ Z.of_nat dn)%Z ->
              (mult L R C (L.[a]) dn w <= mult L R C (L.[b]) dn w)%Z).
    { intros w Hw. pose proof (Hle w ltac:(lia)) as T. cbn [mult] in T.
      replace (w <? 2 ^ Z.of_nat dn)%Z with true in T by (symmetry; apply Z.ltb_lt; lia).
      exact T. }
    assert (HleR : forall w, (0 <= w < 2 ^ Z.of_nat dn)%Z ->
              (mult L R C (R.[a]) dn w <= mult L R C (R.[b]) dn w)%Z).
    { intros w Hw. pose proof (Hle (w + 2 ^ Z.of_nat dn)%Z ltac:(lia)) as T. cbn [mult] in T.
      replace (w + 2 ^ Z.of_nat dn <? 2 ^ Z.of_nat dn)%Z with false in T
        by (symmetry; apply Z.ltb_ge; lia).
      replace (w + 2 ^ Z.of_nat dn - 2 ^ Z.of_nat dn)%Z with w in T by lia. exact T. }
    assert (NL : (0 <= sumz fL (2 ^ dn))%Z).
    { apply sumz_nonneg. intros j Hj. unfold fL. pose proof (HleL (Z.of_nat j) ltac:(lia)). lia. }
    assert (NR : (0 <= sumz fR (2 ^ dn))%Z).
    { apply sumz_nonneg. intros j Hj. unfold fR. pose proof (HleR (Z.of_nat j) ltac:(lia)). lia. }
    assert (Ecl : (φ (C.[L.[b]] - C.[L.[a]])) = ((φ (C.[L.[b]])) - (φ (C.[L.[a]])))%Z).
    { rewrite sub_spec, Z.mod_small; [reflexivity|].
      pose proof (to_Z_bounded (C.[L.[b]])). pose proof (to_Z_bounded (C.[L.[a]])). lia. }
    assert (Ef2 : sumz f (2 ^ dn) = sumz fL (2 ^ dn)) by (apply sumz_ext; exact EfL).
    destruct (k <=? C.[L.[b]] - C.[L.[a]]) eqn:Ek.
    + rewrite leb_spec, Ecl in Ek.
      destruct (IH L R C (L.[a]) (L.[b]) (d - 1) k (Acc_inv H (dec_d d Hdd)) bnd Ed1 ltac:(lia)
                  GLa GLb HleL ltac:(lia)) as [Hr [Hs1 Hs2]].
      fold fL in Hs1, Hs2.
      unfold qpost. fold f. split; [lia|].
      rewrite !(sumz_ext f fL) by (intros j Hj; apply EfL; lia). lia.
    + rewrite <- Bool.not_true_iff_false, leb_spec, Ecl in Ek.
      assert (Ekc : (φ (k - (C.[L.[b]] - C.[L.[a]]))) = ((φ k) - ((φ (C.[L.[b]])) - (φ (C.[L.[a]]))))%Z)
        by (rewrite sub_spec, Ecl, Z.mod_small; pose proof (to_Z_bounded k); lia).
      destruct (IH L R C (R.[a]) (R.[b]) (d - 1) (k - (C.[L.[b]] - C.[L.[a]]))
                  (Acc_inv H (dec_d d Hdd)) bnd Ed1 ltac:(lia) GRa GRb HleR ltac:(lia))
        as [Hr [Hs1 Hs2]].
      fold fR in Hs1, Hs2. rewrite Ekc in Hs1, Hs2.
      set (r' := qry L R C R.[a] R.[b] (d - 1) (k - (C.[L.[b]] - C.[L.[a]]))
                   (Acc_inv H (dec_d d Hdd))) in *.
      assert (Er : (φ ((1 << (d - 1)) + r')) = (2 ^ Z.of_nat dn + (φ r'))%Z)
        by (rewrite add_spec, Hhalf, Z.mod_small; rewrite ?wB_val; lia).
      unfold qpost. fold f. rewrite Er. split; [lia|].
      replace (Z.to_nat (2 ^ Z.of_nat dn + (φ r'))) with (2 ^ dn + Z.to_nat (φ r'))%nat by lia.
      replace (S (2 ^ dn + Z.to_nat (φ r'))) with (2 ^ dn + S (Z.to_nat (φ r')))%nat by lia.
      rewrite !sumz_split, Ef2.
      rewrite !(sumz_ext (fun w => f (w + Z.of_nat (2 ^ dn))%Z) fR)
        by (intros j Hj; apply EfR; lia).
      lia.
Qed.

Lemma depth_loop_eq : forall n d H,
  depth_loop n d H =
  match bdec (d <? 20) with
  | left Hd => if (1 << d) <? n then depth_loop n (d + 1) (Acc_inv H (dec_step 20 d Hd)) else d
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma build_eq : forall sa L R C roots n D i nx H,
  build sa L R C roots n D i nx H =
  match bdec (i <? n) with
  | left Hi =>
      let '(Lq, Rq, Cq) := ins L R C nx roots.[i] D sa.[i] (Zwf_well_founded 0 (φ D)) in
      build sa Lq Rq Cq roots.[i + 1 <- nx + D] n D (i + 1) (nx + D + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => (L, R, C, roots)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pow_lsl : forall d : int, ((φ d) <= 20)%Z -> (φ (1 << d)) = (2 ^ (φ d))%Z.
Proof.
  intros d H. rewrite lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
  pose proof (to_Z_bounded d).
  apply Z.mod_small. split; [apply Z.pow_nonneg; lia|].
  assert (2 ^ (φ d) <= 2 ^ 20)%Z by (apply Z.pow_le_mono_r; lia).
  rewrite wB_val. lia.
Qed.

Lemma depth_spec : forall n z d H, gap 20 d = z ->
  (1 <= (φ n) <= 200000)%Z -> ((φ d) <= 20)%Z ->
  ((φ d) = 0 \/ 2 ^ ((φ d) - 1) < (φ n))%Z ->
  ((φ (depth_loop n d H)) <= 18 /\ (φ n) <= 2 ^ (φ (depth_loop n d H)))%Z.
Proof.
  intros n z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d H Hz Hn Hd Hinv. rewrite depth_loop_eq.
  assert (P18 : (19 <= (φ d))%Z -> (2 ^ 18 <= 2 ^ ((φ d) - 1))%Z)
    by (intros; apply Z.pow_le_mono_r; lia).
  change (2 ^ 18)%Z with 262144%Z in P18.
  destruct (bdec (d <? 20)) as [Hd20 | Hd20].
  - pose proof Hd20 as Hd20'. rewrite ltb_spec in Hd20'. change (φ 20) with 20%Z in Hd20'.
    destruct ((1 << d) <? n) eqn:E.
    + rewrite ltb_spec, pow_lsl in E by lia.
      assert (Hd1 : (φ (d + 1)) = ((φ d) + 1)%Z) by sia.
      apply (IH (gap 20 (d + 1))); [rewrite <- Hz; apply dec_step; exact Hd20 | reflexivity
            | lia | lia | ].
      right. rewrite Hd1. replace ((φ d) + 1 - 1)%Z with (φ d) by lia. exact E.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, pow_lsl in E by lia.
      split; [|lia]. destruct (Z_le_dec (φ d) 18); [lia|]. exfalso.
      destruct Hinv; [lia|]. pose proof (P18 ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hd20. change (φ 20) with 20%Z in Hd20.
    exfalso. destruct Hinv; [lia|]. pose proof (P18 ltac:(lia)). lia.
Qed.

Definition roots_inv (sa L R C roots : array int) (Dn : nat) (j : int) (bnd : Z) : Prop :=
  good L R C (roots.[j]) Dn bnd /\ (φ (C.[roots.[j]])) = (φ j) /\
  forall w, (0 <= w < 2 ^ Z.of_nat Dn)%Z ->
    mult L R C (roots.[j]) Dn w = cnt sa (of_Z w) 0 (Z.to_nat (φ j)).

Lemma cnt_succ_w : forall (sa : array int) (i : int) (w : Z), (0 <= w < 2 ^ 20)%Z ->
  ((φ i) < 4194303)%Z ->
  cnt sa (of_Z w) 0 (Z.to_nat (φ (i + 1))) =
  (cnt sa (of_Z w) 0 (Z.to_nat (φ i)) + (if (w =? (φ (sa.[i])))%Z then 1 else 0))%Z.
Proof.
  intros sa i w Hw Hi. pose proof (to_Z_bounded i).
  replace (Z.to_nat (φ (i + 1))) with (S (Z.to_nat (φ i))) by sia.
  cbn [cnt]. rewrite Z.add_0_l, Z2Nat.id, of_to_Z by lia. f_equal.
  assert (Ew : (φ (of_Z w)) = w) by (apply phi_of_Z; rewrite wB_val; lia).
  destruct (Uint63.eqb sa.[i] (of_Z w)) eqn:E.
  - rewrite Uint63.eqb_spec in E. rewrite E, Ew, Z.eqb_refl. reflexivity.
  - rewrite Uint63.eqb_false_spec in E. destruct (Z.eqb_spec w (φ (sa.[i]))) as [F|]; [|reflexivity].
    exfalso. apply E. apply to_Z_inj. rewrite Ew. symmetry. exact F.
Qed.

Lemma build_spec : forall (sa : array int) (n D : int) (Dn : nat),
  (1 <= (φ n) <= 200000)%Z -> (φ D) = Z.of_nat Dn -> (Dn <= 18)%nat ->
  ((φ n) <= 2 ^ Z.of_nat Dn)%Z ->
  (forall i : int, ((φ i) < (φ n))%Z -> ((φ (sa.[i])) < (φ n))%Z) ->
  forall z i nx L R C roots H, gap n i = z ->
  PArray.length R = PArray.length L -> PArray.length C = PArray.length L ->
  (φ (PArray.length L)) = (1 + (φ n) * (Z.of_nat Dn + 1))%Z ->
  (φ (PArray.length roots)) = ((φ n) + 1)%Z ->
  ((φ i) <= (φ n))%Z -> (φ nx) = (1 + (φ i) * (Z.of_nat Dn + 1))%Z ->
  (forall j : int, ((φ j) <= (φ i))%Z -> roots_inv sa L R C roots Dn j (φ nx)) ->
  match build sa L R C roots n D i nx H with
  | (L', R', C', roots') =>
    forall j : int, ((φ j) <= (φ n))%Z ->
      roots_inv sa L' R' C' roots' Dn j (1 + (φ n) * (Z.of_nat Dn + 1))
  end.
Proof.
  intros sa n D Dn Hn HD HDn Hpow Hsa z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i nx L R C roots H Hz HRL HCL HL Hr Hi Hnx Hinv. rewrite build_eq.
  pose proof (alength_bound L) as BL.
  destruct (bdec (i <? n)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hi1 := succ_phi i n Hin').
    destruct (Hinv i ltac:(lia)) as (Gi & Ci & Mi).
    pose proof (Hsa i Hin') as Bs.
    pose proof (to_Z_bounded (sa.[i])).
    assert (Hlen : ((φ nx) + Z.of_nat Dn < (φ (PArray.length L)))%Z).
    { rewrite HL, Hnx.
      assert (((φ i) + 1) * (Z.of_nat Dn + 1) <= (φ n) * (Z.of_nat Dn + 1))%Z
        by (apply Z.mul_le_mono_nonneg_r; lia).
      lia. }
    pose proof (ins_spec Dn L R C nx (roots.[i]) D (sa.[i]) (Zwf_well_founded 0 (φ D)) HD
                  ltac:(lia) HRL HCL ltac:(lia) Hlen Gi ltac:(lia) ltac:(lia)) as Hins.
    destruct (ins L R C nx roots.[i] D sa.[i] (Zwf_well_founded 0 (φ D))) as [[Lq Rq] Cq].
    destruct Hins as (L1 & R1 & C1' & Ag & G & EC & M).
    assert (EnD : (φ (nx + D)) = ((φ nx) + Z.of_nat Dn)%Z) by sia.
    assert (EnD1 : (φ (nx + D + 1)) = ((φ nx) + Z.of_nat Dn + 1)%Z) by sia.
    assert (Hrb : (i + 1 <? PArray.length roots) = true) by (rewrite ltb_spec, Hr; lia).
    apply (IH (gap n (i + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
          | lia | lia | lia | rewrite alength_set; exact Hr | lia | rewrite EnD1, Hi1, Hnx; lia | ].
    intros j Hj. rewrite Hi1 in Hj. rewrite EnD1.
    destruct (Z.eq_dec (φ j) ((φ i) + 1)) as [Ej | Ej].
    + assert (Ej' : j = i + 1) by (apply to_Z_inj; lia). subst j.
      unfold roots_inv. rewrite aget_set_same by exact Hrb.
      split; [exact G|]. split; [rewrite EC, Ci, Hi1; reflexivity|].
      intros w Hw. rewrite M by exact Hw. rewrite Mi by exact Hw.
      rewrite cnt_succ_w; [reflexivity | | lia].
      assert (2 ^ Z.of_nat Dn <= 2 ^ 20)%Z by (apply Z.pow_le_mono_r; lia). lia.
    + destruct (Hinv j ltac:(lia)) as (Gj & Cj & Mj).
      unfold roots_inv. rewrite aget_set_other by (intro F; subst; lia).
      destruct (good_frame _ _ _ _ _ _ _ _ _ (φ nx) Ag ltac:(lia) Gj) as [Gj' Mj'].
      split; [eapply good_mono; [exact Gj' | lia]|].
      split.
      * destruct (Ag (roots.[j]) (good_lt _ _ _ _ _ _ Gj)) as (_ & _ & E). rewrite E. exact Cj.
      * intros w Hw. rewrite Mj'. apply Mj. exact Hw.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    intros j Hj. assert (Ein : (φ i) = (φ n)) by lia.
    replace (1 + (φ n) * (Z.of_nat Dn + 1))%Z with (φ nx) by (rewrite Hnx, Ein; reflexivity).
    apply Hinv. lia.
Qed.

(* --- list facts --- *)

Lemma filter_all_false : forall (P : nat -> bool) l,
  (forall x, In x l -> P x = false) -> filter P l = [].
Proof.
  intros P l. induction l as [|a l IH]; intros H; [reflexivity|].
  cbn [filter]. rewrite H by (left; reflexivity). apply IH. intros x Hx. apply H. right. exact Hx.
Qed.

Lemma sumz_filter : forall f (P : nat -> bool) m,
  (forall j, (j < m)%nat -> f (Z.of_nat j) = if P j then 1%Z else 0%Z) ->
  sumz f m = Z.of_nat (List.length (filter P (seq 0 m))).
Proof.
  intros f P m. induction m as [|m IH]; intros H; [reflexivity|].
  cbn [sumz]. rewrite seq_S, filter_app, length_app.
  rewrite IH by (intros; apply H; lia). rewrite H by lia. simpl. destruct (P m); simpl; lia.
Qed.

Lemma filter_seq_ext : forall (P : nat -> bool) N M, (N <= M)%nat ->
  (forall j, (N <= j)%nat -> P j = false) ->
  filter P (seq 0 M) = filter P (seq 0 N).
Proof.
  intros P N M HNM H. replace M with (N + (M - N))%nat by lia.
  rewrite seq_app, filter_app.
  rewrite (filter_all_false P (seq (0 + N) (M - N))); [apply app_nil_r|].
  intros x Hx. apply in_seq in Hx. apply H. lia.
Qed.

Lemma nth_filter_seq : forall (P : nat -> bool) N r, (r < N)%nat -> P r = true ->
  nth_error (filter P (seq 0 N)) (List.length (filter P (seq 0 r))) = Some r.
Proof.
  intros P N r Hr Hp. replace N with (r + S (N - r - 1))%nat by lia.
  rewrite seq_app, filter_app, nth_error_app2 by lia. rewrite Nat.sub_diag, Nat.add_0_l.
  cbn [seq filter]. rewrite Hp. reflexivity.
Qed.

Lemma cnt_unique : forall (a : array int) v (lo : Z) len (j0 : Z),
  (0 <= lo)%Z -> (lo + Z.of_nat len <= 4194303)%Z ->
  (forall j : nat, (j < len)%nat -> (a.[of_Z (lo + Z.of_nat j)] = v <-> lo + Z.of_nat j = j0)%Z) ->
  cnt a v lo len = if andb (lo <=? j0)%Z (j0 <? lo + Z.of_nat len)%Z then 1%Z else 0%Z.
Proof.
  intros a v lo len j0 Hlo. induction len as [|l IH]; intros Hb H.
  - cbn [cnt]. destruct (Z.leb_spec lo j0), (Z.ltb_spec j0 (lo + Z.of_nat 0)); simpl; lia.
  - cbn [cnt]. rewrite IH by (try lia; intros; apply H; lia).
    rewrite Nat2Z.inj_succ.
    destruct (Uint63.eqb a.[of_Z (lo + Z.of_nat l)] v) eqn:Ev.
    + rewrite Uint63.eqb_spec in Ev. apply H in Ev; [|lia].
      destruct (Z.leb_spec lo j0), (Z.ltb_spec j0 (lo + Z.of_nat l)),
               (Z.ltb_spec j0 (lo + Z.succ (Z.of_nat l))); simpl; lia.
    + rewrite Uint63.eqb_false_spec in Ev.
      assert (j0 <> lo + Z.of_nat l)%Z by (intro F; apply Ev; apply H; lia).
      destruct (Z.leb_spec lo j0), (Z.ltb_spec j0 (lo + Z.of_nat l)),
               (Z.ltb_spec j0 (lo + Z.succ (Z.of_nat l))); simpl; lia.
Qed.

Lemma starts_at_beyond : forall s t p, (0 < String.length t)%nat -> (String.length s <= p)%nat ->
  starts_at s t p = false.
Proof.
  intros s t p Ht Hp. unfold starts_at.
  replace (p + String.length t <=? String.length s)%nat with false by (symmetry; apply Nat.leb_gt; lia).
  reflexivity.
Qed.

Lemma starts_at_lt : forall s t p, starts_at s t p = true -> (p + String.length t <= String.length s)%nat.
Proof.
  intros s t p H. unfold starts_at in H. apply andb_prop in H. apply Nat.leb_le. apply H.
Qed.

Lemma sint_small : forall r : int, ((φ r) < 4611686018427387904)%Z -> Sint63.to_Z r = (φ r).
Proof.
  intros r H. rewrite Sint63.to_Z_cmodwB. apply Sint63.cmod_small.
  pose proof (to_Z_bounded r). rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z.
  lia.
Qed.

Section Answer.
  Variables (x : PrimString.string) (s : string) (n : int) (sa L R C roots : array int).
  Variables (D : int) (Dn : nat) (bnd : Z).
  Hypothesis Hx : repr x s.
  Hypothesis Hn : (φ n) = Z.of_nat (String.length s).
  Hypothesis Bn : (1 <= (φ n) <= 200000)%Z.
  Hypothesis Hsa : sa_ok (codes s) n sa.
  Hypothesis HD : (φ D) = Z.of_nat Dn.
  Hypothesis HDn : (Dn <= 18)%nat.
  Hypothesis Hpow : ((φ n) <= 2 ^ Z.of_nat Dn)%Z.
  Hypothesis Hroots : forall j : int, ((φ j) <= (φ n))%Z -> roots_inv sa L R C roots Dn j bnd.

  Lemma sa_range : forall i : int, ((φ i) < (φ n))%Z -> ((φ (sa.[i])) < (φ n))%Z.
  Proof.
    intros i Hi. destruct Hsa as (_ & Ps & _). rewrite <- at_idx.
    apply perm_range with (n := (φ n)); [exact Ps | pose proof (to_Z_bounded i); lia].
  Qed.

  Lemma sa_sorted : forall i j : int, ((φ i) <= (φ j) < (φ n))%Z ->
    lexle (sufZ (codes s) (φ (sa.[i]))) (sufZ (codes s) (φ (sa.[j]))).
  Proof.
    intros i j Hij. destruct Hsa as (_ & _ & Ss).
    pose proof (sorted_all (sufle (codes s)) (sufle_total (codes s)) (sufle_trans (codes s))
                  sa 0 n Ss i j ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded i); lia)
                  ltac:(lia) ltac:(lia)) as T.
    unfold sufle in T. unfold lexle. destruct (lexcmp _ _); congruence.
  Qed.

  Lemma answer1_spec : forall (t : PrimString.string) (tt : string) (k : int),
    repr t tt -> (1 <= Z.of_nat (String.length tt) <= 200000)%Z ->
    (1 <= (φ k) <= (φ n))%Z ->
    Sint63.to_Z (answer1 x n sa L R C roots D t k) = answer s tt (Z.to_N (φ k)).
  Proof.
    intros t tt k Ht Btt Hk. unfold answer1. cbv zeta.
    set (m := PrimString.length t).
    assert (Hm : (φ m) = Z.of_nat (String.length tt)) by (apply repr_str_len; exact Ht).
    set (W := fun i : int => firstn (String.length tt) (sufZ (codes s) (φ (sa.[i])))).
    assert (HPc : forall i : int, ((φ i) < (φ n))%Z -> cmp_at x t n m sa i = lexcmp (codes tt) (W i)).
    { intros i Hi. unfold cmp_at, W, sufZ. pose proof (sa_range i Hi).
      rewrite (cmpt_spec x t s tt Hx Ht n m (sa.[i]) Hn Hm ltac:(lia) ltac:(lia) ltac:(lia)
                 (gap m 0) 0 _ eq_refl ltac:(change (φ 0) with 0%Z; lia)).
      change (φ 0) with 0%Z. rewrite Z.sub_0_r, Z.add_0_r, Hm, Nat2Z.id. reflexivity. }
    set (P1 := fun i => match cmp_at x t n m sa i with Gt => false | _ => true end).
    set (P2 := fun i => match cmp_at x t n m sa i with Lt => true | _ => false end).
    assert (EP1 : forall i, ((φ i) < (φ n))%Z -> P1 i = true <-> lexle (codes tt) (W i)).
    { intros i Hi. unfold P1. rewrite HPc by exact Hi. unfold lexle.
      destruct (lexcmp _ _); split; congruence. }
    assert (EP2 : forall i, ((φ i) < (φ n))%Z -> P2 i = true <-> ~ lexle (W i) (codes tt)).
    { intros i Hi. unfold P2. rewrite HPc by exact Hi. rewrite <- lexcmp_lt_iff.
      destruct (lexcmp _ _); split; congruence. }
    assert (HW : forall i j : int, ((φ i) <= (φ j) < (φ n))%Z -> lexle (W i) (W j))
      by (intros i j Hij; apply lexle_firstn, sa_sorted; exact Hij).
    assert (M1 : forall i j : int, ((φ i) <= (φ j) < (φ n))%Z -> P1 i = true -> P1 j = true).
    { intros i j Hij H. rewrite EP1 in H |- * by lia. eapply lexle_trans; [exact H | apply HW; lia]. }
    assert (M2 : forall i j : int, ((φ i) <= (φ j) < (φ n))%Z -> P2 i = true -> P2 j = true).
    { intros i j Hij H. rewrite EP2 in H |- * by lia. intros F. apply H.
      eapply lexle_trans; [apply HW; exact Hij | exact F]. }
    assert (Hneg : forall i : int, ((φ i) < (φ 0))%Z -> forall P : int -> bool, P i = false)
      by (intros i Hi; change (φ 0) with 0%Z in Hi; pose proof (to_Z_bounded i); lia).
    destruct (bs_spec P1 n M1 (gap n 0) 0 n (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) (fun i Hi => Hneg i Hi P1)
                ltac:(intros i Hi; lia)) as [Blo Ilo].
    destruct (bs_spec P2 n M2 (gap n 0) 0 n (Zwf_well_founded 0 (gap n 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) (fun i Hi => Hneg i Hi P2)
                ltac:(intros i Hi; lia)) as [Bhi Ihi].
    set (lo := bs P1 0 n (Zwf_well_founded 0 (gap n 0))) in *.
    set (hi := bs P2 0 n (Zwf_well_founded 0 (gap n 0))) in *.
    assert (Hlohi : ((φ lo) <= (φ hi))%Z).
    { destruct (Z_lt_le_dec (φ hi) (φ n)) as [Hh | Hh]; [|lia].
      assert (P2 hi = true) by (apply Ihi; lia).
      assert (P1 hi = true).
      { unfold P1. unfold P2 in H. destruct (cmp_at x t n m sa hi); congruence. }
      apply Ilo in H0; [exact H0 | exact Hh]. }
    assert (Hin : forall i : int, ((φ i) < (φ n))%Z ->
              (((φ lo) <= (φ i) < (φ hi))%Z <-> starts_at s tt (Z.to_nat (φ (sa.[i]))) = true)).
    { intros i Hi. rewrite starts_at_iff by lia.
      assert (E : ((φ lo) <= (φ i) < (φ hi))%Z <-> (P1 i = true /\ P2 i = false)).
      { rewrite (Ilo i Hi). rewrite <- Bool.not_true_iff_false, (Ihi i Hi). lia. }
      rewrite E. unfold P1, P2. rewrite HPc by exact Hi. unfold W, sufZ.
      destruct (lexcmp (codes tt) _) eqn:Ec.
      - split; [intros _; symmetry; apply lexcmp_eq; exact Ec | intros _; split; reflexivity].
      - split; [intros [_ F]; discriminate | intros F; rewrite F, lexcmp_refl in Ec; discriminate].
      - split; [intros [F _]; discriminate | intros F; rewrite F, lexcmp_refl in Ec; discriminate]. }
    destruct (Hroots lo Blo) as (Glo & Clo & Mlo).
    destruct (Hroots hi Bhi) as (Ghi & Chi & Mhi).
    destruct Hsa as (Ls & Ps & _).
    set (occ := starts_at s tt).
    assert (Hp20 : (2 ^ Z.of_nat Dn <= 2 ^ 18)%Z) by (apply Z.pow_le_mono_r; lia).
    change (2 ^ 18)%Z with 262144%Z in Hp20.
    set (f := fun w => (mult L R C (roots.[hi]) Dn w - mult L R C (roots.[lo]) Dn w)%Z).
    assert (Hf : forall w, (0 <= w < 2 ^ Z.of_nat Dn)%Z ->
               f w = if occ (Z.to_nat w) then 1%Z else 0%Z).
    { intros w Hw. unfold f. rewrite Mhi, Mlo by exact Hw.
      pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
      replace (Z.to_nat (φ hi)) with (Z.to_nat (φ lo) + Z.to_nat ((φ hi) - (φ lo)))%nat by lia.
      rewrite cnt_split. rewrite Z2Nat.id by lia. rewrite Z.add_0_l.
      assert (Ew : (φ (of_Z w)) = w) by (apply phi_of_Z; rewrite wB_val; lia).
      destruct (Z_lt_le_dec w (φ n)) as [Hwn | Hwn].
      - destruct (perm_surj sa (φ n) Ps (of_Z w) ltac:(lia)) as (j0 & Hj0 & Ej0).
        rewrite (cnt_unique sa (of_Z w) (φ lo) (Z.to_nat ((φ hi) - (φ lo))) (Z.of_nat j0)); try lia.
        + assert (Hs0 := Hin (of_Z (Z.of_nat j0)) ltac:(rewrite phi_of_Z by (rewrite wB_val; lia); lia)).
          rewrite phi_of_Z in Hs0 by (rewrite wB_val; lia).
          unfold at_ in Ej0. rewrite Ej0, Ew in Hs0. fold occ in Hs0.
          destruct (occ (Z.to_nat w)) eqn:Eo.
          * assert (Hyes : ((φ lo) <= Z.of_nat j0 < (φ hi))%Z) by (apply Hs0; reflexivity).
            destruct (Z.leb_spec (φ lo) (Z.of_nat j0)),
              (Z.ltb_spec (Z.of_nat j0) ((φ lo) + Z.of_nat (Z.to_nat ((φ hi) - (φ lo))))); simpl; lia.
          * assert (Hno : ~ ((φ lo) <= Z.of_nat j0 < (φ hi))%Z) by (intros F; apply Hs0 in F; discriminate).
            destruct (Z.leb_spec (φ lo) (Z.of_nat j0)),
              (Z.ltb_spec (Z.of_nat j0) ((φ lo) + Z.of_nat (Z.to_nat ((φ hi) - (φ lo))))); simpl; lia.
        + intros j Hj. split.
          * intros E. assert (Ej : at_ sa (Z.to_nat ((φ lo) + Z.of_nat j)) = at_ sa j0).
            { unfold at_ in *. rewrite Z2Nat.id by lia. rewrite E. symmetry. exact Ej0. }
            apply (perm_inj sa (φ n) Ps) in Ej; lia.
          * intros E. rewrite E. unfold at_ in Ej0. exact Ej0.
      - rewrite (cnt_unique sa (of_Z w) (φ lo) (Z.to_nat ((φ hi) - (φ lo))) (-1)); try lia.
        + replace (((φ lo) <=? -1)%Z) with false by (symmetry; apply Z.leb_gt; lia). simpl.
          unfold occ. rewrite starts_at_beyond by lia. lia.
        + intros j Hj. split; [|lia]. intros E.
          pose proof (sa_range (of_Z ((φ lo) + Z.of_nat j))
                        ltac:(rewrite phi_of_Z by (rewrite wB_val; lia); lia)) as T.
          rewrite E, Ew in T. lia. }
    assert (Hcnt : forall M, (M <= 2 ^ Dn)%nat ->
              sumz f M = Z.of_nat (List.length (filter occ (seq 0 M)))).
    { intros M HM. apply sumz_filter. intros j Hj. rewrite Hf by (rewrite <- pow2_nat; lia).
      rewrite Nat2Z.id. reflexivity. }
    assert (Hall : filter occ (seq 0 (2 ^ Dn)) = filter occ (seq 0 (String.length s))).
    { apply filter_seq_ext; [apply Nat2Z.inj_le; rewrite pow2_nat; lia|].
      intros j Hj. apply starts_at_beyond; lia. }
    assert (Htot : ((φ hi) - (φ lo))%Z = Z.of_nat (List.length (filter occ (seq 0 (String.length s))))).
    { rewrite <- Chi, <- Clo. rewrite (diff_sum L R C (roots.[lo]) (roots.[hi]) Dn bnd Glo Ghi).
      fold f. rewrite Hcnt by lia. rewrite Hall. reflexivity. }
    assert (Ediff : (φ (hi - lo)) = ((φ hi) - (φ lo))%Z) by (rewrite sub_spec, Z.mod_small; pose proof (to_Z_bounded hi); lia).
    unfold answer, occurrences. fold occ.
    rewrite nth_error_map.
    destruct (k <=? hi - lo) eqn:Ek.
    - rewrite leb_spec, Ediff in Ek.
      assert (Hle : forall w, (0 <= w < 2 ^ Z.of_nat Dn)%Z ->
                (mult L R C (roots.[lo]) Dn w <= mult L R C (roots.[hi]) Dn w)%Z).
      { intros w Hw. pose proof (Hf w Hw). unfold f in H. destruct (occ _); lia. }
      destruct (qry_spec Dn L R C (roots.[lo]) (roots.[hi]) D k (Zwf_well_founded 0 (φ D)) bnd
                  HD ltac:(lia) Glo Ghi Hle ltac:(lia)) as [Hr [Hs1 Hs2]].
      fold f in Hs1, Hs2.
      set (r := qry L R C roots.[lo] roots.[hi] D k (Zwf_well_founded 0 (φ D))) in *.
      rewrite !Hcnt in Hs1, Hs2 by (apply Nat2Z.inj_le; rewrite pow2_nat; lia).
      rewrite seq_S, filter_app, length_app in Hs2. simpl in Hs2.
      destruct (occ (Z.to_nat (φ r))) eqn:Eo; simpl in Hs2; [|lia].
      pose proof (starts_at_lt s tt _ Eo).
      replace (N.to_nat (Z.to_N (φ k)) - 1)%nat with (List.length (filter occ (seq 0 (Z.to_nat (φ r))))) by lia.
      rewrite nth_filter_seq by (try lia; exact Eo). simpl.
      rewrite sint_small by (rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia).
      rewrite add_spec, Z.mod_small; change (φ 1) with 1%Z; rewrite ?wB_val; lia.
    - rewrite <- Bool.not_true_iff_false, leb_spec, Ediff in Ek.
      replace (nth_error (filter occ (seq 0 (String.length s))) (N.to_nat (Z.to_N (φ k)) - 1)) with
        (@None nat) by (symmetry; apply nth_error_None; lia).
      reflexivity.
  Qed.
End Answer.

Lemma qloop_eq : forall x n sa L R C roots D ts ks out q Q H,
  qloop x n sa L R C roots D ts ks out q Q H =
  match bdec (q <? Q) with
  | left Hq =>
      qloop x n sa L R C roots D ts ks
        out.[q <- answer1 x n sa L R C roots D ts.[q] ks.[q]] (q + 1) Q
        (Acc_inv H (dec_step Q q Hq))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma qloop_spec : forall x n sa L R C roots D ts ks Q z q out H, gap Q q = z ->
  PArray.length out = Q -> ((φ q) <= (φ Q))%Z ->
  (forall y : int, ((φ y) < (φ q))%Z -> out.[y] = answer1 x n sa L R C roots D ts.[y] ks.[y]) ->
  PArray.length (qloop x n sa L R C roots D ts ks out q Q H) = Q /\
  forall y : int, ((φ y) < (φ Q))%Z ->
    (qloop x n sa L R C roots D ts ks out q Q H).[y] = answer1 x n sa L R C roots D ts.[y] ks.[y].
Proof.
  intros x n sa L R C roots D ts ks Q z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q out H Hz Hl Hq Ha. rewrite qloop_eq.
  destruct (bdec (q <? Q)) as [Hin | Hin].
  - pose proof Hin as Hin'. rewrite ltb_spec in Hin'.
    assert (Hq1 := succ_phi q Q Hin').
    apply (IH (gap Q (q + 1))); [rewrite <- Hz; apply dec_step; exact Hin | reflexivity
          | rewrite alength_set; exact Hl | lia | ].
    intros y Hy. destruct (Z.eq_dec (φ y) (φ q)) as [E|E].
    + apply to_Z_inj in E. subst y. apply aget_set_same. rewrite Hl. exact Hin.
    + rewrite aget_set_other by (intro F; subst; lia). apply Ha. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hin.
    split; [exact Hl|]. intros y Hy. apply Ha. lia.
Qed.

Lemma total_len_in : forall ts t, In t ts -> (slen t <= total_len ts)%N.
Proof.
  induction ts as [|a ts IH]; intros t Ht; simpl in *; [contradiction|].
  destruct Ht as [E | Ht]; [subst; lia | pose proof (IH t Ht); lia].
Qed.

Lemma kth_occurrences_impl_correct :
  forall (s : string) (ts : list string) (ks : list N)
         (x : PrimString.string) (y : array PrimString.string) (z : array uint),
  valid_input s ts ks -> repr x s -> repr y ts -> repr z ks ->
  exists o : list Z, repr (kth_occurrences_impl x y z) o /\ kth_occurrences_spec s ts ks o.
Proof.
  intros s ts ks x y z Hv Hx Hy Hz.
  destruct Hv as [Vs _ Vq Vks Vt _ Vk Vsum].
  unfold slen, len in *.
  set (o := map (fun q => answer s (nth q ts EmptyString) (nth q ks 0%N)) (seq 0 (List.length ts))).
  exists o.
  unfold kth_occurrences_impl. cbv zeta.
  set (n := PrimString.length x).
  assert (Hn : (φ n) = Z.of_nat (String.length s)) by (apply repr_str_len; exact Hx).
  assert (Bn : (1 <= (φ n) <= 200000)%Z) by lia.
  assert (Hsa := build_sa_spec x s n Hx Hn ltac:(lia)).
  set (sa := build_sa x n) in *.
  destruct (depth_spec n (gap 20 0) 0 (Zwf_well_founded 0 (gap 20 0)) eq_refl Bn
              ltac:(change (φ 0) with 0%Z; lia) ltac:(left; reflexivity)) as [BD PD].
  set (D := depth_loop n 0 (Zwf_well_founded 0 (gap 20 0))) in *.
  set (Dn := Z.to_nat (φ D)).
  assert (HD : (φ D) = Z.of_nat Dn) by (unfold Dn; pose proof (to_Z_bounded D); lia).
  rewrite HD in PD.
  assert (HM0 : ((φ n) * ((φ D) + 1) <= 200000 * 19)%Z)
    by (apply Z.mul_le_mono_nonneg; pose proof (to_Z_bounded D); lia).
  assert (HM : (φ (n * (D + 1) + 1)) = (1 + (φ n) * (Z.of_nat Dn + 1))%Z).
  { assert (E1 : (φ (D + 1)) = ((φ D) + 1)%Z) by sia.
    rewrite add_spec, mul_spec, E1. change (φ 1) with 1%Z.
    rewrite (Z.mod_small ((φ n) * ((φ D) + 1))) by (rewrite wB_val; pose proof (to_Z_bounded D); nia).
    rewrite Z.mod_small by (rewrite wB_val; pose proof (to_Z_bounded D); nia). rewrite HD. lia. }
  set (M := n * (D + 1) + 1) in *.
  assert (LM : PArray.length (PArray.make M 0) = M) by (apply alength_make; rewrite HM; lia).
  assert (Hn1 : (φ (n + 1)) = ((φ n) + 1)%Z) by sia.
  assert (LR : PArray.length (PArray.make (n + 1) 0) = n + 1) by (apply alength_make; lia).
  destruct Hsa as (Ls & Ps & Ss) eqn:Hsa'.
  assert (Hrange : forall i : int, ((φ i) < (φ n))%Z -> ((φ (sa.[i])) < (φ n))%Z).
  { intros i Hi. rewrite <- at_idx. apply perm_range with (n := (φ n)); [exact Ps |].
    pose proof (to_Z_bounded i). lia. }
  pose proof (build_spec sa n D Dn Bn HD ltac:(lia) PD Hrange (gap n 0) 0 1
                (PArray.make M 0) (PArray.make M 0) (PArray.make M 0) (PArray.make (n + 1) 0)
                (Zwf_well_founded 0 (gap n 0)) eq_refl (eq_trans LM (eq_sym LM))
                (eq_trans LM (eq_sym LM)) ltac:(rewrite LM; exact HM) ltac:(rewrite LR; exact Hn1)
                ltac:(change (φ 0) with 0%Z; lia) ltac:(change (φ 0) with 0%Z; change (φ 1) with 1%Z; lia))
    as Hb.
  (* the initial invariant *)
  assert (Hinit : forall j : int, ((φ j) <= (φ 0))%Z ->
            roots_inv sa (PArray.make M 0) (PArray.make M 0) (PArray.make M 0)
              (PArray.make (n + 1) 0) Dn j (φ 1)).
  { intros j Hj. change (φ 0) with 0%Z in Hj. pose proof (to_Z_bounded j).
    assert (j = 0) by (apply to_Z_inj; change (φ 0) with 0%Z; lia). subst j.
    unfold roots_inv. rewrite !aget_make.
    destruct (good_zero (PArray.make M 0) (PArray.make M 0) (PArray.make M 0) (φ 1)
                (aget_make _ _ _) (aget_make _ _ _) (aget_make _ _ _) ltac:(change (φ 1) with 1%Z; lia) Dn)
      as [G0 M0].
    split; [exact G0|]. split; [reflexivity|]. intros w Hw. rewrite M0. reflexivity. }
  specialize (Hb Hinit).
  destruct (build sa (PArray.make M 0) (PArray.make M 0) (PArray.make M 0) (PArray.make (n + 1) 0)
              n D 0 1 (Zwf_well_founded 0 (gap n 0))) as [[[L R] C] roots].
  set (Q := PArray.length y).
  assert (BQ : ((φ Q) <= 4194303)%Z)
    by (pose proof (leb_length _ y) as HQ; rewrite leb_spec, max_length_val in HQ; exact HQ).
  assert (LQ : PArray.length (PArray.make Q 0) = Q) by (apply alength_make; exact BQ).
  assert (Hneg0 : forall y0 : int, ((φ y0) < (φ 0))%Z -> False).
  { intros y0 Hy0. change (φ 0) with 0%Z in Hy0.
    exact (Z.lt_irrefl _ (Z.le_lt_trans _ _ _ (proj1 (to_Z_bounded y0)) Hy0)). }
  pose proof (qloop_spec x n sa L R C roots D y z Q (gap Q 0) 0 (PArray.make Q 0)
              (Zwf_well_founded 0 (gap Q 0)) eq_refl LQ
              ltac:(change (φ 0) with 0%Z; exact (proj1 (to_Z_bounded Q)))
              (fun y0 Hy0 => False_ind _ (Hneg0 y0 Hy0)))
    as [Lo Co].
  set (out := qloop x n sa L R C roots D y z (PArray.make Q 0) 0 Q (Zwf_well_founded 0 (gap Q 0))) in *.
  destruct Hy as [Hyl Hyc]. destruct Hz as [Hzl Hzc].
  assert (HQ : (φ Q) = Z.of_nat (List.length ts)) by (symmetry; exact Hyl).
  assert (Hlo : List.length o = List.length ts) by (unfold o; rewrite length_map, length_seq; reflexivity).
  (* each cell *)
  assert (Hcell : forall q : nat, (q < List.length ts)%nat ->
            Sint63.to_Z (out.[of_Z (Z.of_nat q)]) = answer s (nth q ts EmptyString) (nth q ks 0%N)).
  { intros q Hq.
    destruct (Hyc q Hq) as (t & Et & Rt).
    destruct (Hzc q ltac:(lia)) as (k & Ek & Rk).
    assert (Eq : (φ (of_Z (Z.of_nat q))) = Z.of_nat q) by (apply phi_of_Z; rewrite wB_val; lia).
    rewrite Co by (rewrite Eq; lia).
    rewrite (nth_error_nth _ _ _ Et), (nth_error_nth _ _ _ Ek).
    unfold repr, repr_uint in Rk. rewrite <- Rk.
    assert (Tin : In t ts) by (eapply nth_error_In; exact Et).
    assert (Kin : In k ks) by (eapply nth_error_In; exact Ek).
    rewrite Forall_forall in Vt, Vk.
    pose proof (Vt t Tin). pose proof (Vk k Kin). pose proof (total_len_in ts t Tin).
    unfold slen in *.
    apply (answer1_spec x s n sa L R C roots D Dn (1 + (φ n) * (Z.of_nat Dn + 1)) Hx Hn Bn Hsa HD
             ltac:(lia) PD Hb); [exact Rt | lia |].
    pose proof (to_Z_bounded (z.[of_Z (Z.of_nat q)])). lia. }
  split.
  - split.
    + rewrite Hlo. assert (E : (φ (PArray.length out)) = Z.of_nat (List.length ts)) by (rewrite Lo; exact HQ).
      exact (eq_sym E).
    + intros q Hq. rewrite Hlo in Hq. exists (answer s (nth q ts EmptyString) (nth q ks 0%N)).
      split.
      * unfold o. rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec q (List.length ts)); [reflexivity | lia].
      * unfold repr, repr_sint. exact (Hcell q Hq).
  - split; [unfold len; rewrite Hlo; reflexivity|].
    intros q t k Et Ek.
    assert (Hq : (q < List.length ts)%nat) by (apply nth_error_Some; congruence).
    unfold o. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec q (List.length ts)); [|lia]. simpl.
    rewrite (nth_error_nth _ _ _ Et), (nth_error_nth _ _ _ Ek). reflexivity.
Qed.

Definition kth_occurrences_correct :
  forall (s : string) (ts : list string) (ks : list N)
         (x : PrimString.string) (y : array PrimString.string) (z : array uint),
  valid_input s ts ks -> repr x s -> repr y ts -> repr z ks ->
  exists o : list Z, repr (kth_occurrences x y z) o /\
                     kth_occurrences_spec s ts ks o
  := kth_occurrences_impl_correct.
