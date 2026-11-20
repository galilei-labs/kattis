(* Implementation of addemup (addemup.spec): sort, then binary search.

   Code.  Every card c (index i) shows its face value c and, when it can be
   turned, its upside-down reading [alt c] (computed on the int, digit by
   digit with div/mod 10; a card that cannot be turned gets [alt c = c], a
   harmless duplicate).  The shown values are tagged with their card in one
   int key  v * K + i  (K = 2^17 > 100 000 >= the number of cards), stored
   in one flat table T of 2n cells (T[2i] face, T[2i+1] reading), sorted
   once by a top-down merge sort with one auxiliary buffer.  Then, for each
   card i and each of its shown values v <= s, the complement w = s - v is
   looked up by binary search (lower bound) in the sorted table: a card
   j < i showing w is a key in [w*K, w*K + i), a card j > i a key in
   [w*K + i + 1, (w+1)*K); one lower-bound search per range.  No Z, no nat,
   no list in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) measure] proof, as in template/polymul1. *)

From Addemup.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Sorted Permutation Orders Mergesort.
From KattisLib Require Import Cost.
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

Lemma dec_lo : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma dec_hi : forall lo hi : int,
  (lo <? hi) = true -> Zwf 0 (gap hi (lo + (hi - lo) / 2 + 1)) (gap hi lo).
Proof. intros lo hi H. rewrite ltb_spec in H. unfold Zwf, gap. sia. Qed.

Lemma dec_mid : forall lo hi : int,
  (lo <? hi) = true -> (1 <? hi - lo) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros lo hi H H'. rewrite ltb_spec in H, H'. unfold Zwf, gap. sia.
Qed.

Lemma dec_div : forall x : int, (0 <? x) = true -> Zwf 0 (φ (x / 10)) (φ x).
Proof. intros x H. rewrite ltb_spec in H. unfold Zwf. sia. Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* A digit read upside down, if it reads as a digit. *)
Definition rotd (d : int) : option int :=
  if d =? 0 then Some 0 else if d =? 1 then Some 1 else
  if d =? 2 then Some 2 else if d =? 5 then Some 5 else
  if d =? 6 then Some 9 else if d =? 8 then Some 8 else
  if d =? 9 then Some 6 else None.
Elpi complexity rotd.
Arguments rotd_cost : simpl never.

(* The digits of x, least significant first, rotated and appended to r. *)
Fixpoint rloop (x r : int) (H : Acc (Zwf 0) (φ x)) {struct H} : option int :=
  match bdec (0 <? x) with
  | left Hx =>
      match rotd (x mod 10) with
      | Some e => rloop (x / 10) (r * 10 + e) (Acc_inv H (dec_div x Hx))
      | None => None
      end
  | right _ => Some r
  end.
Elpi complexity rloop.
Arguments rloop_cost : simpl never.

Lemma rloop_eq : forall x r H,
  rloop x r H =
  match bdec (0 <? x) with
  | left Hx =>
      match rotd (x mod 10) with
      | Some e => rloop (x / 10) (r * 10 + e) (Acc_inv H (dec_div x Hx))
      | None => None
      end
  | right _ => Some r
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The upside-down reading of c, or c itself when c cannot be turned. *)
Definition alt (c : int) : int :=
  match rloop c 0 (Zwf_well_founded 0 (φ c)) with
  | Some r => r
  | None => c
  end.
Elpi complexity alt.
Arguments alt_cost : simpl never.

Definition K : int := 131072.
Elpi complexity K.
Arguments K_cost : simpl never.

(* T[2j] := c_j * K + j and T[2j+1] := alt c_j * K + j, for j = i .. n-1. *)
Fixpoint build (y T : array int) (n i : int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      build y (T.[2 * i <- c * K + i].[2 * i + 1 <- alt c * K + i]) n (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.
Elpi complexity build.
Arguments build_cost : simpl never.

Lemma build_eq : forall y T n i H,
  build y T n i H =
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      build y (T.[2 * i <- c * K + i].[2 * i + 1 <- alt c * K + i]) n (i + 1)
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Merge src[i..mid) and src[j..hi) into dst[k..hi). *)
Fixpoint merge_loop (src dst : array int) (i mid j hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      if i <? mid then
        if j <? hi then
          if src.[i] <=? src.[j] then
            merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
          else
            merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
        else
          merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
            (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Elpi complexity merge_loop.
Arguments merge_loop_cost : simpl never.

Lemma merge_loop_eq : forall src dst i mid j hi k H,
  merge_loop src dst i mid j hi k H =
  match bdec (k <? hi) with
  | left Hk =>
      if i <? mid then
        if j <? hi then
          if src.[i] <=? src.[j] then
            merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
          else
            merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
              (Acc_inv H (dec_step hi k Hk))
        else
          merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
            (Acc_inv H (dec_step hi k Hk))
      else
        merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
          (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* dst[k..hi) := src[k..hi). *)
Fixpoint copy_loop (src dst : array int) (hi k : int)
    (H : Acc (Zwf 0) (gap hi k)) {struct H} : array int :=
  match bdec (k <? hi) with
  | left Hk =>
      copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Elpi complexity copy_loop.
Arguments copy_loop_cost : simpl never.

Lemma copy_loop_eq : forall src dst hi k H,
  copy_loop src dst hi k H =
  match bdec (k <? hi) with
  | left Hk =>
      copy_loop src dst.[k <- src.[k]] hi (k + 1) (Acc_inv H (dec_step hi k Hk))
  | right _ => dst
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Top-down merge sort of a[lo..hi), with the buffer b; returns both. *)
Fixpoint msort (a b : array int) (lo hi : int) (H : Acc (Zwf 0) (gap hi lo))
    {struct H} : array int * array int :=
  match bdec (lo <? hi) with
  | left H1 =>
      match bdec (1 <? hi - lo) with
      | left H2 =>
          let mid := lo + (hi - lo) / 2 in
          let (a1, b1) := msort a b lo mid (Acc_inv H (dec_lo lo hi H1)) in
          let (a2, b2) := msort a1 b1 mid hi (Acc_inv H (dec_mid lo hi H1 H2)) in
          let b3 := merge_loop a2 b2 lo mid mid hi lo
                      (Zwf_well_founded 0 (gap hi lo)) in
          (copy_loop b3 a2 hi lo (Zwf_well_founded 0 (gap hi lo)), b3)
      | right _ => (a, b)
      end
  | right _ => (a, b)
  end.
Elpi complexity msort.
Arguments msort_cost : simpl never.

Lemma msort_eq : forall a b lo hi H,
  msort a b lo hi H =
  match bdec (lo <? hi) with
  | left H1 =>
      match bdec (1 <? hi - lo) with
      | left H2 =>
          let mid := lo + (hi - lo) / 2 in
          let (a1, b1) := msort a b lo mid (Acc_inv H (dec_lo lo hi H1)) in
          let (a2, b2) := msort a1 b1 mid hi (Acc_inv H (dec_mid lo hi H1 H2)) in
          let b3 := merge_loop a2 b2 lo mid mid hi lo
                      (Zwf_well_founded 0 (gap hi lo)) in
          (copy_loop b3 a2 hi lo (Zwf_well_founded 0 (gap hi lo)), b3)
      | right _ => (a, b)
      end
  | right _ => (a, b)
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Lower bound: the first position p in [lo, hi) with S[p] >= x (or hi). *)
Fixpoint lbloop (S : array int) (x lo hi : int) (H : Acc (Zwf 0) (gap hi lo))
    {struct H} : int :=
  match bdec (lo <? hi) with
  | left Hlt =>
      if S.[lo + (hi - lo) / 2] <? x
      then lbloop S x (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_hi lo hi Hlt))
      else lbloop S x lo (lo + (hi - lo) / 2) (Acc_inv H (dec_lo lo hi Hlt))
  | right _ => lo
  end.
Elpi complexity lbloop.
Arguments lbloop_cost : simpl never.

Lemma lbloop_eq : forall S x lo hi H,
  lbloop S x lo hi H =
  match bdec (lo <? hi) with
  | left Hlt =>
      if S.[lo + (hi - lo) / 2] <? x
      then lbloop S x (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_hi lo hi Hlt))
      else lbloop S x lo (lo + (hi - lo) / 2) (Acc_inv H (dec_lo lo hi Hlt))
  | right _ => lo
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Some key of the sorted S[0..m) lies in [lo, hi). *)
Definition inrange (S : array int) (m lo hi : int) : bool :=
  let p := lbloop S lo 0 m (Zwf_well_founded 0 (gap m 0)) in
  if p <? m then S.[p] <? hi else false.
Elpi complexity inrange.
Arguments inrange_cost : simpl never.

(* Some card other than i shows w. *)
Definition found (S : array int) (m w i : int) : bool :=
  if inrange S m (w * K) (w * K + i) then true
  else inrange S m (w * K + i + 1) ((w + 1) * K).
Elpi complexity found.
Arguments found_cost : simpl never.

(* Card i shows v, and some other card shows s - v. *)
Definition okv (S : array int) (m s v i : int) : bool :=
  if v <=? s then found S m (s - v) i else false.
Elpi complexity okv.
Arguments okv_cost : simpl never.

(* Some card i' in [i, n) completes a winning pair. *)
Fixpoint scan (y S : array int) (s m n i : int) (H : Acc (Zwf 0) (gap n i))
    {struct H} : bool :=
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      if okv S m s c i then true
      else if okv S m s (alt c) i then true
      else scan y S s m n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => false
  end.
Elpi complexity scan.
Arguments scan_cost : simpl never.

Lemma scan_eq : forall y S s m n i H,
  scan y S s m n i H =
  match bdec (i <? n) with
  | left Hi =>
      let c := y.[i] in
      if okv S m s c i then true
      else if okv S m s (alt c) i then true
      else scan y S s m n (i + 1) (Acc_inv H (dec_step n i Hi))
  | right _ => false
  end.
Proof. intros. destruct H. reflexivity. Qed.

Elpi complexity fst.
Arguments fst_cost : simpl never.

Definition addemup_impl (s : uint) (y : array uint) : bool :=
  let n := PArray.length y in
  let m := 2 * n in
  let T := build y (PArray.make m 0) n 0 (Zwf_well_founded 0 (gap n 0)) in
  let S := fst (msort T (PArray.make m 0) 0 m (Zwf_well_founded 0 (gap m 0))) in
  scan y S s m n 0 (Zwf_well_founded 0 (gap n 0)).
Elpi complexity addemup_impl.

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

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma of_Z_phi : forall z : Z, (0 <= z < wB)%Z -> (φ (of_Z z)) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small. exact Hz. Qed.

Lemma int_neq : forall a b : int, (φ a) <> (φ b) -> a <> b.
Proof. intros a b H E. apply H. rewrite E. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The upside-down reading                                             *)
(* ------------------------------------------------------------------ *)

Open Scope N_scope.

(* digits least significant first *)
Fixpoint decLSB (L : list N) : N :=
  match L with [] => 0 | d :: L' => d + 10 * decLSB L' end.

Definition NZ (L : list N) : Prop := L = [] \/ last L 0 <> 0.

Definition rotN (d : N) : option N :=
  if d =? 0 then Some 0 else if d =? 1 then Some 1 else
  if d =? 2 then Some 2 else if d =? 5 then Some 5 else
  if d =? 6 then Some 9 else if d =? 8 then Some 8 else
  if d =? 9 then Some 6 else None.

Definition rotf (d : N) : N := match rotN d with Some e => e | None => 0 end.

Definition allrot (L : list N) : Prop := Forall (fun d => rotN d <> None) L.

Definition rfold (L : list N) (acc : N) : N :=
  fold_left (fun acc d => 10 * acc + rotf d) L acc.

Lemma rotates_iff : forall d e, rotates d e <-> rotN d = Some e.
Proof.
  intros d e. unfold rotates, rotN. split.
  - simpl. intros H.
    repeat (destruct H as [H | H]; [injection H as <- <-; reflexivity |]).
    destruct H.
  - repeat match goal with |- context [N.eqb d ?k] =>
      destruct (N.eqb_spec d k); [subst; intros H; injection H as <-; simpl; tauto |] end.
    intros H; discriminate H.
Qed.

Lemma rotf_le : forall d, rotf d <= 9.
Proof.
  intros d. unfold rotf, rotN.
  repeat (destruct (N.eqb _ _); [lia |]). lia.
Qed.

Lemma decLSB_pos : forall L d, last (d :: L) 0 <> 0 -> 0 < decLSB (d :: L).
Proof.
  induction L as [| e L IH]; intros d H.
  - simpl in *. lia.
  - change (last (d :: e :: L) 0) with (last (e :: L) 0) in H.
    specialize (IH e H). cbn [decLSB] in *. lia.
Qed.

Lemma digits_exist : forall x : N,
  exists L, Forall (fun d => d <= 9) L /\ NZ L /\ decLSB L = x.
Proof.
  intros x. induction x as [x IH] using (well_founded_induction N.lt_wf_0).
  destruct (N.eq_dec x 0) as [-> | Hx].
  - exists []. split; [constructor | split; [left; reflexivity | reflexivity]].
  - destruct (IH (x / 10)) as [L [Hf [Hnz Hd]]].
    { apply N.div_lt; lia. }
    exists ((x mod 10) :: L). split; [| split].
    + constructor; [| exact Hf]. pose proof (N.mod_lt x 10). lia.
    + right. destruct L as [| e L'].
      * cbn [decLSB last] in Hd |- *. intros E.
        pose proof (N.div_mod x 10 ltac:(lia)). lia.
      * destruct Hnz as [Hn | Hn]; [discriminate | exact Hn].
    + cbn [decLSB]. rewrite Hd. pose proof (N.div_mod x 10 ltac:(lia)). lia.
Qed.

Lemma decimal_from_app : forall ds es acc,
  decimal_from (ds ++ es) acc = decimal_from es (decimal_from ds acc).
Proof.
  induction ds as [|d ds IH]; intros es acc; cbn [app decimal_from].
  - reflexivity.
  - apply IH.
Qed.

Lemma decimal_rev : forall ds, decimal ds = decLSB (rev ds).
Proof.
  intros ds. induction ds as [| d ds IH] using rev_ind; [reflexivity |].
  unfold decimal in *. rewrite decimal_from_app, rev_unit. cbn [decimal_from decLSB].
  rewrite IH. lia.
Qed.

Lemma hd_rev : forall (l : list N) d, hd d (rev l) = last l d.
Proof.
  intros l d. destruct l as [| a l] using rev_ind; [reflexivity |].
  rewrite rev_unit, last_last. reflexivity.
Qed.

Lemma forall2_rot : forall L es, Forall2 rotates L es ->
  allrot L /\ forall acc, decimal_from es acc = rfold L acc.
Proof.
  intros L es H. induction H as [| d e L es Hde _ [Ha IH]].
  - split; [constructor | reflexivity].
  - rewrite rotates_iff in Hde. split.
    + constructor; [rewrite Hde; discriminate | exact Ha].
    + intros acc. cbn [decimal_from]. rewrite IH. unfold rfold. cbn [fold_left].
      replace (rotf d) with e by (unfold rotf; rewrite Hde; reflexivity).
      reflexivity.
Qed.

Lemma allrot_forall2 : forall L, allrot L ->
  Forall2 rotates L (map rotf L) /\
  forall acc, decimal_from (map rotf L) acc = rfold L acc.
Proof.
  intros L H. induction H as [| d L Hd _ [IH1 IH2]].
  - split; [constructor | reflexivity].
  - split.
    + constructor; [| exact IH1]. apply rotates_iff. unfold rotf.
      destruct (rotN d); [reflexivity | contradiction].
    + intros acc. cbn [decimal_from map]. rewrite IH2. reflexivity.
Qed.

Lemma upside_iff : forall c v, 1 <= c ->
  (upside_down c v <->
   exists L, Forall (fun d => d <= 9) L /\ NZ L /\ decLSB L = c /\
             allrot L /\ rfold L 0 = v).
Proof.
  intros c v Hc. split.
  - intros (ds & es & [Hne [Hf [Hhd Hdec]]] & H2 & H3).
    destruct (forall2_rot _ _ H2) as [Ha Hfold].
    exists (rev ds). split; [| split; [| split; [| split]]].
    + apply Forall_rev. exact Hf.
    + right. rewrite <- hd_rev, rev_involutive. exact Hhd.
    + rewrite <- decimal_rev. exact Hdec.
    + exact Ha.
    + rewrite <- Hfold. exact H3.
  - intros (L & Hf & Hnz & Hd & Ha & Hv).
    destruct (allrot_forall2 L Ha) as [H2 Hfold].
    exists (rev L), (map rotf L). split; [| split].
    + split; [| split; [| split]].
      * intros E. apply (f_equal (@rev N)) in E. rewrite rev_involutive in E.
        subst L. simpl in Hd. lia.
      * apply Forall_rev. exact Hf.
      * rewrite hd_rev. destruct Hnz as [-> | Hn]; [cbn [decLSB] in Hd; lia | exact Hn].
      * rewrite decimal_rev, rev_involutive. exact Hd.
    + rewrite rev_involutive. exact H2.
    + unfold decimal. rewrite Hfold. exact Hv.
Qed.

Lemma rfold_bound : forall L acc,
  rfold L acc < (acc + 1) * 10 ^ N.of_nat (List.length L).
Proof.
  induction L as [| d L IH]; intros acc.
  - unfold rfold. cbn [fold_left List.length]. change (N.of_nat 0) with 0. rewrite N.pow_0_r. lia.
  - unfold rfold. cbn [fold_left List.length]. fold (rfold L (10 * acc + rotf d)).
    specialize (IH (10 * acc + rotf d)). pose proof (rotf_le d).
    rewrite Nat2N.inj_succ, N.pow_succ_r'.
    assert ((10 * acc + rotf d + 1) * 10 ^ N.of_nat (List.length L)
            <= (acc + 1) * (10 * 10 ^ N.of_nat (List.length L))) by nia.
    lia.
Qed.

Lemma decLSB_low : forall L d, last (d :: L) 0 <> 0 ->
  10 ^ N.of_nat (List.length L) <= decLSB (d :: L).
Proof.
  induction L as [| e L IH]; intros d H.
  - simpl in *. lia.
  - change (last (d :: e :: L) 0) with (last (e :: L) 0) in H.
    specialize (IH e H). change (List.length (e :: L)) with (S (List.length L)).
    rewrite Nat2N.inj_succ, N.pow_succ_r'. cbn [decLSB] in *. lia.
Qed.

Lemma rfold_small : forall L c, Forall (fun d => d <= 9) L -> NZ L ->
  decLSB L = c -> 1 <= c <= 100000000 -> rfold L 0 < 1000000000.
Proof.
  intros L c Hf Hnz Hd Hc.
  destruct L as [| d L]; [cbn [decLSB] in Hd; lia |].
  destruct Hnz as [Hn | Hn]; [discriminate |].
  pose proof (decLSB_low L d Hn) as Hlow.
  pose proof (rfold_bound (d :: L) 0) as Hb.
  change (List.length (d :: L)) with (S (List.length L)) in Hb.
  rewrite Nat2N.inj_succ, N.pow_succ_r' in Hb.
  assert (Hl : N.of_nat (List.length L) <= 8).
  { destruct (N.le_gt_cases (N.of_nat (List.length L)) 8) as [H | H]; [exact H |].
    assert (10 ^ 9 <= 10 ^ N.of_nat (List.length L)) by (apply N.pow_le_mono_r; lia).
    lia. }
  assert (10 ^ N.of_nat (List.length L) <= 10 ^ 8) by (apply N.pow_le_mono_r; lia).
  lia.
Qed.

Close Scope N_scope.

Lemma rotd_link : forall d : int, ((φ d) < 10)%Z ->
  match rotd d with
  | Some e => rotN (Z.to_N (φ d)) = Some (Z.to_N (φ e))
  | None => rotN (Z.to_N (φ d)) = None
  end.
Proof.
  intros d Hd. pose proof (to_Z_bounded d) as Bd.
  assert (E : d = of_Z (φ d)) by (symmetry; apply of_to_Z).
  remember (φ d) as z eqn:Hz. rewrite E. clear Hz E.
  assert (Hc : z = 0%Z \/ z = 1%Z \/ z = 2%Z \/ z = 3%Z \/ z = 4%Z \/
               z = 5%Z \/ z = 6%Z \/ z = 7%Z \/ z = 8%Z \/ z = 9%Z) by lia.
  repeat (destruct Hc as [-> | Hc]; [reflexivity |]). subst. reflexivity.
Qed.

Lemma modstep : forall (R e : Z),
  (((R mod wB) * 10 + e) mod wB = (R * 10 + e) mod wB)%Z.
Proof.
  intros R e. rewrite <- Z.add_mod_idemp_l by (rewrite wB_val; lia).
  rewrite Z.mul_mod_idemp_l by (rewrite wB_val; lia).
  rewrite Z.add_mod_idemp_l by (rewrite wB_val; lia). reflexivity.
Qed.

Lemma rloop_spec : forall L (x r : int) (R : N) (H : Acc (Zwf 0) (φ x)),
  Forall (fun d => (d <= 9)%N) L -> NZ L ->
  (φ x) = Z.of_N (decLSB L) -> (φ r) = (Z.of_N R mod wB)%Z ->
  match rloop x r H with
  | Some y => allrot L /\ (φ y) = (Z.of_N (rfold L R) mod wB)%Z
  | None => ~ allrot L
  end.
Proof.
  induction L as [| d L IH]; intros x r R H Hf Hnz Hx Hr.
  - rewrite rloop_eq. cbn [decLSB] in Hx.
    destruct (bdec (0 <? x)) as [Hp | Hp].
    + pose proof Hp as Hp'. rewrite ltb_spec in Hp'. change (φ 0) with 0%Z in Hp'. lia.
    + split; [constructor | exact Hr].
  - inversion Hf as [| ? ? Hd Hf']. subst.
    assert (Hpos : (0 < decLSB (d :: L))%N).
    { apply decLSB_pos. destruct Hnz as [Hn | Hn]; [discriminate | exact Hn]. }
    assert (HnzL : NZ L).
    { destruct L as [| e L']; [left; reflexivity | right].
      destruct Hnz as [Hn | Hn]; [discriminate | exact Hn]. }
    cbn [decLSB] in Hx, Hpos.
    rewrite rloop_eq.
    destruct (bdec (0 <? x)) as [Hp | Hp].
    2:{ rewrite <- Bool.not_true_iff_false, ltb_spec in Hp.
        change (φ 0) with 0%Z in Hp. lia. }
    assert (Hm : (φ (x mod 10)) = Z.of_N d) by sia.
    assert (Hdv : (φ (x / 10)) = Z.of_N (decLSB L)) by sia.
    pose proof (rotd_link (x mod 10) ltac:(lia)) as Hl.
    rewrite Hm, N2Z.id in Hl.
    destruct (rotd (x mod 10)) as [e |] eqn:Er.
    + pose proof (to_Z_bounded e) as Be.
      specialize (IH (x / 10) (r * 10 + e) ((10 * R + Z.to_N (φ e))%N)
                     (Acc_inv H (dec_div x Hp)) Hf' HnzL Hdv).
      assert (Hr' : (φ (r * 10 + e)) = (Z.of_N (10 * R + Z.to_N (φ e))%N mod wB)%Z).
      { rewrite add_spec, mul_spec, Hr. change (φ 10) with 10%Z.
        rewrite Z.add_mod_idemp_l by (rewrite wB_val; lia).
        rewrite modstep. f_equal. lia. }
      specialize (IH Hr').
      assert (Hrf : rfold (d :: L) R = rfold L (10 * R + Z.to_N (φ e))%N).
      { unfold rfold. cbn [fold_left]. unfold rotf at 2. rewrite Hl. reflexivity. }
      destruct (rloop (x / 10) (r * 10 + e) _) as [y |].
      * destruct IH as [Ha Hy]. split.
        -- constructor; [rewrite Hl; discriminate | exact Ha].
        -- rewrite Hrf. exact Hy.
      * intros Ha. inversion Ha. contradiction.
    + intros Ha. inversion Ha. contradiction.
Qed.


Lemma alt_spec : forall c : int, (1 <= (φ c) <= 100000000)%Z ->
  ((φ (alt c)) <= 1000000000)%Z /\
  forall v : N, shows (Z.to_N (φ c)) v <-> (Z.of_N v = (φ c) \/ Z.of_N v = (φ (alt c))).
Proof.
  intros c Hc.
  destruct (digits_exist (Z.to_N (φ c))) as [L [Hf [Hnz Hd]]].
  assert (Hx : (φ c) = Z.of_N (decLSB L)) by lia.
  assert (Hr : (φ 0) = (Z.of_N 0 mod wB)%Z) by reflexivity.
  pose proof (rloop_spec L c 0 0 (Zwf_well_founded 0 (φ c)) Hf Hnz Hx Hr) as HL.
  assert (Hsm : forall L2 : list N, Forall (fun d => (d <= 9)%N) L2 -> NZ L2 ->
                decLSB L2 = Z.to_N (φ c) -> (Z.of_N (rfold L2 0) < 1000000000)%Z).
  { intros L2 H1 H2 H3. pose proof (rfold_small L2 _ H1 H2 H3 ltac:(lia)). lia. }
  unfold alt. unfold shows.
  destruct (rloop c 0 (Zwf_well_founded 0 (φ c))) as [y |] eqn:E.
  - destruct HL as [Ha Hy].
    pose proof (Hsm L Hf Hnz Hd) as HsL.
    rewrite Z.mod_small in Hy by (rewrite wB_val; lia).
    split; [lia |]. intros v. split.
    + intros [Hv | Hv]; [left; lia | right].
      apply upside_iff in Hv; [| lia].
      destruct Hv as (L2 & Hf2 & Hnz2 & Hd2 & Ha2 & Hv2).
      assert (Hx2 : (φ c) = Z.of_N (decLSB L2)) by lia.
      pose proof (rloop_spec L2 c 0 0 (Zwf_well_founded 0 (φ c)) Hf2 Hnz2 Hx2 Hr) as HL2.
      rewrite E in HL2. destruct HL2 as [_ Hy2].
      pose proof (Hsm L2 Hf2 Hnz2 Hd2).
      rewrite Z.mod_small in Hy2 by (rewrite wB_val; lia). lia.
    + intros [Hv | Hv]; [left; lia | right].
      apply upside_iff; [lia |].
      exists L. split; [exact Hf | split; [exact Hnz | split; [exact Hd | split; [exact Ha | lia]]]].
  - split; [lia |]. intros v. split.
    + intros [Hv | Hv]; [left; lia |].
      apply upside_iff in Hv; [| lia].
      destruct Hv as (L2 & Hf2 & Hnz2 & Hd2 & Ha2 & Hv2).
      assert (Hx2 : (φ c) = Z.of_N (decLSB L2)) by lia.
      pose proof (rloop_spec L2 c 0 0 (Zwf_well_founded 0 (φ c)) Hf2 Hnz2 Hx2 Hr) as HL2.
      rewrite E in HL2. contradiction.
    + intros [Hv | Hv]; left; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Segments of an array, as lists of Z (Prop side)                     *)
(* ------------------------------------------------------------------ *)

Module ZLeb <: TotalLeBool.
  Definition t := Z.
  Definition leb := Z.leb.
  Theorem leb_total : forall a1 a2, is_true (leb a1 a2) \/ is_true (leb a2 a1).
  Proof. intros a1 a2. unfold is_true, leb. rewrite !Z.leb_le. lia. Qed.
End ZLeb.

Module ZSort := Sort ZLeb.

Definition SortedZ (l : list Z) : Prop :=
  LocallySorted (fun x y => is_true (ZLeb.leb x y)) l.

Lemma merge_nil_l : forall l, ZSort.merge [] l = l.
Proof. intros [| a l]; reflexivity. Qed.

Lemma merge_nil_r : forall l, ZSort.merge l [] = l.
Proof. intros [| a l]; reflexivity. Qed.

Lemma merge_cons : forall a l1 b l2,
  ZSort.merge (a :: l1) (b :: l2) =
  if Z.leb a b then a :: ZSort.merge l1 (b :: l2) else b :: ZSort.merge (a :: l1) l2.
Proof. reflexivity. Qed.

Lemma merge_take_l : forall x l1 l2,
  (forall y l2', l2 = y :: l2' -> (x <= y)%Z) ->
  ZSort.merge (x :: l1) l2 = x :: ZSort.merge l1 l2.
Proof.
  intros x l1 [| y l2] H.
  - rewrite !merge_nil_r. reflexivity.
  - rewrite merge_cons. specialize (H y l2 eq_refl).
    destruct (Z.leb_spec x y); [reflexivity | lia].
Qed.

Lemma merge_take_r : forall l1 y l2,
  (forall x l1', l1 = x :: l1' -> (y < x)%Z) ->
  ZSort.merge l1 (y :: l2) = y :: ZSort.merge l1 l2.
Proof.
  intros [| x l1] y l2 H.
  - rewrite !merge_nil_l. reflexivity.
  - rewrite merge_cons. specialize (H x l1 eq_refl).
    destruct (Z.leb_spec x y); [lia | reflexivity].
Qed.

Fixpoint seg (a : array int) (lo : Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => (φ (a.[of_Z lo])) :: seg a (lo + 1) n'
  end.

Lemma seg_app : forall a n m lo,
  seg a lo (n + m) = seg a lo n ++ seg a (lo + Z.of_nat n) m.
Proof.
  intros a n m. induction n as [| n IH]; intros lo.
  - simpl. rewrite Z.add_0_r. reflexivity.
  - simpl. rewrite IH. do 3 f_equal. lia.
Qed.

Lemma seg_ext : forall a b n lo,
  (forall z, (lo <= z < lo + Z.of_nat n)%Z -> a.[of_Z z] = b.[of_Z z]) ->
  seg a lo n = seg b lo n.
Proof.
  intros a b n. induction n as [| n IH]; intros lo H; [reflexivity |].
  simpl. rewrite H by lia. f_equal. apply IH. intros z Hz. apply H. lia.
Qed.

Lemma seg_snoc_set : forall (dst : array int) lo n (k v : int),
  (0 <= lo)%Z -> (φ k) = (lo + Z.of_nat n)%Z -> (k <? PArray.length dst) = true ->
  seg dst.[k <- v] lo (S n) = seg dst lo n ++ [(φ v)].
Proof.
  intros dst lo n k v Hlo Hk Hb.
  replace (S n) with (n + 1)%nat by lia. rewrite seg_app.
  f_equal.
  - apply seg_ext. intros z Hz. apply aget_set_other.
    apply int_neq. pose proof (to_Z_bounded k). rewrite of_Z_phi by lia. lia.
  - simpl. rewrite <- Hk, of_to_Z, aget_set_same by exact Hb. reflexivity.
Qed.

Lemma seg_cons : forall a lo n,
  seg a lo (S n) = (φ (a.[of_Z lo])) :: seg a (lo + 1) n.
Proof. reflexivity. Qed.

Lemma In_seg : forall a n lo e,
  In e (seg a lo n) <-> exists z, (lo <= z < lo + Z.of_nat n)%Z /\ e = (φ (a.[of_Z z])).
Proof.
  intros a n. induction n as [| n IH]; intros lo e.
  - simpl. split; [intros [] | intros (z & Hz & _); lia].
  - simpl. rewrite IH. split.
    + intros [E | (z & Hz & E)]; [exists lo; split; [lia | auto] | exists z; split; [lia | auto]].
    + intros (z & Hz & E). destruct (Z.eq_dec z lo) as [-> | Hne]; [left; auto |].
      right. exists z. split; [lia | auto].
Qed.

Lemma LocallySorted_tail : forall (R : Z -> Z -> Prop) x l,
  LocallySorted R (x :: l) -> LocallySorted R l.
Proof. intros R x l H. inversion H; [constructor | assumption]. Qed.

Lemma seg_sorted_pw : forall a n lo, SortedZ (seg a lo n) ->
  forall p q, (lo <= p)%Z -> (p <= q < lo + Z.of_nat n)%Z ->
  ((φ (a.[of_Z p])) <= (φ (a.[of_Z q])))%Z.
Proof.
  intros a n. induction n as [| n IH]; intros lo Hs p q Hp Hpq; [lia |].
  unfold SortedZ in Hs. rewrite seg_cons in Hs.
  pose proof (LocallySorted_tail _ _ _ Hs) as Ht.
  destruct (Z.eq_dec p lo) as [-> | Hne].
  - destruct (Z.eq_dec q lo) as [-> | Hq]; [lia |].
    destruct n as [| n]; [lia |].
    rewrite seg_cons in Hs. inversion Hs. subst.
    match goal with Hr : is_true (ZLeb.leb _ _) |- _ =>
      unfold is_true, ZLeb.leb in Hr; apply Z.leb_le in Hr end.
    pose proof (IH (lo + 1)%Z Ht (lo + 1)%Z q ltac:(lia) ltac:(lia)). lia.
  - apply (IH (lo + 1)%Z Ht); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The merge sort                                                      *)
(* ------------------------------------------------------------------ *)

Lemma merge_loop_spec : forall (src : array int) (lo mid hi L : int) (M : list Z) z
    (dst : array int) (i j k : int) (H : Acc (Zwf 0) (gap hi k)),
  gap hi k = z ->
  (0 <= (φ lo) <= (φ i))%Z -> ((φ i) <= (φ mid) <= (φ j))%Z -> ((φ j) <= (φ hi))%Z ->
  ((φ hi) <= (φ L))%Z -> PArray.length dst = L ->
  (φ k) = ((φ i) + (φ j) - (φ mid))%Z ->
  seg dst (φ lo) (Z.to_nat ((φ k) - (φ lo))) ++
    ZSort.merge (seg src (φ i) (Z.to_nat ((φ mid) - (φ i))))
                (seg src (φ j) (Z.to_nat ((φ hi) - (φ j)))) = M ->
  PArray.length (merge_loop src dst i mid j hi k H) = L /\
  seg (merge_loop src dst i mid j hi k H) (φ lo) (Z.to_nat ((φ hi) - (φ lo))) = M.
Proof.
  intros src lo mid hi L M z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros dst i j k H Hz Hlo Him Hjh HhL Hlen Hk HM.
  rewrite merge_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    assert (Ek1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkb : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
    (* the two moves *)
    assert (Tl : ((φ i) < (φ mid))%Z ->
                 (((φ j) < (φ hi))%Z -> ((φ (src.[i])) <= (φ (src.[j])))%Z) ->
      PArray.length (merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
                       (Acc_inv H (dec_step hi k Hkh))) = L /\
      seg (merge_loop src dst.[k <- src.[i]] (i + 1) mid j hi (k + 1)
             (Acc_inv H (dec_step hi k Hkh))) (φ lo) (Z.to_nat ((φ hi) - (φ lo))) = M).
    { intros Hi Hc.
      assert (Ei1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      eapply IH; [ rewrite <- Hz; apply dec_step; exact Hkh | reflexivity
                 | lia | lia | lia | lia | rewrite alength_set; exact Hlen | lia | ].
      rewrite Ek1, Ei1.
      replace (Z.to_nat ((φ k) + 1 - (φ lo))) with (S (Z.to_nat ((φ k) - (φ lo)))) by lia.
      rewrite seg_snoc_set by (exact Hkb || lia).
      rewrite <- HM, <- app_assoc. f_equal.
      replace (Z.to_nat ((φ mid) - (φ i))) with (S (Z.to_nat ((φ mid) - ((φ i) + 1)))) by lia.
      rewrite seg_cons, of_to_Z. simpl app.
      symmetry. apply merge_take_l. intros y l2' E.
      destruct (Z.to_nat ((φ hi) - (φ j))) as [| n] eqn:En; [discriminate |].
      rewrite seg_cons, of_to_Z in E. injection E as <- _. apply Hc. lia. }
    assert (Tr : ((φ j) < (φ hi))%Z ->
                 (((φ i) < (φ mid))%Z -> ((φ (src.[j])) < (φ (src.[i])))%Z) ->
      PArray.length (merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
                       (Acc_inv H (dec_step hi k Hkh))) = L /\
      seg (merge_loop src dst.[k <- src.[j]] i mid (j + 1) hi (k + 1)
             (Acc_inv H (dec_step hi k Hkh))) (φ lo) (Z.to_nat ((φ hi) - (φ lo))) = M).
    { intros Hj Hc.
      assert (Ej1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
      eapply IH; [ rewrite <- Hz; apply dec_step; exact Hkh | reflexivity
                 | lia | lia | lia | lia | rewrite alength_set; exact Hlen | lia | ].
      rewrite Ek1, Ej1.
      replace (Z.to_nat ((φ k) + 1 - (φ lo))) with (S (Z.to_nat ((φ k) - (φ lo)))) by lia.
      rewrite seg_snoc_set by (exact Hkb || lia).
      rewrite <- HM, <- app_assoc. f_equal.
      replace (Z.to_nat ((φ hi) - (φ j))) with (S (Z.to_nat ((φ hi) - ((φ j) + 1)))) by lia.
      rewrite seg_cons, of_to_Z. simpl app.
      symmetry. apply merge_take_r. intros x l1' E.
      destruct (Z.to_nat ((φ mid) - (φ i))) as [| n] eqn:En; [discriminate |].
      rewrite seg_cons, of_to_Z in E. injection E as <- _. apply Hc. lia. }
    destruct (i <? mid) eqn:Ei; [destruct (j <? hi) eqn:Ej |].
    + rewrite ltb_spec in Ei, Ej.
      destruct (src.[i] <=? src.[j]) eqn:Ec.
      * rewrite leb_spec in Ec. apply Tl; [exact Ei | intros _; exact Ec].
      * rewrite <- Bool.not_true_iff_false, leb_spec in Ec.
        apply Tr; [exact Ej | intros _; lia].
    + rewrite ltb_spec in Ei. rewrite <- Bool.not_true_iff_false, ltb_spec in Ej.
      apply Tl; [exact Ei | lia].
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ei.
      apply Tr; [lia | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
    split; [exact Hlen |].
    rewrite <- HM.
    replace (Z.to_nat ((φ mid) - (φ i))) with O by lia.
    replace (Z.to_nat ((φ hi) - (φ j))) with O by lia.
    simpl seg. rewrite merge_nil_l, app_nil_r. f_equal. lia.
Qed.

Lemma copy_loop_spec : forall (src : array int) (hi L : int) z (dst : array int)
    (k : int) (H : Acc (Zwf 0) (gap hi k)),
  gap hi k = z -> ((φ hi) <= (φ L))%Z -> PArray.length dst = L ->
  PArray.length (copy_loop src dst hi k H) = L /\
  forall q, (copy_loop src dst hi k H).[q] =
            if (((φ k) <=? (φ q))%Z && ((φ q) <? (φ hi))%Z)%bool then src.[q] else dst.[q].
Proof.
  intros src hi L z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros dst k H Hz HhL Hlen.
  rewrite copy_loop_eq.
  destruct (bdec (k <? hi)) as [Hkh | Hkh].
  - pose proof Hkh as Hkh'. rewrite ltb_spec in Hkh'.
    assert (Ek1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hkb : (k <? PArray.length dst) = true) by (rewrite ltb_spec; lia).
    destruct (IH (gap hi (k + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hkh)
                 dst.[k <- src.[k]] (k + 1) (Acc_inv H (dec_step hi k Hkh)) eq_refl HhL
                 ltac:(rewrite alength_set; exact Hlen)) as [IHl IHq].
    split; [exact IHl |]. intros q. rewrite IHq, Ek1.
    destruct (Z.eq_dec (φ q) (φ k)) as [Eqk | Hqk'].
    + apply to_Z_inj in Eqk. subst q.
      rewrite aget_set_same by exact Hkb.
      destruct (Z.leb_spec ((φ k) + 1) (φ k)); [lia |].
      destruct (Z.leb_spec (φ k) (φ k)); [| lia].
      destruct (Z.ltb_spec (φ k) (φ hi)); [reflexivity | lia].
    + rewrite aget_set_other by (apply int_neq; lia).
      destruct (Z.leb_spec ((φ k) + 1) (φ q)), (Z.leb_spec (φ k) (φ q)); simpl;
        try reflexivity; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkh.
    split; [exact Hlen |]. intros q.
    destruct (Z.leb_spec (φ k) (φ q)), (Z.ltb_spec (φ q) (φ hi)); simpl;
      try reflexivity; lia.
Qed.

Definition msort_P (L : int) (a : array int) (lo hi : int)
    (r : array int * array int) : Prop :=
  PArray.length (fst r) = L /\ PArray.length (snd r) = L /\
  (forall q, ((φ q) < (φ lo) \/ (φ hi) <= (φ q))%Z -> (fst r).[q] = a.[q]) /\
  SortedZ (seg (fst r) (φ lo) (Z.to_nat ((φ hi) - (φ lo)))) /\
  Permutation (seg (fst r) (φ lo) (Z.to_nat ((φ hi) - (φ lo))))
              (seg a (φ lo) (Z.to_nat ((φ hi) - (φ lo)))).

Lemma msort_spec : forall z (a b : array int) (lo hi L : int)
    (H : Acc (Zwf 0) (gap hi lo)),
  gap hi lo = z -> (0 <= (φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ L))%Z ->
  PArray.length a = L -> PArray.length b = L ->
  msort_P L a lo hi (msort a b lo hi H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros a b lo hi L H Hz Hlh HhL Ha Hb.
  rewrite msort_eq.
  assert (Base : ((φ hi) - (φ lo) <= 1)%Z -> msort_P L a lo hi (a, b)).
  { intros Hd. unfold msort_P; simpl fst; simpl snd.
    split; [exact Ha | split; [exact Hb | split; [reflexivity | split; [| reflexivity]]]].
    destruct (Z.to_nat ((φ hi) - (φ lo))) as [| [| n]] eqn:En;
      [constructor | constructor | lia]. }
  destruct (bdec (lo <? hi)) as [H1 | H1].
  2:{ apply Base. rewrite <- Bool.not_true_iff_false, ltb_spec in H1. lia. }
  destruct (bdec (1 <? hi - lo)) as [H2 | H2].
  2:{ apply Base. rewrite <- Bool.not_true_iff_false, ltb_spec in H2.
      rewrite ltb_spec in H1. revert H2. sia. }
  pose proof H1 as H1'. pose proof H2 as H2'. rewrite ltb_spec in H1', H2'.
  cbv zeta.
  assert (Hm : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z) by sia.
  assert (Hm1 : ((φ lo) < (φ (lo + (hi - lo) / 2)) < (φ hi))%Z) by (revert H2'; sia).
  set (mid := lo + (hi - lo) / 2) in *.
  lazymatch goal with |- context [msort a b lo ?m ?h] =>
    pose proof (IH (gap m lo) ltac:(rewrite <- Hz; apply dec_lo; exact H1)
                 a b lo m L h eq_refl ltac:(lia) ltac:(lia) Ha Hb) as R1;
    destruct (msort a b lo m h) as [a1 b1] end.
  destruct R1 as (La1 & Lb1 & Fa1 & Sa1 & Pa1). simpl fst in *; simpl snd in *.
  lazymatch goal with |- context [msort a1 b1 ?m hi ?h] =>
    pose proof (IH (gap hi m) ltac:(rewrite <- Hz; apply dec_mid; assumption)
                 a1 b1 m hi L h eq_refl ltac:(lia) ltac:(lia) La1 Lb1) as R2;
    destruct (msort a1 b1 m hi h) as [a2 b2] end.
  destruct R2 as (La2 & Lb2 & Fa2 & Sa2 & Pa2). simpl fst in *; simpl snd in *.
  set (l1 := seg a2 (φ lo) (Z.to_nat ((φ mid) - (φ lo)))).
  set (l2 := seg a2 (φ mid) (Z.to_nat ((φ hi) - (φ mid)))).
  destruct (merge_loop_spec a2 lo mid hi L (ZSort.merge l1 l2) (gap hi lo) b2 lo mid lo
              (Zwf_well_founded 0 (gap hi lo)) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
              HhL Lb2 ltac:(lia)) as [Lb3 Sb3].
  { replace (Z.to_nat ((φ lo) - (φ lo))) with O by lia. reflexivity. }
  set (b3 := merge_loop a2 b2 lo mid mid hi lo (Zwf_well_founded 0 (gap hi lo))) in *.
  destruct (copy_loop_spec b3 hi L (gap hi lo) a2 lo (Zwf_well_founded 0 (gap hi lo))
              eq_refl HhL La2) as [La3 Fa3].
  set (a3 := copy_loop b3 a2 hi lo (Zwf_well_founded 0 (gap hi lo))) in *.
  assert (E1 : l1 = seg a1 (φ lo) (Z.to_nat ((φ mid) - (φ lo)))).
  { apply seg_ext. intros zz Hzz. apply Fa2. rewrite of_Z_phi; [lia |].
    pose proof (to_Z_bounded mid). lia. }
  assert (E2 : seg a1 (φ mid) (Z.to_nat ((φ hi) - (φ mid)))
               = seg a (φ mid) (Z.to_nat ((φ hi) - (φ mid)))).
  { apply seg_ext. intros zz Hzz. apply Fa1. rewrite of_Z_phi; [lia |].
    pose proof (to_Z_bounded hi). lia. }
  assert (E3 : seg a3 (φ lo) (Z.to_nat ((φ hi) - (φ lo))) = ZSort.merge l1 l2).
  { rewrite <- Sb3. apply seg_ext. intros zz Hzz. rewrite Fa3.
    pose proof (to_Z_bounded hi).
    rewrite of_Z_phi by lia.
    destruct (Z.leb_spec (φ lo) zz); [| lia].
    destruct (Z.ltb_spec zz (φ hi)); [reflexivity | lia]. }
  unfold msort_P; simpl fst; simpl snd.
  split; [exact La3 | split; [exact Lb3 | split; [| split]]].
  - intros q Hq. rewrite Fa3.
    destruct (Z.leb_spec (φ lo) (φ q)), (Z.ltb_spec (φ q) (φ hi)); simpl; try lia;
      rewrite Fa2 by lia; apply Fa1; lia.
  - rewrite E3. apply ZSort.Sorted_merge.
    + rewrite E1. exact Sa1.
    + exact Sa2.
  - rewrite E3. symmetry. eapply Permutation_trans; [| apply ZSort.Permuted_merge].
    replace (Z.to_nat ((φ hi) - (φ lo)))
      with (Z.to_nat ((φ mid) - (φ lo)) + Z.to_nat ((φ hi) - (φ mid)))%nat by lia.
    rewrite seg_app.
    replace ((φ lo) + Z.of_nat (Z.to_nat ((φ mid) - (φ lo))))%Z with (φ mid) by lia.
    apply Permutation_app.
    + rewrite E1. symmetry. exact Pa1.
    + rewrite <- E2. symmetry. exact Pa2.
Qed.

(* ------------------------------------------------------------------ *)
(* The binary search                                                   *)
(* ------------------------------------------------------------------ *)

Definition PW (S : array int) (m : int) : Prop :=
  forall p q : int, ((φ p) <= (φ q) < (φ m))%Z -> ((φ (S.[p])) <= (φ (S.[q])))%Z.

Lemma PW_of_seg : forall S m, SortedZ (seg S 0 (Z.to_nat (φ m))) -> PW S m.
Proof.
  intros S m Hs p q Hpq.
  pose proof (seg_sorted_pw S _ 0 Hs (φ p) (φ q)) as H.
  rewrite !of_to_Z in H. pose proof (to_Z_bounded p). apply H; lia.
Qed.

Lemma lbloop_spec : forall S m x, PW S m ->
  forall z lo hi (H : Acc (Zwf 0) (gap hi lo)) r,
  gap hi lo = z -> (0 <= (φ lo) <= (φ hi))%Z -> ((φ hi) <= (φ m))%Z ->
  (forall q, ((φ q) < (φ lo))%Z -> ((φ (S.[q])) < (φ x))%Z) ->
  (forall q, ((φ hi) <= (φ q) < (φ m))%Z -> ((φ x) <= (φ (S.[q])))%Z) ->
  lbloop S x lo hi H = r ->
  ((φ lo) <= (φ r) <= (φ hi))%Z /\
  (forall q, ((φ q) < (φ r))%Z -> ((φ (S.[q])) < (φ x))%Z) /\
  (forall q, ((φ r) <= (φ q) < (φ m))%Z -> ((φ x) <= (φ (S.[q])))%Z).
Proof.
  intros S m x Hpw z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros lo hi H r Hz Hlh Hhm Hl Hh Hr.
  rewrite lbloop_eq in Hr.
  destruct (bdec (lo <? hi)) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hm : (φ (lo + (hi - lo) / 2)) = ((φ lo) + ((φ hi) - (φ lo)) / 2)%Z) by sia.
    assert (Hm1 : ((φ lo) <= (φ (lo + (hi - lo) / 2)) < (φ hi))%Z) by (rewrite Hm; sia).
    destruct (S.[lo + (hi - lo) / 2] <? x) eqn:Ec.
    + rewrite ltb_spec in Ec.
      assert (Em : (φ (lo + (hi - lo) / 2 + 1)) = ((φ (lo + (hi - lo) / 2)) + 1)%Z) by sia.
      assert (Hres := IH _ ltac:(rewrite <- Hz; apply dec_hi; exact Hlt)
                 (lo + (hi - lo) / 2 + 1) hi (Acc_inv H (dec_hi lo hi Hlt)) r eq_refl
                 ltac:(lia) Hhm).
      destruct Hres as [Hr1 Hr2]; [| exact Hh | exact Hr | split; [lia | exact Hr2]].
      intros q Hq. pose proof (Hpw q (lo + (hi - lo) / 2) ltac:(lia)). lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ec.
      assert (Hres := IH _ ltac:(rewrite <- Hz; apply dec_lo; exact Hlt)
                 lo (lo + (hi - lo) / 2) (Acc_inv H (dec_lo lo hi Hlt)) r eq_refl
                 ltac:(lia) ltac:(lia) Hl).
      destruct Hres as [Hr1 Hr2]; [| exact Hr | split; [lia | exact Hr2]].
      intros q Hq. pose proof (Hpw (lo + (hi - lo) / 2) q ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt. subst r.
    split; [lia | split; [exact Hl |]]. intros q Hq. apply Hh. lia.
Qed.

Lemma inrange_spec : forall S m lo hi, PW S m ->
  inrange S m lo hi = true <->
  exists q, ((φ q) < (φ m))%Z /\ ((φ lo) <= (φ (S.[q])) < (φ hi))%Z.
Proof.
  intros S m lo hi Hpw. unfold inrange.
  pose proof (to_Z_bounded m) as Bm.
  destruct (lbloop_spec S m lo Hpw _ 0 m (Zwf_well_founded 0 (gap m 0)) _ eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(lia)
              ltac:(intros q Hq; change (φ 0) with 0%Z in Hq; pose proof (to_Z_bounded q); lia)
              ltac:(intros q Hq; lia) eq_refl) as (Hr1 & Hr2 & Hr3).
  set (r := lbloop S lo 0 m (Zwf_well_founded 0 (gap m 0))) in *.
  destruct (r <? m) eqn:Erm.
  - rewrite ltb_spec in Erm. rewrite ltb_spec. split.
    + intros Hs. exists r. split; [exact Erm |]. pose proof (Hr3 r ltac:(lia)). lia.
    + intros (q & Hq & Hv). destruct (Z.lt_ge_cases (φ q) (φ r)) as [Hqr | Hqr].
      * pose proof (Hr2 q Hqr). lia.
      * pose proof (Hpw r q ltac:(lia)). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Erm.
    split; [discriminate |]. intros (q & Hq & Hv). pose proof (Hr2 q ltac:(lia)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The table and the scan                                              *)
(* ------------------------------------------------------------------ *)

Lemma build_spec : forall (y : array int) (n L : int) z (T : array int) (i : int)
    (H : Acc (Zwf 0) (gap n i)) r,
  gap n i = z -> PArray.length T = L -> (φ L) = (2 * (φ n))%Z -> ((φ n) <= 100000)%Z ->
  ((φ i) <= (φ n))%Z ->
  (forall j, (0 <= j < (φ i))%Z ->
     T.[of_Z (2 * j)] = y.[of_Z j] * K + of_Z j /\
     T.[of_Z (2 * j + 1)] = alt (y.[of_Z j]) * K + of_Z j) ->
  build y T n i H = r ->
  PArray.length r = L /\
  (forall j, (0 <= j < (φ n))%Z ->
     r.[of_Z (2 * j)] = y.[of_Z j] * K + of_Z j /\
     r.[of_Z (2 * j + 1)] = alt (y.[of_Z j]) * K + of_Z j).
Proof.
  intros y n L z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros T i H r Hz Hlen HL Hn Hin Hinv Hr.
  rewrite build_eq in Hr.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'. cbv zeta in Hr.
    pose proof (to_Z_bounded i) as Bi.
    assert (E2 : (φ (2 * i)) = (2 * (φ i))%Z) by sia.
    assert (E21 : (φ (2 * i + 1)) = (2 * (φ i) + 1)%Z) by sia.
    assert (Ei1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    set (T' := T.[2 * i <- y.[i] * K + i].[2 * i + 1 <- alt y.[i] * K + i]) in Hr.
    assert (Hz' : Zwf 0 (gap n (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hi).
    assert (HlT : PArray.length T' = L) by (unfold T'; rewrite !alength_set; exact Hlen).
    assert (Hb' : ((φ (i + 1)) <= (φ n))%Z) by lia.
    refine (IH _ Hz' T' (i + 1) _ r eq_refl HlT HL Hn Hb' _ Hr).
    intros j Hj. unfold T'.
    destruct (Z.eq_dec j (φ i)) as [-> | Hne].
    + rewrite of_to_Z.
      replace (of_Z (2 * (φ i))) with (2 * i) by (apply to_Z_inj; rewrite of_Z_phi; [lia | rewrite wB_val; lia]).
      replace (of_Z (2 * (φ i) + 1)) with (2 * i + 1) by (apply to_Z_inj; rewrite of_Z_phi; [lia | rewrite wB_val; lia]).
      split.
      * rewrite aget_set_other by (apply int_neq; lia).
        rewrite aget_set_same; [reflexivity | rewrite ltb_spec; lia].
      * rewrite aget_set_same; [reflexivity | rewrite alength_set, ltb_spec; lia].
    + destruct (Hinv j ltac:(lia)) as [Ha Hb].
      rewrite !aget_set_other; try (apply int_neq; rewrite of_Z_phi; [lia | rewrite wB_val; lia]).
      split; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. subst r.
    split; [exact Hlen |]. intros j Hj. apply Hinv. lia.
Qed.

Lemma scan_spec : forall (y S : array int) (s m n : int) z (i : int)
    (H : Acc (Zwf 0) (gap n i)),
  gap n i = z ->
  (scan y S s m n i H = true <->
   exists i', ((φ i) <= (φ i') < (φ n))%Z /\
     (okv S m s (y.[i']) i' = true \/ okv S m s (alt (y.[i'])) i' = true)).
Proof.
  intros y S s m n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz. rewrite scan_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'. cbv zeta.
    assert (Ei1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (okv S m s (y.[i]) i) eqn:E1.
    { split; [intros _; exists i; split; [lia | left; exact E1] | reflexivity]. }
    destruct (okv S m s (alt (y.[i])) i) eqn:E2.
    { split; [intros _; exists i; split; [lia | right; exact E2] | reflexivity]. }
    rewrite (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hi) (i + 1) _ eq_refl).
    split.
    + intros (i' & Hi'' & Hv). exists i'. split; [lia | exact Hv].
    + intros (i' & Hi'' & Hv). exists i'. split; [| exact Hv].
      destruct (Z.eq_dec (φ i') (φ i)) as [E | E]; [| lia].
      apply to_Z_inj in E. subst i'. rewrite E1, E2 in Hv. destruct Hv; discriminate.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [discriminate |]. intros (i' & Hi' & _). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma repr_len : forall (y : array uint) (l : list N), repr y l ->
  (φ (PArray.length y)) = Z.of_nat (List.length l).
Proof. intros y l [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_get_u : forall (y : array uint) (l : list N), repr y l ->
  forall i : int, ((φ i) < Z.of_nat (List.length l))%Z ->
  Z.to_N (φ (y.[i])) = nth (Z.to_nat (φ i)) l 0%N.
Proof.
  intros y l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  symmetry. apply nth_error_nth. exact Hv.
Qed.

Lemma key_phi : forall (c : int) (j : Z),
  (0 <= (φ c) <= 1000000000)%Z -> (0 <= j < 131072)%Z ->
  (φ (c * K + of_Z j)) = ((φ c) * 131072 + j)%Z.
Proof.
  intros c j Hc Hj.
  rewrite add_spec, mul_spec, of_Z_phi by (rewrite wB_val; lia).
  change (φ K) with 131072%Z. rewrite wB_val.
  rewrite (Z.mod_small ((φ c) * 131072)) by lia. apply Z.mod_small. lia.
Qed.

(* The spec's match on the boolean answer, from the iff form. *)
Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P H; [apply H; reflexivity | intros HP; apply H in HP; discriminate].
Qed.

Lemma addemup_impl_correct : forall (s : N) (cards : list N) (x : uint) (y : array uint),
  valid_input s cards -> repr x s -> repr y cards ->
  exists b : bool, repr (addemup_impl x y) b /\ addemup_spec s cards b.
Proof.
  intros s cards x y Hv Hx Hy.
  exists (addemup_impl x y). split; [reflexivity |].
  destruct Hv as [Hn Hc Hs]. unfold len in Hn.
  pose proof (repr_len y cards Hy) as Ly.
  unfold repr, repr_uint in Hx.
  pose proof (to_Z_bounded x) as Bx.
  assert (Hxs : (1 <= (φ x) <= 200000000)%Z) by lia.
  unfold addemup_impl. cbv zeta.
  set (n := PArray.length y) in *.
  assert (Bn : (1 <= (φ n) <= 100000)%Z) by lia.
  (* read the cards as plain ints from here on (one form of [get] for lia) *)
  change (array int) in y.
  (* the cards *)
  assert (CV : forall j : Z, (0 <= j < (φ n))%Z ->
     Z.to_N (φ ((PArray.get@{Set} y (of_Z j)))) = nth (Z.to_nat j) cards 0%N /\
     (1 <= (φ ((PArray.get@{Set} y (of_Z j)))) <= 100000000)%Z).
  { intros j Hj.
    pose proof (repr_get_u y cards Hy (of_Z j)) as E.
    rewrite of_Z_phi in E by (rewrite wB_val; lia).
    specialize (E ltac:(lia)).
    rewrite Forall_forall in Hc.
    pose proof (Hc (nth (Z.to_nat j) cards 0%N) ltac:(apply nth_In; lia)) as Hb.
    split; [exact E |].
    assert (E' : Z.to_N (φ ((PArray.get@{Set} y (of_Z j)))) = nth (Z.to_nat j) cards 0%N) by exact E.
    lia. }
  assert (AS : forall j : Z, (0 <= j < (φ n))%Z ->
     (0 <= (φ (alt ((PArray.get@{Set} y (of_Z j))))) <= 1000000000)%Z /\
     forall v : N, shows (Z.to_N (φ ((PArray.get@{Set} y (of_Z j))))) v <->
       (Z.of_N v = (φ ((PArray.get@{Set} y (of_Z j)))) \/ Z.of_N v = (φ (alt ((PArray.get@{Set} y (of_Z j))))))).
  { intros j Hj. destruct (CV j Hj) as [_ Hb].
    destruct (alt_spec ((PArray.get@{Set} y (of_Z j))) Hb) as [Ha Hsh]. split; [| exact Hsh].
    pose proof (to_Z_bounded (alt ((PArray.get@{Set} y (of_Z j))))). lia. }
  (* the table *)
  set (m := 2 * n).
  assert (Hm2 : (φ m) = (2 * (φ n))%Z) by (unfold m; sia).
  assert (Hmk : PArray.length (PArray.make m 0) = m).
  { rewrite alength_make.
    replace (m <=? PArray.max_length) with true; [reflexivity |].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  set (T := build y (PArray.make m 0) n 0 (Zwf_well_founded 0 (gap n 0))).
  destruct (build_spec y n m _ (PArray.make m 0) 0 (Zwf_well_founded 0 (gap n 0)) T
              eq_refl Hmk Hm2 ltac:(lia) ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros j Hj; change (φ 0) with 0%Z in Hj; lia) eq_refl) as [LT HT].
  pose proof (msort_spec _ T (PArray.make m 0) 0 m m (Zwf_well_founded 0 (gap m 0))
                eq_refl ltac:(change (φ 0) with 0%Z; lia) ltac:(lia) LT Hmk) as HS.
  set (S := fst (msort T (PArray.make m 0) 0 m (Zwf_well_founded 0 (gap m 0)))).
  destruct HS as (LS & _ & _ & SS & PS). fold S in LS, SS, PS.
  change (φ 0) with 0%Z in SS, PS. rewrite Z.sub_0_r in SS, PS.
  pose proof (PW_of_seg S m SS) as PWS.
  (* the keys of the sorted table *)
  assert (KEYS : forall lo hi : int,
    (exists q, ((φ q) < (φ m))%Z /\ ((φ lo) <= (φ (S.[q])) < (φ hi))%Z) <->
    exists j, (0 <= j < (φ n))%Z /\
      (((φ lo) <= (φ ((PArray.get@{Set} y (of_Z j)))) * 131072 + j < (φ hi))%Z \/
       ((φ lo) <= (φ (alt ((PArray.get@{Set} y (of_Z j))))) * 131072 + j < (φ hi))%Z)).
  { intros lo hi.
    transitivity (exists e, In e (seg S 0 (Z.to_nat (φ m))) /\ ((φ lo) <= e < (φ hi))%Z).
    { split.
      - intros (q & Hq & Hv). exists (φ (S.[q])). split; [| exact Hv].
        apply In_seg. exists (φ q). pose proof (to_Z_bounded q).
        rewrite of_to_Z. split; [lia | reflexivity].
      - intros (e & He & Hv). apply In_seg in He. destruct He as (zz & Hzz & ->).
        exists (of_Z zz). rewrite of_Z_phi by (rewrite wB_val; lia). split; [lia | exact Hv]. }
    transitivity (exists e, In e (seg T 0 (Z.to_nat (φ m))) /\ ((φ lo) <= e < (φ hi))%Z).
    { split; intros (e & He & Hv); exists e; (split; [| exact Hv]).
      - exact (Permutation_in _ PS He).
      - exact (Permutation_in _ (Permutation_sym PS) He). }
    split.
    - intros (e & He & Hv). apply In_seg in He. destruct He as (zz & Hzz & ->).
      exists (zz / 2)%Z.
      pose proof (Z.div_mod zz 2 ltac:(lia)). pose proof (Z.mod_pos_bound zz 2 ltac:(lia)).
      assert (Hj : (0 <= zz / 2 < (φ n))%Z) by lia.
      split; [exact Hj |].
      destruct (HT (zz / 2)%Z Hj) as [HT0 HT1].
      destruct (CV (zz / 2)%Z Hj) as [_ Bc]. destruct (AS (zz / 2)%Z Hj) as [Ba _].
      destruct (Z.eq_dec (zz mod 2)%Z 0%Z) as [E | E].
      + left. replace zz with (2 * (zz / 2))%Z in Hv by lia.
        rewrite HT0, key_phi in Hv by lia. exact Hv.
      + right. replace zz with (2 * (zz / 2) + 1)%Z in Hv by lia.
        rewrite HT1, key_phi in Hv by lia. exact Hv.
    - intros (j & Hj & Hv).
      destruct (HT j Hj) as [HT0 HT1].
      destruct (CV j Hj) as [_ Bc]. destruct (AS j Hj) as [Ba _].
      destruct Hv as [Hv | Hv].
      + exists (φ (T.[of_Z (2 * j)])). split.
        * apply In_seg. exists (2 * j)%Z. split; [lia | reflexivity].
        * rewrite HT0, key_phi by lia. exact Hv.
      + exists (φ (T.[of_Z (2 * j + 1)])). split.
        * apply In_seg. exists (2 * j + 1)%Z. split; [lia | reflexivity].
        * rewrite HT1, key_phi by lia. exact Hv. }
  (* the complement search *)
  assert (HK : (φ K) = 131072%Z) by reflexivity.
  assert (FOUND : forall w i : int, ((φ w) <= 200000000)%Z -> ((φ i) < (φ n))%Z ->
    found S m w i = true <->
    exists j, (0 <= j < (φ n))%Z /\ j <> (φ i) /\
      ((φ ((PArray.get@{Set} y (of_Z j)))) = (φ w) \/ (φ (alt ((PArray.get@{Set} y (of_Z j))))) = (φ w))).
  { intros w i Hw Hi.
    pose proof (to_Z_bounded w) as Bw. pose proof (to_Z_bounded i) as Bi.
    assert (E1 : (φ (w * K)) = ((φ w) * 131072)%Z).
    { rewrite mul_spec, HK. apply Z.mod_small. rewrite wB_val. lia. }
    assert (E2 : (φ (w * K + i)) = ((φ w) * 131072 + (φ i))%Z).
    { rewrite add_spec, E1. apply Z.mod_small. rewrite wB_val. lia. }
    assert (E3 : (φ (w * K + i + 1)) = ((φ w) * 131072 + (φ i) + 1)%Z).
    { rewrite add_spec, E2. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val. lia. }
    assert (E4 : (φ ((w + 1) * K)) = (((φ w) + 1) * 131072)%Z).
    { rewrite mul_spec, add_spec, HK. change (φ 1) with 1%Z.
      rewrite (Z.mod_small ((φ w) + 1)) by (rewrite wB_val; lia).
      apply Z.mod_small. rewrite wB_val. lia. }
    unfold found.
    destruct (inrange S m (w * K) (w * K + i)) eqn:R1.
    - split; [intros _ | reflexivity].
      apply (inrange_spec S m _ _ PWS), KEYS in R1.
      destruct R1 as (j & Hj & Hv). rewrite E1, E2 in Hv.
      destruct (CV j Hj) as [_ Bc]. destruct (AS j Hj) as [Ba _].
      exists j. split; [exact Hj | split; [lia |]].
      destruct Hv as [Hv | Hv]; [left | right]; lia.
    - rewrite <- Bool.not_true_iff_false, (inrange_spec S m _ _ PWS), KEYS in R1.
      rewrite (inrange_spec S m _ _ PWS), KEYS. rewrite E3, E4. rewrite E1, E2 in R1.
      split.
      + intros (j & Hj & Hv).
        destruct (CV j Hj) as [_ Bc]. destruct (AS j Hj) as [Ba _].
        exists j. split; [exact Hj | split; [lia |]].
        destruct Hv as [Hv | Hv]; [left | right]; lia.
      + intros (j & Hj & Hne & Hv).
        destruct (CV j Hj) as [_ Bc]. destruct (AS j Hj) as [Ba _].
        destruct (Z.lt_ge_cases j (φ i)) as [Hlt | Hge].
        * exfalso. apply R1. exists j. split; [exact Hj |].
          destruct Hv as [Hv | Hv]; [left | right]; lia.
        * exists j. split; [exact Hj |].
          destruct Hv as [Hv | Hv]; [left | right]; lia. }
  assert (OKV : forall v i : int, ((φ i) < (φ n))%Z ->
    okv S m x v i = true <->
    ((φ v) <= (φ x))%Z /\
    exists j, (0 <= j < (φ n))%Z /\ j <> (φ i) /\
      ((φ ((PArray.get@{Set} y (of_Z j)))) = ((φ x) - (φ v))%Z \/ (φ (alt ((PArray.get@{Set} y (of_Z j))))) = ((φ x) - (φ v))%Z)).
  { intros v i Hi. unfold okv.
    destruct (v <=? x) eqn:Ev.
    - rewrite leb_spec in Ev.
      assert (Es : (φ (x - v)) = ((φ x) - (φ v))%Z) by sia.
      rewrite FOUND by lia. rewrite Es. split; [intros H; split; assumption | intros [_ H]; exact H].
    - rewrite <- Bool.not_true_iff_false, leb_spec in Ev.
      split; [discriminate | intros [H _]; lia]. }
  (* the scan *)
  unfold addemup_spec.
  rewrite (scan_spec y S x m n _ 0 (Zwf_well_founded 0 (gap n 0)) eq_refl).
  change (φ 0) with 0%Z.
  split.
  - intros (i & Hi & Hv).
    pose proof (to_Z_bounded i) as Bi.
    assert (Hyi : (PArray.get@{Set} y (i)) = (PArray.get@{Set} y (of_Z (φ i)))) by (rewrite of_to_Z; reflexivity).
    rewrite Hyi in Hv.
    destruct (CV (φ i) ltac:(lia)) as [Ci Bci]. destruct (AS (φ i) ltac:(lia)) as [Bai Shi].
    assert (G : forall v : int,
      okv S m x v i = true -> shows (Z.to_N (φ ((PArray.get@{Set} y (of_Z (φ i)))))) (Z.to_N (φ v)) ->
      winnable s cards).
    { intros v Ho Hsh. apply OKV in Ho; [| lia].
      destruct Ho as [Hle (j & Hj & Hne & Hw)].
      pose proof (to_Z_bounded v) as Bv.
      destruct (AS j Hj) as [_ Shj]. destruct (CV j Hj) as [Cj _].
      exists (Z.to_N (φ i)), (Z.to_N j), (Z.to_N (φ v)), (Z.to_N ((φ x) - (φ v))).
      unfold len. split; [lia | split; [lia | split; [lia | split; [| split]]]].
      - rewrite Z_N_nat, <- Ci. exact Hsh.
      - rewrite Z_N_nat, <- Cj. apply Shj. lia.
      - lia. }
    destruct Hv as [Hv | Hv].
    + apply (G _ Hv). apply Shi. left. lia.
    + apply (G _ Hv). apply Shi. right. lia.
  - intros (i & j & vi & vj & Hi & Hj & Hne & Hsi & Hsj & Hsum).
    unfold len in Hi, Hj.
    assert (Hi' : (0 <= Z.of_N i < (φ n))%Z) by lia.
    assert (Hj' : (0 <= Z.of_N j < (φ n))%Z) by lia.
    destruct (CV _ Hi') as [Ci _]. destruct (AS _ Hi') as [_ Shi].
    destruct (CV _ Hj') as [Cj _]. destruct (AS _ Hj') as [_ Shj].
    replace (N.to_nat i) with (Z.to_nat (Z.of_N i)) in Hsi by lia.
    replace (N.to_nat j) with (Z.to_nat (Z.of_N j)) in Hsj by lia.
    rewrite <- Ci, Shi in Hsi. rewrite <- Cj, Shj in Hsj.
    exists (of_Z (Z.of_N i)).
    assert (Ei : (φ (of_Z (Z.of_N i))) = Z.of_N i) by (apply of_Z_phi; rewrite wB_val; lia).
    rewrite Ei. split; [lia |].
    destruct Hsi as [Hsi | Hsi]; [left | right]; apply OKV; try lia;
      (split; [lia |]); exists (Z.of_N j); (split; [exact Hj' | split; [lia |]]);
      destruct Hsj as [Hsj | Hsj]; [left | right | left | right]; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition addemup : uint -> array uint -> bool := addemup_impl.
Elpi complexity addemup.

Definition addemup_correct :
  forall (s : N) (cards : list N) (x : uint) (y : array uint),
  valid_input s cards -> repr x s -> repr y cards ->
  exists b : bool, repr (addemup x y) b /\ addemup_spec s cards b
  := addemup_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost: addemup_time                                                  *)
(* ------------------------------------------------------------------ *)

(* One lemma per loop, by induction on a nat bound of its measure:
   rloop <= 19 * 60 + 10 (at most 19 decimal digits in a 63-bit word),
   alt <= 2000, build from i <= (n - i) * 4100 + 10, merge_loop and
   copy_loop from k <= (hi - k) * 100 + 10, msort on [lo, hi) with
   hi - lo <= 2^d: <= s * d * 400 + (2 s + 1) * 100 (s = hi - lo),
   lbloop on [lo, hi) with hi - lo < 2^d: <= d * 100 + 10, inrange,
   found, okv: O(d), scan from i <= (n - i) * (d * 400 + 4600) + 10;
   with d = log2 n + 2 for the table of m = 2n keys, addemup costs at
   most 20000 * ((n + 1) * (log2 n + 1)) + 1000.
   cbn must not unfold φ (the Acc index of rloop, the measures):
   to_Z is made simpl never for this section. *)

Open Scope uint63_scope.
From Stdlib Require Import ssreflect.
Local Arguments Uint63.to_Z : simpl never.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma rotd_time d dC : (cost (rotd_cost stepsCM d dC) <= 30)%nat.
Proof.
  unfold rotd_cost. cost_simpl.
  repeat match goal with |- context [d =? ?k] => cost_destruct (d =? k); cost_simpl end; lia.
Qed.

Lemma rloop_time x xC r rC H HC :
  (cost (extract (extract (rloop_cost stepsCM x xC) r rC) H HC) <= 19 * 60 + 10)%nat.
Proof.
  unfold rloop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC r rC H HC)] =>
    assert (HG : forall k x xC r rC H HC, (φ x < 10 ^ Z.of_nat k)%Z ->
       (cost (G x xC r rC H HC) <= k * 60 + 10)%nat) end.
  { induction k as [|k IH]; intros x' xC' r' rC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (0 <? x') (bool_w (0 <? x'))) as HB;
      cost_destruct (bdec (0 <? x')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). cbn in Hk. lia.
    - lia.
    - pose proof (rotd_time (x' mod 10) (int_val stepsCM (x' mod 10))) as HR.
      cost_destruct (rotd (x' mod 10)); cost_simpl.
      + assert (Hk' : (φ (x' / 10) < 10 ^ Z.of_nat k)%Z).
        { rewrite Uint63.div_spec. change (φ 10) with 10%Z.
          rewrite Nat2Z.inj_succ Z.pow_succ_r in Hk; [lia|].
          apply Z.div_lt_upper_bound; lia. }
        match goal with |- context [@cost ?T (?G' (x' / 10)%uint63 ?a ?b ?c ?d ?e)] =>
          have HI := (IH (x' / 10)%uint63 a b c d e Hk' : (@cost T (G' (x' / 10)%uint63 a b c d e) <= _)%nat) end.
        lia.
      + lia.
    - lia. }
  apply (HG 19%nat). pose proof (to_Z_bounded x).
  change (10 ^ Z.of_nat 19)%Z with 10000000000000000000%Z. change wB with 9223372036854775808%Z in H0. lia.
Qed.

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
Ltac zall f := z0 f; z1 f; z2 f; z3 f; z4 f; z5 f; z6 f.

(* replace the cost of a call by a fresh variable bounded by the lemma *)
Ltac gen_cost X L :=
  match goal with |- context [@cost ?T X] =>
    let Hc := fresh "Hc" in
    have Hc := (L : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end.

Ltac gen_rloop := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (rloop_cost stepsCM ?x ?xC) ?r ?rC) ?H ?HC =>
    gen_cost X (rloop_time x xC r rC H HC) end end.

Lemma alt_time c cC : (cost (alt_cost stepsCM c cC) <= 2000)%nat.
Proof.
  unfold alt_cost. cost_simpl. zall rloop_cost. gen_rloop.
  cost_destruct (rloop c 0 (Zwf_well_founded 0 (φ c))); cost_simpl; lia.
Qed.


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

Ltac rem_rhs := match goal with |- (_ <= ?r)%nat => let R := fresh "R" in remember r as R eqn:ER end.

Ltac gen_alt := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with alt_cost stepsCM ?c ?cC => gen_cost X (alt_time c cC) end end.

Lemma gap_succ hi k : (k <? hi) = true -> (Z.to_nat (gap hi (k + 1)) < Z.to_nat (gap hi k))%nat.
Proof.
  intros H. rewrite Uint63.ltb_spec in H. unfold gap.
  assert (φ (k + 1) = (φ k + 1)%Z) by (zify; Z.to_euclidean_division_equations; lia). lia.
Qed.

Lemma build_time y yC A0 A0C n nC i iC H HC :
  (cost (extract (extract (extract (extract (build_cost stepsCM y yC) A0 A0C) n nC) i iC) H HC) <= Z.to_nat (gap n i) * 4100 + 10)%nat.
Proof.
  unfold build_cost. cbn.
  match goal with |- context [@cost ?T (?G y yC A0 A0C n nC i iC H HC)] =>
    assert (HG : forall m A0 A0C i iC H HC, (Z.to_nat (gap n i) <= m)%nat ->
       (cost (G y yC A0 A0C n nC i iC H HC) <= m * 4100 + 10)%nat) end.
  { induction m as [|m IH]; intros A' AC' i' iC' [g] HC' Hm; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - pose proof (gap_succ n i' e) as Hs.
      assert (Hm' : (Z.to_nat (gap n (i' + 1)) <= m)%nat) by lia.
      zall alt_cost. gen_alt. set_simpl.
      match goal with |- context [@cost ?T (?G' y ?yc ?a ?ac n ?nc (i' + 1)%uint63 ?ic ?h ?hc)] =>
        have HI := (IH a ac (i' + 1)%uint63 ic h hc Hm' : (@cost T (G' y yc a ac n nc (i' + 1)%uint63 ic h hc) <= _)%nat) end.
      subst R. lia.
    - lia. }
  exact (HG _ A0 A0C i iC H HC (le_n _)).
Qed.

Lemma merge_loop_time src srcC dst dstC i iC mid midC j jC hi hiC k kC H HC :
  (cost (extract (extract (extract (extract (extract (extract (extract (merge_loop_cost stepsCM src srcC) dst dstC) i iC) mid midC) j jC) hi hiC) k kC) H HC) <= Z.to_nat (gap hi k) * 100 + 10)%nat.
Proof.
  unfold merge_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G src srcC dst dstC i iC mid midC j jC hi hiC k kC H HC)] =>
    assert (HG : forall m dst dstC i iC j jC k kC H HC, (Z.to_nat (gap hi k) <= m)%nat ->
       (cost (G src srcC dst dstC i iC mid midC j jC hi hiC k kC H HC) <= m * 100 + 10)%nat) end.
  { induction m as [|m IH]; intros dst' dstC' i' iC' j' jC' k' kC' [g] HC' Hm; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (k' <? hi) (bool_w (k' <? hi))) as HB;
      cost_destruct (bdec (k' <? hi)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - pose proof (gap_succ hi k' e) as Hs.
      assert (Hm' : (Z.to_nat (gap hi (k' + 1)) <= m)%nat) by lia.
      cost_destruct (i' <? mid); cost_simpl;
      [cost_destruct (j' <? hi); cost_simpl; [cost_destruct (src.[i'] <=? src.[j']); cost_simpl|]|];
      set_simpl;
      match goal with |- context [@cost ?T (?G' src ?sc ?d ?dc ?i2 ?ic2 mid ?mc ?j2 ?jc2 hi ?hc (k' + 1)%uint63 ?kc ?h ?hc2)] =>
        have HI := (IH d dc i2 ic2 j2 jc2 (k' + 1)%uint63 kc h hc2 Hm' : (@cost T (G' src sc d dc i2 ic2 mid mc j2 jc2 hi hc (k' + 1)%uint63 kc h hc2) <= _)%nat) end;
      subst R; lia.
    - lia. }
  exact (HG _ dst dstC i iC j jC k kC H HC (le_n _)).
Qed.

Lemma copy_loop_time src srcC dst dstC hi hiC k kC H HC :
  (cost (extract (extract (extract (extract (copy_loop_cost stepsCM src srcC) dst dstC) hi hiC) k kC) H HC) <= Z.to_nat (gap hi k) * 100 + 10)%nat.
Proof.
  unfold copy_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G src srcC dst dstC hi hiC k kC H HC)] =>
    assert (HG : forall m dst dstC k kC H HC, (Z.to_nat (gap hi k) <= m)%nat ->
       (cost (G src srcC dst dstC hi hiC k kC H HC) <= m * 100 + 10)%nat) end.
  { induction m as [|m IH]; intros dst' dstC' k' kC' [g] HC' Hm; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (k' <? hi) (bool_w (k' <? hi))) as HB;
      cost_destruct (bdec (k' <? hi)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - pose proof (gap_succ hi k' e) as Hs.
      assert (Hm' : (Z.to_nat (gap hi (k' + 1)) <= m)%nat) by lia.
      set_simpl;
      match goal with |- context [@cost ?T (?G' src ?sc ?d ?dc hi ?hc (k' + 1)%uint63 ?kc ?h ?hc2)] =>
        have HI := (IH d dc (k' + 1)%uint63 kc h hc2 Hm' : (@cost T (G' src sc d dc hi hc (k' + 1)%uint63 kc h hc2) <= _)%nat) end;
      subst R; lia.
    - lia. }
  exact (HG _ dst dstC k kC H HC (le_n _)).
Qed.

Lemma lb_halves lo hi : (lo <? hi) = true ->
  (φ (lo + (hi - lo) / 2) - φ lo = (φ hi - φ lo) / 2 /\
   φ hi - φ (lo + (hi - lo) / 2 + 1) = φ hi - φ lo - (φ hi - φ lo) / 2 - 1)%Z.
Proof.
  intros H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded lo). pose proof (to_Z_bounded hi).
  assert (E1 : (φ (hi - lo) = φ hi - φ lo)%Z) by (zify; Z.to_euclidean_division_equations; lia).
  assert (E2 : (φ ((hi - lo) / 2) = (φ hi - φ lo) / 2)%Z) by (rewrite Uint63.div_spec E1; reflexivity).
  assert (E3 : (φ (lo + (hi - lo) / 2) = φ lo + (φ hi - φ lo) / 2)%Z).
  { rewrite Uint63.add_spec E2. apply Z.mod_small. split; Z.to_euclidean_division_equations; lia. }
  assert (E4 : (φ (lo + (hi - lo) / 2 + 1) = φ lo + (φ hi - φ lo) / 2 + 1)%Z).
  { rewrite Uint63.add_spec E3. change (φ 1) with 1%Z. apply Z.mod_small. Z.to_euclidean_division_equations; lia. }
  rewrite E3 E4. lia.
Qed.

Lemma lbloop_time S SC x xC lo loC hi hiC H HC dd :
  (φ hi - φ lo < 2 ^ Z.of_nat dd)%Z ->
  (cost (extract (extract (extract (extract (lbloop_cost stepsCM S SC) x xC) lo loC) hi hiC) H HC) <= dd * 100 + 10)%nat.
Proof.
  intros Hd0. unfold lbloop_cost. cbn.
  match goal with |- context [@cost ?T (?G S SC x xC lo loC hi hiC H HC)] =>
    assert (HG : forall k lo loC hi hiC H HC, (φ hi - φ lo < 2 ^ Z.of_nat k)%Z ->
       (cost (G S SC x xC lo loC hi hiC H HC) <= k * 100 + 10)%nat) end.
  { clear Hd0; induction k as [|k IH]; intros lo' loC' hi' hiC' [g] HC' Hd; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (lo' <? hi') (bool_w (lo' <? hi'))) as HB;
      cost_destruct (bdec (lo' <? hi')); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). cbn in Hd. lia.
    - subst R; lia.
    - destruct (lb_halves lo' hi' e) as [E1 E2].
      pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      rewrite Nat2Z.inj_succ Z.pow_succ_r in Hd; [lia|].
      assert (Hl : (φ (lo' + (hi' - lo') / 2) - φ lo' < 2 ^ Z.of_nat k)%Z) by (rewrite E1; Z.to_euclidean_division_equations; lia).
      assert (Hr : (φ hi' - φ (lo' + (hi' - lo') / 2 + 1) < 2 ^ Z.of_nat k)%Z) by (rewrite E2; Z.to_euclidean_division_equations; lia).
      clear E1 E2.
      cost_destruct (S.[lo' + (hi' - lo') / 2] <? x); cost_simpl;
      match goal with |- context [@cost ?T (?G' S ?sc x ?xc ?l ?lc ?h ?hc ?p ?pc)] =>
        first [ have HI := (IH l lc h hc p pc Hl : (@cost T (G' S sc x xc l lc h hc p pc) <= _)%nat)
              | have HI := (IH l lc h hc p pc Hr : (@cost T (G' S sc x xc l lc h hc p pc) <= _)%nat) ] end;
      subst R; lia.
    - subst R; lia. }
  exact (HG dd lo loC hi hiC H HC Hd0).
Qed.

Ltac gen_merge := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (extract (merge_loop_cost stepsCM ?s ?sC) ?d ?dC) ?i ?iC) ?m ?mC) ?j ?jC) ?h ?hC) ?k ?kC) ?H ?HC =>
    gen_cost X (merge_loop_time s sC d dC i iC m mC j jC h hC k kC H HC) end end.
Ltac gen_copy := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (copy_loop_cost stepsCM ?s ?sC) ?d ?dC) ?h ?hC) ?k ?kC) ?H ?HC =>
    gen_cost X (copy_loop_time s sC d dC h hC k kC H HC) end end.

Lemma msort_arith (s s1 s2 dd : nat) : (s = s1 + s2 -> 2 <= s ->
  s1 * dd * 400 + (2 * s1 + 1) * 100 + (s2 * dd * 400 + (2 * s2 + 1) * 100) + 2 * (s * 100 + 10) + 100
  <= s * S dd * 400 + (2 * s + 1) * 100)%nat.
Proof. intros -> H. nia. Qed.

Lemma msort_time a aC b bC lo loC hi hiC H HC d :
  (φ hi - φ lo <= 2 ^ Z.of_nat d)%Z ->
  (cost (extract (extract (extract (extract (msort_cost stepsCM a aC) b bC) lo loC) hi hiC) H HC)
     <= Z.to_nat (gap hi lo) * d * 400 + (2 * Z.to_nat (gap hi lo) + 1) * 100)%nat.
Proof.
  intros Hd0. unfold msort_cost. cbn.
  match goal with |- context [@cost ?T (?G a aC b bC lo loC hi hiC H HC)] =>
    assert (HG : forall dd a aC b bC lo loC hi hiC H HC, (φ hi - φ lo <= 2 ^ Z.of_nat dd)%Z ->
       (cost (G a aC b bC lo loC hi hiC H HC) <= Z.to_nat (gap hi lo) * dd * 400 + (2 * Z.to_nat (gap hi lo) + 1) * 100)%nat) end.
  { clear Hd0; induction dd as [|dd IH]; intros a' aC' b' bC' lo' loC' hi' hiC' [g] HC' Hd; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (lo' <? hi') (bool_w (lo' <? hi'))) as HB;
      cost_destruct (bdec (lo' <? hi')); cost_simpl.
    - pose proof (bdec_time (1 <? hi' - lo') (bool_w (1 <? hi' - lo'))) as HB2.
      cost_destruct (bdec (1 <? hi' - lo')); cost_simpl.
      + exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). pose proof (proj1 (Uint63.ltb_spec _ _) e0).
        assert (φ (hi' - lo') = φ hi' - φ lo')%Z by (zify; Z.to_euclidean_division_equations; lia).
        cbn in Hd. lia.
      + subst R. lia.
    - subst R. lia.
    - pose proof (bdec_time (1 <? hi' - lo') (bool_w (1 <? hi' - lo'))) as HB2.
      cost_destruct (bdec (1 <? hi' - lo')); cost_simpl.
      + zall merge_loop_cost. zall copy_loop_cost. gen_merge. gen_copy.
        pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
        pose proof (proj1 (Uint63.ltb_spec _ _) e0) as Hlt2.
        destruct (lb_halves lo' hi' e) as [E1 _].
        assert (Esub : (φ (hi' - lo') = φ hi' - φ lo')%Z) by (zify; Z.to_euclidean_division_equations; lia).
        rewrite Esub in Hlt2. change (φ 1) with 1%Z in Hlt2. clear Esub.
        rewrite Nat2Z.inj_succ Z.pow_succ_r in Hd; [lia|].
        assert (Hl : (φ (lo' + (hi' - lo') / 2) - φ lo' <= 2 ^ Z.of_nat dd)%Z) by (rewrite E1; Z.to_euclidean_division_equations; lia).
        assert (Hr : (φ hi' - φ (lo' + (hi' - lo') / 2) <= 2 ^ Z.of_nat dd)%Z) by (Z.to_euclidean_division_equations; lia).
        match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc lo' ?lc ?m ?mc ?h ?hc)] =>
          have HI1 := (IH a ac b bc lo' lc m mc h hc Hl : (@cost T (G' a ac b bc lo' lc m mc h hc) <= _)%nat);
          revert HI1; generalize (@cost T (G' a ac b bc lo' lc m mc h hc)); intros ? HI1 end.
        match goal with |- context [msort a' b' lo' ?m ?h] =>
          cost_destruct_witness (msort a' b' lo' m h) as [a1 a1C b1 b1C] eqn:EM1 end.
        cost_simpl.
        match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?l ?lc hi' ?hc ?h ?hcc)] =>
          have HI2 := (IH a ac b bc l lc hi' hc h hcc Hr : (@cost T (G' a ac b bc l lc hi' hc h hcc) <= _)%nat);
          revert HI2; generalize (@cost T (G' a ac b bc l lc hi' hc h hcc)); intros ? HI2 end.
        match goal with |- context [msort a1 b1 ?l hi' ?h] =>
          cost_destruct_witness (msort a1 b1 l hi' h) as [a2 a2C b2 b2C] eqn:EM2 end.
        cost_simpl.
        zall merge_loop_cost. zall copy_loop_cost. gen_merge. gen_copy.
        assert (Es : (Z.to_nat (gap hi' lo') = Z.to_nat (gap (lo' + (hi' - lo') / 2) lo') + Z.to_nat (gap hi' (lo' + (hi' - lo') / 2)))%nat) by (unfold gap; lia).
        assert (Hs2 : (2 <= Z.to_nat (gap hi' lo'))%nat) by (unfold gap; lia).
        pose proof (msort_arith _ _ _ dd Es Hs2) as HA.
        clear -HA HI1 HI2 ER HB HB2 Hc Hc0.
        set (s := Z.to_nat (gap hi' lo')) in *.
        set (s1 := Z.to_nat (gap (lo' + (hi' - lo') / 2) lo')) in *.
        set (s2 := Z.to_nat (gap hi' (lo' + (hi' - lo') / 2))) in *.
        clearbody s s1 s2. subst R. lia.
      + subst R. lia.
    - subst R. lia. }
  exact (HG d a aC b bC lo loC hi hiC H HC Hd0).
Qed.

Ltac gen_lb dd Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (lbloop_cost stepsCM ?s ?sC) ?x ?xC) ?l ?lC) ?h ?hC) ?H ?HC =>
    gen_cost X (lbloop_time s sC x xC l lC h hC H HC dd ltac:(unfold gap in *; change (φ 0) with 0%Z; lia)) end end.

Lemma inrange_time S SC m mC lo loC hi hiC dd : (φ m < 2 ^ Z.of_nat dd)%Z ->
  (cost (extract (extract (extract (inrange_cost stepsCM S SC) m mC) lo loC) hi hiC) <= dd * 100 + 40)%nat.
Proof.
  intros Hd. rem_rhs. unfold inrange_cost. cost_simpl. zall lbloop_cost. gen_lb dd Hd.
  cost_destruct (lbloop S lo 0 m (Zwf_well_founded 0 (gap m 0)) <? m); cost_simpl; subst R; lia.
Qed.

Ltac gen_inrange dd Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (inrange_cost stepsCM ?s ?sC) ?m ?mC) ?l ?lC) ?h ?hC =>
    gen_cost X (inrange_time s sC m mC l lC h hC dd Hd) end end.

Lemma found_time S SC m mC w wC i iC dd : (φ m < 2 ^ Z.of_nat dd)%Z ->
  (cost (extract (extract (extract (found_cost stepsCM S SC) m mC) w wC) i iC) <= dd * 200 + 150)%nat.
Proof.
  intros Hd. rem_rhs. unfold found_cost. cost_simpl. zall inrange_cost. gen_inrange dd Hd.
  match goal with |- context [if inrange ?a ?b ?c ?d then _ else _] => cost_destruct (inrange a b c d) end;
    cost_simpl; zall inrange_cost; gen_inrange dd Hd; subst R; lia.
Qed.

Ltac gen_found dd Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (found_cost stepsCM ?s ?sC) ?m ?mC) ?w ?wC) ?i ?iC =>
    gen_cost X (found_time s sC m mC w wC i iC dd Hd) end end.

Lemma okv_time S SC m mC s sC v vC i iC dd : (φ m < 2 ^ Z.of_nat dd)%Z ->
  (cost (extract (extract (extract (extract (okv_cost stepsCM S SC) m mC) s sC) v vC) i iC) <= dd * 200 + 170)%nat.
Proof.
  intros Hd. rem_rhs. unfold okv_cost. cost_simpl.
  cost_destruct (v <=? s); cost_simpl; zall found_cost; gen_found dd Hd; subst R; lia.
Qed.


Ltac gen_okv dd Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (okv_cost stepsCM ?S ?SC) ?m ?mC) ?s ?sC) ?v ?vC) ?i ?iC =>
    gen_cost X (okv_time S SC m mC s sC v vC i iC dd Hd) end end.

Lemma scan_time y yC S SC s sC m mC n nC i iC H HC dd : (φ m < 2 ^ Z.of_nat dd)%Z ->
  (cost (extract (extract (extract (extract (extract (extract (scan_cost stepsCM y yC) S SC) s sC) m mC) n nC) i iC) H HC)
    <= Z.to_nat (gap n i) * (dd * 400 + 4600) + 10)%nat.
Proof.
  intros Hd. unfold scan_cost. cbn.
  match goal with |- context [@cost ?T (?G y yC S SC s sC m mC n nC i iC H HC)] =>
    assert (HG : forall k i iC H HC, (Z.to_nat (gap n i) <= k)%nat ->
       (cost (G y yC S SC s sC m mC n nC i iC H HC) <= k * (dd * 400 + 4600) + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' [g] HC' Hk; rem_rhs;
      cost_simpl;
      pose proof (bdec_time (i' <? n) (bool_w (i' <? n))) as HB;
      cost_destruct (bdec (i' <? n)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - subst R; lia.
    - pose proof (gap_succ n i' e) as Hs.
      assert (Hk' : (Z.to_nat (gap n (i' + 1)) <= k)%nat) by lia.
      zall okv_cost. gen_okv dd Hd.
      cost_destruct (okv S m s y.[i'] i'); cost_simpl; [subst R; lia|].
      zall alt_cost. gen_alt. zall okv_cost. gen_okv dd Hd.
      cost_destruct (okv S m s (alt y.[i']) i'); cost_simpl; [subst R; lia|].
      match goal with |- context [@cost ?T (?G' y ?yc S ?sc s ?ssc m ?mc n ?nc (i' + 1)%uint63 ?ic ?h ?hc)] =>
        have HI := (IH (i' + 1)%uint63 ic h hc Hk' : (@cost T (G' y yc S sc s ssc m mc n nc (i' + 1)%uint63 ic h hc) <= _)%nat) end.
      subst R; lia.
    - subst R; lia. }
  exact (HG _ i iC H HC (le_n _)).
Qed.

Lemma fst_time A (AC : A -> Type) B (BC : B -> Type) p (pC : prod_cost stepsCM A AC B BC p) :
  (cost (extract (extract (fst_cost stepsCM A AC) B BC) p pC) <= 5)%nat.
Proof. unfold fst_cost. destruct pC; cbn; lia. Qed.

Ltac make_simpl :=
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  | |- context [cost (extract (make_cost ?a ?b ?c) ?d ?e)] =>
      change (cost (extract (make_cost a b c) d e)) with 0%nat
  | |- context [cost (make_cost ?a ?b ?c)] =>
      change (cost (make_cost a b c)) with 0%nat
  end.

Ltac gen_build := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (build_cost stepsCM ?y ?yC) ?a ?aC) ?n ?nC) ?i ?iC) ?H ?HC =>
    gen_cost X (build_time y yC a aC n nC i iC H HC) end end.
Ltac gen_msort d Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (msort_cost stepsCM ?a ?aC) ?b ?bC) ?l ?lC) ?h ?hC) ?H ?HC =>
    gen_cost X (msort_time a aC b bC l lC h hC H HC d Hd) end end.
Ltac gen_scan dd Hd := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (scan_cost stepsCM ?y ?yC) ?S ?SC) ?s ?sC) ?m ?mC) ?n ?nC) ?i ?iC) ?H ?HC =>
    gen_cost X (scan_time y yC S SC s sC m mC n nC i iC H HC dd Hd) end end.
Ltac gen_fst := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (fst_cost stepsCM ?A ?AC) ?B ?BC) ?p ?pC =>
    gen_cost X (fst_time A AC B BC p pC) end end.

Lemma top_arith (N L : nat) :
  (N * 4100 + 10 + (2 * N * (L + 2) * 400 + (2 * (2 * N) + 1) * 100) + 5 + (N * ((L + 2) * 400 + 4600) + 10) + 100
   <= 20 * 1000 * ((N + 1) * (L + 1)) + 1000)%nat.
Proof. nia. Qed.


Theorem addemup_time : exists c1 c2 : nat,
  forall (desired_sum : N) (cards : list N)
  (desired_sum_int : uint) (cards_arr : array uint),
  valid_input desired_sum cards ->
  repr desired_sum_int desired_sum -> repr cards_arr cards
  ->
  (cost2 addemup_cost desired_sum_int cards_arr <= c1 * ((size cards_arr + 1) * (Nat.log2 (size cards_arr) + 1)) + c2)%nat.
Proof.
  exists (20 * 1000)%nat, 1000%nat. intros ds cards x y _ _ _.
  rem_rhs.
  unfold cost2, addemup_cost. rewrite call_cost2_eq. cost_simpl.
  zall scan_cost. zall msort_cost. zall build_cost. z0 fst_cost. z1 fst_cost. make_simpl.
  pose proof (PArray.leb_length _ y) as Hlen. rewrite Uint63.leb_spec in Hlen.
  change (φ PArray.max_length) with 4194303%Z in Hlen.
  pose proof (to_Z_bounded (PArray.length y)) as Hlen0.
  assert (E2 : (φ (2 * PArray.length y) = 2 * φ (PArray.length y))%Z).
  { rewrite Uint63.mul_spec. change (φ 2) with 2%Z. apply Z.mod_small. change wB with 9223372036854775808%Z. lia. }
  remember (Z.to_nat (φ (PArray.length y))) as N eqn:EN.
  assert (HP : (2 * N < 2 ^ (Nat.log2 N + 2))%nat).
  { destruct N as [|N']; [cbn; lia|]. pose proof (Nat.log2_spec (S N') ltac:(lia)) as [_ Hs].
    rewrite Nat.pow_add_r. cbn [Nat.pow] in *. lia. }
  assert (HZ : (φ (2 * PArray.length y) < 2 ^ Z.of_nat (Nat.log2 N + 2))%Z).
  { rewrite E2. rewrite <- (Z2Nat.id 2) by lia. rewrite <- Nat2Z.inj_pow.
    change (Z.to_nat 2) with 2%nat. lia. }
  assert (HZ' : (φ (2 * PArray.length y) - φ 0 <= 2 ^ Z.of_nat (Nat.log2 N + 2))%Z) by (change (φ 0) with 0%Z; lia).
  gen_build. gen_msort (Nat.log2 N + 2)%nat HZ'. gen_fst. gen_scan (Nat.log2 N + 2)%nat HZ.
  assert (G1 : Z.to_nat (gap (PArray.length y) 0) = N) by (unfold gap; change (φ 0) with 0%Z; rewrite EN; f_equal; lia).
  assert (G2 : Z.to_nat (gap (2 * PArray.length y) 0) = (2 * N)%nat) by (unfold gap; change (φ 0) with 0%Z; rewrite E2 EN; lia).
  assert (SN : size y = N) by (rewrite EN; reflexivity).
  rewrite G1 in Hc Hc2. rewrite G2 in Hc0. rewrite SN in ER.
  clear -Hc Hc0 Hc1 Hc2 ER.
  set (L := Nat.log2 N) in *. clearbody L. subst R. pose proof (top_arith N L). lia.
Qed.
