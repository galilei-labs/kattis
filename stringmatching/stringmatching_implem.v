(* Implementation of stringmatching (stringmatching.spec): Knuth-Morris-
   Pratt.

   Code.  [find_all xp xt] returns the empty array when |xt| < |xp|.
   Otherwise it builds the failure table once ([build]: one flat
   [array int] of |xp| cells, tbl.[i] = the longest proper border of the
   prefix of length i+1, computed left to right with the same fallback
   [fall] as the scan), then scans the text once left to right ([scan]):
   [fall] extends the matched length q by the next text symbol, falling
   back through tbl.[q-1] on a mismatch; on a full match (q = |xp|) the
   position i+1-|xp| is written into a scratch buffer of |xt|-|xp|+1
   cells and q falls back to tbl.[|xp|-1], so overlapping occurrences are
   found.  At the end the cnt positions found are copied ([copy]) into an
   exactly sized result.  Every array is threaded linearly; the strings
   are only read.  No Z, N or nat in the code.

   [fall] carries one extra comparison, [tbl.[q-1] <? q], as its
   termination guard (the recursion is on an erased [Acc (Zwf 0) (φ q)]);
   the proof shows the guard always holds (a border is shorter than its
   prefix).  The other loops recurse on [Acc (Zwf 0) (gap _ _)] as in
   template/polymul1.

   Proof.  On abstract symbol maps p, u : Z -> Z, [S i q] (the prefix of
   length q of p ends at position i of u) and [border q k]; [tbl_ok F Q]
   says F q is the longest proper border of prefix q for q <= Q.
   [fall_spec]: from S i q, the result r satisfies S (i+1) r and is the
   largest such length below q+1.  [build_spec] (u = p) and [scan_spec]
   (u = the text) are the loop invariants; [occurs_iff_occ] links the
   spec's [occurs_at] (on String.string) to the symbol maps through
   [repr]; [out_ok_correct] reads the math list off the result array. *)

From Stringmatching.spec Require Import Prelude.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.

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

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n i : int) (b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

(* A flat logical buffer backed by two linearly threaded primitive arrays.
   The failure table remains a single primitive array. *)
Definition buffer := (array int * array int)%type.
Definition alen (a : array int) : int := @PArray.length@{Set} int a.
Definition blength (t : buffer) : int :=
  alen (fst t) + alen (snd t).
Definition bget (t : buffer) (i : int) : int :=
  let '(a, b) := t in
  if i <? alen a then a.[i] else b.[i - alen a].
Definition bset (t : buffer) (i v : int) : buffer :=
  let '(a, b) := t in
  if i <? alen a then (a.[i <- v], b)
  else (a, b.[i - alen a <- v]).
Definition bmake (n : int) : buffer :=
  (PArray.make n 0,
   PArray.make (if 4194303 <? n then n - 4194303 else 0) 0).

Local Notation "a .{ i }" := (bget a i) (at level 1, format "a .{ i }").
Local Notation "a .{ i <- v }" := (bset a i v) (at level 1, format "a .{ i  <-  v }").

Lemma array_bound (a : array int) : 0 <= (φ (alen a)) <= 4194303.
Proof.
  pose proof (@leb_length@{Set} int a) as H. rewrite leb_spec, max_length_val in H.
  pose proof (to_Z_bounded (alen a)). unfold alen. lia.
Qed.

Lemma blength_val (t : buffer) :
  (φ (blength t)) = ((φ (alen (fst t))) + (φ (alen (snd t))))%Z.
Proof.
  destruct t as [a b]. unfold blength; cbn -[alen].
  rewrite Uint63.add_spec, Z.mod_small; pose proof (array_bound a);
    pose proof (array_bound b); rewrite ?wB_val; lia.
Qed.

Lemma blength_set t i v : blength t.{i <- v} = blength t.
Proof.
  destruct t as [a b]. unfold bset, blength; cbn -[alen].
  destruct (i <? alen a); unfold alen; cbn; rewrite alength_set; reflexivity.
Qed.

Lemma bget_set_same t i v : (i <? blength t) = true -> t.{i <- v}.{i} = v.
Proof.
  intros H. rewrite ltb_spec, blength_val in H.
  destruct t as [a b]. cbn -[alen] in H. unfold bset, bget; cbn -[alen].
  destruct (i <? alen a) eqn:E; unfold alen in *; cbn; rewrite ?alength_set, E.
  - apply aget_set_same. exact E.
  - apply aget_set_same.
    apply Bool.not_true_iff_false in E. rewrite ltb_spec in E.
    pose proof (array_bound a). pose proof (array_bound b).
    rewrite ltb_spec. sia.
Qed.

Lemma bget_set_other t i j v :
  (φ i) < (φ (blength t)) -> (φ j) < (φ (blength t)) ->
  i <> j -> t.{i <- v}.{j} = t.{j}.
Proof.
  destruct t as [a b]. intros Hi Hj Hne.
  rewrite blength_val in Hi, Hj. cbn -[alen] in Hi, Hj.
  unfold bset, bget; cbn -[alen].
  destruct (i <? alen a) eqn:Ei;
    destruct (j <? alen a) eqn:Ej; unfold alen in *; cbn; rewrite ?alength_set, ?Ej; try reflexivity.
  - apply aget_set_other. exact Hne.
  - apply aget_set_other. intro E. apply Hne. apply to_Z_inj.
    apply Bool.not_true_iff_false in Ei, Ej. rewrite ltb_spec in Ei, Ej.
    pose proof (array_bound a). pose proof (array_bound b).
    pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
    apply (f_equal Uint63.to_Z) in E. sia.
Qed.

Lemma blength_make n : (φ n) <= 8388606 -> blength (bmake n) = n.
Proof.
  intros Hn. apply to_Z_inj. rewrite blength_val.
  unfold bmake, alen; cbn -[PArray.max_length Uint63.to_Z]. fold PArray.max_length.
  rewrite !alength_make.
  destruct (n <=? PArray.max_length) eqn:E;
    destruct (PArray.max_length <? n) eqn:F.
  - rewrite leb_spec, max_length_val in E. rewrite ltb_spec, max_length_val in F. lia.
  - cbn. change ((φ n) + 0 = (φ n))%Z. lia.
  - rewrite ltb_spec, max_length_val in F.
    assert (Hsub : (φ (n - PArray.max_length)) = ((φ n) - 4194303)%Z).
    { rewrite Uint63.sub_spec, max_length_val, Z.mod_small; rewrite ?wB_val; lia. }
    assert (Hle : (n - PArray.max_length <=? PArray.max_length) = true).
    { rewrite leb_spec, Hsub, max_length_val. lia. }
    rewrite Hle, Hsub, max_length_val. lia.
  - apply Bool.not_true_iff_false in E, F.
    rewrite leb_spec, max_length_val in E. rewrite ltb_spec, max_length_val in F. lia.
Qed.

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

Lemma dec_fall : forall q' q : int,
  (q' <? q) = true -> Zwf 0 (φ q') (φ q).
Proof.
  intros q' q H. rewrite ltb_spec in H. pose proof (to_Z_bounded q').
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The fallback of KMP.  q is the length of the current matched prefix
   of the pattern xp, c the next symbol: while the pattern's symbol q
   differs from c, fall back to tbl.[q-1] (the failure value of the prefix
   of length q); return the new matched length (q + 1 on a match, 0 when
   even the empty prefix cannot be extended).  The test [q' <? q] is the
   termination guard (a failure value is always shorter than its prefix,
   so the [right] branch is dead code). *)
Fixpoint fall (xp : PrimString.string) (tbl : array int) (c q : int)
    (H : Acc (Zwf 0) (φ q)) {struct H} : int :=
  if PrimString.get xp q =? c then q + 1
  else match bdec (0 <? q) with
       | left _ =>
           let q' := tbl.[q - 1] in
           match bdec (q' <? q) with
           | left Hlt => fall xp tbl c q' (Acc_inv H (dec_fall q' q Hlt))
           | right _ => 0
           end
       | right _ => 0
       end.

Lemma fall_eq : forall xp tbl c q H,
  fall xp tbl c q H =
  if PrimString.get xp q =? c then q + 1
  else match bdec (0 <? q) with
       | left _ =>
           let q' := tbl.[q - 1] in
           match bdec (q' <? q) with
           | left Hlt => fall xp tbl c q' (Acc_inv H (dec_fall q' q Hlt))
           | right _ => 0
           end
       | right _ => 0
       end.
Proof. intros. destruct H. reflexivity. Qed.

(* The failure table: tbl.[i] := the length of the longest proper border
   of the prefix of length i + 1, for i = 1 .. m-1 (tbl.[0] = 0 from the
   allocation); q is tbl.[i-1]. *)
Fixpoint build (xp : PrimString.string) (m : int) (tbl : array int) (i q : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xp i) q (Zwf_well_founded 0 (φ q)) in
      build xp m tbl.[i <- r] (i + 1) r (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.

Lemma build_eq : forall xp m tbl i q H,
  build xp m tbl i q H =
  match bdec (i <? m) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xp i) q (Zwf_well_founded 0 (φ q)) in
      build xp m tbl.[i <- r] (i + 1) r (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* res.[k] := buf.[k] for k = k0 .. c-1. *)
Fixpoint copy (buf res : buffer) (c k : int)
    (H : Acc (Zwf 0) (gap c k)) {struct H} : buffer :=
  match bdec (k <? c) with
  | left Hk => copy buf res.{k <- buf.{k}} c (k + 1) (Acc_inv H (dec_step c k Hk))
  | right _ => res
  end.

Lemma copy_eq : forall buf res c k H,
  copy buf res c k H =
  match bdec (k <? c) with
  | left Hk => copy buf res.{k <- buf.{k}} c (k + 1) (Acc_inv H (dec_step c k Hk))
  | right _ => res
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* The text scan: i the next text position, q the matched length, the
   occurrences found so far in buf.[0 .. cnt-1]; on a full match record
   i + 1 - m and fall back to tbl.[m-1].  At the end, copy the cnt
   positions into an exactly sized array. *)
Fixpoint scan (xp xt : PrimString.string) (tbl : array int) (m n : int)
    (buf : buffer) (i q cnt : int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : buffer :=
  match bdec (i <? n) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xt i) q (Zwf_well_founded 0 (φ q)) in
      if r =? m then
        scan xp xt tbl m n buf.{cnt <- i + 1 - m} (i + 1) tbl.[m - 1] (cnt + 1)
          (Acc_inv H (dec_step n i Hi))
      else
        scan xp xt tbl m n buf (i + 1) r cnt (Acc_inv H (dec_step n i Hi))
  | right _ => copy buf (bmake cnt) cnt 0 (Zwf_well_founded 0 (gap cnt 0))
  end.

Lemma scan_eq : forall xp xt tbl m n buf i q cnt H,
  scan xp xt tbl m n buf i q cnt H =
  match bdec (i <? n) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xt i) q (Zwf_well_founded 0 (φ q)) in
      if r =? m then
        scan xp xt tbl m n buf.{cnt <- i + 1 - m} (i + 1) tbl.[m - 1] (cnt + 1)
          (Acc_inv H (dec_step n i Hi))
      else
        scan xp xt tbl m n buf (i + 1) r cnt (Acc_inv H (dec_step n i Hi))
  | right _ => copy buf (bmake cnt) cnt 0 (Zwf_well_founded 0 (gap cnt 0))
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition find_all_impl (xp xt : PrimString.string) : buffer :=
  let m := PrimString.length xp in
  let n := PrimString.length xt in
  if n <? m then bmake 0
  else
    let tbl := build xp m (PArray.make m 0) 1 0 (Zwf_well_founded 0 (gap m 1)) in
    scan xp xt tbl m n (bmake (n - m + 1)) 0 0 0
      (Zwf_well_founded 0 (gap n 0)).

(* ------------------------------------------------------------------ *)
(* Prop side: borders and matched prefixes, on abstract symbol maps    *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

Section Borders.
  Variables p u : Z -> Z.

  (* the prefix of length q of p ends at position i of u (exclusive) *)
  Definition S (i q : Z) : Prop :=
    0 <= q <= i /\ forall j, 0 <= j < q -> p j = u (i - q + j).

  (* k is the length of a proper border of the prefix of length q of p *)
  Definition border (q k : Z) : Prop :=
    0 <= k < q /\ forall j, 0 <= j < k -> p j = p (q - k + j).

  Lemma S_border : forall i q k, S i q -> 0 <= k < q -> (S i k <-> border q k).
  Proof.
    intros i q k [Hq Hs] Hk. split.
    - intros [Hk' Hsk]. split; [lia|]. intros j Hj.
      rewrite (Hsk j) by lia. rewrite (Hs (q - k + j)) by lia. f_equal; lia.
    - intros [_ Hb]. split; [lia|]. intros j Hj.
      rewrite (Hb j) by lia. rewrite (Hs (q - k + j)) by lia. f_equal; lia.
  Qed.

  Lemma S_succ : forall i q, 0 <= q -> (S (i + 1) (q + 1) <-> S i q /\ p q = u i).
  Proof.
    intros i q Hq0. split.
    - intros [Hq Hs]. split.
      + split; [lia|]. intros j Hj. rewrite (Hs j) by lia. f_equal; lia.
      + rewrite (Hs q) by lia. f_equal; lia.
    - intros [[Hq Hs] Hpq]. split; [lia|]. intros j Hj.
      destruct (Z.eq_dec j q) as [E | E].
      + subst j. rewrite Hpq. f_equal; lia.
      + rewrite (Hs j) by lia. f_equal; lia.
  Qed.

  Lemma S_zero : forall i, 0 <= i -> S i 0.
  Proof. intros i Hi. split; [lia|]. intros j Hj. lia. Qed.

  Lemma S_pred : forall i k, 1 <= k -> S (i + 1) k -> S i (k - 1) /\ p (k - 1) = u i.
  Proof.
    intros i k Hk H. replace k with (k - 1 + 1) in H by lia.
    apply S_succ in H; [exact H | lia].
  Qed.

  Lemma S_nonneg : forall i q, S i q -> 0 <= q.
  Proof. intros i q [H _]. lia. Qed.

  (* F q is the longest proper border of the prefix of length q, for
     q = 1 .. Q *)
  Definition tbl_ok (F : Z -> Z) (Q : Z) : Prop :=
    forall q, 1 <= q <= Q -> border q (F q) /\ forall k, border q k -> k <= F q.
End Borders.

Lemma border_S : forall p q k, border p q k -> S p p q k.
Proof. intros p q k [Hk Hb]. split; [lia|]. exact Hb. Qed.

Lemma S_border_self : forall p i k, S p p i k -> k < i -> border p i k.
Proof. intros p i k [Hk Hs] Hki. split; [lia|]. exact Hs. Qed.

(* ------------------------------------------------------------------ *)
(* The machine symbols and the machine table                           *)
(* ------------------------------------------------------------------ *)

(* symbol j of a primitive string, as a Z *)
Definition P (x : PrimString.string) (j : Z) : Z := (φ (PrimString.get x (of_Z j))).

(* the failure value of the prefix of length q, read off the table *)
Definition F (tbl : array int) (q : Z) : Z := (φ (tbl.[of_Z (q - 1)])).

Lemma F_get : forall tbl q, 0 < (φ q) -> F tbl (φ q) = (φ (tbl.[q - 1])).
Proof.
  intros tbl q Hq. unfold F. do 2 f_equal.
  rewrite <- (of_to_Z (q - 1)). f_equal. sia.
Qed.

Lemma P_get : forall x q, P x (φ q) = (φ (PrimString.get x q)).
Proof. intros x q. unfold P. rewrite of_to_Z. reflexivity. Qed.

Lemma fall_spec : forall xp tbl (u : Z -> Z) Q c i,
  Q <= 16777211 ->
  tbl_ok (P xp) (F tbl) Q -> (φ c) = u i ->
  forall (z : Z) (q : int) (H : Acc (Zwf 0) (φ q)), (φ q) = z -> (φ q) <= Q ->
  S (P xp) u i (φ q) ->
  S (P xp) u (i + 1) (φ (fall xp tbl c q H)) /\
  (φ (fall xp tbl c q H)) <= (φ q) + 1 /\
  forall k, S (P xp) u (i + 1) k -> k <= (φ q) + 1 -> k <= (φ (fall xp tbl c q H)).
Proof.
  intros xp tbl u Q c i HQ Htbl Hc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros q H Hz HqQ HS.
  pose proof (to_Z_bounded q) as Bq.
  rewrite fall_eq.
  destruct (PrimString.get xp q =? c)%uint63 eqn:Ec.
  - rewrite Uint63.eqb_spec in Ec.
    assert (Hq1 : (φ (q + 1))%uint63 = (φ q) + 1) by sia.
    rewrite Hq1.
    assert (HS1 : S (P xp) u (i + 1) ((φ q) + 1)).
    { apply S_succ; [lia|]. split; [exact HS|]. rewrite P_get, Ec. exact Hc. }
    split; [exact HS1|]. split; [lia|]. intros k _ Hk. exact Hk.
  - rewrite Uint63.eqb_false_spec in Ec.
    assert (Hneq : P xp (φ q) <> u i).
    { rewrite P_get. intro E. apply Ec. apply to_Z_inj. lia. }
    assert (Hi0 : 0 <= i) by (destruct HS; lia).
    destruct (bdec (0 <? q)%uint63) as [H0 | H0].
    + rewrite ltb_spec in H0. change (φ 0) with 0 in H0.
      destruct (Htbl (φ q) ltac:(lia)) as [Hb Hmax].
      cbv zeta.
      destruct (bdec (tbl.[q - 1] <? q)%uint63) as [Hlt | Hlt].
      * assert (Hq'F : (φ (tbl.[q - 1])) = F tbl (φ q)) by (rewrite F_get by lia; reflexivity).
        assert (HS' : S (P xp) u i (φ (tbl.[q - 1]))).
        { rewrite Hq'F. apply (S_border _ _ i (φ q)); [exact HS | destruct Hb; lia | exact Hb]. }
        destruct Hb as [Hbr _].
        destruct (IH (φ (tbl.[q - 1])) ltac:(rewrite <- Hz; unfold Zwf; lia)
                    (tbl.[q - 1]) (Acc_inv H (dec_fall (tbl.[q - 1]) q Hlt)) eq_refl ltac:(lia) HS') as [R1 [R2 R3]].
        split; [exact R1|]. split; [lia|].
        intros k Hk Hkq.
        destruct (Z.eq_dec k ((φ q) + 1)) as [E | E].
        { subst k. apply S_succ in Hk; [| lia]. destruct Hk as [_ Hk]. contradiction. }
        destruct (Z_lt_le_dec k 1) as [Hk1 | Hk1].
        { pose proof (S_nonneg _ _ _ _ Hk). pose proof (S_nonneg _ _ _ _ R1). lia. }
        destruct (S_pred _ _ _ _ Hk1 Hk) as [Hk' _].
        assert (Hbk : border (P xp) (φ q) (k - 1)).
        { apply (proj1 (S_border (P xp) u i (φ q) (k - 1) HS ltac:(lia))). exact Hk'. }
        pose proof (Hmax _ Hbk). apply R3; [exact Hk | lia].
      * rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
        destruct Hb as [Hbr _]. rewrite F_get in Hbr by lia. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in H0. change (φ 0) with 0 in H0.
      change (φ 0) with 0.
      assert (Eq0 : (φ q) = 0) by lia.
      split; [apply S_zero; lia|]. split; [lia|].
      intros k Hk Hkq. pose proof (S_nonneg _ _ _ _ Hk).
      destruct (Z.eq_dec k 1) as [E | E]; [|lia].
      subst k. apply S_pred in Hk; [| lia]. destruct Hk as [_ Hk].
      replace (1 - 1) with (φ q) in Hk by lia. contradiction.
Qed.

(* The table construction. *)
Lemma build_spec : forall xp (m : int), (φ m) <= 16777211 ->
  forall (z : Z) (i : int) (tbl : array int) (q : int) (H : Acc (Zwf 0) (gap m i)),
  gap m i = z ->
  PArray.length tbl = m -> 1 <= (φ i) <= (φ m) ->
  tbl_ok (P xp) (F tbl) (φ i) -> (φ q) = F tbl (φ i) ->
  PArray.length (build xp m tbl i q H) = m /\
  tbl_ok (P xp) (F (build xp m tbl i q H)) (φ m).
Proof.
  intros xp m Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i tbl q H Hz Hlen Hi Htbl Hq.
  rewrite build_eq.
  destruct (bdec (i <? m)%uint63) as [Hlt | Hlt].
  - cbv zeta. pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    destruct (Htbl (φ i) ltac:(lia)) as [Hbi Hmaxi].
    destruct (fall_spec xp tbl (P xp) (φ i) (PrimString.get xp i) (φ i) ltac:(lia)
                Htbl (eq_sym (P_get xp i)) _ q (Zwf_well_founded 0 (φ q)) eq_refl
                ltac:(destruct Hbi; lia)
                ltac:(rewrite Hq; apply border_S; exact Hbi)) as [R1 [R2 R3]].
    set (r := fall xp tbl (PrimString.get xp i) q (Zwf_well_founded 0 (φ q))) in *.
    pose proof (S_nonneg _ _ _ _ R1) as Hr0.
    assert (HF : forall q', 1 <= q' <= (φ i) -> F tbl.[i <- r] q' = F tbl q').
    { intros q' Hq'. unfold F. rewrite aget_set_other; [reflexivity|].
      intro E. apply (f_equal to_Z) in E.
      rewrite of_Z_spec, Z.mod_small in E by (pose proof (to_Z_bounded i); rewrite wB_val; lia).
      lia. }
    assert (HFi : F tbl.[i <- r] ((φ i) + 1) = (φ r)).
    { unfold F. replace ((φ i) + 1 - 1) with (φ i) by lia. rewrite of_to_Z.
      rewrite aget_set_same; [reflexivity|]. rewrite Hlen. exact Hlt. }
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity
               | rewrite alength_set; exact Hlen | lia | | ];
      rewrite Hi1.
    + intros q' Hq'. destruct (Z.eq_dec q' ((φ i) + 1)) as [E | E].
      * subst q'. rewrite HFi. split.
        { apply S_border_self; [exact R1 | destruct Hbi; lia]. }
        intros k Hk. pose proof Hk as [Hk0 _].
        destruct (Z_lt_le_dec k 1) as [Hk1 | Hk1]; [lia|].
        apply border_S in Hk.
        destruct (S_pred _ _ _ _ Hk1 Hk) as [Hk' _].
        apply S_border_self in Hk'; [| lia].
        pose proof (Hmaxi _ Hk'). apply R3; [exact Hk | lia].
      * rewrite HF by lia. apply Htbl. lia.
    + rewrite HFi. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hlen|]. replace (φ m) with (φ i) by lia. exact Htbl.
Qed.

(* The final copy. *)
Lemma copy_spec : forall (buf : buffer) (c : int),
  forall (z : Z) (k : int) (res : buffer) (H : Acc (Zwf 0) (gap c k)),
  gap c k = z -> blength res = c -> (φ k) <= (φ c) ->
  (forall k' : int, (φ k') < (φ k) -> res.{k'} = buf.{k'}) ->
  blength (copy buf res c k H) = c /\
  forall k' : int, (φ k') < (φ c) -> (copy buf res c k H).{k'} = buf.{k'}.
Proof.
  intros buf c z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k res H Hz Hlen Hkc Hc.
  rewrite copy_eq.
  destruct (bdec (k <? c)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hk1 : (φ (k + 1))%uint63 = (φ k) + 1) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity
               | rewrite blength_set; exact Hlen | lia | ].
    intros k' Hk'. rewrite Hk1 in Hk'.
    destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
    + apply to_Z_inj in E. subst k'.
      apply bget_set_same. rewrite Hlen. exact Hlt.
    + rewrite bget_set_other; [|rewrite Hlen; lia|rewrite Hlen; lia|intro F'; apply E; rewrite F'; reflexivity].
      apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hlen|]. intros k' Hk'. apply Hc. lia.
Qed.

(* pat occurs in txt at s, on the symbol maps *)
Definition occ (xp xt : PrimString.string) (m s : Z) : Prop :=
  forall j, 0 <= j < m -> P xp j = P xt (s + j).

(* res lists, strictly ascending, exactly the occurrences *)
Definition out_ok (xp xt : PrimString.string) (m n : Z) (res : buffer) : Prop :=
  (forall k1 k2, 0 <= k1 < k2 /\ k2 < (φ (blength res)) ->
     (φ (res.{of_Z k1})) < (φ (res.{of_Z k2}))) /\
  (forall s, (exists k, 0 <= k < (φ (blength res)) /\ (φ (res.{of_Z k})) = s) <->
             (0 <= s /\ s + m <= n /\ occ xp xt m s)).

Lemma get_set_Z : forall (t : buffer) (c v : int) (k : Z),
  0 <= k <= (φ c) -> (c <? blength t)%uint63 = true ->
  (φ (t.{c <- v}.{of_Z k})) = if Z.eq_dec k (φ c) then (φ v) else (φ (t.{of_Z k})).
Proof.
  intros t c v k Hk Hc. pose proof (to_Z_bounded c) as Bc.
  destruct (Z.eq_dec k (φ c)) as [E | E].
  - subst k. rewrite of_to_Z, bget_set_same by exact Hc. reflexivity.
  - rewrite bget_set_other; [reflexivity|rewrite ltb_spec in Hc; lia|
      rewrite of_Z_spec, Z.mod_small by lia; rewrite ltb_spec in Hc; lia|].
    intro E'. apply E.
    rewrite E', of_Z_spec, Z.mod_small; [reflexivity | lia].
Qed.

Lemma of_Z_to_Z : forall k, 0 <= k < wB -> (φ (of_Z k)) = k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. exact Hk. Qed.

(* The text scan. *)
Lemma scan_spec : forall xp xt (tbl : array int) (m n : int),
  tbl_ok (P xp) (F tbl) (φ m) -> 1 <= (φ m) <= (φ n) -> (φ n) <= 5000000 ->
  forall (z : Z) (i q cnt : int) (buf : buffer) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> (φ i) <= (φ n) ->
  S (P xp) (P xt) (φ i) (φ q) -> (φ q) < (φ m) ->
  (forall k, k < (φ m) -> S (P xp) (P xt) (φ i) k -> k <= (φ q)) ->
  (φ (blength buf)) = (φ n) - (φ m) + 1 ->
  (φ cnt) <= Z.max 0 ((φ i) - (φ m) + 1) ->
  (forall k1 k2, 0 <= k1 < k2 /\ k2 < (φ cnt) ->
     (φ (buf.{of_Z k1})) < (φ (buf.{of_Z k2}))) ->
  (forall s, (exists k, 0 <= k < (φ cnt) /\ (φ (buf.{of_Z k})) = s) <->
             (0 <= s /\ s + (φ m) <= (φ i) /\ occ xp xt (φ m) s)) ->
  out_ok xp xt (φ m) (φ n) (scan xp xt tbl m n buf i q cnt H).
Proof.
  intros xp xt tbl m n Htbl Hmn Hn z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i q cnt buf H Hz Hin HS Hqm Hmax Hbl Hcnt Hasc Hset.
  pose proof (to_Z_bounded cnt) as Bcnt.
  rewrite scan_eq.
  destruct (bdec (i <? n)%uint63) as [Hlt | Hlt].
  - cbv zeta. pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1))%uint63 = (φ i) + 1) by sia.
    destruct (fall_spec xp tbl (P xt) (φ m) (PrimString.get xt i) (φ i) ltac:(lia)
                Htbl (eq_sym (P_get xt i)) _ q (Zwf_well_founded 0 (φ q)) eq_refl
                ltac:(lia) HS) as [R1 [R2 R3]].
    set (r := fall xp tbl (PrimString.get xt i) q (Zwf_well_founded 0 (φ q))) in *.
    pose proof (S_nonneg _ _ _ _ R1) as Hr0.
    assert (Hmaxr : forall k, k <= (φ m) -> S (P xp) (P xt) ((φ i) + 1) k -> k <= (φ r)).
    { intros k Hk HSk. destruct (Z_lt_le_dec k 1) as [Hk1 | Hk1].
      - pose proof (S_nonneg _ _ _ _ HSk). lia.
      - destruct (S_pred _ _ _ _ Hk1 HSk) as [HSk' _].
        pose proof (Hmax (k - 1) ltac:(lia) HSk'). apply R3; [exact HSk | lia]. }
    destruct (r =? m)%uint63 eqn:Er.
    + rewrite Uint63.eqb_spec in Er. rewrite Er in R1.
      assert (Hmi : (φ m) <= (φ i) + 1) by (destruct R1 as [? _]; lia).
      assert (Hs : (φ (i + 1 - m))%uint63 = (φ i) + 1 - (φ m)) by sia.
      destruct (Htbl (φ m) ltac:(lia)) as [Hbm Hmaxm].
      assert (HqF : (φ (tbl.[m - 1])) = F tbl (φ m)) by (rewrite F_get by lia; reflexivity).
      assert (Hcb : (cnt <? blength buf)%uint63 = true) by (rewrite ltb_spec; lia).
      assert (Hc1 : (φ (cnt + 1))%uint63 = (φ cnt) + 1) by sia.
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | | | | | | | | ];
        rewrite ?Hi1, ?Hc1, ?HqF.
      * lia.
      * apply (proj2 (S_border (P xp) (P xt) ((φ i) + 1) (φ m) (F tbl (φ m)) R1
                        ltac:(destruct Hbm; lia))). exact Hbm.
      * destruct Hbm; lia.
      * intros k Hk HSk. apply Hmaxm.
        apply (proj1 (S_border _ _ ((φ i) + 1) (φ m) k R1
                        ltac:(pose proof (S_nonneg _ _ _ _ HSk); lia))). exact HSk.
      * rewrite blength_set. exact Hbl.
      * lia.
      * intros k1 k2 Hk. rewrite !get_set_Z by (auto; lia).
        destruct (Z.eq_dec k2 (φ cnt)), (Z.eq_dec k1 (φ cnt)); try lia.
        -- rewrite Hs.
           assert (Hk1 : 0 <= k1 < (φ cnt)) by lia.
           destruct (proj1 (Hset (φ (buf.{of_Z k1})))
                       (ex_intro _ k1 (conj Hk1 eq_refl))) as [_ [Hx _]].
           lia.
        -- apply Hasc. lia.
      * intros s. split.
        -- intros [k [Hk Hks]]. rewrite get_set_Z in Hks by (auto; lia).
           destruct (Z.eq_dec k (φ cnt)).
           ++ rewrite Hs in Hks. subst s. split; [lia|]. split; [lia|].
              exact (proj2 R1).
           ++ assert (Hk' : 0 <= k < (φ cnt)) by lia.
              destruct (proj1 (Hset s) (ex_intro _ k (conj Hk' Hks)))
                as [A [B C]].
              split; [lia|]. split; [lia | exact C].
        -- intros [A [B C]]. destruct (Z.eq_dec (s + (φ m)) ((φ i) + 1)).
           ++ exists (φ cnt). split; [lia|]. rewrite get_set_Z by (auto; lia).
              destruct (Z.eq_dec (φ cnt) (φ cnt)); [|lia]. rewrite Hs. lia.
           ++ assert (B' : s + (φ m) <= (φ i)) by lia.
              destruct (proj2 (Hset s) (conj A (conj B' C))) as [k [Hk Hks]].
              exists k. split; [lia|]. rewrite get_set_Z by (auto; lia).
              destruct (Z.eq_dec k (φ cnt)); [lia|]. exact Hks.
    + rewrite Uint63.eqb_false_spec in Er.
      assert (Hrm : (φ r) <> (φ m)) by (intro E; apply Er; apply to_Z_inj; exact E).
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | | | | | | | | ];
        rewrite ?Hi1.
      * lia.
      * exact R1.
      * lia.
      * intros k Hk HSk. apply Hmaxr; [lia | exact HSk].
      * exact Hbl.
      * lia.
      * exact Hasc.
      * intros s. rewrite Hset. split.
        -- intros [A [B C]]. split; [exact A|]. split; [lia | exact C].
        -- intros [A [B C]]. split; [exact A|]. split; [|exact C].
           destruct (Z.eq_dec (s + (φ m)) ((φ i) + 1)) as [E | E]; [|lia].
           assert (HSm : S (P xp) (P xt) ((φ i) + 1) (φ m)).
           { split; [lia|]. intros j Hj. rewrite (C j Hj). f_equal. lia. }
           pose proof (Hmaxr (φ m) ltac:(lia) HSm). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    assert (Hcn : (φ cnt) <= 5000000) by lia.
    assert (Hml : blength (bmake cnt) = cnt) by (apply blength_make; lia).
    destruct (copy_spec buf cnt _ 0 (bmake cnt) (Zwf_well_founded 0 (gap cnt 0))
                eq_refl Hml ltac:(change (φ 0) with 0; lia)
                ltac:(intros k' Hk'; change (φ 0) with 0 in Hk';
                      pose proof (to_Z_bounded k'); lia)) as [Hrl Hrc].
    set (res := copy buf (bmake cnt) cnt 0 (Zwf_well_founded 0 (gap cnt 0))) in *.
    assert (Hcell : forall k, 0 <= k < (φ cnt) -> res.{of_Z k} = buf.{of_Z k}).
    { intros k Hk. apply Hrc. rewrite of_Z_to_Z by (rewrite wB_val; lia). lia. }
    unfold out_ok. rewrite Hrl. split.
    + intros k1 k2 Hk. rewrite !Hcell by lia. apply Hasc. exact Hk.
    + intros s. replace (φ n) with (φ i) by lia. rewrite <- Hset. split.
      * intros [k [Hk Hks]]. exists k. split; [exact Hk|]. rewrite <- Hcell by lia. exact Hks.
      * intros [k [Hk Hks]]. exists k. split; [exact Hk|]. rewrite Hcell by lia. exact Hks.
Qed.

(* ------------------------------------------------------------------ *)
(* The math side: occurs_at on the symbol maps                         *)
(* ------------------------------------------------------------------ *)

Lemma slength_app : forall s1 s2 : string,
  String.length (s1 ++ s2) = (String.length s1 + String.length s2)%nat.
Proof. induction s1 as [| c s1 IH]; intros s2; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma substring_length : forall (s : string) (n l : nat),
  (n + l <= String.length s)%nat -> String.length (substring n l s) = l.
Proof.
  induction s as [| c s IH]; intros n l H.
  - destruct n, l; simpl in *; try reflexivity; lia.
  - destruct n as [| n], l as [| l]; simpl in *.
    + reflexivity.
    + f_equal. apply IH. lia.
    + apply IH. lia.
    + apply IH. lia.
Qed.

Lemma get_none : forall (s : string) (n : nat),
  (String.length s <= n)%nat -> String.get n s = None.
Proof.
  induction s as [| c s IH]; intros [| n] H; simpl in *; try reflexivity; try lia.
  apply IH. lia.
Qed.

Lemma occurs_at_iff : forall (pat txt : string) (i : N),
  occurs_at pat txt i <->
  (N.to_nat i + String.length pat <= String.length txt)%nat /\
  forall j, (j < String.length pat)%nat ->
    String.get j pat = String.get (N.to_nat i + j) txt.
Proof.
  intros pat txt i. split.
  - intros [pre [post [E Hl]]]. unfold slen in Hl.
    assert (Hi : N.to_nat i = String.length pre) by lia.
    rewrite Hi. subst txt. rewrite !slength_app. split; [lia|].
    intros j Hj. rewrite Nat.add_comm, <- append_correct2.
    apply append_correct1. exact Hj.
  - intros [Hl Hg].
    set (k := N.to_nat i) in *.
    set (lp := String.length pat) in *.
    set (pre := substring 0 k txt).
    set (post := substring (k + lp) (String.length txt - k - lp) txt).
    assert (Hpre : String.length pre = k) by (apply substring_length; lia).
    exists pre, post. split.
    + apply (proj1 (get_correct _ _)). intros p.
      destruct (Compare_dec.lt_dec p k) as [Hp | Hp].
      * rewrite <- append_correct1 by lia. unfold pre.
        rewrite substring_correct1 by lia. rewrite Nat.add_0_r. reflexivity.
      * replace (String.get p (pre ++ pat ++ post)) with (String.get (p - k) (pat ++ post))
          by (rewrite (append_correct2 pre (pat ++ post) (p - k)), Hpre; f_equal; lia).
        destruct (Compare_dec.lt_dec (p - k) lp) as [Hq | Hq].
        -- rewrite <- append_correct1 by exact Hq. rewrite Hg by exact Hq.
           f_equal. lia.
        -- replace (String.get (p - k) (pat ++ post)) with (String.get (p - k - lp) post)
             by (rewrite (append_correct2 pat post (p - k - lp)); f_equal; unfold lp in *; lia).
           unfold post.
           destruct (Compare_dec.lt_dec (p - k - lp) (String.length txt - k - lp)) as [Hr | Hr].
           ++ rewrite substring_correct1 by exact Hr. f_equal. lia.
           ++ rewrite substring_correct2 by lia. apply get_none. lia.
    + unfold slen. rewrite Hpre. unfold k. apply N2Nat.id.
Qed.

Lemma repr_char : forall (x : PrimString.string) (s : string), repr x s ->
  forall j, (j < String.length s)%nat ->
  exists c, String.get j s = Some c /\ P x (Z.of_nat j) = Z.of_N (N_of_ascii c).
Proof.
  intros x s [Hl Hc] j Hj. destruct (Hc j Hj) as [c [Hg Hr]].
  exists c. split; [exact Hg|].
  unfold repr, repr_uint in Hr. unfold P. rewrite <- Hr.
  rewrite Z2N.id; [reflexivity|].
  pose proof (to_Z_bounded (PrimString.get x (of_nat j))). lia.
Qed.

Lemma ascii_eq_iff : forall c1 c2 : ascii,
  Some c1 = Some c2 <-> Z.of_N (N_of_ascii c1) = Z.of_N (N_of_ascii c2).
Proof.
  intros c1 c2. split.
  - intros E. inversion E. reflexivity.
  - intros E. apply N2Z.inj in E.
    rewrite <- (ascii_N_embedding c1), <- (ascii_N_embedding c2), E. reflexivity.
Qed.

Lemma occurs_iff_occ : forall pat txt xp xt,
  repr xp pat -> repr xt txt -> forall i : N,
  occurs_at pat txt i <->
  (Z.of_N i + (φ (PrimString.length xp)) <= (φ (PrimString.length xt)) /\
   occ xp xt (φ (PrimString.length xp)) (Z.of_N i)).
Proof.
  intros pat txt xp xt Hp Ht i.
  pose proof (proj1 Hp) as Hlp. pose proof (proj1 Ht) as Hlt.
  rewrite occurs_at_iff. split.
  - intros [Hle Hg]. split; [lia|].
    intros j Hj.
    destruct (repr_char xp pat Hp (Z.to_nat j) ltac:(lia)) as [c1 [G1 E1]].
    destruct (repr_char xt txt Ht (N.to_nat i + Z.to_nat j) ltac:(lia)) as [c2 [G2 E2]].
    rewrite Z2Nat.id in E1 by lia.
    replace (Z.of_nat (N.to_nat i + Z.to_nat j)) with (Z.of_N i + j) in E2 by lia.
    rewrite E1, E2. apply ascii_eq_iff. rewrite <- G1, <- G2. apply Hg. lia.
  - intros [Hle Hocc]. split; [lia|].
    intros j Hj.
    destruct (repr_char xp pat Hp j Hj) as [c1 [G1 E1]].
    destruct (repr_char xt txt Ht (N.to_nat i + j) ltac:(lia)) as [c2 [G2 E2]].
    replace (Z.of_nat (N.to_nat i + j)) with (Z.of_N i + Z.of_nat j) in E2 by lia.
    rewrite G1, G2. apply ascii_eq_iff. rewrite <- E1, <- E2. apply Hocc. lia.
Qed.

Lemma buffer_repr (res : buffer) :
  positions_repr res
    (map (fun k => Z.to_N (φ (res.{of_Z (Z.of_nat k)})))
      (seq 0 (Z.to_nat (φ (blength res))))).
Proof.
  destruct res as [a b].
  set (A := Z.to_nat (φ (alen a))).
  set (B := Z.to_nat (φ (alen b))).
  set (f := fun k => Z.to_N (φ ((a,b).{of_Z (Z.of_nat k)}))).
  assert (LA : Z.of_nat A = (φ (alen a))) by (unfold A; pose proof (array_bound a); lia).
  assert (LB : Z.of_nat B = (φ (alen b))) by (unfold B; pose proof (array_bound b); lia).
  exists (map f (seq 0 A)), (map f (seq A B)). split.
  - split; split; cbn [fst snd]; rewrite ?length_map, ?length_seq; try (exact LA); try (exact LB).
    + intros k Hk. exists (f k). split.
      * rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k A); [reflexivity|lia].
      * unfold repr, repr_uint, f, bget; cbn -[alen Uint63.to_Z].
        assert (E : (of_Z (Z.of_nat k) <? alen a)%uint63 = true).
        { rewrite ltb_spec, of_Z_to_Z; pose proof (array_bound a); rewrite ?wB_val; lia. }
        rewrite E at 1. reflexivity.
    + intros k Hk. exists (f (A + k)%nat). split.
      * rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k B); [reflexivity|lia].
      * unfold repr, repr_uint, f, bget; cbn -[alen Uint63.to_Z].
        assert (E : (of_Z (Z.of_nat (A+k)) <? alen a)%uint63 = false).
        { apply Bool.not_true_iff_false. rewrite ltb_spec, Nat2Z.inj_add.
          rewrite LA. apply Nat2Z.inj_lt in Hk. rewrite LB in Hk.
          rewrite of_Z_to_Z by
            (rewrite wB_val; pose proof (array_bound a); pose proof (array_bound b);
              pose proof (Nat2Z.is_nonneg k); lia).
          lia. }
        rewrite E at 1. replace (of_Z (Z.of_nat (A+k)) - alen a)%uint63 with (of_nat k).
        -- reflexivity.
        -- apply to_Z_inj. rewrite Nat2Z.inj_add.
           rewrite of_Z_to_Z by
             (rewrite wB_val; pose proof (array_bound a); pose proof (array_bound b); lia).
           pose proof (array_bound a). pose proof (array_bound b).
           sia.
  - change (map f (seq 0 (Z.to_nat (φ (blength (a,b))))) =
      map f (seq 0 A) ++ map f (seq A B)).
    rewrite blength_val. cbn -[alen Uint63.to_Z].
    replace (Z.to_nat ((φ (alen a)) + (φ (alen b)))) with (A+B)%nat by lia.
    rewrite seq_app, map_app. reflexivity.
Qed.

(* From the machine output to the math output. *)
Lemma out_ok_correct : forall pat txt xp xt (res : buffer),
  repr xp pat -> repr xt txt ->
  out_ok xp xt (φ (PrimString.length xp)) (φ (PrimString.length xt)) res ->
  exists ps : list N, positions_repr res ps /\ find_all_spec pat txt ps.
Proof.
  intros pat txt xp xt res Hp Ht [Hasc Hset].
  set (L := Z.to_nat (φ (blength res))).
  set (f := fun k : nat => Z.to_N (φ (res.{of_Z (Z.of_nat k)}))).
  exists (map f (seq 0 L)).
  pose proof (to_Z_bounded (blength res)) as BL.
  assert (Hlen : List.length (map f (seq 0 L)) = L) by (rewrite length_map, length_seq; reflexivity).
  assert (Hnth : forall k, (k < L)%nat -> nth_error (map f (seq 0 L)) k = Some (f k)).
  { intros k Hk. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k L); [reflexivity | lia]. }
  split; [apply buffer_repr|split].
  - intros t u Htu. unfold len in Htu. rewrite Hlen in Htu.
    unfold get_list_N.
    rewrite (nth_error_nth _ _ _ (Hnth (N.to_nat t) ltac:(lia))).
    rewrite (nth_error_nth _ _ _ (Hnth (N.to_nat u) ltac:(lia))).
    unfold f.
    assert (Hk : 0 <= Z.of_nat (N.to_nat t) < Z.of_nat (N.to_nat u) /\
                 Z.of_nat (N.to_nat u) < (φ (blength res))) by (unfold L in *; lia).
    pose proof (Hasc _ _ Hk) as Hlt.
    apply Z2N.inj_lt; [apply (proj1 (to_Z_bounded _)) | apply (proj1 (to_Z_bounded _)) | exact Hlt].
  - intros i. rewrite (occurs_iff_occ pat txt xp xt Hp Ht i).
    rewrite in_map_iff. split.
    + intros [k [Hfk Hk]]. rewrite in_seq in Hk.
       assert (Hs : exists kz, 0 <= kz < (φ (blength res)) /\
                    (φ (res.{of_Z kz})) = Z.of_N i).
      { exists (Z.of_nat k). split; [unfold L in *; lia|].
        rewrite <- Hfk. unfold f.
         pose proof (to_Z_bounded (res.{of_Z (Z.of_nat k)})). lia. }
      apply Hset in Hs. destruct Hs as [_ [A B]]. split; [exact A | exact B].
    + intros [A B].
      destruct (proj2 (Hset (Z.of_N i)) (conj (N2Z.is_nonneg i) (conj A B)))
        as [kz [Hkz Hks]].
      exists (Z.to_nat kz). split.
      * unfold f. rewrite Z2Nat.id by lia.
        transitivity (Z.to_N (Z.of_N i)); [f_equal; exact Hks | apply N2Z.id].
      * rewrite in_seq. split; [lia|]. simpl. unfold L.
        apply Z2Nat.inj_lt; [lia | apply (proj1 (to_Z_bounded _)) | exact (proj2 Hkz)].
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma find_all_impl_correct : forall (pat txt : string) (xp xt : PrimString.string),
  valid_input pat txt -> repr xp pat -> repr xt txt ->
  exists ps : list N, positions_repr (find_all_impl xp xt) ps /\ find_all_spec pat txt ps.
Proof.
  intros pat txt xp xt Hv Hp Ht.
  apply (out_ok_correct pat txt xp xt _ Hp Ht).
  destruct Hv as [Hvp Hvt Hvf]. unfold slen in *.
  pose proof (proj1 Hp) as Hlp. pose proof (proj1 Ht) as Hlt.
  unfold find_all_impl. cbv zeta.
  set (m := PrimString.length xp) in *. set (n := PrimString.length xt) in *.
  assert (Hm1 : 1 <= (φ m)) by lia.
  assert (Hn : (φ n) <= 5000000) by lia.
  destruct (n <? m)%uint63 eqn:E.
  - rewrite ltb_spec in E.
    assert (HL0 : (φ (blength (bmake 0))) = 0) by reflexivity.
    split.
    + intros k1 k2 Hk. rewrite HL0 in Hk. lia.
    + intros s. rewrite HL0. split.
      * intros [k [Hk _]]. lia.
      * intros [A [B _]]. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
    assert (Hm : (φ m) <= 2500000) by lia.
    assert (Hlen0 : PArray.length (PArray.make m 0%uint63) = m).
    { rewrite alength_make.
      replace (m <=? PArray.max_length)%uint63 with true; [reflexivity|].
      symmetry. rewrite leb_spec, max_length_val. lia. }
    assert (Htbl1 : tbl_ok (P xp) (F (PArray.make m 0%uint63)) (φ 1)).
    { intros q Hq. change (φ 1) with 1 in Hq.
      replace q with 1 by lia. unfold F. rewrite aget_make. change (φ 0) with 0.
      split.
      - split; [lia|]. intros j Hj. lia.
      - intros k [Hk _]. lia. }
    assert (Hq0 : (φ 0) = F (PArray.make m 0%uint63) (φ 1))
      by (unfold F; rewrite aget_make; reflexivity).
    destruct (build_spec xp m ltac:(lia) _ 1 (PArray.make m 0%uint63) 0
                (Zwf_well_founded 0 (gap m 1)) eq_refl Hlen0
                ltac:(change (φ 1) with 1; lia) Htbl1 Hq0) as [_ Hbok].
    assert (Hbuf : (φ (blength (bmake (n - m + 1)))) = (φ n) - (φ m) + 1).
    { rewrite blength_make; sia. }
    apply (scan_spec xp xt _ m n Hbok ltac:(lia) Hn _ 0 0 0 _ _ eq_refl);
      change (φ 0) with 0.
    + lia.
    + apply S_zero. lia.
    + lia.
    + intros k _ [Hk _]. lia.
    + exact Hbuf.
    + lia.
    + intros k1 k2 Hk. lia.
    + intros s. split.
      * intros [k [Hk _]]. lia.
      * intros [A [B _]]. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition find_all : PrimString.string -> PrimString.string -> buffer :=
  find_all_impl.

Definition find_all_correct :
  forall (pat txt : string) (xp xt : PrimString.string),
  valid_input pat txt -> repr xp pat -> repr xt txt ->
  exists ps : list N, positions_repr (find_all xp xt) ps /\ find_all_spec pat txt ps
  := find_all_impl_correct.

(* Cost proofs for main's KMP implementation. *)
Elpi complexity sumbool.
Elpi complexity bdec.
Elpi complexity fall.
Elpi complexity build.
Elpi complexity buffer.
Elpi complexity alen.
Elpi complexity bget.
Elpi complexity bset.
Elpi complexity bmake.
Elpi complexity copy.
Elpi complexity scan.
Elpi complexity find_all_impl.
Elpi complexity find_all.

From Stdlib Require Import ssreflect.
Arguments Uint63.to_Z : simpl never.
Arguments fall : simpl never.
Arguments build : simpl never.
Arguments copy : simpl never.
Arguments scan : simpl never.
Arguments Zwf_well_founded : simpl never.
Open Scope uint63_scope.
Open Scope nat_scope.

Definition zn (x : int) := Z.to_nat (φ x).

Lemma bdec_time b bC : (cost (bdec_cost stepsCM b bC) <= 2)%nat.
Proof. destruct bC; cbn; lia. Qed.

Ltac bound_bdec :=
  repeat match goal with |- context [@cost ?T (bdec_cost stepsCM ?b ?w)] =>
    let HB := fresh "Hbdec" in
    have HB := (bdec_time b w : (@cost T (bdec_cost stepsCM b w) <= _)%nat);
    let C := fresh "branch_cost" in
    set (C := @cost T (bdec_cost stepsCM b w)) in *; clearbody C end.

Lemma succ_le q : (φ (q + 1) <= φ q + 1)%Z.
Proof. pose proof (to_Z_bounded q). sia. Qed.

Lemma fall_range xp tbl c : forall N q H, (zn q <= N)%nat ->
  (φ (fall xp tbl c q H) <= φ q + 1)%Z.
Proof.
  induction N as [N IH] using lt_wf_ind. intros q H HN. rewrite fall_eq.
  destruct (PrimString.get xp q =? c)%uint63; [apply succ_le|].
  destruct (bdec (0 <? q)%uint63) as [Hq|Hq]; [|change (φ 0) with 0%Z; pose proof (to_Z_bounded q); lia].
  cbv zeta. destruct (bdec (tbl.[q - 1] <? q)%uint63) as [Ht|Ht];
    [|change (φ 0) with 0%Z; pose proof (to_Z_bounded q); lia].
  pose proof (proj1 (Uint63.ltb_spec _ _) Ht) as E.
  pose proof (to_Z_bounded tbl.[q - 1]).
  eapply Z.le_trans; [eapply (IH (zn tbl.[q - 1])); unfold zn in *; lia|]. lia.
Qed.

Lemma fall_time xp xpC tbl tblC c cC q qC H HC :
  (cost (extract (extract (extract (extract (fall_cost stepsCM xp xpC) tbl tblC) c cC) q qC) H HC)
    + 100 * zn (fall xp tbl c q H) <= 100 * zn q + 200)%nat.
Proof.
  unfold fall_cost. cbn.
  match goal with |- context [@cost ?T (?G xp xpC tbl tblC c cC q qC H HC)] =>
    assert (HG : forall N q qC H HC, (zn q <= N)%nat ->
      (cost (G xp xpC tbl tblC c cC q qC H HC) + 100 * zn (fall xp tbl c q H)
        <= 100 * zn q + 200)%nat) end.
  { intros N. induction N as [N IH] using lt_wf_ind. intros q' qC' [g] HC' HN.
    remember (zn (fall xp tbl c q' (Acc_intro _ g))) as potential eqn:Ep.
    rewrite fall_eq in Ep. cost_simpl; bound_bdec.
    lazymatch goal with |- context [if ?b then _ else _] => destruct b eqn:E end; cost_simpl.
    - pose proof (succ_le q'). unfold zn in *. pose proof (to_Z_bounded q'). lia.
    - cost_destruct (bdec (0 <? q')%uint63); cost_simpl; bound_bdec.
      + cbv zeta in Ep. cost_destruct (bdec (tbl.[q' - 1] <? q')%uint63); cost_simpl.
        * pose proof (proj1 (Uint63.ltb_spec _ _) e0) as Hlt.
          match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?d ?dc ?r ?rc ?h ?hc)] =>
            have HI := (IH (zn r) ltac:(unfold zn in *; pose proof (to_Z_bounded r); lia)
              r rc h hc (le_n _) : (@cost T (G' a ac b bc d dc r rc h hc) + 100 * zn (fall a b d r h) <= _)%nat)
          end.
          cbn [Acc_inv] in Ep. rewrite <- Ep in HI.
          unfold zn in *. pose proof (to_Z_bounded tbl.[q' - 1]). lia.
        * change (potential = 0%nat) in Ep. lia.
      + change (potential = 0%nat) in Ep. lia. }
  match goal with |- context [@cost ?T (?G xp xpC tbl tblC c cC q qC H HC)] =>
    exact (HG (zn q) q qC H HC (le_n _)
      : (@cost T (G xp xpC tbl tblC c cC q qC H HC) + 100 * zn (fall xp tbl c q H) <= _)%nat) end.
Qed.

Ltac cost_head f c := lazymatch c with
  | extract ?g _ _ => cost_head f g
  | f stepsCM _ _ => idtac end.
Ltac zero_partial f := repeat match goal with |- context [@cost ?T ?c] =>
  cost_head f c; change (@cost T c) with 0%nat end.
Arguments fall_cost : simpl never.

Ltac gen_fall :=
  try match goal with |- context [@cost ?T (?G ?a ?ac ?b ?bc ?c ?cc ?d ?dc ?h ?hc)] =>
    change (@cost T (G a ac b bc c cc d dc h hc)) with
      (cost (extract (extract (extract (extract (fall_cost stepsCM a ac) b bc) c cc) d dc) h hc)) end;
  zero_partial fall_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (fall_cost stepsCM ?a ?ac) ?b ?bc) ?c ?cc) ?d ?dc) ?h ?hc =>
      let HI := fresh "Hfall" in
      have HI := (fall_time a ac b bc c cc d dc h hc : (@cost T X + 100 * zn (fall a b c d h) <= _)%nat);
      let C := fresh "fallback_cost" in set (C := @cost T X) in *; clearbody C end end.

Ltac set_simpl := repeat match goal with
  | |- context [cost (extract (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g) ?h ?i)] =>
    change (cost (extract (extract (extract (set_cost a b c) d e) f g) h i)) with 1%nat
  | |- context [cost (extract (extract (set_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
    change (cost (extract (extract (set_cost a b c) d e) f g)) with 0%nat
  | |- context [cost (extract (set_cost ?a ?b ?c) ?d ?e)] =>
    change (cost (extract (set_cost a b c) d e)) with 0%nat
  | |- context [cost (set_cost ?a ?b ?c)] =>
    change (cost (set_cost a b c)) with 0%nat end.

Lemma bget_time t tC i iC :
  (cost (extract (bget_cost stepsCM t tC) i iC) <= 20)%nat.
Proof.
  destruct t as [a b]. destruct tC as [aC bC].
  unfold bget_cost, alen_cost. cost_simpl.
  repeat match goal with |- context [if ?c then _ else _] =>
    rewrite cost_if; destruct c; cost_simpl end; lia.
Qed.

Lemma bset_time t tC i iC v vC :
  (cost (extract (extract (bset_cost stepsCM t tC) i iC) v vC) <= 32)%nat.
Proof.
  destruct t as [a b]. destruct tC as [aC bC].
  unfold bset_cost, alen_cost. cost_simpl.
  repeat match goal with |- context [if ?c then _ else _] =>
    rewrite cost_if; destruct c; cost_simpl; set_simpl end; lia.
Qed.

Lemma bmake_time n nC : (cost (bmake_cost stepsCM n nC) <= 64)%nat.
Proof.
  unfold bmake_cost. cost_simpl. rewrite cost_if.
  destruct (4194303 <? n)%uint63; cost_simpl; zero_partial make_cost;
    repeat match goal with |- context [@cost ?T ?X] =>
      cost_head make_cost X; change (@cost T X) with 1%nat end; lia.
Qed.

Arguments bget_cost : simpl never.
Arguments bset_cost : simpl never.
Arguments bmake_cost : simpl never.

Ltac bound_buffer :=
  zero_partial bget_cost; zero_partial bset_cost;
  repeat match goal with
  | |- context [cost (extract (bget_cost stepsCM ?t ?tc) ?i ?ic)] =>
    let H := fresh "Hget" in pose proof (bget_time t tc i ic) as H;
    let C := fresh "get_cost_bound" in
    set (C := cost (extract (bget_cost stepsCM t tc) i ic)) in *; clearbody C
  | |- context [cost (extract (extract (bset_cost stepsCM ?t ?tc) ?i ?ic) ?v ?vc)] =>
    let H := fresh "Hset" in pose proof (bset_time t tc i ic v vc) as H;
    let C := fresh "set_cost_bound" in
    set (C := cost (extract (extract (bset_cost stepsCM t tc) i ic) v vc)) in *; clearbody C
  | |- context [cost (bmake_cost stepsCM ?n ?nc)] =>
    let H := fresh "Hmake" in pose proof (bmake_time n nc) as H;
    let C := fresh "make_cost_bound" in
    set (C := cost (bmake_cost stepsCM n nc)) in *; clearbody C
  end.

Lemma build_time xp xpC m mC tbl tblC i iC q qC H HC :
  (cost (extract (extract (extract (extract (extract (build_cost stepsCM xp xpC) m mC) tbl tblC) i iC) q qC) H HC)
    <= 400 * Z.to_nat (gap m i) + 100 * zn q + 50)%nat.
Proof.
  unfold build_cost. cbn -[fall_cost].
  match goal with |- context [@cost ?T (?G xp xpC m mC tbl tblC i iC q qC H HC)] =>
    assert (HG : forall N tbl tblC i iC q qC H HC, (Z.to_nat (gap m i) <= N)%nat ->
      (cost (G xp xpC m mC tbl tblC i iC q qC H HC) <= 400*N+100*zn q+50)%nat) end.
  { induction N as [|N IH]; intros tbl' tblC' i' iC' q' qC' [g] HC' HN;
      match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end;
      cost_simpl; bound_bdec; cost_destruct (bdec (i' <? m)%uint63); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in HN. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hi.
      assert (Ei : φ (i'+1) = (φ i'+1)%Z) by sia.
      gen_fall. set_simpl.
      match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?t ?tc ?ii ?ic ?r ?rc ?h ?hc)] =>
        have HI := (IH t tc ii ic r rc h hc ltac:(unfold gap in *; rewrite Ei; lia)
          : (@cost T (G' a ac b bc t tc ii ic r rc h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G xp xpC m mC tbl tblC i iC q qC H HC)] =>
    exact (HG _ tbl tblC i iC q qC H HC (le_n _)
      : (@cost T (G xp xpC m mC tbl tblC i iC q qC H HC) <= _)%nat) end.
Qed.

Lemma set_bounded (tbl : array int) i v m :
  (forall k, (φ (@PArray.get@{Set} int tbl k) <= φ m)%Z) -> (φ v <= φ m)%Z ->
  forall k, (φ (@PArray.get@{Set} int (@PArray.set@{Set} int tbl i v) k) <= φ m)%Z.
Proof.
  intros Hb Hv k. destruct (Uint63.eqb i k) eqn:E.
  - apply Uint63.eqb_spec in E. subst k. destruct (i <? @PArray.length@{Set} int tbl)%uint63 eqn:Hi.
    + rewrite (@get_set_same@{Set} int tbl i v Hi). exact Hv.
    + rewrite (@get_out_of_bounds@{Set} int (@PArray.set@{Set} int tbl i v) i
        ltac:(rewrite (@length_set@{Set} int tbl i v); exact Hi)).
      rewrite (@default_set@{Set} int tbl i v).
      rewrite <- (@get_out_of_bounds@{Set} int tbl i Hi). apply Hb.
  - rewrite (@get_set_other@{Set} int tbl i k v ltac:(intro He; subst k; rewrite Uint63.eqb_refl in E; discriminate)). apply Hb.
Qed.

Lemma build_table xp m : forall N tbl i q H, (Z.to_nat (gap m i) <= N)%nat ->
  (φ q <= φ i)%Z -> (forall k, (φ (@PArray.get@{Set} int tbl k) <= φ m)%Z) ->
  forall k, (φ (@PArray.get@{Set} int (build xp m tbl i q H) k) <= φ m)%Z.
Proof.
  induction N as [|N IH]; intros tbl i q H HN Hq Hb k; rewrite build_eq;
    destruct (bdec (i <? m)%uint63) as [Hi|Hi]; [|apply Hb| |apply Hb].
  - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) Hi). unfold gap in HN. lia.
  - cbv zeta. pose proof (proj1 (Uint63.ltb_spec _ _) Hi) as Hil.
    assert (Ei : φ (i+1) = (φ i+1)%Z) by sia.
    pose proof (fall_range xp tbl (PrimString.get xp i) (zn q) q
      (Zwf_well_founded 0 (φ q)) (le_n _)) as Hr.
    apply IH; [unfold gap in *; rewrite Ei; lia|lia|].
    apply set_bounded; [exact Hb|lia].
Qed.

Lemma copy_time buf bufC res resC c cC k kC H HC :
  (cost (extract (extract (extract (extract (copy_cost stepsCM buf bufC) res resC) c cC) k kC) H HC)
    <= 100 * Z.to_nat (gap c k) + 20)%nat.
Proof.
  unfold copy_cost. cbn -[bget_cost bset_cost].
  match goal with |- context [@cost ?T (?G buf bufC res resC c cC k kC H HC)] =>
    assert (HG : forall N res resC k kC H HC, (Z.to_nat (gap c k) <= N)%nat ->
      (cost (G buf bufC res resC c cC k kC H HC) <= 100*N+20)%nat) end.
  { induction N as [|N IH]; intros res' resC' k' kC' [g] HC' HN;
      match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end;
      cost_simpl; bound_bdec; cost_destruct (bdec (k' <? c)%uint63); cost_simpl; set_simpl; bound_buffer.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in HN. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Ek : φ (k'+1) = (φ k'+1)%Z) by sia.
      match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?d ?dc ?j ?jc ?h ?hc)] =>
        have HI := (IH b bc j jc h hc ltac:(unfold gap in *; rewrite Ek; lia)
          : (@cost T (G' a ac b bc d dc j jc h hc) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G buf bufC res resC c cC k kC H HC)] =>
    exact (HG _ res resC k kC H HC (le_n _)
      : (@cost T (G buf bufC res resC c cC k kC H HC) <= _)%nat) end.
Qed.

Arguments copy_cost : simpl never.
Ltac gen_copy :=
  try match goal with |- context [@cost ?T (?G ?a ?ac ?b ?bc ?c ?cc ?d ?dc ?h ?hc)] =>
    change (@cost T (G a ac b bc c cc d dc h hc)) with
      (cost (extract (extract (extract (extract (copy_cost stepsCM a ac) b bc) c cc) d dc) h hc)) end;
  zero_partial copy_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (copy_cost stepsCM ?a ?ac) ?b ?bc) ?c ?cc) ?d ?dc) ?h ?hc =>
      let HI := fresh "Hcopy" in
      have HI := (copy_time a ac b bc c cc d dc h hc : (@cost T X <= _)%nat);
      let C := fresh "copy_cost_bound" in set (C := @cost T X) in *; clearbody C end end.
Ltac make_simpl :=
  zero_partial make_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
    cost_head make_cost X; change (@cost T X) with 1%nat end.

Lemma scan_time xp xpC xt xtC tbl tblC m mC n nC buf bufC i iC q qC cnt cntC H HC :
  (forall k, (φ (@PArray.get@{Set} int tbl k) <= φ m)%Z) ->
  (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract
    (scan_cost stepsCM xp xpC) xt xtC) tbl tblC) m mC) n nC) buf bufC) i iC) q qC) cnt cntC) H HC)
    <= 600 * Z.to_nat (gap n i) + 100 * zn q + 100 * zn cnt + 100)%nat.
Proof.
  intro Htbl. unfold scan_cost. cbn -[fall_cost copy_cost bset_cost bmake_cost].
  match goal with |- context [@cost ?T (?G xp xpC xt xtC tbl tblC m mC n nC buf bufC i iC q qC cnt cntC H HC)] =>
    assert (HG : forall N buf bufC i iC q qC cnt cntC H HC, (Z.to_nat (gap n i) <= N)%nat ->
      (cost (G xp xpC xt xtC tbl tblC m mC n nC buf bufC i iC q qC cnt cntC H HC)
        <= 600*N+100*zn q+100*zn cnt+100)%nat) end.
  { induction N as [|N IH]; intros buf' bufC' i' iC' q' qC' cnt' cntC' [g] HC' HN;
      match goal with |- (_ <= ?rhs)%nat => remember rhs as budget eqn:Hbudget end;
      cost_simpl; bound_bdec; cost_destruct (bdec (i' <? n)%uint63); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in HN. lia.
    - gen_copy. make_simpl. bound_buffer.
      repeat match goal with HH : context [Z.to_nat (gap ?x 0)] |- _ =>
        unfold gap in HH; change (φ 0) with 0%Z in HH; rewrite Z.sub_0_r in HH end.
      unfold zn in *. lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hi.
      assert (Ei : φ (i'+1) = (φ i'+1)%Z) by sia.
      gen_fall. rewrite cost_if.
      lazymatch goal with |- context [if ?b then _ else _] => destruct b eqn:Er end;
        cost_simpl; bound_bdec; set_simpl; bound_buffer.
      + match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?t ?tc ?mm ?mc ?nn ?nc ?bb ?bbc ?ii ?ic ?r ?rc ?cc ?ccc ?h ?hc)] =>
          have HI := (IH bb bbc ii ic r rc cc ccc h hc ltac:(unfold gap in *; rewrite Ei; lia)
            : (@cost T (G' a ac b bc t tc mm mc nn nc bb bbc ii ic r rc cc ccc h hc) <= _)%nat) end.
        pose proof (succ_le cnt'). pose proof (Htbl (m-1)%uint63).
        apply Uint63.eqb_spec in Er. rewrite Er in Hfall.
        assert (Hr : (zn (@PArray.get@{Set} int tbl (m-1)) <= zn m)%nat).
        { unfold zn. apply Z2Nat.inj_le; pose proof (to_Z_bounded (@PArray.get@{Set} int tbl (m-1))); lia. }
        assert (Hcnt : (zn (cnt'+1) <= zn cnt'+1)%nat).
        { unfold zn. pose proof (to_Z_bounded cnt'). pose proof (to_Z_bounded (cnt'+1)%uint63). lia. }
        match type of HI with (?X <= _)%nat =>
          let C := fresh "recursive_cost" in set (C := X) in *; clearbody C end.
        lia.
      + match goal with |- context [@cost ?T (?G' ?a ?ac ?b ?bc ?t ?tc ?mm ?mc ?nn ?nc ?bb ?bbc ?ii ?ic ?r ?rc ?cc ?ccc ?h ?hc)] =>
          have HI := (IH bb bbc ii ic r rc cc ccc h hc ltac:(unfold gap in *; rewrite Ei; lia)
            : (@cost T (G' a ac b bc t tc mm mc nn nc bb bbc ii ic r rc cc ccc h hc) <= _)%nat) end.
        lia.
    - gen_copy. make_simpl. bound_buffer.
      repeat match goal with HH : context [Z.to_nat (gap ?x 0)] |- _ =>
        unfold gap in HH; change (φ 0) with 0%Z in HH; rewrite Z.sub_0_r in HH end.
      unfold zn in *. lia. }
  match goal with |- context [@cost ?T (?G xp xpC xt xtC tbl tblC m mC n nC buf bufC i iC q qC cnt cntC H HC)] =>
    exact (HG _ buf bufC i iC q qC cnt cntC H HC (le_n _)
      : (@cost T (G xp xpC xt xtC tbl tblC m mC n nC buf bufC i iC q qC cnt cntC H HC) <= _)%nat) end.
Qed.

Lemma built_table xp m : forall k,
  (φ (@PArray.get@{Set} int
    (build xp m (@PArray.make@{Set} int m 0%uint63) 1%uint63 0%uint63
      (Zwf_well_founded 0 (gap m 1%uint63))) k) <= φ m)%Z.
Proof.
  apply (build_table xp m _ _ _ _ _ (le_n _)).
  - change (0 <= 1)%Z. lia.
  - intro k. rewrite (@get_make@{Set} int 0%uint63 m k).
    change (φ 0) with 0%Z. pose proof (to_Z_bounded m). lia.
Qed.

Arguments build_cost : simpl never.
Arguments scan_cost : simpl never.
Ltac gen_build :=
  try match goal with |- context [@cost ?T (?G ?a ?ac ?b ?bc ?c ?cc ?d ?dc ?e ?ec ?h ?hc)] =>
    change (@cost T (G a ac b bc c cc d dc e ec h hc)) with
      (cost (extract (extract (extract (extract (extract (build_cost stepsCM a ac) b bc) c cc) d dc) e ec) h hc)) end;
  zero_partial build_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (build_cost stepsCM ?a ?ac) ?b ?bc) ?c ?cc) ?d ?dc) ?e ?ec) ?h ?hc =>
      let HI := fresh "Hbuild" in
      have HI := (build_time a ac b bc c cc d dc e ec h hc : (@cost T X <= _)%nat);
      let C := fresh "build_cost_bound" in set (C := @cost T X) in *; clearbody C end end.

Ltac gen_scan :=
  try match goal with |- context [@cost ?T (?G ?a ?ac ?b ?bc ?c ?cc ?d ?dc ?e ?ec ?f ?fc ?g ?gc ?h ?hc ?i ?ic ?j ?jc)] =>
    change (@cost T (G a ac b bc c cc d dc e ec f fc g gc h hc i ic j jc)) with
      (cost (extract (extract (extract (extract (extract (extract (extract (extract (extract
        (scan_cost stepsCM a ac) b bc) c cc) d dc) e ec) f fc) g gc) h hc) i ic) j jc)) end;
  zero_partial scan_cost;
  repeat match goal with |- context [@cost ?T ?X] =>
    lazymatch X with extract (extract (extract (extract (extract (extract (extract (extract (extract
      (scan_cost stepsCM ?a ?ac) ?b ?bc) ?c ?cc) ?d ?dc) ?e ?ec) ?f ?fc) ?g ?gc) ?h ?hc) ?i ?ic) ?j ?jc =>
      let HI := fresh "Hscan" in
      have HI := (scan_time a ac b bc c cc d dc e ec f fc g gc h hc i ic j jc ltac:(apply built_table)
        : (@cost T X <= _)%nat);
      let C := fresh "scan_cost_bound" in set (C := @cost T X) in *; clearbody C end end.

Lemma find_all_time : exists c1 c2, forall pattern_str text_str,
  (cost2 find_all_cost pattern_str text_str <=
    c1 * (Cost.size pattern_str + Cost.size text_str + 1) + c2)%nat.
Proof.
  exists 2000%nat, 2000%nat. intros xp xt.
  unfold cost2, find_all_cost, find_all_impl_cost. cost_simpl.
  rewrite cost_if. destruct (PrimString.length xt <? PrimString.length xp)%uint63.
  - cbn -[make_cost bmake_cost]. make_simpl. bound_buffer. lia.
  - cost_simpl. gen_build. gen_scan. make_simpl. bound_buffer.
    change (Cost.size xp) with (zn (PrimString.length xp)).
    change (Cost.size xt) with (zn (PrimString.length xt)).
    unfold gap in Hbuild, Hscan. change (φ 1) with 1%Z in Hbuild.
    change (φ 0) with 0%Z in Hscan.
    change (zn 0) with 0%nat in Hbuild, Hscan.
    unfold zn in *. pose proof (to_Z_bounded (PrimString.length xp)).
    pose proof (to_Z_bounded (PrimString.length xt)). lia.
Qed.

Print Assumptions find_all_correct.
Print Assumptions find_all_time.
