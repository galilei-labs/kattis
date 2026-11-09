(* Correctness proofs for stringmatching_implem.v. *)
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
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf String Ascii.
From Stdlib Require PrimString.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Stringmatching Require Export stringmatching_implem.
Open Scope uint63_scope.
Open Scope array_scope.


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

Lemma build_eq : forall xp m tbl i q H,
  build xp m tbl i q H =
  match bdec (i <? m) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xp i) q (Zwf_well_founded 0 (φ q)) in
      build xp m tbl.[i <- r] (i + 1) r (Acc_inv H (dec_step m i Hi))
  | right _ => tbl
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma copy_eq : forall buf res c k H,
  copy buf res c k H =
  match bdec (k <? c) with
  | left Hk => copy buf res.[k <- buf.[k]] c (k + 1) (Acc_inv H (dec_step c k Hk))
  | right _ => res
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_eq : forall xp xt tbl m n buf i q cnt H,
  scan xp xt tbl m n buf i q cnt H =
  match bdec (i <? n) with
  | left Hi =>
      let r := fall xp tbl (PrimString.get xt i) q (Zwf_well_founded 0 (φ q)) in
      if r =? m then
        scan xp xt tbl m n buf.[cnt <- i + 1 - m] (i + 1) tbl.[m - 1] (cnt + 1)
          (Acc_inv H (dec_step n i Hi))
      else
        scan xp xt tbl m n buf (i + 1) r cnt (Acc_inv H (dec_step n i Hi))
  | right _ => copy buf (PArray.make cnt 0) cnt 0 (Zwf_well_founded 0 (gap cnt 0))
  end.
Proof. intros. destruct H. reflexivity. Qed.

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
Lemma copy_spec : forall (buf : array int) (c : int),
  forall (z : Z) (k : int) (res : array int) (H : Acc (Zwf 0) (gap c k)),
  gap c k = z -> PArray.length res = c -> (φ k) <= (φ c) ->
  (forall k' : int, (φ k') < (φ k) -> res.[k'] = buf.[k']) ->
  PArray.length (copy buf res c k H) = c /\
  forall k' : int, (φ k') < (φ c) -> (copy buf res c k H).[k'] = buf.[k'].
Proof.
  intros buf c z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k res H Hz Hlen Hkc Hc.
  rewrite copy_eq.
  destruct (bdec (k <? c)%uint63) as [Hlt | Hlt].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hk1 : (φ (k + 1))%uint63 = (φ k) + 1) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity
               | rewrite alength_set; exact Hlen | lia | ].
    intros k' Hk'. rewrite Hk1 in Hk'.
    destruct (Z.eq_dec (φ k') (φ k)) as [E | E].
    + apply to_Z_inj in E. subst k'.
      apply aget_set_same. rewrite Hlen. exact Hlt.
    + rewrite aget_set_other by (intro F'; apply E; rewrite F'; reflexivity).
      apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hlt.
    split; [exact Hlen|]. intros k' Hk'. apply Hc. lia.
Qed.

(* pat occurs in txt at s, on the symbol maps *)
Definition occ (xp xt : PrimString.string) (m s : Z) : Prop :=
  forall j, 0 <= j < m -> P xp j = P xt (s + j).

(* res lists, strictly ascending, exactly the occurrences *)
Definition out_ok (xp xt : PrimString.string) (m n : Z) (res : array int) : Prop :=
  (forall k1 k2, 0 <= k1 < k2 /\ k2 < (φ (PArray.length res)) ->
     (φ (res.[of_Z k1])) < (φ (res.[of_Z k2]))) /\
  (forall s, (exists k, 0 <= k < (φ (PArray.length res)) /\ (φ (res.[of_Z k])) = s) <->
             (0 <= s /\ s + m <= n /\ occ xp xt m s)).

Lemma get_set_Z : forall (t : array int) (c v : int) (k : Z),
  0 <= k <= (φ c) -> (c <? PArray.length t)%uint63 = true ->
  (φ (t.[c <- v].[of_Z k])) = if Z.eq_dec k (φ c) then (φ v) else (φ (t.[of_Z k])).
Proof.
  intros t c v k Hk Hc. pose proof (to_Z_bounded c) as Bc.
  destruct (Z.eq_dec k (φ c)) as [E | E].
  - subst k. rewrite of_to_Z, aget_set_same by exact Hc. reflexivity.
  - rewrite aget_set_other; [reflexivity|]. intro E'. apply E.
    rewrite E', of_Z_spec, Z.mod_small; [reflexivity | lia].
Qed.

Lemma of_Z_to_Z : forall k, 0 <= k < wB -> (φ (of_Z k)) = k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. exact Hk. Qed.

(* The text scan. *)
Lemma scan_spec : forall xp xt (tbl : array int) (m n : int),
  tbl_ok (P xp) (F tbl) (φ m) -> 1 <= (φ m) <= (φ n) -> (φ n) <= 4194303 ->
  forall (z : Z) (i q cnt : int) (buf : array int) (H : Acc (Zwf 0) (gap n i)),
  gap n i = z -> (φ i) <= (φ n) ->
  S (P xp) (P xt) (φ i) (φ q) -> (φ q) < (φ m) ->
  (forall k, k < (φ m) -> S (P xp) (P xt) (φ i) k -> k <= (φ q)) ->
  (φ (PArray.length buf)) = (φ n) - (φ m) + 1 ->
  (φ cnt) <= Z.max 0 ((φ i) - (φ m) + 1) ->
  (forall k1 k2, 0 <= k1 < k2 /\ k2 < (φ cnt) ->
     (φ (buf.[of_Z k1])) < (φ (buf.[of_Z k2]))) ->
  (forall s, (exists k, 0 <= k < (φ cnt) /\ (φ (buf.[of_Z k])) = s) <->
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
      assert (Hcb : (cnt <? PArray.length buf)%uint63 = true) by (rewrite ltb_spec; lia).
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
      * rewrite alength_set. exact Hbl.
      * lia.
      * intros k1 k2 Hk. rewrite !get_set_Z by (auto; lia).
        destruct (Z.eq_dec k2 (φ cnt)), (Z.eq_dec k1 (φ cnt)); try lia.
        -- rewrite Hs.
           assert (Hk1 : 0 <= k1 < (φ cnt)) by lia.
           destruct (proj1 (Hset (φ (buf.[of_Z k1])))
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
    assert (Hcn : (φ cnt) <= 4194303) by lia.
    assert (Hml : PArray.length (PArray.make cnt 0%uint63) = cnt).
    { rewrite alength_make.
      replace (cnt <=? PArray.max_length)%uint63 with true; [reflexivity|].
      symmetry. rewrite leb_spec, max_length_val. lia. }
    destruct (copy_spec buf cnt _ 0 (PArray.make cnt 0%uint63) (Zwf_well_founded 0 (gap cnt 0))
                eq_refl Hml ltac:(change (φ 0) with 0; lia)
                ltac:(intros k' Hk'; change (φ 0) with 0 in Hk';
                      pose proof (to_Z_bounded k'); lia)) as [Hrl Hrc].
    set (res := copy buf (PArray.make cnt 0%uint63) cnt 0 (Zwf_well_founded 0 (gap cnt 0))) in *.
    assert (Hcell : forall k, 0 <= k < (φ cnt) -> res.[of_Z k] = buf.[of_Z k]).
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

(* From the machine output to the math output. *)
Lemma out_ok_correct : forall pat txt xp xt (res : array uint),
  repr xp pat -> repr xt txt ->
  out_ok xp xt (φ (PrimString.length xp)) (φ (PrimString.length xt)) res ->
  exists ps : list N, repr res ps /\ find_all_spec pat txt ps.
Proof.
  intros pat txt xp xt res Hp Ht [Hasc Hset].
  set (L := Z.to_nat (φ (PArray.length res))).
  set (f := fun k : nat => Z.to_N (φ (res.[of_Z (Z.of_nat k)]))).
  exists (map f (seq 0 L)).
  pose proof (to_Z_bounded (PArray.length res)) as BL.
  assert (Hlen : List.length (map f (seq 0 L)) = L) by (rewrite length_map, length_seq; reflexivity).
  assert (Hnth : forall k, (k < L)%nat -> nth_error (map f (seq 0 L)) k = Some (f k)).
  { intros k Hk. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec k L); [reflexivity | lia]. }
  split; [split|split].
  - rewrite Hlen. unfold L. lia.
  - intros k Hk. rewrite Hlen in Hk. exists (f k). split; [apply Hnth; exact Hk|].
    reflexivity.
  - intros t u Htu. unfold len in Htu. rewrite Hlen in Htu.
    unfold get_list_N.
    rewrite (nth_error_nth _ _ _ (Hnth (N.to_nat t) ltac:(lia))).
    rewrite (nth_error_nth _ _ _ (Hnth (N.to_nat u) ltac:(lia))).
    unfold f.
    assert (Hk : 0 <= Z.of_nat (N.to_nat t) < Z.of_nat (N.to_nat u) /\
                 Z.of_nat (N.to_nat u) < (φ (PArray.length res))) by (unfold L in *; lia).
    pose proof (Hasc _ _ Hk) as Hlt.
    apply Z2N.inj_lt; [apply (proj1 (to_Z_bounded _)) | apply (proj1 (to_Z_bounded _)) | exact Hlt].
  - intros i. rewrite (occurs_iff_occ pat txt xp xt Hp Ht i).
    rewrite in_map_iff. split.
    + intros [k [Hfk Hk]]. rewrite in_seq in Hk.
      assert (Hs : exists kz, 0 <= kz < (φ (PArray.length res)) /\
                   (φ (res.[of_Z kz])) = Z.of_N i).
      { exists (Z.of_nat k). split; [unfold L in *; lia|].
        rewrite <- Hfk. unfold f.
        pose proof (to_Z_bounded (res.[of_Z (Z.of_nat k)])). lia. }
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
  exists ps : list N, repr (find_all_impl xp xt) ps /\ find_all_spec pat txt ps.
Proof.
  intros pat txt xp xt Hv Hp Ht.
  apply (out_ok_correct pat txt xp xt _ Hp Ht).
  destruct Hv as [Hvp Hvt Hvf Hvpa]. unfold slen in *.
  pose proof (proj1 Hp) as Hlp. pose proof (proj1 Ht) as Hlt.
  unfold find_all_impl. cbv zeta.
  set (m := PrimString.length xp) in *. set (n := PrimString.length xt) in *.
  assert (Hm1 : 1 <= (φ m)) by lia.
  assert (Hn : (φ n) <= 4194303) by lia.
  destruct (n <? m)%uint63 eqn:E.
  - rewrite ltb_spec in E.
    assert (HL0 : (φ (PArray.length (PArray.make 0 0%uint63))) = 0) by reflexivity.
    split.
    + intros k1 k2 Hk. rewrite HL0 in Hk. lia.
    + intros s. rewrite HL0. split.
      * intros [k [Hk _]]. lia.
      * intros [A [B _]]. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
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
    assert (Hbuf : (φ (PArray.length (PArray.make (n - m + 1) 0%uint63))) = (φ n) - (φ m) + 1).
    { rewrite alength_make.
      replace (n - m + 1 <=? PArray.max_length)%uint63 with true; [sia|].
      symmetry. rewrite leb_spec, max_length_val. sia. }
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

Definition find_all_correct :
  forall (pat txt : string) (xp xt : PrimString.string),
  valid_input pat txt -> repr xp pat -> repr xt txt ->
  exists ps : list N, repr (find_all xp xt) ps /\ find_all_spec pat txt ps
  := find_all_impl_correct.
