(* Implementation of polymul1 (polymul1.spec): the schoolbook product,
   the double loop over the index pairs (i, j) of the two operands.

   Code.  [polymul x y] allocates the result [PArray.make L 0] with
   L = |x| + |y| - 1, then for i = 0 .. |x|-1 and j = 0 .. |y|-1 adds
   x.[i] * y.[j] into cell i + j (read the cell, set it: the result is
   threaded linearly, x and y are only read).  Every product and sum is a
   wrapping 63-bit operation: each cell holds its true coefficient modulo
   2^63, and since [valid_input] bounds every coefficient of the product
   to a signed 32-bit integer, the signed reading of the cell is the
   exact coefficient.  No Z, no list, no nat in the code.

   Termination: both loops recurse structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof (the template's device).

   Proof.  The loops are proven against the coefficient function
   [rows a b I k = sum_{i < I} a_i * b_{k-i}] (inner loop: row I done up
   to column J); the final cells are [conv a b k = rows a b |a| k].  The
   math product [pmul] (sum of shifted scaled copies of b) evaluates to
   eval a x * eval b x and has conv a b k as its k-th coefficient, so it
   is the witness of the existential.

   Cost.  [Elpi complexity] translates sumbool, bdec, row_loop, rows_loop,
   polymul_impl and polymul (callee first).  row_loop from j costs at most
   50 * (lb - j) + 10 steps (row_loop_time); rows_loop from i at most
   (50 * lb + 100) * (la - i) + 10 (rows_loop_time); polymul at most
   150 * ((p + 1) * (q + 1)) + 100 (polymul_time). *)

From Polymul1.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63.
From KattisLib Require Import Cost.
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

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Lemma aget_make : forall (n : int) (b : int) (i : int),
  (PArray.make n b).[i] = b.
Proof. intros n b i. exact (get_make int b n i). Qed.

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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Row i: for j, j+1, ..., lb-1, cell i + j of r receives ai * y.[j]. *)
Fixpoint row_loop (y : array int) (ai i lb j : int) (r : array int)
    (H : Acc (Zwf 0) (gap lb j)) {struct H} : array int :=
  match bdec (j <? lb) with
  | left Hj =>
      let k := i + j in
      row_loop y ai i lb (j + 1) r.[k <- r.[k] + ai * y.[j]]
        (Acc_inv H (dec_step lb j Hj))
  | right _ => r
  end.
Elpi complexity row_loop.
Arguments row_loop_cost : simpl never.

Lemma row_loop_eq : forall y ai i lb j r H,
  row_loop y ai i lb j r H =
  match bdec (j <? lb) with
  | left Hj =>
      let k := i + j in
      row_loop y ai i lb (j + 1) r.[k <- r.[k] + ai * y.[j]]
        (Acc_inv H (dec_step lb j Hj))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* Rows i, i+1, ..., la-1. *)
Fixpoint rows_loop (x y : array int) (la lb i : int) (r : array int)
    (H : Acc (Zwf 0) (gap la i)) {struct H} : array int :=
  match bdec (i <? la) with
  | left Hi =>
      rows_loop x y la lb (i + 1)
        (row_loop y x.[i] i lb 0 r (Zwf_well_founded 0 (gap lb 0)))
        (Acc_inv H (dec_step la i Hi))
  | right _ => r
  end.
Elpi complexity rows_loop.
Arguments rows_loop_cost : simpl never.

Lemma rows_loop_eq : forall x y la lb i r H,
  rows_loop x y la lb i r H =
  match bdec (i <? la) with
  | left Hi =>
      rows_loop x y la lb (i + 1)
        (row_loop y x.[i] i lb 0 r (Zwf_well_founded 0 (gap lb 0)))
        (Acc_inv H (dec_step la i Hi))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition polymul_impl (x y : array sint) : array sint :=
  let la := PArray.length x in
  let lb := PArray.length y in
  if la =? 0 then PArray.make 0 0
  else if lb =? 0 then PArray.make 0 0
  else
    rows_loop x y la lb 0 (PArray.make (la + lb - 1) 0)
      (Zwf_well_founded 0 (gap la 0)).
Elpi complexity polymul_impl.
Arguments polymul_impl_cost : simpl never.

(* ------------------------------------------------------------------ *)
(* Math side: the coefficient functions                                *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

Fixpoint sumn (f : nat -> Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n' => sumn f n' + f n'
  end.

Lemma sumn_ext : forall f g n, (forall i, (i < n)%nat -> f i = g i) ->
  sumn f n = sumn g n.
Proof.
  intros f g n. induction n as [| n IH]; intros E; simpl; [reflexivity|].
  rewrite IH by (intros; apply E; lia). rewrite E by lia. reflexivity.
Qed.

Lemma sumn_shift : forall f n, sumn f (S n) = f O + sumn (fun i => f (S i)) n.
Proof.
  intros f n. induction n as [| n IH]; [simpl; lia|].
  change (sumn f (S (S n))) with (sumn f (S n) + f (S n)).
  rewrite IH. simpl. lia.
Qed.

Lemma sumn_zero : forall f n, (forall i, (i < n)%nat -> f i = 0) -> sumn f n = 0.
Proof.
  intros f n E. rewrite (sumn_ext f (fun _ => 0)) by exact E.
  clear E. induction n; simpl; lia.
Qed.

(* the coefficient of index t, 0 outside the list *)
Definition cz (l : list Z) (t : Z) : Z :=
  if t <? 0 then 0 else nth (Z.to_nat t) l 0.

Lemma cz_neg : forall l t, t < 0 -> cz l t = 0.
Proof. intros l t H. unfold cz. destruct (Z.ltb_spec t 0); [reflexivity | lia]. Qed.

Lemma cz_beyond : forall l t, Z.of_nat (List.length l) <= t -> cz l t = 0.
Proof.
  intros l t H. unfold cz. destruct (Z.ltb_spec t 0); [reflexivity|].
  apply nth_overflow. lia.
Qed.

Lemma cz_cons_succ : forall c l (i : nat),
  cz (c :: l) (Z.of_nat (S i)) = cz l (Z.of_nat i).
Proof.
  intros c l i. unfold cz.
  destruct (Z.ltb_spec (Z.of_nat (S i)) 0); [lia|].
  destruct (Z.ltb_spec (Z.of_nat i) 0); [lia|].
  rewrite !Nat2Z.id. reflexivity.
Qed.

(* sum_{i < I} a_i * b_{k - i} *)
Definition rows (a b : list Z) (I k : Z) : Z :=
  sumn (fun i => cz a (Z.of_nat i) * cz b (k - Z.of_nat i)) (Z.to_nat I).

Lemma rows_succ : forall a b I k, 0 <= I ->
  rows a b (I + 1) k = rows a b I k + cz a I * cz b (k - I).
Proof.
  intros a b I k HI. unfold rows.
  rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma rows_zero : forall a b k, rows a b 0 k = 0.
Proof. reflexivity. Qed.

(* row I, done for the columns j < J *)
Definition partial (a b : list Z) (I J k : Z) : Z :=
  rows a b I k + (if andb (I <=? k) (k <? I + J) then cz a I * cz b (k - I) else 0).

Lemma partial_full : forall a b I k, 0 <= I ->
  partial a b I (Z.of_nat (List.length b)) k = rows a b (I + 1) k.
Proof.
  intros a b I k HI. unfold partial. rewrite rows_succ by exact HI. f_equal.
  destruct (Z.leb_spec I k), (Z.ltb_spec k (I + Z.of_nat (List.length b))); simpl;
    try reflexivity.
  - rewrite (cz_beyond b) by lia. lia.
  - rewrite (cz_neg b) by lia. lia.
  - rewrite (cz_neg b) by lia. lia.
Qed.

Definition conv (a b : list Z) (k : Z) : Z := rows a b (Z.of_nat (List.length a)) k.

(* ------------------------------------------------------------------ *)
(* Math side: the product polynomial                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint padd (p q : list Z) : list Z :=
  match p with
  | [] => q
  | c :: p' => match q with
               | [] => p
               | d :: q' => (c + d) :: padd p' q'
               end
  end.

Definition pscale (c : Z) (q : list Z) : list Z := map (Z.mul c) q.

Fixpoint pmul (a b : list Z) : list Z :=
  match a with
  | [] => []
  | c :: a' => padd (pscale c b) (0 :: pmul a' b)
  end.

Lemma eval_padd : forall p q x, eval (padd p q) x = eval p x + eval q x.
Proof.
  induction p as [| c p IH]; intros q x; [simpl; lia|].
  destruct q as [| d q]; simpl; [lia|]. rewrite IH. ring.
Qed.

Lemma eval_pscale : forall c q x, eval (pscale c q) x = c * eval q x.
Proof.
  intros c q x. unfold pscale. induction q as [| d q IH]; simpl; [lia|].
  rewrite IH. ring.
Qed.

Lemma eval_pmul : forall a b x, eval (pmul a b) x = eval a x * eval b x.
Proof.
  induction a as [| c a IH]; intros b x; [reflexivity|].
  simpl. rewrite eval_padd, eval_pscale. simpl. rewrite IH. ring.
Qed.

Lemma length_padd : forall p q,
  List.length (padd p q) = Nat.max (List.length p) (List.length q).
Proof.
  induction p as [| c p IH]; intros q; [reflexivity|].
  destruct q as [| d q]; simpl; [lia|]. rewrite IH. reflexivity.
Qed.

Lemma length_pmul : forall a b, (0 < List.length b)%nat ->
  List.length (pmul a b) =
    match a with [] => O | _ => (List.length a + List.length b - 1)%nat end.
Proof.
  induction a as [| c a IH]; intros b Hb; [reflexivity|].
  simpl. rewrite length_padd. unfold pscale. rewrite length_map. simpl.
  rewrite (IH b Hb). destruct a; simpl; lia.
Qed.

Lemma nth_padd : forall p q n, nth n (padd p q) 0 = nth n p 0 + nth n q 0.
Proof.
  induction p as [| c p IH]; intros q n.
  - simpl. destruct n; lia.
  - destruct q as [| d q]; destruct n; simpl; try lia. apply IH.
Qed.

Lemma nth_pscale : forall c q n, nth n (pscale c q) 0 = c * nth n q 0.
Proof.
  intros c q. unfold pscale. induction q as [| d q IH]; intros n;
    destruct n; simpl; try lia. apply IH.
Qed.

Lemma nth_pmul : forall a b (n : nat), nth n (pmul a b) 0 = conv a b (Z.of_nat n).
Proof.
  induction a as [| c a IH]; intros b n.
  - simpl. destruct n; reflexivity.
  - simpl pmul. rewrite nth_padd, nth_pscale.
    unfold conv, rows. simpl List.length. rewrite Nat2Z.id, sumn_shift.
    assert (E0 : cz (c :: a) (Z.of_nat 0) * cz b (Z.of_nat n - Z.of_nat 0)
                 = c * nth n b 0).
    { unfold cz. simpl. rewrite Z.sub_0_r.
      destruct (Z.ltb_spec (Z.of_nat n) 0); [lia|]. rewrite Nat2Z.id. reflexivity. }
    rewrite E0. f_equal.
    destruct n as [| m].
    + simpl. symmetry. apply sumn_zero. intros i Hi.
      rewrite (cz_neg b) by lia. lia.
    + simpl nth. rewrite IH. unfold conv, rows. rewrite Nat2Z.id.
      apply sumn_ext. intros i Hi. rewrite cz_cons_succ. f_equal. f_equal. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the inputs                                                  *)
(* ------------------------------------------------------------------ *)

Lemma repr_get : forall (x : array sint) (a : list Z), repr x a ->
  forall i : int, (φ i) < Z.of_nat (List.length a) ->
  Sint63.to_Z x.[i] = cz a (φ i).
Proof.
  intros x a [Hl Hc] i Hi.
  pose proof (to_Z_bounded i) as Bi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by lia.
  rewrite of_to_Z in Hr. rewrite Hr.
  unfold cz. destruct (Z.ltb_spec (φ i) 0); [lia|].
  symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma sint_mod : forall v : int, Sint63.to_Z v mod wB = (φ v).
Proof. intros v. apply Sint63.to_Z_mod_Uint63to_Z. Qed.

Lemma step_arith : forall (Rm R X Y A B : Z),
  Rm = R mod wB -> A mod wB = X -> B mod wB = Y ->
  (Rm + (X * Y) mod wB) mod wB = (R + A * B) mod wB.
Proof.
  intros Rm R X Y A B HR HX HY. subst.
  rewrite <- Zmult_mod, Zplus_mod_idemp_r, Zplus_mod_idemp_l. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The loops                                                           *)
(* ------------------------------------------------------------------ *)

Lemma row_loop_spec : forall (a b : list Z) (y : array sint),
  repr y b ->
  forall (L i ai : int),
  (φ L) = Z.of_nat (List.length a) + Z.of_nat (List.length b) - 1 ->
  (φ i) < Z.of_nat (List.length a) ->
  (φ ai) = cz a (φ i) mod wB ->
  forall (z : Z) (j : int) (r : array int)
         (H : Acc (Zwf 0) (gap (PArray.length y) j)),
  gap (PArray.length y) j = z ->
  (φ j) <= Z.of_nat (List.length b) ->
  PArray.length r = L ->
  (forall k : int, (φ k) < (φ L) ->
     (φ (r.[k])) = partial a b (φ i) (φ j) (φ k) mod wB) ->
  PArray.length (row_loop y ai i (PArray.length y) j r H) = L /\
  forall k : int, (φ k) < (φ L) ->
    (φ ((row_loop y ai i (PArray.length y) j r H).[k]))
    = partial a b (φ i) (Z.of_nat (List.length b)) (φ k) mod wB.
Proof.
  intros a b y Hb L i ai HL Hi Hai z.
  pose proof (repr_length y b Hb) as Ly.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j r H Hz Hj Hlen Hinv.
  rewrite row_loop_eq.
  destruct (bdec (j <? PArray.length y)%uint63) as [Hjb | Hjb].
  - pose proof Hjb as Hj'. rewrite ltb_spec in Hj'.
    pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded j) as Bj.
    pose proof (to_Z_bounded L) as BL.
    assert (Hj1 : (φ (j + 1)) = (φ j) + 1) by sia.
    assert (Hk0 : (φ (i + j)) = (φ i) + (φ j)) by sia.
    cbv zeta.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hjb.
    + rewrite alength_set. exact Hlen.
    + intros k Hk. rewrite Hj1.
      destruct (Z.eq_dec (φ k) (φ (i + j))) as [Ek | Ek].
      * assert (k = (i + j)%uint63) by (apply to_Z_inj; exact Ek). subst k.
        rewrite aget_set_same by (rewrite ltb_spec, Hlen; lia).
        rewrite add_spec, mul_spec, Hinv by lia.
        assert (Pold : partial a b (φ i) (φ j) (φ (i + j)) = rows a b (φ i) (φ (i + j))).
        { unfold partial. rewrite Hk0.
          destruct (Z.leb_spec (φ i) ((φ i) + (φ j))); [|lia].
          destruct (Z.ltb_spec ((φ i) + (φ j)) ((φ i) + (φ j))); [lia|]. simpl. lia. }
        assert (Pnew : partial a b (φ i) ((φ j) + 1) (φ (i + j))
                       = rows a b (φ i) (φ (i + j)) + cz a (φ i) * cz b (φ j)).
        { unfold partial. rewrite Hk0.
          destruct (Z.leb_spec (φ i) ((φ i) + (φ j))); [|lia].
          destruct (Z.ltb_spec ((φ i) + (φ j)) ((φ i) + ((φ j) + 1))); [|lia]. simpl.
          replace ((φ i) + (φ j) - (φ i)) with (φ j) by lia. reflexivity. }
        rewrite Pold, Pnew.
        apply step_arith.
        -- reflexivity.
        -- symmetry. exact Hai.
        -- rewrite <- (repr_get y b Hb j) by lia. apply sint_mod.
      * rewrite aget_set_other by (intro F; apply Ek; rewrite F; reflexivity).
        rewrite Hinv by exact Hk. unfold partial. f_equal. f_equal.
        rewrite Hk0 in Ek.
        destruct (Z.leb_spec (φ i) (φ k)), (Z.ltb_spec (φ k) ((φ i) + (φ j))),
                 (Z.ltb_spec (φ k) ((φ i) + ((φ j) + 1))); simpl; try reflexivity; lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hjb.
    split; [exact Hlen|].
    intros k Hk. rewrite Hinv by exact Hk.
    replace (φ j) with (Z.of_nat (List.length b)) by lia. reflexivity.
Qed.

Lemma rows_loop_spec : forall (a b : list Z) (x y : array sint),
  repr x a -> repr y b ->
  forall L : int,
  (φ L) = Z.of_nat (List.length a) + Z.of_nat (List.length b) - 1 ->
  forall (z : Z) (i : int) (r : array int)
         (H : Acc (Zwf 0) (gap (PArray.length x) i)),
  gap (PArray.length x) i = z ->
  (φ i) <= Z.of_nat (List.length a) ->
  PArray.length r = L ->
  (forall k : int, (φ k) < (φ L) -> (φ (r.[k])) = rows a b (φ i) (φ k) mod wB) ->
  PArray.length (rows_loop x y (PArray.length x) (PArray.length y) i r H) = L /\
  forall k : int, (φ k) < (φ L) ->
    (φ ((rows_loop x y (PArray.length x) (PArray.length y) i r H).[k]))
    = conv a b (φ k) mod wB.
Proof.
  intros a b x y Ha Hb L HL z.
  pose proof (repr_length x a Ha) as Lx.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i r H Hz Hi Hlen Hinv.
  rewrite rows_loop_eq.
  destruct (bdec (i <? PArray.length x)%uint63) as [Hia | Hia].
  - pose proof Hia as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
    assert (Hai : (φ (x.[i])) = cz a (φ i) mod wB).
    { rewrite <- (repr_get x a Ha i) by lia. symmetry. apply sint_mod. }
    assert (Hia2 : (φ i) < Z.of_nat (List.length a)) by lia.
    destruct (row_loop_spec a b y Hb L i x.[i] HL Hia2 Hai
                _ 0 r (Zwf_well_founded 0 (gap (PArray.length y) 0)) eq_refl
                ltac:(change (φ 0) with 0; lia) Hlen
                ltac:(intros k Hk; rewrite Hinv by exact Hk; unfold partial;
                      change (φ 0) with 0;
                      destruct (Z.leb_spec (φ i) (φ k));
                      destruct (Z.ltb_spec (φ k) ((φ i) + 0));
                      simpl; first [lia | f_equal; lia]))
      as [Hl' Hc'].
    eapply IH; [ | reflexivity | lia | exact Hl' | ].
    + rewrite <- Hz. apply dec_step. exact Hia.
    + intros k Hk. rewrite Hi1, <- partial_full by lia. exact (Hc' k Hk).
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hia.
    split; [exact Hlen|].
    intros k Hk. rewrite Hinv by exact Hk. unfold conv.
    replace (φ i) with (Z.of_nat (List.length a)) by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The output                                                          *)
(* ------------------------------------------------------------------ *)

Lemma pmul_product : forall a b, valid_input a b -> polymul_spec a b (pmul a b).
Proof.
  intros a b [Hva Hvb _ _ _]. unfold len in Hva, Hvb.
  split.
  - unfold len. rewrite length_pmul by lia.
    destruct a as [| c a']; [simpl in Hva; lia|].
    rewrite Nat2N.inj_sub, Nat2N.inj_add. simpl. lia.
  - intros x. apply eval_pmul.
Qed.

Lemma out_correct : forall (a b : list Z) (r : array@{Set} sint) (L : int),
  valid_input a b ->
  PArray.length@{Set} r = L ->
  (φ L) = Z.of_nat (List.length a) + Z.of_nat (List.length b) - 1 ->
  (forall k : int, (φ k) < (φ L) ->
     (φ (PArray.get@{Set} r k)) = conv a b (φ k) mod wB) ->
  repr r (pmul a b) /\ polymul_spec a b (pmul a b).
Proof.
  intros a b r L Hv Hrl0 HL Hrc0.
  (* [repr] reads the array at the universe of Repr.v's instance; the
     primitive operations at Set and at that universe are convertible. *)
  assert (Hrl : PArray.length@{repr_array.u0} r = L) by exact Hrl0.
  assert (Hrc : forall k : int, (φ k) < (φ L) ->
     (φ (PArray.get@{repr_array.u0} r k)) = conv a b (φ k) mod wB)
    by exact Hrc0.
  clear Hrl0 Hrc0.
  pose proof (pmul_product a b Hv) as Hp.
  pose proof (vi_product a b Hv _ Hp) as Hbnd.
  destruct Hv as [Hva Hvb _ _ _].
  unfold len in Hva, Hvb.
  assert (Hlen_p : List.length (pmul a b) = (List.length a + List.length b - 1)%nat).
  { rewrite length_pmul by lia. destruct a; simpl in *; lia. }
  split; [| exact Hp].
  split.
  - rewrite Hlen_p, Hrl, HL. lia.
  - intros n Hn. rewrite Hlen_p in Hn.
    exists (nth n (pmul a b) 0). split.
    + apply nth_error_nth'. rewrite Hlen_p. exact Hn.
    + unfold repr, repr_sint.
      assert (Hn' : (φ (of_Z (Z.of_nat n))) = Z.of_nat n).
      { rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
      rewrite Sint63.to_Z_cmodwB, Hrc by (rewrite Hn', HL; lia).
      rewrite Sint63.cmod_mod, Hn', <- nth_pmul.
      apply Sint63.cmod_small.
      rewrite Forall_forall in Hbnd.
      assert (Hin := Hbnd _ (@nth_In _ n (pmul a b) 0 ltac:(rewrite Hlen_p; lia))).
      rewrite wB_val. change (9223372036854775808 / 2) with 4611686018427387904.
      lia.
Qed.

Lemma polymul_impl_correct : forall (a b : list Z) (x y : array sint),
  valid_input a b -> repr x a -> repr y b ->
  exists p : list Z, repr (polymul_impl x y) p /\ polymul_spec a b p.
Proof.
  intros a b x y Hv Ha Hb.
  pose proof Hv as Hv'.
  destruct Hv' as [Hva Hvb _ _ _].
  unfold len in Hva, Hvb.
  pose proof (repr_length x a Ha) as Lx. pose proof (repr_length y b Hb) as Ly.
  exists (pmul a b).
  unfold polymul_impl.
  assert (Ex : (PArray.length x =? 0)%uint63 = false)
    by (rewrite eqb_false_spec; intro E; rewrite E in Lx; change (φ 0) with 0 in Lx; lia).
  assert (Ey : (PArray.length y =? 0)%uint63 = false)
    by (rewrite eqb_false_spec; intro E; rewrite E in Ly; change (φ 0) with 0 in Ly; lia).
  lazymatch goal with |- context [if ?c then _ else _] =>
    replace c with false by (symmetry; exact Ex) end.
  lazymatch goal with |- context [if ?c then _ else _] =>
    replace c with false by (symmetry; exact Ey) end.
  assert (HL : (φ (PArray.length x + PArray.length y - 1))%uint63
               = Z.of_nat (List.length a) + Z.of_nat (List.length b) - 1)
    by sia.
  assert (HmL : PArray.length (PArray.make (PArray.length x + PArray.length y - 1) 0%uint63)
                = (PArray.length x + PArray.length y - 1)%uint63).
  { rewrite alength_make.
    replace (PArray.length x + PArray.length y - 1 <=? PArray.max_length)%uint63 with true;
      [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  destruct (rows_loop_spec a b x y Ha Hb
              (PArray.length x + PArray.length y - 1) HL
              _ 0 (PArray.make (PArray.length x + PArray.length y - 1) 0%uint63)
              (Zwf_well_founded 0 (gap (PArray.length x) 0))
              eq_refl
              ltac:(change (φ 0) with 0; lia) HmL
              ltac:(intros k Hk; rewrite aget_make; reflexivity))
    as [Hrl Hrc].
  exact (out_correct a b _ _ Hv Hrl HL Hrc).
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition polymul : array sint -> array sint -> array sint := polymul_impl.
Elpi complexity polymul.

Definition polymul_correct : forall (a b : list Z) (x y : array sint),
  valid_input a b -> repr x a -> repr y b ->
  exists p : list Z, repr (polymul x y) p /\ polymul_spec a b p
  := polymul_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import ssreflect.

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

Lemma row_loop_time y yC ai aiC i iC lb lbC j jC r rC H HC :
  (cost (extract (extract (extract (extract (extract (extract (row_loop_cost stepsCM y yC) ai aiC) i iC) lb lbC) j jC) r rC) H HC)
   <= 50 * Z.to_nat (gap lb j) + 10)%nat.
Proof.
  unfold row_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G y yC ai aiC i iC lb lbC j jC r rC H HC)] =>
    assert (HG : forall m j jC r rC H HC, (Z.to_nat (gap lb j) <= m)%nat ->
       (cost (G y yC ai aiC i iC lb lbC j jC r rC H HC) <= 50 * m + 10)%nat) end.
  { induction m as [|m IH]; intros j' jC' r' rC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (j' <? lb)%uint63 (bool_w (j' <? lb)%uint63)) as HB;
      cost_destruct (bdec (j' <? lb)%uint63); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hm' : (Z.to_nat (gap lb (j' + 1)) <= m)%nat).
      { unfold gap in *. assert (φ (j' + 1) = φ j' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      set_simpl. z0 row_loop_cost; z1 row_loop_cost; z2 row_loop_cost; z3 row_loop_cost; z4 row_loop_cost; z5 row_loop_cost.
      match goal with |- context [@cost ?T (?G' y yC ai aiC i iC lb lbC (j' + 1)%uint63 ?w ?d ?dC ?a ?e)] =>
        have HI := (IH (j' + 1)%uint63 w d dC a e Hm' : (@cost T (G' y yC ai aiC i iC lb lbC (j' + 1)%uint63 w d dC a e) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G y yC ai aiC i iC lb lbC j jC r rC H HC)] =>
    exact (HG _ j jC r rC H HC (le_n _) : (@cost T (G y yC ai aiC i iC lb lbC j jC r rC H HC) <= _)%nat) end.
Qed.

Ltac gen_row := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (row_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    let Hc := fresh "Hrow" in
    have Hc := (row_loop_time a aC b bC c cC d dC e eC f fC g gC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma rows_loop_time x xC y yC la laC lb lbC i iC r rC H HC :
  (cost (extract (extract (extract (extract (extract (extract (rows_loop_cost stepsCM x xC) y yC) la laC) lb lbC) i iC) r rC) H HC)
   <= (50 * Z.to_nat (gap lb 0) + 100) * Z.to_nat (gap la i) + 10)%nat.
Proof.
  remember (Z.to_nat (gap lb 0)) as GB eqn:EGB.
  unfold rows_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC la laC lb lbC i iC r rC H HC)] =>
    assert (HG : forall m i iC r rC H HC, (Z.to_nat (gap la i) <= m)%nat ->
       (cost (G x xC y yC la laC lb lbC i iC r rC H HC) <= (50 * GB + 100) * m + 10)%nat) end.
  { induction m as [|m IH]; intros i' iC' r' rC' [g] HC' Hm;
      cost_simpl;
      pose proof (bdec_time (i' <? la)%uint63 (bool_w (i' <? la)%uint63)) as HB;
      cost_destruct (bdec (i' <? la)%uint63); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hm. lia.
    - lia.
    - z0 row_loop_cost; z1 row_loop_cost; z2 row_loop_cost; z3 row_loop_cost; z4 row_loop_cost; z5 row_loop_cost.
      gen_row. rewrite <- EGB in Hrow.
      cost_simpl.
      pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hm' : (Z.to_nat (gap la (i' + 1)) <= m)%nat).
      { unfold gap in *. assert (φ (i' + 1) = φ i' + 1)%Z by (zify; Z.to_euclidean_division_equations; lia). lia. }
      z0 rows_loop_cost; z1 rows_loop_cost; z2 rows_loop_cost; z3 rows_loop_cost; z4 rows_loop_cost; z5 rows_loop_cost.
      match goal with |- context [@cost ?T (?G' x xC y yC la laC lb lbC (i' + 1)%uint63 ?w ?d ?dC ?a ?e)] =>
        have HI := (IH (i' + 1)%uint63 w d dC a e Hm' : (@cost T (G' x xC y yC la laC lb lbC (i' + 1)%uint63 w d dC a e) <= _)%nat) end.
      lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC y yC la laC lb lbC i iC r rC H HC)] =>
    exact (HG _ i iC r rC H HC (le_n _) : (@cost T (G x xC y yC la laC lb lbC i iC r rC H HC) <= _)%nat) end.
Qed.

Ltac gen_rows := repeat match goal with |- context [@cost ?T ?X] =>
  lazymatch X with extract (extract (extract (extract (extract (extract (rows_loop_cost stepsCM ?a ?aC) ?b ?bC) ?c ?cC) ?d ?dC) ?e ?eC) ?f ?fC) ?g ?gC =>
    let Hc := fresh "Hrows" in
    have Hc := (rows_loop_time a aC b bC c cC d dC e eC f fC g gC : (@cost T X <= _)%nat);
    revert Hc; generalize (@cost T X); intros ? Hc end end.

Lemma gap0 x : Z.to_nat (gap x 0) = Z.to_nat (φ x).
Proof. unfold gap. change (φ 0) with 0%Z. rewrite Z.sub_0_r. reflexivity. Qed.


Theorem polymul_time : exists c1 c2 : nat,
  forall (first_coeffs second_coeffs : list ℤ)
  (first_coeffs_arr second_coeffs_arr : array sint),
  valid_input first_coeffs second_coeffs ->
  repr first_coeffs_arr first_coeffs ->
  repr second_coeffs_arr second_coeffs ->
  (cost2 polymul_cost first_coeffs_arr second_coeffs_arr <= c1 * ((size first_coeffs_arr + 1) * (size second_coeffs_arr + 1)) + c2)%nat.
Proof.
  exists 150%nat, 100%nat. intros a b x y _ _ _.
  remember (size x) as P eqn:EP. remember (size y) as Q eqn:EQ.
  match goal with |- (_ <= ?R)%nat => remember R as RHS eqn:ER end.
  unfold cost2, polymul_cost, polymul_impl_cost. cost_simpl.
  z0 make_cost. z1 make_cost.
  repeat match goal with
  | |- context [cost (extract (extract (make_cost ?a ?b ?c) ?d ?e) ?f ?g)] =>
      change (cost (extract (extract (make_cost a b c) d e) f g)) with 1%nat
  end.
  z0 rows_loop_cost; z1 rows_loop_cost; z2 rows_loop_cost; z3 rows_loop_cost; z4 rows_loop_cost; z5 rows_loop_cost.
  gen_rows.
  rewrite !gap0 in Hrows.
  assert (E1 : Z.to_nat (φ (length x)) = P) by (rewrite EP; reflexivity).
  assert (E2 : Z.to_nat (φ (length y)) = Q) by (rewrite EQ; reflexivity).
  rewrite E1 E2 in Hrows.
  destruct (length x =? 0)%uint63; [|destruct (length y =? 0)%uint63]; cbn [cost].
  all: clear E1 E2 EP EQ; subst RHS.
  all: cbn; assert (Hb : ((50 * Q + 100) * P + 10 <= 150 * ((P + 1) * (Q + 1)))%nat) by nia;
    revert Hb Hrows; generalize ((50 * Q + 100) * P)%nat ((P + 1) * (Q + 1))%nat; intros; lia.
Qed.

Print Assumptions polymul_time.
