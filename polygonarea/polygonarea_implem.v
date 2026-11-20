(* Implementation of polygonarea (polygonarea.spec): the shoelace formula,
   one left-to-right pass.

   Code.  [signed_area2 x y] with n = |x| runs i = 0 .. n-2 accumulating
   x.[i] * y.[i+1] - x.[i+1] * y.[i] in one int, then adds the closing term
   x.[n-1] * y.[0] - x.[0] * y.[n-1].  Both arrays are only read, nothing is
   allocated.  The arithmetic is wrapping 63-bit: every operation is exact
   modulo 2^63, and the contract bounds |shoelace| by 2 * 1000 * 10^8 < 2^62,
   so the word read through Sint63 is the exact sum.  No Z in the code.

   Termination: the loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1.

   Cost: [Elpi complexity] translates sumbool, bdec, area_loop,
   signed_area2_impl and signed_area2 (callee first).  area_loop from i costs
   at most gap m i * 100 + 10 steps (area_loop_time), the whole call at most
   loop_meas x * 100 + 100 (signed_area2_steps), and on a valid input
   (n >= 3, so length x - 1 does not wrap) at most 100 * (|x| + |y| + 1)
   (signed_area2_time). *)

From Polygonarea.spec Require Import Prelude.
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
(* Uint63 plumbing                                                     *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

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

(* acc + sum_{j = i}^{m - 1} (x.[j] * y.[j+1] - x.[j+1] * y.[j]), mod 2^63. *)
Fixpoint area_loop (x y : array int) (m i acc : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : int :=
  match bdec (i <? m) with
  | left Hi =>
      area_loop x y m (i + 1)
        (acc + x.[i] * y.[i + 1] - x.[i + 1] * y.[i])
        (Acc_inv H (dec_step m i Hi))
  | right _ => acc
  end.
Elpi complexity area_loop.

Lemma area_loop_eq : forall x y m i acc H,
  area_loop x y m i acc H =
  match bdec (i <? m) with
  | left Hi =>
      area_loop x y m (i + 1)
        (acc + x.[i] * y.[i + 1] - x.[i + 1] * y.[i])
        (Acc_inv H (dec_step m i Hi))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition signed_area2_impl (x y : array sint) : sint :=
  let m := PArray.length x - 1 in
  let s := area_loop x y m 0 0 (Zwf_well_founded 0 (gap m 0)) in
  s + x.[m] * y.[0] - x.[0] * y.[m].
Elpi complexity signed_area2_impl.

(* ------------------------------------------------------------------ *)
(* Prop side                                                           *)
(* ------------------------------------------------------------------ *)

(* Reading an in-bounds cell of an array representing a. *)
Lemma repr_get : forall (x : array sint) (a : list Z), repr x a ->
  forall i : int, ((φ i) < Z.of_nat (List.length a))%Z ->
  Sint63.to_Z x.[i] = get_list_Z a (Z.to_N (φ i)).
Proof.
  intros x a [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  unfold get_list_Z. rewrite Z_N_nat. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (a : list Z), repr x a ->
  (φ (PArray.length x)) = Z.of_nat (List.length a).
Proof. intros x a [Hl _]. symmetry. exact Hl. Qed.

Lemma sint_mod : forall v : int, (Sint63.to_Z v mod wB)%Z = (φ v).
Proof. intros v. apply Sint63.to_Z_mod_Uint63to_Z. Qed.

(* A word whose unsigned value is z modulo 2^63, z in the signed range,
   reads z through Sint63. *)
Lemma sint_exact : forall (v : int) (z : Z),
  (φ v) = (z mod wB)%Z -> (-4611686018427387904 <= z < 4611686018427387904)%Z ->
  Sint63.to_Z v = z.
Proof.
  intros v z Hv Hz.
  rewrite Sint63.to_Z_cmodwB, Hv, Sint63.cmod_mod.
  apply Sint63.cmod_small.
  rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z.
  lia.
Qed.

(* One step of the accumulation, modulo 2^63. *)
Lemma step_arith : forall (acc s A B C D SA SB SC SD : Z),
  (SA mod wB = A -> SB mod wB = B -> SC mod wB = C -> SD mod wB = D ->
   acc = s mod wB ->
   (((acc + (A * B) mod wB) mod wB - (C * D) mod wB) mod wB
    = (s + (SA * SB - SC * SD)) mod wB))%Z.
Proof.
  intros acc s A B C D SA SB SC SD HA HB HC HD Hacc. subst.
  rewrite <- (Zmult_mod SA SB), <- (Zmult_mod SC SD).
  rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r.
  rewrite Zminus_mod_idemp_r, Zminus_mod_idemp_l.
  f_equal. ring.
Qed.

(* The shoelace term of vertex i. *)
Definition term (a b : list Z) : N -> Z :=
  fun i => (get_list_Z a i * get_list_Z b (next (len a) i)
            - get_list_Z a (next (len a) i) * get_list_Z b i)%Z.

Lemma next_inner : forall n i : N, (i + 1 < n)%N -> next n i = (i + 1)%N.
Proof. intros n i H. unfold next. apply N.mod_small. exact H. Qed.

Lemma next_last : forall n : N, (1 <= n)%N -> next n (n - 1) = 0%N.
Proof.
  intros n H. unfold next. replace (n - 1 + 1)%N with n by lia.
  apply N.mod_same. lia.
Qed.

(* The loop over i = 0 .. m - 1, m = n - 1. *)
Lemma area_loop_spec : forall (a b : list Z) (x y : array sint),
  repr x a -> repr y b -> List.length b = List.length a ->
  forall m : int, ((φ m) + 1 = Z.of_nat (List.length a))%Z ->
  forall (z : Z) (i acc : int) (H : Acc (Zwf 0) (gap m i)),
  gap m i = z ->
  ((φ i) <= (φ m))%Z ->
  (φ acc) = (sum_below (term a b) (Z.to_nat (φ i)) mod wB)%Z ->
  (φ (area_loop x y m i acc H))
  = (sum_below (term a b) (Z.to_nat (φ m)) mod wB)%Z.
Proof.
  intros a b x y Ha Hb Hlb m Hm z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i acc H Hz Him Hacc.
  rewrite area_loop_eq.
  destruct (bdec (i <? m)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded m) as Bm.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hi.
    + rewrite Hi1, Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
      pose proof (repr_get x a Ha i ltac:(lia)) as E1.
      pose proof (repr_get y b Hb i ltac:(lia)) as E2.
      pose proof (repr_get x a Ha (i + 1) ltac:(lia)) as E3.
      pose proof (repr_get y b Hb (i + 1) ltac:(lia)) as E4.
      rewrite Hi1 in E3, E4.
      unfold term.
      replace (N.of_nat (Z.to_nat (φ i))) with (Z.to_N (φ i)) by lia.
      rewrite next_inner by (unfold len; lia).
      replace (Z.to_N (φ i) + 1)%N with (Z.to_N ((φ i) + 1)) by lia.
      rewrite sub_spec, add_spec, !mul_spec.
      rewrite <- E1, <- E2, <- E3, <- E4.
      apply step_arith; try apply sint_mod. exact Hacc.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    replace (φ m) with (φ i) by lia. exact Hacc.
Qed.

(* Every coordinate, and so every read of the list, is within 10^4. *)
Lemma get_bounded : forall (l : list Z) (k : N),
  Forall (fun c => -10000 <= c <= 10000)%Z l ->
  (-10000 <= get_list_Z l k <= 10000)%Z.
Proof.
  intros l k Hf. unfold get_list_Z.
  destruct (nth_in_or_default (N.to_nat k) l 0%Z) as [Hin | Hd].
  - rewrite Forall_forall in Hf. apply Hf. exact Hin.
  - rewrite Hd. lia.
Qed.

Lemma term_bounded : forall a b k,
  Forall (fun c => -10000 <= c <= 10000)%Z a ->
  Forall (fun c => -10000 <= c <= 10000)%Z b ->
  (Z.abs (term a b k) <= 200000000)%Z.
Proof.
  intros a b k Ha Hb. unfold term.
  pose proof (get_bounded a k Ha) as B1.
  pose proof (get_bounded b (next (len a) k) Hb) as B2.
  pose proof (get_bounded a (next (len a) k) Ha) as B3.
  pose proof (get_bounded b k Hb) as B4.
  set (p := get_list_Z a k) in *. set (q := get_list_Z b (next (len a) k)) in *.
  set (r := get_list_Z a (next (len a) k)) in *. set (s := get_list_Z b k) in *.
  assert (Z.abs (p * q) <= 100000000)%Z.
  { rewrite Z.abs_mul. apply (Z.le_trans _ (10000 * 10000)); [|lia].
    apply Z.mul_le_mono_nonneg; lia. }
  assert (Z.abs (r * s) <= 100000000)%Z.
  { rewrite Z.abs_mul. apply (Z.le_trans _ (10000 * 10000)); [|lia].
    apply Z.mul_le_mono_nonneg; lia. }
  lia.
Qed.

Lemma sum_below_bounded : forall (f : N -> Z) (B : Z) n,
  (forall k, Z.abs (f k) <= B)%Z ->
  (Z.abs (sum_below f n) <= Z.of_nat n * B)%Z.
Proof.
  intros f B n Hf. induction n as [| n IH]; [simpl; lia|].
  cbn [sum_below].
  pose proof (Hf (N.of_nat n)). rewrite Nat2Z.inj_succ, Z.mul_succ_l.
  pose proof (Z.abs_triangle (sum_below f n) (f (N.of_nat n))). lia.
Qed.

Lemma signed_area2_impl_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists v : Z, repr (signed_area2_impl x y) v /\ signed_area2_spec xs ys v.
Proof.
  intros a b x y Hv Ha Hb.
  destruct Hv as [Hn Hlb Hfa Hfb].
  unfold len in Hn, Hlb.
  assert (Hlb' : List.length b = List.length a) by lia.
  assert (Hla : (3 <= Z.of_nat (List.length a) <= 1000)%Z) by lia.
  assert (Hsh : shoelace a b = sum_below (term a b) (List.length a)).
  { unfold shoelace, len. rewrite Nat2N.id. reflexivity. }
  pose proof (repr_length x a Ha) as Lx.
  exists (shoelace a b). split; [| reflexivity].
  unfold repr, repr_sint, signed_area2_impl.
  assert (Hm : (φ (PArray.length x - 1)) = (Z.of_nat (List.length a) - 1)%Z)
    by (rewrite sub_spec, Lx; change (φ 1) with 1%Z;
       apply Z.mod_small; rewrite wB_val; lia).
  set (m := PArray.length x - 1) in *.
  pose proof (area_loop_spec a b x y Ha Hb Hlb' m ltac:(lia) _ 0 0
                (Zwf_well_founded 0 (gap m 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia)
                ltac:(change (φ 0) with 0%Z; reflexivity)) as Hloop.
  set (s := area_loop x y m 0 0 _) in *.
  (* the unsigned value modulo 2^63 *)
  assert (Hmod : (φ (s + x.[m] * y.[0] - x.[0] * y.[m]))
                 = (shoelace a b mod wB)%Z).
  { pose proof (repr_get x a Ha m ltac:(lia)) as E1.
    pose proof (repr_get y b Hb 0 ltac:(change (φ 0) with 0%Z; lia)) as E2.
    pose proof (repr_get x a Ha 0 ltac:(change (φ 0) with 0%Z; lia)) as E3.
    pose proof (repr_get y b Hb m ltac:(lia)) as E4.
    change (φ 0) with 0%Z in E2, E3.
    rewrite sub_spec, add_spec, !mul_spec.
    rewrite Hsh.
    replace (List.length a) with (S (Z.to_nat (φ m))) by lia.
    simpl sum_below.
    replace (term a b (N.of_nat (Z.to_nat (φ m)))) with
      (get_list_Z a (Z.to_N (φ m)) * get_list_Z b (Z.to_N 0)
       - get_list_Z a (Z.to_N 0) * get_list_Z b (Z.to_N (φ m)))%Z.
    - rewrite <- E1, <- E2, <- E3, <- E4.
      apply step_arith; try apply sint_mod. exact Hloop.
    - unfold term. replace (N.of_nat (Z.to_nat (φ m))) with (len a - 1)%N
        by (unfold len; lia).
      replace (Z.to_N (φ m)) with (len a - 1)%N by (unfold len; lia).
      rewrite next_last by (unfold len; lia). reflexivity. }
  (* the signed reading is the exact sum *)
  assert (Hbound : (Z.abs (shoelace a b) <= 200000000000)%Z).
  { rewrite Hsh.
    pose proof (sum_below_bounded (term a b) 200000000 (List.length a)
                  (fun k => term_bounded a b k Hfa Hfb)) as Hs.
    clear - Hs Hla. lia. }
  apply sint_exact; [exact Hmod | clear - Hbound; lia].
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition signed_area2 : array sint -> array sint -> sint := signed_area2_impl.
Elpi complexity signed_area2.

Definition signed_area2_correct : forall (xs ys : list Z) (x y : array sint),
  valid_input xs ys -> repr x xs -> repr y ys ->
  exists v : Z, repr (signed_area2 x y) v /\ signed_area2_spec xs ys v
  := signed_area2_impl_correct.

(* ------------------------------------------------------------------ *)
(* Cost                                                                *)
(* ------------------------------------------------------------------ *)

From Stdlib Require Import ssreflect.

Lemma bdec_time b (w : bool_cost stepsCM b) : (cost (bdec_cost stepsCM b w) <= 2)%nat.
Proof. destruct w; cbn; lia. Qed.

Lemma area_loop_time x xC y yC m mC i iC acc accC H HC :
  (cost (extract (extract (extract (extract (extract (area_loop_cost stepsCM x xC) y yC) m mC) i iC) acc accC) H HC)
     <= Z.to_nat (gap m i) * 100 + 10)%nat.
Proof.
  unfold area_loop_cost. cbn.
  match goal with |- context [@cost ?T (?G x xC y yC m mC i iC acc accC H HC)] =>
    assert (HG : forall k i iC acc accC H HC, (Z.to_nat (gap m i) <= k)%nat ->
       (cost (G x xC y yC m mC i iC acc accC H HC) <= k * 100 + 10)%nat) end.
  { induction k as [|k IH]; intros i' iC' acc' accC' [g] HC' Hk;
      cost_simpl;
      pose proof (bdec_time (i' <? m) (bool_w (i' <? m))) as HB;
      cost_destruct (bdec (i' <? m)); cost_simpl.
    - exfalso. pose proof (proj1 (Uint63.ltb_spec _ _) e). unfold gap in Hk. lia.
    - lia.
    - pose proof (proj1 (Uint63.ltb_spec _ _) e) as Hlt.
      assert (Hk' : (Z.to_nat (gap m (i' + 1)) <= k)%nat).
      { unfold gap in *. assert (φ (i' + 1) = φ i' + 1)%Z by sia. lia. }
      match goal with |- context [@cost ?T (?G' x xC y yC m mC (i' + 1)%uint63 ?w ?c ?wc ?h ?e)] =>
        have HI := (IH (i' + 1)%uint63 w c wc h e : _ -> (@cost T (G' x xC y yC m mC (i' + 1)%uint63 w c wc h e) <= _)%nat) end.
      specialize (HI Hk'). lia.
    - lia. }
  match goal with |- context [@cost ?T (?G x xC y yC m mC i iC acc accC H HC)] =>
    exact (HG _ i iC acc accC H HC (le_n _) : (@cost T (G x xC y yC m mC i iC acc accC H HC) <= _)%nat) end.
Qed.

Definition loop_meas (x : array sint) : nat := Z.to_nat (gap (PArray.length x - 1) 0).
Arguments loop_meas : simpl never.

Lemma signed_area2_steps : forall x y : array sint,
  (cost2 signed_area2_cost x y <= loop_meas x * 100 + 100)%nat.
Proof.
  intros x y. unfold cost2, signed_area2_cost. rewrite call_cost2_eq. cost_simpl.
  match goal with |- context [@cost ?T (?G x ?xw y ?yw ?m ?mw 0%uint63 ?w1 0%uint63 ?w2 ?h ?e)] =>
    have HS := (area_loop_time x xw y yw m mw 0 w1 0 w2 h e
                : (@cost T (G x xw y yw m mw 0%uint63 w1 0%uint63 w2 h e) <= _)%nat);
    revert HS; generalize (@cost T (G x xw y yw m mw 0%uint63 w1 0%uint63 w2 h e)); intros C HS end.
  change (Z.to_nat (gap (PArray.length x - 1) 0)) with (loop_meas x) in HS.
  lia.
Qed.

(* On a valid input x has at least three cells, so length x - 1 does not
   wrap and the loop runs size x - 1 times.  (On an empty x it would wrap
   to 2^63 - 1: the bound needs the contract's premises.) *)
Lemma loop_meas_size : forall (xs : list Z) (x : array sint),
  repr x xs -> (1 <= len xs)%N -> (loop_meas x <= size x)%nat.
Proof.
  intros xs x Hx Hn. unfold loop_meas, gap.
  pose proof (repr_length x xs Hx) as Lx. unfold len in Hn.
  assert (Es : Z.to_nat (φ (PArray.length x)) = size x) by reflexivity.
  rewrite <- Es.
  match goal with |- (Z.to_nat (φ (?L - 1) - _) <= _)%nat =>
    assert (HL : φ L = Z.of_nat (List.length xs)) by exact Lx;
    assert (Hm : φ (L - 1) = (φ L - 1)%Z)
      by (rewrite sub_spec; change (φ 1) with 1%Z;
          pose proof (to_Z_bounded L); apply Z.mod_small; lia) end.
  rewrite Hm HL. change (φ 0) with 0%Z. lia.
Qed.

Theorem signed_area2_time : exists c1 c2 : nat,
  forall (x_coordinates y_coordinates : list Z)
         (x_coordinates_arr y_coordinates_arr : array sint),
  valid_input x_coordinates y_coordinates ->
  repr x_coordinates_arr x_coordinates ->
  repr y_coordinates_arr y_coordinates ->
  (cost2 signed_area2_cost x_coordinates_arr y_coordinates_arr <=
     c1 * (size x_coordinates_arr + size y_coordinates_arr + 1) + c2)%nat.
Proof.
  exists 100%nat, 0%nat. intros xs ys x y Hv Hx Hy.
  pose proof (signed_area2_steps x y) as H.
  assert (Hn : (1 <= len xs)%N) by (destruct Hv; lia).
  pose proof (loop_meas_size xs x Hx Hn) as HM.
  revert H HM. generalize (cost2 signed_area2_cost x y) (loop_meas x) (size x) (size y).
  intros. lia.
Qed.

Print Assumptions signed_area2_correct.
Print Assumptions signed_area2_time.
