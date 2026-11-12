(* Implementation of tsp.spec: CLRS 35.2 APPROX-TSP-TOUR, a minimum
   spanning tree by dense Prim (O(n^2), no heap, no edge list, no distance
   matrix), then the preorder walk of the tree from vertex 0.

   Code.  Exactness: [fex] reads every coordinate as m * 2^e (m, e in Z,
   from [frshiftexp] / [normfr_mantissa] and the standard [Uint63.to_Z]);
   E is the least exponent of all the coordinates, and GX, GY hold the
   coordinates as integers on the grid 2^E (exact).  [Dz a b] is the exact
   squared distance in units of 2^(2E), a Z: Prim compares these, so its
   choices are exact with respect to the real distances.
   Prim: rank array rk (n = not in the tree yet), key array K (Z), parent
   array P; step k picks the outside vertex of least key (one scan), gives
   it rank k, relaxes the keys of the outside vertices (one scan).
   Walk: an explicit stack and a scan pointer it[u] per vertex; at the top
   u, the vertex c = it[u] is scanned, output and pushed when P[c] = u;
   u is popped when it[u] = n.  At most n^2 + n steps, bounded by the
   [loop] combinator (erased Acc on hi - i), as are all the loops.

   Proof.  [path_bound]: Prim's cut property (the edge added at step k is
   no longer than any edge between ranks < k and ranks >= k) bounds the
   tree weight W by any Hamiltonian path (induction removing the vertex of
   largest rank), hence by any tour ([W_le_tour]).  The walk invariant
   [DI]: output length + d(last, top of stack) + length of the stack path
   <= 2 * (weight of the tree edges of the vertices output so far), by the
   triangle inequality at every pop; at the end every vertex has been
   output exactly once (induction on the rank), so the tour is at most 2 W.
   The exact distance is the spec's [dist]; [di_D] ties it to [Dz]. *)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr repr_float.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
From Tsp.spec Require Import Prelude.
Import ListNotations.

Open Scope uint63_scope.
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

Definition gap (m j : int) : Z := (to_Z m - to_Z j)%Z.

Lemma dec_step : forall hi i : int, (i <? hi) = true -> Zwf 0 (gap hi (i + 1)) (gap hi i).
Proof.
  intros hi i H. rewrite Uint63.ltb_spec in H. pose proof (to_Z_bounded hi).
  assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. unfold Zwf, gap. lia.
Qed.


(* The one loop combinator: for i = lo, lo+1, ... while i < hi and
   [cont i s], s := f i s. *)
Section Loop.
Context {St : Type}.

Fixpoint wloop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) (H : Acc (Zwf 0) (gap hi i)) {struct H} : St :=
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.

Definition loop (hi : int) (cont : int -> St -> bool) (f : int -> St -> St)
    (i : int) (s : St) : St :=
  wloop hi cont f i s (Zwf_well_founded 0 (gap hi i)).

End Loop.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* -- Exact arithmetic, used only to settle close comparisons. -------- *)

Definition zofi (i : int) : Z :=
  Uint63.to_Z i.

(* A dyadic number (m, e) denotes m * 2^e. *)
Definition dal (d : Z * Z) (e : Z) : Z := Z.shiftl (fst d) (snd d - e).
Definition dadd (a b : Z * Z) : Z * Z :=
  let e := Z.min (snd a) (snd b) in (dal a e + dal b e, e)%Z.
Definition dsub (a b : Z * Z) : Z * Z :=
  let e := Z.min (snd a) (snd b) in (dal a e - dal b e, e)%Z.
Definition dmul (a b : Z * Z) : Z * Z := (fst a * fst b, snd a + snd b)%Z.
Definition dlt (a b : Z * Z) : bool :=
  let e := Z.min (snd a) (snd b) in Z.ltb (dal a e) (dal b e).

(* the exact value of a finite float, from its normalised mantissa and
   exponent: f = m * 2^(e - 2101 - 53) *)
Definition fex_raw (f : float) : Z * Z :=
  let (z, e) := frshiftexp f in
  let m := zofi (normfr_mantissa z) in
  ((if (f <? 0)%float then - m else m)%Z, (zofi e - 2154)%Z).

(* Zero needs no fine grid: an exponent of -2154 otherwise inflates every
   nonzero coordinate by roughly 2100 bits when an input coordinate is zero. *)
Definition fex (f : float) : Z * Z :=
  let '(m, e) := fex_raw f in
  if Z.eqb m 0 then (0, 0)%Z else (m, e).

(* the exact squared distance between points a and b *)
Definition dex (x y : array float) (a b : int) : Z * Z :=
  let dx := dsub (fex x.[a]) (fex x.[b]) in
  let dy := dsub (fex y.[a]) (fex y.[b]) in
  dadd (dmul dx dx) (dmul dy dy).

(* -- Floats. ---------------------------------------------------------- *)


(* -- The exact grid. ---------------------------------------------------- *)

(* the least exponent over all the coordinates (and 0) *)
Definition expo_step (x y : array float) (i : int) (E : Z) : Z :=
  Z.min E (Z.min (snd (fex x.[i])) (snd (fex y.[i]))).

(* the coordinates as integers on the grid 2^E: exact *)
Definition grid_step (x y : array float) (E : Z) (i : int) (st : array Z * array Z)
    : array Z * array Z :=
  ((fst st).[i <- dal (fex x.[i]) E], (snd st).[i <- dal (fex y.[i]) E]).

(* the exact squared distance between points a and b, in units of 2^(2E) *)
Definition Dz (GX GY : array Z) (a b : int) : Z :=
  let dx := (GX.[a] - GX.[b])%Z in
  let dy := (GY.[a] - GY.[b])%Z in
  (dx * dx + dy * dy)%Z.

(* -- Prim, dense. ---------------------------------------------------------- *)

Definition key_init (GX GY : array Z) (w : int) (K : array Z) : array Z :=
  K.[w <- Dz GX GY 0 w].

(* the vertex outside the tree (rank n) of least key; n if none *)
Definition amin_step (n : int) (rk : array int) (K : array Z) (w b : int) : int :=
  if rk.[w] =? n then
    if b =? n then w else if Z.ltb K.[w] K.[b] then w else b
  else b.

Lemma amin_step_projected n rk K w b :
  amin_step n rk K w b =
  if andb (rk.[w] =? n) (orb (b =? n) (Z.ltb K.[w] K.[b])) then w else b.
Proof.
  unfold amin_step. destruct (rk.[w] =? n), (b =? n), (Z.ltb K.[w] K.[b]); reflexivity.
Qed.

Definition relax_step (GX GY : array Z) (n : int) (rk : array int) (v : int) (w : int)
    (st : array Z * array int) : array Z * array int :=
  if rk.[w] =? n then
    let d := Dz GX GY v w in
    if Z.ltb d (fst st).[w] then ((fst st).[w <- d], (snd st).[w <- v]) else st
  else st.

(* step k: the vertex v of least key gets rank k, then the keys are relaxed *)
Definition prim_step (GX GY : array Z) (n : int) (k : int)
    (st : array int * array Z * array int) : array int * array Z * array int :=
  let rk := fst (fst st) in
  let v := loop n (fun _ _ => true) (amin_step n rk (snd (fst st))) 0 n in
  let rk' := rk.[v <- k] in
  let KP := loop n (fun _ _ => true) (relax_step GX GY n rk' v) 0 (snd (fst st), snd st) in
  (rk', fst KP, snd KP).

(* -- The preorder walk. ------------------------------------------------------ *)

(* state: per-vertex scan pointer, stack and its size, output and its size *)
Definition DS : Type := array int * array int * int * array int * int.

Definition ds_it (s : DS) : array int := fst (fst (fst (fst s))).
Definition ds_stk (s : DS) : array int := snd (fst (fst (fst s))).
Definition ds_sp (s : DS) : int := snd (fst (fst s)).
Definition ds_out (s : DS) : array int := snd (fst s).
Definition ds_cnt (s : DS) : int := snd s.

(* at the top u of the stack: scan the next vertex c; when c is a child of
   u, output it and push it; when u has been scanned to n, pop it *)
Definition dfs_step (n : int) (P : array int) (j : int) (s : DS) : DS :=
  let '((((it, stk), sp), out), cnt) := s in
  let u := stk.[sp - 1] in
  let c := it.[u] in
  if c <? n then
    let it' := it.[u <- c + 1] in
    if andb (P.[c] =? u) (negb (c =? 0)) then
      (it', stk.[sp <- c], sp + 1, out.[cnt <- c], cnt + 1)
    else (it', stk, sp, out, cnt)
  else (it, stk, sp - 1, out, cnt).

Definition tsp_impl (x y : array float) : array int :=
  let n := PArray.length x in
  let E := loop n (fun _ _ => true) (expo_step x y) 0 0%Z in
  let G := loop n (fun _ _ => true) (grid_step x y E) 0
             (PArray.make n 0%Z, PArray.make n 0%Z) in
  let GX := fst G in let GY := snd G in
  let K0 := loop n (fun _ _ => true) (key_init GX GY) 0 (PArray.make n 0%Z) in
  let rk0 := (PArray.make n n).[0 <- 0] in
  let PR := loop n (fun _ _ => true) (prim_step GX GY n) 1 (rk0, K0, PArray.make n 0) in
  let s := loop (n * n + n + 1) (fun _ s => 0 <? ds_sp s) (dfs_step n (snd PR)) 0
             (PArray.make n 0, PArray.make n 0, 1, PArray.make n 0, 1) in
  ds_out s.
(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) cont (f : int -> St -> St) i s H,
  wloop hi cont f i s H =
  match bdec (i <? hi) with
  | left Hi =>
      if cont i s then wloop hi cont f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
      else s
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma loop_inv : forall (P : int -> St -> Prop) (hi lo : int) cont f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> cont j t = true ->
     P (j + 1) (f j t)) ->
  exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (loop hi cont f lo s) /\
    (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (loop hi cont f lo s) = false)).
Proof.
  intros P hi lo cont f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t ->
     exists j, (to_Z lo <= to_Z j <= to_Z hi)%Z /\ P j (wloop hi cont f i t H) /\
       (to_Z j = to_Z hi \/ ((to_Z j < to_Z hi)%Z /\ cont j (wloop hi cont f i t H) = false))).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      destruct (cont i t) eqn:Ec.
      + apply (IH (gap hi (i + 1))).
        * rewrite <- En. apply dec_step; exact Hlt.
        * reflexivity.
        * pose proof (to_Z_bounded hi).
          assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
        * apply Hstep; auto; lia.
      + exists i. split; [lia |]. split; [exact Pt | right; split; [lia | exact Ec]].
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      exists i. split; [lia |]. split; [exact Pt | left; lia]. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi (fun _ _ => true) f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep.
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E | [_ E]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E. subst j. exact Pj.
  - discriminate.
Qed.

End LoopProof.

(* ------------------------------------------------------------------ *)
(* PArray plumbing, restated at [array int] (universe instances)       *)
(* ------------------------------------------------------------------ *)

Lemma iget_set_same : forall (t : array int) (i v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same int t i v H). Qed.

Lemma iget_set_other : forall (t : array int) (i j v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma ilength_set : forall (t : array int) (i v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set int t i v). Qed.

Lemma ilength_make : forall (n v : int),
  PArray.length (PArray.make n v) = if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make int n v). Qed.

Lemma ilength_bound : forall (t : array int), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma flength_bound : forall (t : array float), (to_Z (PArray.length t) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length float t) as H. rewrite Uint63.leb_spec in H.
  exact H.
Qed.

Lemma to_Z_of_Z_small : forall z, (0 <= z < wB)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_big : (4194304 < wB)%Z.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Exact arithmetic                                                    *)
(* ------------------------------------------------------------------ *)

Lemma zofi_spec : forall i, zofi i = to_Z i.
Proof. reflexivity. Qed.

Local Notation bp := (Raux.bpow Zaux.radix2).

Definition dval (d : Z * Z) : R := (IZR (fst d) * bp (snd d))%R.

Lemma fex_zero_normalization_value f :
  dval (fex f) = dval (fex_raw f).
Proof.
  unfold fex. destruct (fex_raw f) as [m e].
  destruct (Z.eqb m 0) eqn:E; [apply Z.eqb_eq in E; subst m | reflexivity].
  unfold dval; cbn [fst snd]. ring.
Qed.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bp k.
Proof. intros k Hk. destruct k as [| p | p]; [reflexivity | reflexivity | lia]. Qed.

Lemma dal_val : forall d e, (e <= snd d)%Z -> (IZR (dal d e) * bp e = dval d)%R.
Proof.
  intros d e He. unfold dal, dval. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite mult_IZR, IZR_pow2 by lia. rewrite Rmult_assoc, <- Raux.bpow_plus.
  f_equal. f_equal. lia.
Qed.

Lemma dval_dadd : forall a b, dval (dadd a b) = (dval a + dval b)%R.
Proof.
  intros a b. unfold dadd. cbv zeta.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  unfold dval; simpl. rewrite plus_IZR. ring.
Qed.

Lemma dval_dsub : forall a b, dval (dsub a b) = (dval a - dval b)%R.
Proof.
  intros a b. unfold dsub. cbv zeta.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  unfold dval; simpl. rewrite minus_IZR. ring.
Qed.

Lemma dval_dmul : forall a b, dval (dmul a b) = (dval a * dval b)%R.
Proof.
  intros a b. unfold dmul, dval; simpl. rewrite mult_IZR, Raux.bpow_plus. ring.
Qed.

Lemma dlt_iff : forall a b, dlt a b = true <-> (dval a < dval b)%R.
Proof.
  intros a b. unfold dlt. cbv zeta. rewrite Z.ltb_lt.
  rewrite <- (dal_val a (Z.min (snd a) (snd b))) by lia.
  rewrite <- (dal_val b (Z.min (snd a) (snd b))) by lia.
  pose proof (Raux.bpow_gt_0 Zaux.radix2 (Z.min (snd a) (snd b))).
  split; intros H'.
  - apply Rmult_lt_compat_r; [exact H | apply IZR_lt; exact H'].
  - apply lt_IZR. eapply Rmult_lt_reg_r; [exact H | exact H'].
Qed.

Lemma repr_zero : repr 0%float 0%R.
Proof. split; reflexivity. Qed.

Lemma fex_raw_val : forall (f : float) r, repr f r -> dval (fex_raw f) = r.
Proof.
  intros f r Hf.
  assert (Hs : (f <? 0)%float = Raux.Rlt_bool r 0) by (apply repr_ltb; [exact Hf | exact repr_zero]).
  pose proof Hf as Hf'. apply repr_float_iff in Hf' as [Fin Ev].
  unfold fex_raw. pose proof (Flocq.IEEE754.PrimFloat.frshiftexp_equiv f) as Fr.
  destruct (frshiftexp f) as [z e]. rewrite Hs. unfold dval; simpl fst; simpl snd.
  unfold zofi. rewrite Flocq.IEEE754.PrimFloat.normfr_mantissa_equiv.
  rewrite <- Ev. clear Hs Ev Hf. revert Fr Fin.
  destruct (Flocq.IEEE754.PrimFloat.Prim2B f) as [s|s| |s m ex Hb]; intros Fr Fin; try discriminate.
  - simpl in Fr. injection Fr as Ez _. rewrite Ez. simpl.
    destruct (Raux.Rlt_bool 0 0); simpl; ring.
  - pose proof (BinarySingleNaN.Bfrexp_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hprec (BinarySingleNaN.B754_finite s m ex Hb) eq_refl) as C.
    rewrite <- Fr in C. destruct C as [E1 C]. destruct (C eq_refl) as [Hz _]. clear C.
    pose proof (BinarySingleNaN.Bnormfr_mantissa_correct FloatOps.prec FloatOps.emax Flocq.IEEE754.PrimFloat.Hmax (Flocq.IEEE754.PrimFloat.Prim2B z) Hz) as Nm.
    destruct (Flocq.IEEE754.PrimFloat.Prim2B z) as [| | |s' m' e' Hb']; try contradiction.
    destruct Nm as [Nm [_ Ee]]. rewrite Nm. subst e'. rewrite E1. clear E1 Hz Fr Nm.
    cbn [BinarySingleNaN.B2R]. unfold Defs.F2R; simpl Defs.Fnum; simpl Defs.Fexp.
    change FloatOps.shift with 2101%Z.
    replace (to_Z e - 2154)%Z with (to_Z e - 2101 + -53)%Z by lia.
    rewrite Raux.bpow_plus.
    pose proof (Raux.bpow_gt_0 Zaux.radix2 (-53)). pose proof (Raux.bpow_gt_0 Zaux.radix2 (to_Z e - 2101)).
    destruct s'; simpl Zaux.cond_Zopp; simpl Z.of_N.
    + rewrite Raux.Rlt_bool_true; [rewrite opp_IZR; change (Zneg m') with (- Zpos m')%Z; rewrite opp_IZR; ring |].
      assert (0 < IZR (Zpos m'))%R by (apply IZR_lt; lia).
      change (Zneg m') with (- Zpos m')%Z; rewrite opp_IZR.
      assert (0 < IZR (Z.pos m') * bp (-53) * bp (to_Z e - 2101))%R
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
      nra.
    + rewrite Raux.Rlt_bool_false; [ring |].
      assert (0 < IZR (Zpos m'))%R by (apply IZR_lt; lia).
      assert (0 < IZR (Z.pos m') * bp (-53) * bp (to_Z e - 2101))%R
        by (apply Rmult_lt_0_compat; [apply Rmult_lt_0_compat|]; lra).
      lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Generic lemmas: sums, the triangle inequality, pigeonholes          *)
(* ------------------------------------------------------------------ *)

Lemma fex_val f r :
  repr f r -> dval (fex f) = r.
Proof. rewrite fex_zero_normalization_value. apply fex_raw_val. Qed.

Local Open Scope R_scope.

Lemma sum_below_S : forall f m, sum_below f (S m) = (sum_below f m + f m)%R.
Proof. reflexivity. Qed.

Lemma sum_below_ext : forall f g m, (forall k, (k < m)%nat -> f k = g k) ->
  sum_below f m = sum_below g m.
Proof.
  intros f g m. induction m as [| m IH]; intros H; simpl; [reflexivity |].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sum_below_le : forall f g m, (forall k, (k < m)%nat -> f k <= g k) ->
  sum_below f m <= sum_below g m.
Proof.
  intros f g m. induction m as [| m IH]; intros H; simpl; [lra |].
  pose proof (IH (fun k Hk => H k ltac:(lia))). pose proof (H m ltac:(lia)). lra.
Qed.

Lemma sum_below_nonneg : forall f m, (forall k, (k < m)%nat -> 0 <= f k) -> 0 <= sum_below f m.
Proof.
  intros f m H. apply Rle_trans with (sum_below (fun _ => 0) m).
  - clear H. induction m; simpl; lra.
  - apply sum_below_le. exact H.
Qed.

Lemma sum_below_update : forall f g m k0, (k0 < m)%nat ->
  (forall k, (k < m)%nat -> k <> k0 -> g k = f k) ->
  sum_below g m = sum_below f m - f k0 + g k0.
Proof.
  intros f g m. induction m as [| m IH]; intros k0 Hk H; [lia |]. simpl.
  destruct (Nat.eq_dec k0 m) as [E | E].
  - subst k0. rewrite (sum_below_ext g f m) by (intros; apply H; lia). ring.
  - rewrite (IH k0) by (try lia; intros; apply H; lia). rewrite (H m) by lia. ring.
Qed.

Definition rmf {A} (f : nat -> A) (q j : nat) : A := if (j <? q)%nat then f j else f (S j).

Lemma sum_below_rm : forall c M t, (t <= M)%nat ->
  sum_below c (S M) = sum_below (rmf c t) M + c t.
Proof.
  intros c M. induction M as [| M IH]; intros t Ht.
  - assert (t = 0%nat) by lia. subst t. simpl. ring.
  - destruct (Nat.eq_dec t (S M)) as [E | E].
    + subst t. change (sum_below c (S (S M))) with (sum_below c (S M) + c (S M)).
      f_equal. apply sum_below_ext. intros k Hk. unfold rmf.
      destruct (Nat.ltb_spec k (S M)); [reflexivity | lia].
    + change (sum_below c (S (S M))) with (sum_below c (S M) + c (S M)).
      rewrite (IH t) by lia.
      change (sum_below (rmf c t) (S M)) with (sum_below (rmf c t) M + rmf c t M).
      assert (E' : rmf c t M = c (S M)) by (unfold rmf; destruct (Nat.ltb_spec M t); [lia | reflexivity]).
      rewrite E'. ring.
Qed.

Lemma triangle : forall p q r s : R,
  sqrt ((p + r) * (p + r) + (q + s) * (q + s)) <=
  sqrt (p * p + q * q) + sqrt (r * r + s * s).
Proof.
  intros p q r s.
  pose proof (sqrt_cauchy p q r s) as C. unfold Rsqr in C.
  pose proof (sqrt_pos (p * p + q * q)). pose proof (sqrt_pos (r * r + s * s)).
  assert (P1 : sqrt (p * p + q * q) * sqrt (p * p + q * q) = p * p + q * q)
    by (apply sqrt_sqrt; nra).
  assert (P2 : sqrt (r * r + s * s) * sqrt (r * r + s * s) = r * r + s * s)
    by (apply sqrt_sqrt; nra).
  rewrite <- (sqrt_square (sqrt (p * p + q * q) + sqrt (r * r + s * s))) by lra.
  apply sqrt_le_1_alt. nra.
Qed.

Local Close Scope R_scope.

Lemma seq_NoDup_map : forall {A} (o : nat -> A) m,
  (forall i j, (i < m)%nat -> (j < m)%nat -> o i = o j -> i = j) ->
  NoDup (map o (seq 0 m)).
Proof.
  intros A o m H. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros a b Ha Hb E. apply in_seq in Ha, Hb. apply H; [lia | lia | exact E].
Qed.

(* an injection of [0, m) into [0, k) : m <= k *)
Lemma pigeon_le : forall (o : nat -> nat) m k,
  (forall i, (i < m)%nat -> (o i < k)%nat) ->
  (forall i j, (i < m)%nat -> (j < m)%nat -> o i = o j -> i = j) -> (m <= k)%nat.
Proof.
  intros o m k Hr Hi.
  assert (L : (List.length (map o (seq 0 m)) <= List.length (seq 0 k))%nat).
  2: rewrite length_map, !length_seq in L; exact L.
  apply NoDup_incl_length; [apply seq_NoDup_map; exact Hi |].
  intros y Hy. apply in_map_iff in Hy as (i & <- & Hi'). apply in_seq in Hi'.
  apply in_seq. pose proof (Hr i ltac:(lia)). lia.
Qed.

(* an injection of [0, m) into itself is onto *)
Lemma pigeon_surj : forall (o : nat -> nat) m,
  (forall i, (i < m)%nat -> (o i < m)%nat) ->
  (forall i j, (i < m)%nat -> (j < m)%nat -> o i = o j -> i = j) ->
  forall y, (y < m)%nat -> exists i, (i < m)%nat /\ o i = y.
Proof.
  intros o m Hr Hi y Hy.
  assert (Inc : incl (seq 0 m) (map o (seq 0 m))).
  { apply NoDup_length_incl; [apply seq_NoDup_map; exact Hi | rewrite length_map; lia |].
    intros z Hz. apply in_map_iff in Hz as (i & <- & Hi'). apply in_seq in Hi'.
    apply in_seq. pose proof (Hr i ltac:(lia)). lia. }
  assert (In y (seq 0 m)) by (apply in_seq; lia).
  apply Inc in H. apply in_map_iff in H as (i & E & Hi'). apply in_seq in Hi'.
  exists i. split; [lia | exact E].
Qed.

Local Open Scope nat_scope.

(* The Prim-versus-path lemma.  A path p_0 .. p_{m-1} whose vertices carry
   the distinct ranks o_0 .. o_{m-1} (a permutation of [0, m)); its edge j,
   of weight c j, joins ranks o_j and o_{j+1}, so it crosses every cut
   {rank < k} for min < k <= max.  If the step weight w k is at most the
   weight of every edge crossing the cut {rank < k} (Prim's cut property),
   then w 1 + ... + w (m-1) <= c 0 + ... + c (m-2).  Induction on m: the
   vertex of rank m-1 is removed, one of its (at most two) path edges pays
   for w (m-1), the other one stands for the merged edge. *)
Lemma path_bound : forall m (o : nat -> nat) (c w : nat -> R),
  (forall i, (i < m)%nat -> (o i < m)%nat) ->
  (forall i j, (i < m)%nat -> (j < m)%nat -> o i = o j -> i = j) ->
  (forall j k, (S j < m)%nat -> (Nat.min (o j) (o (S j)) < k)%nat ->
     (k <= Nat.max (o j) (o (S j)))%nat -> (w k <= c j)%R) ->
  (sum_below (fun k => w (S k)) (m - 1) <= sum_below c (m - 1))%R.
Proof.
  induction m as [| m IH]; intros o c w Hr Hi Hc; [simpl; lra |].
  destruct (Nat.eq_dec m 0) as [Z0 | NZ]; [subst m; simpl; lra |].
  destruct (pigeon_surj o (S m) Hr Hi m ltac:(lia)) as (q & Hq & Oq).
  assert (Lt : forall i, (i < S m)%nat -> i <> q -> (o i < m)%nat).
  { intros i Hi' Ne. pose proof (Hr i Hi'). destruct (Nat.eq_dec (o i) m) as [E | E]; [| lia].
    exfalso. apply Ne. apply Hi; [lia | lia | congruence]. }
  set (t := if (q =? 0)%nat then 0%nat else if (q =? m)%nat then (q - 1)%nat
            else if (o (q - 1) <? o (S q))%nat then q else (q - 1)%nat).
  assert (Ht : (t = q /\ q < m \/ t = q - 1 /\ 1 <= q)%nat).
  { unfold t. destruct (Nat.eqb_spec q 0); [left; lia |].
    destruct (Nat.eqb_spec q m); [right; lia |].
    destruct (Nat.ltb_spec (o (q - 1)) (o (S q))); [left | right]; lia. }
  replace (S m - 1)%nat with (S (m - 1)) by lia.
  rewrite (sum_below_rm c (m - 1) t) by lia. simpl sum_below at 1.
  replace (S (m - 1)) with m by lia.
  assert (Wm : (w m <= c t)%R).
  { apply Hc; [lia | |].
    - destruct Ht as [[-> Hq1] | [-> Hq1]].
      + pose proof (Lt (S q) ltac:(lia) ltac:(lia)). lia.
      + replace (S (q - 1)) with q by lia. pose proof (Lt (q - 1)%nat ltac:(lia) ltac:(lia)). lia.
    - destruct Ht as [[-> Hq1] | [-> Hq1]]; [lia |]. replace (S (q - 1)) with q by lia. lia. }
  assert (IHm : (sum_below (fun k => w (S k)) (m - 1) <= sum_below (rmf c t) (m - 1))%R).
  { apply (IH (rmf o q)).
    - intros i Hi'. unfold rmf. destruct (Nat.ltb_spec i q).
      + apply Lt; lia.
      + apply Lt; lia.
    - intros i j Hi' Hj' E. unfold rmf in E.
      destruct (Nat.ltb_spec i q), (Nat.ltb_spec j q);
        apply Hi in E; lia.
    - intros j k Hj Hk1 Hk2. unfold rmf in *.
      destruct (Nat.ltb_spec j q) as [Jq | Jq]; destruct (Nat.ltb_spec (S j) q) as [Sq | Sq].
      + (* the edge j, untouched *)
        destruct (Nat.ltb_spec j t); [| lia]. apply Hc; lia.
      + (* the merged edge: S j = q *)
        assert (Eq : S j = q) by lia. subst q.
        pose proof (Lt j ltac:(lia) ltac:(lia)) as L1.
        pose proof (Lt (S (S j)) ltac:(lia) ltac:(lia)) as L2.
        assert (Tq : t = (if (o j <? o (S (S j)))%nat then S j else j)).
        { unfold t. destruct (Nat.eqb_spec (S j) 0); [lia |].
          destruct (Nat.eqb_spec (S j) m); [lia |]. replace (S j - 1)%nat with j by lia. reflexivity. }
        rewrite Tq in *. destruct (Nat.ltb_spec (o j) (o (S (S j)))).
        * destruct (Nat.ltb_spec j (S j)); [| lia]. apply Hc; lia.
        * destruct (Nat.ltb_spec j j); [lia |]. apply Hc; lia.
      + lia.
      + (* the edge S j, shifted *)
        destruct (Nat.ltb_spec j t); [destruct Ht; lia |]. apply Hc; lia. }
  lra.
Qed.

Local Close Scope nat_scope.

(* ------------------------------------------------------------------ *)
(* The exact distance: symmetry, triangle inequality                  *)
(* ------------------------------------------------------------------ *)

Lemma dist_sym : forall xs ys i j, dist xs ys i j = dist xs ys j i.
Proof. intros. unfold dist. f_equal. ring. Qed.

Lemma dist_self : forall xs ys i, dist xs ys i i = 0%R.
Proof.
  intros. unfold dist. replace ((_ - _) * (_ - _) + (_ - _) * (_ - _))%R with 0%R by ring.
  apply sqrt_0.
Qed.

Lemma dist_nonneg : forall xs ys i j, (0 <= dist xs ys i j)%R.
Proof. intros. apply sqrt_pos. Qed.

Lemma dist_tri : forall xs ys i j k, (dist xs ys i k <= dist xs ys i j + dist xs ys j k)%R.
Proof.
  intros. unfold dist. cbv zeta.
  set (a := get_list_R xs i). set (b := get_list_R xs j). set (c := get_list_R xs k).
  set (a' := get_list_R ys i). set (b' := get_list_R ys j). set (c' := get_list_R ys k).
  replace (a - c)%R with ((a - b) + (b - c))%R by ring.
  replace (a' - c')%R with ((a' - b') + (b' - c'))%R by ring.
  apply triangle.
Qed.

(* ------------------------------------------------------------------ *)
(* PArray plumbing at [array Z]                                        *)
(* ------------------------------------------------------------------ *)

Lemma zget_set_same : forall (t : array Z) (i : int) (v : Z),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (get_set_same Z t i v H). Qed.

Lemma zget_set_other : forall (t : array Z) (i j : int) (v : Z),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other Z t i j v H). Qed.

Lemma zlength_set : forall (t : array Z) (i : int) (v : Z),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (length_set Z t i v). Qed.

Lemma zlength_make : forall (n : int) (v : Z),
  PArray.length (PArray.make n v) = if n <=? max_length then n else max_length.
Proof. intros n v. exact (length_make Z n v). Qed.

Lemma iget_make : forall (m i v : int), (PArray.make m v : array int).[i] = v.
Proof. intros m i v. exact (get_make int v m i). Qed.

Lemma zget_make : forall (m i : int) (v : Z), (PArray.make m v : array Z).[i] = v.
Proof. intros m i v. exact (get_make Z v m i). Qed.

(* the first i < m with f i, or m *)
Fixpoint fnd (f : nat -> bool) (m : nat) : nat :=
  match m with
  | O => O
  | S m' => let r := fnd f m' in if (r <? m')%nat then r else if f m' then m' else S m'
  end.

Lemma fnd_true : forall f m, (fnd f m < m)%nat -> f (fnd f m) = true.
Proof.
  intros f m. induction m as [| m IH]; intros H; simpl in *; [lia |].
  destruct (Nat.ltb_spec (fnd f m) m) as [L | L]; [exact (IH L) |].
  destruct (f m) eqn:Fm; [exact Fm | lia].
Qed.

Lemma fnd_lt : forall f m, (exists i, (i < m)%nat /\ f i = true) -> (fnd f m < m)%nat.
Proof.
  intros f m. induction m as [| m IH]; intros (i & Hi & Fi); [lia |]. simpl.
  destruct (Nat.ltb_spec (fnd f m) m) as [L | L]; [lia |].
  destruct (f m) eqn:Fm; [lia |].
  destruct (Nat.eq_dec i m) as [-> | Ne]; [congruence |].
  assert (fnd f m < m)%nat by (apply IH; exists i; split; [lia | exact Fi]). lia.
Qed.

(* ================================================================== *)
(* The main proof                                                      *)
(* ================================================================== *)

Section Main.
Variables (xs ys : list R) (x y : array float).
Hypothesis Hv : valid_input xs ys.
Hypothesis Hx : repr x xs.
Hypothesis Hy : repr y ys.

Local Notation nx := (PArray.length x).
Local Notation bp := (Raux.bpow Zaux.radix2).

Definition X (a : int) : R := nth (Z.to_nat (to_Z a)) xs 0%R.
Definition Y (a : int) : R := nth (Z.to_nat (to_Z a)) ys 0%R.
Definition V (a : int) : Prop := (to_Z a < to_Z nx)%Z.

Lemma len_x : Z.of_nat (List.length xs) = to_Z nx.
Proof. exact (proj1 Hx). Qed.

Lemma len_y : Z.of_nat (List.length ys) = to_Z nx.
Proof.
  rewrite <- len_x. pose proof (vi_ys _ _ Hv) as E. unfold len in E. lia.
Qed.

Lemma n_bounds : (1 <= to_Z nx <= 1000)%Z.
Proof. rewrite <- len_x. pose proof (vi_n _ _ Hv) as E. unfold len in E. lia. Qed.

Lemma repr_nth : forall (l : list R) (t : array float) (a : int), repr t l ->
  (to_Z a < Z.of_nat (List.length l))%Z -> repr t.[a] (nth (Z.to_nat (to_Z a)) l 0%R).
Proof.
  intros l t a [_ H] Ha. destruct (H (Z.to_nat (to_Z a)) ltac:(lia)) as (m & E & R).
  rewrite (nth_error_nth _ _ _ E). rewrite Z2Nat.id in R by (pose proof (to_Z_bounded a); lia).
  rewrite of_to_Z in R. exact R.
Qed.

Lemma repr_X : forall a, V a -> repr x.[a] (X a).
Proof. intros a Ha. unfold X. refine (repr_nth xs x a Hx _). rewrite len_x; exact Ha. Qed.

Lemma repr_Y : forall a, V a -> repr y.[a] (Y a).
Proof. intros a Ha. unfold Y. refine (repr_nth ys y a Hy _). rewrite len_y; exact Ha. Qed.

Lemma V0 : V 0.
Proof. unfold V. pose proof n_bounds. change (to_Z 0) with 0%Z. lia. Qed.

Lemma succ_V : forall j : int, (to_Z j < to_Z nx)%Z -> to_Z (j + 1) = (to_Z j + 1)%Z.
Proof. intros j H. pose proof n_bounds. pose proof (to_Z_bounded j). sia. Qed.

Lemma ilength_make_n : forall v : int, PArray.length (PArray.make nx v) = nx.
Proof.
  intros v. rewrite ilength_make. pose proof n_bounds as H.
  replace (nx <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec. change (to_Z max_length) with 4194303%Z. lia.
Qed.

Lemma zlength_make_n : forall v : Z, PArray.length (PArray.make nx v) = nx.
Proof.
  intros v. rewrite zlength_make. pose proof n_bounds as H.
  replace (nx <=? max_length) with true; [reflexivity |].
  symmetry. rewrite Uint63.leb_spec. change (to_Z max_length) with 4194303%Z. lia.
Qed.

Lemma ltb_V : forall (a : int) (L : int), L = nx -> V a -> (a <? L) = true.
Proof. intros a L -> H. rewrite Uint63.ltb_spec. exact H. Qed.

(* -- The grid. -- *)

Definition E : Z := loop nx (fun _ _ => true) (expo_step x y) 0 0%Z.

Lemma E_le : forall a, V a -> (E <= snd (fex x.[a]))%Z /\ (E <= snd (fex y.[a]))%Z.
Proof.
  pose proof n_bounds.
  assert (G := for_inv (fun i e => forall a, (to_Z a < to_Z i)%Z ->
     (e <= snd (fex x.[a]))%Z /\ (e <= snd (fex y.[a]))%Z) nx 0 (expo_step x y) 0%Z).
  intros a Ha. unfold E. refine (G _ _ _ a Ha); [change (to_Z 0) with 0%Z; lia | |].
  - intros a' Ha'. change (to_Z 0) with 0%Z in Ha'. pose proof (to_Z_bounded a'). lia.
  - intros j e Hj Pe a' Ha'. rewrite succ_V in Ha' by lia. unfold expo_step.
    destruct (Z.eq_dec (to_Z a') (to_Z j)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst a'. lia.
    + destruct (Pe a' ltac:(lia)). lia.
Qed.

Definition GR : array Z * array Z :=
  loop nx (fun _ _ => true) (grid_step x y E) 0 (PArray.make nx 0%Z, PArray.make nx 0%Z).
Definition GX : array Z := fst GR.
Definition GY : array Z := snd GR.

Lemma grid_spec : PArray.length GX = nx /\ PArray.length GY = nx /\
  forall a, V a -> GX.[a] = dal (fex x.[a]) E /\ GY.[a] = dal (fex y.[a]) E.
Proof.
  pose proof n_bounds.
  assert (G := for_inv (fun i (st : array Z * array Z) =>
     PArray.length (fst st) = nx /\ PArray.length (snd st) = nx /\
     forall a, (to_Z a < to_Z i)%Z ->
       (fst st).[a] = dal (fex x.[a]) E /\ (snd st).[a] = dal (fex y.[a]) E)
     nx 0 (grid_step x y E) (PArray.make nx 0%Z, PArray.make nx 0%Z)).
  destruct G as (G1 & G2 & G3).
  - change (to_Z 0) with 0%Z; lia.
  - simpl. rewrite !zlength_make_n. split; [reflexivity | split; [reflexivity |]].
    intros a' Ha'. change (to_Z 0) with 0%Z in Ha'. pose proof (to_Z_bounded a'). lia.
  - intros j [GX0 GY0] Hj (L1 & L2 & P). simpl in *. unfold grid_step; simpl.
    rewrite !zlength_set. split; [exact L1 | split; [exact L2 |]].
    intros a' Ha'. rewrite succ_V in Ha' by lia.
    destruct (Z.eq_dec (to_Z a') (to_Z j)) as [Ej | Ej].
    + apply to_Z_inj in Ej. subst a'.
      rewrite !zget_set_same by (rewrite Uint63.ltb_spec; lia). split; reflexivity.
    + assert (a' <> j) by (intros ->; lia).
      rewrite !zget_set_other by congruence. apply P. lia.
  - unfold GX, GY, GR. split; [exact G1 | split; [exact G2 | exact G3]].
Qed.

Lemma GX_val : forall a, V a -> (IZR GX.[a] * bp E = X a)%R.
Proof.
  intros a Ha. destruct grid_spec as (_ & _ & G). rewrite (proj1 (G a Ha)).
  rewrite dal_val by (apply E_le; exact Ha). apply fex_val, repr_X, Ha.
Qed.

Lemma GY_val : forall a, V a -> (IZR GY.[a] * bp E = Y a)%R.
Proof.
  intros a Ha. destruct grid_spec as (_ & _ & G). rewrite (proj2 (G a Ha)).
  rewrite dal_val by (apply E_le; exact Ha). apply fex_val, repr_Y, Ha.
Qed.

Definition D (a b : int) : Z := Dz GX GY a b.

Lemma D_sym : forall a b, D a b = D b a.
Proof. intros. unfold D, Dz. ring. Qed.

Definition di (a b : int) : R := dist xs ys (Z.to_N (to_Z a)) (Z.to_N (to_Z b)).

Lemma di_D : forall a b, V a -> V b -> di a b = sqrt (IZR (D a b) * (bp E * bp E)).
Proof.
  intros a b Ha Hb. unfold di, dist, get_list_R, D, Dz. cbv zeta. f_equal.
  rewrite !Z_N_nat. fold (X a) (X b) (Y a) (Y b).
  rewrite <- (GX_val a Ha), <- (GX_val b Hb), <- (GY_val a Ha), <- (GY_val b Hb).
  rewrite plus_IZR, !mult_IZR, !minus_IZR. ring.
Qed.

Lemma di_mono : forall a b c d, V a -> V b -> V c -> V d -> (D a b <= D c d)%Z ->
  (di a b <= di c d)%R.
Proof.
  intros a b c d Ha Hb Hc Hd H. rewrite !di_D by assumption.
  apply sqrt_le_1_alt. apply Rmult_le_compat_r.
  - pose proof (Raux.bpow_gt_0 Zaux.radix2 E). nra.
  - apply IZR_le. exact H.
Qed.

Lemma di_sym : forall a b, di a b = di b a.
Proof. intros. unfold di. apply dist_sym. Qed.

Lemma di_self : forall a, di a a = 0%R.
Proof. intros. unfold di. apply dist_self. Qed.

Lemma di_tri : forall a b c, (di a c <= di a b + di b c)%R.
Proof. intros. unfold di. apply dist_tri. Qed.

Lemma di_nonneg : forall a b, (0 <= di a b)%R.
Proof. intros. unfold di. apply dist_nonneg. Qed.


(* -- nat <-> int, for the pigeonholes -- *)

Definition ofn (v : nat) : int := of_Z (Z.of_nat v).

Lemma ofn_spec : forall v, (Z.of_nat v < 4194304)%Z -> to_Z (ofn v) = Z.of_nat v.
Proof. intros v H. unfold ofn. apply to_Z_of_Z_small. pose proof wB_big. lia. Qed.

Lemma ofn_V : forall a, V a -> ofn (Z.to_nat (to_Z a)) = a.
Proof.
  intros a Ha. unfold V in Ha. pose proof n_bounds. pose proof (to_Z_bounded a).
  apply to_Z_inj. rewrite ofn_spec by lia. lia.
Qed.

Lemma V_ofn : forall v, (Z.of_nat v < to_Z nx)%Z -> V (ofn v).
Proof. intros v H. pose proof n_bounds. unfold V. rewrite ofn_spec by lia. exact H. Qed.

Definition NX : nat := Z.to_nat (to_Z nx).

(* -- Prim: the invariant at step k (ranks 0 .. k-1 given) -- *)

Definition PI (k : int) (st : array int * array Z * array int) : Prop :=
  let rk := fst (fst st) in let K := snd (fst st) in let P := snd st in
  PArray.length rk = nx /\ PArray.length K = nx /\ PArray.length P = nx /\
  (to_Z k <= to_Z nx)%Z /\
  (forall w, V w -> (to_Z rk.[w] < to_Z k)%Z \/ rk.[w] = nx) /\
  (forall w w', V w -> V w' -> rk.[w] = rk.[w'] -> (to_Z rk.[w] < to_Z k)%Z -> w = w') /\
  (forall i, (to_Z i < to_Z k)%Z -> exists w, V w /\ rk.[w] = i) /\
  rk.[0] = 0 /\
  (forall w, V w -> rk.[w] = nx ->
     V P.[w] /\ (to_Z rk.[P.[w]] < to_Z k)%Z /\ K.[w] = D P.[w] w /\
     forall a, V a -> (to_Z rk.[a] < to_Z k)%Z -> (K.[w] <= D a w)%Z) /\
  (forall w, V w -> (1 <= to_Z rk.[w] < to_Z k)%Z ->
     V P.[w] /\ (to_Z rk.[P.[w]] < to_Z rk.[w])%Z /\
     forall a b, V a -> V b -> (to_Z rk.[a] < to_Z rk.[w] <= to_Z rk.[b])%Z ->
       (D w P.[w] <= D a b)%Z).

Lemma nonmember_exists : forall k st, PI k st -> (to_Z k < to_Z nx)%Z ->
  exists w, V w /\ (fst (fst st)).[w] = nx.
Proof.
  intros k st HP Hk. destruct st as [[rk K] P]. unfold PI in HP; simpl in *.
  destruct HP as (L1 & _ & _ & _ & I1 & I2 & _).
  pose proof n_bounds.
  set (f := fun v : nat => (rk.[ofn v] =? nx)).
  destruct (Nat.ltb_spec (fnd f NX) NX) as [Lt | Ge].
  - exists (ofn (fnd f NX)). split; [apply V_ofn; unfold NX in *; lia |].
    apply Uint63.eqb_spec. exact (fnd_true f NX Lt).
  - exfalso.
    assert (Al : forall v, (v < NX)%nat -> (to_Z rk.[ofn v] < to_Z k)%Z).
    { intros v Hv'. assert (Vv : V (ofn v)) by (apply V_ofn; unfold NX in Hv'; lia).
      destruct (I1 _ Vv) as [Hl | He]; [exact Hl |].
      assert (fnd f NX < NX)%nat; [| lia].
      apply fnd_lt. exists v. split; [exact Hv' |]. unfold f. apply Uint63.eqb_spec. exact He. }
    assert (NX <= Z.to_nat (to_Z k))%nat; [| unfold NX in *; lia].
    apply (pigeon_le (fun v => Z.to_nat (to_Z rk.[ofn v]))).
    + intros i Hi. pose proof (Al i Hi). pose proof (to_Z_bounded rk.[ofn i]). lia.
    + intros i j Hi Hj E'.
      assert (Vi : V (ofn i)) by (apply V_ofn; unfold NX in Hi; lia).
      assert (Vj : V (ofn j)) by (apply V_ofn; unfold NX in Hj; lia).
      pose proof (Al i Hi). pose proof (to_Z_bounded rk.[ofn i]). pose proof (to_Z_bounded rk.[ofn j]).
      assert (E2 : rk.[ofn i] = rk.[ofn j]) by (apply to_Z_inj; lia).
      pose proof (I2 _ _ Vi Vj E2 ltac:(lia)) as E3. apply (f_equal to_Z) in E3.
      rewrite !ofn_spec in E3 by (unfold NX in *; lia). lia.
Qed.

Lemma amin_spec : forall k st, PI k st -> (to_Z k < to_Z nx)%Z ->
  let rk := fst (fst st) in let K := snd (fst st) in
  let v := loop nx (fun _ _ => true) (amin_step nx rk K) 0 nx in
  V v /\ rk.[v] = nx /\ forall w, V w -> rk.[w] = nx -> (K.[v] <= K.[w])%Z.
Proof.
  intros k st HP Hk rk K. cbv zeta.
  destruct (nonmember_exists k st HP Hk) as (w0 & Vw0 & Ew0). fold rk in Ew0.
  pose proof n_bounds.
  assert (G := for_inv (fun i b =>
     (b = nx /\ forall w, (to_Z w < to_Z i)%Z -> rk.[w] <> nx) \/
     (V b /\ rk.[b] = nx /\ forall w, (to_Z w < to_Z i)%Z -> rk.[w] = nx -> (K.[b] <= K.[w])%Z))
     nx 0 (amin_step nx rk K) nx).
  destruct G as [[_ G] | G].
  - change (to_Z 0) with 0%Z; lia.
  - left. split; [reflexivity |]. intros w Hw. change (to_Z 0) with 0%Z in Hw.
    pose proof (to_Z_bounded w). lia.
  - intros j b Hj Pb. rewrite amin_step_projected.
    rewrite (succ_V j) by lia.
    destruct (rk.[j] =? nx) eqn:Rj0; simpl andb;
      [assert (Rj : rk.[j] = nx) by (apply Uint63.eqb_spec; exact Rj0)
      | assert (Rj : rk.[j] <> nx) by (apply Uint63.eqb_false_spec; exact Rj0)].
    + destruct Pb as [[Eb Pb] | (Vb & Rb & Pb)].
      * subst b. rewrite Uint63.eqb_refl. simpl. right.
        split; [unfold V; lia |]. split; [exact Rj |].
        intros w Hw Rw. destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
        -- apply to_Z_inj in Ew. subst w. lia.
        -- exfalso. exact (Pb w ltac:(lia) Rw).
      * assert (Bn : (b =? nx) = false) by (apply Uint63.eqb_false_spec; intros ->; unfold V in Vb; lia).
        rewrite Bn. simpl orb. destruct (Z.ltb_spec K.[j] K.[b]) as [Lt | Ge].
        -- right. split; [unfold V; lia |]. split; [exact Rj |].
           intros w Hw Rw. destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
           ++ apply to_Z_inj in Ew. subst w. lia.
           ++ pose proof (Pb w ltac:(lia) Rw). lia.
        -- right. split; [exact Vb |]. split; [exact Rb |].
           intros w Hw Rw. destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
           ++ apply to_Z_inj in Ew. subst w. lia.
           ++ apply Pb; [lia | exact Rw].
    + destruct Pb as [[Eb Pb] | (Vb & Rb & Pb)]; [left | right].
      * split; [exact Eb |]. intros w Hw. destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
        -- apply to_Z_inj in Ew. subst w. exact Rj.
        -- apply Pb. lia.
      * split; [exact Vb |]. split; [exact Rb |]. intros w Hw Rw.
        destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
        -- apply to_Z_inj in Ew. subst w. contradiction.
        -- apply Pb; [lia | exact Rw].
  - exfalso. exact (G w0 Vw0 Ew0).
  - destruct G as (G1 & G2 & G3). split; [exact G1 | split; [exact G2 |]].
    intros w Hw. apply G3. exact Hw.
Qed.


Definition rcond (rk' : array int) (K : array Z) (v w : int) : bool :=
  andb (rk'.[w] =? nx) (Z.ltb (D v w) K.[w]).

Lemma relax_spec : forall (rk' : array int) (K : array Z) (P : array int) (v : int),
  PArray.length K = nx -> PArray.length P = nx ->
  let KP := loop nx (fun _ _ => true) (relax_step GX GY nx rk' v) 0 (K, P) in
  PArray.length (fst KP) = nx /\ PArray.length (snd KP) = nx /\ forall w, V w ->
    (fst KP).[w] = (if rcond rk' K v w then D v w else K.[w]) /\
    (snd KP).[w] = (if rcond rk' K v w then v else P.[w]).
Proof.
  intros rk' K P v LK LP. cbv zeta. pose proof n_bounds.
  assert (G := for_inv (fun i (st : array Z * array int) =>
     PArray.length (fst st) = nx /\ PArray.length (snd st) = nx /\ forall w, V w ->
     ((to_Z w < to_Z i)%Z ->
        (fst st).[w] = (if rcond rk' K v w then D v w else K.[w]) /\
        (snd st).[w] = (if rcond rk' K v w then v else P.[w])) /\
     ((to_Z i <= to_Z w)%Z -> (fst st).[w] = K.[w] /\ (snd st).[w] = P.[w]))
     nx 0 (relax_step GX GY nx rk' v) (K, P)).
  destruct G as (G1 & G2 & G3).
  - change (to_Z 0) with 0%Z; lia.
  - simpl. split; [exact LK | split; [exact LP |]]. intros w Hw. split; [| auto].
    intros Hw'. change (to_Z 0) with 0%Z in Hw'. pose proof (to_Z_bounded w). lia.
  - intros j [K1 P1] Hj (L1 & L2 & Q). simpl fst in *; simpl snd in *.
    assert (Vj : V j) by (unfold V; lia).
    destruct (Q j Vj) as [_ Qj]. destruct (Qj ltac:(lia)) as [Kj Pj].
    unfold relax_step. simpl fst; simpl snd. fold (D v j). rewrite Kj.
    assert (Hc : forall w, V w -> w <> j -> (to_Z w < to_Z (j + 1))%Z -> (to_Z w < to_Z j)%Z)
      by (intros w _ Ne Hw; rewrite succ_V in Hw by lia; assert (to_Z w <> to_Z j) by (intros E'; apply Ne, to_Z_inj, E'); lia).
    assert (Hd : forall w, (to_Z (j + 1) <= to_Z w)%Z -> (to_Z j <= to_Z w)%Z)
      by (intros w Hw; rewrite succ_V in Hw by lia; lia).
    destruct (rcond rk' K v j) eqn:Rc.
    + unfold rcond in Rc. apply andb_prop in Rc as [R1 R2]. rewrite R1, R2. simpl.
      rewrite zlength_set, ilength_set. split; [exact L1 | split; [exact L2 |]].
      intros w Hw. destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
      * apply to_Z_inj in Ew. subst w.
        rewrite zget_set_same by (apply ltb_V; [exact L1 | exact Vj]).
        rewrite iget_set_same by (apply ltb_V; [exact L2 | exact Vj]).
        unfold rcond. rewrite R1, R2. split; [auto | intros; lia].
      * assert (w <> j) by (intros ->; lia).
        rewrite zget_set_other, iget_set_other by congruence.
        destruct (Q w Hw) as [Q1 Q2]. split; [intros Hw'; apply Q1; apply Hc; auto | intros Hw'; apply Q2; apply Hd; exact Hw'].
    + assert (St : (if rk'.[j] =? nx then if (D v j <? K.[j])%Z then (K1.[j <- D v j], P1.[j <- v]) else (K1, P1) else (K1, P1)) = (K1, P1)).
      { unfold rcond in Rc. destruct (rk'.[j] =? nx); [simpl in Rc; rewrite Rc |]; reflexivity. }
      rewrite St. simpl. split; [exact L1 | split; [exact L2 |]].
      intros w Hw. destruct (Q w Hw) as [Q1 Q2].
      destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
      * apply to_Z_inj in Ew. subst w. rewrite Rc. split; [intros; split; assumption | intros; lia].
      * split; [intros Hw'; apply Q1; apply Hc; auto; intros ->; lia | intros Hw'; apply Q2; apply Hd; exact Hw'].
  - split; [exact G1 | split; [exact G2 |]]. intros w Hw. apply (G3 w Hw). exact Hw.
Qed.


Lemma prim_step_spec : forall k st, PI k st -> (1 <= to_Z k < to_Z nx)%Z ->
  PI (k + 1) (prim_step GX GY nx k st).
Proof.
  intros k [[rk K] P] HP Hk.
  pose proof (amin_spec k _ HP (proj2 Hk)) as AM. cbv zeta in AM. simpl fst in AM; simpl snd in AM.
  set (v := loop nx (fun _ _ => true) (amin_step nx rk K) 0 nx) in AM.
  destruct AM as (Vv & Rv & Mv).
  unfold PI in HP; simpl fst in HP; simpl snd in HP.
  destruct HP as (L1 & L2 & L3 & Lk & I1 & I2 & I3 & I4 & I5 & I6).
  pose proof n_bounds.
  unfold prim_step. simpl fst; simpl snd. fold v.
  set (rk' := rk.[v <- k]).
  pose proof (relax_spec rk' K P v L2 L3) as RX. cbv zeta in RX.
  set (KP := loop nx (fun _ _ => true) (relax_step GX GY nx rk' v) 0 (K, P)) in *.
  destruct RX as (RL1 & RL2 & RX).
  assert (Rk1 : rk'.[v] = k) by (apply iget_set_same; apply ltb_V; auto).
  assert (Rk2 : forall w, w <> v -> rk'.[w] = rk.[w]) by (intros; apply iget_set_other; congruence).
  assert (Sk : to_Z (k + 1) = (to_Z k + 1)%Z) by (apply succ_V; lia).
  assert (Knx : to_Z k <> to_Z nx) by lia.
  assert (Mem : forall w, V w -> (to_Z rk.[w] < to_Z (k + 1))%Z -> (to_Z rk.[w] < to_Z k)%Z).
  { intros w Hw Hr. rewrite Sk in Hr. destruct (I1 w Hw) as [Hl | He]; [exact Hl | rewrite He in Hr; lia]. }
  assert (Nv : forall w, V w -> (to_Z rk.[w] < to_Z k)%Z -> w <> v).
  { intros w Hw Hr ->. rewrite Rv in Hr. lia. }
  assert (Rc : forall w, V w -> rcond rk' K v w = andb (rk'.[w] =? nx) (Z.ltb (D v w) K.[w]))
    by reflexivity.
  unfold PI. simpl fst; simpl snd.
  split; [unfold rk'; rewrite ilength_set; exact L1 |].
  split; [exact RL1 |]. split; [exact RL2 |]. split; [lia |].
  (* 5 *)
  split.
  { intros w Hw. destruct (Z.eq_dec (to_Z w) (to_Z v)) as [Ew | Ew].
    - apply to_Z_inj in Ew. subst w. left. rewrite Rk1. lia.
    - rewrite Rk2 by (intros ->; lia). destruct (I1 w Hw); [left; lia | right; assumption]. }
  (* 6 *)
  split.
  { intros w w' Hw Hw' Ee Hl.
    destruct (Z.eq_dec (to_Z w) (to_Z v)) as [Ew | Ew];
    destruct (Z.eq_dec (to_Z w') (to_Z v)) as [Ew' | Ew'].
    - apply to_Z_inj in Ew, Ew'. congruence.
    - apply to_Z_inj in Ew. subst w. rewrite Rk1, Rk2 in Ee by (intros ->; lia).
      destruct (I1 w' Hw') as [Hl' | He']; [rewrite <- Ee in Hl'; lia | rewrite <- Ee in He'; lia].
    - apply to_Z_inj in Ew'. subst w'. rewrite Rk1, Rk2 in Ee by (intros ->; lia).
      destruct (I1 w Hw) as [Hl' | He']; [rewrite Ee in Hl'; lia | rewrite Ee in He'; lia].
    - rewrite !Rk2 in Ee by (intros ->; lia). rewrite Rk2 in Hl by (intros ->; lia).
      apply I2; auto. }
  (* 7 *)
  split.
  { intros i Hi. rewrite Sk in Hi. destruct (Z.eq_dec (to_Z i) (to_Z k)) as [Ei | Ei].
    - apply to_Z_inj in Ei. subst i. exists v. split; [exact Vv | exact Rk1].
    - destruct (I3 i ltac:(lia)) as (w & Hw & Ew). exists w. split; [exact Hw |].
      rewrite Rk2; [exact Ew |]. apply Nv; [exact Hw | rewrite Ew; lia]. }
  (* 8 *)
  split.
  { rewrite Rk2; [exact I4 |]. apply Nv; [exact V0 | rewrite I4; change (to_Z 0) with 0%Z; lia]. }
  (* 9 *)
  split.
  { intros w Hw Rw.
    assert (Wv : w <> v) by (intros ->; rewrite Rk1 in Rw; apply Knx; rewrite Rw; reflexivity).
    rewrite Rk2 in Rw by exact Wv.
    destruct (RX w Hw) as [RK RP]. rewrite Rc in RK, RP by exact Hw.
    rewrite (Rk2 w Wv), Rw, Uint63.eqb_refl in RK, RP. simpl andb in RK, RP.
    destruct (I5 w Hw Rw) as (P1 & P2 & P3 & P4).
    destruct (Z.ltb_spec (D v w) K.[w]) as [Lt | Ge].
    - rewrite RK, RP. split; [exact Vv |]. split; [rewrite Rk1; lia |]. split; [reflexivity |].
      intros a Ha Hra. destruct (Z.eq_dec (to_Z a) (to_Z v)) as [Ea | Ea].
      + apply to_Z_inj in Ea. subst a. lia.
      + rewrite Rk2 in Hra by (intros ->; lia). pose proof (P4 a Ha (Mem a Ha Hra)). lia.
    - rewrite RK, RP. split; [exact P1 |].
      split; [rewrite Rk2 by (apply Nv; assumption); lia |]. split; [exact P3 |].
      intros a Ha Hra. destruct (Z.eq_dec (to_Z a) (to_Z v)) as [Ea | Ea].
      + apply to_Z_inj in Ea. subst a. lia.
      + rewrite Rk2 in Hra by (intros ->; lia). apply P4; [exact Ha | apply Mem; assumption]. }
  (* 10 *)
  { intros w Hw Hrw. destruct (RX w Hw) as [_ RP]. rewrite Rc in RP by exact Hw.
    destruct (Z.eq_dec (to_Z w) (to_Z v)) as [Ew | Ew].
    - apply to_Z_inj in Ew. subst w. rewrite Rk1 in RP, Hrw |- *.
      replace (k =? nx) with false in RP by (symmetry; apply Uint63.eqb_false_spec; intros E'; apply Knx; rewrite E'; reflexivity).
      simpl andb in RP. rewrite RP.
      destruct (I5 v Vv Rv) as (P1 & P2 & P3 & P4).
      split; [exact P1 |]. split; [rewrite Rk2 by (apply Nv; assumption); exact P2 |].
      intros a b Ha Hb (Hab1 & Hab2).
      assert (Av : a <> v) by (intros ->; rewrite Rk1 in Hab1; lia).
      rewrite Rk2 in Hab1 by exact Av.
      destruct (Z.eq_dec (to_Z b) (to_Z v)) as [Eb | Eb].
      + apply to_Z_inj in Eb. subst b. rewrite D_sym, <- P3. apply P4; [exact Ha | exact Hab1].
      + rewrite Rk2 in Hab2 by (intros ->; lia).
        assert (Rb : rk.[b] = nx) by (destruct (I1 b Hb); [lia | assumption]).
        pose proof (Mv b Hb Rb). destruct (I5 b Hb Rb) as (_ & _ & _ & Q4).
        pose proof (Q4 a Ha Hab1). rewrite D_sym, <- P3. lia.
    - assert (Wv : w <> v) by (intros ->; lia).
      rewrite (Rk2 w Wv) in RP, Hrw |- *.
      assert (Hrw' : (to_Z rk.[w] < to_Z k)%Z) by (apply Mem; [exact Hw | lia]).
      replace (rk.[w] =? nx) with false in RP by (symmetry; apply Uint63.eqb_false_spec; intros E'; rewrite E' in Hrw'; lia).
      simpl andb in RP. rewrite RP.
      destruct (I6 w Hw ltac:(lia)) as (P1 & P2 & P3).
      split; [exact P1 |]. split; [rewrite Rk2 by (apply Nv; [exact P1 | lia]); exact P2 |].
      intros a b Ha Hb (Hab1 & Hab2).
      assert (Av : a <> v) by (intros ->; rewrite Rk1 in Hab1; lia).
      rewrite Rk2 in Hab1 by exact Av.
      apply P3; [exact Ha | exact Hb | split; [exact Hab1 |]].
      destruct (Z.eq_dec (to_Z b) (to_Z v)) as [Eb | Eb].
      + apply to_Z_inj in Eb. subst b. rewrite Rv. pose proof (to_Z_bounded rk.[w]). lia.
      + rewrite Rk2 in Hab2 by (intros ->; lia). exact Hab2. }
Qed.


(* -- Prim: start and end -- *)

Definition K0 : array Z := loop nx (fun _ _ => true) (key_init GX GY) 0 (PArray.make nx 0%Z).
Definition rk0 : array int := (PArray.make nx nx).[0 <- 0].

Lemma K0_spec : PArray.length K0 = nx /\ forall w, V w -> K0.[w] = D 0 w.
Proof.
  pose proof n_bounds.
  assert (G := for_inv (fun i (K : array Z) => PArray.length K = nx /\
     forall w, (to_Z w < to_Z i)%Z -> K.[w] = D 0 w) nx 0 (key_init GX GY) (PArray.make nx 0%Z)).
  destruct G as [G1 G2].
  - change (to_Z 0) with 0%Z; lia.
  - split; [apply zlength_make_n |]. intros w Hw. change (to_Z 0) with 0%Z in Hw.
    pose proof (to_Z_bounded w). lia.
  - intros j K Hj [L Q]. unfold key_init. rewrite zlength_set. split; [exact L |].
    intros w Hw. rewrite succ_V in Hw by lia.
    destruct (Z.eq_dec (to_Z w) (to_Z j)) as [Ew | Ew].
    + apply to_Z_inj in Ew. subst w. rewrite zget_set_same by (apply ltb_V; [exact L | unfold V; lia]).
      reflexivity.
    + rewrite zget_set_other by (intros ->; lia). apply Q. lia.
  - split; [exact G1 | exact G2].
Qed.

Lemma rk0_0 : rk0.[0] = 0.
Proof. unfold rk0. apply iget_set_same. apply ltb_V; [apply ilength_make_n | exact V0]. Qed.

Lemma rk0_other : forall w, w <> 0 -> rk0.[w] = nx.
Proof. intros w Hw. unfold rk0. rewrite iget_set_other by congruence. apply iget_make. Qed.

Lemma PI_init : PI 1 (rk0, K0, PArray.make nx 0).
Proof.
  pose proof n_bounds. destruct K0_spec as [KL KV].
  assert (Z1 : forall w, V w -> (to_Z rk0.[w] < to_Z 1)%Z -> w = 0).
  { intros w Hw Hr. destruct (Z.eq_dec (to_Z w) 0) as [E0 | E0].
    - apply to_Z_inj. exact E0.
    - rewrite rk0_other in Hr by (intros ->; apply E0; reflexivity). change (to_Z 1) with 1%Z in Hr. lia. }
  unfold PI; simpl fst; simpl snd.
  split; [unfold rk0; rewrite ilength_set; apply ilength_make_n |].
  split; [exact KL |]. split; [apply ilength_make_n |]. split; [change (to_Z 1) with 1%Z; lia |].
  split.
  { intros w Hw. destruct (Z.eq_dec (to_Z w) 0) as [E0 | E0].
    - left. replace w with 0 by (apply to_Z_inj; symmetry; exact E0). rewrite rk0_0. reflexivity.
    - right. apply rk0_other. intros ->. apply E0. reflexivity. }
  split.
  { intros w w' Hw Hw' E' Hl. pose proof (Z1 w Hw Hl). subst w. rewrite rk0_0 in E'.
    symmetry. apply Z1; [exact Hw' | rewrite <- E'; reflexivity]. }
  split.
  { intros i Hi. change (to_Z 1) with 1%Z in Hi. exists 0. split; [exact V0 |].
    rewrite rk0_0. apply to_Z_inj. pose proof (to_Z_bounded i). change (to_Z 0) with 0%Z. lia. }
  split; [exact rk0_0 |].
  split.
  { intros w Hw Rw. rewrite iget_make. split; [exact V0 |]. split; [rewrite rk0_0; reflexivity |].
    split; [apply KV, Hw |]. intros a Ha Hra. rewrite (Z1 a Ha Hra), KV by exact Hw. lia. }
  { intros w Hw Hr. change (to_Z 1) with 1%Z in Hr. lia. }
Qed.

Definition PR := loop nx (fun _ _ => true) (prim_step GX GY nx) 1 (rk0, K0, PArray.make nx 0).
Definition RK : array int := fst (fst PR).
Definition PA : array int := snd PR.

Lemma PI_final : PI nx PR.
Proof.
  pose proof n_bounds. unfold PR. apply for_inv.
  - change (to_Z 1) with 1%Z; lia.
  - exact PI_init.
  - intros j t Hj Pt. apply prim_step_spec; [exact Pt | change (to_Z 1) with 1%Z in Hj; lia].
Qed.

(* the vertex of rank k *)
Definition invn (k : nat) : nat := fnd (fun v => RK.[ofn v] =? ofn k) NX.
Definition inv (k : nat) : int := ofn (invn k).

Lemma invn_lt : forall k, (k < NX)%nat -> (invn k < NX)%nat /\ RK.[inv k] = ofn k.
Proof.
  intros k Hk. pose proof n_bounds. pose proof PI_final as HP.
  unfold PI in HP. destruct HP as (_ & _ & _ & _ & _ & _ & I3 & _).
  fold RK in I3.
  destruct (I3 (ofn k)) as (w & Hw & Ew); [rewrite ofn_spec; unfold NX in Hk; lia |].
  assert (Lt : (invn k < NX)%nat).
  { apply fnd_lt. exists (Z.to_nat (to_Z w)). split; [unfold V, NX in *; lia |].
    rewrite ofn_V by exact Hw. apply Uint63.eqb_spec. exact Ew. }
  split; [exact Lt |].
  apply Uint63.eqb_spec. exact (fnd_true _ _ Lt).
Qed.

Lemma inv_spec : forall k, (k < NX)%nat -> V (inv k) /\ RK.[inv k] = ofn k.
Proof.
  intros k Hk. pose proof n_bounds. destruct (invn_lt k Hk) as [Lt R].
  split; [apply V_ofn; unfold NX in Lt; lia | exact R].
Qed.

Lemma RK_lt : forall w, V w -> (to_Z RK.[w] < to_Z nx)%Z.
Proof.
  intros w Hw. pose proof n_bounds. pose proof PI_final as HP.
  unfold PI in HP. destruct HP as (_ & _ & _ & _ & I1 & _). fold RK in I1.
  destruct (I1 w Hw) as [Hl | He]; [exact Hl | exfalso].
  assert (Inj : forall i j, (i < NX)%nat -> (j < NX)%nat -> invn i = invn j -> i = j).
  { intros i j Hi Hj E'. destruct (inv_spec i Hi) as [_ Ri]. destruct (inv_spec j Hj) as [_ Rj].
    unfold inv in Ri, Rj. rewrite E' in Ri. rewrite Ri in Rj. apply (f_equal to_Z) in Rj.
    rewrite !ofn_spec in Rj by (unfold NX in *; lia). lia. }
  assert (Rng : forall i, (i < NX)%nat -> (invn i < NX)%nat).
  { intros i Hi. apply (invn_lt i Hi). }
  destruct (pigeon_surj invn NX Rng Inj (Z.to_nat (to_Z w))) as (i & Hi & Ei); [unfold V, NX in *; lia |].
  destruct (inv_spec i Hi) as [_ Ri]. unfold inv in Ri. rewrite Ei, ofn_V in Ri by exact Hw.
  rewrite He in Ri. apply (f_equal to_Z) in Ri. rewrite ofn_spec in Ri by (unfold NX in *; lia).
  unfold NX in Hi. lia.
Qed.


(* -- What the walk and the comparison use of Prim's tree -- *)

Lemma RK_inj : forall w w', V w -> V w' -> RK.[w] = RK.[w'] -> w = w'.
Proof.
  intros w w' Hw Hw' E'. pose proof PI_final as HP. unfold PI in HP.
  destruct HP as (_ & _ & _ & _ & _ & I2 & _). apply I2; auto. apply RK_lt, Hw.
Qed.

Lemma RK_0 : RK.[0] = 0.
Proof. pose proof PI_final as HP. unfold PI in HP. destruct HP as (_ & _ & _ & _ & _ & _ & _ & I4 & _). exact I4. Qed.

Lemma RK_pos : forall w, V w -> w <> 0 -> (1 <= to_Z RK.[w])%Z.
Proof.
  intros w Hw Ne. destruct (Z.eq_dec (to_Z RK.[w]) 0) as [E0 | E0]; [| pose proof (to_Z_bounded RK.[w]); lia].
  exfalso. apply Ne. apply RK_inj; [exact Hw | exact V0 |]. rewrite RK_0. apply to_Z_inj. exact E0.
Qed.

Lemma PA_spec : forall w, V w -> w <> 0 ->
  V PA.[w] /\ (to_Z RK.[PA.[w]] < to_Z RK.[w])%Z /\
  forall a b, V a -> V b -> (to_Z RK.[a] < to_Z RK.[w] <= to_Z RK.[b])%Z ->
    (D w PA.[w] <= D a b)%Z.
Proof.
  intros w Hw Ne. pose proof PI_final as HP. unfold PI in HP.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & I6). apply I6; [exact Hw |].
  split; [apply RK_pos; assumption | apply RK_lt, Hw].
Qed.

Lemma inv_RK : forall w, V w -> inv (Z.to_nat (to_Z RK.[w])) = w.
Proof.
  intros w Hw. pose proof (RK_lt w Hw). pose proof (to_Z_bounded RK.[w]). pose proof n_bounds.
  destruct (inv_spec (Z.to_nat (to_Z RK.[w]))) as [Vi Ri]; [unfold NX; lia |].
  apply RK_inj; [exact Vi | exact Hw |]. rewrite Ri. apply to_Z_inj. rewrite ofn_spec by lia. lia.
Qed.

(* the weight of the tree edge added at step k *)
Definition wk (k : nat) : R := di (inv k) PA.[inv k].

Definition W : R := sum_below (fun k => wk (S k)) (NX - 1).

Lemma cut_R : forall k, (1 <= k < NX)%nat -> forall a b, V a -> V b ->
  (to_Z RK.[a] < Z.of_nat k <= to_Z RK.[b])%Z -> (wk k <= di a b)%R.
Proof.
  intros k Hk a b Ha Hb Hab. pose proof n_bounds.
  destruct (inv_spec k ltac:(lia)) as [Vi Ri].
  assert (Rk : to_Z RK.[inv k] = Z.of_nat k) by (rewrite Ri; apply ofn_spec; unfold NX in Hk; lia).
  assert (Ni : inv k <> 0) by (intros E'; rewrite E', RK_0 in Rk; change (to_Z 0) with 0%Z in Rk; lia).
  destruct (PA_spec (inv k) Vi Ni) as (P1 & _ & P3).
  unfold wk. apply di_mono; try assumption. apply P3; [exact Ha | exact Hb | lia].
Qed.

(* -- The lower bound: W is at most the length of any tour -- *)

Lemma W_le_tour : forall u, is_tour (len xs) u -> (W <= tour_length xs ys u)%R.
Proof.
  intros u (Lu & Fu & Du). pose proof n_bounds. pose proof len_x as LX.
  unfold len in Lu. assert (Lu' : List.length u = NX) by (unfold NX; lia).
  set (pv := fun j => nth j u 0%N).
  assert (Pv : forall j, (j < NX)%nat -> (pv j < N.of_nat NX)%N).
  { intros j Hj. rewrite Forall_forall in Fu. unfold pv. unfold NX in *.
    assert (In (nth j u 0%N) u) as Hin by (apply nth_In; lia).
    pose proof (Fu _ Hin) as Hf. unfold len in Hf. lia. }
  set (vi := fun j => ofn (N.to_nat (pv j))).
  assert (Vvi : forall j, (j < NX)%nat -> V (vi j)).
  { intros j Hj. pose proof (Pv j Hj). apply V_ofn. unfold NX in *. lia. }
  assert (Dvi : forall j j', (j < NX)%nat -> (j' < NX)%nat ->
            di (vi j) (vi j') = dist xs ys (pv j) (pv j')).
  { intros j j' Hj Hj'. pose proof (Pv j Hj). pose proof (Pv j' Hj'). unfold di, vi.
    rewrite !ofn_spec by (unfold NX in *; lia). rewrite !N_nat_Z, !N2Z.id. reflexivity. }
  set (o := fun j => Z.to_nat (to_Z RK.[vi j])).
  set (c := fun j => dist xs ys (pv j) (pv (S j))).
  assert (PB : (sum_below (fun k => wk (S k)) (NX - 1) <= sum_below c (NX - 1))%R).
  { apply (path_bound NX o c wk).
    - intros i Hi. unfold o. pose proof (RK_lt (vi i) (Vvi i Hi)). unfold NX. lia.
    - intros i j Hi Hj E'. unfold o in E'.
      pose proof (to_Z_bounded RK.[vi i]). pose proof (to_Z_bounded RK.[vi j]).
      assert (E2 : RK.[vi i] = RK.[vi j]) by (apply to_Z_inj; lia).
      apply RK_inj in E2; [| apply Vvi; exact Hi | apply Vvi; exact Hj].
      unfold vi in E2. apply (f_equal to_Z) in E2.
      pose proof (Pv i Hi). pose proof (Pv j Hj).
      rewrite !ofn_spec in E2 by (unfold NX in *; lia).
      apply (proj1 (NoDup_nth u 0%N) Du); [lia | lia |]. unfold pv in *. lia.
    - intros j k Hj Hk1 Hk2. unfold c.
      pose proof (RK_lt (vi j) (Vvi j ltac:(lia))). pose proof (RK_lt (vi (S j)) (Vvi (S j) Hj)).
      pose proof (to_Z_bounded RK.[vi j]). pose proof (to_Z_bounded RK.[vi (S j)]).
      unfold o in Hk1, Hk2.
      destruct (Z_lt_le_dec (to_Z RK.[vi j]) (to_Z RK.[vi (S j)])) as [Lt | Ge].
      + rewrite <- Dvi by lia. apply cut_R; [unfold NX in *; lia | apply Vvi; lia | apply Vvi; lia | lia].
      + rewrite dist_sym. rewrite <- Dvi by lia.
        apply cut_R; [unfold NX in *; lia | apply Vvi; lia | apply Vvi; lia | lia]. }
  unfold W. eapply Rle_trans; [exact PB |].
  unfold tour_length. rewrite Lu'. cbv zeta.
  replace NX with (S (NX - 1)) at 2 by (unfold NX; lia).
  simpl sum_below.
  assert (E' : sum_below c (NX - 1) =
     sum_below (fun k => dist xs ys (nth k u 0%N) (nth ((k + 1) mod NX) u 0%N)) (NX - 1)).
  { apply sum_below_ext. intros k Hk. unfold c, pv. rewrite Nat.mod_small by lia.
    replace (k + 1)%nat with (S k) by lia. reflexivity. }
  rewrite <- E'. pose proof (dist_nonneg xs ys (nth (NX - 1) u 0%N) (nth ((NX - 1 + 1) mod NX) u 0%N)).
  lra.
Qed.


(* -- The walk: definitions -- *)

Fixpoint sumZ (f : nat -> Z) (m : nat) : Z :=
  match m with O => 0%Z | S m' => (sumZ f m' + f m')%Z end.

Lemma sumZ_ext : forall f g m, (forall k, (k < m)%nat -> g k = f k) -> sumZ g m = sumZ f m.
Proof.
  intros f g m. induction m as [| m IH]; intros H; [reflexivity |]. simpl.
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumZ_update : forall f g m k0, (k0 < m)%nat ->
  (forall k, (k < m)%nat -> k <> k0 -> g k = f k) -> g k0 = (f k0 + 1)%Z ->
  sumZ g m = (sumZ f m + 1)%Z.
Proof.
  intros f g m. induction m as [| m IH]; intros k0 Hk H H0; [lia |]. simpl.
  destruct (Nat.eq_dec k0 m) as [E' | E'].
  - subst k0. rewrite (sumZ_ext f g m) by (intros; apply H; lia). lia.
  - rewrite (IH k0) by (try lia; intros; apply H; lia). rewrite (H m) by lia. lia.
Qed.

Lemma sumZ_bound : forall f m B, (forall k, (k < m)%nat -> (0 <= f k <= B)%Z) ->
  (0 <= sumZ f m <= Z.of_nat m * B)%Z.
Proof.
  intros f m B. induction m as [| m IH]; intros H; cbn [sumZ]; [lia |].
  pose proof (IH (fun k Hk => H k ltac:(lia))). pose proof (H m ltac:(lia)).
  rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia.
Qed.

Definition InOc (out : array int) (cnt : int) (c : int) : Prop :=
  exists i, (to_Z i < to_Z cnt)%Z /\ out.[i] = c.
Definition InO (s : DS) (c : int) : Prop := InOc (ds_out s) (ds_cnt s) c.
Definition geti (t : array int) (i : nat) : int := t.[ofn i].
Definition pathlen (s : DS) : R :=
  sum_below (fun i => di (geti (ds_out s) i) (geti (ds_out s) (S i))) (Z.to_nat (to_Z (ds_cnt s)) - 1).
Definition chain (s : DS) : R :=
  sum_below (fun i => di (geti (ds_stk s) i) (geti (ds_stk s) (S i))) (Z.to_nat (to_Z (ds_sp s)) - 1).
Definition lastv (s : DS) : int := (ds_out s).[ds_cnt s - 1].
Definition topv (s : DS) : int := if 0 <? ds_sp s then (ds_stk s).[ds_sp s - 1] else 0.
Definition ind (it : array int) (k : nat) : R :=
  if Z.ltb (to_Z (inv k)) (to_Z it.[PA.[inv k]]) then wk k else 0%R.
Definition Wout (s : DS) : R := sum_below (fun k => ind (ds_it s) (S k)) (NX - 1).
Definition sumit (t : array int) : Z := sumZ (fun v => to_Z t.[ofn v]) NX.

Definition PL (t : array int) (q : int) : R :=
  sum_below (fun i => di (geti t i) (geti t (S i))) (Z.to_nat (to_Z q) - 1).

Definition DI (j : int) (s : DS) : Prop :=
  let it := ds_it s in let stk := ds_stk s in let sp := ds_sp s in
  let out := ds_out s in let cnt := ds_cnt s in
  PArray.length it = nx /\ PArray.length stk = nx /\ PArray.length out = nx /\
  (1 <= to_Z cnt <= to_Z nx)%Z /\ (to_Z sp <= to_Z cnt)%Z /\
  to_Z j = (sumit it + to_Z cnt - to_Z sp)%Z /\
  (forall i, (to_Z i < to_Z cnt)%Z -> V out.[i]) /\ out.[0] = 0 /\
  (forall i i', (to_Z i < to_Z cnt)%Z -> (to_Z i' < to_Z cnt)%Z -> out.[i] = out.[i'] -> i = i') /\
  (forall v, V v -> (to_Z it.[v] <= to_Z nx)%Z) /\
  (forall c, V c -> c <> 0 -> (InO s c <-> (to_Z c < to_Z it.[PA.[c]])%Z)) /\
  (forall i, (to_Z i < to_Z sp)%Z -> V stk.[i] /\ InO s stk.[i]) /\
  ((0 < to_Z sp)%Z -> stk.[0] = 0) /\
  (forall v, V v -> InO s v -> (exists i, (to_Z i < to_Z sp)%Z /\ stk.[i] = v) \/ it.[v] = nx) /\
  (PL out cnt + di out.[cnt - 1] (if 0 <? sp then stk.[sp - 1] else 0) + PL stk sp <=
     2 * sum_below (fun k => ind it (S k)) (NX - 1))%R.

(* -- small facts -- *)

Lemma geti_eq : forall t i (p : int), Z.of_nat i = to_Z p -> geti t i = t.[p].
Proof.
  intros t i p E'. unfold geti. f_equal. apply to_Z_inj. pose proof (to_Z_bounded p).
  unfold ofn. rewrite of_Z_spec, E'. apply Z.mod_small. exact (to_Z_bounded p).
Qed.

Lemma geti_set_other : forall t i (p v : int), Z.of_nat i <> to_Z p -> (Z.of_nat i < 4194304)%Z ->
  geti (t.[p <- v]) i = geti t i.
Proof.
  intros t i p v Ne Hi. unfold geti. apply iget_set_other. intros E'. apply Ne.
  rewrite E'. apply eq_sym, ofn_spec. exact Hi.
Qed.

Lemma ind_nonzero_v : forall k, (1 <= k < NX)%nat -> inv k <> 0.
Proof.
  intros k Hk E'. pose proof n_bounds. destruct (inv_spec k ltac:(lia)) as [_ R].
  rewrite E', RK_0 in R. apply (f_equal to_Z) in R. rewrite ofn_spec in R by (unfold NX in *; lia).
  change (to_Z 0) with 0%Z in R. lia.
Qed.

Lemma inv_eq_rank : forall k c, (1 <= k < NX)%nat -> V c -> inv k = c -> Z.of_nat k = to_Z RK.[c].
Proof.
  intros k c Hk Hc E'. pose proof n_bounds. destruct (inv_spec k ltac:(lia)) as [_ R].
  rewrite E' in R. rewrite R. apply eq_sym, ofn_spec. unfold NX in *; lia.
Qed.

Lemma ind_same : forall (it : array int) u c k, PArray.length it = nx -> V u -> it.[u] = c ->
  (to_Z c < to_Z nx)%Z -> (inv k <> c \/ PA.[inv k] <> u) ->
  ind (it.[u <- c + 1]) k = ind it k.
Proof.
  intros it u c k L Vu Iu Hc H. unfold ind.
  destruct (Uint63.eqs PA.[inv k] u) as [E' | Ne].
  - rewrite E', iget_set_same by (apply ltb_V; assumption). rewrite Iu.
    rewrite succ_V by exact Hc.
    destruct H as [H | H]; [| contradiction].
    assert (to_Z (inv k) <> to_Z c) by (intros E2; apply H, to_Z_inj, E2).
    destruct (Z.ltb_spec (to_Z (inv k)) (to_Z c + 1)), (Z.ltb_spec (to_Z (inv k)) (to_Z c)); try reflexivity; lia.
  - rewrite iget_set_other by congruence. reflexivity.
Qed.

Lemma sumit_set : forall (it : array int) u c, PArray.length it = nx -> V u -> it.[u] = c ->
  (to_Z c < to_Z nx)%Z -> sumit (it.[u <- c + 1]) = (sumit it + 1)%Z.
Proof.
  intros it u c L Vu Iu Hc. pose proof n_bounds. unfold sumit.
  apply (sumZ_update _ _ _ (Z.to_nat (to_Z u))).
  - unfold V, NX in *. lia.
  - intros k Hk Ne. rewrite iget_set_other; [reflexivity |]. intros E'. apply Ne.
    rewrite E'. rewrite ofn_spec by (unfold NX in *; lia). lia.
  - rewrite ofn_V by exact Vu. rewrite iget_set_same by (apply ltb_V; assumption).
    rewrite Iu. apply succ_V. exact Hc.
Qed.


Lemma pathlen_PL : forall s, pathlen s = PL (ds_out s) (ds_cnt s).
Proof. reflexivity. Qed.

Lemma chain_PL : forall s, chain s = PL (ds_stk s) (ds_sp s).
Proof. reflexivity. Qed.

Lemma PL_succ : forall t q, (1 <= to_Z q < to_Z nx)%Z ->
  PL t (q + 1) = (PL t q + di t.[q - 1] t.[q])%R.
Proof.
  intros t q Hq. pose proof n_bounds. unfold PL. rewrite succ_V by lia.
  replace (Z.to_nat (to_Z q + 1) - 1)%nat with (S (Z.to_nat (to_Z q) - 1)) by lia.
  rewrite sum_below_S.
  assert (to_Z (q - 1) = (to_Z q - 1)%Z) by sia.
  rewrite (geti_eq t (Z.to_nat (to_Z q) - 1) (q - 1)) by lia.
  rewrite (geti_eq t (S (Z.to_nat (to_Z q) - 1)) q) by lia.
  reflexivity.
Qed.

Lemma PL_set : forall t q c, (to_Z q < to_Z nx)%Z -> PL (t.[q <- c]) q = PL t q.
Proof.
  intros t q c Hq. pose proof n_bounds. unfold PL. apply sum_below_ext. intros k Hk.
  rewrite !geti_set_other by lia. reflexivity.
Qed.

Lemma PL_0 : forall t, PL t 0 = 0%R.
Proof. reflexivity. Qed.

Lemma PL_1 : forall t, PL t 1 = 0%R.
Proof. reflexivity. Qed.

Lemma InOc_push : forall out cnt c v, (to_Z cnt < to_Z nx)%Z ->
  PArray.length out = nx ->
  (InOc (out.[cnt <- c]) (cnt + 1) v <-> InOc out cnt v \/ v = c).
Proof.
  intros out cnt c v Hc L. pose proof n_bounds. unfold InOc. rewrite succ_V by lia. split.
  - intros (i & Hi & Ei). destruct (Z.eq_dec (to_Z i) (to_Z cnt)) as [E' | E'].
    + apply to_Z_inj in E'. subst i. rewrite iget_set_same in Ei by (apply ltb_V; [exact L | exact Hc]).
      right. congruence.
    + left. exists i. split; [lia |]. rewrite iget_set_other in Ei by (intros ->; lia). exact Ei.
  - intros [(i & Hi & Ei) | ->].
    + exists i. split; [lia |]. rewrite iget_set_other by (intros ->; lia). exact Ei.
    + exists cnt. split; [lia |]. apply iget_set_same. apply ltb_V; [exact L | exact Hc].
Qed.

Lemma cnt_lt : forall (out : array int) cnt c, (1 <= to_Z cnt <= to_Z nx)%Z ->
  (forall i, (to_Z i < to_Z cnt)%Z -> V out.[i]) ->
  (forall i i', (to_Z i < to_Z cnt)%Z -> (to_Z i' < to_Z cnt)%Z -> out.[i] = out.[i'] -> i = i') ->
  V c -> ~ InOc out cnt c -> (to_Z cnt < to_Z nx)%Z.
Proof.
  intros out cnt c Hc O1 O3 Vc Nin. pose proof n_bounds.
  set (cn := Z.to_nat (to_Z c)).
  set (o := fun i : nat => let v := Z.to_nat (to_Z out.[ofn i]) in if (v <? cn)%nat then v else (v - 1)%nat).
  assert (Hv' : forall i, (i < Z.to_nat (to_Z cnt))%nat ->
     (to_Z (ofn i) < to_Z cnt)%Z /\ V out.[ofn i] /\ out.[ofn i] <> c).
  { intros i Hi. assert (Ei : to_Z (ofn i) = Z.of_nat i) by (apply ofn_spec; lia).
    split; [lia |]. split; [apply O1; lia |]. intros E'. apply Nin. exists (ofn i). split; [lia | exact E']. }
  assert (Z.to_nat (to_Z cnt) <= NX - 1)%nat; [| unfold NX in *; lia].
  apply (pigeon_le o).
  - intros i Hi. destruct (Hv' i Hi) as (_ & Vi & Ni). unfold o. cbv zeta. unfold V, NX, cn in *.
    assert (to_Z out.[ofn i] <> to_Z c) by (intros E'; apply Ni, to_Z_inj, E').
    destruct (Nat.ltb_spec (Z.to_nat (to_Z out.[ofn i])) (Z.to_nat (to_Z c))); lia.
  - intros i i' Hi Hi' E'. destruct (Hv' i Hi) as (Ci & Vi & Ni). destruct (Hv' i' Hi') as (Ci' & Vi' & Ni').
    unfold o in E'. cbv zeta in E'. unfold cn in E'.
    assert (to_Z out.[ofn i] <> to_Z c) by (intros E2; apply Ni, to_Z_inj, E2).
    assert (to_Z out.[ofn i'] <> to_Z c) by (intros E2; apply Ni', to_Z_inj, E2).
    pose proof (to_Z_bounded out.[ofn i]). pose proof (to_Z_bounded out.[ofn i']). pose proof (to_Z_bounded c).
    assert (Eo : out.[ofn i] = out.[ofn i']).
    { apply to_Z_inj.
      destruct (Nat.ltb_spec (Z.to_nat (to_Z out.[ofn i])) (Z.to_nat (to_Z c)));
      destruct (Nat.ltb_spec (Z.to_nat (to_Z out.[ofn i'])) (Z.to_nat (to_Z c))); lia. }
    apply O3 in Eo; [| lia | lia]. apply (f_equal to_Z) in Eo.
    rewrite !ofn_spec in Eo by lia. lia.
Qed.

Lemma Wout_push : forall (it : array int) u c, PArray.length it = nx -> V u -> it.[u] = c ->
  (to_Z c < to_Z nx)%Z -> PA.[c] = u -> c <> 0 ->
  sum_below (fun k => ind (it.[u <- c + 1]) (S k)) (NX - 1) =
  (sum_below (fun k => ind it (S k)) (NX - 1) + di c u)%R.
Proof.
  intros it u c L Vu Iu Hc Pc Nc. pose proof n_bounds.
  assert (Vc : V c) by exact Hc.
  set (r := Z.to_nat (to_Z RK.[c])).
  assert (Hr : (1 <= r < NX)%nat).
  { pose proof (RK_pos c Vc Nc). pose proof (RK_lt c Vc). unfold r, NX. lia. }
  assert (Ir : inv r = c) by (apply inv_RK, Vc).
  assert (Hu : forall k, (k < NX - 1)%nat -> k <> (r - 1)%nat ->
     ind (it.[u <- c + 1]) (S k) = ind it (S k)).
  { intros k Hk Ne. apply ind_same; try assumption. left. intros E'. apply Ne.
    pose proof (inv_eq_rank (S k) c ltac:(lia) Vc E'). unfold r. lia. }
  rewrite (sum_below_update (fun k => ind it (S k)) _ (NX - 1) (r - 1) ltac:(lia) Hu).
  replace (S (r - 1)) with r by lia.
  unfold ind. rewrite Ir, Pc, iget_set_same by (apply ltb_V; assumption). rewrite Iu, succ_V by exact Hc.
  destruct (Z.ltb_spec (to_Z c) (to_Z c)); [lia |].
  destruct (Z.ltb_spec (to_Z c) (to_Z c + 1)); [| lia].
  unfold wk. rewrite Ir, Pc. ring.
Qed.

Lemma Wout_scan : forall (it : array int) u c, PArray.length it = nx -> V u -> it.[u] = c ->
  (to_Z c < to_Z nx)%Z -> ~ (PA.[c] = u /\ c <> 0) ->
  sum_below (fun k => ind (it.[u <- c + 1]) (S k)) (NX - 1) =
  sum_below (fun k => ind it (S k)) (NX - 1).
Proof.
  intros it u c L Vu Iu Hc Nn. apply sum_below_ext. intros k Hk.
  apply ind_same; try assumption.
  destruct (Uint63.eqs (inv (S k)) c) as [E' | E']; [right | left; exact E'].
  intros Pu. apply Nn. rewrite <- E'. split; [exact Pu |]. apply ind_nonzero_v. lia.
Qed.


Lemma sumit_bound : forall it : array int, (forall v, V v -> (to_Z it.[v] <= to_Z nx)%Z) ->
  (0 <= sumit it <= to_Z nx * to_Z nx)%Z.
Proof.
  intros it T. pose proof n_bounds. unfold sumit.
  pose proof (sumZ_bound (fun v => to_Z it.[ofn v]) NX (to_Z nx)) as B.
  unfold NX in B. rewrite Z2Nat.id in B by lia. apply B.
  intros k Hk. pose proof (to_Z_bounded it.[ofn k]). split; [lia |]. apply T. apply V_ofn. lia.
Qed.

Ltac ieq i j E := destruct (Uint63.eqb i j) eqn:E;
  [apply Uint63.eqb_spec in E; subst i | apply Uint63.eqb_false_spec in E].

Ltac unDI H := unfold DI, InO, ds_it, ds_stk, ds_sp, ds_out, ds_cnt in H; cbn [fst snd] in H.
Ltac unDIg := unfold DI, InO, ds_it, ds_stk, ds_sp, ds_out, ds_cnt; cbn [fst snd].

Lemma int_cases : forall a b : int, a = b \/ a <> b.
Proof. intros a b. destruct (Uint63.eqs a b); [left | right]; assumption. Qed.

Lemma dfs_push : forall j it stk sp out cnt, DI j (it, stk, sp, out, cnt) -> (0 < to_Z sp)%Z ->
  (to_Z it.[stk.[sp - 1]] < to_Z nx)%Z -> PA.[it.[stk.[sp - 1]]] = stk.[sp - 1] ->
  it.[stk.[sp - 1]] <> 0 ->
  DI (j + 1) (it.[stk.[sp - 1] <- it.[stk.[sp - 1]] + 1], stk.[sp <- it.[stk.[sp - 1]]], sp + 1,
              out.[cnt <- it.[stk.[sp - 1]]], cnt + 1).
Proof.
  intros j it stk sp out cnt HD Hsp.
  set (u := stk.[sp - 1]). set (c := it.[u]). intros Hc Pc Nc.
  unDI HD.
  destruct HD as (L1 & L2 & L3 & C1 & C2 & J & O1 & O2 & O3 & T1 & T2 & S1 & S2 & S3 & LEN).
  pose proof n_bounds.
  assert (Sp1 : to_Z (sp - 1) = (to_Z sp - 1)%Z) by sia.
  destruct (S1 (sp - 1) ltac:(lia)) as [Vu Iu]. fold u in Vu, Iu.
  assert (Vc : V c) by exact Hc.
  assert (Nin : ~ InOc out cnt c).
  { intros Hin. apply (T2 c Vc Nc) in Hin. rewrite Pc in Hin. fold c in Hin. lia. }
  assert (Cn : (to_Z cnt < to_Z nx)%Z) by (apply (cnt_lt out cnt c); assumption).
  assert (Cs : to_Z (cnt + 1) = (to_Z cnt + 1)%Z) by (apply succ_V; lia).
  assert (Ss : to_Z (sp + 1) = (to_Z sp + 1)%Z) by (apply succ_V; lia).
  assert (Cc : to_Z (c + 1) = (to_Z c + 1)%Z) by (apply succ_V; lia).
  assert (In' : forall v, InOc (out.[cnt <- c]) (cnt + 1) v <-> InOc out cnt v \/ v = c)
    by (intros; apply InOc_push; assumption).
  assert (Gi : forall v, it.[u <- c + 1].[v] = if Uint63.eqb v u then c + 1 else it.[v]).
  { intros v. destruct (int_cases v u) as [-> | Ne].
    - rewrite Uint63.eqb_refl. apply iget_set_same, ltb_V; assumption.
    - replace (v =? u) with false by (symmetry; apply Uint63.eqb_false_spec; exact Ne).
      apply iget_set_other. congruence. }
  assert (Go : forall i, out.[cnt <- c].[i] = if Uint63.eqb i cnt then c else out.[i]).
  { intros i. destruct (int_cases i cnt) as [-> | Ne].
    - rewrite Uint63.eqb_refl. apply iget_set_same, ltb_V; assumption.
    - replace (i =? cnt) with false by (symmetry; apply Uint63.eqb_false_spec; exact Ne).
      apply iget_set_other. congruence. }
  assert (Gs : forall i, stk.[sp <- c].[i] = if Uint63.eqb i sp then c else stk.[i]).
  { intros i. destruct (int_cases i sp) as [-> | Ne].
    - rewrite Uint63.eqb_refl. apply iget_set_same, ltb_V; [assumption | unfold V; lia].
    - replace (i =? sp) with false by (symmetry; apply Uint63.eqb_false_spec; exact Ne).
      apply iget_set_other. congruence. }
  unDIg.
  split; [rewrite ilength_set; exact L1 |].
  split; [rewrite ilength_set; exact L2 |].
  split; [rewrite ilength_set; exact L3 |].
  split; [lia |]. split; [lia |].
  assert (Hsb := sumit_bound it T1).
  split.
  { rewrite (sumit_set it u c L1 Vu eq_refl Hc).
    assert (Nb : (to_Z nx * to_Z nx <= 1000000)%Z) by (clear - H; nia).
    assert (Jb : (to_Z j < 2000000)%Z) by lia.
    assert (to_Z (j + 1) = (to_Z j + 1)%Z) by sia. lia. }
  split.
  { intros i Hi. rewrite Go. ieq i cnt QQ; [exact Vc | apply O1].
    assert (to_Z i <> to_Z cnt) by (intros E'; apply QQ, to_Z_inj, E'). lia. }
  split.
  { rewrite Go. replace (0 =? cnt) with false; [exact O2 |].
    symmetry. apply Uint63.eqb_false_spec. intros E'. rewrite <- E' in C1. change (to_Z 0) with 0%Z in C1. lia. }
  split.
  { intros i i' Hi Hi' Ee. rewrite !Go in Ee.
    assert (Ii : forall a, a <> cnt -> (to_Z a < to_Z (cnt + 1))%Z -> (to_Z a < to_Z cnt)%Z).
    { intros a Na Ha. assert (to_Z a <> to_Z cnt) by (intros E'; apply Na, to_Z_inj, E'). lia. }
    ieq i cnt QQ; ieq i' cnt QQ2; try reflexivity.
    - exfalso. apply Nin. exists i'. split; [apply Ii; assumption | symmetry; exact Ee].
    - exfalso. apply Nin. exists i. split; [apply Ii; assumption | exact Ee].
    - apply O3; [apply Ii; assumption | apply Ii; assumption | exact Ee]. }
  split.
  { intros v Hv'. rewrite Gi. ieq v u QQ; [lia | apply T1, Hv']. }
  split.
  { intros c0 V0' N0. rewrite In', Gi.
    destruct (int_cases PA.[c0] u) as [Pu | Pu].
    - rewrite Pu, Uint63.eqb_refl, Cc. rewrite (T2 c0 V0' N0), Pu. fold c.
      split.
      + intros [Hl | ->]; lia.
      + intros Hl. destruct (Z.eq_dec (to_Z c0) (to_Z c)) as [Ec | Ec]; [right; apply to_Z_inj, Ec | left; lia].
    - replace (PA.[c0] =? u) with false by (symmetry; apply Uint63.eqb_false_spec; exact Pu).
      rewrite <- (T2 c0 V0' N0). split; [| tauto].
      intros [Hl | ->]; [exact Hl | contradiction]. }
  split.
  { intros i Hi. rewrite Gs. ieq i sp QQ.
    - split; [exact Vc |]. apply In'. right. reflexivity.
    - assert (to_Z i <> to_Z sp) by (intros E'; apply QQ, to_Z_inj, E').
      destruct (S1 i ltac:(lia)) as [Si1 Si2]. split; [exact Si1 | apply In'; left; exact Si2]. }
  split.
  { intros _. rewrite Gs. replace (0 =? sp) with false; [apply S2; exact Hsp |].
    symmetry. apply Uint63.eqb_false_spec. intros E'. rewrite <- E' in Hsp. change (to_Z 0) with 0%Z in Hsp. lia. }
  split.
  { intros v Hv' Hin. apply In' in Hin.
    destruct (int_cases v c) as [-> | Nvc].
    - left. exists sp. split; [lia |]. rewrite Gs, Uint63.eqb_refl. reflexivity.
    - destruct Hin as [Hin | Hin]; [| contradiction].
      destruct (int_cases v u) as [-> | Nvu].
      + left. exists (sp - 1). split; [lia |]. rewrite Gs.
        replace (sp - 1 =? sp) with false; [reflexivity |].
        symmetry. apply Uint63.eqb_false_spec. intros E'. apply (f_equal to_Z) in E'. lia.
      + destruct (S3 v Hv' Hin) as [(i & Hi & Ei) | Ei].
        * left. exists i. split; [lia |]. rewrite Gs.
          replace (i =? sp) with false; [exact Ei |].
          symmetry. apply Uint63.eqb_false_spec. intros ->. lia.
        * right. rewrite Gi. replace (v =? u) with false; [exact Ei |].
          symmetry. apply Uint63.eqb_false_spec. exact Nvu. }
  (* the length invariant *)
  rewrite (PL_succ _ cnt) by lia. rewrite (PL_set out cnt c) by lia.
  rewrite (PL_succ _ sp) by lia. rewrite (PL_set stk sp c) by lia.
  rewrite (Wout_push it u c L1 Vu eq_refl Hc Pc Nc).
  replace (cnt + 1 - 1) with cnt by (apply to_Z_inj; sia).
  replace (sp + 1 - 1) with sp by (apply to_Z_inj; sia).
  replace (0 <? sp + 1) with true by (symmetry; apply Uint63.ltb_spec; change (to_Z 0) with 0%Z; lia).
  replace (0 <? sp) with true in LEN by (symmetry; apply Uint63.ltb_spec; change (to_Z 0) with 0%Z; lia).
  fold u in LEN.
  rewrite !Go, !Gs, !Uint63.eqb_refl.
  replace (cnt - 1 =? cnt) with false by (symmetry; apply Uint63.eqb_false_spec; intros E'; apply (f_equal to_Z) in E'; sia).
  replace (sp - 1 =? sp) with false by (symmetry; apply Uint63.eqb_false_spec; intros E'; apply (f_equal to_Z) in E'; lia).
  fold u. rewrite di_self.
  pose proof (di_tri out.[cnt - 1] u c). rewrite (di_sym c u). lra.
Qed.


Lemma dfs_scan : forall j it stk sp out cnt, DI j (it, stk, sp, out, cnt) -> (0 < to_Z sp)%Z ->
  (to_Z it.[stk.[sp - 1]] < to_Z nx)%Z ->
  ~ (PA.[it.[stk.[sp - 1]]] = stk.[sp - 1] /\ it.[stk.[sp - 1]] <> 0) ->
  DI (j + 1) (it.[stk.[sp - 1] <- it.[stk.[sp - 1]] + 1], stk, sp, out, cnt).
Proof.
  intros j it stk sp out cnt HD Hsp.
  set (u := stk.[sp - 1]). set (c := it.[u]). intros Hc Nn.
  unDI HD.
  destruct HD as (L1 & L2 & L3 & C1 & C2 & J & O1 & O2 & O3 & T1 & T2 & S1 & S2 & S3 & LEN).
  pose proof n_bounds.
  assert (Sp1 : to_Z (sp - 1) = (to_Z sp - 1)%Z) by sia.
  destruct (S1 (sp - 1) ltac:(lia)) as [Vu Iu]. fold u in Vu, Iu.
  assert (Cc : to_Z (c + 1) = (to_Z c + 1)%Z) by (apply succ_V; lia).
  assert (Gi : forall v, it.[u <- c + 1].[v] = if Uint63.eqb v u then c + 1 else it.[v]).
  { intros v. destruct (int_cases v u) as [-> | Ne].
    - rewrite Uint63.eqb_refl. apply iget_set_same, ltb_V; assumption.
    - replace (v =? u) with false by (symmetry; apply Uint63.eqb_false_spec; exact Ne).
      apply iget_set_other. congruence. }
  assert (Hsb := sumit_bound it T1).
  unDIg.
  split; [rewrite ilength_set; exact L1 |].
  split; [exact L2 |]. split; [exact L3 |]. split; [lia |]. split; [lia |].
  split.
  { rewrite (sumit_set it u c L1 Vu eq_refl Hc).
    assert (Nb : (to_Z nx * to_Z nx <= 1000000)%Z) by (clear - H; nia).
    assert (Jb : (to_Z j < 2000000)%Z) by lia.
    assert (to_Z (j + 1) = (to_Z j + 1)%Z) by sia. lia. }
  split; [exact O1 |]. split; [exact O2 |]. split; [exact O3 |].
  split.
  { intros v Hv'. rewrite Gi. ieq v u QQ; [lia | apply T1, Hv']. }
  split.
  { intros c0 V0' N0. rewrite Gi. rewrite (T2 c0 V0' N0).
    destruct (int_cases PA.[c0] u) as [Pu | Pu].
    - rewrite Pu, Uint63.eqb_refl, Cc. fold c.
      assert (Nc0 : c0 <> c) by (intros ->; apply Nn; split; assumption).
      assert (to_Z c0 <> to_Z c) by (intros E'; apply Nc0, to_Z_inj, E'). lia.
    - replace (PA.[c0] =? u) with false by (symmetry; apply Uint63.eqb_false_spec; exact Pu).
      tauto. }
  split; [exact S1 |]. split; [exact S2 |].
  split.
  { intros v Hv' Hin. destruct (int_cases v u) as [-> | Nvu].
    - left. exists (sp - 1). split; [lia | reflexivity].
    - destruct (S3 v Hv' Hin) as [Ex | Ei]; [left; exact Ex |].
      right. rewrite Gi. replace (v =? u) with false; [exact Ei |].
      symmetry. apply Uint63.eqb_false_spec. exact Nvu. }
  rewrite (Wout_scan it u c L1 Vu eq_refl Hc Nn). exact LEN.
Qed.

Lemma dfs_pop : forall j it stk sp out cnt, DI j (it, stk, sp, out, cnt) -> (0 < to_Z sp)%Z ->
  (to_Z nx <= to_Z it.[stk.[sp - 1]])%Z ->
  DI (j + 1) (it, stk, sp - 1, out, cnt).
Proof.
  intros j it stk sp out cnt HD Hsp.
  set (u := stk.[sp - 1]). intros Hc.
  unDI HD.
  destruct HD as (L1 & L2 & L3 & C1 & C2 & J & O1 & O2 & O3 & T1 & T2 & S1 & S2 & S3 & LEN).
  pose proof n_bounds.
  assert (Sp1 : to_Z (sp - 1) = (to_Z sp - 1)%Z) by sia.
  destruct (S1 (sp - 1) ltac:(lia)) as [Vu Iu]. fold u in Vu, Iu.
  assert (Iun : it.[u] = nx) by (apply to_Z_inj; pose proof (T1 u Vu); lia).
  assert (Hsb := sumit_bound it T1).
  unDIg.
  split; [exact L1 |]. split; [exact L2 |]. split; [exact L3 |]. split; [lia |]. split; [lia |].
  split.
  { assert (Nb : (to_Z nx * to_Z nx <= 1000000)%Z) by (clear - H; nia).
    assert (Jb : (to_Z j < 2000000)%Z) by lia.
    assert (to_Z (j + 1) = (to_Z j + 1)%Z) by sia. lia. }
  split; [exact O1 |]. split; [exact O2 |]. split; [exact O3 |].
  split; [exact T1 |]. split; [exact T2 |].
  split; [intros i Hi; apply S1; lia |].
  split; [intros Hp; apply S2; lia |].
  split.
  { intros v Hv' Hin. destruct (S3 v Hv' Hin) as [(i & Hi & Ei) | Ei]; [| right; exact Ei].
    destruct (Z.eq_dec (to_Z i) (to_Z sp - 1)) as [Ei' | Ei'].
    - right. assert (i = sp - 1) by (apply to_Z_inj; lia). subst i. fold u in Ei. subst v. exact Iun.
    - left. exists i. split; [lia | exact Ei]. }
  replace (0 <? sp) with true in LEN by (symmetry; apply Uint63.ltb_spec; change (to_Z 0) with 0%Z; lia).
  fold u in LEN.
  destruct (Z.eq_dec (to_Z sp) 1) as [S11 | S11].
  - assert (sp = 1) by (apply to_Z_inj; exact S11). subst sp.
    replace (0 <? 1 - 1) with false by reflexivity. rewrite PL_0. rewrite PL_1 in LEN.
    assert (U0 : u = 0) by (apply S2; lia). change (1 - 1) with 0 in U0. rewrite U0 in LEN. lra.
  - replace (0 <? sp - 1) with true by (symmetry; apply Uint63.ltb_spec; change (to_Z 0) with 0%Z; lia).
    assert (PLs : PL stk sp = (PL stk (sp - 1) + di stk.[sp - 1 - 1] stk.[sp - 1])%R).
    { pose proof (PL_succ stk (sp - 1) ltac:(lia)) as Q.
      replace (sp - 1 + 1) with sp in Q by (apply to_Z_inj; sia). exact Q. }
    rewrite PLs in LEN. fold u in LEN.
    pose proof (di_tri out.[cnt - 1] u stk.[sp - 1 - 1]). rewrite (di_sym u) in H0. lra.
Qed.


Lemma dfs_step_spec : forall j s, DI j s -> (0 < to_Z (ds_sp s))%Z -> DI (j + 1) (dfs_step nx PA j s).
Proof.
  intros j [[[[it stk] sp] out] cnt] HD Hsp. unfold ds_sp in Hsp; cbn [fst snd] in Hsp.
  unfold dfs_step, ds_it, ds_stk, ds_sp, ds_out, ds_cnt. cbn [fst snd].
  destruct (it.[stk.[sp - 1]] <? nx) eqn:Lc.
  - apply Uint63.ltb_spec in Lc.
    destruct (andb (PA.[it.[stk.[sp - 1]]] =? stk.[sp - 1]) (negb (it.[stk.[sp - 1]] =? 0))) eqn:Pc.
    + apply andb_prop in Pc as [P1 P2]. apply Uint63.eqb_spec in P1.
      apply Bool.negb_true_iff, Uint63.eqb_false_spec in P2.
      apply dfs_push; assumption.
    + apply dfs_scan; try assumption. intros [P1 P2].
      rewrite (proj2 (Uint63.eqb_spec _ _) P1) in Pc.
      rewrite (proj2 (Uint63.eqb_false_spec _ _) P2) in Pc. discriminate.
  - apply dfs_pop; try assumption.
    assert (~ (to_Z it.[stk.[sp - 1]] < to_Z nx)%Z) by (rewrite <- Uint63.ltb_spec; congruence). lia.
Qed.

Lemma sumZ_zero : forall m, sumZ (fun _ => 0%Z) m = 0%Z.
Proof. induction m; simpl; [reflexivity | rewrite IHm; reflexivity]. Qed.

Lemma ind_nonneg : forall it k, (0 <= ind it k)%R.
Proof. intros it k. unfold ind. destruct (_ <? _)%Z; [apply di_nonneg | lra]. Qed.

Definition DS0 : DS := (PArray.make nx 0, PArray.make nx 0, 1, PArray.make nx 0, 1).

Lemma DI_init : DI 0 DS0.
Proof.
  pose proof n_bounds.
  assert (In0 : forall v, InOc (PArray.make nx 0) 1 v -> v = 0).
  { intros v (i & Hi & Ei). rewrite iget_make in Ei. congruence. }
  unfold DS0. unDIg.
  split; [apply ilength_make_n |]. split; [apply ilength_make_n |]. split; [apply ilength_make_n |].
  change (to_Z 1) with 1%Z. split; [lia |]. split; [lia |].
  split.
  { unfold sumit. rewrite (sumZ_ext (fun _ => 0%Z)). - rewrite sumZ_zero. reflexivity.
    - intros k _. rewrite iget_make. reflexivity. }
  split; [intros i _; rewrite iget_make; exact V0 |].
  split; [apply iget_make |].
  split; [intros i i' Hi Hi' _; apply to_Z_inj; pose proof (to_Z_bounded i); pose proof (to_Z_bounded i'); lia |].
  split; [intros v _; rewrite iget_make; change (to_Z 0) with 0%Z; lia |].
  split.
  { intros c Vc Nc. rewrite iget_make. change (to_Z 0) with 0%Z. split.
    - intros Hin. exfalso. exact (Nc (In0 c Hin)).
    - intros Hl. pose proof (to_Z_bounded c). lia. }
  split.
  { intros i Hi. rewrite iget_make. split; [exact V0 |]. exists 0. split; [reflexivity | apply iget_make]. }
  split; [intros _; apply iget_make |].
  split.
  { intros v _ Hin. left. exists 0. split; [reflexivity |]. rewrite iget_make. symmetry. apply In0, Hin. }
  rewrite !PL_1. rewrite !iget_make. replace (0 <? 1) with true by reflexivity.
  rewrite di_self.
  pose proof (sum_below_nonneg (fun k => ind (PArray.make nx 0) (S k)) (NX - 1) (fun k _ => ind_nonneg _ _)).
  lra.
Qed.

Definition HI : int := nx * nx + nx + 1.
Definition SF : DS := loop HI (fun _ s => 0 <? ds_sp s) (dfs_step nx PA) 0 DS0.

Lemma SF_spec : exists j, DI j SF /\ ds_sp SF = 0.
Proof.
  pose proof n_bounds.
  assert (Nb : (to_Z nx * to_Z nx <= 1000000)%Z) by (clear - H; nia).
  assert (Hh : to_Z HI = (to_Z nx * to_Z nx + to_Z nx + 1)%Z) by (unfold HI; sia).
  destruct (loop_inv DI HI 0 (fun _ s => 0 <? ds_sp s) (dfs_step nx PA) DS0) as (j & Hj & Dj & Ej).
  - change (to_Z 0) with 0%Z. lia.
  - exact DI_init.
  - intros j t _ Dt Ct. apply dfs_step_spec; [exact Dt |]. apply Uint63.ltb_spec in Ct. exact Ct.
  - exists j. fold SF in Dj, Ej. split; [exact Dj |].
    destruct Ej as [Ej | [_ Ej]].
    + exfalso. unfold DI in Dj. destruct Dj as (_ & _ & _ & C1 & C2 & J & _ & _ & _ & T1 & _).
      pose proof (sumit_bound _ T1). pose proof (to_Z_bounded (ds_sp SF)). lia.
    + assert (~ (to_Z 0 < to_Z (ds_sp SF))%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      apply to_Z_inj. change (to_Z 0) with 0%Z in *.
      pose proof (to_Z_bounded (ds_sp SF)). lia.
Qed.


(* -- The walk visits every vertex once, within twice the tree -- *)

Definition OUT : array int := ds_out SF.

Lemma walk_final :
  PArray.length OUT = nx /\
  (forall i, (to_Z i < to_Z nx)%Z -> V OUT.[i]) /\ OUT.[0] = 0 /\
  (forall i i', (to_Z i < to_Z nx)%Z -> (to_Z i' < to_Z nx)%Z -> OUT.[i] = OUT.[i'] -> i = i') /\
  (PL OUT nx + di OUT.[nx - 1] 0 <= 2 * W)%R.
Proof.
  pose proof n_bounds. destruct SF_spec as (j & Dj & Sp0).
  unfold DI in Dj. cbv zeta in Dj.
  destruct Dj as (L1 & L2 & L3 & C1 & C2 & J & O1 & O2 & O3 & T1 & T2 & S1 & S2 & S3 & LEN).
  fold OUT in *. set (it := ds_it SF) in *. set (cnt := ds_cnt SF) in *.
  rewrite Sp0 in S3, LEN. change (to_Z 0) with 0%Z in S3.
  replace (0 <? 0) with false in LEN by reflexivity. rewrite PL_0 in LEN.
  unfold InO in T2, S3. fold OUT cnt in T2, S3.
  assert (Fin : forall v, V v -> InOc OUT cnt v -> it.[v] = nx).
  { intros v Vv Hin. destruct (S3 v Vv Hin) as [(i & Hi & _) | E']; [pose proof (to_Z_bounded i); lia | exact E']. }
  assert (All : forall m v, V v -> (Z.to_nat (to_Z RK.[v]) <= m)%nat -> InOc OUT cnt v).
  { induction m as [| m IH]; intros v Vv Hm; (destruct (int_cases v 0) as [-> | Nv0];
      [exists 0; split; [change (to_Z 0) with 0%Z; lia | exact O2] |]).
    - pose proof (RK_pos v Vv Nv0). lia.
    - destruct (PA_spec v Vv Nv0) as (Vp & Rp & _).
      apply (T2 v Vv Nv0). rewrite (Fin _ Vp); [exact Vv |].
      apply IH; [exact Vp | pose proof (to_Z_bounded RK.[PA.[v]]); lia]. }
  assert (All' : forall v, V v -> InOc OUT cnt v)
    by (intros v Vv; apply (All (Z.to_nat (to_Z RK.[v]))); [exact Vv | lia]).
  assert (Cn : cnt = nx).
  { apply to_Z_inj. enough (NX <= Z.to_nat (to_Z cnt))%nat by (unfold NX in *; lia).
    set (CN := Z.to_nat (to_Z cnt)).
    set (o := fun v : nat => fnd (fun i => OUT.[ofn i] =? ofn v) CN).
    assert (Ho : forall v, (v < NX)%nat -> (o v < CN)%nat /\ OUT.[ofn (o v)] = ofn v).
    { intros v Hv'. assert (Vv : V (ofn v)) by (apply V_ofn; unfold NX in *; lia).
      assert (Lt : (o v < CN)%nat).
      { apply fnd_lt. destruct (All' _ Vv) as (i & Hi & Ei).
        exists (Z.to_nat (to_Z i)). split; [unfold CN; lia |].
        rewrite ofn_V by (unfold V; lia). apply Uint63.eqb_spec. exact Ei. }
      split; [exact Lt |]. apply Uint63.eqb_spec. exact (fnd_true _ _ Lt). }
    apply (pigeon_le o).
    - intros i Hi. apply Ho, Hi.
    - intros i i' Hi Hi' E'. destruct (Ho i Hi) as [_ Q]. destruct (Ho i' Hi') as [_ Q'].
      rewrite E' in Q. rewrite Q in Q'. apply (f_equal to_Z) in Q'.
      rewrite !ofn_spec in Q' by (unfold NX in *; lia). lia. }
  rewrite Cn in *.
  assert (Wo : sum_below (fun k => ind it (S k)) (NX - 1) = W).
  { unfold W. apply sum_below_ext. intros k Hk. unfold ind.
    destruct (inv_spec (S k) ltac:(lia)) as [Vz _].
    pose proof (ind_nonzero_v (S k) ltac:(lia)) as Nz.
    destruct (PA_spec _ Vz Nz) as (Vp & _ & _).
    rewrite (Fin _ Vp (All' _ Vp)).
    destruct (Z.ltb_spec (to_Z (inv (S k))) (to_Z nx)); [reflexivity | unfold V in Vz; lia]. }
  rewrite Wo in LEN.
  split; [exact L3 |]. split; [exact O1 |]. split; [exact O2 |]. split; [exact O3 |]. lra.
Qed.

Lemma tsp_unfold : tsp_impl x y = OUT.
Proof. reflexivity. Qed.

Definition TL : list N := map (fun i => Z.to_N (to_Z OUT.[ofn i])) (seq 0 NX).

Lemma TL_length : List.length TL = NX.
Proof. unfold TL. rewrite length_map, length_seq. reflexivity. Qed.

Lemma TL_nth : forall k, (k < NX)%nat -> nth k TL 0%N = Z.to_N (to_Z OUT.[ofn k]).
Proof.
  intros k Hk. apply nth_error_nth. unfold TL. rewrite nth_error_map, nth_error_seq.
  destruct (Nat.ltb_spec k NX); [reflexivity | lia].
Qed.

Lemma tsp_main : exists t : list N, repr (tsp_impl x y : array uint) t /\ tsp_spec xs ys t.
Proof.
  pose proof n_bounds. destruct walk_final as (L & O1 & O2 & O3 & LEN).
  assert (Vk : forall k, (k < NX)%nat -> V OUT.[ofn k]).
  { intros k Hk. apply O1. rewrite ofn_spec by (unfold NX in *; lia). unfold NX in *; lia. }
  assert (Tour : is_tour (len xs) TL).
  { unfold is_tour. split; [| split].
    - unfold len. rewrite TL_length. unfold NX. rewrite <- len_x, Nat2Z.id. reflexivity.
    - apply Forall_forall. intros v Hin. unfold TL in Hin. apply in_map_iff in Hin as (k & <- & Hk).
      apply in_seq in Hk. pose proof (Vk k ltac:(lia)) as Vv. unfold V in Vv. unfold len.
      rewrite <- len_x in Vv. lia.
    - unfold TL. apply seq_NoDup_map. intros i i' Hi Hi' E'.
      pose proof (Vk i Hi). pose proof (Vk i' Hi'). pose proof (to_Z_bounded OUT.[ofn i]).
      pose proof (to_Z_bounded OUT.[ofn i']).
      assert (E2 : OUT.[ofn i] = OUT.[ofn i']) by (apply to_Z_inj; lia).
      apply O3 in E2; [| rewrite ofn_spec; unfold NX in *; lia | rewrite ofn_spec; unfold NX in *; lia].
      apply (f_equal to_Z) in E2. rewrite !ofn_spec in E2 by (unfold NX in *; lia). lia. }
  exists TL. split.
  - rewrite tsp_unfold. split.
    + rewrite TL_length. unfold NX. rewrite Z2Nat.id by lia. symmetry. exact (f_equal to_Z L).
    + intros k Hk. rewrite TL_length in Hk. exists (Z.to_N (to_Z OUT.[ofn k])). split.
      * unfold TL. rewrite nth_error_map, nth_error_seq.
        destruct (Nat.ltb_spec k NX); [reflexivity | lia].
      * reflexivity.
  - split; [exact Tour |]. intros u Hu.
    apply Rle_trans with (2 * W)%R; [| pose proof (W_le_tour u Hu); lra].
    unfold tour_length. rewrite TL_length. cbv zeta.
    replace NX with (S (NX - 1)) at 1 by (unfold NX in *; lia).
    rewrite sum_below_S.
    assert (Eq1 : sum_below (fun k => dist xs ys (nth k TL 0%N) (nth ((k + 1) mod NX) TL 0%N)) (NX - 1)
                  = PL OUT nx).
    { unfold PL. replace (Z.to_nat (to_Z nx) - 1)%nat with (NX - 1)%nat by reflexivity.
      apply sum_below_ext. intros k Hk. rewrite Nat.mod_small by lia.
      rewrite !TL_nth by lia. replace (k + 1)%nat with (S k) by lia. reflexivity. }
    rewrite Eq1.
    replace (NX - 1 + 1)%nat with NX by (unfold NX in *; lia). rewrite Nat.Div0.mod_same by (unfold NX in *; lia).
    rewrite !TL_nth by (unfold NX in *; lia).
    change (dist xs ys (Z.to_N (to_Z OUT.[ofn (NX - 1)])) (Z.to_N (to_Z OUT.[ofn 0])))
      with (di OUT.[ofn (NX - 1)] OUT.[ofn 0]).
    replace (ofn 0) with 0 by reflexivity. rewrite O2.
    replace (ofn (NX - 1)) with (nx - 1) by (apply to_Z_inj; rewrite ofn_spec by (unfold NX; lia); unfold NX; sia).
    lra.
Qed.

End Main.

Definition tsp : array float -> array float -> array uint := tsp_impl.

Lemma tsp_correct :
  forall (xs ys : list R) (x y : array float),
    valid_input xs ys -> repr x xs -> repr y ys ->
    exists t : list N, repr (tsp x y) t /\ tsp_spec xs ys t.
Proof. intros xs ys x y Hv Hx Hy. exact (tsp_main xs ys x y Hv Hx Hy). Qed.
