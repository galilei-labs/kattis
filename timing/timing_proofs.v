(* Correctness proofs for timing_implem.v. *)
(* Implementation of timing.spec (steering v3): the t time units
   simulated one by one in binary64, a per-fort error bound accumulated at
   run time in floats rounded upward, and the exact computation of the
   first try as the fallback.

   MAIN PATH ([timing_impl], Part 3 at the end of the file).
   - once: [cnt_step] counts the non-self links touching each fort (an
     [array int]), [out_step] sums the fraction leaving each fort (an
     [array float]).
   - [tstep], t times, on (v, e, ok): v the strengths (one flat
     [array float]), e one error bound per fort (0 at the start: the inputs
     are the exact floats the spec reads), ok a flag.  [unit_f] (try 2,
     unchanged) copies v and scatters every link j (s -> d, s <> d):
     a := p_j * v[s]; w[d] += a; w[s] -= a, every product from the
     start-of-unit v.  [ebound] then makes one pass over the links
     ([elink]: Ein[d] += p_j * e[s]; Mac[s], Mac[d] += |a|) and one over
     the forts ([efort]):
        e'[x] = up( coef_x * e[x] + Ein[x] + k_x * (|v[x]| + Mac[x] + 1) )
     coef_x = |1 - out_x| + 2^-30 (an upper bound of |1 - out_x|),
     k_x = (2 cnt_x + 3) u, u = 2^-52, up(y) = y * (1 + 2^-30) + 2^-52.
     ok drops to false (and stays false) as soon as some e'[x] > 1.
   - the faced value of each fort in floats ([faced_f], try 2) and their
     minimum o ([fmin]); per fort, [fpair] sums e and |v| over the fort and
     the forts joined to it, and F_i = up(E_i + (N+1) u (M_i + 1))
     ([fbound]); B = max_i F_i ([gmax]).
   - [fcheck]: o is returned when ok and (B < 2^-20, an absolute error
     below 10^-6, or B (2^20 + 1) < o, a relative one), compared exactly
     over Z on the dyadic values of B and o (try 2's [fex], [dlt]).
     Otherwise the fallback runs.

   PROOF.  [ap k x X]: the float x and the real X >= 0 are within the
   factor (1+u)^k (and k eta) of each other, both ways; it goes through
   the rounded add and mul of nonneg values ([ap_add], [ap_mulc],
   [ap_mul0]) and [up] turns it into fval (up x) >= X ([ap_up]).  The link
   pass and the fort pass ([elink_spec], [ebound_spec]) give
   fval e'[x] >= Sx: coef_x e[x] + sum_{d_j = x} p_j e[s_j] +
   k_x (|v[x]| + sum of the |a| touching x + 1).  Against the exact step
   ([unit_err], from try 2's [unit_spec] and [Am_apply]) the new error at
   x is at most |1 - out_x| |err x| + sum_{d_j = x, s_j <> x} p_j |err s_j|
   + (2 cnt_x + 2) u (M_x + 1), M_x = |v x| + the transfers touching x.
   Induction over the units ([sim_inv]): |v_k(i) - strength k i| <= e_k(i)
   <= 1.  The faced sums add N u (M_i + 1) ([faced_f_spec2], per fort), so
   every computed faced value is within F_i <= B of the exact one, and the
   computed minimum within B of the true minimum.

   FALLBACK (Part 1, from ../implem-bens-1, renamed [timing_exact]):
   matrix exponentiation by squaring, Strassen products, in fixed point
   over Z at scale 2^-96.

   Exact arithmetic: in the fallback (Z bignums) and in [fcheck] (the
   comparison of B and o over Z, once).  The main path's strengths,
   fractions, error bounds and faced values are floats only.

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Respeced Require Import Repr ReprFloat.
From Flocq Require Core.Core IEEE754.BinarySingleNaN IEEE754.PrimFloat.
Import ListNotations.

Open Scope uint63_scope.
Unset Lia Cache.

Require Export timing_implem.
Open Scope uint63_scope.


(* ------------------------------------------------------------------ *)
(* Loop and array plumbing                                             *)
(* ------------------------------------------------------------------ *)

Ltac snia := zify; Z.to_euclidean_division_equations; nia.

Section LoopProof.
Context {St : Type}.

Lemma wloop_eq : forall (hi : int) (f : int -> St -> St) i s H,
  wloop hi f i s H =
  match bdec (i <? hi) with
  | left Hi => wloop hi f (i + 1) (f i s) (Acc_inv H (dec_step hi i Hi))
  | right _ => s
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma for_inv : forall (P : int -> St -> Prop) (hi lo : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (loop hi f lo s).
Proof.
  intros P hi lo f s Hle Hp Hstep. unfold loop.
  assert (G : forall n i t (H : Acc (Zwf 0) (gap hi i)), gap hi i = n ->
     (to_Z lo <= to_Z i <= to_Z hi)%Z -> P i t -> P hi (wloop hi f i t H)).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i t H En Hi Pt. rewrite wloop_eq. destruct (bdec (i <? hi)) as [Hlt | Hge].
    - pose proof Hlt as Hlt'. rewrite Uint63.ltb_spec in Hlt'.
      apply (IH (gap hi (i + 1))).
      + rewrite <- En. apply dec_step; exact Hlt.
      + reflexivity.
      + pose proof (to_Z_bounded hi).
        assert (to_Z (i + 1) = (to_Z i + 1)%Z) by sia. lia.
      + apply Hstep; auto; lia.
    - assert (~ (to_Z i < to_Z hi)%Z) by (rewrite <- Uint63.ltb_spec; congruence).
      assert (i = hi) by (apply to_Z_inj; lia). subst i. exact Pt. }
  apply (G _ lo s _ eq_refl); [lia | exact Hp].
Qed.

End LoopProof.

Lemma max_length_val : to_Z PArray.max_length = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alen_make : forall (n : int) (v : Z), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  transitivity (if n <=? max_length then n else max_length); [exact (length_make Z n v)|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec, max_length_val. exact H.
Qed.

Lemma alen_makeb : forall (n : int) (v : bool), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  transitivity (if n <=? max_length then n else max_length); [exact (length_make bool n v)|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec, max_length_val. exact H.
Qed.

Lemma zlen_set : forall (t : array Z) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set Z t i v). Qed.
Lemma zget_set_same : forall (t : array Z) i v,
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros. exact (get_set_same Z t i v H). Qed.
Lemma zget_set_other : forall (t : array Z) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros. exact (get_set_other Z t i j v H). Qed.
Lemma blen_set : forall (t : array bool) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set bool t i v). Qed.
Lemma bget_set_same : forall (t : array bool) i v,
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros. exact (get_set_same bool t i v H). Qed.
Lemma bget_set_other : forall (t : array bool) i j v, i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros. exact (get_set_other bool t i j v H). Qed.

Lemma build_spec : forall (len : int) (f : int -> Z), (to_Z len <= 4194303)%Z ->
  PArray.length (build len f) = len /\
  forall k, (to_Z k < to_Z len)%Z -> (build len f).[k] = f k.
Proof.
  intros len f Hlen. unfold build.
  apply (for_inv (fun i (a : array Z) => PArray.length a = len /\
            forall k, (to_Z k < to_Z i)%Z -> a.[k] = f k)).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded len). lia.
  - split; [apply alen_make; exact Hlen|]. intros k Hk.
    change (to_Z 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
  - intros j a Hj [Hl Hc]. split; [rewrite zlen_set; exact Hl|].
    intros k Hk.
    assert (to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    destruct (Z.eq_dec (to_Z k) (to_Z j)) as [E | E].
    + apply to_Z_inj in E. subst k. apply zget_set_same.
      rewrite Uint63.ltb_spec, Hl. lia.
    + rewrite zget_set_other by (intros F; subst; contradiction).
      apply Hc. lia.
Qed.

Lemma build_len : forall (len : int) (f : int -> Z), (to_Z len <= 4194303)%Z ->
  PArray.length (build len f) = len.
Proof. intros. apply build_spec; assumption. Qed.

Lemma build_get : forall (len : int) (f : int -> Z) k, (to_Z len <= 4194303)%Z ->
  (to_Z k < to_Z len)%Z -> (build len f).[k] = f k.
Proof. intros. apply build_spec; assumption. Qed.

(* ------------------------------------------------------------------ *)
(* Integer matrices, mathematically                                    *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.

(* f 0 + ... + f (n-1) *)
Fixpoint zs (f : Z -> Z) (n : nat) : Z :=
  match n with O => 0 | S k => zs f k + f (Z.of_nat k) end.

Lemma zs_ext : forall f g n, (forall k, 0 <= k < Z.of_nat n -> f k = g k) -> zs f n = zs g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma zs_add : forall f g n, zs (fun k => f k + g k) n = zs f n + zs g n.
Proof. intros f g n. induction n; simpl; [reflexivity | rewrite IHn; ring]. Qed.

Lemma zs_sub : forall f g n, zs (fun k => f k - g k) n = zs f n - zs g n.
Proof. intros f g n. induction n; simpl; [reflexivity | rewrite IHn; ring]. Qed.

Lemma zs_split : forall f a b,
  zs f (a + b) = zs f a + zs (fun k => f (k + Z.of_nat a)) b.
Proof.
  intros f a b. induction b as [|b IH]; simpl.
  - rewrite Nat.add_0_r. ring.
  - rewrite Nat.add_succ_r. simpl. rewrite IH. rewrite Nat2Z.inj_add. ring_simplify.
    f_equal. f_equal. lia.
Qed.

Definition zmm (s : nat) (A B : Z -> Z -> Z) (i j : Z) : Z :=
  zs (fun k => A i k * B k j) s.

Lemma zmm_addl : forall s A B C i j,
  zmm s (fun a b => A a b + B a b) C i j = zmm s A C i j + zmm s B C i j.
Proof. intros. unfold zmm. rewrite <- zs_add. apply zs_ext. intros. ring. Qed.
Lemma zmm_subl : forall s A B C i j,
  zmm s (fun a b => A a b - B a b) C i j = zmm s A C i j - zmm s B C i j.
Proof. intros. unfold zmm. rewrite <- zs_sub. apply zs_ext. intros. ring. Qed.
Lemma zmm_addr : forall s A B C i j,
  zmm s C (fun a b => A a b + B a b) i j = zmm s C A i j + zmm s C B i j.
Proof. intros. unfold zmm. rewrite <- zs_add. apply zs_ext. intros. ring. Qed.
Lemma zmm_subr : forall s A B C i j,
  zmm s C (fun a b => A a b - B a b) i j = zmm s C A i j - zmm s C B i j.
Proof. intros. unfold zmm. rewrite <- zs_sub. apply zs_ext. intros. ring. Qed.

Ltac zmm_lin := repeat (rewrite ?zmm_addl, ?zmm_subl, ?zmm_addr, ?zmm_subr).

Lemma strassen_11 : forall h (x11 x12 x22 y11 y21 y22 : Z -> Z -> Z) i j,
  zmm h (fun a b => x11 a b + x22 a b) (fun a b => y11 a b + y22 a b) i j
  + zmm h x22 (fun a b => y21 a b - y11 a b) i j
  - zmm h (fun a b => x11 a b + x12 a b) y22 i j
  + zmm h (fun a b => x12 a b - x22 a b) (fun a b => y21 a b + y22 a b) i j
  = zmm h x11 y11 i j + zmm h x12 y21 i j.
Proof. intros. zmm_lin. ring. Qed.

Lemma strassen_12 : forall h (x11 x12 y12 y22 : Z -> Z -> Z) i j,
  zmm h x11 (fun a b => y12 a b - y22 a b) i j
  + zmm h (fun a b => x11 a b + x12 a b) y22 i j
  = zmm h x11 y12 i j + zmm h x12 y22 i j.
Proof. intros. zmm_lin. ring. Qed.

Lemma strassen_21 : forall h (x21 x22 y11 y21 : Z -> Z -> Z) i j,
  zmm h (fun a b => x21 a b + x22 a b) y11 i j
  + zmm h x22 (fun a b => y21 a b - y11 a b) i j
  = zmm h x21 y11 i j + zmm h x22 y21 i j.
Proof. intros. zmm_lin. ring. Qed.

Lemma strassen_22 : forall h (x11 x21 x22 y11 y12 y22 : Z -> Z -> Z) i j,
  zmm h (fun a b => x11 a b + x22 a b) (fun a b => y11 a b + y22 a b) i j
  - zmm h (fun a b => x21 a b + x22 a b) y11 i j
  + zmm h x11 (fun a b => y12 a b - y22 a b) i j
  + zmm h (fun a b => x21 a b - x11 a b) (fun a b => y11 a b + y12 a b) i j
  = zmm h x21 y12 i j + zmm h x22 y22 i j.
Proof. intros. zmm_lin. ring. Qed.

Lemma zmm_ext : forall n A A' B B' i j,
  (forall k, 0 <= k < Z.of_nat n -> A i k = A' i k) ->
  (forall k, 0 <= k < Z.of_nat n -> B k j = B' k j) ->
  zmm n A B i j = zmm n A' B' i j.
Proof.
  intros n A A' B B' i j HA HB. unfold zmm. apply zs_ext. intros k Hk.
  rewrite HA, HB by exact Hk. reflexivity.
Qed.

Lemma zmm_block : forall h X Y i j, 0 <= h ->
  zmm (Z.to_nat h + Z.to_nat h) X Y i j
  = zmm (Z.to_nat h) X Y i j
    + zmm (Z.to_nat h) (fun a b => X a (b + h)) (fun a b => Y (a + h) b) i j.
Proof.
  intros h X Y i j Hh. unfold zmm. rewrite zs_split. f_equal.
  apply zs_ext. intros k Hk. rewrite Z2Nat.id by exact Hh. reflexivity.
Qed.

(* the matrix stored in a flat array, row length s *)
Definition getM (X : array Z) (s i j : Z) : Z := X.[of_Z (i * s + j)].

Lemma getM_idx : forall X s i j (k : int), to_Z k = i * s + j -> X.[k] = getM X s i j.
Proof. intros X s i j k H. unfold getM. rewrite <- H, of_to_Z. reflexivity. Qed.

Lemma to_Z_of_Z_small : forall z, 0 <= z < wB -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_val : wB = 9223372036854775808.
Proof. reflexivity. Qed.

Lemma divmod_ij : forall s i j, 0 <= j < s -> (i * s + j) / s = i /\ (i * s + j) mod s = j.
Proof.
  intros s i j H. split.
  - rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. ring.
  - rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma idx2 : forall i h j : int, 0 <= to_Z i * to_Z h + to_Z j < wB ->
  to_Z (i * h + j) = to_Z i * to_Z h + to_Z j.
Proof.
  intros i h j H. pose proof (to_Z_bounded i). pose proof (to_Z_bounded h). pose proof (to_Z_bounded j).
  rewrite Uint63.add_spec, Uint63.mul_spec.
  rewrite (Z.mod_small (to_Z i * to_Z h)) by nia. apply Z.mod_small. exact H.
Qed.

(* R holds the h*h matrix F *)
Definition eqr (h : Z) (R : array Z) (F : Z -> Z -> Z) : Prop :=
  to_Z (PArray.length R) = h * h /\
  forall a b, 0 <= a < h -> 0 <= b < h -> getM R h a b = F a b.

Lemma eqr_ext : forall h R F G, eqr h R F ->
  (forall a b, 0 <= a < h -> 0 <= b < h -> F a b = G a b) -> eqr h R G.
Proof. intros h R F G [L E] H. split; [exact L|]. intros. rewrite E by assumption. auto. Qed.

(* building an h*h matrix entry by entry *)
Lemma build_mat : forall (h : int) (f : int -> Z) (F : Z -> Z -> Z),
  to_Z h * to_Z h <= 4194303 ->
  (forall a b (k : int), 0 <= a < to_Z h -> 0 <= b < to_Z h -> to_Z k = a * to_Z h + b ->
     f k = F a b) ->
  eqr (to_Z h) (build (h * h) f) F.
Proof.
  intros h f F Hb Hf. pose proof (to_Z_bounded h).
  assert (Hhh : to_Z (h * h) = to_Z h * to_Z h) by snia.
  split.
  - rewrite build_len by lia. exact Hhh.
  - intros a b Ha Hb'. unfold getM.
    assert (Hk : to_Z (of_Z (a * to_Z h + b)) = a * to_Z h + b)
      by (apply to_Z_of_Z_small; rewrite wB_val; nia).
    rewrite build_get by (try rewrite Hk; try rewrite Hhh; nia).
    apply Hf; assumption.
Qed.

Lemma dot_spec : forall (s : int) X Y (i j : int),
  to_Z s * to_Z s <= 4194303 -> to_Z i < to_Z s -> to_Z j < to_Z s ->
  dot s X Y i j = zmm (Z.to_nat (to_Z s)) (getM X (to_Z s)) (getM Y (to_Z s)) (to_Z i) (to_Z j).
Proof.
  intros s X Y i j Hb Hi Hj. unfold dot, zmm.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  apply (for_inv (fun k acc => acc = zs (fun c => getM X (to_Z s) (to_Z i) c * getM Y (to_Z s) c (to_Z j))
                                     (Z.to_nat (to_Z k)))).
  - change (to_Z 0) with 0. lia.
  - reflexivity.
  - intros k acc Hk ->. change (to_Z 0) with 0 in Hk.
    assert (E : to_Z (k + 1) = to_Z k + 1) by sia. rewrite E.
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia.
    f_equal. f_equal; apply getM_idx; snia.
Qed.

Lemma naive_spec : forall (s : int) X Y, to_Z s * to_Z s <= 4194303 ->
  eqr (to_Z s) (naive s X Y) (zmm (Z.to_nat (to_Z s)) (getM X (to_Z s)) (getM Y (to_Z s))).
Proof.
  intros s X Y Hb. unfold naive. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. pose proof (to_Z_bounded s).
  destruct (divmod_ij (to_Z s) a b Hb') as [D M].
  rewrite dot_spec by (rewrite ?Uint63.div_spec, ?Uint63.mod_spec, ?Hk, ?D, ?M; lia).
  rewrite Uint63.div_spec, Uint63.mod_spec, Hk, D, M. reflexivity.
Qed.

Lemma quad_spec : forall X (s h di dj : int),
  to_Z s * to_Z s <= 4194303 ->
  to_Z di + to_Z h <= to_Z s -> to_Z dj + to_Z h <= to_Z s ->
  eqr (to_Z h) (quad X s h di dj) (fun a b => getM X (to_Z s) (a + to_Z di) (b + to_Z dj)).
Proof.
  intros X s h di dj Hb H1 H2. unfold quad.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded h).
  pose proof (to_Z_bounded di). pose proof (to_Z_bounded dj).
  apply build_mat; [nia|].
  intros a b k Ha Hb' Hk.
  destruct (divmod_ij (to_Z h) a b Hb') as [D M].
  apply getM_idx.
  assert (Ed : to_Z (k / h) = a) by (rewrite Uint63.div_spec, Hk; exact D).
  assert (Em : to_Z (k mod h) = b) by (rewrite Uint63.mod_spec, Hk; exact M).
  assert (E1 : to_Z (di + k / h) = to_Z di + a) by (rewrite Uint63.add_spec, Ed; apply Z.mod_small; rewrite wB_val; lia).
  assert (E2 : to_Z (dj + k mod h) = to_Z dj + b) by (rewrite Uint63.add_spec, Em; apply Z.mod_small; rewrite wB_val; lia).
  assert (P1 : (to_Z di + a) * to_Z s <= (to_Z s - 1) * to_Z s) by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite Uint63.add_spec, Uint63.mul_spec, E1, E2.
  rewrite (Z.mod_small ((to_Z di + a) * to_Z s)) by (rewrite wB_val; lia).
  rewrite Z.mod_small by (rewrite wB_val; lia). ring.
Qed.

Lemma madd_spec : forall (h : int) A B F G, to_Z h * to_Z h <= 4194303 ->
  eqr (to_Z h) A F -> eqr (to_Z h) B G ->
  eqr (to_Z h) (madd h A B) (fun a b => F a b + G a b).
Proof.
  intros h A B F G Hb [_ EA] [_ EB]. unfold madd. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. rewrite (getM_idx A (to_Z h) a b k Hk), (getM_idx B (to_Z h) a b k Hk).
  rewrite EA, EB by assumption. reflexivity.
Qed.

Lemma msub_spec : forall (h : int) A B F G, to_Z h * to_Z h <= 4194303 ->
  eqr (to_Z h) A F -> eqr (to_Z h) B G ->
  eqr (to_Z h) (msub h A B) (fun a b => F a b - G a b).
Proof.
  intros h A B F G Hb [_ EA] [_ EB]. unfold msub. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. rewrite (getM_idx A (to_Z h) a b k Hk), (getM_idx B (to_Z h) a b k Hk).
  rewrite EA, EB by assumption. reflexivity.
Qed.

Lemma comb_spec : forall (s h : int) C11 C12 C21 C22 F11 F12 F21 F22,
  to_Z s * to_Z s <= 4194303 -> to_Z s = 2 * to_Z h ->
  eqr (to_Z h) C11 F11 -> eqr (to_Z h) C12 F12 -> eqr (to_Z h) C21 F21 -> eqr (to_Z h) C22 F22 ->
  eqr (to_Z s) (comb s h C11 C12 C21 C22)
    (fun i j => if i <? to_Z h then (if j <? to_Z h then F11 i j else F12 i (j - to_Z h))
                else (if j <? to_Z h then F21 (i - to_Z h) j else F22 (i - to_Z h) (j - to_Z h))).
Proof.
  intros s h C11 C12 C21 C22 F11 F12 F21 F22 Hb Hs [_ E11] [_ E12] [_ E21] [_ E22].
  unfold comb. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. pose proof (to_Z_bounded s). pose proof (to_Z_bounded h).
  assert (Hhh : to_Z h * to_Z h <= 4194303) by nia.
  destruct (divmod_ij (to_Z s) a b Hb') as [D M].
  assert (Ed : to_Z (k / s) = a) by (rewrite Uint63.div_spec, Hk; exact D).
  assert (Em : to_Z (k mod s) = b) by (rewrite Uint63.mod_spec, Hk; exact M).
  cbv zeta.
  assert (Li : (k / s <? h)%uint63 = (a <? to_Z h)).
  { destruct (k / s <? h)%uint63 eqn:E1; destruct (a <? to_Z h) eqn:E2; try reflexivity;
      [rewrite Uint63.ltb_spec in E1; rewrite Z.ltb_ge in E2
      | rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E1; rewrite Z.ltb_lt in E2]; lia. }
  assert (Lj : (k mod s <? h)%uint63 = (b <? to_Z h)).
  { destruct (k mod s <? h)%uint63 eqn:E1; destruct (b <? to_Z h) eqn:E2; try reflexivity;
      [rewrite Uint63.ltb_spec in E1; rewrite Z.ltb_ge in E2
      | rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E1; rewrite Z.ltb_lt in E2]; lia. }
  rewrite Li, Lj.
  destruct (a <? to_Z h) eqn:Ea; destruct (b <? to_Z h) eqn:Eb;
    [rewrite Z.ltb_lt in Ea, Eb | rewrite Z.ltb_lt in Ea; rewrite Z.ltb_ge in Eb
    | rewrite Z.ltb_ge in Ea; rewrite Z.ltb_lt in Eb | rewrite Z.ltb_ge in Ea, Eb].
  - rewrite <- E11 by lia. apply getM_idx.
    rewrite idx2, Ed, Em; [reflexivity|]. rewrite Ed, Em. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia|].
    assert (a * to_Z h <= to_Z h * to_Z h) by (apply Z.mul_le_mono_nonneg_r; lia). rewrite wB_val; lia.
  - rewrite <- E12 by lia. apply getM_idx.
    assert (Es : to_Z (k mod s - h) = b - to_Z h) by (rewrite Uint63.sub_spec, Em; apply Z.mod_small; lia).
    rewrite idx2, Ed, Es; [reflexivity|]. rewrite Ed, Es. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia|].
    assert (a * to_Z h <= to_Z h * to_Z h) by (apply Z.mul_le_mono_nonneg_r; lia). rewrite wB_val; lia.
  - rewrite <- E21 by lia. apply getM_idx.
    assert (Es : to_Z (k / s - h) = a - to_Z h) by (rewrite Uint63.sub_spec, Ed; apply Z.mod_small; lia).
    rewrite idx2, Es, Em; [reflexivity|]. rewrite Es, Em. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia|].
    assert ((a - to_Z h) * to_Z h <= to_Z h * to_Z h) by (apply Z.mul_le_mono_nonneg_r; lia). rewrite wB_val; lia.
  - rewrite <- E22 by lia. apply getM_idx.
    assert (Es : to_Z (k / s - h) = a - to_Z h) by (rewrite Uint63.sub_spec, Ed; apply Z.mod_small; lia).
    assert (Es' : to_Z (k mod s - h) = b - to_Z h) by (rewrite Uint63.sub_spec, Em; apply Z.mod_small; lia).
    rewrite idx2, Es, Es'; [reflexivity|]. rewrite Es, Es'. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia|].
    assert ((a - to_Z h) * to_Z h <= to_Z h * to_Z h) by (apply Z.mul_le_mono_nonneg_r; lia). rewrite wB_val; lia.
Qed.

Lemma getM_eq : forall X s i j i' j', i = i' -> j = j' -> getM X s i j = getM X s i' j'.
Proof. intros; subst; reflexivity. Qed.

Lemma strass_eq : forall s X Y H, (strass s X Y H =
  match bdec (splitb s) with
  | left Hs =>
      let h := s / 2 in
      let sr := fun A B => strass h A B (Acc_inv H (dec_split s Hs)) in
      let A11 := quad X s h 0 0 in let A12 := quad X s h 0 h in
      let A21 := quad X s h h 0 in let A22 := quad X s h h h in
      let B11 := quad Y s h 0 0 in let B12 := quad Y s h 0 h in
      let B21 := quad Y s h h 0 in let B22 := quad Y s h h h in
      let M1 := sr (madd h A11 A22) (madd h B11 B22) in
      let M2 := sr (madd h A21 A22) B11 in
      let M3 := sr A11 (msub h B12 B22) in
      let M4 := sr A22 (msub h B21 B11) in
      let M5 := sr (madd h A11 A12) B22 in
      let M6 := sr (msub h A21 A11) (madd h B11 B12) in
      let M7 := sr (msub h A12 A22) (madd h B21 B22) in
      comb s h (madd h (msub h (madd h M1 M4) M5) M7)
               (madd h M3 M5)
               (madd h M2 M4)
               (madd h (madd h (msub h M1 M2) M3) M6)
  | right _ => naive s X Y
  end)%uint63.
Proof. intros. destruct H; reflexivity. Qed.

Ltac blk := unfold zmm; f_equal;
  (apply zs_ext; intros ? ?; cbv beta; f_equal; apply getM_eq; try change (to_Z 0%uint63) with 0%Z; lia).

Lemma strass_spec : forall n (s : int) X Y H, to_Z s = n -> to_Z s * to_Z s <= 4194303 ->
  eqr (to_Z s) (strass s X Y H) (zmm (Z.to_nat (to_Z s)) (getM X (to_Z s)) (getM Y (to_Z s))).
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros s X Y H En Hb. rewrite strass_eq.
  destruct (bdec (splitb s)) as [Hs | Hs]; [| apply naive_spec; exact Hb].
  cbv zeta.
  pose proof (to_Z_bounded s) as Bs.
  assert (Hs' := Hs). unfold splitb in Hs'. apply andb_prop in Hs' as [Hc He].
  unfold cut in Hc. rewrite Uint63.ltb_spec in Hc. change (to_Z 16) with 16 in Hc.
  apply Uint63.eqb_spec in He. apply (f_equal to_Z) in He. rewrite Uint63.mod_spec in He.
  change (to_Z 0) with 0 in He. change (to_Z 2) with 2 in He.
  assert (Hh : to_Z (s / 2)%uint63 = to_Z s / 2) by (rewrite Uint63.div_spec; reflexivity).
  set (h := (s / 2)%uint63) in *.
  assert (H2 : to_Z s = 2 * to_Z h) by (rewrite Hh; pose proof (Z.div_mod (to_Z s) 2); lia).
  assert (Hbh : to_Z h * to_Z h <= 4194303) by nia.
  pose proof (to_Z_bounded h) as Bh.
  assert (SR : forall S T F G, eqr (to_Z h) S F -> eqr (to_Z h) T G ->
            eqr (to_Z h) (strass h S T (Acc_inv H (dec_split s Hs))) (zmm (Z.to_nat (to_Z h)) F G)).
  { intros S T F G [_ ES] [_ ET].
    eapply eqr_ext; [apply (IH (to_Z h)); [unfold Zwf; lia | reflexivity | exact Hbh] |].
    intros a b Ha Hb'. apply zmm_ext; intros k Hk; [apply ES | apply ET]; lia. }
  assert (MA : forall A B F G, eqr (to_Z h) A F -> eqr (to_Z h) B G ->
            eqr (to_Z h) (madd h A B) (fun a b => F a b + G a b))
    by (intros; apply madd_spec; assumption).
  assert (MS : forall A B F G, eqr (to_Z h) A F -> eqr (to_Z h) B G ->
            eqr (to_Z h) (msub h A B) (fun a b => F a b - G a b))
    by (intros; apply msub_spec; assumption).
  assert (Z0 : to_Z 0%uint63 = 0) by reflexivity.
  pose proof (quad_spec X s h 0%uint63 0%uint63 Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QX11.
  pose proof (quad_spec X s h 0%uint63 h Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QX12.
  pose proof (quad_spec X s h h 0%uint63 Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QX21.
  pose proof (quad_spec X s h h h Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QX22.
  pose proof (quad_spec Y s h 0%uint63 0%uint63 Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QY11.
  pose proof (quad_spec Y s h 0%uint63 h Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QY12.
  pose proof (quad_spec Y s h h 0%uint63 Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QY21.
  pose proof (quad_spec Y s h h h Hb ltac:(rewrite ?Z0; lia) ltac:(rewrite ?Z0; lia)) as QY22.
  pose proof (SR _ _ _ _ (MA _ _ _ _ QX11 QX22) (MA _ _ _ _ QY11 QY22)) as M1.
  pose proof (SR _ _ _ _ (MA _ _ _ _ QX21 QX22) QY11) as M2.
  pose proof (SR _ _ _ _ QX11 (MS _ _ _ _ QY12 QY22)) as M3.
  pose proof (SR _ _ _ _ QX22 (MS _ _ _ _ QY21 QY11)) as M4.
  pose proof (SR _ _ _ _ (MA _ _ _ _ QX11 QX12) QY22) as M5.
  pose proof (SR _ _ _ _ (MS _ _ _ _ QX21 QX11) (MA _ _ _ _ QY11 QY12)) as M6.
  pose proof (SR _ _ _ _ (MS _ _ _ _ QX12 QX22) (MA _ _ _ _ QY21 QY22)) as M7.
  pose proof (comb_spec s h _ _ _ _ _ _ _ _ Hb H2
    (MA _ _ _ _ (MS _ _ _ _ (MA _ _ _ _ M1 M4) M5) M7)
    (MA _ _ _ _ M3 M5) (MA _ _ _ _ M2 M4)
    (MA _ _ _ _ (MA _ _ _ _ (MS _ _ _ _ M1 M2) M3) M6)) as HC.
  clear M1 M2 M3 M4 M5 M6 M7.
  eapply eqr_ext; [exact HC |]. clear HC.
  intros a b Ha Hb'. cbv beta.
  assert (En' : Z.to_nat (to_Z s) = (Z.to_nat (to_Z h) + Z.to_nat (to_Z h))%nat) by lia.
  rewrite En', zmm_block by lia.
  destruct (a <? to_Z h) eqn:Ea; destruct (b <? to_Z h) eqn:Eb;
    [rewrite Z.ltb_lt in Ea, Eb | rewrite Z.ltb_lt in Ea; rewrite Z.ltb_ge in Eb
    | rewrite Z.ltb_ge in Ea; rewrite Z.ltb_lt in Eb | rewrite Z.ltb_ge in Ea, Eb].
  - etransitivity; [apply strassen_11 |]. blk.
  - etransitivity; [apply strassen_12 |]. blk.
  - etransitivity; [apply strassen_21 |]. blk.
  - etransitivity; [apply strassen_22 |]. blk.
Qed.

(* the exact product, floored back to 2^-PP *)
Lemma mulr_spec : forall (m : int) X Y, to_Z m * to_Z m <= 4194303 ->
  eqr (to_Z m) (mulr m X Y)
    (fun i j => Z.shiftr (zmm (Z.to_nat (to_Z m)) (getM X (to_Z m)) (getM Y (to_Z m)) i j) PP).
Proof.
  intros m X Y Hb. unfold mulr. cbv zeta. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. f_equal.
  destruct (strass_spec _ m X Y (Zwf_well_founded 0 (to_Z m)) eq_refl Hb) as [_ E].
  rewrite <- E by assumption. apply getM_idx. exact Hk.
Qed.

Lemma ident_spec : forall (m : int), to_Z m * to_Z m <= 4194303 ->
  eqr (to_Z m) (ident m) (fun i j => if i =? j then ONE else 0).
Proof.
  intros m Hb. unfold ident. apply build_mat; [exact Hb|].
  intros a b k Ha Hb' Hk. destruct (divmod_ij (to_Z m) a b Hb') as [D M].
  assert (Ed : to_Z (k / m) = a) by (rewrite Uint63.div_spec, Hk; exact D).
  assert (Em : to_Z (k mod m) = b) by (rewrite Uint63.mod_spec, Hk; exact M).
  destruct (k / m =? k mod m)%uint63 eqn:E; destruct (a =? b) eqn:E'; try reflexivity.
  - apply Uint63.eqb_spec in E. apply Z.eqb_neq in E'. rewrite <- Ed, <- Em, E in E'. lia.
  - apply Uint63.eqb_false_spec in E. apply Z.eqb_eq in E'. exfalso. apply E.
    apply to_Z_inj. lia.
Qed.

(* get after set, by Z indices *)
Lemma zget_set : forall (t : array Z) (p q : int) v, (to_Z p < to_Z (PArray.length t)) ->
  t.[p <- v].[q] = if to_Z p =? to_Z q then v else t.[q].
Proof.
  intros t p q v H. destruct (to_Z p =? to_Z q) eqn:E.
  - apply Z.eqb_eq, to_Z_inj in E. subst q. apply zget_set_same. rewrite Uint63.ltb_spec. exact H.
  - apply Z.eqb_neq in E. apply zget_set_other. intros F. subst. contradiction.
Qed.

Lemma idx_inj : forall m i j d s, 0 <= j < m -> 0 <= s < m -> 0 <= i -> 0 <= d ->
  (i * m + j = d * m + s <-> i = d /\ j = s).
Proof.
  intros m i j d s Hj Hs Hi Hd. split; [| intros [-> ->]; reflexivity].
  intros E. destruct (divmod_ij m i j Hj) as [D1 M1]. destruct (divmod_ij m d s Hs) as [D2 M2].
  rewrite E in D1, M1. split; congruence.
Qed.

Definition indZ (a b : Z) : Z := if a =? b then 1 else 0.

Section Amat.
Variables (m L : int) (xs xd : array uint) (xf : array float).
Hypothesis Hm : to_Z m * to_Z m <= 4194303.
Hypothesis Hsrc : forall l : int, to_Z l < to_Z L -> 0 <= to_Z xs.[l] < to_Z m.
Hypothesis Hdst : forall l : int, to_Z l < to_Z L -> 0 <= to_Z xd.[l] < to_Z m.

Definition Fl (l : Z) : Z := fixv xf.[of_Z l].
Definition sl (l : Z) : Z := to_Z xs.[of_Z l].
Definition dl (l : Z) : Z := to_Z xd.[of_Z l].

Definition Aint (k : nat) (i j : Z) : Z :=
  (if i =? j then ONE else 0) +
  zs (fun l => Fl l * (indZ i (dl l) * indZ j (sl l) - indZ i (sl l) * indZ j (sl l))) k.

Lemma Aint_S : forall k i j, Aint (S k) i j = Aint k i j +
  Fl (Z.of_nat k) * (indZ i (dl (Z.of_nat k)) * indZ j (sl (Z.of_nat k))
                     - indZ i (sl (Z.of_nat k)) * indZ j (sl (Z.of_nat k))).
Proof. intros. unfold Aint. simpl. ring. Qed.

Lemma amat_spec : to_Z L <= 4194303 ->
  eqr (to_Z m) (amat m L xs xd xf) (Aint (Z.to_nat (to_Z L))).
Proof.
  intros HL. unfold amat.
  apply (for_inv (fun l A => eqr (to_Z m) A (Aint (Z.to_nat (to_Z l))))).
  - change (to_Z 0%uint63) with 0. pose proof (to_Z_bounded L). lia.
  - eapply eqr_ext; [apply ident_spec; exact Hm|]. intros a b _ _. unfold Aint. simpl. ring.
  - intros l A Hl [HlA EA]. change (to_Z 0%uint63) with 0 in Hl.
    pose proof (to_Z_bounded m) as Bm. pose proof (to_Z_bounded l) as Bl.
    assert (El : to_Z (l + 1) = to_Z l + 1) by sia.
    destruct (Hsrc l ltac:(lia)) as [Hs1 Hs2]. destruct (Hdst l ltac:(lia)) as [Hd1 Hd2].
    unfold link_step. cbv zeta.
    set (s := xs.[l]). set (d := xd.[l]). set (F := fixv xf.[l]).
    assert (Ids : to_Z (d * m + s) = to_Z d * to_Z m + to_Z s)
      by (apply idx2; assert (to_Z d * to_Z m <= (to_Z m - 1) * to_Z m) by (apply Z.mul_le_mono_nonneg_r; lia);
          rewrite wB_val; lia).
    assert (Iss : to_Z (s * m + s) = to_Z s * to_Z m + to_Z s)
      by (apply idx2; assert (to_Z s * to_Z m <= (to_Z m - 1) * to_Z m) by (apply Z.mul_le_mono_nonneg_r; lia);
          rewrite wB_val; lia).
    assert (Bds : to_Z d * to_Z m + to_Z s < to_Z m * to_Z m)
      by (assert (to_Z d * to_Z m <= (to_Z m - 1) * to_Z m) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
    assert (Bss : to_Z s * to_Z m + to_Z s < to_Z m * to_Z m)
      by (assert (to_Z s * to_Z m <= (to_Z m - 1) * to_Z m) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
    split.
    + rewrite !zlen_set. exact HlA.
    + intros a b Ha Hb'.
      assert (Iab : to_Z (of_Z (a * to_Z m + b)) = a * to_Z m + b)
        by (apply to_Z_of_Z_small; assert (a * to_Z m <= (to_Z m - 1) * to_Z m) by (apply Z.mul_le_mono_nonneg_r; lia);
            rewrite wB_val; lia).
      unfold getM at 1.
      rewrite zget_set by (rewrite zlen_set, HlA, Iss; exact Bss).
      rewrite !(zget_set A (d * m + s)) by (rewrite HlA, Ids; exact Bds).
      rewrite ?Iss, ?Ids, ?Iab.
      rewrite (getM_idx A (to_Z m) (to_Z s) (to_Z s) (s * m + s) Iss).
      rewrite (getM_idx A (to_Z m) (to_Z d) (to_Z s) (d * m + s) Ids).
      fold (getM A (to_Z m) a b).
      replace (Z.to_nat (to_Z (l + 1))) with (S (Z.to_nat (to_Z l))) by lia.
      rewrite Aint_S, Z2Nat.id by lia.
      replace (Fl (to_Z l)) with F by (unfold Fl, F; rewrite of_to_Z; reflexivity).
      replace (sl (to_Z l)) with (to_Z s) by (unfold sl, s; rewrite of_to_Z; reflexivity).
      replace (dl (to_Z l)) with (to_Z d) by (unfold dl, d; rewrite of_to_Z; reflexivity).
      destruct (Z.eqb_spec (to_Z s * to_Z m + to_Z s) (a * to_Z m + b)) as [E1|E1].
      * apply idx_inj in E1; [|lia..]. destruct E1 as [Ea Eb]. subst a b.
        destruct (Z.eqb_spec (to_Z d * to_Z m + to_Z s) (to_Z s * to_Z m + to_Z s)) as [E2|E2].
        -- apply idx_inj in E2; [|lia..]. destruct E2 as [E2 _]. rewrite EA by lia. rewrite E2.
           unfold indZ. rewrite Z.eqb_refl. ring.
        -- rewrite EA by lia. unfold indZ. rewrite Z.eqb_refl.
           destruct (Z.eqb_spec (to_Z s) (to_Z d)) as [E|E]; [exfalso; apply E2; rewrite E; reflexivity|]. ring.
      * destruct (Z.eqb_spec (to_Z d * to_Z m + to_Z s) (a * to_Z m + b)) as [E3|E3].
        -- apply idx_inj in E3; [|lia..]. destruct E3 as [Ea Eb]. subst a b. rewrite EA by lia.
           unfold indZ. rewrite !Z.eqb_refl.
           destruct (Z.eqb_spec (to_Z d) (to_Z s)) as [E|E]; [exfalso; apply E1; rewrite E; reflexivity|]. ring.
        -- rewrite EA by lia. unfold indZ.
           destruct (Z.eqb_spec a (to_Z d)), (Z.eqb_spec b (to_Z s)), (Z.eqb_spec a (to_Z s)); subst;
             try (exfalso; first [apply E3; reflexivity | apply E1; reflexivity]); ring.
Qed.
End Amat.

(* ------------------------------------------------------------------ *)
(* Real matrices and the column-sum norm                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Fixpoint rs (f : Z -> R) (n : nat) : R :=
  match n with O => 0 | S k => rs f k + f (Z.of_nat k) end.

Lemma rs_ext : forall f g n, (forall k, (0 <= k < Z.of_nat n)%Z -> f k = g k) -> rs f n = rs g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma rs_add : forall f g n, rs (fun k => f k + g k) n = rs f n + rs g n.
Proof. intros f g n. induction n; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma rs_sub : forall f g n, rs (fun k => f k - g k) n = rs f n - rs g n.
Proof. intros f g n. induction n; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma rs_scal : forall c f n, rs (fun k => c * f k) n = c * rs f n.
Proof. intros c f n. induction n; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma rs_scal_r : forall c f n, rs (fun k => f k * c) n = rs f n * c.
Proof. intros c f n. induction n; simpl; [ring | rewrite IHn; ring]. Qed.

Lemma rs_le : forall f g n, (forall k, (0 <= k < Z.of_nat n)%Z -> f k <= g k) -> rs f n <= rs g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; simpl; [lra|].
  pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (Z.of_nat n) ltac:(lia)). lra.
Qed.

Lemma rs_nonneg : forall f n, (forall k, (0 <= k < Z.of_nat n)%Z -> 0 <= f k) -> 0 <= rs f n.
Proof.
  intros f n H. replace 0 with (rs (fun _ => 0) n).
  - apply rs_le. exact H.
  - clear H. induction n; simpl; [reflexivity | rewrite IHn; ring].
Qed.

Lemma rs_abs : forall f n, Rabs (rs f n) <= rs (fun k => Rabs (f k)) n.
Proof.
  intros f n. induction n; simpl.
  - rewrite Rabs_R0. lra.
  - eapply Rle_trans; [apply Rabs_triang | lra].
Qed.

Lemma rs_zero : forall n, rs (fun _ => 0) n = 0.
Proof. induction n; simpl; [reflexivity | rewrite IHn; ring]. Qed.

Lemma rs_swap : forall (f : Z -> Z -> R) n1 n2,
  rs (fun i => rs (fun k => f i k) n2) n1 = rs (fun k => rs (fun i => f i k) n1) n2.
Proof.
  intros f n1. induction n1 as [|n1 IH]; intros n2; simpl.
  - symmetry. apply rs_zero.
  - rewrite IH. rewrite <- rs_add. reflexivity.
Qed.

Lemma rs_const_le : forall f n c, (forall k, (0 <= k < Z.of_nat n)%Z -> f k <= c) ->
  rs f n <= INR n * c.
Proof.
  intros f n c. induction n as [|n IH]; intros H; [simpl; lra|].
  pose proof (IH ltac:(intros; apply H; lia)). pose proof (H (Z.of_nat n) ltac:(lia)).
  rewrite S_INR. cbn [rs]. lra.
Qed.

Lemma rs_ind : forall (g : Z -> R) x n,
  rs (fun k => if (k =? x)%Z then g k else 0) n =
  if ((0 <=? x) && (x <? Z.of_nat n))%Z then g x else 0.
Proof.
  intros g x n. induction n as [|n IH]; simpl.
  - destruct (Z.leb_spec 0 x), (Z.ltb_spec x 0); simpl; try reflexivity; lia.
  - rewrite IH. replace (Z.pos (Pos.of_succ_nat n)) with (Z.succ (Z.of_nat n)) by lia.
    destruct (Z.eqb_spec (Z.of_nat n) x) as [E|E].
    + subst x. rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
      rewrite (proj2 (Z.leb_le _ _)) by lia. simpl. ring.
    + destruct (Z.leb_spec 0 x); simpl; [| ring].
      destruct (Z.ltb_spec x (Z.of_nat n)); destruct (Z.ltb_spec x (Z.succ (Z.of_nat n))); try lia; ring.
Qed.

Lemma rs_ind_in : forall (g : Z -> R) x n, (0 <= x < Z.of_nat n)%Z ->
  rs (fun k => if (k =? x)%Z then g k else 0) n = g x.
Proof.
  intros g x n H. rewrite rs_ind.
  rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.

Lemma rs_IZR : forall f n, IZR (zs f n) = rs (fun k => IZR (f k)) n.
Proof. intros f n. induction n; simpl; [reflexivity | rewrite plus_IZR, IHn; reflexivity]. Qed.

Definition Mat := Z -> Z -> R.

Definition mmR (n : nat) (A B : Mat) : Mat := fun i j => rs (fun k => A i k * B k j) n.
Definition dsub (A B : Mat) : Mat := fun i j => A i j - B i j.
Definition colb (n : nat) (A : Mat) (c : R) : Prop :=
  forall j, (0 <= j < Z.of_nat n)%Z -> rs (fun i => Rabs (A i j)) n <= c.

Lemma colb_ext : forall n A B c, (forall i j, (0 <= i < Z.of_nat n)%Z -> (0 <= j < Z.of_nat n)%Z ->
  A i j = B i j) -> colb n A c -> colb n B c.
Proof.
  intros n A B c E H j Hj. rewrite <- (rs_ext (fun i => Rabs (A i j))); [apply H; exact Hj|].
  intros i Hi. rewrite E by assumption. reflexivity.
Qed.

Lemma colb_mono : forall n A c d, c <= d -> colb n A c -> colb n A d.
Proof. intros n A c d Hcd H j Hj. specialize (H j Hj). lra. Qed.

Lemma colb_nonneg : forall n A c, (0 < n)%nat -> colb n A c -> 0 <= c.
Proof.
  intros n A c Hn H. specialize (H 0%Z ltac:(lia)).
  pose proof (rs_nonneg (fun i => Rabs (A i 0%Z)) n ltac:(intros; apply Rabs_pos)). lra.
Qed.

Lemma colb_add : forall n A B a b, colb n A a -> colb n B b ->
  colb n (fun i j => A i j + B i j) (a + b).
Proof.
  intros n A B a b HA HB j Hj.
  eapply Rle_trans; [apply rs_le; intros i _; apply Rabs_triang|].
  rewrite rs_add. pose proof (HA j Hj). pose proof (HB j Hj). lra.
Qed.

Lemma colb_mul : forall n A B a b, 0 <= a -> colb n A a -> colb n B b -> colb n (mmR n A B) (a * b).
Proof.
  intros n A B a b Ha HA HB j Hj. unfold mmR.
  eapply Rle_trans.
  { apply rs_le. intros i _. eapply Rle_trans; [apply rs_abs|].
    apply Req_le. apply rs_ext. intros k _. apply Rabs_mult. }
  rewrite rs_swap.
  eapply Rle_trans.
  { apply rs_le. intros k Hk. rewrite rs_scal_r.
    apply Rmult_le_compat_r; [apply Rabs_pos | apply HA; exact Hk]. }
  rewrite rs_scal. apply Rmult_le_compat_l; [exact Ha | apply HB; exact Hj].
Qed.

Lemma mmR_ext : forall n A A' B B' i j,
  (forall k, (0 <= k < Z.of_nat n)%Z -> A i k = A' i k /\ B k j = B' k j) ->
  mmR n A B i j = mmR n A' B' i j.
Proof.
  intros. unfold mmR. apply rs_ext. intros k Hk. destruct (H k Hk) as [-> ->]. reflexivity.
Qed.

Lemma mmR_assoc : forall n A B C i j, mmR n (mmR n A B) C i j = mmR n A (mmR n B C) i j.
Proof.
  intros. unfold mmR.
  transitivity (rs (fun k => rs (fun l => A i l * B l k * C k j) n) n).
  { apply rs_ext. intros k _. rewrite <- rs_scal_r. reflexivity. }
  rewrite rs_swap. apply rs_ext. intros l _. rewrite <- rs_scal. apply rs_ext. intros k _. ring.
Qed.

(* (XY - AB) = (X - A) Y + A (Y - B) *)
Lemma mm_dist : forall n X Y A B i j,
  dsub (mmR n X Y) (mmR n A B) i j = mmR n (dsub X A) Y i j + mmR n A (dsub Y B) i j.
Proof.
  intros. unfold dsub, mmR. rewrite <- rs_add, <- rs_sub. apply rs_ext. intros. ring.
Qed.

Lemma prod_err : forall n X Y A B ex ey a y, 0 <= ex -> 0 <= a ->
  colb n (dsub X A) ex -> colb n (dsub Y B) ey -> colb n A a -> colb n Y y ->
  colb n (dsub (mmR n X Y) (mmR n A B)) (ex * y + a * ey).
Proof.
  intros n X Y A B ex ey a y Hex Ha HX HY HA HYb.
  eapply colb_ext; [intros i j _ _; symmetry; apply mm_dist|].
  apply colb_add; apply colb_mul; assumption.
Qed.

Lemma colb_tri : forall n X Y W e1 e2, colb n (dsub X Y) e1 -> colb n (dsub Y W) e2 ->
  colb n (dsub X W) (e1 + e2).
Proof.
  intros. eapply colb_ext; [| apply (colb_add _ _ _ _ _ H H0)].
  intros. unfold dsub. ring.
Qed.

Lemma colb_approx : forall n Y B b e, colb n B b -> colb n (dsub Y B) e -> colb n Y (b + e).
Proof.
  intros. eapply colb_ext; [| apply (colb_add _ _ _ _ _ H H0)].
  intros. unfold dsub. ring.
Qed.

Lemma nth_Forall : forall {A} (P : A -> Prop) l k d, Forall P l -> (k < List.length l)%nat -> P (nth k l d).
Proof.
  intros A P l k d H Hk. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Lemma sum_below_rs : forall f n, sum_below f n = rs (fun k => f (Z.to_N k)) n.
Proof.
  intros f n. induction n; simpl; [reflexivity|]. rewrite IHn. f_equal. f_equal. lia.
Qed.

Definition indR (a b : Z) : R := if (a =? b)%Z then 1 else 0.

Lemma indR_sym : forall a b, indR a b = indR b a.
Proof. intros. unfold indR. rewrite Z.eqb_sym. reflexivity. Qed.

Lemma indR_abs : forall a b, Rabs (indR a b) = indR a b.
Proof. intros. unfold indR. destruct (a =? b)%Z; [apply Rabs_R1 | apply Rabs_R0]. Qed.

Lemma rs_indR_r : forall (g : Z -> R) x n, (0 <= x < Z.of_nat n)%Z ->
  rs (fun k => indR k x * g k) n = g x.
Proof.
  intros g x n H. rewrite <- (rs_ind_in g x n H). apply rs_ext. intros k _.
  unfold indR. destruct (k =? x)%Z; ring.
Qed.

Lemma rs_indR_le : forall x n, rs (fun k => indR k x) n <= 1.
Proof.
  intros x n. transitivity (rs (fun k => if (k =? x)%Z then 1 else 0) n); [right; reflexivity|].
  rewrite rs_ind. destruct (_ && _)%Z; lra.
Qed.

Section Galaxy2.
Variables (t : N) (u : list R) (src dst : list N) (frac : list R) (mn : nat).
Hypothesis Hv : valid_input t u src dst frac.
Hypothesis Hmn : (List.length u <= mn)%nat.

Let Lr := List.length src.
Definition fr (l : Z) : R := get_R frac (Z.to_N l).
Definition sr (l : Z) : Z := Z.of_N (get_N src (Z.to_N l)).
Definition dr (l : Z) : Z := Z.of_N (get_N dst (Z.to_N l)).

Lemma len_nat : forall {A} (l : list A), len l = N.of_nat (List.length l).
Proof. reflexivity. Qed.

Lemma sr_range : forall l, (0 <= l < Z.of_nat Lr)%Z -> (0 <= sr l < Z.of_nat (List.length u))%Z.
Proof.
  intros l Hl. destruct Hv as [_ _ _ _ _ _ Hs _ _ _]. unfold sr, get_N.
  pose proof (nth_Forall _ src (N.to_nat (Z.to_N l)) 0%N Hs ltac:(unfold Lr in Hl; lia)) as H.
  cbv beta in H. rewrite len_nat in H. lia.
Qed.

Lemma dr_range : forall l, (0 <= l < Z.of_nat Lr)%Z -> (0 <= dr l < Z.of_nat (List.length u))%Z.
Proof.
  intros l Hl. destruct Hv as [_ _ _ Hdl _ _ _ Hd _ _]. unfold dr, get_N.
  rewrite !len_nat in Hdl. apply Nat2N.inj in Hdl.
  pose proof (nth_Forall _ dst (N.to_nat (Z.to_N l)) 0%N Hd ltac:(unfold Lr in Hl; lia)) as H.
  cbv beta in H. rewrite len_nat in H. lia.
Qed.

Lemma fr_range : forall l, (0 <= l < Z.of_nat Lr)%Z -> 0 < fr l <= 1.
Proof.
  intros l Hl. destruct Hv as [_ _ _ _ Hfl _ _ _ Hf _]. unfold fr, get_R.
  rewrite !len_nat in Hfl. apply Nat2N.inj in Hfl.
  pose proof (nth_Forall _ frac (N.to_nat (Z.to_N l)) 0 Hf ltac:(unfold Lr in Hl; lia)) as H.
  exact H.
Qed.

(* the one-step transfer matrix, padded with the identity *)
Definition Am : Mat := fun i j =>
  indR i j + rs (fun l => fr l * (indR i (dr l) * indR j (sr l) - indR i (sr l) * indR j (sr l))) Lr.

Definition Id : Mat := fun i j => indR i j.

Fixpoint mpow (k : nat) : Mat :=
  match k with O => Id | S k => mmR mn Am (mpow k) end.

Definition gam : R := 1 + 2 / 1000000000.

Lemma colb_Id : colb mn Id 1.
Proof.
  intros j Hj. unfold Id. rewrite (rs_ext _ (fun i => indR i j)) by (intros; apply indR_abs).
  apply rs_indR_le.
Qed.

(* what leaves fort j *)
Definition outj (j : Z) : R :=
  rs (fun l => if ((sr l =? j) && negb (dr l =? j))%Z then fr l else 0) Lr.

Lemma outj_spec : forall j, (0 <= j)%Z -> 0 <= outj j <= 1 + / 1000000000.
Proof.
  intros j Hj. split.
  - apply rs_nonneg. intros l Hl. destruct (_ && _)%Z; [pose proof (fr_range l Hl); lra | lra].
  - destruct (Z_lt_le_dec j (Z.of_nat (List.length u))) as [Hju | Hju].
    + destruct Hv as [_ _ _ _ _ _ _ _ _ Ho].
      specialize (Ho (Z.to_N j) ltac:(rewrite len_nat; lia)).
      unfold outflow in Ho. rewrite sum_below_rs in Ho. unfold outj.
      erewrite rs_ext; [exact Ho|]. intros l Hl. unfold sr, dr.
      replace ((Z.of_N (get_N src (Z.to_N l)) =? j)%Z) with ((get_N src (Z.to_N l) =? Z.to_N j)%N)
        by (destruct (N.eqb_spec (get_N src (Z.to_N l)) (Z.to_N j)), (Z.eqb_spec (Z.of_N (get_N src (Z.to_N l))) j); lia).
      replace ((Z.of_N (get_N dst (Z.to_N l)) =? j)%Z) with ((get_N dst (Z.to_N l) =? Z.to_N j)%N)
        by (destruct (N.eqb_spec (get_N dst (Z.to_N l)) (Z.to_N j)), (Z.eqb_spec (Z.of_N (get_N dst (Z.to_N l))) j); lia).
      reflexivity.
    + unfold outj. rewrite (rs_ext _ (fun _ => 0)); [rewrite rs_zero; lra|].
      intros l Hl. pose proof (sr_range l Hl).
      destruct (Z.eqb_spec (sr l) j); [lia | reflexivity].
Qed.

Lemma Am_split : forall i j, Am i j =
  indR i j * (1 - outj j) +
  rs (fun l => (if ((sr l =? j) && negb (dr l =? j))%Z then fr l else 0) * indR i (dr l)) Lr.
Proof.
  intros i j. unfold Am, outj.
  transitivity (indR i j + rs (fun l => - indR i j * (if ((sr l =? j) && negb (dr l =? j))%Z then fr l else 0)
       + (if ((sr l =? j) && negb (dr l =? j))%Z then fr l else 0) * indR i (dr l)) Lr).
  - f_equal. apply rs_ext. intros l _. unfold indR.
    destruct (Z.eqb_spec (sr l) j), (Z.eqb_spec (dr l) j), (Z.eqb_spec i j), (Z.eqb_spec i (dr l)),
      (Z.eqb_spec i (sr l)), (Z.eqb_spec j (sr l)); subst; simpl; try lia; ring.
  - rewrite rs_add, rs_scal. ring.
Qed.

Lemma colb_Am : colb mn Am gam.
Proof.
  intros j Hj.
  set (c := fun l => if ((sr l =? j) && negb (dr l =? j))%Z then fr l else 0).
  assert (Hc : forall l, (0 <= l < Z.of_nat Lr)%Z -> 0 <= c l).
  { intros l Hl. unfold c. destruct (_ && _)%Z; [pose proof (fr_range l Hl); lra | lra]. }
  eapply Rle_trans.
  { apply rs_le. intros i _. rewrite Am_split. apply Rabs_triang. }
  rewrite rs_add.
  assert (E1 : rs (fun i => Rabs (indR i j * (1 - outj j))) mn = Rabs (1 - outj j)).
  { rewrite (rs_ext _ (fun i => indR i j * Rabs (1 - outj j))).
    - rewrite rs_scal_r. replace (rs (fun i => indR i j) mn) with 1; [ring|].
      transitivity (rs (fun k => if (k =? j)%Z then 1 else 0) mn); [|reflexivity].
      rewrite rs_ind_in by lia. reflexivity.
    - intros i _. rewrite Rabs_mult, indR_abs. reflexivity. }
  rewrite E1.
  assert (E2 : rs (fun i => Rabs (rs (fun l => c l * indR i (dr l)) Lr)) mn <= outj j).
  { eapply Rle_trans; [apply rs_le; intros i _; apply rs_abs|].
    rewrite rs_swap.
    unfold outj. fold c. apply rs_le. intros l Hl.
    rewrite (rs_ext _ (fun i => c l * indR i (dr l))).
    - rewrite rs_scal. pose proof (rs_indR_le (dr l) mn). pose proof (Hc l Hl).
      rewrite <- (Rmult_1_r (c l)) at 2. apply Rmult_le_compat_l; assumption.
    - intros i _. rewrite Rabs_mult, indR_abs, Rabs_right by (apply Rle_ge, Hc, Hl). reflexivity. }
  pose proof (outj_spec j ltac:(lia)).
  eapply Rle_trans; [apply Rplus_le_compat_l; exact E2|].
  unfold gam. destruct (Rle_dec 0 (1 - outj j)); [rewrite Rabs_right | rewrite Rabs_left]; lra.
Qed.

Lemma colb_mpow : forall k, colb mn (mpow k) (gam ^ k).
Proof.
  induction k; simpl.
  - apply colb_Id.
  - apply colb_mul; [unfold gam; lra | apply colb_Am | exact IHk].
Qed.

Lemma Id_l : forall M i j, (0 <= i < Z.of_nat mn)%Z -> mmR mn Id M i j = M i j.
Proof.
  intros M i j Hi. unfold mmR, Id.
  rewrite (rs_ext _ (fun k => indR k i * M k j)).
  - apply (rs_indR_r (fun k => M k j)). exact Hi.
  - intros k _. unfold indR. rewrite Z.eqb_sym. reflexivity.
Qed.

Lemma mpow_add : forall a b i j, (0 <= i < Z.of_nat mn)%Z -> (0 <= j < Z.of_nat mn)%Z ->
  mpow (a + b) i j = mmR mn (mpow a) (mpow b) i j.
Proof.
  induction a as [|a IH]; intros b i j Hi Hj; simpl.
  - symmetry. apply Id_l. exact Hi.
  - rewrite mmR_assoc. apply mmR_ext. intros k Hk. split; [reflexivity|]. apply IH; assumption.
Qed.

Lemma step_mat : forall (v : N -> R) i, (0 <= i < Z.of_nat mn)%Z ->
  step src dst frac v (Z.to_N i) = rs (fun j => Am i j * v (Z.to_N j)) mn.
Proof.
  intros v i Hi.
  assert (R1 : rs (fun j => Am i j * v (Z.to_N j)) mn = v (Z.to_N i) +
     rs (fun l => fr l * (indR i (dr l) * v (Z.to_N (sr l)) - indR i (sr l) * v (Z.to_N (sr l)))) Lr).
  { unfold Am.
    rewrite (rs_ext _ (fun j => indR j i * v (Z.to_N j) +
       rs (fun l => fr l * indR i (dr l) * (indR j (sr l) * v (Z.to_N j))
                    - fr l * indR i (sr l) * (indR j (sr l) * v (Z.to_N j))) Lr)).
    2: { intros j _. rewrite Rmult_plus_distr_r, <- rs_scal_r, (indR_sym i j).
         f_equal. apply rs_ext. intros. ring. }
    rewrite rs_add, (rs_indR_r (fun j => v (Z.to_N j))) by exact Hi. f_equal.
    rewrite rs_swap. apply rs_ext. intros l Hl. pose proof (sr_range l Hl).
    rewrite rs_sub, !rs_scal, !(rs_indR_r (fun j => v (Z.to_N j))) by lia. ring. }
  rewrite R1. unfold step. rewrite !sum_below_rs.
  match goal with |- _ + ?A - ?B = _ + ?C => assert (E : C = A - B); [| rewrite E; ring] end.
  rewrite <- rs_sub. apply rs_ext. intros l Hl. unfold fr, sr, dr, indR. rewrite !N2Z.id.
  destruct (N.eqb_spec (get_N dst (Z.to_N l)) (Z.to_N i)) as [E1|E1],
    (Z.eqb_spec i (Z.of_N (get_N dst (Z.to_N l)))) as [E2|E2],
    (N.eqb_spec (get_N src (Z.to_N l)) (Z.to_N i)) as [E3|E3],
    (Z.eqb_spec i (Z.of_N (get_N src (Z.to_N l)))) as [E4|E4];
    try lia; rewrite ?E3; ring.
Qed.

Lemma strength_mat : forall k i, (0 <= i < Z.of_nat mn)%Z ->
  strength u src dst frac k (Z.to_N i) = rs (fun j => mpow k i j * get_R u (Z.to_N j)) mn.
Proof.
  induction k as [|k IH]; intros i Hi; simpl.
  - unfold Id. rewrite (rs_ext _ (fun j => indR j i * get_R u (Z.to_N j))).
    + rewrite rs_indR_r by exact Hi. reflexivity.
    + intros j _. unfold indR. rewrite Z.eqb_sym. reflexivity.
  - rewrite step_mat by exact Hi.
    rewrite (rs_ext _ (fun j => rs (fun l => Am i j * (mpow k j l * get_R u (Z.to_N l))) mn)).
    2: { intros j Hj. rewrite rs_scal, <- IH by lia. reflexivity. }
    rewrite rs_swap. unfold mmR. apply rs_ext. intros l _. rewrite <- rs_scal_r. apply rs_ext. intros. ring.
Qed.

End Galaxy2.

Lemma pow_bern : forall x k, 0 <= x -> INR k * x <= 1 / 2 -> (1 + x) ^ k <= 1 + 2 * INR k * x.
Proof.
  intros x k Hx. induction k as [|k IH]; intros Hk; [simpl; lra|].
  rewrite S_INR in *. cbn [pow]. pose proof (pos_INR k).
  assert (Hk' : INR k * x <= 1 / 2) by nra.
  specialize (IH Hk').
  assert (0 <= (1 + x) ^ k) by (apply pow_le; lra). nra.
Qed.

Lemma gam_pow : forall k, (Z.of_nat k <= 10000)%Z -> gam ^ k <= 3 / 2.
Proof.
  intros k Hk. apply IZR_le in Hk. rewrite <- INR_IZR_INZ in Hk. pose proof (pos_INR k).
  unfold gam. eapply Rle_trans; [apply pow_bern|]; nra.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact value of a float, fixed point                                 *)
(* ------------------------------------------------------------------ *)

Local Instance prec53' : FLX.Prec_gt_0 53 := eq_refl _.
Local Instance fexp64_valid' : Generic_fmt.Valid_exp fexp64 := FLT.FLT_exp_valid _ _.

Lemma zofi_rec_eq : forall i H, zofi_rec i H =
  match bdec (i =? 0)%uint63 with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if (i mod 2 =? 0)%uint63 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma zofi_spec : forall i, zofi i = to_Z i.
Proof.
  assert (G : forall n i H, to_Z i = n -> zofi_rec i H = to_Z i).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i H En. rewrite zofi_rec_eq. destruct (bdec (i =? 0)%uint63) as [E | E].
    - apply Uint63.eqb_spec in E. subst i. reflexivity.
    - cbv zeta. rewrite (IH (to_Z (i / 2))); [| rewrite <- En; apply dec_half; exact E | reflexivity].
      pose proof (to_Z_bounded i).
      destruct (i mod 2 =? 0)%uint63 eqn:Em.
      + apply Uint63.eqb_spec in Em. apply (f_equal to_Z) in Em. sia.
      + apply Uint63.eqb_false_spec in Em.
        assert (to_Z (i mod 2) <> 0%Z) by (intros E'; apply Em, to_Z_inj; exact E'). sia. }
  intros i. unfold zofi. apply (G _ i _ eq_refl).
Qed.

Local Notation bp := (Raux.bpow Zaux.radix2).

Definition dval (d : Z * Z) : R := (IZR (fst d) * bp (snd d))%R.

Lemma IZR_pow2 : forall k, (0 <= k)%Z -> IZR (2 ^ k) = bp k.
Proof. intros k Hk. destruct k as [| p | p]; [reflexivity | reflexivity | lia]. Qed.

Lemma repr_zero : repr 0%float 0%R.
Proof. split; reflexivity. Qed.

Lemma fex_val : forall (f : float) r, repr f r -> dval (fex f) = r.
Proof.
  intros f r Hf.
  assert (Hs : (f <? 0)%float = Raux.Rlt_bool r 0) by (apply repr_ltb; [exact Hf | exact repr_zero]).
  pose proof Hf as Hf'. apply repr_float_iff in Hf' as [Fin Ev].
  unfold fex. pose proof (Flocq.IEEE754.PrimFloat.frshiftexp_equiv f) as Fr.
  destruct (frshiftexp f) as [z e]. rewrite Hs. unfold dval; simpl fst; simpl snd.
  rewrite !zofi_spec, Flocq.IEEE754.PrimFloat.normfr_mantissa_equiv.
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

(* the scale *)
Definition sc : R := IZR ONE.

Lemma ONE_val : ONE = (2 ^ PP)%Z.
Proof. reflexivity. Qed.

Lemma sc_bp : sc = bp PP.
Proof. unfold sc. rewrite ONE_val. apply IZR_pow2. unfold PP. lia. Qed.

Lemma sc_pos : 0 < sc.
Proof. rewrite sc_bp. apply Raux.bpow_gt_0. Qed.

(* floor (a * 2^k) *)
Lemma shiftl_floor : forall a k,
  IZR (Z.shiftl a k) <= IZR a * bp k < IZR (Z.shiftl a k) + 1.
Proof.
  intros a k. destruct (Z_le_gt_dec 0 k) as [Hk | Hk].
  - rewrite Z.shiftl_mul_pow2 by exact Hk. rewrite mult_IZR, IZR_pow2 by exact Hk. lra.
  - replace k with (- (- k))%Z by lia. rewrite Z.shiftl_opp_r, Z.shiftr_div_pow2 by lia.
    set (K := (- k)%Z). assert (HK : (0 < K)%Z) by (unfold K; lia).
    pose proof (Z.div_mod a (2 ^ K) ltac:(apply Z.pow_nonzero; lia)) as Dm.
    pose proof (Z.mod_pos_bound a (2 ^ K) ltac:(apply Z.pow_pos_nonneg; lia)) as Mb.
    set (q := (a / 2 ^ K)%Z) in *. set (r := (a mod 2 ^ K)%Z) in *.
    assert (Hb : bp (- K) * bp K = 1) by (rewrite <- Raux.bpow_plus; replace (- K + K)%Z with 0%Z by lia; reflexivity).
    assert (HbK : IZR (2 ^ K) = bp K) by (apply IZR_pow2; lia).
    assert (Hp : 0 < bp (- K)) by apply Raux.bpow_gt_0.
    rewrite Dm, plus_IZR, mult_IZR, HbK.
    destruct Mb as [Mb0 Mb2]. apply IZR_lt in Mb2. apply IZR_le in Mb0. rewrite HbK in Mb2.
    split.
    + replace ((bp K * IZR q + IZR r) * bp (- K)) with (IZR q * (bp (- K) * bp K) + IZR r * bp (- K)) by ring.
      rewrite Hb. nra.
    + replace ((bp K * IZR q + IZR r) * bp (- K)) with (IZR q * (bp (- K) * bp K) + IZR r * bp (- K)) by ring.
      rewrite Hb.
      assert (IZR r * bp (- K) < bp K * bp (- K)) by (apply Rmult_lt_compat_r; lra). lra.
Qed.

Lemma fixv_spec : forall (f : float) r, repr f r -> IZR (fixv f) <= r * sc < IZR (fixv f) + 1.
Proof.
  intros f r Hf. rewrite <- (fex_val f r Hf). unfold fixv, dval. rewrite sc_bp.
  rewrite Rmult_assoc, <- Raux.bpow_plus. apply shiftl_floor.
Qed.

Lemma shiftr_floor : forall z, Rabs (IZR (Z.shiftr z PP) / sc - IZR z / (sc * sc)) <= / sc.
Proof.
  intros z. pose proof (shiftl_floor z (- PP)) as H.
  rewrite Z.shiftl_opp_r in H.
  assert (Hb : bp (- PP) = / sc) by (rewrite sc_bp, Raux.bpow_opp; reflexivity).
  rewrite Hb in H. pose proof sc_pos.
  assert (E : IZR z / (sc * sc) = IZR z * / sc * / sc) by (field; lra).
  rewrite E. unfold Rdiv.
  set (q := IZR (Z.shiftr z PP)) in *. set (w := IZR z * / sc) in *.
  assert (Hi : 0 < / sc) by (apply Rinv_0_lt_compat; lra).
  rewrite Rabs_left1.
  - assert (q * / sc <= w * / sc) by (apply Rmult_le_compat_r; lra).
    assert (w * / sc < (q + 1) * / sc) by (apply Rmult_lt_compat_r; lra). lra.
  - assert (q * / sc <= w * / sc) by (apply Rmult_le_compat_r; lra). lra.
Qed.

Definition frM (X : array Z) (m : Z) : Mat := fun i j => IZR (getM X m i j) / sc.

Lemma mmR_frM : forall n X Y m i j,
  mmR n (frM X m) (frM Y m) i j = IZR (zmm n (getM X m) (getM Y m) i j) / (sc * sc).
Proof.
  intros. unfold mmR, frM, zmm. rewrite rs_IZR. unfold Rdiv at 3. rewrite <- rs_scal_r.
  pose proof sc_pos. apply rs_ext. intros. rewrite mult_IZR. field. lra.
Qed.

Lemma mulr_err : forall (m : int) X Y, (to_Z m * to_Z m <= 4194303)%Z ->
  colb (Z.to_nat (to_Z m))
    (dsub (frM (mulr m X Y) (to_Z m)) (mmR (Z.to_nat (to_Z m)) (frM X (to_Z m)) (frM Y (to_Z m))))
    (INR (Z.to_nat (to_Z m)) * / sc).
Proof.
  intros m X Y Hb j Hj. apply rs_const_le. intros i Hi.
  destruct (mulr_spec m X Y Hb) as [_ E].
  unfold dsub. rewrite mmR_frM. unfold frM at 1. rewrite E by lia.
  apply shiftr_floor.
Qed.

Lemma IZR_indZ : forall a b, IZR (indZ a b) = indR a b.
Proof. intros. unfold indZ, indR. destruct (a =? b)%Z; reflexivity. Qed.

Lemma indR_le1 : forall a b, 0 <= indR a b <= 1.
Proof. intros. unfold indR. destruct (a =? b)%Z; lra. Qed.

Section Err.
Variables (src dst : list N) (frac : list R) (mn : nat) (xs xd : array uint) (xf : array float).
Let Lr := List.length src.
Hypothesis HA : forall l, (0 <= l < Z.of_nat Lr)%Z ->
  sl xs l = sr src l /\ dl xd l = dr dst l /\ IZR (Fl xf l) <= fr frac l * sc < IZR (Fl xf l) + 1.

Lemma A_err : colb mn (dsub (fun i j => IZR (Aint xs xd xf Lr i j) / sc) (Am src dst frac))
                      (INR Lr * (2 / sc)).
Proof.
  pose proof sc_pos as Hsc.
  set (e := fun l => IZR (Fl xf l) / sc - fr frac l).
  set (G := fun l i j => indR i (dr dst l) * indR j (sr src l) - indR i (sr src l) * indR j (sr src l)).
  assert (He : forall l, (0 <= l < Z.of_nat Lr)%Z -> Rabs (e l) <= / sc).
  { intros l Hl. destruct (HA l Hl) as (_ & _ & H1 & H2). unfold e.
    assert (E1 : IZR (Fl xf l) / sc <= fr frac l).
    { apply (Rmult_le_reg_r sc); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
    assert (E2 : fr frac l < IZR (Fl xf l) / sc + / sc).
    { apply (Rmult_lt_reg_r sc); [lra|]. rewrite Rmult_plus_distr_r. unfold Rdiv.
      rewrite Rmult_assoc, !Rinv_l by lra. lra. }
    rewrite Rabs_left1; lra. }
  eapply colb_ext.
  - intros i j _ _. symmetry.
    instantiate (1 := fun i j => rs (fun l => e l * G l i j) Lr).
    unfold dsub, Am, Aint. rewrite plus_IZR, rs_IZR.
    rewrite (rs_ext _ (fun l => IZR (Fl xf l) * G l i j) Lr).
    2: { intros l Hl. destruct (HA l Hl) as (Es & Ed & _). rewrite mult_IZR, minus_IZR, !mult_IZR, !IZR_indZ.
         rewrite Es, Ed. reflexivity. }
    assert (Ei : IZR (if (i =? j)%Z then ONE else 0) / sc = indR i j).
    { unfold indR. destruct (i =? j)%Z; [fold sc; field; lra | unfold Rdiv; ring]. }
    unfold Rdiv at 1. rewrite Rmult_plus_distr_r. fold (Rdiv (IZR (if (i =? j)%Z then ONE else 0)) sc).
    rewrite Ei. rewrite <- rs_scal_r. fold G.
    rewrite (rs_ext (fun l => fr frac l * _) (fun l => fr frac l * G l i j)) by reflexivity.
    change (Datatypes.length src) with Lr.
    match goal with |- ?a + ?b - (?a + ?c) = _ => replace (a + b - (a + c)) with (b - c) by ring end.
    rewrite <- rs_sub. apply rs_ext. intros. unfold e. unfold Rdiv. ring.
  - intros j Hj.
    eapply Rle_trans; [apply rs_le; intros i _; apply rs_abs|].
    rewrite rs_swap.
    rewrite <- (Rmult_comm (2 / sc)). rewrite Rmult_comm.
    replace (INR Lr * (2 / sc)) with (INR Lr * (/ sc * 2)) by (unfold Rdiv; ring).
    apply rs_const_le. intros l Hl.
    rewrite (rs_ext _ (fun i => Rabs (e l) * Rabs (G l i j))) by (intros; apply Rabs_mult).
    rewrite rs_scal.
    assert (HG : rs (fun i => Rabs (G l i j)) mn <= 2).
    { eapply Rle_trans.
      - apply rs_le. intros i _. instantiate (1 := fun i => indR i (dr dst l) + indR i (sr src l)).
        unfold G. cbv beta.
        pose proof (indR_le1 i (dr dst l)). pose proof (indR_le1 j (sr src l)). pose proof (indR_le1 i (sr src l)).
        unfold Rabs. destruct (Rcase_abs _); nra.
      - rewrite rs_add. pose proof (rs_indR_le (dr dst l) mn). pose proof (rs_indR_le (sr src l) mn). lra. }
    pose proof (He l Hl). pose proof (Rabs_pos (e l)).
    apply Rmult_le_compat; try lra. apply rs_nonneg. intros. apply Rabs_pos.
Qed.

End Err.

Lemma Id_r : forall n M i j, (0 <= j < Z.of_nat n)%Z -> mmR n M Id i j = M i j.
Proof.
  intros n M i j Hj. unfold mmR, Id.
  rewrite (rs_ext _ (fun k => indR k j * M i k)).
  - apply (rs_indR_r (fun k => M i k)). exact Hj.
  - intros k _. ring.
Qed.

Lemma pw_eq : forall m t R B H, pw m t R B H =
  match bdec (t =? 0)%uint63 with
  | left _ => R
  | right Hn =>
      let R' := if (t mod 2 =? 0)%uint63 then R
                else Some (match R with None => B | Some X => mulr m X B end) in
      let t' := (t / 2)%uint63 in
      if (t' =? 0)%uint63 then R' else pw m t' R' (mulr m B B) (Acc_inv H (dec_half t Hn))
  end.
Proof. intros. destruct H; reflexivity. Qed.

Section Pow.
Variables (src dst : list N) (frac : list R) (m : int) (T : nat) (rho : R).
Let mn := Z.to_nat (to_Z m).
Let M := mpow src dst frac mn.
Hypothesis Hm : (to_Z m * to_Z m <= 4194303)%Z.
Hypothesis HT : (Z.of_nat T <= 5000)%Z.
Hypothesis Hrho : 0 <= rho.
Hypothesis Hrnd : INR mn * / sc <= rho.
Hypothesis Hrho8 : rho * 8 ^ 13 <= 1 / 2.
Hypothesis Hnorm : forall k, (Z.of_nat k <= 10000)%Z -> colb mn (M k) (3 / 2).

Definition approx (X : array Z) (k : nat) (e : R) : Prop :=
  to_Z (PArray.length X) = (to_Z m * to_Z m)%Z /\ colb mn (dsub (frM X (to_Z m)) (M k)) e.

Lemma approx_mono : forall X k e e', e <= e' -> approx X k e -> approx X k e'.
Proof. intros X k e e' H [L C]. split; [exact L | eapply colb_mono; eassumption]. Qed.

Lemma approx_mul : forall X Y a b ex ey, approx X a ex -> approx Y b ey ->
  (Z.of_nat (a + b) <= 10000)%Z -> 0 <= ex <= 1 / 2 -> 0 <= ey <= 1 / 2 ->
  approx (mulr m X Y) (a + b) (2 * ex + 2 * ey + rho).
Proof.
  intros X Y a b ex ey [LX CX] [LY CY] Hab Hex Hey. split.
  - unfold mulr. cbv zeta. rewrite build_len by snia. pose proof (to_Z_bounded m). snia.
  - apply (colb_mono _ _ (INR mn * / sc + (ex * 2 + 3 / 2 * ey))); [lra|].
    apply (colb_tri _ _ (mmR mn (frM X (to_Z m)) (frM Y (to_Z m)))).
    + apply mulr_err. exact Hm.
    + eapply colb_ext; [| apply (prod_err mn (frM X (to_Z m)) (frM Y (to_Z m)) (M a) (M b) ex ey (3 / 2) 2); try eassumption].
      * intros i j Hi Hj. unfold dsub. f_equal. symmetry. apply mpow_add; assumption.
      * lra.
      * lra.
      * apply Hnorm. lia.
      * apply (colb_mono _ _ (3 / 2 + ey)); [lra|]. apply (colb_approx _ _ (M b)); [apply Hnorm; lia | exact CY].
Qed.

Lemma pow8_ge1 : forall i, 1 <= 8 ^ i.
Proof. intros i. induction i; simpl; lra. Qed.

Lemma pow8_mono : forall i j, (i <= j)%nat -> 8 ^ i <= 8 ^ j.
Proof.
  intros i j H. induction H; [lra|]. simpl. pose proof (pow8_ge1 m0). lra.
Qed.

Lemma i_small : forall i, (2 ^ Z.of_nat i <= 5000)%Z -> (i <= 12)%nat.
Proof.
  intros i H. destruct (le_lt_dec i 12) as [Hi | Hi]; [exact Hi|].
  exfalso. assert (2 ^ 13 <= 2 ^ Z.of_nat i)%Z by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma pw_spec : forall n (t : int) R B H (i a : nat),
  to_Z t = n ->
  (Z.of_nat a + to_Z t * 2 ^ Z.of_nat i = Z.of_nat T)%Z ->
  (to_Z t = 0%Z -> R <> None -> (2 ^ Z.of_nat i <= Z.of_nat T)%Z) ->
  (to_Z t <> 0%Z -> (2 ^ Z.of_nat i <= Z.of_nat T)%Z) ->
  approx B (Nat.pow 2 i) (rho * 8 ^ i) ->
  match R with None => a = 0%nat | Some X => approx X a (rho * 8 ^ i) end ->
  match pw m t R B H with None => T = 0%nat | Some X => approx X T (rho * 8 ^ 13) end.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros t R B H i a En Ht Hi0 Hi1 HB HR. rewrite pw_eq.
  pose proof (to_Z_bounded t) as Bt.
  assert (Hp : (0 < 2 ^ Z.of_nat i)%Z) by (apply Z.pow_pos_nonneg; lia).
  destruct (bdec (t =? 0)%uint63) as [E0 | E0].
  - apply Uint63.eqb_spec in E0. subst t. change (to_Z 0%uint63) with 0%Z in *.
    destruct R as [X|].
    + assert (a = T) by lia. subst a.
      pose proof (i_small i ltac:(specialize (Hi0 eq_refl ltac:(discriminate)); lia)).
      eapply approx_mono; [| exact HR]. apply Rmult_le_compat_l; [exact Hrho|]. apply pow8_mono. lia.
    + lia.
  - pose proof E0 as E0'. apply Uint63.eqb_false_spec in E0'.
    assert (Et : to_Z t <> 0%Z) by (intros E; apply E0', to_Z_inj; exact E).
    specialize (Hi1 Et). pose proof (i_small i ltac:(lia)) as Hi12.
    assert (Hr8 : rho * 8 ^ i <= 1 / 2 / 8).
    { assert (8 ^ i * 8 <= 8 ^ 13).
      { replace (8 ^ i * 8) with (8 ^ (S i)) by (simpl; ring). apply pow8_mono. lia. }
      assert (0 <= rho * 8 ^ i) by (pose proof (pow8_ge1 i); nra). nra. }
    assert (Hr0 : 0 <= rho * 8 ^ i) by (pose proof (pow8_ge1 i); nra).
    assert (Hnext : 5 * (rho * 8 ^ i) <= rho * 8 ^ (S i)) by (simpl; nra).
    assert (Hr1 : rho <= rho * 8 ^ i) by (pose proof (pow8_ge1 i); nra).
    assert (H2i : Z.of_nat (Nat.pow 2 i) = (2 ^ Z.of_nat i)%Z) by (rewrite Nat2Z.inj_pow; reflexivity).
    cbv zeta.
    (* the new accumulator *)
    set (a' := (a + (if (t mod 2 =? 0)%uint63 then 0 else Nat.pow 2 i))%nat).
    set (R' := if (t mod 2 =? 0)%uint63 then R
               else Some (match R with None => B | Some X => mulr m X B end)).
    assert (Hmod : to_Z (t mod 2) = (to_Z t mod 2)%Z) by (rewrite Uint63.mod_spec; reflexivity).
    assert (Ha' : (Z.of_nat a' + (to_Z t / 2) * 2 ^ Z.of_nat (S i) = Z.of_nat T)%Z).
    { unfold a'. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      pose proof (Z.div_mod (to_Z t) 2 ltac:(lia)). pose proof (Z.mod_pos_bound (to_Z t) 2 ltac:(lia)).
      destruct (t mod 2 =? 0)%uint63 eqn:Em.
      - apply Uint63.eqb_spec in Em. apply (f_equal to_Z) in Em. rewrite Hmod in Em.
        change (to_Z 0%uint63) with 0%Z in Em. rewrite Nat.add_0_r. nia.
      - apply Uint63.eqb_false_spec in Em.
        assert (to_Z t mod 2 = 1)%Z.
        { assert (to_Z t mod 2 <> 0)%Z; [|lia]. intros E. apply Em. apply to_Z_inj. rewrite Hmod, E. reflexivity. }
        rewrite Nat2Z.inj_add, H2i. nia. }
    assert (HR' : match R' with None => a' = 0%nat | Some X => approx X a' (rho * 8 ^ (S i)) end).
    { unfold R', a'. destruct (t mod 2 =? 0)%uint63 eqn:Em.
      - rewrite Nat.add_0_r. destruct R as [X|]; [| exact HR].
        eapply approx_mono; [| exact HR]. lra.
      - destruct R as [X|].
        + eapply approx_mono; [| apply approx_mul; [exact HR | exact HB | | lra | lra]]; [lra|].
          assert (Z.of_nat a + 2 ^ Z.of_nat i <= Z.of_nat T)%Z by (pose proof (Z.div_mod (to_Z t) 2 ltac:(lia)); nia).
          rewrite Nat2Z.inj_add, H2i. lia.
        + subst a. simpl. eapply approx_mono; [| exact HB]. lra. }
    assert (Hdh : to_Z (t / 2)%uint63 = (to_Z t / 2)%Z) by (rewrite Uint63.div_spec; reflexivity).
    destruct ((t / 2)%uint63 =? 0)%uint63 eqn:Eh.
    + apply Uint63.eqb_spec in Eh. apply (f_equal to_Z) in Eh. rewrite Hdh in Eh.
      change (to_Z 0%uint63) with 0%Z in Eh. rewrite Eh in Ha'.
      destruct R' as [X|].
      * replace T with a' by lia. eapply approx_mono; [| exact HR'].
        apply Rmult_le_compat_l; [exact Hrho|]. apply pow8_mono. lia.
      * lia.
    + apply Uint63.eqb_false_spec in Eh.
      assert (Eh' : (to_Z t / 2 <> 0)%Z) by (intros E; apply Eh, to_Z_inj; rewrite Hdh, E; reflexivity).
      assert (Hpi : (2 ^ Z.of_nat (S i) <= Z.of_nat T)%Z).
      { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
        assert (1 <= to_Z t / 2)%Z by (pose proof (Z.div_pos (to_Z t) 2 ltac:(lia) ltac:(lia)); lia).
        assert (0 <= Z.of_nat a')%Z by lia. rewrite Nat2Z.inj_succ, Z.pow_succ_r in Ha' by lia. nia. }
      apply (IH (to_Z (t / 2)%uint63)) with (i := S i) (a := a').
      * rewrite <- En. apply dec_half. exact E0.
      * reflexivity.
      * rewrite Hdh. exact Ha'.
      * intros _ _. exact Hpi.
      * intros _. exact Hpi.
      * replace (Nat.pow 2 (S i)) with (Nat.pow 2 i + Nat.pow 2 i)%nat by (simpl; lia).
        eapply approx_mono; [| apply approx_mul; [exact HB | exact HB | | lra | lra]]; [lra|].
        rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hpi by lia. rewrite Nat2Z.inj_add, H2i. lia.
      * exact HR'.
Qed.

End Pow.

(* ------------------------------------------------------------------ *)
(* Vectors, the argmin, the output conversion                          *)
(* ------------------------------------------------------------------ *)

Lemma colb_vec : forall n A a (x : Z -> R), 0 <= a -> colb n A a ->
  rs (fun i => Rabs (rs (fun k => A i k * x k) n)) n <= a * rs (fun k => Rabs (x k)) n.
Proof.
  intros n A a x Ha HA.
  eapply Rle_trans.
  { apply rs_le. intros i _. eapply Rle_trans; [apply rs_abs|].
    apply Req_le. apply rs_ext. intros k _. apply Rabs_mult. }
  rewrite rs_swap. rewrite <- rs_scal. apply rs_le. intros k Hk.
  rewrite rs_scal_r. apply Rmult_le_compat_r; [apply Rabs_pos | apply HA; exact Hk].
Qed.

Lemma vec_err : forall n (Rt M : Mat) (uh w : Z -> R) E c W D, 0 <= E -> 0 <= c ->
  colb n (dsub Rt M) E -> colb n M c ->
  rs (fun k => Rabs (uh k)) n <= W -> rs (fun k => Rabs (uh k - w k)) n <= D ->
  rs (fun i => Rabs (rs (fun k => Rt i k * uh k) n - rs (fun k => M i k * w k) n)) n <= E * W + c * D.
Proof.
  intros n Rt M uh w E c W D HE Hc H1 H2 H3 H4.
  eapply Rle_trans.
  { apply rs_le. intros i _.
    replace (rs (fun k => Rt i k * uh k) n - rs (fun k => M i k * w k) n)
      with (rs (fun k => dsub Rt M i k * uh k) n + rs (fun k => M i k * (uh k - w k)) n)
      by (rewrite <- rs_add, <- rs_sub; apply rs_ext; intros; unfold dsub; ring).
    apply Rabs_triang. }
  rewrite rs_add.
  pose proof (colb_vec n (dsub Rt M) E uh HE H1). pose proof (colb_vec n M c (fun k => uh k - w k) Hc H2).
  cbv beta in *.
  assert (E * rs (fun k => Rabs (uh k)) n <= E * W) by (apply Rmult_le_compat_l; assumption).
  assert (c * rs (fun k => Rabs (uh k - w k)) n <= c * D) by (apply Rmult_le_compat_l; assumption).
  lra.
Qed.

Lemma argmin_exists : forall (f : Z -> R) n, (1 <= n)%Z ->
  exists i, (0 <= i < n)%Z /\ forall k, (0 <= k < n)%Z -> f i <= f k.
Proof.
  intros f n Hn. pattern n. apply (Zlt_lower_bound_ind _ 1); [| exact Hn].
  intros x IH Hx. destruct (Z.eq_dec x 1) as [E | E].
  - subst. exists 0%Z. split; [lia|]. intros k Hk. replace k with 0%Z by lia. lra.
  - destruct (IH (x - 1)%Z ltac:(lia)) as (i & Hi & Hm).
    destruct (Rle_dec (f i) (f (x - 1)%Z)) as [Hle | Hlt].
    + exists i. split; [lia|]. intros k Hk. destruct (Z.eq_dec k (x - 1)) as [-> | Ek]; [exact Hle|]. apply Hm. lia.
    + exists (x - 1)%Z. split; [lia|]. intros k Hk. destruct (Z.eq_dec k (x - 1)) as [-> | Ek]; [lra|].
      pose proof (Hm k ltac:(lia)). lra.
Qed.

Lemma iofp_spec : forall p, to_Z (iofp p) = (Zpos p mod wB)%Z.
Proof.
  induction p as [p IH | p IH |]; simpl iofp.
  - rewrite Uint63.add_spec, Uint63.mul_spec, IH. change (to_Z 2%uint63) with 2%Z. change (to_Z 1%uint63) with 1%Z.
    rewrite Zmult_mod_idemp_r, Zplus_mod_idemp_l. f_equal.
  - rewrite Uint63.mul_spec, IH. change (to_Z 2%uint63) with 2%Z.
    rewrite Zmult_mod_idemp_r. f_equal.
  - reflexivity.
Qed.

Lemma iofz_spec : forall z, (0 <= z < wB)%Z -> to_Z (iofz z) = z.
Proof.
  intros z Hz. destruct z as [| p | p]; [reflexivity | | lia].
  simpl. rewrite iofp_spec. apply Z.mod_small. exact Hz.
Qed.

Lemma sc2_bp : sc * sc = bp (2 * PP).
Proof. rewrite sc_bp, <- Raux.bpow_plus. f_equal. Qed.

Lemma cv_spec : forall z, (0 <= z)%Z -> IZR z / (sc * sc) <= 400000 ->
  exists r, repr (cv z) r /\ Rabs (r - IZR z / (sc * sc)) <= / 100000000.
Proof.
  intros z Hz Hb. unfold cv.
  set (K := Z.shiftr z (2 * PP - 30)).
  pose proof (shiftl_floor z (- (2 * PP - 30))) as Hf. rewrite Z.shiftl_opp_r in Hf. fold K in Hf.
  assert (Hbp : bp (- (2 * PP - 30)) = / (sc * sc) * 1073741824).
  { rewrite sc2_bp, <- Raux.bpow_opp. replace (- (2 * PP - 30))%Z with (- (2 * PP) + 30)%Z by lia.
    rewrite Raux.bpow_plus. reflexivity. }
  rewrite Hbp in Hf.
  assert (HK0 : (0 <= K)%Z) by (unfold K; apply Z.shiftr_nonneg; exact Hz).
  pose proof sc_pos.
  assert (Hzs : 0 <= IZR z / (sc * sc)) by (apply Rmult_le_pos; [apply IZR_le; exact Hz | left; apply Rinv_0_lt_compat; nra]).
  assert (HK1 : IZR K <= 400000 * 1073741824).
  { replace (IZR z * (/ (sc * sc) * 1073741824)) with (IZR z / (sc * sc) * 1073741824) in Hf by (unfold Rdiv; ring). nra. }
  assert (HK2 : (K < 2 ^ 53)%Z) by (apply lt_IZR; change (IZR (2 ^ 53)) with 9007199254740992; lra).
  assert (HK3 : to_Z (iofz K) = K) by (apply iofz_spec; rewrite wB_val; lia).
  pose proof (repr_of_uint63_exact (iofz K) ltac:(rewrite HK3; exact HK2)) as R1. rewrite HK3 in R1.
  pose proof (repr_of_uint63_exact 1073741824 ltac:(reflexivity)) as R2.
  change (to_Z 1073741824%uint63) with 1073741824%Z in R2.
  set (x := IZR K / IZR 1073741824).
  assert (Hx0 : 0 <= x) by (unfold x; apply Rmult_le_pos; [apply IZR_le; lia | left; apply Rinv_0_lt_compat; apply IZR_lt; lia]).
  assert (Hx1 : x <= 400000) by (unfold x; apply (Rmult_le_reg_r 1073741824); [lra|]; unfold Rdiv; rewrite Rmult_assoc, Rinv_l; [lra | lra]).
  assert (Hx2 : Rabs (x - IZR z / (sc * sc)) <= / 1073741824).
  { unfold x. replace (IZR z * (/ (sc * sc) * 1073741824)) with (IZR z / (sc * sc) * 1073741824) in Hf by (unfold Rdiv; ring).
    replace (IZR K / 1073741824 - IZR z / (sc * sc)) with ((IZR K - IZR z / (sc * sc) * 1073741824) * / 1073741824)
      by (field; lra).
    rewrite Rabs_mult, (Rabs_right (/ 1073741824)) by lra.
    rewrite <- (Rmult_1_l (/ 1073741824)) at 2. apply Rmult_le_compat_r; [lra|].
    apply Rabs_le. lra. }
  exists (rnd x). split.
  - apply repr_div; [exact R1 | exact R2 | apply IZR_neq; lia |].
    apply rnd_no_overflow_small. fold x. rewrite Rabs_right by lra.
    assert (400000 <= bp 1000) by (apply (Rle_trans _ (bp 20)); [simpl; lra | apply Raux.bpow_le; lia]). lra.
  - destruct (rnd_model x) as (eps & eta & He & Hn & _ & Er). rewrite Er.
    pose proof u_val. pose proof eta_max_le_u.
    assert (Rabs (x * eps) <= 400000 * (u / 2)) by (rewrite Rabs_mult, Rabs_right by lra; apply Rmult_le_compat; try lra; apply Rabs_pos).
    replace (x * (1 + eps) + eta - IZR z / (sc * sc)) with ((x - IZR z / (sc * sc)) + x * eps + eta) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
    rewrite u_val in *. lra.
Qed.

Lemma conv_spec : forall z, Rabs (IZR z / (sc * sc)) <= 400000 ->
  exists r, repr (conv z) r /\ Rabs (r - IZR z / (sc * sc)) <= / 100000000.
Proof.
  intros z Hb. unfold conv. destruct (Z.ltb_spec z 0) as [Hn | Hp].
  - assert (E : IZR (- z) / (sc * sc) = - (IZR z / (sc * sc))) by (rewrite opp_IZR; unfold Rdiv; ring).
    destruct (cv_spec (- z) ltac:(lia)) as (r & Hr & Hd).
    { rewrite E. pose proof (Rle_abs (- (IZR z / (sc * sc)))) as H. rewrite Rabs_Ropp in H. lra. }
    exists (- r). split; [apply repr_opp; exact Hr|]. rewrite E in Hd.
    replace (- r - IZR z / (sc * sc)) with (- (r - - (IZR z / (sc * sc)))) by ring. rewrite Rabs_Ropp. exact Hd.
  - apply cv_spec; [exact Hp|]. pose proof (Rle_abs (IZR z / (sc * sc))). lra.
Qed.

(* ------------------------------------------------------------------ *)
(* The remaining loops                                                 *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

Lemma rowdot_spec : forall (s : int) (X u : array Z) (i : int),
  to_Z s * to_Z s <= 4194303 -> to_Z i < to_Z s ->
  loop s (fun k acc => (acc + X.[i * s + k] * u.[k])%Z) 0%uint63 0%Z
  = zs (fun k => getM X (to_Z s) (to_Z i) k * u.[of_Z k]) (Z.to_nat (to_Z s)).
Proof.
  intros s X u i Hb Hi.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded i).
  apply (for_inv (fun k acc => acc = zs (fun c => getM X (to_Z s) (to_Z i) c * u.[of_Z c]) (Z.to_nat (to_Z k)))).
  - change (to_Z 0%uint63) with 0. lia.
  - reflexivity.
  - intros k acc Hk ->. change (to_Z 0%uint63) with 0 in Hk.
    assert (E : to_Z (k + 1) = to_Z k + 1) by sia. rewrite E.
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia.
    f_equal. f_equal; [apply getM_idx; snia | rewrite of_to_Z; reflexivity].
Qed.

Lemma loop_cond_sum : forall (n : int) (b : int -> bool) (v : array Z),
  loop n (fun k acc => if b k then (acc + v.[k])%Z else acc) 0%uint63 0%Z
  = zs (fun k => if b (of_Z k) then v.[of_Z k] else 0) (Z.to_nat (to_Z n)).
Proof.
  intros n b v. pose proof (to_Z_bounded n).
  apply (for_inv (fun k acc => acc = zs (fun c => if b (of_Z c) then v.[of_Z c] else 0) (Z.to_nat (to_Z k)))).
  - change (to_Z 0%uint63) with 0. lia.
  - reflexivity.
  - intros k acc Hk ->. change (to_Z 0%uint63) with 0 in Hk.
    assert (E : to_Z (k + 1) = to_Z k + 1) by sia. rewrite E.
    rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. rewrite of_to_Z.
    destruct (b k); ring.
Qed.

Lemma loop_min : forall (n : int) (g : int -> Z), 1 <= to_Z n ->
  exists ic, 0 <= to_Z ic < to_Z n /\
    loop n (fun i b => Z.min b (g i)) 1%uint63 (g 0%uint63) = g ic /\
    forall i, to_Z i < to_Z n -> loop n (fun i b => Z.min b (g i)) 1%uint63 (g 0%uint63) <= g i.
Proof.
  intros n g Hn.
  apply (for_inv (fun j b => exists ic, 0 <= to_Z ic < to_Z n /\ b = g ic /\
                    forall i, to_Z i < to_Z j -> b <= g i)).
  - change (to_Z 1%uint63) with 1. exact Hn.
  - exists 0%uint63. change (to_Z 0%uint63) with 0. split; [lia|]. split; [reflexivity|].
    intros i Hi. change (to_Z 1%uint63) with 1 in Hi. pose proof (to_Z_bounded i).
    assert (i = 0%uint63) by (apply to_Z_inj; change (to_Z 0%uint63) with 0; lia). subst. lia.
  - intros j b Hj (ic & Hic & -> & Hm). change (to_Z 1%uint63) with 1 in Hj.
    assert (E : to_Z (j + 1) = to_Z j + 1) by sia.
    destruct (Z.le_ge_cases (g ic) (g j)) as [Hle | Hge].
    + exists ic. split; [exact Hic|]. split; [lia|].
      intros i Hi. rewrite E in Hi. destruct (Z.eq_dec (to_Z i) (to_Z j)) as [Eij | Eij].
      * apply to_Z_inj in Eij. subst. lia.
      * pose proof (Hm i ltac:(lia)). lia.
    + exists j. split; [lia|]. split; [lia|].
      intros i Hi. rewrite E in Hi. destruct (Z.eq_dec (to_Z i) (to_Z j)) as [Eij | Eij].
      * apply to_Z_inj in Eij. subst. lia.
      * pose proof (Hm i ltac:(lia)). lia.
Qed.

Lemma bget_set : forall (t : array bool) (p q : int) v, (to_Z p < to_Z (PArray.length t)) ->
  t.[p <- v].[q] = if to_Z p =? to_Z q then v else t.[q].
Proof.
  intros t p q v H. destruct (to_Z p =? to_Z q) eqn:E.
  - apply Z.eqb_eq, to_Z_inj in E. subst q. apply bget_set_same. rewrite Uint63.ltb_spec. exact H.
  - apply Z.eqb_neq in E. apply bget_set_other. intros F. subst. contradiction.
Qed.

Lemma bget_make : forall (n i : int) (v : bool), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make bool v n i). Qed.

Section Adj.
Variables (src dst : list N) (n L : int) (xs xd : array uint).
Hypothesis Hn : to_Z n * to_Z n <= 4194303.
Hypothesis HL : Z.of_nat (List.length src) = to_Z L.
Hypothesis Hs : forall l, 0 <= l < to_Z L -> to_Z xs.[of_Z l] = Z.of_N (get_N src (Z.to_N l)) /\ to_Z xs.[of_Z l] < to_Z n.
Hypothesis Hd : forall l, 0 <= l < to_Z L -> to_Z xd.[of_Z l] = Z.of_N (get_N dst (Z.to_N l)) /\ to_Z xd.[of_Z l] < to_Z n.

Definition Jl (l : nat) (i k : Z) : bool :=
  negb (Z.to_N i =? Z.to_N k)%N &&
  existsb (fun j => (get_N src j =? Z.to_N i)%N && (get_N dst j =? Z.to_N k)%N
                 || (get_N src j =? Z.to_N k)%N && (get_N dst j =? Z.to_N i)%N)
          (map N.of_nat (seq 0 l)).

Lemma adj_spec :
  let adj := loop L (adj_step n xs xd) 0%uint63 (PArray.make (n * n) false) in
  forall i k, 0 <= i < to_Z n -> 0 <= k < to_Z n ->
    adj.[of_Z (i * to_Z n + k)] = Jl (List.length src) i k.
Proof.
  intros adj. unfold adj.
  pose proof (to_Z_bounded n) as Bn.
  assert (Hnn : to_Z (n * n) = to_Z n * to_Z n) by snia.
  replace (List.length src) with (Z.to_nat (to_Z L)) by lia.
  apply (for_inv (fun l a => PArray.length a = (n * n)%uint63 /\
     forall i k, 0 <= i < to_Z n -> 0 <= k < to_Z n -> a.[of_Z (i * to_Z n + k)] = Jl (Z.to_nat (to_Z l)) i k)).
  - change (to_Z 0%uint63) with 0. pose proof (to_Z_bounded L). lia.
  - split; [apply alen_makeb; lia|]. intros i k _ _. rewrite bget_make.
    unfold Jl. simpl. destruct (_ =? _)%N; reflexivity.
  - intros l a Hl [La Ea]. change (to_Z 0%uint63) with 0 in Hl.
    assert (El : to_Z (l + 1) = to_Z l + 1) by sia.
    destruct (Hs (to_Z l) Hl) as [Es Bs]. destruct (Hd (to_Z l) Hl) as [Ed Bd]. rewrite of_to_Z in Es, Bs, Ed, Bd.
    pose proof (to_Z_bounded xs.[l]). pose proof (to_Z_bounded xd.[l]).
    assert (HJ : forall i k, 0 <= i -> 0 <= k -> Jl (Z.to_nat (to_Z (l + 1))) i k =
              Jl (Z.to_nat (to_Z l)) i k ||
              (negb (i =? k) && ((to_Z xs.[l] =? i) && (to_Z xd.[l] =? k) || (to_Z xs.[l] =? k) && (to_Z xd.[l] =? i)))).
    { intros i k Hi Hk. unfold Jl. rewrite El, Z2Nat.inj_add, Nat.add_1_r, seq_S, map_app, existsb_app by lia.
      simpl existsb. rewrite Es, Ed.
      rewrite ?Nat.add_0_l. replace (N.of_nat (Z.to_nat (to_Z l))) with (Z.to_N (to_Z l)) by lia.
      replace (Z.to_N i =? Z.to_N k)%N with (i =? k) by (destruct (N.eqb_spec (Z.to_N i) (Z.to_N k)), (Z.eqb_spec i k); lia).
      set (gs := get_N src (Z.to_N (to_Z l))). set (gd := get_N dst (Z.to_N (to_Z l))).
      replace (gs =? Z.to_N i)%N with (Z.of_N gs =? i) by (destruct (N.eqb_spec gs (Z.to_N i)), (Z.eqb_spec (Z.of_N gs) i); lia).
      replace (gs =? Z.to_N k)%N with (Z.of_N gs =? k) by (destruct (N.eqb_spec gs (Z.to_N k)), (Z.eqb_spec (Z.of_N gs) k); lia).
      replace (gd =? Z.to_N i)%N with (Z.of_N gd =? i) by (destruct (N.eqb_spec gd (Z.to_N i)), (Z.eqb_spec (Z.of_N gd) i); lia).
      replace (gd =? Z.to_N k)%N with (Z.of_N gd =? k) by (destruct (N.eqb_spec gd (Z.to_N k)), (Z.eqb_spec (Z.of_N gd) k); lia).
      destruct (i =? k), (existsb _ _); simpl; repeat rewrite Bool.orb_false_r; reflexivity. }
    unfold adj_step. cbv zeta.
    destruct (xs.[l] =? xd.[l])%uint63 eqn:Esd.
    + apply Uint63.eqb_spec in Esd. split; [exact La|].
      intros i k Hi Hk. rewrite HJ by lia. rewrite Ea by assumption. rewrite Esd.
      destruct (Z.eqb_spec i k), (Z.eqb_spec (to_Z xd.[l]) i), (Z.eqb_spec (to_Z xd.[l]) k); simpl;
        rewrite ?Bool.orb_false_r; try reflexivity; lia.
    + apply Uint63.eqb_false_spec in Esd.
      assert (Esd' : to_Z xs.[l] <> to_Z xd.[l]) by (intros E; apply Esd, to_Z_inj, E).
      set (s := xs.[l]) in *. set (d := xd.[l]) in *.
      assert (I1 : to_Z (s * n + d) = to_Z s * to_Z n + to_Z d)
        by (apply idx2; assert (to_Z s * to_Z n <= (to_Z n - 1) * to_Z n) by (apply Z.mul_le_mono_nonneg_r; lia); rewrite wB_val; lia).
      assert (I2 : to_Z (d * n + s) = to_Z d * to_Z n + to_Z s)
        by (apply idx2; assert (to_Z d * to_Z n <= (to_Z n - 1) * to_Z n) by (apply Z.mul_le_mono_nonneg_r; lia); rewrite wB_val; lia).
      assert (B1 : to_Z s * to_Z n + to_Z d < to_Z n * to_Z n)
        by (assert (to_Z s * to_Z n <= (to_Z n - 1) * to_Z n) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
      assert (B2 : to_Z d * to_Z n + to_Z s < to_Z n * to_Z n)
        by (assert (to_Z d * to_Z n <= (to_Z n - 1) * to_Z n) by (apply Z.mul_le_mono_nonneg_r; lia); lia).
      split; [rewrite !blen_set; exact La|].
      intros i k Hi Hk.
      assert (Iik : to_Z (of_Z (i * to_Z n + k)) = i * to_Z n + k)
        by (apply to_Z_of_Z_small; assert (i * to_Z n <= (to_Z n - 1) * to_Z n) by (apply Z.mul_le_mono_nonneg_r; lia);
            rewrite wB_val; lia).
      rewrite bget_set by (rewrite blen_set, La, Hnn, I2; exact B2).
      rewrite bget_set by (rewrite La, Hnn, I1; exact B1).
      rewrite I1, I2, Iik, HJ by lia. rewrite Ea by assumption.
      destruct (Z.eqb_spec (to_Z d * to_Z n + to_Z s) (i * to_Z n + k)) as [E2|E2].
      * apply idx_inj in E2; [|lia..]. destruct E2 as [<- <-].
        rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite !Z.eqb_refl. simpl. rewrite ?Bool.andb_false_r, !Bool.orb_true_r. reflexivity.
      * destruct (Z.eqb_spec (to_Z s * to_Z n + to_Z d) (i * to_Z n + k)) as [E1|E1].
        -- apply idx_inj in E1; [|lia..]. destruct E1 as [<- <-].
           rewrite (proj2 (Z.eqb_neq _ _)) by lia. rewrite !Z.eqb_refl. simpl. rewrite ?Bool.andb_false_r, !Bool.orb_true_r. reflexivity.
        -- destruct (Z.eqb_spec (to_Z s) i), (Z.eqb_spec (to_Z d) k), (Z.eqb_spec (to_Z s) k), (Z.eqb_spec (to_Z d) i);
             subst; simpl; rewrite ?Bool.andb_false_r, ?Bool.orb_false_r; try reflexivity; try lia;
             exfalso; first [apply E1; reflexivity | apply E2; reflexivity].
Qed.

End Adj.

(* ------------------------------------------------------------------ *)
(* Reading the inputs                                                  *)
(* ------------------------------------------------------------------ *)

Lemma of_nat_Z : forall k : nat, (Z.of_nat k < wB)%Z -> Uint63.of_nat k = of_Z (Z.of_nat k).
Proof. intros. reflexivity. Qed.

Lemma repr_len_f : forall (x : array float) (l : list R), repr x l ->
  to_Z (PArray.length x) = Z.of_nat (List.length l).
Proof. intros x l [H _]. symmetry. exact H. Qed.

Lemma repr_len_u : forall (x : array uint) (l : list N), repr x l ->
  to_Z (PArray.length x) = Z.of_nat (List.length l).
Proof. intros x l [H _]. symmetry. exact H. Qed.

Lemma repr_get_f : forall (x : array float) (l : list R) k, repr x l ->
  (0 <= k < Z.of_nat (List.length l))%Z -> repr x.[of_Z k] (nth (Z.to_nat k) l 0%R).
Proof.
  intros x l k [_ Hc] Hk. destruct (Hc (Z.to_nat k) ltac:(lia)) as (r & Hr & Hx).
  rewrite (nth_error_nth _ _ _ Hr). unfold Uint63.of_nat in Hx. rewrite Z2Nat.id in Hx by lia. exact Hx.
Qed.

Lemma repr_get_u : forall (x : array uint) (l : list N) k, repr x l ->
  (0 <= k < Z.of_nat (List.length l))%Z -> to_Z x.[of_Z k] = Z.of_N (nth (Z.to_nat k) l 0%N).
Proof.
  intros x l k [_ Hc] Hk. destruct (Hc (Z.to_nat k) ltac:(lia)) as (r & Hr & Hx).
  rewrite (nth_error_nth _ _ _ Hr). unfold Uint63.of_nat in Hx. rewrite Z2Nat.id in Hx by lia.
  change (Z.to_N (to_Z (x.[of_Z k])) = r) in Hx. pose proof (to_Z_bounded (x.[of_Z k])). rewrite <- Hx. lia.
Qed.

Local Open Scope R_scope.

Lemma rs_single : forall f n i, (forall k, (0 <= k < Z.of_nat n)%Z -> 0 <= f k) ->
  (0 <= i < Z.of_nat n)%Z -> f i <= rs f n.
Proof.
  intros f n. induction n as [|n IH]; intros i Hf Hi; [lia|]. simpl.
  destruct (Z.eq_dec i (Z.of_nat n)) as [E|E].
  - subst. pose proof (rs_nonneg f n ltac:(intros; apply Hf; lia)). lra.
  - pose proof (IH i ltac:(intros; apply Hf; lia) ltac:(lia)). pose proof (Hf (Z.of_nat n) ltac:(lia)). lra.
Qed.

Lemma rs_mono_n : forall f n1 n2, (n1 <= n2)%nat -> (forall k, (0 <= k < Z.of_nat n2)%Z -> 0 <= f k) ->
  rs f n1 <= rs f n2.
Proof.
  intros f n1 n2 H. induction H as [|n2 H IH]; intros Hf; [lra|].
  simpl. pose proof (IH ltac:(intros; apply Hf; lia)). pose proof (Hf (Z.of_nat n2) ltac:(lia)). lra.
Qed.

Lemma sc_val : sc = 79228162514264337593543950336.
Proof. unfold sc. rewrite ONE_val. reflexivity. Qed.

Lemma get_R_out : forall (l : list R) k, (Z.of_nat (List.length l) <= k)%Z -> get_R l (Z.to_N k) = 0.
Proof. intros l k H. unfold get_R. apply nth_overflow. lia. Qed.

Lemma fix_err : forall F r, IZR F <= r * sc < IZR F + 1 -> Rabs (IZR F / sc - r) <= / sc.
Proof.
  intros F r [H1 H2]. pose proof sc_pos.
  assert (E1 : IZR F / sc <= r).
  { apply (Rmult_le_reg_r sc); [lra|]. unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
  assert (E2 : r < IZR F / sc + / sc).
  { apply (Rmult_lt_reg_r sc); [lra|]. rewrite Rmult_plus_distr_r. unfold Rdiv.
    rewrite Rmult_assoc, !Rinv_l by lra. lra. }
  rewrite Rabs_left1; lra.
Qed.

Lemma faced_z_spec : forall (n : int) adj v (i : Z), (to_Z n * to_Z n <= 4194303)%Z -> (0 <= i < to_Z n)%Z ->
  faced_z n adj v (of_Z i) =
  (v.[of_Z i] + zs (fun k => if adj.[of_Z (i * to_Z n + k)] then v.[of_Z k] else 0) (Z.to_nat (to_Z n)))%Z.
Proof.
  intros n adj v i Hb Hi. unfold faced_z. f_equal.
  rewrite (loop_cond_sum n (fun k => adj.[of_Z i * n + k]) v). apply zs_ext. intros k Hk.
  pose proof (to_Z_bounded n).
  assert (Ii : to_Z (of_Z i) = i) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
  assert (Ik : to_Z (of_Z k) = k) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
  replace (of_Z i * n + of_Z k)%uint63 with (of_Z (i * to_Z n + k)); [reflexivity|].
  apply to_Z_inj. rewrite idx2, Ii, Ik.
  - apply to_Z_of_Z_small. assert (i * to_Z n <= (to_Z n - 1) * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite wB_val. lia.
  - rewrite Ii, Ik. assert (i * to_Z n <= (to_Z n - 1) * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite wB_val. split; [apply Z.add_nonneg_nonneg; [apply Z.mul_nonneg_nonneg|]; lia | lia].
Qed.

Theorem timing_exact_correct : forall (t : N) (u : list R) (src dst : list N) (frac : list R)
    (xt : uint) (xu : array float) (xs xd : array uint) (xf : array float),
  valid_input t u src dst frac ->
  repr xt t -> repr xu u -> repr xs src -> repr xd dst -> repr xf frac ->
  exists o : R, repr (timing_exact xt xu xs xd xf) o /\ timing_spec t u src dst frac o.
Proof.
  intros t u src dst frac xt xu xs xd xf Hv Ht Hu Hs Hd Hf.
  pose proof Hv as Hv'. destruct Hv' as [HN Hl HT Hdl Hfl Hu0 Hs0 Hd0 Hf0 Ho].
  set (nu := List.length u) in *. set (Lr := List.length src) in *.
  unfold len in HN, Hl, Hdl, Hfl. fold nu Lr in HN, Hl, Hdl, Hfl.
  apply Nat2N.inj in Hdl. apply Nat2N.inj in Hfl.
  assert (Hnu : (1 <= Z.of_nat nu <= 100)%Z) by lia.
  assert (HLr : (Z.of_nat Lr <= 9801)%Z).
  { assert ((N.of_nat nu - 1) ^ 2 <= 9801)%N by (change 9801%N with (99 ^ 2)%N; apply N.pow_le_mono_l; lia). lia. }
  assert (Hxt : to_Z xt = Z.of_N t) by (unfold repr, repr_uint in Ht; pose proof (to_Z_bounded xt); lia).
  pose proof (repr_len_f xu u Hu) as Lxu. pose proof (repr_len_u xs src Hs) as Lxs.
  unfold timing_exact. cbv zeta.
  set (n := PArray.length xu) in *. set (L := PArray.length xs) in *. fold nu in Lxu. fold Lr in Lxs.
  set (m := ((n + 7) / 8 * 8)%uint63).
  assert (Hm : to_Z m = ((to_Z n + 7) / 8 * 8)%Z) by (unfold m; rewrite Uint63.mul_spec, Uint63.div_spec, Uint63.add_spec;
     change (to_Z 7%uint63) with 7%Z; change (to_Z 8%uint63) with 8%Z; rewrite Lxu;
     rewrite (Z.mod_small (_ + 7)) by (rewrite wB_val; lia); apply Z.mod_small; rewrite wB_val;
     pose proof (Z.div_pos (Z.of_nat nu + 7) 8); pose proof (Z.div_le_upper_bound (Z.of_nat nu + 7) 8 108); lia).
  assert (Hmb : (Z.of_nat nu <= to_Z m <= 107)%Z).
  { rewrite Hm, Lxu. pose proof (Z.div_mod (Z.of_nat nu + 7) 8). pose proof (Z.mod_pos_bound (Z.of_nat nu + 7) 8). lia. }
  assert (Hmm : (to_Z m * to_Z m <= 4194303)%Z) by nia.
  assert (Hmm2 : to_Z (m * m)%uint63 = (to_Z m * to_Z m)%Z)
    by (rewrite Uint63.mul_spec; apply Z.mod_small; rewrite wB_val; pose proof (to_Z_bounded m); nia).
  set (mn := Z.to_nat (to_Z m)).
  assert (Hmn : (nu <= mn)%nat) by lia.
  assert (Hmn' : Z.of_nat mn = to_Z m) by lia.
  (* the links *)
  assert (HsrcZ : forall l, (0 <= l < to_Z L)%Z ->
            to_Z xs.[of_Z l] = Z.of_N (get_N src (Z.to_N l)) /\ (to_Z xs.[of_Z l] < to_Z n)%Z).
  { intros l Hl'. rewrite (repr_get_u xs src l Hs) by lia. unfold get_N. rewrite Z_N_nat. split; [reflexivity|].
    pose proof (nth_Forall _ src (Z.to_nat l) 0%N Hs0 ltac:(lia)) as B. cbv beta in B. rewrite len_nat in B. lia. }
  assert (HdstZ : forall l, (0 <= l < to_Z L)%Z ->
            to_Z xd.[of_Z l] = Z.of_N (get_N dst (Z.to_N l)) /\ (to_Z xd.[of_Z l] < to_Z n)%Z).
  { intros l Hl'. rewrite (repr_get_u xd dst l Hd) by lia. unfold get_N. rewrite Z_N_nat. split; [reflexivity|].
    pose proof (nth_Forall _ dst (Z.to_nat l) 0%N Hd0 ltac:(lia)) as B. cbv beta in B. rewrite len_nat in B. lia. }
  (* the transfer matrix *)
  assert (HA : eqr (to_Z m) (amat m L xs xd xf) (Aint xs xd xf Lr)).
  { replace Lr with (Z.to_nat (to_Z L)) by lia. apply amat_spec; [exact Hmm | | | lia].
    - intros l Hl'. pose proof (to_Z_bounded l). destruct (HsrcZ (to_Z l) ltac:(lia)) as [_ B]. rewrite of_to_Z in B.
      split; [apply (proj1 (to_Z_bounded _)) | eapply Z.lt_le_trans; [exact B | lia]].
    - intros l Hl'. pose proof (to_Z_bounded l). destruct (HdstZ (to_Z l) ltac:(lia)) as [_ B]. rewrite of_to_Z in B.
      split; [apply (proj1 (to_Z_bounded _)) | eapply Z.lt_le_trans; [exact B | lia]]. }
  set (A := amat m L xs xd xf) in *.
  set (rho := 32768 / sc).
  pose proof sc_val as Esc. pose proof sc_pos as Psc.
  assert (Hrho : 0 <= rho) by (unfold rho; rewrite Esc; lra).
  assert (Hrnd : INR mn * / sc <= rho).
  { unfold rho. rewrite INR_IZR_INZ, Hmn'. assert (Hmb' : IZR (to_Z m) <= 107) by (apply IZR_le; lia). unfold Rdiv. rewrite Esc in *. lra. }
  assert (Hrho8 : rho * 8 ^ 13 <= 1 / 2) by (unfold rho; rewrite Esc; simpl; lra).
  assert (Hnorm : forall k, (Z.of_nat k <= 10000)%Z -> colb mn (mpow src dst frac mn k) (3 / 2)).
  { intros k Hk. eapply colb_mono; [apply gam_pow; exact Hk | apply (colb_mpow t u); assumption]. }
  assert (HA1 : approx src dst frac m A (Nat.pow 2 0) (rho * 8 ^ 0)).
  { split; [destruct HA as [L0 _]; exact L0|].
    eapply colb_ext; [| eapply colb_mono; [| apply (A_err src dst frac mn xs xd xf)]].
    - intros i j Hi Hj. unfold dsub, frM. destruct HA as [_ EA]. rewrite EA by lia.
      simpl mpow. rewrite Id_r by exact Hj. reflexivity.
    - unfold rho. simpl. rewrite INR_IZR_INZ. change (Datatypes.length src) with Lr. apply IZR_le in HLr. rewrite Esc. unfold Rdiv. lra.
    - intros l Hl'. fold Lr in Hl'.
      destruct (HsrcZ l ltac:(lia)) as [E1 _]. destruct (HdstZ l ltac:(lia)) as [E2 _].
      split; [exact E1|]. split; [exact E2|].
      unfold Fl. apply fixv_spec. unfold fr, get_R. rewrite Z_N_nat. exact (repr_get_f xf frac l Hf ltac:(lia)). }
  (* the power *)
  set (T := Z.to_nat (to_Z xt)).
  assert (HT' : (Z.of_nat T <= 5000)%Z) by lia.
  pose proof (pw_spec src dst frac m T rho Hmm HT' Hrho Hrnd Hrho8 Hnorm (to_Z xt) xt None A
                (Zwf_well_founded 0 (to_Z xt)) 0%nat 0%nat eq_refl ltac:(simpl; lia)
                ltac:(intros _ F; exfalso; apply F; reflexivity) ltac:(intros; simpl; lia) HA1 eq_refl) as HP.
  set (E := rho * 8 ^ 13) in *.
  assert (HE : 0 <= E <= 1 / 2) by (split; [unfold E; apply Rmult_le_pos; [exact Hrho | pose proof (pow8_ge1 13); lra] | exact Hrho8]).
  set (Rf := match pw m xt None A (Zwf_well_founded 0 (to_Z xt)) with None => ident m | Some X => X end).
  assert (HRf : approx src dst frac m Rf T E).
  { unfold Rf. destruct (pw m xt None A (Zwf_well_founded 0 (to_Z xt))) as [X|]; [exact HP|].
    rewrite HP. split.
    - unfold ident. rewrite build_len by (rewrite Hmm2; lia). exact Hmm2.
    - intros j Hj. destruct (ident_spec m Hmm) as [_ EI].
      rewrite (rs_ext _ (fun _ => 0)); [rewrite rs_zero; lra|].
      intros i Hi. unfold dsub, frM. rewrite EI by lia. simpl mpow. unfold Id, indR.
      destruct (i =? j)%Z; [fold sc; rewrite Esc; rewrite Rabs_right; lra | unfold Rdiv; rewrite Rmult_0_l, Rminus_0_r, Rabs_R0; reflexivity]. }
  destruct HRf as [LRf CRf].
  (* the strengths, in fixed point *)
  set (uh := build m (fun s => if (s <? n)%uint63 then fixv xu.[s] else 0%Z)).
  assert (Huh : forall k, (0 <= k < to_Z m)%Z ->
            uh.[of_Z k] = if (k <? Z.of_nat nu)%Z then fixv xu.[of_Z k] else 0%Z).
  { intros k Hk. assert (Ik : to_Z (of_Z k) = k) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    unfold uh. rewrite build_get by lia.
    replace ((of_Z k <? n)%uint63) with (k <? Z.of_nat nu)%Z; [reflexivity|].
    destruct (Z.ltb_spec k (Z.of_nat nu)), (of_Z k <? n)%uint63 eqn:Ek; try reflexivity;
      [rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Ek | rewrite Uint63.ltb_spec in Ek]; lia. }
  set (w := fun k => get_R u (Z.to_N k)).
  set (uhR := fun k => IZR (uh.[of_Z k]) / sc).
  assert (Hw : forall k, (0 <= k < Z.of_nat mn)%Z -> Rabs (uhR k - w k) <= / sc /\ 0 <= w k <= 1000).
  { intros k Hk. unfold uhR, w. rewrite Huh by lia.
    destruct (Z.ltb_spec k (Z.of_nat nu)) as [Hkn | Hkn].
    - assert (Ew : get_R u (Z.to_N k) = nth (Z.to_nat k) u 0) by (unfold get_R; rewrite Z_N_nat; reflexivity).
      rewrite Ew. split.
      + apply fix_err, fixv_spec. exact (repr_get_f xu u k Hu ltac:(lia)).
      + exact (nth_Forall _ u (Z.to_nat k) 0 Hu0 ltac:(lia)).
    - rewrite get_R_out by lia. unfold Rdiv. rewrite Rmult_0_l, Rminus_0_r, Rabs_R0.
      split; [left; apply Rinv_0_lt_compat; exact Psc | lra]. }
  assert (HW : rs (fun k => Rabs (uhR k)) mn <= 108000).
  { eapply Rle_trans; [apply (rs_const_le _ _ 1001) |].
    - intros k Hk. destruct (Hw k Hk) as [H1 H2].
      assert (Rabs (uhR k) <= Rabs (uhR k - w k) + Rabs (w k))
        by (replace (uhR k) with ((uhR k - w k) + w k) at 1 by ring; apply Rabs_triang).
      rewrite (Rabs_right (w k)) in H by lra. rewrite Esc in H1. lra.
    - rewrite INR_IZR_INZ, Hmn'. assert (IZR (to_Z m) <= 107) by (apply IZR_le; lia). lra. }
  assert (HD : rs (fun k => Rabs (uhR k - w k)) mn <= INR mn * / sc)
    by (apply rs_const_le; intros k Hk; apply Hw; exact Hk).
  (* v = A^t u *)
  set (v := build m (fun i => loop m (fun k acc => (acc + Rf.[i * m + k] * uh.[k])%Z) 0%uint63 0%Z)).
  set (vR := fun i => IZR (v.[of_Z i]) / (sc * sc)).
  assert (Hvv : forall i, (0 <= i < to_Z m)%Z -> vR i = rs (fun k => frM Rf (to_Z m) i k * uhR k) mn).
  { intros i Hi. assert (Ii : to_Z (of_Z i) = i) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    unfold vR, v. rewrite build_get by lia. rewrite rowdot_spec by lia. rewrite Ii. fold mn.
    rewrite rs_IZR. unfold Rdiv. rewrite <- rs_scal_r. apply rs_ext. intros k _. unfold frM, uhR.
    rewrite mult_IZR. field. lra. }
  set (sR := fun i => strength u src dst frac T (Z.to_N i)).
  assert (HsR : forall i, (0 <= i < Z.of_nat mn)%Z -> sR i = rs (fun k => mpow src dst frac mn T i k * w k) mn)
    by (intros i Hi; unfold sR; apply (strength_mat t); assumption).
  set (Ev := E * 108000 + 3 / 2 * (INR mn * / sc)).
  assert (Hverr : rs (fun i => Rabs (vR i - sR i)) mn <= Ev).
  { rewrite (rs_ext _ (fun i => Rabs (rs (fun k => frM Rf (to_Z m) i k * uhR k) mn
                                    - rs (fun k => mpow src dst frac mn T i k * w k) mn))).
    - apply vec_err; [lra | lra | exact CRf | apply Hnorm; lia | exact HW | exact HD].
    - intros i Hi. rewrite Hvv, HsR by lia. reflexivity. }
  assert (HsB : rs (fun i => Rabs (sR i)) mn <= 160500).
  { rewrite (rs_ext _ (fun i => Rabs (rs (fun k => mpow src dst frac mn T i k * w k) mn)))
      by (intros i Hi; rewrite HsR by exact Hi; reflexivity).
    eapply Rle_trans; [apply (colb_vec mn _ (3 / 2) w); [lra | apply Hnorm; lia]|].
    assert (rs (fun k => Rabs (w k)) mn <= INR mn * 1000)
      by (apply rs_const_le; intros k Hk; destruct (Hw k Hk) as [_ H2]; rewrite Rabs_right; lra).
    rewrite INR_IZR_INZ, Hmn' in H. assert (IZR (to_Z m) <= 107) by (apply IZR_le; lia). lra. }
  (* the adjacency *)
  set (adj := loop L (adj_step n xs xd) 0%uint63 (PArray.make (n * n) false)).
  assert (Hnn : (to_Z n * to_Z n <= 4194303)%Z)
    by (rewrite Lxu; assert (Z.of_nat nu * Z.of_nat nu <= 100 * 100)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hadj : forall i k, (0 <= i < to_Z n)%Z -> (0 <= k < to_Z n)%Z ->
            adj.[of_Z (i * to_Z n + k)] = joined src dst (Z.to_N i) (Z.to_N k)).
  { intros i k Hi Hk. unfold adj.
    exact (adj_spec src dst n L xs xd Hnn ltac:(lia) HsrcZ HdstZ i k Hi Hk). }
  (* faced *)
  set (FzR := fun i => IZR (faced_z n adj v (of_Z i)) / (sc * sc)).
  set (fc := fun i => faced u src dst frac T (Z.to_N i)).
  assert (Herr : forall i, (0 <= i < Z.of_nat nu)%Z -> Rabs (FzR i - fc i) <= 2 * Ev).
  { intros i Hi.
    assert (EF : FzR i = vR i + rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then vR k else 0) nu).
    { unfold FzR. rewrite faced_z_spec by lia. rewrite Lxu, Nat2Z.id.
      rewrite plus_IZR, rs_IZR. unfold Rdiv. rewrite Rmult_plus_distr_r. f_equal.
      rewrite <- rs_scal_r. apply rs_ext. intros k Hk. rewrite <- Lxu, Hadj by lia.
      destruct (joined _ _ _ _); [reflexivity | rewrite Rmult_0_l; reflexivity]. }
    assert (Ef : fc i = sR i + rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then sR k else 0) nu)
      by (unfold fc, sR, faced; rewrite sum_below_rs; reflexivity).
    rewrite EF, Ef.
    replace (vR i + rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then vR k else 0) nu -
             (sR i + rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then sR k else 0) nu))
      with ((vR i - sR i) + rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then vR k - sR k else 0) nu)
      by (rewrite (rs_ext (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then vR k - sR k else 0)
             (fun k => (if joined src dst (Z.to_N i) (Z.to_N k) then vR k else 0) - (if joined src dst (Z.to_N i) (Z.to_N k) then sR k else 0)) nu)
             by (intros; destruct (joined _ _ _ _); ring); rewrite rs_sub; ring).
    eapply Rle_trans; [apply Rabs_triang|].
    assert (H1 : Rabs (vR i - sR i) <= rs (fun i => Rabs (vR i - sR i)) mn)
      by (apply (rs_single (fun i => Rabs (vR i - sR i))); [intros; apply Rabs_pos | lia]).
    assert (H2 : Rabs (rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then vR k - sR k else 0) nu)
                 <= rs (fun i => Rabs (vR i - sR i)) mn).
    { eapply Rle_trans; [apply rs_abs|]. eapply Rle_trans; [| apply rs_mono_n; [exact Hmn | intros; apply Rabs_pos]].
      apply rs_le. intros k _. destruct (joined _ _ _ _); [lra | rewrite Rabs_R0; apply Rabs_pos]. }
    lra. }
  assert (Hfb : forall i, (0 <= i < Z.of_nat nu)%Z -> Rabs (fc i) <= 321000).
  { intros i Hi. unfold fc, faced. rewrite sum_below_rs. cbv beta. fold (sR i). change (Datatypes.length u) with nu.
    eapply Rle_trans; [apply Rabs_triang|].
    assert (H1 : Rabs (sR i) <= rs (fun i => Rabs (sR i)) mn)
      by (apply (rs_single (fun i => Rabs (sR i))); [intros; apply Rabs_pos | lia]).
    assert (H2 : Rabs (rs (fun k => if joined src dst (Z.to_N i) (Z.to_N k) then strength u src dst frac T (Z.to_N k) else 0) nu)
                 <= rs (fun i => Rabs (sR i)) mn).
    { eapply Rle_trans; [apply rs_abs|]. eapply Rle_trans; [| apply rs_mono_n; [exact Hmn | intros; apply Rabs_pos]].
      apply rs_le. intros k _. unfold sR. destruct (joined _ _ _ _); [lra | rewrite Rabs_R0; apply Rabs_pos]. }
    lra. }
  (* the least *)
  destruct (loop_min n (faced_z n adj v) ltac:(lia)) as (ic & Hic & Hbest & Hmin).
  set (best := loop n (fun i b => Z.min b (faced_z n adj v i)) 1%uint63 (faced_z n adj v 0%uint63)) in *.
  destruct (argmin_exists fc (Z.of_nat nu) ltac:(lia)) as (is & His & Hism).
  set (bR := IZR best / (sc * sc)).
  assert (Hev : 2 * Ev <= / 20000000).
  { unfold Ev, E, rho. rewrite INR_IZR_INZ, Hmn'. assert (IZR (to_Z m) <= 107) by (apply IZR_le; lia).
    rewrite Esc in *. simpl. lra. }
  assert (Hb1 : bR <= fc is + 2 * Ev).
  { assert (Ii : to_Z (of_Z is) = is) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    pose proof (Hmin (of_Z is) ltac:(lia)) as Hm1.
    pose proof (Herr is His) as He1. unfold FzR in He1.
    unfold bR. apply IZR_le in Hm1.
    assert (IZR best / (sc * sc) <= IZR (faced_z n adj v (of_Z is)) / (sc * sc))
      by (apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; nra | exact Hm1]).
    pose proof (Rle_abs (IZR (faced_z n adj v (of_Z is)) / (sc * sc) - fc is)). lra. }
  assert (Hb2 : fc is - 2 * Ev <= bR).
  { pose proof (Herr (to_Z ic) ltac:(lia)) as He1. unfold FzR in He1. rewrite of_to_Z in He1.
    unfold bR. rewrite Hbest.
    pose proof (Hism (to_Z ic) ltac:(lia)).
    pose proof (Rle_abs (- (IZR (faced_z n adj v ic) / (sc * sc) - fc (to_Z ic)))) as Ha. rewrite Rabs_Ropp in Ha. lra. }
  destruct (conv_spec best) as (r & Hr & Hrd).
  { fold bR. pose proof (Hfb is His). apply Rabs_le.
    pose proof (Rle_abs (fc is)). pose proof (Rle_abs (- fc is)) as Hn. rewrite Rabs_Ropp in Hn. lra. }
  exists r. split; [exact Hr|].
  assert (ET : T = N.to_nat t) by (unfold T; rewrite Hxt; lia).
  exists (Z.to_N is). split; [unfold len; fold nu; lia|]. split.
  - intros m' Hm'. rewrite <- ET. pose proof (Hism (Z.of_N m') ltac:(unfold len in Hm'; fold nu in Hm'; lia)) as Hq.
    unfold fc in Hq. rewrite N2Z.id in Hq. exact Hq.
  - cbv zeta. left. rewrite <- ET. fold (fc is). fold bR in Hrd.
    apply (Rle_lt_trans _ (/ 100000000 + 2 * Ev)); [| lra].
    replace (r - fc is) with ((r - bR) + (bR - fc is)) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat; [exact Hrd|].
    apply Rabs_le. lra.
Qed.


Open Scope uint63_scope.


Local Open Scope R_scope.

Lemma repr_fval : forall (x : float) r, repr x r -> fval x = r.
Proof. intros x r [_ H]. exact H. Qed.

Lemma rnd_err : forall z, Rabs (rnd z - z) <= u / 2 * Rabs z + eta_max.
Proof.
  intros z. destruct (rnd_model z) as (eps & eta & He & Hn & _ & ->).
  replace (z * (1 + eps) + eta - z) with (z * eps + eta) by ring.
  eapply Rle_trans; [apply Rabs_triang|]. rewrite Rabs_mult.
  pose proof (Rabs_pos z).
  assert (Rabs z * Rabs eps <= Rabs z * (u / 2)) by (apply Rmult_le_compat_l; lra). lra.
Qed.

(* one rounded operation of a running sum *)
Lemma op_err : forall z Y M c, 0 <= c -> c * u <= 1 -> Rabs Y <= M ->
  Rabs (z - Y) <= c * u * (M + 1) ->
  Rabs (rnd z - Y) <= (c + 1) * u * (M + 1) /\ Rabs z <= 2 * M + 1.
Proof.
  intros z Y M c Hc Hcu HY Hz. pose proof u_pos. pose proof eta_max_le_u. pose proof (Rabs_pos Y).
  assert (HM : 0 <= M) by lra.
  assert (Hcz : c * u * (M + 1) <= M + 1)
    by (rewrite <- (Rmult_1_l (M + 1)) at 2; apply Rmult_le_compat_r; lra).
  assert (Hzz : Rabs z <= M + c * u * (M + 1)).
  { replace z with ((z - Y) + Y) by ring. eapply Rle_trans; [apply Rabs_triang|]. lra. }
  split; [| lra].
  pose proof (rnd_err z) as Hr.
  assert (Ha : u / 2 * Rabs z <= u / 2 * (M + c * u * (M + 1))) by (apply Rmult_le_compat_l; lra).
  assert (Hb : u / 2 * (c * u * (M + 1)) <= u / 2 * (M + 1)) by (apply Rmult_le_compat_l; lra).
  replace (rnd z - Y) with ((rnd z - z) + (z - Y)) by ring.
  eapply Rle_trans; [apply Rabs_triang|].
  replace ((c + 1) * u * (M + 1)) with (c * u * (M + 1) + u * (M + 1)) by ring.
  nra.
Qed.

Definition fv (v : array float) (i : Z) : R := fval v.[of_Z i].

Definition okv (v : array float) (n : Z) : Prop :=
  to_Z (PArray.length v) = n /\
  forall i, (0 <= i < n)%Z -> PrimFloat.is_finite v.[of_Z i] = true.

Lemma okv_repr : forall v n i, okv v n -> (0 <= i < n)%Z -> repr v.[of_Z i] (fv v i).
Proof. intros v n i [_ H] Hi. split; [apply H; exact Hi | reflexivity]. Qed.

Lemma fget_set : forall (t : array float) (p q : int) v, (to_Z p < to_Z (PArray.length t))%Z ->
  t.[p <- v].[q] = if (to_Z p =? to_Z q)%Z then v else t.[q].
Proof.
  intros t p q v H. destruct (to_Z p =? to_Z q)%Z eqn:E.
  - apply Z.eqb_eq, to_Z_inj in E. subst q. refine (get_set_same float t p v _). rewrite Uint63.ltb_spec. exact H.
  - apply Z.eqb_neq in E. refine (get_set_other float t p q v _). intros F. subst. contradiction.
Qed.

Lemma flen_set : forall (t : array float) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set float t i v). Qed.

Lemma iget_set : forall (t : array int) (p q : int) v, (to_Z p < to_Z (PArray.length t))%Z ->
  t.[p <- v].[q] = if (to_Z p =? to_Z q)%Z then v else t.[q].
Proof.
  intros t p q v H. destruct (to_Z p =? to_Z q)%Z eqn:E.
  - apply Z.eqb_eq, to_Z_inj in E. subst q. refine (get_set_same int t p v _). rewrite Uint63.ltb_spec. exact H.
  - apply Z.eqb_neq in E. refine (get_set_other int t p q v _). intros F. subst. contradiction.
Qed.

Lemma ilen_set : forall (t : array int) i v, PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set int t i v). Qed.

Lemma iget_make : forall (n i v : int), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make int v n i). Qed.

Lemma ilen_make : forall (n : int) (v : int), (to_Z n <= 4194303)%Z ->
  PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  transitivity (if n <=? max_length then n else max_length); [exact (length_make int n v)|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec, max_length_val. exact H.
Qed.

Lemma to_Z_of_Z_n : forall z, (0 <= z <= 4194303)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. apply to_Z_of_Z_small. rewrite wB_val. lia. Qed.

(* ------------------------------------------------------------------ *)
(* The maxima                                                          *)
(* ------------------------------------------------------------------ *)


Lemma big_no_overflow : forall z, Rabs z <= 1000000000000000 -> Rabs (rnd z) < Raux.bpow Zaux.radix2 1024.
Proof.
  intros z Hz. apply rnd_no_overflow_small.
  pose proof (Raux.bpow_le Zaux.radix2 50 1000 ltac:(lia)) as H.
  change (Raux.bpow Zaux.radix2 50) with 1125899906842624 in H. lra.
Qed.

Lemma zs_bound : forall f m, (forall k, (0 <= f k <= 2)%Z) -> (0 <= zs f m <= 2 * Z.of_nat m)%Z.
Proof. intros f m H. induction m; simpl; [lia|]. pose proof (H (Z.of_nat m)). lia. Qed.

Lemma indZ_range : forall a b, (0 <= indZ a b <= 1)%Z.
Proof. intros. unfold indZ. destruct (a =? b)%Z; lia. Qed.

Lemma indR_nonneg : forall a b, 0 <= indR a b.
Proof. intros. unfold indR. destruct (a =? b)%Z; lra. Qed.

Lemma indR_eq : forall a, indR a a = 1.
Proof. intros. unfold indR. rewrite Z.eqb_refl. reflexivity. Qed.

Lemma indR_neq : forall a b, a <> b -> indR a b = 0.
Proof. intros a b H. unfold indR. rewrite (proj2 (Z.eqb_neq a b) H). reflexivity. Qed.

Section Links.
Variables (src dst : list N) (frac : list R) (n L : int) (xs xd : array uint) (xf : array float).
Hypothesis HL : Z.of_nat (List.length src) = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.

Definition tauZ (l x : Z) : Z :=
  if (sr src l =? dr dst l)%Z then 0%Z else (indZ x (sr src l) + indZ x (dr dst l))%Z.

Lemma tauZ_range : forall l x, (0 <= tauZ l x <= 2)%Z.
Proof.
  intros. unfold tauZ. destruct (_ =? _)%Z; [lia|].
  pose proof (indZ_range x (sr src l)). pose proof (indZ_range x (dr dst l)). lia.
Qed.

Lemma cnt_spec : let c := loop L (cnt_step xs xd) 0%uint63 (PArray.make n 0%uint63) in
  PArray.length c = n /\
  forall x, (0 <= x < to_Z n)%Z -> to_Z c.[of_Z x] = zs (fun l => tauZ l x) (List.length src).
Proof.
  intros c. unfold c. rewrite <- (Nat2Z.id (List.length src)), HL.
  apply (for_inv (fun j c => PArray.length c = n /\ forall x, (0 <= x < to_Z n)%Z ->
                    to_Z c.[of_Z x] = zs (fun l => tauZ l x) (Z.to_nat (to_Z j)))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia.
  - split; [apply ilen_make; lia|]. intros x Hx. rewrite iget_make. reflexivity.
  - intros j c0 Hj [Lc Ec]. change (to_Z 0) with 0%Z in Hj.
    assert (E1 : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    assert (Ez : forall x, zs (fun l => tauZ l x) (Z.to_nat (to_Z (j + 1))) =
                 (zs (fun l => tauZ l x) (Z.to_nat (to_Z j)) + tauZ (to_Z j) x)%Z).
    { intros x. rewrite E1, Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. }
    destruct (Hs (to_Z j) Hj) as [Es Bs]. destruct (Hd (to_Z j) Hj) as [Ed Bd].
    rewrite of_to_Z in Es, Ed.
    assert (Bc : forall x, (0 <= x < to_Z n)%Z -> (0 <= to_Z c0.[of_Z x] <= 2 * to_Z j)%Z).
    { intros x Hx. rewrite Ec by exact Hx. pose proof (zs_bound (fun l => tauZ l x) (Z.to_nat (to_Z j)) (fun k => tauZ_range k x)). lia. }
    unfold cnt_step. cbv zeta. destruct (xs.[j] =? xd.[j]) eqn:Esd.
    + apply Uint63.eqb_spec in Esd. split; [exact Lc|]. intros x Hx. rewrite Ez, Ec by exact Hx.
      unfold tauZ. rewrite Esd in Es. rewrite Es in Ed. rewrite Ed, Z.eqb_refl. ring.
    + apply Uint63.eqb_false_spec in Esd.
      assert (Esd' : sr src (to_Z j) <> dr dst (to_Z j)) by (intros F; apply Esd, to_Z_inj; lia).
      set (s := xs.[j]) in *. set (d := xd.[j]) in *.
      assert (Cs := Bc (to_Z s) ltac:(lia)). assert (Cd := Bc (to_Z d) ltac:(lia)).
      rewrite of_to_Z in Cs, Cd.
      split; [rewrite !ilen_set; exact Lc|].
      intros x Hx. rewrite Ez, <- Ec by exact Hx.
      assert (Ix : to_Z (of_Z x) = x) by (apply to_Z_of_Z_n; lia).
      rewrite iget_set by (rewrite ilen_set, Lc; lia).
      rewrite (iget_set c0 s d) by (rewrite Lc; lia).
      rewrite (iget_set c0 s (of_Z x)) by (rewrite Lc; lia).
      rewrite Ix. unfold tauZ. rewrite (proj2 (Z.eqb_neq _ _) Esd'). unfold indZ.
      destruct (Z.eqb_spec (to_Z d) x) as [Edx|Edx].
      * subst x. rewrite (proj2 (Z.eqb_neq (to_Z s) (to_Z d))) by lia.
        rewrite (proj2 (Z.eqb_neq (to_Z d) (sr src (to_Z j)))) by lia.
        rewrite (proj2 (Z.eqb_eq (to_Z d) (dr dst (to_Z j)))) by lia.
        rewrite Uint63.add_spec. change (to_Z 1) with 1%Z. rewrite Z.mod_small by (rewrite wB_val; lia).
        rewrite ?Ix, ?of_to_Z. ring.
      * destruct (Z.eqb_spec (to_Z s) x) as [Esx|Esx].
        -- subst x. rewrite (proj2 (Z.eqb_eq (to_Z s) (sr src (to_Z j)))) by lia.
           rewrite (proj2 (Z.eqb_neq (to_Z s) (dr dst (to_Z j)))) by lia.
           rewrite Uint63.add_spec. change (to_Z 1) with 1%Z. rewrite Z.mod_small by (rewrite wB_val; lia).
           rewrite ?Ix, ?of_to_Z. ring.
        -- rewrite (proj2 (Z.eqb_neq x (sr src (to_Z j)))) by lia.
           rewrite (proj2 (Z.eqb_neq x (dr dst (to_Z j)))) by lia. ring.
Qed.

Definition nsR (l : Z) : R := if (sr src l =? dr dst l)%Z then 0 else 1.
Definition Af (v : array float) (l : Z) : R := rnd (fr frac l * fv v (sr src l)).
Definition gR (v : array float) (l x : Z) : R :=
  nsR l * (indR x (dr dst l) - indR x (sr src l)) * Af v l.
Definition tauR (l x : Z) : R := IZR (tauZ l x).
Definition Mx (v : array float) (x : Z) : R :=
  Rabs (fv v x) + rs (fun l => tauR l x * Rabs (Af v l)) (List.length src).

Lemma tauR_eq : forall l x, tauR l x = nsR l * (indR x (sr src l) + indR x (dr dst l)).
Proof.
  intros. unfold tauR, tauZ, nsR. destruct (_ =? _)%Z; [simpl; ring|].
  rewrite plus_IZR, !IZR_indZ. ring.
Qed.

Lemma tauR_range : forall l x, 0 <= tauR l x <= 2.
Proof. intros. unfold tauR. pose proof (tauZ_range l x) as [H1 H2]. apply IZR_le in H1, H2. simpl in *. lra. Qed.

Lemma gR_abs : forall v l x, Rabs (gR v l x) <= tauR l x * Rabs (Af v l).
Proof.
  intros. unfold gR. rewrite Rabs_mult. apply Rmult_le_compat_r; [apply Rabs_pos|].
  rewrite tauR_eq. unfold nsR, indR.
  destruct (sr src l =? dr dst l)%Z, (x =? dr dst l)%Z, (x =? sr src l)%Z; apply Rabs_le; lra.
Qed.

Lemma psum_le : forall v x k, (k <= List.length src)%nat ->
  Rabs (fv v x + rs (fun l => gR v l x) k) <= Mx v x.
Proof.
  intros v x k Hk. unfold Mx. eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat_l.
  eapply Rle_trans; [apply rs_abs|].
  eapply Rle_trans; [apply rs_le; intros l _; apply gR_abs|].
  apply rs_mono_n; [exact Hk|]. intros l _. pose proof (tauR_range l x). pose proof (Rabs_pos (Af v l)). nra.
Qed.

Lemma gR_self : forall v l x, (sr src l = dr dst l) -> gR v l x = 0.
Proof. intros v l x E. unfold gR, nsR. rewrite (proj2 (Z.eqb_eq _ _) E). ring. Qed.

Lemma fget_copy : forall (v : array float) i, (PArray.copy v).[i] = v.[i].
Proof. intros. exact (get_copy float v i). Qed.

Lemma flen_copy : forall (v : array float), PArray.length (PArray.copy v) = PArray.length v.
Proof. intros. exact (length_copy float v). Qed.

Lemma Af_bound : forall v l, Rabs (fv v (sr src l)) <= 1000000 -> 0 <= fr frac l <= 1 ->
  Rabs (fr frac l * fv v (sr src l)) <= 1000000 /\ Rabs (Af v l) <= 2000001.
Proof.
  intros v l H Hf0. assert (Hp : Rabs (fr frac l * fv v (sr src l)) <= 1000000).
  { rewrite Rabs_mult, (Rabs_right (fr frac l)) by lra. pose proof (Rabs_pos (fv v (sr src l))). nra. }
  split; [exact Hp|]. unfold Af. pose proof (rnd_err (fr frac l * fv v (sr src l))).
  pose proof u_pos. pose proof eta_max_le_u. rewrite u_val in *.
  assert (Rabs (rnd (fr frac l * fv v (sr src l))) <= Rabs (rnd (fr frac l * fv v (sr src l)) - fr frac l * fv v (sr src l)) + Rabs (fr frac l * fv v (sr src l)))
    by (replace (rnd _) with ((rnd (fr frac l * fv v (sr src l)) - fr frac l * fv v (sr src l)) + fr frac l * fv v (sr src l)) at 1 by ring; apply Rabs_triang).
  assert (/ 4503599627370496 / 2 * Rabs (fr frac l * fv v (sr src l)) <= / 4503599627370496 / 2 * 1000000)
    by (apply Rmult_le_compat_l; lra).
  lra.
Qed.

Lemma unit_spec : forall v, okv v (to_Z n) ->
  (forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i) <= 1000000) ->
  let w := unit_f L xs xd xf v in
  okv w (to_Z n) /\ forall x, (0 <= x < to_Z n)%Z ->
    Rabs (fv w x - fv v x - rs (fun l => gR v l x) (List.length src)) <=
    IZR (zs (fun l => tauZ l x) (List.length src)) * u * (Mx v x + 1).
Proof.
  intros v Okv Hvb w. unfold w, unit_f. clear w.
  assert (HAf : forall l, (0 <= l < to_Z L)%Z -> Rabs (Af v l) <= 2000001).
  { intros l Hl. destruct (Hs l Hl) as [_ Bs]. destruct (Hf l Hl) as [_ Bf].
    apply (Af_bound v l (Hvb _ Bs)). lra. }
  assert (HM : forall x, (0 <= x < to_Z n)%Z -> Mx v x <= 100000000000).
  { intros x Hx. unfold Mx. pose proof (Hvb x Hx).
    assert (rs (fun l => tauR l x * Rabs (Af v l)) (List.length src) <= INR (List.length src) * 4000002).
    { apply rs_const_le. intros l Hl. pose proof (tauR_range l x). pose proof (HAf l ltac:(lia)).
      pose proof (Rabs_pos (Af v l)). nra. }
    rewrite INR_IZR_INZ, HL in H0. apply IZR_le in HLb. lra. }
  assert (Hcu : forall x j, (j <= List.length src)%nat ->
            0 <= IZR (zs (fun l => tauZ l x) j) /\ IZR (zs (fun l => tauZ l x) j) * u <= 1).
  { intros x j Hj. pose proof (zs_bound (fun l => tauZ l x) j (fun k => tauZ_range k x)) as [H1 H2].
    apply IZR_le in H1, H2. rewrite mult_IZR in H2. rewrite u_val. split; [exact H1|].
    assert (IZR (Z.of_nat j) <= 9801) by (apply IZR_le; lia). simpl in H2. lra. }
  rewrite <- (Nat2Z.id (List.length src)). rewrite HL.
  apply (for_inv (fun j w => okv w (to_Z n) /\ forall x, (0 <= x < to_Z n)%Z ->
    Rabs (fv w x - fv v x - rs (fun l => gR v l x) (Z.to_nat (to_Z j))) <=
    IZR (zs (fun l => tauZ l x) (Z.to_nat (to_Z j))) * u * (Mx v x + 1))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia.
  - split.
    + destruct Okv as [Lv Fv]. split; [rewrite flen_copy; exact Lv|]. intros i Hi. rewrite fget_copy. apply Fv, Hi.
    + intros x Hx. unfold fv at 1. rewrite fget_copy. fold (fv v x). simpl.
      replace (fv v x - fv v x - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - intros j w Hj [Okw IH]. change (to_Z 0) with 0%Z in Hj.
    set (jz := to_Z j) in *.
    assert (E1 : to_Z (j + 1) = (jz + 1)%Z) by (unfold jz; sia).
    assert (Hjn : (Z.to_nat (to_Z (j + 1)) <= List.length src)%nat) by lia.
    assert (Ez : forall x, zs (fun l => tauZ l x) (Z.to_nat (to_Z (j + 1))) =
                 (zs (fun l => tauZ l x) (Z.to_nat jz) + tauZ jz x)%Z).
    { intros x. rewrite E1, Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. }
    assert (Er : forall x, rs (fun l => gR v l x) (Z.to_nat (to_Z (j + 1))) =
                 rs (fun l => gR v l x) (Z.to_nat jz) + gR v jz x).
    { intros x. rewrite E1, Z2Nat.inj_add, Nat.add_1_r by lia. simpl. rewrite Z2Nat.id by lia. reflexivity. }
    destruct (Hs jz Hj) as [Es Bs]. destruct (Hd jz Hj) as [Ed Bd]. destruct (Hf jz Hj) as [Hfj Bf].
    unfold jz in Es, Ed, Hfj. rewrite of_to_Z in Es, Ed, Hfj. fold jz in Es, Ed, Hfj.
    unfold link_f. cbv zeta. destruct (xs.[j] =? xd.[j]) eqn:Esd.
    + apply Uint63.eqb_spec in Esd. rewrite Esd in Es. rewrite Es in Ed.
      split; [exact Okw|]. intros x Hx. rewrite Ez, Er, (gR_self v jz x) by lia.
      unfold tauZ. rewrite (proj2 (Z.eqb_eq _ _)) by lia. rewrite Z.add_0_r, Rplus_0_r. apply IH, Hx.
    + apply Uint63.eqb_false_spec in Esd.
      assert (Esd' : sr src jz <> dr dst jz) by (intros F; apply Esd, to_Z_inj; lia).
      set (s := xs.[j]) in *. set (d := xd.[j]) in *.
      set (s' := sr src jz) in *. set (d' := dr dst jz) in *.
      assert (Hvs : repr v.[s] (fv v s')) by (rewrite <- (of_to_Z s), Es; apply (okv_repr v (to_Z n)); [exact Okv | lia]).
      assert (Hws : repr w.[s] (fv w s')) by (rewrite <- (of_to_Z s), Es; apply (okv_repr w (to_Z n)); [exact Okw | lia]).
      assert (Hwd : repr w.[d] (fv w d')) by (rewrite <- (of_to_Z d), Ed; apply (okv_repr w (to_Z n)); [exact Okw | lia]).
      set (A := Af v jz).
      assert (Ha : repr (xf.[j] * v.[s])%float A).
      { unfold A, Af. fold s'. apply repr_mul; [exact Hfj | exact Hvs |].
        apply big_no_overflow. pose proof (Af_bound v jz (Hvb s' ltac:(lia)) ltac:(lra)) as [H1 _]. fold s' in H1. lra. }
      assert (GD : gR v jz d' = A).
      { unfold gR, nsR. fold s' d'. rewrite (proj2 (Z.eqb_neq _ _) Esd'), indR_eq, indR_neq by lia. fold A. ring. }
      assert (GS : gR v jz s' = - A).
      { unfold gR, nsR. fold s' d'. rewrite (proj2 (Z.eqb_neq _ _) Esd'), indR_eq, indR_neq by lia. fold A. ring. }
      assert (TD : tauZ jz d' = 1%Z).
      { unfold tauZ. fold s' d'. rewrite (proj2 (Z.eqb_neq _ _) Esd'). unfold indZ.
        rewrite Z.eqb_refl, (proj2 (Z.eqb_neq d' s')) by lia. reflexivity. }
      assert (TS : tauZ jz s' = 1%Z).
      { unfold tauZ. fold s' d'. rewrite (proj2 (Z.eqb_neq _ _) Esd'). unfold indZ.
        rewrite Z.eqb_refl, (proj2 (Z.eqb_neq s' d')) by lia. reflexivity. }
      assert (TO : forall x, x <> s' -> x <> d' -> tauZ jz x = 0%Z /\ gR v jz x = 0).
      { intros x H1 H2. unfold tauZ, gR, nsR. fold s' d'. rewrite (proj2 (Z.eqb_neq _ _) Esd'). unfold indZ.
        rewrite !indR_neq by assumption. rewrite (proj2 (Z.eqb_neq x s')), (proj2 (Z.eqb_neq x d')) by assumption.
        split; [reflexivity | ring]. }
      (* the two rounded operations *)
      destruct (Hcu d' (Z.to_nat jz) ltac:(lia)) as [Cd0 Cd1].
      destruct (Hcu s' (Z.to_nat jz) ltac:(lia)) as [Cs0 Cs1].
      destruct (op_err (fv w d' + A) (fv v d' + rs (fun l => gR v l d') (Z.to_nat (to_Z (j + 1)))) (Mx v d')
                  _ Cd0 Cd1 (psum_le v d' _ Hjn)) as [OD BD].
      { rewrite Er, GD. replace (fv w d' + A - (fv v d' + (rs (fun l => gR v l d') (Z.to_nat jz) + A)))
          with (fv w d' - fv v d' - rs (fun l => gR v l d') (Z.to_nat jz)) by ring. apply IH. lia. }
      destruct (op_err (fv w s' - A) (fv v s' + rs (fun l => gR v l s') (Z.to_nat (to_Z (j + 1)))) (Mx v s')
                  _ Cs0 Cs1 (psum_le v s' _ Hjn)) as [OS BS].
      { rewrite Er, GS. replace (fv w s' - A - (fv v s' + (rs (fun l => gR v l s') (Z.to_nat jz) + - A)))
          with (fv w s' - fv v s' - rs (fun l => gR v l s') (Z.to_nat jz)) by ring. apply IH. lia. }
      pose proof (HM d' ltac:(lia)). pose proof (HM s' ltac:(lia)).
      assert (Rd : repr (w.[d] + (xf.[j] * v.[s]))%float (rnd (fv w d' + A)))
        by (apply repr_add; [exact Hwd | exact Ha | apply big_no_overflow; lra]).
      assert (Rs : repr (w.[s] - (xf.[j] * v.[s]))%float (rnd (fv w s' - A)))
        by (apply repr_sub; [exact Hws | exact Ha | apply big_no_overflow; lra]).
      destruct Okw as [Lw Fw].
      assert (W1s : (w.[d <- (w.[d] + xf.[j] * v.[s])%float]).[s] = w.[s])
        by (rewrite fget_set by lia; rewrite (proj2 (Z.eqb_neq _ _)) by lia; reflexivity).
      rewrite W1s.
      set (w2 := (w.[d <- (w.[d] + xf.[j] * v.[s])%float]).[s <- (w.[s] - xf.[j] * v.[s])%float]).
      assert (Hw2 : forall x, (0 <= x < to_Z n)%Z ->
        repr w2.[of_Z x] (if (x =? s')%Z then rnd (fv w s' - A) else if (x =? d')%Z then rnd (fv w d' + A) else fv w x)).
      { intros x Hx. assert (Ix : to_Z (of_Z x) = x) by (apply to_Z_of_Z_n; lia).
        unfold w2. rewrite fget_set by (rewrite flen_set; lia). rewrite Ix, Es.
        destruct (Z.eqb_spec s' x) as [<- | E1']; [rewrite Z.eqb_refl; exact Rs|].
        rewrite (proj2 (Z.eqb_neq x s')) by lia.
        rewrite fget_set by lia. rewrite Ix, Ed.
        destruct (Z.eqb_spec d' x) as [<- | E2']; [rewrite Z.eqb_refl; exact Rd|].
        rewrite (proj2 (Z.eqb_neq x d')) by lia. apply (okv_repr w (to_Z n)); [split; assumption | exact Hx]. }
      split.
      * split; [unfold w2; rewrite !flen_set; exact Lw|]. intros i Hi. exact (proj1 (Hw2 i Hi)).
      * intros x Hx. unfold fv at 1. rewrite (repr_fval _ _ (Hw2 x Hx)). rewrite Ez, plus_IZR.
        destruct (Z.eqb_spec x s') as [-> | E1'].
        -- rewrite TS. replace (rnd (fv w s' - A) - fv v s' - rs (fun l => gR v l s') (Z.to_nat (to_Z (j + 1))))
             with (rnd (fv w s' - A) - (fv v s' + rs (fun l => gR v l s') (Z.to_nat (to_Z (j + 1))))) by ring.
           exact OS.
        -- destruct (Z.eqb_spec x d') as [-> | E2'].
           ++ rewrite TD. replace (rnd (fv w d' + A) - fv v d' - rs (fun l => gR v l d') (Z.to_nat (to_Z (j + 1))))
                with (rnd (fv w d' + A) - (fv v d' + rs (fun l => gR v l d') (Z.to_nat (to_Z (j + 1))))) by ring.
              exact OD.
           ++ destruct (TO x E1' E2') as [T1 T2]. rewrite T1, Er, T2, Rplus_0_r, Rplus_0_r. apply IH, Hx.
Qed.

End Links.

(* ------------------------------------------------------------------ *)
(* The error of one time unit, against the exact step                  *)
(* ------------------------------------------------------------------ *)

Lemma eta_small : 20000 * eta_max <= u / 4.
Proof.
  pose proof (Raux.bpow_le Zaux.radix2 (-1075) (-80) ltac:(lia)) as H. fold eta_max in H.
  replace (Raux.bpow Zaux.radix2 (-80)) with (/ 1208925819614629174706176) in H by reflexivity.
  rewrite u_val. lra.
Qed.

Section StepErr.
Variables (t0 : N) (us : list R) (src dst : list N) (frac : list R).
Hypothesis Hv : valid_input t0 us src dst frac.
Let nn := List.length us.
Let Lr := List.length src.

Lemma tauR_r : forall l x, 0 <= tauR src dst l x <= 2.
Proof. exact (tauR_range src dst 0%uint63 0%uint63). Qed.

Lemma Am_apply : forall (X : Z -> R) i, (0 <= i < Z.of_nat nn)%Z ->
  rs (fun j => Am src dst frac i j * X j) nn =
  X i + rs (fun l => fr frac l * (indR i (dr dst l) * X (sr src l) - indR i (sr src l) * X (sr src l))) Lr.
Proof.
  intros X i Hi. unfold Am.
  rewrite (rs_ext _ (fun j => indR j i * X j +
     rs (fun l => fr frac l * indR i (dr dst l) * (indR j (sr src l) * X j)
                  - fr frac l * indR i (sr src l) * (indR j (sr src l) * X j)) (List.length src))).
  2: { intros j _. rewrite Rmult_plus_distr_r, <- rs_scal_r, (indR_sym i j).
       f_equal. apply rs_ext. intros. ring. }
  rewrite rs_add, (rs_indR_r X) by exact Hi. f_equal.
  rewrite rs_swap. apply rs_ext. intros l Hl. pose proof (sr_range t0 us src dst frac nn Hv (le_n _) l Hl).
  rewrite rs_sub, !rs_scal, !(rs_indR_r X) by lia. ring.
Qed.


End StepErr.


(* ------------------------------------------------------------------ *)
(* The faced values, their minimum                                     *)
(* ------------------------------------------------------------------ *)

Lemma rs_pick : forall (f : Z -> R) (J : Z -> bool) i nn k, (0 <= i < Z.of_nat nn)%Z -> J i = false ->
  (k <= nn)%nat -> (forall m, 0 <= f m) ->
  f i + rs (fun m => if J m then f m else 0) k <= rs f nn.
Proof.
  intros f J i nn k Hi HJ Hk Hf.
  assert (rs (fun m => if J m then f m else 0) k <= rs (fun m => if J m then f m else 0) nn)
    by (apply rs_mono_n; [exact Hk | intros m _; destruct (J m); [apply Hf | lra]]).
  assert (E : f i = rs (fun m => if (m =? i)%Z then f m else 0) nn) by (rewrite rs_ind_in by exact Hi; reflexivity).
  rewrite E. eapply Rle_trans; [apply Rplus_le_compat_l; exact H|]. rewrite <- rs_add. apply rs_le.
  intros m _. destruct (Z.eqb_spec m i) as [-> | Em]; [rewrite HJ; lra|]. destruct (J m); pose proof (Hf m); lra.
Qed.

Lemma loop_fmin : forall (n : int) (g : int -> float) (G : Z -> R), (1 <= to_Z n)%Z ->
  (forall i : int, (to_Z i < to_Z n)%Z -> repr (g i) (G (to_Z i))) ->
  exists ic, (0 <= ic < to_Z n)%Z /\ repr (loop n (fun i b => fmin b (g i)) 1%uint63 (g 0%uint63)) (G ic) /\
    forall i, (0 <= i < to_Z n)%Z -> G ic <= G i.
Proof.
  intros n g G Hn Hg.
  apply (for_inv (fun j b => exists ic, (0 <= ic < to_Z n)%Z /\ repr b (G ic) /\
                    forall i, (0 <= i < to_Z j)%Z -> G ic <= G i)).
  - change (to_Z 1) with 1%Z. exact Hn.
  - exists 0%Z. split; [lia|]. split; [apply (Hg 0%uint63); change (to_Z 0%uint63) with 0%Z; lia|].
    intros i Hi. change (to_Z 1) with 1%Z in Hi. replace i with 0%Z by lia. lra.
  - intros j b Hj (ic & Hic & Hb & Hm). change (to_Z 1) with 1%Z in Hj.
    assert (E : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    pose proof (Hg j ltac:(lia)) as Hgj.
    unfold fmin. pose proof (repr_ltb_iff (g j) b (G (to_Z j)) (G ic) Hgj Hb) as Hlt.
    destruct (g j <? b)%float eqn:Ec.
    + exists (to_Z j). split; [lia|]. split; [exact Hgj|].
      intros i Hi. rewrite E in Hi. destruct (Z.eq_dec i (to_Z j)) as [-> | Ei]; [lra|].
      pose proof (Hm i ltac:(lia)). pose proof (proj1 Hlt eq_refl). lra.
    + exists ic. split; [exact Hic|]. split; [exact Hb|].
      intros i Hi. rewrite E in Hi. destruct (Z.eq_dec i (to_Z j)) as [-> | Ei]; [| apply Hm; lia].
      destruct (Rlt_le_dec (G (to_Z j)) (G ic)) as [Hl | Hl]; [apply Hlt in Hl; discriminate | exact Hl].
Qed.

(* ------------------------------------------------------------------ *)
(* The check                                                           *)
(* ------------------------------------------------------------------ *)


Lemma IZR_shiftl : forall x k, (0 <= k)%Z -> IZR (Z.shiftl x k) = IZR x * bp k.
Proof. intros x k Hk. rewrite Z.shiftl_mul_pow2 by exact Hk. rewrite mult_IZR, IZR_pow2 by exact Hk. reflexivity. Qed.

Lemma dlt_spec : forall x a y b, dlt x a y b = true -> IZR x * bp a < IZR y * bp b.
Proof.
  intros x a y b H. unfold dlt in H. pose proof (Raux.bpow_gt_0 Zaux.radix2 a). pose proof (Raux.bpow_gt_0 Zaux.radix2 b).
  destruct (Z.leb_spec a b) as [Hab | Hab]; apply Z.ltb_lt in H; apply IZR_lt in H.
  - rewrite IZR_shiftl in H by lia.
    assert (E : bp b = bp (b - a) * bp a) by (rewrite <- Raux.bpow_plus; f_equal; ring). rewrite E.
    apply Rmult_lt_compat_r with (r := bp a) in H; [| exact H0]. lra.
  - rewrite IZR_shiftl in H by lia.
    assert (E : bp a = bp (a - b) * bp b) by (rewrite <- Raux.bpow_plus; f_equal; ring). rewrite E.
    apply Rmult_lt_compat_r with (r := bp b) in H; [| exact H1]. lra.
Qed.


Lemma half_u : u / 2 = bp (-53).
Proof. unfold u. change (-52)%Z with (-53 + 1)%Z. rewrite Raux.bpow_plus_1. change (IZR (Zaux.radix_val Zaux.radix2)) with 2. field. Qed.


Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* Constants                                                           *)
(* ------------------------------------------------------------------ *)

Local Open Scope R_scope.

Lemma repr_fu : repr f_u u.
Proof. split; [reflexivity|]. rewrite u_val. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl powerRZ. lra. Qed.

Lemma repr_K1 : repr f_K1 (1 + / 1073741824).
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl powerRZ. lra. Qed.

Lemma repr_s30 : repr f_s30 (/ 1073741824).
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl powerRZ. lra. Qed.

Lemma repr_one : repr 1%float 1.
Proof. split; [reflexivity|]. unfold fval. vm_compute Prim2SF. cbv iota beta. simpl powerRZ. lra. Qed.

Lemma eta_tiny : eta_max <= / 10 ^ 300.
Proof.
  unfold eta_max. pose proof (Raux.bpow_le Zaux.radix2 (-1075) (-1000) ltac:(lia)) as H.
  eapply Rle_trans; [exact H|]. replace (bp (-1000)) with (/ bp 1000) by (rewrite <- Raux.bpow_opp; reflexivity).
  apply Rinv_le_contravar; [apply pow_lt; lra|].
  replace (10 ^ 300) with (IZR (10 ^ 300)) by (rewrite pow_IZR; reflexivity).
  change (bp 1000) with (IZR (2 ^ 1000)). apply IZR_le. vm_compute. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Upward bounds through rounded operations                           *)
(* ------------------------------------------------------------------ *)

Definition q (k : nat) : R := (1 + u) ^ k.

(* x is a nonneg finite float within the factor q k (and k eta) of X >= 0, both ways *)
Definition ap (k : nat) (x : float) (X : R) : Prop :=
  PrimFloat.is_finite x = true /\ 0 <= X /\ 0 <= fval x /\
  X <= q k * (fval x + INR k * eta_max) /\ fval x <= q k * (X + INR k * eta_max).

Lemma q_ge1 : forall k, 1 <= q k.
Proof. intros. unfold q. apply pow_R1_Rle. pose proof u_pos. lra. Qed.

Lemma q_mono : forall a b, (a <= b)%nat -> q a <= q b.
Proof. intros. unfold q. apply Rle_pow; [pose proof u_pos; lra | exact H]. Qed.

Lemma INR_200k : forall k, (Z.of_nat k <= 200000)%Z -> INR k <= 200000.
Proof. intros k H. rewrite INR_IZR_INZ. apply IZR_le in H. exact H. Qed.

Lemma q_small : forall k, (Z.of_nat (k) <= 200000)%Z -> q k <= 1 + / 10000000000.
Proof.
  intros k Hk. unfold q. pose proof u_pos. apply INR_200k in Hk. pose proof (pos_INR k).
  assert (INR k * u <= 200000 * u) by (apply Rmult_le_compat_r; lra).
  eapply Rle_trans; [apply pow_bern; rewrite u_val in *; lra|]. rewrite u_val in *. lra.
Qed.

Lemma q_S : forall k, q (k + 1) = q k * (1 + u).
Proof. intros. unfold q. rewrite pow_add. simpl. ring. Qed.

Lemma rnd_nonneg : forall z, 0 <= z -> 0 <= rnd z.
Proof. intros z H. rewrite <- rnd_0. apply rnd_le. exact H. Qed.

Lemma rnd_lo : forall z, 0 <= z -> z * (1 - u / 2) - eta_max <= rnd z.
Proof.
  intros z Hz. destruct (rnd_model z) as (eps & eta & He & Hn & _ & ->).
  apply Raux.Rabs_le_inv in He. apply Raux.Rabs_le_inv in Hn.
  assert (z * (1 - u / 2) <= z * (1 + eps)) by (apply Rmult_le_compat_l; lra). lra.
Qed.

Lemma rnd_hi : forall z, 0 <= z -> rnd z <= z * (1 + u / 2) + eta_max.
Proof.
  intros z Hz. destruct (rnd_model z) as (eps & eta & He & Hn & _ & ->).
  apply Raux.Rabs_le_inv in He. apply Raux.Rabs_le_inv in Hn.
  assert (z * (1 + eps) <= z * (1 + u / 2)) by (apply Rmult_le_compat_l; lra). lra.
Qed.

Lemma rnd_up : forall z, 0 <= z ->
  z <= (1 + u) * (rnd z + eta_max) /\ rnd z <= (1 + u) * (z + eta_max).
Proof.
  intros z Hz. pose proof (rnd_lo z Hz). pose proof (rnd_hi z Hz). pose proof u_pos.
  pose proof eta_max_pos. pose proof eta_max_le_u. rewrite u_val in *. split.
  - assert (z <= (1 + / 4503599627370496) * (z * (1 - / 4503599627370496 / 2))) by nra. nra.
  - nra.
Qed.

Lemma ap_exact : forall x X, repr x X -> 0 <= X -> ap 0 x X.
Proof.
  intros x X [F E] H. unfold ap, q. simpl. rewrite E. repeat split; try lra. exact F.
Qed.

Lemma ap_mono : forall a b x X, (a <= b)%nat -> ap a x X -> ap b x X.
Proof.
  intros a b x X Hab (F & H0 & H1 & H2 & H3). pose proof (q_mono a b Hab). pose proof (q_ge1 a).
  apply le_INR in Hab. pose proof eta_max_pos. pose proof (pos_INR a).
  assert (INR a * eta_max <= INR b * eta_max) by (apply Rmult_le_compat_r; lra).
  repeat split; try assumption.
  - eapply Rle_trans; [exact H2|]. apply Rmult_le_compat; nra.
  - eapply Rle_trans; [exact H3|]. apply Rmult_le_compat; nra.
Qed.

Lemma ap_le2 : forall k x X, (Z.of_nat (k) <= 200000)%Z -> ap k x X ->
  fval x <= 2 * X + 1 /\ X <= 2 * fval x + 1.
Proof.
  intros k x X Hk (F & H0 & H1 & H2 & H3). pose proof (q_small k Hk). pose proof (q_ge1 k).
  pose proof eta_tiny. pose proof eta_max_pos. apply INR_200k in Hk. pose proof (pos_INR k).
  assert (INR k * eta_max <= 200000 * / 10 ^ 300) by (apply Rmult_le_compat; lra).
  assert (/ 10 ^ 300 <= / 10 ^ 6) by (apply Rinv_le_contravar; [apply pow_lt; lra | apply Rle_pow; [lra | lia]]).
  assert (/ 10 ^ 6 = 1 / 1000000) by (simpl; lra).
  split; nra.
Qed.

Lemma ap_add : forall a b x y X Y, (Z.of_nat (a + b + 1) <= 200000)%Z -> ap a x X -> ap b y Y ->
  X + Y <= 100000000000000 -> ap (a + b + 1) (x + y)%float (X + Y).
Proof.
  intros a b x y X Y Hk Ha Hb HXY.
  pose proof (ap_le2 a x X ltac:(lia) Ha) as [La _]. pose proof (ap_le2 b y Y ltac:(lia) Hb) as [Lb _].
  destruct Ha as (Fa & Xa & Pa & A1 & A2). destruct Hb as (Fb & Xb & Pb & B1 & B2).
  set (z := fval x + fval y).
  assert (Hr : repr (x + y)%float (rnd z)).
  { apply repr_add; [split; [exact Fa | reflexivity] | split; [exact Fb | reflexivity] |].
    apply big_no_overflow. unfold z. rewrite Rabs_right; lra. }
  destruct Hr as [Fr Er]. unfold ap. rewrite Er.
  assert (Hz : 0 <= z) by (unfold z; lra).
  destruct (rnd_up z Hz) as [U1 U2]. pose proof (rnd_nonneg z Hz).
  pose proof (q_mono a (a + b) ltac:(lia)). pose proof (q_mono b (a + b) ltac:(lia)).
  pose proof (q_ge1 a). pose proof (q_ge1 b). pose proof (q_ge1 (a + b)). pose proof u_pos.
  pose proof eta_max_pos. pose proof (pos_INR a). pose proof (pos_INR b).
  rewrite q_S, !plus_INR. simpl INR.
  assert (Ea : INR a * eta_max >= 0) by nra. assert (Eb : INR b * eta_max >= 0) by nra.
  repeat split; try assumption; try lra.
  - (* X + Y <= ... *)
    assert (X <= q (a + b) * (fval x + INR a * eta_max)) by (eapply Rle_trans; [exact A1|]; apply Rmult_le_compat_r; lra).
    assert (Y <= q (a + b) * (fval y + INR b * eta_max)) by (eapply Rle_trans; [exact B1|]; apply Rmult_le_compat_r; lra).
    assert (q (a + b) * z <= q (a + b) * ((1 + u) * (rnd z + eta_max))) by (apply Rmult_le_compat_l; lra).
    assert (q (a + b) * ((INR a + INR b) * eta_max) <= q (a + b) * (1 + u) * ((INR a + INR b) * eta_max))
      by (apply Rmult_le_compat_r; nra).
    unfold z in *. nra.
  - assert (fval x <= q (a + b) * (X + INR a * eta_max)) by (eapply Rle_trans; [exact A2|]; apply Rmult_le_compat_r; lra).
    assert (fval y <= q (a + b) * (Y + INR b * eta_max)) by (eapply Rle_trans; [exact B2|]; apply Rmult_le_compat_r; lra).
    assert (z <= q (a + b) * (X + Y + (INR a + INR b) * eta_max)) by (unfold z; nra).
    assert ((1 + u) * (z + eta_max) <= (1 + u) * (q (a + b) * (X + Y + (INR a + INR b) * eta_max) + eta_max))
      by (apply Rmult_le_compat_l; lra).
    assert (eta_max <= q (a + b) * eta_max) by nra.
    nra.
Qed.

Lemma ap_mulc : forall a c x C X, (Z.of_nat (a + 1) <= 200000)%Z -> repr c C -> 0 <= C <= 1 -> ap a x X ->
  X <= 100000000000000 -> ap (a + 1) (c * x)%float (C * X).
Proof.
  intros a c x C X Hk Hc HC Ha HX.
  pose proof (ap_le2 a x X ltac:(lia) Ha) as [La _].
  destruct Ha as (Fa & Xa & Pa & A1 & A2).
  set (z := C * fval x).
  assert (Hz : 0 <= z) by (unfold z; nra).
  assert (Hr : repr (c * x)%float (rnd z)).
  { apply repr_mul; [exact Hc | split; [exact Fa | reflexivity] |].
    apply big_no_overflow. rewrite Rabs_right by (apply Rle_ge; exact Hz). unfold z. nra. }
  destruct Hr as [Fr Er]. unfold ap. rewrite Er.
  destruct (rnd_up z Hz) as [U1 U2]. pose proof (rnd_nonneg z Hz).
  pose proof (q_ge1 a). pose proof u_pos. pose proof eta_max_pos. pose proof (pos_INR a).
  rewrite q_S, !plus_INR. simpl INR.
  repeat split; try assumption; try nra.
  - assert (C * X <= C * (q a * (fval x + INR a * eta_max))) by (apply Rmult_le_compat_l; lra).
    assert (C * (INR a * eta_max) <= INR a * eta_max)
      by (rewrite <- (Rmult_1_l (INR a * eta_max)) at 2; apply Rmult_le_compat_r; nra).
    assert (C * (q a * (fval x + INR a * eta_max)) <= q a * (z + INR a * eta_max)).
    { replace (C * (q a * (fval x + INR a * eta_max))) with (q a * (z + C * (INR a * eta_max))) by (unfold z; ring).
      apply Rmult_le_compat_l; lra. }
    assert (q a * z <= q a * ((1 + u) * (rnd z + eta_max))) by (apply Rmult_le_compat_l; lra).
    assert (0 <= q a * (INR a * eta_max)) by (apply Rmult_le_pos; [lra | apply Rmult_le_pos; lra]).
    assert (0 <= u * (q a * (INR a * eta_max))) by (apply Rmult_le_pos; lra).
    assert (q a * (INR a * eta_max) <= q a * (1 + u) * (INR a * eta_max)).
    { replace (q a * (1 + u) * (INR a * eta_max)) with (q a * (INR a * eta_max) + u * (q a * (INR a * eta_max))) by ring. lra. }
    nra.
  - assert (z <= C * (q a * (X + INR a * eta_max))) by (unfold z; apply Rmult_le_compat_l; lra).
    assert (C * (INR a * eta_max) <= INR a * eta_max)
      by (rewrite <- (Rmult_1_l (INR a * eta_max)) at 2; apply Rmult_le_compat_r; nra).
    assert (C * (q a * (X + INR a * eta_max)) <= q a * (C * X + INR a * eta_max)).
    { replace (C * (q a * (X + INR a * eta_max))) with (q a * (C * X + C * (INR a * eta_max))) by ring.
      apply Rmult_le_compat_l; lra. }
    assert (eta_max <= q a * eta_max) by (rewrite <- (Rmult_1_l eta_max) at 1; apply Rmult_le_compat_r; lra).
    assert (Hz5 : z + eta_max <= q a * (C * X + (INR a + 1) * eta_max)).
    { replace (q a * (C * X + (INR a + 1) * eta_max)) with (q a * (C * X + INR a * eta_max) + q a * eta_max) by ring. lra. }
    eapply Rle_trans; [exact U2|].
    replace (q a * (1 + u) * (C * X + (INR a + 1) * eta_max)) with ((1 + u) * (q a * (C * X + (INR a + 1) * eta_max))) by ring.
    apply Rmult_le_compat_l; lra.
Qed.

Lemma ap_mul0 : forall x y X Y, repr x X -> repr y Y -> 0 <= X -> 0 <= Y ->
  X * Y <= 100000000000000 -> ap 1 (x * y)%float (X * Y).
Proof.
  intros x y X Y Hx Hy HX HY HXY.
  assert (Hz : 0 <= X * Y) by nra.
  assert (Hr : repr (x * y)%float (rnd (X * Y))).
  { apply repr_mul; [exact Hx | exact Hy |]. apply big_no_overflow. rewrite Rabs_right; lra. }
  destruct Hr as [Fr Er]. destruct (rnd_up _ Hz) as [U1 U2]. pose proof (rnd_nonneg _ Hz).
  pose proof eta_max_pos. pose proof u_pos.
  unfold ap, q. rewrite Er. simpl. repeat split; try assumption; lra.
Qed.

(* the final step: a float above X *)
Lemma ap_up : forall k x X, (Z.of_nat (k) <= 200000)%Z -> ap k x X -> X <= 100000000000000 ->
  exists Y, repr (up x) Y /\ X <= Y /\ Y <= 3 * X + 2.
Proof.
  intros k x X Hk Ha HX.
  pose proof (ap_le2 k x X Hk Ha) as [La _].
  destruct Ha as (Fa & Xa & Pa & A1 & A2).
  pose proof (q_small k Hk). pose proof (q_ge1 k). pose proof u_pos. pose proof eta_max_pos. pose proof eta_tiny.
  apply INR_200k in Hk. pose proof (pos_INR k).
  set (K := 1 + / 1073741824).
  set (z1 := fval x * K).
  assert (Hz1 : 0 <= z1) by (unfold z1, K; nra).
  assert (R1 : repr (x * f_K1)%float (rnd z1)).
  { apply repr_mul; [split; [exact Fa | reflexivity] | exact repr_K1 |].
    apply big_no_overflow. rewrite Rabs_right by (apply Rle_ge; exact Hz1). unfold z1, K. nra. }
  pose proof (rnd_nonneg z1 Hz1). pose proof (rnd_lo z1 Hz1). pose proof (rnd_hi z1 Hz1).
  assert (Bz1 : z1 <= 300000000000000) by (unfold z1, K; nra).
  assert (Br1 : rnd z1 <= 2 * z1 + 1).
  { assert (z1 * (1 + u / 2) <= z1 * 2) by (apply Rmult_le_compat_l; [lra | rewrite u_val; lra]).
    pose proof eta_max_le_u. rewrite u_val in *. lra. }
  set (z2 := rnd z1 + u).
  assert (Hz2 : 0 <= z2) by (unfold z2; lra).
  assert (R2 : repr (x * f_K1 + f_u)%float (rnd z2)).
  { apply repr_add; [exact R1 | exact repr_fu |].
    apply big_no_overflow. rewrite Rabs_right by (apply Rle_ge; exact Hz2). unfold z2. rewrite u_val in *. lra. }
  pose proof (rnd_lo z2 Hz2). pose proof (rnd_hi z2 Hz2).
  exists (rnd z2). split; [exact R2|].
  assert (INR k * eta_max <= 200000 * / 10 ^ 300) by (apply Rmult_le_compat; lra).
  assert (/ 10 ^ 300 <= / 10 ^ 30) by (apply Rinv_le_contravar; [apply pow_lt; lra | apply Rle_pow; [lra | lia]]).
  assert (E30 : / 10 ^ 30 = / 1000000000000000000000000000000) by (simpl; lra).
  unfold z2, z1, K in *. rewrite u_val in *.
  assert (0 <= INR k * eta_max) by (apply Rmult_le_pos; lra).
  assert (X <= (1 + / 10000000000) * (fval x + INR k * eta_max)) by (eapply Rle_trans; [exact A1|]; apply Rmult_le_compat_r; lra).
  split; lra.
Qed.

Lemma ap_eq : forall k k' x X X', ap k x X -> k = k' -> X = X' -> ap k' x X'.
Proof. intros. subst. assumption. Qed.

Lemma ap_val : forall k x X, ap k x X -> repr x (fval x).
Proof. intros k x X (F & _). split; [exact F | reflexivity]. Qed.

(* ------------------------------------------------------------------ *)
(* Loop plumbing                                                       *)
(* ------------------------------------------------------------------ *)

Lemma int_next : forall j : int, (0 <= to_Z j < 4194303)%Z ->
  to_Z (j + 1) = (to_Z j + 1)%Z /\ Z.to_nat (to_Z (j + 1)) = S (Z.to_nat (to_Z j)).
Proof. intros j Hj. assert (E : to_Z (j + 1) = (to_Z j + 1)%Z) by sia. split; [exact E | rewrite E; lia]. Qed.

Lemma rs_S : forall f k, rs f (S k) = rs f k + f (Z.of_nat k).
Proof. reflexivity. Qed.

Lemma fget_make : forall (n i : int) (v : float), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make float v n i). Qed.

Lemma flen_make : forall (n : int) (v : float), (to_Z n <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  transitivity (if n <=? max_length then n else max_length); [exact (length_make float n v)|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec, max_length_val. exact H.
Qed.

Lemma repr_zero' : repr 0%float 0.
Proof. split; reflexivity. Qed.

Lemma Rabs_tri : forall a b, Rabs a <= Rabs b + Rabs (a - b).
Proof. intros. replace a with (b + (a - b)) at 1 by ring. apply Rabs_triang. Qed.

(* the fraction leaving x through the first k links *)
Definition outp (src dst : list N) (frac : list R) (x : Z) (k : nat) : R :=
  rs (fun l => if ((sr src l =? x) && negb (dr dst l =? x))%Z then fr frac l else 0) k.

Lemma Z200k : forall k : nat, (Z.of_nat k <= 9801)%Z -> (Z.of_nat (3 * k + 6) <= 200000)%Z.
Proof. intros. lia. Qed.

Section Bound.
Variables (src dst : list N) (frac : list R) (n L : int) (xs xd : array uint) (xf : array float).
Hypothesis HL : Z.of_nat (List.length src) = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.
Let Lr := List.length src.

Lemma fr_in : forall l, (0 <= l < Z.of_nat Lr)%Z -> 0 < fr frac l <= 1.
Proof. intros l Hl. apply (Hf l). unfold Lr in Hl. lia. Qed.

Lemma outp_bound : forall x k, (k <= Lr)%nat -> 0 <= outp src dst frac x k <= INR k.
Proof.
  intros x k Hk. unfold outp. split.
  - apply rs_nonneg. intros l Hl. destruct (_ && _)%Z; [pose proof (fr_in l ltac:(lia)); lra | lra].
  - rewrite <- (Rmult_1_r (INR k)). apply rs_const_le. intros l Hl. destruct (_ && _)%Z; [pose proof (fr_in l ltac:(lia)); lra | lra].
Qed.

Lemma outp_S : forall x k, outp src dst frac x (S k) = outp src dst frac x k +
  (if ((sr src (Z.of_nat k) =? x) && negb (dr dst (Z.of_nat k) =? x))%Z then fr frac (Z.of_nat k) else 0).
Proof. reflexivity. Qed.

Lemma out_spec : let o := loop L (out_step xs xd xf) 0 (PArray.make n 0%float) in
  PArray.length o = n /\ forall x, (0 <= x < to_Z n)%Z -> ap Lr o.[of_Z x] (outp src dst frac x Lr).
Proof.
  intros o. unfold o, Lr. rewrite <- (Nat2Z.id (List.length src)), HL.
  apply (for_inv (fun j o => PArray.length o = n /\ forall x, (0 <= x < to_Z n)%Z ->
     ap (Z.to_nat (to_Z j)) o.[of_Z x] (outp src dst frac x (Z.to_nat (to_Z j))))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia.
  - split; [apply flen_make; lia|]. intros x Hx. rewrite fget_make.
    change (Z.to_nat (to_Z 0)) with 0%nat. apply ap_exact; [exact repr_zero' | unfold outp; simpl; lra].
  - intros j o0 Hj [Lo IH]. change (to_Z 0) with 0%Z in Hj.
    destruct (int_next j ltac:(lia)) as [E1 E2]. rewrite E2.
    set (jz := to_Z j) in *. set (jn := Z.to_nat jz) in *.
    assert (Ejn : Z.of_nat jn = jz) by (unfold jn; lia).
    destruct (Hs jz Hj) as [Es Bs]. destruct (Hd jz Hj) as [Ed Bd]. destruct (Hf jz Hj) as [Hfj Bf].
    unfold jz in Es, Ed, Hfj. rewrite of_to_Z in Es, Ed, Hfj. fold jz in Es, Ed, Hfj.
    assert (Hjb : (Z.of_nat (S jn) <= 9801)%Z) by lia.
    unfold out_step. cbv zeta. destruct (xs.[j] =? xd.[j]) eqn:Esd.
    + apply Uint63.eqb_spec in Esd. rewrite Esd in Es. rewrite Es in Ed.
      split; [exact Lo|]. intros x Hx. rewrite outp_S, Ejn.
      replace (if ((sr src jz =? x) && negb (dr dst jz =? x))%Z then fr frac jz else 0) with 0
        by (destruct (Z.eqb_spec (sr src jz) x), (Z.eqb_spec (dr dst jz) x); simpl; try lia; reflexivity).
      rewrite Rplus_0_r. apply (ap_mono jn); [lia | apply IH, Hx].
    + apply Uint63.eqb_false_spec in Esd.
      assert (Esd' : sr src jz <> dr dst jz) by (intros F; apply Esd, to_Z_inj; lia).
      split; [rewrite flen_set; exact Lo|]. intros x Hx.
      assert (Ix : to_Z (of_Z x) = x) by (apply to_Z_of_Z_n; lia).
      rewrite outp_S, Ejn. rewrite fget_set by lia. rewrite Ix, Es.
      destruct (Z.eqb_spec (sr src jz) x) as [Ex | Ex].
      * rewrite (proj2 (Z.eqb_neq (dr dst jz) x)) by lia. simpl.
        assert (Hos : o0.[xs.[j]] = o0.[of_Z x]) by (rewrite <- (of_to_Z (xs.[j])), Es, Ex; reflexivity).
        rewrite Hos. pose proof (outp_bound x jn ltac:(unfold Lr; lia)) as Bo.
        replace (S jn) with (jn + 0 + 1)%nat by lia.
        apply ap_add; [lia | apply IH, Hx | apply ap_exact; [exact Hfj | lra] |].
        assert (INR jn <= 9801) by (rewrite INR_IZR_INZ; apply IZR_le; lia). lra.
      * simpl. rewrite Rplus_0_r. apply (ap_mono jn); [lia | apply IH, Hx].
Qed.

End Bound.

Lemma eta30 : eta_max <= / 1000000000000000000000000000000.
Proof.
  eapply Rle_trans; [apply eta_tiny|].
  assert (/ 10 ^ 300 <= / 10 ^ 30) by (apply Rinv_le_contravar; [apply pow_lt; lra | apply Rle_pow; [lra | lia]]).
  assert (/ 10 ^ 30 = / 1000000000000000000000000000000) by (simpl; lra). lra.
Qed.

Lemma ap_close : forall k x X, (Z.of_nat k <= 200000)%Z -> ap k x X ->
  fval x <= (1 + / 10000000000) * X + / 10000000000000000000000 /\
  X <= (1 + / 10000000000) * fval x + / 10000000000000000000000.
Proof.
  intros k x X Hk Ha. pose proof (q_small k Hk) as Hq. pose proof (q_ge1 k).
  destruct Ha as (F & H0 & H1 & A1 & A2). apply INR_200k in Hk. pose proof (pos_INR k).
  pose proof eta30. pose proof eta_max_pos.
  assert (0 <= INR k * eta_max <= 200000 * / 1000000000000000000000000000000)
    by (split; [apply Rmult_le_pos; lra | apply Rmult_le_compat; lra]).
  assert (q k * (X + INR k * eta_max) <= (1 + / 10000000000) * (X + INR k * eta_max)) by (apply Rmult_le_compat_r; lra).
  assert (q k * (fval x + INR k * eta_max) <= (1 + / 10000000000) * (fval x + INR k * eta_max)) by (apply Rmult_le_compat_r; lra).
  split; lra.
Qed.

Lemma coef_spec : forall (ou : array float) (x : int) K O, (Z.of_nat K <= 200000)%Z -> ap K ou.[x] O ->
  O <= 1 + / 1000000000 -> exists C, repr (coef ou x) C /\ Rabs (1 - O) <= C <= 5.
Proof.
  intros ou x K O HK Ha HO.
  pose proof (ap_val _ _ _ Ha) as Ro. pose proof (ap_close _ _ _ HK Ha) as [C1 C2].
  destruct Ha as (F & H0 & H1 & _ & _).
  set (fo := fval ou.[x]) in *.
  assert (R1 : repr (1 - ou.[x])%float (rnd (1 - fo))).
  { apply repr_sub; [exact repr_one | exact Ro |]. apply big_no_overflow. apply Rabs_le. lra. }
  pose proof (rnd_err (1 - fo)) as E1.
  set (r1 := rnd (1 - fo)) in *.
  assert (Ab : Rabs (1 - fo) <= 3) by (apply Rabs_le; lra).
  assert (u / 2 * Rabs (1 - fo) <= u / 2 * 3) by (apply Rmult_le_compat_l; [pose proof u_pos; lra | exact Ab]).
  pose proof (repr_abs _ _ R1) as R2.
  pose proof (Rabs_pos r1).
  assert (Hr1 : Rabs r1 <= 4).
  { pose proof (Rabs_tri r1 (1 - fo)). pose proof eta30. rewrite u_val in *. lra. }
  set (z := Rabs r1 + / 1073741824).
  assert (Hz : 0 <= z) by (unfold z; lra).
  assert (R3 : repr (PrimFloat.abs (1 - ou.[x]) + f_s30)%float (rnd z)).
  { apply repr_add; [exact R2 | exact repr_s30 |]. apply big_no_overflow. rewrite Rabs_right by lra. unfold z. lra. }
  exists (rnd z). split; [exact R3|].
  pose proof (rnd_lo z Hz). pose proof (rnd_hi z Hz). pose proof eta30. pose proof eta_max_pos.
  pose proof (Rabs_tri (1 - O) (1 - fo)).
  assert (Rabs (1 - O - (1 - fo)) <= 3 / 10000000000) by (apply Rabs_le; lra).
  pose proof (Rabs_tri (1 - fo) r1). rewrite Rabs_minus_sym in E1.
  unfold z in *. rewrite u_val in *. split; lra.
Qed.

Lemma kx_spec : forall (c : array int) (x : int), (to_Z c.[x] <= 19602)%Z ->
  exists K, repr (kx c x) K /\ (2 * IZR (to_Z c.[x]) + 2) * u <= K <= 1.
Proof.
  intros c x Hc. pose proof (to_Z_bounded c.[x]).
  assert (E : to_Z (c.[x] + c.[x] + 3) = (2 * to_Z c.[x] + 3)%Z) by sia.
  assert (R0 : repr (of_uint63 (c.[x] + c.[x] + 3)) (IZR (2 * to_Z c.[x] + 3))).
  { rewrite <- E. apply repr_of_uint63_exact. rewrite E. lia. }
  set (z := IZR (2 * to_Z c.[x] + 3) * u).
  assert (Hz0 : 0 <= IZR (to_Z c.[x]) <= 19602) by (split; apply IZR_le; lia).
  assert (Ez : z = (2 * IZR (to_Z c.[x]) + 3) * u) by (unfold z; rewrite plus_IZR, mult_IZR; reflexivity).
  assert (Hz : 0 <= z) by (rewrite Ez; pose proof u_pos; nra).
  assert (R : repr (kx c x) (rnd z)).
  { apply repr_mul; [exact R0 | exact repr_fu |]. apply big_no_overflow.
    change (IZR (2 * to_Z c.[x] + 3) * u) with z. rewrite Rabs_right by lra.
    rewrite Ez, u_val. lra. }
  exists (rnd z). split; [exact R|].
  pose proof (rnd_lo z Hz). pose proof (rnd_hi z Hz). pose proof eta30.
  rewrite Ez in *. rewrite u_val in *. split; lra.
Qed.

Lemma fget_set_Z : forall (t : array float) (p : int) x v, (to_Z p < to_Z (PArray.length t))%Z ->
  (0 <= x <= 4194303)%Z -> t.[p <- v].[of_Z x] = if (to_Z p =? x)%Z then v else t.[of_Z x].
Proof. intros t p x v H Hx. rewrite fget_set by exact H. rewrite to_Z_of_Z_n by exact Hx. reflexivity. Qed.

(* what flows into x from the bounds e over the first k links *)
Definition EinX (src dst : list N) (frac : list R) (e : array float) (x : Z) (k : nat) : R :=
  rs (fun l => nsR src dst l * indR x (dr dst l) * (fr frac l * fv e (sr src l))) k.

(* the sizes of the transfers touching x over the first k links *)
Definition MacX (src dst : list N) (frac : list R) (v : array float) (x : Z) (k : nat) : R :=
  rs (fun l => tauR src dst l x * Rabs (Af src frac v l)) k.

Lemma nsR_range : forall src dst l, 0 <= nsR src dst l <= 1.
Proof. intros. unfold nsR. destruct (_ =? _)%Z; lra. Qed.

Lemma indR_le1' : forall a b, 0 <= indR a b <= 1.
Proof. intros. unfold indR. destruct (_ =? _)%Z; lra. Qed.

Section Elink.
Variables (src dst : list N) (frac : list R) (n L : int) (xs xd : array uint) (xf : array float).
Hypothesis HL : Z.of_nat (List.length src) = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.
Variables (v e : array float).
Hypothesis Hokv : okv v (to_Z n).
Hypothesis Hvb : forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i) <= 1000000.
Hypothesis Hoke : okv e (to_Z n).
Hypothesis Heb : forall i, (0 <= i < to_Z n)%Z -> 0 <= fv e i <= 1.
Let Lr := List.length src.

Lemma Ein_bound : forall x k, (k <= Lr)%nat -> 0 <= EinX src dst frac e x k <= INR k.
Proof.
  intros x k Hk. unfold EinX.
  assert (B : forall l, (0 <= l < Z.of_nat k)%Z ->
     0 <= nsR src dst l * indR x (dr dst l) * (fr frac l * fv e (sr src l)) <= 1).
  { intros l Hl. assert (Hl' : (0 <= l < to_Z L)%Z) by (unfold Lr in Hk; lia).
    pose proof (Hf l Hl') as [_ F]. pose proof (Heb (sr src l) (proj2 (Hs l Hl'))).
    pose proof (nsR_range src dst l). pose proof (indR_le1' x (dr dst l)).
    assert (0 <= fr frac l * fv e (sr src l) <= 1) by (split; nra).
    split; [apply Rmult_le_pos; [apply Rmult_le_pos|]; lra|].
    assert (nsR src dst l * indR x (dr dst l) <= 1) by nra. nra. }
  split; [apply rs_nonneg; intros; apply B; lia|].
  rewrite <- (Rmult_1_r (INR k)). apply rs_const_le. intros; apply B; lia.
Qed.

Lemma Af_le : forall l, (0 <= l < to_Z L)%Z -> Rabs (Af src frac v l) <= 2000001.
Proof.
  intros l Hl. destruct (Hs l Hl) as [_ Bs]. destruct (Hf l Hl) as [_ Bf].
  apply (Af_bound src frac v l (Hvb _ Bs)). lra.
Qed.

Lemma Mac_bound : forall x k, (k <= Lr)%nat -> 0 <= MacX src dst frac v x k <= INR k * 4000002.
Proof.
  intros x k Hk. unfold MacX.
  assert (B : forall l, (0 <= l < Z.of_nat k)%Z -> 0 <= tauR src dst l x * Rabs (Af src frac v l) <= 4000002).
  { intros l Hl. pose proof (Af_le l ltac:(unfold Lr in Hk; lia)). pose proof (tauR_range src dst 0%uint63 0%uint63 l x).
    pose proof (Rabs_pos (Af src frac v l)). split; nra. }
  split; [apply rs_nonneg; intros; apply B; lia|]. apply rs_const_le. intros; apply B; lia.
Qed.

Lemma elink_spec : let st := loop L (elink xs xd xf v e) 0 (PArray.make n 0%float, PArray.make n 0%float) in
  PArray.length (fst st) = n /\ PArray.length (snd st) = n /\
  forall x, (0 <= x < to_Z n)%Z ->
    ap (2 * Lr) (fst st).[of_Z x] (EinX src dst frac e x Lr) /\ ap Lr (snd st).[of_Z x] (MacX src dst frac v x Lr).
Proof.
  intros st. unfold st, Lr. rewrite <- (Nat2Z.id (List.length src)), HL.
  apply (for_inv (fun j st => PArray.length (fst st) = n /\ PArray.length (snd st) = n /\
     forall x, (0 <= x < to_Z n)%Z ->
       ap (2 * Z.to_nat (to_Z j)) (fst st).[of_Z x] (EinX src dst frac e x (Z.to_nat (to_Z j))) /\
       ap (Z.to_nat (to_Z j)) (snd st).[of_Z x] (MacX src dst frac v x (Z.to_nat (to_Z j))))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded L). lia.
  - simpl fst; simpl snd. split; [apply flen_make; lia|]. split; [apply flen_make; lia|].
    intros x Hx. rewrite !fget_make. change (Z.to_nat (to_Z 0)) with 0%nat.
    split; apply ap_exact; try exact repr_zero'; unfold EinX, MacX; simpl; lra.
  - intros j [ein mac] Hj (Le & Lm & IH). simpl fst in *; simpl snd in *. change (to_Z 0) with 0%Z in Hj.
    destruct (int_next j ltac:(lia)) as [E1 E2]. rewrite E2.
    set (jz := to_Z j) in *. set (jn := Z.to_nat jz) in *.
    assert (Ejn : Z.of_nat jn = jz) by (unfold jn; lia).
    assert (Hjl : (S jn <= Lr)%nat) by (unfold jn, Lr; lia).
    assert (Hjb : (Z.of_nat (S jn) <= 9801)%Z) by lia.
    destruct (Hs jz Hj) as [Es Bs]. destruct (Hd jz Hj) as [Ed Bd]. destruct (Hf jz Hj) as [Hfj Bf].
    unfold jz in Es, Ed, Hfj. rewrite of_to_Z in Es, Ed, Hfj. fold jz in Es, Ed, Hfj.
    assert (EE : forall x, EinX src dst frac e x (S jn) = EinX src dst frac e x jn +
        nsR src dst jz * indR x (dr dst jz) * (fr frac jz * fv e (sr src jz)))
      by (intros; unfold EinX; rewrite rs_S, Ejn; reflexivity).
    assert (EM : forall x, MacX src dst frac v x (S jn) = MacX src dst frac v x jn +
        tauR src dst jz x * Rabs (Af src frac v jz))
      by (intros; unfold MacX; rewrite rs_S, Ejn; reflexivity).
    assert (INR jn <= 9801) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
    unfold elink. cbv zeta. destruct (xs.[j] =? xd.[j]) eqn:Esd.
    + apply Uint63.eqb_spec in Esd. rewrite Esd in Es. rewrite Es in Ed.
      assert (N0 : nsR src dst jz = 0) by (unfold nsR; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
      assert (T0 : forall x, tauR src dst jz x = 0)
        by (intros; unfold tauR, tauZ; rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity).
      split; [exact Le|]. split; [exact Lm|]. intros x Hx. rewrite EE, EM, N0, T0.
      rewrite !Rmult_0_l, !Rplus_0_r. destruct (IH x Hx) as [I1 I2].
      split; [apply (ap_mono (2 * jn)); [lia | exact I1] | apply (ap_mono jn); [lia | exact I2]].
    + apply Uint63.eqb_false_spec in Esd.
      assert (Esd' : sr src jz <> dr dst jz) by (intros F; apply Esd, to_Z_inj; lia).
      cbn [fst snd].
      set (s := xs.[j]) in *. set (d := xd.[j]) in *.
      set (s' := sr src jz) in *. set (d' := dr dst jz) in *.
      assert (N1 : nsR src dst jz = 1) by (unfold nsR; fold s' d'; rewrite (proj2 (Z.eqb_neq _ _) Esd'); reflexivity).
      assert (Tx : forall x, tauR src dst jz x = indR x s' + indR x d')
        by (intros; rewrite tauR_eq, N1; fold s' d'; ring).
      assert (Hvs : repr v.[s] (fv v s')) by (rewrite <- (of_to_Z s), Es; apply (okv_repr v (to_Z n)); [exact Hokv | lia]).
      assert (Hes : repr e.[s] (fv e s')) by (rewrite <- (of_to_Z s), Es; apply (okv_repr e (to_Z n)); [exact Hoke | lia]).
      set (A := Af src frac v jz).
      assert (Ha : repr (PrimFloat.abs (xf.[j] * v.[s])) (Rabs A)).
      { apply repr_abs. unfold A, Af. fold s'. apply repr_mul; [exact Hfj | exact Hvs |].
        apply big_no_overflow. pose proof (Af_bound src frac v jz (Hvb s' ltac:(lia)) ltac:(lra)) as [H1 _]. fold s' in H1. lra. }
      pose proof (Af_le jz Hj) as HA. fold A in HA. pose proof (Rabs_pos A).
      pose proof (Heb s' ltac:(lia)) as Hes'.
      assert (Hp : ap 1 (xf.[j] * e.[s])%float (fr frac jz * fv e s'))
        by (apply ap_mul0; [exact Hfj | exact Hes | lra | lra | nra]).
      assert (Hp1 : fr frac jz * fv e s' <= 1) by nra.
      split; [rewrite flen_set; exact Le|]. split; [rewrite !flen_set; exact Lm|].
      intros x Hx. rewrite EE, EM, N1, Tx. destruct (IH x Hx) as [I1 I2].
      pose proof (Ein_bound x jn ltac:(lia)). pose proof (Mac_bound x jn ltac:(lia)).
      split.
      * rewrite fget_set_Z by (rewrite ?Le; lia). rewrite Ed.
        destruct (Z.eqb_spec d' x) as [<- | Ex].
        -- rewrite indR_eq. replace ein.[d] with ein.[of_Z d'] by (rewrite <- Ed, of_to_Z; reflexivity).
           replace (2 * S jn)%nat with (2 * jn + 1 + 1)%nat by lia.
           replace (EinX src dst frac e d' jn + 1 * 1 * (fr frac jz * fv e s'))
             with (EinX src dst frac e d' jn + fr frac jz * fv e s') by ring.
           apply ap_add; [lia | exact I1 | exact Hp | lra].
        -- rewrite indR_neq by lia. rewrite Rmult_0_r, Rmult_0_l, Rplus_0_r.
           apply (ap_mono (2 * jn)); [lia | exact I1].
      * rewrite fget_set_Z by (rewrite ?flen_set, ?Lm; lia). rewrite Es.
        destruct (Z.eqb_spec s' x) as [<- | Ex1].
        -- rewrite fget_set by (rewrite Lm; lia). rewrite Ed, Es, (proj2 (Z.eqb_neq d' s')) by lia.
           rewrite indR_eq, (indR_neq s' d') by lia. fold A. replace mac.[s] with mac.[of_Z s'] by (rewrite <- Es, of_to_Z; reflexivity).
           replace (S jn) with (jn + 0 + 1)%nat by lia.
           replace (MacX src dst frac v s' jn + (1 + 0) * Rabs A) with (MacX src dst frac v s' jn + Rabs A) by ring.
           apply ap_add; [lia | exact I2 | apply ap_exact; [exact Ha | lra] | lra].
        -- rewrite fget_set_Z by (rewrite ?Lm; lia). rewrite Ed.
           destruct (Z.eqb_spec d' x) as [<- | Ex2].
           ++ rewrite indR_eq, (indR_neq d' s') by lia. fold A. replace mac.[d] with mac.[of_Z d'] by (rewrite <- Ed, of_to_Z; reflexivity).
              replace (S jn) with (jn + 0 + 1)%nat by lia.
              replace (MacX src dst frac v d' jn + (0 + 1) * Rabs A) with (MacX src dst frac v d' jn + Rabs A) by ring.
              apply ap_add; [lia | exact I2 | apply ap_exact; [exact Ha | lra] | lra].
           ++ rewrite !indR_neq by lia. rewrite Rplus_0_r, Rmult_0_l, Rplus_0_r.
              apply (ap_mono jn); [lia | exact I2].
Qed.

End Elink.

Definition Sx (src dst : list N) (frac : list R) (ou : array float) (c : array int) (v e : array float) (x : Z) : R :=
  fval (coef ou (of_Z x)) * fv e x + EinX src dst frac e x (List.length src) +
  fval (kx c (of_Z x)) * (Rabs (fv v x) + MacX src dst frac v x (List.length src) + 1).

Section Efort.
Variables (src dst : list N) (frac : list R) (n L : int) (xs xd : array uint) (xf : array float).
Hypothesis HL : Z.of_nat (List.length src) = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.
Variables (v e : array float) (ou : array float) (c : array int).
Hypothesis Hokv : okv v (to_Z n).
Hypothesis Hvb : forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i) <= 1000000.
Hypothesis Hoke : okv e (to_Z n).
Hypothesis Heb : forall i, (0 <= i < to_Z n)%Z -> 0 <= fv e i <= 1.
Hypothesis Hco : forall x, (0 <= x < to_Z n)%Z ->
  repr (coef ou (of_Z x)) (fval (coef ou (of_Z x))) /\ 0 <= fval (coef ou (of_Z x)) <= 5.
Hypothesis Hkx : forall x, (0 <= x < to_Z n)%Z ->
  repr (kx c (of_Z x)) (fval (kx c (of_Z x))) /\ 0 <= fval (kx c (of_Z x)) <= 1.
Let Lr := List.length src.

Lemma ebound_spec : let r := ebound n L xs xd xf ou c v e in
  PArray.length (fst r) = n /\
  (snd r = true -> forall x, (0 <= x < to_Z n)%Z ->
     repr (fst r).[of_Z x] (fv (fst r) x) /\ Sx src dst frac ou c v e x <= fv (fst r) x <= 1).
Proof.
  intros r. unfold r, ebound.
  destruct (elink_spec src dst frac n L xs xd xf HL HLb Hn Hs Hd Hf v e Hokv Hvb Hoke Heb) as (Le & Lm & Hem).
  set (st := loop L (elink xs xd xf v e) 0 (PArray.make n 0%float, PArray.make n 0%float)) in *.
  set (ein := fst st) in *. set (mac := snd st) in *. fold Lr in Hem.
  assert (HLr : (Z.of_nat Lr <= 9801)%Z) by (unfold Lr; lia).
  assert (HLr' : INR Lr <= 9801) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
  apply (for_inv (fun j st => PArray.length (fst st) = n /\
     (snd st = true -> forall x, (0 <= x < to_Z j)%Z ->
        repr (fst st).[of_Z x] (fv (fst st) x) /\ Sx src dst frac ou c v e x <= fv (fst st) x <= 1))).
  - change (to_Z 0) with 0%Z. lia.
  - simpl fst. split; [apply flen_make; lia|]. intros _ x Hx. change (to_Z 0) with 0%Z in Hx. lia.
  - intros j [e' ok] Hj [Le' IH]. simpl fst in *; simpl snd in *. change (to_Z 0) with 0%Z in Hj.
    destruct (int_next j ltac:(lia)) as [E1 _].
    set (x0 := to_Z j) in *.
    assert (Ej : j = of_Z x0) by (unfold x0; rewrite of_to_Z; reflexivity).
    unfold efort. cbn [fst snd].
    destruct (Hem x0 Hj) as [Ae Am]. destruct (Hco x0 Hj) as [Rc Bc]. destruct (Hkx x0 Hj) as [Rk Bk].
    rewrite <- Ej in Ae, Am, Rc, Bc, Rk, Bk.
    pose proof (Heb x0 Hj) as Be. pose proof (Hvb x0 Hj) as Bv.
    assert (Rv : repr v.[j] (fv v x0)) by (rewrite Ej; apply (okv_repr v (to_Z n)); [exact Hokv | lia]).
    assert (Re : repr e.[j] (fv e x0)) by (rewrite Ej; apply (okv_repr e (to_Z n)); [exact Hoke | lia]).
    pose proof (Ein_bound src dst frac n L xs xf HL Hs Hf e Heb x0 Lr (le_n _)) as BE.
    pose proof (Mac_bound src dst frac n L xs xf HL Hs Hf v Hvb x0 Lr (le_n _)) as BM.
    fold Lr in BE, BM.
    set (C := fval (coef ou j)) in *. set (K := fval (kx c j)) in *.
    assert (h1 : ap 1 (coef ou j * e.[j])%float (C * fv e x0)) by (apply ap_mul0; [exact Rc | exact Re | lra | lra | nra]).
    assert (h2 : ap (1 + 2 * Lr + 1) (coef ou j * e.[j] + ein.[j])%float (C * fv e x0 + EinX src dst frac e x0 Lr))
      by (apply ap_add; [lia | exact h1 | exact Ae | nra]).
    assert (h3 : ap (0 + Lr + 1) (PrimFloat.abs v.[j] + mac.[j])%float (Rabs (fv v x0) + MacX src dst frac v x0 Lr))
      by (apply ap_add; [lia | apply ap_exact; [apply repr_abs, Rv | apply Rabs_pos] | exact Am | lra]).
    assert (h4 : ap (0 + Lr + 1 + 0 + 1) (PrimFloat.abs v.[j] + mac.[j] + 1)%float (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1))
      by (apply ap_add; [lia | exact h3 | apply ap_exact; [exact repr_one | lra] | lra]).
    assert (h5 : ap (0 + Lr + 1 + 0 + 1 + 1) (kx c j * (PrimFloat.abs v.[j] + mac.[j] + 1))%float
                    (K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1)))
      by (apply ap_mulc; [lia | exact Rk | exact Bk | exact h4 | lra]).
    assert (h6 : ap ((1 + 2 * Lr + 1) + (0 + Lr + 1 + 0 + 1 + 1) + 1)
                    ((coef ou j * e.[j] + ein.[j]) + kx c j * (PrimFloat.abs v.[j] + mac.[j] + 1))%float
                    (C * fv e x0 + EinX src dst frac e x0 Lr + K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1))).
    { apply ap_add; [lia | exact h2 | exact h5 |].
      assert (K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1) <= 1 * 50000000000)
        by (apply Rmult_le_compat; try lra; pose proof (Rabs_pos (fv v x0)); lra).
      nra. }
    assert (HS : C * fv e x0 + EinX src dst frac e x0 Lr + K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1) <= 100000000000).
    { assert (K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1) <= 1 * 50000000000)
        by (apply Rmult_le_compat; try lra; pose proof (Rabs_pos (fv v x0)); lra).
      nra. }
    assert (HS2 : C * fv e x0 + EinX src dst frac e x0 Lr +
        K * (Rabs (fv v x0) + MacX src dst frac v x0 Lr + 1) <= 100000000000000) by lra.
    assert (Hk6 : (Z.of_nat (1 + 2 * Lr + 1 + (0 + Lr + 1 + 0 + 1 + 1) + 1) <= 200000)%Z) by lia.
    destruct (ap_up _ _ _ Hk6 h6 HS2) as (Y & RY & Y1 & Y2).
    set (y := up ((coef ou j * e.[j] + ein.[j]) + kx c j * ((PrimFloat.abs v.[j] + mac.[j]) + 1))%float) in *.
    split; [rewrite flen_set; exact Le'|].
    intros Hok x Hx. rewrite E1 in Hx. apply andb_prop in Hok as [Hok Hy].
    assert (Iy : fv (e'.[j <- y]) x0 = Y /\ repr (e'.[j <- y]).[of_Z x0] Y).
    { unfold fv. rewrite <- Ej. rewrite fget_set by lia. rewrite Z.eqb_refl.
      split; [apply repr_fval, RY | exact RY]. }
    destruct (Z.eq_dec x x0) as [-> | Ex].
    + destruct Iy as [Iy1 Iy2]. rewrite Iy1. split; [exact Iy2|].
      pose proof (proj1 (repr_leb_iff y 1%float Y 1 RY repr_one) Hy).
      unfold Sx. fold Lr. rewrite <- Ej. fold C K. lra.
    + assert (Gx : (e'.[j <- y]).[of_Z x] = e'.[of_Z x]).
      { rewrite fget_set by lia. rewrite to_Z_of_Z_n by lia. fold x0. rewrite (proj2 (Z.eqb_neq x0 x)) by lia. reflexivity. }
      unfold fv. rewrite Gx. apply IH; [exact Hok | lia].
Qed.

End Efort.

Lemma af_err : forall z, Rabs (rnd z - z) <= u * Rabs (rnd z) + 2 * eta_max.
Proof.
  intros z. pose proof (rnd_err z). pose proof (Rabs_tri z (rnd z)). pose proof u_pos. pose proof eta_max_pos.
  rewrite (Rabs_minus_sym z (rnd z)) in H0.
  assert (u / 2 * Rabs z <= u / 2 * (Rabs (rnd z) + Rabs (rnd z - z))) by (apply Rmult_le_compat_l; lra).
  assert (u / 2 * Rabs (rnd z - z) <= 1 / 2 * Rabs (rnd z - z))
    by (apply Rmult_le_compat_r; [apply Rabs_pos | rewrite u_val; lra]).
  assert (0 <= u * Rabs (rnd z)) by (apply Rmult_le_pos; [lra | apply Rabs_pos]).
  lra.
Qed.

Section UErr.
Variables (t0 : N) (us : list R) (src dst : list N) (frac : list R).
Variables (n L : int) (xs xd : array uint) (xf : array float).
Hypothesis Hv : valid_input t0 us src dst frac.
Let nn := List.length us.
Let Lr := List.length src.
Hypothesis Hnn : to_Z n = Z.of_nat nn.
Hypothesis HL : Z.of_nat Lr = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.
Variables (v e : array float) (X : Z -> R) (ou : array float) (c : array int).
Hypothesis Hokv : okv v (to_Z n).
Hypothesis Hvb : forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i) <= 1000000.
Hypothesis Herr : forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i - X i) <= fv e i.
Hypothesis Hco : forall x, (0 <= x < to_Z n)%Z -> Rabs (1 - outj src dst frac x) <= fval (coef ou (of_Z x)).
Hypothesis Hkx : forall x, (0 <= x < to_Z n)%Z ->
  (2 * IZR (zs (fun l => tauZ src dst l x) Lr) + 2) * u <= fval (kx c (of_Z x)).

Lemma unit_err : forall x, (0 <= x < to_Z n)%Z ->
  Rabs (fv (unit_f L xs xd xf v) x - rs (fun j => Am src dst frac x j * X j) nn) <= Sx src dst frac ou c v e x.
Proof.
  intros x Hx.
  destruct (unit_spec src dst frac n L xs xd xf HL HLb Hn Hs Hd Hf v Hokv Hvb) as [_ Hw].
  specialize (Hw x Hx). fold Lr in Hw.
  unfold nn. rewrite (Am_apply t0 us src dst frac Hv X x) by (fold nn; lia). fold Lr.
  set (D := fun i => fv v i - X i).
  set (w := unit_f L xs xd xf v) in *.
  set (G := rs (fun l => gR src dst frac v l x) Lr) in *.
  set (P := rs (fun l => fr frac l * (indR x (dr dst l) * X (sr src l) - indR x (sr src l) * X (sr src l))) Lr).
  set (Pv := rs (fun l => fr frac l * (indR x (dr dst l) * fv v (sr src l) - indR x (sr src l) * fv v (sr src l))) Lr).
  assert (Hsr : forall l, (0 <= l < Z.of_nat Lr)%Z -> (0 <= sr src l < to_Z n)%Z) by (intros l Hl; apply (Hs l); lia).
  assert (Hfr : forall l, (0 <= l < Z.of_nat Lr)%Z -> 0 < fr frac l <= 1) by (intros l Hl; apply (Hf l); lia).
  (* the third part: the propagated error *)
  assert (E3 : Pv - P = rs (fun l => nsR src dst l * indR x (dr dst l) * (fr frac l * D (sr src l))) Lr - D x * outj src dst frac x).
  { unfold Pv, P, outj. rewrite <- rs_sub, <- rs_scal, <- rs_sub. fold Lr. apply rs_ext. intros l _.
    unfold D, nsR, indR.
    destruct (Z.eqb_spec (sr src l) (dr dst l)) as [E|E], (Z.eqb_spec x (dr dst l)), (Z.eqb_spec x (sr src l)),
      (Z.eqb_spec (sr src l) x), (Z.eqb_spec (dr dst l) x); simpl; subst; try lia; try ring. }
  assert (B3 : Rabs (D x + (Pv - P)) <= fval (coef ou (of_Z x)) * fv e x + EinX src dst frac e x Lr).
  { rewrite E3. replace (D x + (rs (fun l => nsR src dst l * indR x (dr dst l) * (fr frac l * D (sr src l))) Lr - D x * outj src dst frac x))
      with ((1 - outj src dst frac x) * D x + rs (fun l => nsR src dst l * indR x (dr dst l) * (fr frac l * D (sr src l))) Lr) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat.
    - rewrite Rabs_mult. apply Rmult_le_compat; try apply Rabs_pos; [apply Hco, Hx | apply Herr, Hx].
    - eapply Rle_trans; [apply rs_abs|]. unfold EinX. apply rs_le. intros l Hl.
      pose proof (Hfr l Hl). pose proof (Herr (sr src l) (Hsr l Hl)). pose proof (nsR_range src dst l).
      pose proof (indR_le1' x (dr dst l)). fold D in H0.
      rewrite !Rabs_mult, (Rabs_right (nsR src dst l)), (Rabs_right (indR x (dr dst l))), (Rabs_right (fr frac l)) by lra.
      apply Rmult_le_compat_l; [apply Rmult_le_pos; lra|]. apply Rmult_le_compat_l; [lra | exact H0]. }
  (* the second part: the rounded products *)
  assert (E2 : G - Pv = rs (fun l => nsR src dst l * (indR x (dr dst l) - indR x (sr src l)) *
                                      (Af src frac v l - fr frac l * fv v (sr src l))) Lr).
  { unfold G, Pv. rewrite <- rs_sub. apply rs_ext. intros l _. unfold gR, nsR, indR.
    destruct (Z.eqb_spec (sr src l) (dr dst l)) as [E|E]; [rewrite E; destruct (x =? dr dst l)%Z; ring | ring]. }
  set (cnt := IZR (zs (fun l => tauZ src dst l x) Lr)).
  assert (B2 : Rabs (G - Pv) <= u * MacX src dst frac v x Lr + 2 * eta_max * cnt).
  { rewrite E2. eapply Rle_trans; [apply rs_abs|].
    unfold cnt. rewrite rs_IZR. unfold MacX. rewrite <- !rs_scal, <- rs_add. apply rs_le. intros l _.
    rewrite Rabs_mult. pose proof (af_err (fr frac l * fv v (sr src l))) as Ha. fold (Af src frac v l) in Ha.
    change (IZR (tauZ src dst l x)) with (tauR src dst l x).
    assert (Hta : Rabs (nsR src dst l * (indR x (dr dst l) - indR x (sr src l))) <= tauR src dst l x).
    { rewrite tauR_eq. unfold nsR, indR.
      destruct (sr src l =? dr dst l)%Z, (x =? dr dst l)%Z, (x =? sr src l)%Z; apply Rabs_le; lra. }
    pose proof (tauR_range src dst 0%uint63 0%uint63 l x).
    eapply Rle_trans; [apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | exact Hta | exact Ha]|].
    right. ring. }
  (* the first part *)
  assert (Hcnt : 0 <= cnt <= 19602).
  { unfold cnt. pose proof (zs_bound (fun l => tauZ src dst l x) Lr (fun k => tauZ_range src dst 0%uint63 0%uint63 k x)) as [H1 H2].
    split; apply IZR_le; lia. }
  assert (BM : 0 <= MacX src dst frac v x Lr).
  { unfold MacX. apply rs_nonneg. intros l _. pose proof (tauR_range src dst 0%uint63 0%uint63 l x).
    pose proof (Rabs_pos (Af src frac v l)). nra. }
  assert (EM : Mx src dst frac v x = Rabs (fv v x) + MacX src dst frac v x Lr) by reflexivity.
  rewrite EM in Hw. fold cnt in Hw.
  replace (fv w x - (X x + P)) with ((fv w x - fv v x - G) + (G - Pv) + (D x + (Pv - P))) by (unfold D; ring).
  eapply Rle_trans; [apply Rabs_triang|]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
  unfold Sx. fold Lr.
  pose proof (Hkx x Hx) as HK. fold cnt in HK. set (K := fval (kx c (of_Z x))) in *.
  set (M := Rabs (fv v x) + MacX src dst frac v x Lr) in *.
  assert (HM : 0 <= M) by (unfold M; pose proof (Rabs_pos (fv v x)); lra).
  assert (K * (M + 1) >= (2 * cnt + 2) * u * (M + 1)) by (apply Rle_ge, Rmult_le_compat_r; lra).
  pose proof u_pos. pose proof eta_max_le_u. pose proof eta_max_pos.
  assert (2 * eta_max * cnt <= u * cnt) by (apply Rmult_le_compat_r; lra).
  assert (u * MacX src dst frac v x Lr <= u * M) by (apply Rmult_le_compat_l; [lra | unfold M; pose proof (Rabs_pos (fv v x)); lra]).
  assert (cnt * u * (M + 1) + u * M + u * cnt <= (2 * cnt + 2) * u * (M + 1)).
  { assert (0 <= cnt * u * M) by (apply Rmult_le_pos; [nra | lra]). nra. }
  replace (Rabs (fv v x) + MacX src dst frac v x Lr + 1) with (M + 1) by (unfold M; ring).
  lra.
Qed.

End UErr.

(* ------------------------------------------------------------------ *)
(* The t time units with their bounds                                  *)
(* ------------------------------------------------------------------ *)

Definition exs (us : list R) (src dst : list N) (frac : list R) (k : nat) (i : Z) : R :=
  strength us src dst frac k (Z.to_N i).

Lemma ex_bound : forall t0 us src dst frac k i, valid_input t0 us src dst frac ->
  (Z.of_nat k <= 10000)%Z -> (0 <= i < Z.of_nat (List.length us))%Z ->
  Rabs (exs us src dst frac k i) <= 150000.
Proof.
  intros t0 us src dst frac k i Hv Hk Hi. set (nn := List.length us) in *.
  assert (E : rs (fun i => Rabs (exs us src dst frac k i)) nn <= 3 / 2 * rs (fun j => Rabs (get_R us (Z.to_N j))) nn).
  { rewrite (rs_ext _ (fun i => Rabs (rs (fun j => mpow src dst frac nn k i j * get_R us (Z.to_N j)) nn)))
      by (intros i' Hi'; unfold exs; rewrite (strength_mat t0 us src dst frac nn Hv (le_n _)) by exact Hi'; reflexivity).
    eapply Rle_trans; [apply (colb_vec nn _ (gam ^ k)); [apply pow_le; unfold gam; lra | apply (colb_mpow t0 us src dst frac nn Hv (le_n _))]|].
    pose proof (gam_pow k Hk).
    assert (0 <= rs (fun j => Rabs (get_R us (Z.to_N j))) nn) by (apply rs_nonneg; intros; apply Rabs_pos).
    apply Rmult_le_compat_r; lra. }
  assert (U : rs (fun j => Rabs (get_R us (Z.to_N j))) nn <= INR nn * 1000).
  { apply rs_const_le. intros j Hj. destruct Hv as [_ _ _ _ _ Hu0 _ _ _ _].
    unfold get_R. rewrite Z_N_nat. pose proof (nth_Forall _ us (Z.to_nat j) 0 Hu0 ltac:(unfold nn in Hj; lia)) as H.
    cbv beta in H. rewrite Rabs_right by lra. lra. }
  assert (HN : INR nn <= 100).
  { destruct Hv as [HN _ _ _ _ _ _ _ _ _]. unfold len in HN. fold nn in HN. rewrite INR_IZR_INZ. apply IZR_le. lia. }
  pose proof (rs_single (fun i => Rabs (exs us src dst frac k i)) nn i ltac:(intros; apply Rabs_pos) Hi).
  cbv beta in H. lra.
Qed.

Definition INV (us : list R) (src dst : list N) (frac : list R) (n : int) (k : nat) (v e : array float) : Prop :=
  okv v (to_Z n) /\ okv e (to_Z n) /\
  forall i, (0 <= i < to_Z n)%Z -> 0 <= fv e i <= 1 /\ Rabs (fv v i - exs us src dst frac k i) <= fv e i.

Section Sim3.
Variables (t0 : N) (us : list R) (src dst : list N) (frac : list R).
Variables (n L xt : int) (xs xd : array uint) (xf xu : array float) (ou : array float) (c : array int).
Hypothesis Hv : valid_input t0 us src dst frac.
Let nn := List.length us.
Let Lr := List.length src.
Hypothesis Hnn : to_Z n = Z.of_nat nn.
Hypothesis HL : Z.of_nat Lr = to_Z L.
Hypothesis HLb : (to_Z L <= 9801)%Z.
Hypothesis Hn : (1 <= to_Z n <= 100)%Z.
Hypothesis Hs : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z.
Hypothesis Hd : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z.
Hypothesis Hf : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1.
Hypothesis Hu : forall i, (0 <= i < to_Z n)%Z -> repr xu.[of_Z i] (get_R us (Z.to_N i)).
Hypothesis Hlu : to_Z (PArray.length xu) = to_Z n.
Hypothesis HT : (to_Z xt <= 5000)%Z.
Hypothesis Hco : forall x, (0 <= x < to_Z n)%Z -> repr (coef ou (of_Z x)) (fval (coef ou (of_Z x))) /\
  Rabs (1 - outj src dst frac x) <= fval (coef ou (of_Z x)) <= 5.
Hypothesis Hkx : forall x, (0 <= x < to_Z n)%Z -> repr (kx c (of_Z x)) (fval (kx c (of_Z x))) /\
  (2 * IZR (zs (fun l => tauZ src dst l x) Lr) + 2) * u <= fval (kx c (of_Z x)) <= 1.

Lemma sim_inv : let st := loop xt (tstep n L xs xd xf ou c) 0 (xu, PArray.make n 0%float, true) in
  snd st = true -> INV us src dst frac n (Z.to_nat (to_Z xt)) (fst (fst st)) (snd (fst st)).
Proof.
  intros st. unfold st.
  apply (for_inv (fun j st => snd st = true -> INV us src dst frac n (Z.to_nat (to_Z j)) (fst (fst st)) (snd (fst st)))).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded xt). lia.
  - intros _. simpl fst; simpl snd. change (Z.to_nat (to_Z 0)) with 0%nat. split; [|split].
    + split; [exact Hlu | intros i Hi; exact (proj1 (Hu i Hi))].
    + split; [rewrite flen_make; lia | intros i Hi; rewrite fget_make; reflexivity].
    + intros i Hi. unfold fv. rewrite fget_make. unfold exs. simpl.
      rewrite (repr_fval _ _ (Hu i Hi)). replace (fval 0%float) with 0 by reflexivity.
      unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. lra.
  - intros j [[v e] ok] Hj IH Hok. simpl fst in *; simpl snd in *. change (to_Z 0) with 0%Z in Hj.
    destruct (int_next j ltac:(lia)) as [_ E2]. rewrite E2.
    unfold tstep in *. destruct ok; [| discriminate].
    destruct (IH eq_refl) as (Okv & Oke & Hve).
    set (k := Z.to_nat (to_Z j)) in *.
    assert (Hvb : forall i, (0 <= i < to_Z n)%Z -> Rabs (fv v i) <= 1000000).
    { intros i Hi. destruct (Hve i Hi) as [B1 B2].
      pose proof (ex_bound t0 us src dst frac k i Hv ltac:(unfold k; lia) ltac:(fold nn; lia)).
      pose proof (Rabs_tri (fv v i) (exs us src dst frac k i)). lra. }
    assert (Heb : forall i, (0 <= i < to_Z n)%Z -> 0 <= fv e i <= 1) by (intros i Hi; apply (Hve i Hi)).
    destruct (ebound_spec src dst frac n L xs xd xf ltac:(fold Lr; lia) HLb Hn Hs Hd Hf v e ou c Okv Hvb Oke Heb
                ltac:(intros x Hx; destruct (Hco x Hx) as (H1 & H2 & H3); split; [exact H1 | pose proof (Rabs_pos (1 - outj src dst frac x)); lra])
                ltac:(intros x Hx; destruct (Hkx x Hx) as (H1 & H2 & H3); split; [exact H1 | split; [| exact H3]];
                      pose proof u_pos; pose proof (zs_bound (fun l => tauZ src dst l x) Lr (fun k => tauZ_range src dst 0%uint63 0%uint63 k x)) as [Z1 _];
                      apply IZR_le in Z1; nra))
      as [Le' He'].
    set (r := ebound n L xs xd xf ou c v e) in *. destruct r as [e' ok'] eqn:Er. simpl fst in *; simpl snd in *.
    simpl in Hok. specialize (He' Hok).
    destruct (unit_spec src dst frac n L xs xd xf ltac:(fold Lr; lia) HLb Hn Hs Hd Hf v Okv Hvb) as [Okw _].
    split; [exact Okw|]. split.
    + split; [rewrite Le'; reflexivity | intros i Hi; exact (proj1 (proj1 (He' i Hi)))].
    + intros x Hx. destruct (He' x Hx) as [_ [S1 S2]].
      assert (Hs0 : 0 <= Sx src dst frac ou c v e x).
      { pose proof (unit_err t0 us src dst frac n L xs xd xf Hv Hnn HL HLb Hn Hs Hd Hf v e (exs us src dst frac k) ou c
                      Okv Hvb (fun i Hi => proj2 (Hve i Hi)) (fun x Hx => proj1 (proj2 (Hco x Hx))) (fun x Hx => proj1 (proj2 (Hkx x Hx))) x Hx).
        pose proof (Rabs_pos (fv (unit_f L xs xd xf v) x - rs (fun j => Am src dst frac x j * exs us src dst frac k j) nn)).
        fold nn in H. lra. }
      split; [lra|].
      pose proof (unit_err t0 us src dst frac n L xs xd xf Hv Hnn HL HLb Hn Hs Hd Hf v e (exs us src dst frac k) ou c
                    Okv Hvb (fun i Hi => proj2 (Hve i Hi)) (fun x Hx => proj1 (proj2 (Hco x Hx))) (fun x Hx => proj1 (proj2 (Hkx x Hx))) x Hx) as UE.
      assert (Ex : exs us src dst frac (S k) x = rs (fun j => Am src dst frac x j * exs us src dst frac k j) nn).
      { unfold exs. simpl strength. apply (step_mat t0 us src dst frac nn Hv (le_n _)). lia. }
      rewrite Ex. fold nn in UE. lra.
Qed.

End Sim3.

(* ------------------------------------------------------------------ *)
(* The faced values and their bounds                                   *)
(* ------------------------------------------------------------------ *)

Lemma faced_f_spec2 : forall (n : int) (adj : array bool) (v : array float) (J : Z -> bool) (i : int) (Sm : R),
  (1 <= to_Z n <= 100)%Z -> okv v (to_Z n) -> (to_Z i < to_Z n)%Z ->
  (forall k : int, (to_Z k < to_Z n)%Z -> adj.[i * n + k] = J (to_Z k)) ->
  Rabs (fv v (to_Z i)) + rs (fun k => if J k then Rabs (fv v k) else 0) (Z.to_nat (to_Z n)) <= Sm -> Sm <= 1000000000 ->
  exists F, repr (faced_f n adj v i) F /\
    Rabs (F - (fv v (to_Z i) + rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z n))))
      <= INR (Z.to_nat (to_Z n)) * u * (Sm + 1).
Proof.
  intros n adj v J i Sm Hn Ok Hi HJ HS HS1. unfold faced_f.
  assert (HJn : forall k, 0 <= (if J k then Rabs (fv v k) else 0)) by (intros; destruct (J k); [apply Rabs_pos | lra]).
  assert (HS0 : 0 <= Sm).
  { eapply Rle_trans; [| exact HS]. pose proof (Rabs_pos (fv v (to_Z i))).
    pose proof (rs_nonneg (fun k => if J k then Rabs (fv v k) else 0) (Z.to_nat (to_Z n)) ltac:(intros; apply HJn)). lra. }
  pose proof (to_Z_bounded i). pose proof u_pos.
  apply (for_inv (fun k acc => exists F, repr acc F /\
    Rabs (F - (fv v (to_Z i) + rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z k))))
      <= INR (Z.to_nat (to_Z k)) * u * (Sm + 1))).
  - change (to_Z 0) with 0%Z. lia.
  - exists (fv v (to_Z i)). split; [rewrite <- (of_to_Z i) at 1; apply (okv_repr v (to_Z n)); [exact Ok | lia]|].
    simpl. replace (fv v (to_Z i) - (fv v (to_Z i) + 0)) with 0 by ring. rewrite Rabs_R0. lra.
  - intros k acc Hk (F & HF & HE). change (to_Z 0) with 0%Z in Hk.
    assert (E1 : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    assert (Ek : Z.to_nat (to_Z (k + 1)) = S (Z.to_nat (to_Z k))) by (rewrite E1; lia).
    rewrite Ek. simpl rs. rewrite Z2Nat.id by lia. rewrite HJ by lia.
    assert (HY : Rabs (fv v (to_Z i) + (rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z k)) +
                       (if J (to_Z k) then fv v (to_Z k) else 0))) <= Sm).
    { eapply Rle_trans; [| exact HS].
      eapply Rle_trans; [apply Rabs_triang|]. apply Rplus_le_compat_l.
      replace (rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z k)) + (if J (to_Z k) then fv v (to_Z k) else 0))
        with (rs (fun k => if J k then fv v k else 0) (S (Z.to_nat (to_Z k)))) by (simpl; rewrite Z2Nat.id by lia; reflexivity).
      eapply Rle_trans; [apply rs_abs|].
      eapply Rle_trans; [| apply (rs_mono_n _ (S (Z.to_nat (to_Z k)))); [lia | intros; apply HJn]].
      apply rs_le. intros m _. destruct (J m); [lra | rewrite Rabs_R0; lra]. }
    assert (Hc : 0 <= INR (Z.to_nat (to_Z k)) /\ INR (Z.to_nat (to_Z k)) * u <= 1).
    { split; [apply pos_INR|]. rewrite INR_IZR_INZ. assert (IZR (Z.of_nat (Z.to_nat (to_Z k))) <= 100) by (apply IZR_le; lia).
      rewrite u_val. lra. }
    destruct (J (to_Z k)) eqn:EJ.
    + destruct (op_err (F + fv v (to_Z k)) _ Sm _ (proj1 Hc) (proj2 Hc) HY) as [O1 O2].
      { replace (F + fv v (to_Z k) - (fv v (to_Z i) + (rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z k)) + fv v (to_Z k))))
          with (F - (fv v (to_Z i) + rs (fun k => if J k then fv v k else 0) (Z.to_nat (to_Z k)))) by ring. exact HE. }
      exists (rnd (F + fv v (to_Z k))). split.
      * apply repr_add; [exact HF | rewrite <- (of_to_Z k) at 1; apply (okv_repr v (to_Z n)); [exact Ok | lia] |].
        apply big_no_overflow. lra.
      * rewrite S_INR. exact O1.
    + exists F. split; [exact HF|]. rewrite Rplus_0_r, S_INR.
      eapply Rle_trans; [exact HE|]. apply Rmult_le_compat_r; [lra|]. apply Rmult_le_compat_r; lra.
Qed.

Lemma fpair_spec : forall (n : int) (adj : array bool) (v e : array float) (J : Z -> bool) (i : int),
  (1 <= to_Z n <= 100)%Z -> okv v (to_Z n) -> okv e (to_Z n) -> (to_Z i < to_Z n)%Z ->
  (forall k, (0 <= k < to_Z n)%Z -> 0 <= fv e k <= 1 /\ Rabs (fv v k) <= 1000000) ->
  (forall k : int, (to_Z k < to_Z n)%Z -> adj.[i * n + k] = J (to_Z k)) ->
  let p := fpair n adj v e i in
  ap (Z.to_nat (to_Z n)) (fst p) (fv e (to_Z i) + rs (fun k => if J k then fv e k else 0) (Z.to_nat (to_Z n))) /\
  ap (Z.to_nat (to_Z n)) (snd p) (Rabs (fv v (to_Z i)) + rs (fun k => if J k then Rabs (fv v k) else 0) (Z.to_nat (to_Z n))).
Proof.
  intros n adj v e J i Hn Okv Oke Hi Hb HJ p. unfold p, fpair.
  pose proof (to_Z_bounded i).
  assert (Ri : repr v.[i] (fv v (to_Z i))) by (rewrite <- (of_to_Z i) at 1; apply (okv_repr v (to_Z n)); [exact Okv | lia]).
  assert (Re : repr e.[i] (fv e (to_Z i))) by (rewrite <- (of_to_Z i) at 1; apply (okv_repr e (to_Z n)); [exact Oke | lia]).
  destruct (Hb (to_Z i) ltac:(lia)) as [Bei Bvi].
  apply (for_inv (fun k st =>
    ap (Z.to_nat (to_Z k)) (fst st) (fv e (to_Z i) + rs (fun k => if J k then fv e k else 0) (Z.to_nat (to_Z k))) /\
    ap (Z.to_nat (to_Z k)) (snd st) (Rabs (fv v (to_Z i)) + rs (fun k => if J k then Rabs (fv v k) else 0) (Z.to_nat (to_Z k))))).
  - change (to_Z 0) with 0%Z. lia.
  - simpl fst; simpl snd. change (Z.to_nat (to_Z 0)) with 0%nat. simpl rs. rewrite !Rplus_0_r.
    split; apply ap_exact; [exact Re | lra | apply repr_abs, Ri | apply Rabs_pos].
  - intros k [a b] Hk [IA IB]. simpl fst in *; simpl snd in *. change (to_Z 0) with 0%Z in Hk.
    destruct (int_next k ltac:(lia)) as [_ E2]. rewrite E2. rewrite !rs_S, Z2Nat.id by lia.
    set (kn := Z.to_nat (to_Z k)) in *.
    assert (Hkn : (Z.of_nat (S kn) <= 100)%Z) by (unfold kn; lia).
    assert (INR kn <= 100) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
    assert (BE : 0 <= rs (fun k => if J k then fv e k else 0) kn <= INR kn).
    { split; [apply rs_nonneg | rewrite <- (Rmult_1_r (INR kn)); apply rs_const_le]; intros m Hm;
        destruct (J m); try lra; apply (Hb m); lia. }
    assert (BV : 0 <= rs (fun k => if J k then Rabs (fv v k) else 0) kn <= INR kn * 1000000).
    { split; [apply rs_nonneg | apply rs_const_le]; intros m Hm; destruct (J m); try lra;
        [apply Rabs_pos | apply (Hb m); lia]. }
    rewrite HJ by lia. destruct (J (to_Z k)) eqn:EJ; simpl fst; simpl snd.
    + assert (Rk : repr v.[k] (fv v (to_Z k))) by (rewrite <- (of_to_Z k) at 1; apply (okv_repr v (to_Z n)); [exact Okv | lia]).
      assert (Rek : repr e.[k] (fv e (to_Z k))) by (rewrite <- (of_to_Z k) at 1; apply (okv_repr e (to_Z n)); [exact Oke | lia]).
      destruct (Hb (to_Z k) ltac:(lia)) as [Bek Bvk].
      replace (S kn) with (kn + 0 + 1)%nat by lia. rewrite <- !Rplus_assoc.
      split; apply ap_add; try lia; try assumption.
      * apply ap_exact; [exact Rek | lra].
      * lra.
      * apply ap_exact; [apply repr_abs, Rk | apply Rabs_pos].
      * lra.
    + rewrite !Rplus_0_r. split; [apply (ap_mono kn); [lia | exact IA] | apply (ap_mono kn); [lia | exact IB]].
Qed.

Lemma gmax_spec : forall (n : int) (g : int -> float) (G : Z -> R),
  (forall i : int, (to_Z i < to_Z n)%Z -> repr (g i) (G (to_Z i)) /\ 0 <= G (to_Z i)) ->
  exists Bv, repr (gmax n g) Bv /\ 0 <= Bv /\ forall i, (0 <= i < to_Z n)%Z -> G i <= Bv.
Proof.
  intros n g G HG. unfold gmax.
  apply (for_inv (fun j m => exists Bv, repr m Bv /\ 0 <= Bv /\ forall i, (0 <= i < to_Z j)%Z -> G i <= Bv)).
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded n). lia.
  - exists 0. split; [exact repr_zero'|]. split; [lra|]. intros i Hi. change (to_Z 0) with 0%Z in Hi. lia.
  - intros j m Hj (Bv & Hr & HB0 & Hle). change (to_Z 0) with 0%Z in Hj.
    assert (E : to_Z (j + 1) = (to_Z j + 1)%Z) by sia.
    destruct (HG j ltac:(lia)) as [Hgj Bj].
    pose proof (repr_ltb_iff m (g j) Bv (G (to_Z j)) Hr Hgj) as Hlt.
    destruct (m <? g j)%float eqn:Ec.
    + exists (G (to_Z j)). split; [exact Hgj|]. split; [lra|]. intros i Hi. rewrite E in Hi.
      destruct (Z.eq_dec i (to_Z j)) as [-> | Ei]; [lra|]. pose proof (Hle i ltac:(lia)).
      pose proof (proj1 Hlt eq_refl). lra.
    + exists Bv. split; [exact Hr|]. split; [lra|]. intros i Hi. rewrite E in Hi.
      destruct (Z.eq_dec i (to_Z j)) as [-> | Ei]; [| apply Hle; lia].
      destruct (Rlt_le_dec Bv (G (to_Z j))) as [Hl | Hl]; [| exact Hl].
      apply Hlt in Hl. discriminate.
Qed.

Lemma fcheck_spec : forall B o Bv Ov, fcheck B o = true -> repr B Bv -> repr o Ov ->
  Bv < / 1048576 \/ Bv * 1048577 < Ov.
Proof.
  intros B o Bv Ov H HB HO. unfold fcheck in H.
  pose proof (fex_val B Bv HB) as FB. pose proof (fex_val o Ov HO) as FO.
  destruct (fex B) as [mb eb]. destruct (fex o) as [mo eo]. unfold dval in FB, FO; simpl in FB, FO.
  apply Bool.orb_prop in H as [H | H]; apply dlt_spec in H.
  - left. replace (bp (-20)) with (/ 1048576) in H by reflexivity. lra.
  - right. rewrite mult_IZR in H. rewrite <- FB, <- FO. lra.
Qed.

Lemma fbound_spec : forall (n : int) (adj : array bool) (v e : array float) (J : Z -> bool) (i : int) (nu : float) (NU : R),
  (1 <= to_Z n <= 100)%Z -> okv v (to_Z n) -> okv e (to_Z n) -> (to_Z i < to_Z n)%Z ->
  (forall k, (0 <= k < to_Z n)%Z -> 0 <= fv e k <= 1 /\ Rabs (fv v k) <= 1000000) ->
  (forall k : int, (to_Z k < to_Z n)%Z -> adj.[i * n + k] = J (to_Z k)) ->
  repr nu NU -> 0 <= NU <= 1 ->
  exists F, repr (fbound n adj v e nu i) F /\ 0 <= F /\
    (fv e (to_Z i) + rs (fun k => if J k then fv e k else 0) (Z.to_nat (to_Z n))) +
    NU * ((Rabs (fv v (to_Z i)) + rs (fun k => if J k then Rabs (fv v k) else 0) (Z.to_nat (to_Z n))) + 1) <= F.
Proof.
  intros n adj v e J i nu NU Hn Okv Oke Hi Hb HJ Rnu Bnu.
  destruct (fpair_spec n adj v e J i Hn Okv Oke Hi Hb HJ) as [A1 A2].
  unfold fbound. set (p := fpair n adj v e i) in *. set (nn := Z.to_nat (to_Z n)) in *.
  set (Ef := fv e (to_Z i) + rs (fun k => if J k then fv e k else 0) nn) in *.
  set (Mf := Rabs (fv v (to_Z i)) + rs (fun k => if J k then Rabs (fv v k) else 0) nn) in *.
  assert (Hnn : (Z.of_nat nn <= 100)%Z) by (unfold nn; lia).
  assert (INR nn <= 100) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
  pose proof (to_Z_bounded i).
  assert (BE : 0 <= Ef <= 101).
  { destruct (Hb (to_Z i) ltac:(lia)) as [B1 _].
    assert (0 <= rs (fun k => if J k then fv e k else 0) nn <= INR nn).
    { split; [apply rs_nonneg | rewrite <- (Rmult_1_r (INR nn)); apply rs_const_le]; intros m Hm;
        destruct (J m); try lra; apply (Hb m); unfold nn in Hm; lia. }
    unfold Ef. lra. }
  assert (BM : 0 <= Mf <= 101000000).
  { destruct (Hb (to_Z i) ltac:(lia)) as [_ B2].
    assert (0 <= rs (fun k => if J k then Rabs (fv v k) else 0) nn <= INR nn * 1000000).
    { split; [apply rs_nonneg | apply rs_const_le]; intros m Hm; destruct (J m); try lra;
        [apply Rabs_pos | apply (Hb m); unfold nn in Hm; lia]. }
    pose proof (Rabs_pos (fv v (to_Z i))). unfold Mf. lra. }
  assert (h1 : ap (nn + 0 + 1) (snd p + 1)%float (Mf + 1))
    by (apply ap_add; [lia | exact A2 | apply ap_exact; [exact repr_one | lra] | lra]).
  assert (h2 : ap (nn + 0 + 1 + 1) (nu * (snd p + 1))%float (NU * (Mf + 1)))
    by (apply ap_mulc; [lia | exact Rnu | exact Bnu | exact h1 | lra]).
  assert (B3 : NU * (Mf + 1) <= 1 * 101000001) by (apply Rmult_le_compat; lra).
  assert (h3 : ap (nn + (nn + 0 + 1 + 1) + 1) (fst p + nu * (snd p + 1))%float (Ef + NU * (Mf + 1)))
    by (apply ap_add; [lia | exact A1 | exact h2 | lra]).
  assert (Hk : (Z.of_nat (nn + (nn + 0 + 1 + 1) + 1) <= 200000)%Z) by lia.
  assert (HX : Ef + NU * (Mf + 1) <= 100000000000000) by lra.
  destruct (ap_up _ _ _ Hk h3 HX) as (F & RF & F1 & F2).
  exists F. split; [exact RF|]. assert (0 <= NU * (Mf + 1)) by (apply Rmult_le_pos; lra). split; lra.
Qed.

Lemma nu_spec : forall n : int, (1 <= to_Z n <= 100)%Z ->
  exists NU, repr (of_uint63 (n + 1) * f_u)%float NU /\ INR (Z.to_nat (to_Z n)) * u <= NU <= 1.
Proof.
  intros n Hn.
  assert (E : to_Z (n + 1) = (to_Z n + 1)%Z) by sia.
  assert (R0 : repr (of_uint63 (n + 1)) (IZR (to_Z n + 1))).
  { rewrite <- E. apply repr_of_uint63_exact. rewrite E. lia. }
  set (z := IZR (to_Z n + 1) * u).
  assert (Ez : z = (IZR (to_Z n) + 1) * u) by (unfold z; rewrite plus_IZR; reflexivity).
  assert (Hn0 : 1 <= IZR (to_Z n) <= 100) by (split; apply IZR_le; lia).
  assert (Hz : 0 <= z) by (rewrite Ez; pose proof u_pos; nra).
  assert (R : repr (of_uint63 (n + 1) * f_u)%float (rnd z)).
  { apply repr_mul; [exact R0 | exact repr_fu |]. apply big_no_overflow.
    change (IZR (to_Z n + 1) * u) with z. rewrite Rabs_right by lra. rewrite Ez, u_val. lra. }
  exists (rnd z). split; [exact R|].
  rewrite INR_IZR_INZ, Z2Nat.id by lia.
  pose proof (rnd_lo z Hz). pose proof (rnd_hi z Hz). pose proof eta30.
  rewrite Ez in *. rewrite u_val in *. split; lra.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Theorem timing_impl_correct : forall (t : N) (us : list R) (src dst : list N) (frac : list R)
    (xt : uint) (xu : array float) (xs xd : array uint) (xf : array float),
  valid_input t us src dst frac ->
  repr xt t -> repr xu us -> repr xs src -> repr xd dst -> repr xf frac ->
  exists o : R, repr (timing_impl xt xu xs xd xf) o /\ timing_spec t us src dst frac o.
Proof.
  intros t us src dst frac xt xu xs xd xf Hv Ht Hu Hs Hd Hf.
  pose proof Hv as Hv'. destruct Hv' as [HN Hl HT Hdl Hfl Hu0 Hs0 Hd0 Hf0 Ho].
  set (nu := List.length us) in *. set (Lr := List.length src) in *.
  unfold len in HN, Hl, Hdl, Hfl. fold nu Lr in HN, Hl, Hdl, Hfl.
  apply Nat2N.inj in Hdl. apply Nat2N.inj in Hfl.
  assert (Hnu : (1 <= Z.of_nat nu <= 100)%Z) by lia.
  assert (HLr : (Z.of_nat Lr <= 9801)%Z).
  { assert ((N.of_nat nu - 1) ^ 2 <= 9801)%N by (change 9801%N with (99 ^ 2)%N; apply N.pow_le_mono_l; lia). lia. }
  assert (Hxt : to_Z xt = Z.of_N t) by (unfold repr, repr_uint in Ht; pose proof (to_Z_bounded xt); lia).
  pose proof (repr_len_f xu us Hu) as Lxu. pose proof (repr_len_u xs src Hs) as Lxs.
  unfold timing_impl. cbv zeta.
  set (n := PArray.length xu) in *. set (L := PArray.length xs) in *. fold nu in Lxu. fold Lr in Lxs.
  assert (Hn : (1 <= to_Z n <= 100)%Z) by lia.
  assert (HL : Z.of_nat Lr = to_Z L) by lia.
  assert (HLb : (to_Z L <= 9801)%Z) by lia.
  assert (HsrcZ : forall l, (0 <= l < to_Z L)%Z -> to_Z xs.[of_Z l] = sr src l /\ (0 <= sr src l < to_Z n)%Z).
  { intros l Hl'. rewrite (repr_get_u xs src l Hs) by lia. unfold sr, get_N. rewrite Z_N_nat. split; [reflexivity|].
    pose proof (nth_Forall _ src (Z.to_nat l) 0%N Hs0 ltac:(lia)) as B. cbv beta in B. rewrite len_nat in B. lia. }
  assert (HdstZ : forall l, (0 <= l < to_Z L)%Z -> to_Z xd.[of_Z l] = dr dst l /\ (0 <= dr dst l < to_Z n)%Z).
  { intros l Hl'. rewrite (repr_get_u xd dst l Hd) by lia. unfold dr, get_N. rewrite Z_N_nat. split; [reflexivity|].
    pose proof (nth_Forall _ dst (Z.to_nat l) 0%N Hd0 ltac:(lia)) as B. cbv beta in B. rewrite len_nat in B. lia. }
  assert (HfrZ : forall l, (0 <= l < to_Z L)%Z -> repr xf.[of_Z l] (fr frac l) /\ 0 < fr frac l <= 1).
  { intros l Hl'. split.
    - pose proof (repr_get_f xf frac l Hf ltac:(lia)) as [H1 H2].
      unfold fr, get_R. rewrite Z_N_nat. split; [exact H1 | exact H2].
    - apply (fr_range t us src dst frac nu Hv (le_n _)). fold Lr. lia. }
  assert (HuZ : forall i, (0 <= i < to_Z n)%Z -> repr xu.[of_Z i] (get_R us (Z.to_N i))).
  { intros i Hi. pose proof (repr_get_f xu us i Hu ltac:(lia)) as [H1 H2].
    unfold get_R. rewrite Z_N_nat. split; [exact H1 | exact H2]. }
  (* the counts and the outflows *)
  destruct (cnt_spec src dst n L xs xd HL HLb Hn HsrcZ HdstZ) as [Lc Ecnt].
  set (c := loop L (cnt_step xs xd) 0%uint63 (PArray.make n 0%uint63)) in *.
  destruct (out_spec src dst frac n L xs xd xf HL HLb Hn HsrcZ HdstZ HfrZ) as [Lou Hou].
  set (ou := loop L (out_step xs xd xf) 0 (PArray.make n 0%float)) in *. fold Lr in Hou.
  assert (Hco : forall x, (0 <= x < to_Z n)%Z -> repr (coef ou (of_Z x)) (fval (coef ou (of_Z x))) /\
            Rabs (1 - outj src dst frac x) <= fval (coef ou (of_Z x)) <= 5).
  { intros x Hx. pose proof (outj_spec t us src dst frac nu Hv (le_n _) x ltac:(lia)) as [_ Bo].
    destruct (coef_spec ou (of_Z x) Lr (outp src dst frac x Lr) ltac:(lia) (Hou x Hx) Bo) as (C & RC & BC).
    rewrite (repr_fval _ _ RC). split; [exact RC | exact BC]. }
  assert (Hkx : forall x, (0 <= x < to_Z n)%Z -> repr (kx c (of_Z x)) (fval (kx c (of_Z x))) /\
            (2 * IZR (zs (fun l => tauZ src dst l x) Lr) + 2) * u <= fval (kx c (of_Z x)) <= 1).
  { intros x Hx. pose proof (Ecnt x Hx) as Ex. fold Lr in Ex.
    pose proof (zs_bound (fun l => tauZ src dst l x) Lr (fun k => tauZ_range src dst 0%uint63 0%uint63 k x)) as Zb.
    destruct (kx_spec c (of_Z x) ltac:(lia)) as (K & RK & BK).
    rewrite (repr_fval _ _ RK). rewrite Ex in BK. split; [exact RK | exact BK]. }
  (* the simulation *)
  assert (Hnu' : to_Z n = Z.of_nat nu) by lia.
  assert (Hlu : to_Z (PArray.length xu) = to_Z n) by reflexivity.
  assert (HT' : (to_Z xt <= 5000)%Z) by lia.
  pose proof (sim_inv t us src dst frac n L xt xs xd xf xu ou c Hv Hnu' HL HLb Hn HsrcZ HdstZ HfrZ HuZ
                Hlu HT' Hco Hkx) as SI.
  cbv zeta in SI.
  destruct (loop xt (tstep n L xs xd xf ou c) 0 (xu, PArray.make n 0%float, true)) as [[v e] ok] eqn:Est.
  simpl fst in SI; simpl snd in SI.
  destruct ok; [| apply timing_exact_correct; assumption].
  destruct (SI eq_refl) as (Okv & Oke & Hve).
  set (T := Z.to_nat (to_Z xt)) in *.
  assert (HT5 : (Z.of_nat T <= 10000)%Z) by (unfold T; lia).
  assert (Hb : forall k, (0 <= k < to_Z n)%Z -> 0 <= fv e k <= 1 /\ Rabs (fv v k) <= 1000000).
  { intros k Hk. destruct (Hve k Hk) as [B1 B2]. split; [exact B1|].
    pose proof (ex_bound t us src dst frac T k Hv HT5 ltac:(lia)).
    pose proof (Rabs_tri (fv v k) (exs us src dst frac T k)). lra. }
  (* the adjacency *)
  set (adj := loop L (adj_step n xs xd) 0%uint63 (PArray.make (n * n) false)) in *.
  assert (Hnn : (to_Z n * to_Z n <= 4194303)%Z) by nia.
  assert (Hadj : forall i k, (0 <= i < to_Z n)%Z -> (0 <= k < to_Z n)%Z ->
            adj.[of_Z (i * to_Z n + k)] = joined src dst (Z.to_N i) (Z.to_N k)).
  { intros i k Hi Hk. unfold adj.
    refine (adj_spec src dst n L xs xd Hnn ltac:(lia) _ _ i k Hi Hk).
    - intros l Hl'. destruct (HsrcZ l Hl') as [E1 E2]. split; [exact E1 | pose proof (proj2 E2) as E3; rewrite <- E1 in E3; exact E3].
    - intros l Hl'. destruct (HdstZ l Hl') as [E1 E2]. split; [exact E1 | pose proof (proj2 E2) as E3; rewrite <- E1 in E3; exact E3]. }
  assert (HadjJ : forall z, (0 <= z < to_Z n)%Z -> forall k : int, (to_Z k < to_Z n)%Z ->
            adj.[of_Z z * n + k] = joined src dst (Z.to_N z) (Z.to_N (to_Z k))).
  { intros z Hz k Hk. assert (Iz : to_Z (of_Z z) = z) by (apply to_Z_of_Z_n; lia).
    rewrite <- Hadj by (pose proof (to_Z_bounded k); lia).
    pose proof (to_Z_bounded k).
    assert (Hzn : (0 <= z * to_Z n <= 10000)%Z)
      by (split; [apply Z.mul_nonneg_nonneg; lia | apply (Z.le_trans _ (100 * 100)); [apply Z.mul_le_mono_nonneg; lia | lia]]).
    f_equal. apply to_Z_inj. rewrite idx2, Iz.
    + symmetry. apply to_Z_of_Z_small. rewrite wB_val. lia.
    + rewrite Iz. rewrite wB_val. lia. }
  destruct (nu_spec n Hn) as (NU & RNU & BNU).
  set (nuf := (of_uint63 (n + 1) * f_u)%float) in *.
  replace (Z.to_nat (to_Z n)) with nu in BNU by lia.
  (* the faced values: each within its bound F_z *)
  set (G := fun z => fval (faced_f n adj v (of_Z z))).
  set (fc := fun z => faced us src dst frac T (Z.to_N z)).
  set (Fz := fun z => fval (fbound n adj v e nuf (of_Z z))).
  assert (Hface : forall z, (0 <= z < to_Z n)%Z ->
     repr (faced_f n adj v (of_Z z)) (G z) /\ repr (fbound n adj v e nuf (of_Z z)) (Fz z) /\ 0 <= Fz z /\
     Rabs (G z - fc z) <= Fz z).
  { intros z Hz. assert (Iz : to_Z (of_Z z) = z) by (apply to_Z_of_Z_n; lia).
    set (J := fun k => joined src dst (Z.to_N z) (Z.to_N k)).
    set (Mf := Rabs (fv v z) + rs (fun k => if J k then Rabs (fv v k) else 0) nu).
    set (Ef := fv e z + rs (fun k => if J k then fv e k else 0) nu).
    assert (HJ : forall k : int, (to_Z k < to_Z n)%Z -> adj.[of_Z z * n + k] = J (to_Z k)) by (intros; apply HadjJ; lia).
    destruct (fbound_spec n adj v e J (of_Z z) nuf NU Hn Okv Oke ltac:(lia) Hb HJ RNU ltac:(pose proof u_pos; pose proof (pos_INR nu); nra))
      as (F & RF & F0 & FX).
    rewrite Iz in FX. replace (Z.to_nat (to_Z n)) with nu in FX by lia. fold Mf Ef in FX.
    assert (HMf : Mf <= 1000000000).
    { assert (rs (fun k => if J k then Rabs (fv v k) else 0) nu <= INR nu * 1000000)
        by (apply rs_const_le; intros m Hm; destruct (J m); [apply (Hb m); lia | lra]).
      assert (INR nu <= 100) by (rewrite INR_IZR_INZ; apply IZR_le; lia).
      pose proof (proj2 (Hb z Hz)). unfold Mf. lra. }
    destruct (faced_f_spec2 n adj v J (of_Z z) Mf Hn Okv ltac:(lia) HJ ltac:(rewrite Iz; replace (Z.to_nat (to_Z n)) with nu by lia; apply Rle_refl) HMf)
      as (Fa & HFa & HFe).
    rewrite Iz in HFe. replace (Z.to_nat (to_Z n)) with nu in HFe by lia.
    assert (EG : G z = Fa) by (unfold G; exact (repr_fval _ _ HFa)).
    assert (EF : Fz z = F) by (unfold Fz; exact (repr_fval _ _ RF)).
    split; [rewrite EG; exact HFa|]. split; [rewrite EF; exact RF|]. rewrite EF. split; [exact F0|]. rewrite EG.
    assert (Ef' : fc z = exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu)
      by (unfold fc, faced, exs, J; rewrite sum_below_rs; reflexivity).
    rewrite Ef'.
    assert (H2 : Rabs ((fv v z + rs (fun k => if J k then fv v k else 0) nu) -
                       (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu)) <= Ef).
    { replace ((fv v z + rs (fun k => if J k then fv v k else 0) nu) -
               (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu))
        with ((fv v z - exs us src dst frac T z) + rs (fun k => if J k then fv v k - exs us src dst frac T k else 0) nu)
        by (rewrite (rs_ext (fun k => if J k then fv v k - exs us src dst frac T k else 0)
               (fun k => (if J k then fv v k else 0) - (if J k then exs us src dst frac T k else 0)) nu)
               by (intros; destruct (J _); ring); rewrite rs_sub; ring).
      eapply Rle_trans; [apply Rabs_triang|]. unfold Ef. apply Rplus_le_compat; [apply (Hve z Hz)|].
      eapply Rle_trans; [apply rs_abs|]. apply rs_le. intros k Hk. destruct (J k); [apply (Hve k); lia | rewrite Rabs_R0; lra]. }
    assert (H3 : INR nu * u * (Mf + 1) <= NU * (Mf + 1)).
    { apply Rmult_le_compat_r; [pose proof (Rabs_pos (fv v z)); unfold Mf;
        pose proof (rs_nonneg (fun k => if J k then Rabs (fv v k) else 0) nu ltac:(intros m _; cbv beta; destruct (J m); [apply Rabs_pos | lra])); lra | lra]. }
    pose proof (Rabs_tri (Fa - (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu))
                         ((fv v z + rs (fun k => if J k then fv v k else 0) nu) -
                          (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu))) as H4.
    replace (Fa - (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu) -
             (fv v z + rs (fun k => if J k then fv v k else 0) nu - (exs us src dst frac T z + rs (fun k => if J k then exs us src dst frac T k else 0) nu)))
      with (Fa - (fv v z + rs (fun k => if J k then fv v k else 0) nu)) in H4 by ring.
    lra. }
  (* the bound B and the least computed value *)
  destruct (gmax_spec n (fbound n adj v e nuf) Fz) as (Bv & RB & B0 & HBm).
  { intros i Hi. pose proof (to_Z_bounded i). destruct (Hface (to_Z i) ltac:(lia)) as (_ & H1 & H2 & _).
    rewrite of_to_Z in H1. unfold Fz in *. rewrite of_to_Z in *. split; [exact H1 | exact H2]. }
  destruct (loop_fmin n (faced_f n adj v) G ltac:(lia)) as (ic & Hic & Ho' & Hmin).
  { intros i Hi. pose proof (to_Z_bounded i). destruct (Hface (to_Z i) ltac:(lia)) as [H1 _]. rewrite of_to_Z in H1. exact H1. }
  set (o := loop n (fun i b => fmin b (faced_f n adj v i)) 1 (faced_f n adj v 0)) in *.
  set (B := gmax n (fbound n adj v e nuf)) in *.
  destruct (fcheck B o) eqn:Ec; [| apply timing_exact_correct; assumption].
  pose proof (fcheck_spec B o Bv (G ic) Ec RB Ho') as HB2.
  destruct (argmin_exists fc (Z.of_nat nu) ltac:(lia)) as (is & His & Hism).
  exists (G ic). split; [exact Ho'|].
  assert (ET : T = N.to_nat t) by (unfold T; rewrite Hxt; lia).
  assert (Hb1 : G ic <= fc is + Bv).
  { pose proof (Hmin is ltac:(lia)). destruct (Hface is ltac:(lia)) as (_ & _ & _ & H2).
    pose proof (HBm is ltac:(lia)). pose proof (Rle_abs (G is - fc is)). lra. }
  assert (Hb2 : fc is - Bv <= G ic).
  { pose proof (Hism ic ltac:(lia)). destruct (Hface ic Hic) as (_ & _ & _ & H2). pose proof (HBm ic Hic).
    pose proof (Rle_abs (- (G ic - fc ic))) as Ha. rewrite Rabs_Ropp in Ha. lra. }
  exists (Z.to_N is). split; [unfold len; fold nu; lia|]. split.
  - intros m' Hm'. rewrite <- ET. pose proof (Hism (Z.of_N m') ltac:(unfold len in Hm'; fold nu in Hm'; lia)) as Hq.
    unfold fc in Hq. rewrite N2Z.id in Hq. exact Hq.
  - cbv zeta. rewrite <- ET. fold (fc is).
    destruct HB2 as [HB2 | HB2].
    + left. apply Rabs_def1; lra.
    + right. assert (Ha : 1048576 * Bv < fc is) by lra.
      rewrite (Rabs_right (fc is)) by lra. apply Rabs_def1; lra.
Qed.

Definition timing_correct :
  forall (t : N) (u : list R) (src dst : list N) (frac : list R)
         (xt : uint) (xu : array float) (xs xd : array uint)
         (xf : array float),
    valid_input t u src dst frac ->
    repr xt t -> repr xu u -> repr xs src -> repr xd dst -> repr xf frac ->
    exists o : R, repr (timing xt xu xs xd xf) o /\
                  timing_spec t u src dst frac o
  := timing_impl_correct.
