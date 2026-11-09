(* Correctness proofs for ada_implem.v. *)
(* Implementation of ada (ada.spec): Newton's forward-difference table.

   Code.  [ada a] copies a into one flat array t of length n and runs
   n - 1 rounds in place: round k (k = 1 .. n-1) overwrites
   t[j] <- t[j+1] - t[j] for j = 0 .. n-1-k, so after round k the cells
   0 .. n-1-k hold the k-th differences and the cells above hold, each, the
   last entry of an earlier row: at the end t[i] is the last entry of row
   n-1-i.  While a round runs it records whether its row has a non-zero
   entry; d is the last round whose row is non-zero (0 if none).  The answer
   is (d, sum_{k=0}^{d} t[n-1-k]): the last entries of rows 0 .. d, which is
   the extension of the table by one column.  All arithmetic is wrapping
   63-bit; every difference and the sum are bounded by 2^10 * 2*10^6 in
   absolute value, so the words read through Sint63 are exact.  No Z, no
   nat in the code.

   Termination: every loop recurses structurally on an erased
   [Acc (Zwf 0) (gap m i)] proof, as in template/polymul1.

   Proof.  The math side models the table with [diffZ k g j] (k-th forward
   difference of g = nth _ v 0).  Over R, a polynomial of length <= k has
   zero k-th differences along x0, x0+h, ... ([diffR_poly], through the
   difference operator [dp] on coefficient lists); this gives minimality
   and, with Newton's identity [newton], the extrapolated value.  The
   existence of a polynomial of degree d goes through Newton-style
   interpolation on the first d+1 nodes ([interp]) and the propagation of
   the zero (d+1)-th row to all n values ([propagate]). *)

From Ada.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Reals Lra.
From Stdlib Require Sint63.
Import ListNotations.

Open Scope uint63_scope.
Open Scope Z_scope.

Unset Lia Cache.

From Ada Require Export ada_implem.
Open Scope uint63_scope.
Open Scope Z_scope.


(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma acopy_get : forall (t : array int) (i : int), (acopy t).[i] = t.[i].
Proof. intros t i. exact (get_copy int t i). Qed.

Lemma acopy_length : forall (t : array int), PArray.length (acopy t) = PArray.length t.
Proof. intros t. exact (length_copy int t). Qed.

Lemma row_loop_eq : forall m j t nz H,
  row_loop m j t nz H =
  match bdec (j <? m)%uint63 with
  | left Hj =>
      let x := (t.[j + 1] - t.[j])%uint63 in
      row_loop m (j + 1) t.[j <- x] (nz || negb (x =? 0)%uint63)
        (Acc_inv H (dec_step m j Hj))
  | right _ => (t, nz)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rows_loop_eq : forall n k t d H,
  rows_loop n k t d H =
  match bdec (k <? n)%uint63 with
  | left Hk =>
      let r := row_loop (n - k) 0 t false (Zwf_well_founded 0 (gap (n - k) 0)) in
      rows_loop n (k + 1) (fst r) (if snd r then k else d)
        (Acc_inv H (dec_step n k Hk))
  | right _ => (t, d)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sum_loop_eq : forall t top e k acc H,
  sum_loop t top e k acc H =
  match bdec (k <? e)%uint63 with
  | left Hk => sum_loop t top e (k + 1) (acc + t.[top - k])
                 (Acc_inv H (dec_step e k Hk))
  | right _ => acc
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Finite differences over Z and over R                                *)
(* ------------------------------------------------------------------ *)

Fixpoint diffZ (k : nat) (f : nat -> Z) : nat -> Z :=
  match k with
  | O => f
  | S k' => fun j => (diffZ k' f (S j) - diffZ k' f j)%Z
  end.

Fixpoint diffR (k : nat) (f : nat -> R) : nat -> R :=
  match k with
  | O => f
  | S k' => fun j => (diffR k' f (S j) - diffR k' f j)%R
  end.

Lemma diffZ_S : forall k f j, diffZ (S k) f j = (diffZ k f (S j) - diffZ k f j)%Z.
Proof. reflexivity. Qed.

Lemma diffR_S : forall k f j, diffR (S k) f j = (diffR k f (S j) - diffR k f j)%R.
Proof. reflexivity. Qed.

Lemma diffR_local : forall k f g j,
  (forall i, (j <= i <= j + k)%nat -> f i = g i) -> diffR k f j = diffR k g j.
Proof.
  induction k as [|k IH]; intros f g j Hfg.
  - apply Hfg. lia.
  - rewrite !diffR_S. rewrite (IH f g (S j)), (IH f g j); [reflexivity | | ];
      intros i Hi; apply Hfg; lia.
Qed.

Lemma diffR_ext : forall k f g,
  (forall i, f i = g i) -> forall j, diffR k f j = diffR k g j.
Proof. intros k f g H j. apply diffR_local. intros i _. apply H. Qed.

Lemma diffR_commute : forall k f j,
  diffR k (fun i => (f (S i) - f i)%R) j = diffR (S k) f j.
Proof.
  induction k as [|k IH]; intros f j.
  - reflexivity.
  - rewrite diffR_S, !IH. reflexivity.
Qed.

Lemma diffR_sub : forall k f g j,
  diffR k (fun i => (f i - g i)%R) j = (diffR k f j - diffR k g j)%R.
Proof.
  induction k as [|k IH]; intros f g j.
  - reflexivity.
  - rewrite !diffR_S, !IH. ring.
Qed.

Lemma diffR_IZR : forall k g j,
  diffR k (fun i => IZR (g i)) j = IZR (diffZ k g j).
Proof.
  induction k as [|k IH]; intros g j.
  - reflexivity.
  - rewrite diffR_S, diffZ_S, !IH, minus_IZR. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Polynomials as coefficient lists                                    *)
(* ------------------------------------------------------------------ *)

Section Poly.
Local Open Scope R_scope.

Lemma pe_nil : forall x, poly_eval [] x = 0.
Proof. reflexivity. Qed.

Lemma pe_cons : forall a c x, poly_eval (a :: c) x = a + x * poly_eval c x.
Proof. reflexivity. Qed.

Fixpoint padd (p q : list R) : list R :=
  match p, q with
  | [], _ => q
  | _, [] => p
  | a :: p', b :: q' => (a + b) :: padd p' q'
  end.

Lemma padd_eval : forall p q x,
  poly_eval (padd p q) x = poly_eval p x + poly_eval q x.
Proof.
  induction p as [|a p IH]; intros [|b q] x; cbn [padd];
    rewrite ?pe_nil, ?pe_cons, ?IH; ring.
Qed.

Lemma padd_len : forall p q,
  List.length (padd p q) = Nat.max (List.length p) (List.length q).
Proof.
  induction p as [|a p IH]; intros [|b q]; cbn [padd List.length]; try lia.
  rewrite IH. lia.
Qed.

Definition pscale (a : R) (p : list R) : list R := map (fun b => a * b) p.

Lemma pscale_eval : forall a p x, poly_eval (pscale a p) x = a * poly_eval p x.
Proof.
  intros a p x. induction p as [|b p IH]; unfold pscale in *; cbn [map].
  - rewrite pe_nil. ring.
  - rewrite !pe_cons, IH. ring.
Qed.

Lemma pscale_len : forall a p, List.length (pscale a p) = List.length p.
Proof. intros. unfold pscale. apply length_map. Qed.

Definition cons0 (p : list R) : list R :=
  match p with [] => [] | _ => 0 :: p end.

Lemma cons0_eval : forall p x, poly_eval (cons0 p) x = x * poly_eval p x.
Proof.
  intros [|a p] x; unfold cons0; rewrite ?pe_nil, ?pe_cons; ring.
Qed.

Lemma cons0_len : forall p, (List.length (cons0 p) <= S (List.length p))%nat.
Proof. intros [|a p]; cbn; lia. Qed.

(* p(x + h) *)
Fixpoint shp (h : R) (c : list R) : list R :=
  match c with
  | [] => []
  | a :: c' => padd [a] (padd (pscale h (shp h c')) (cons0 (shp h c')))
  end.

Lemma shp_eval : forall h c x, poly_eval (shp h c) x = poly_eval c (x + h).
Proof.
  intros h c. induction c as [|a c IH]; intros x; cbn [shp].
  - rewrite !pe_nil. reflexivity.
  - rewrite !padd_eval, pscale_eval, cons0_eval, !pe_cons, pe_nil, IH. ring.
Qed.

Lemma shp_len : forall h c, (List.length (shp h c) <= List.length c)%nat.
Proof.
  intros h c. induction c as [|a c IH]; cbn [shp]; [cbn; lia|].
  rewrite !padd_len, pscale_len. pose proof (cons0_len (shp h c)).
  cbn [List.length]. lia.
Qed.

(* p(x + h) - p(x) *)
Fixpoint dp (h : R) (c : list R) : list R :=
  match c with
  | [] => []
  | a :: c' => padd (cons0 (dp h c')) (pscale h (shp h c'))
  end.

Lemma dp_eval : forall h c x,
  poly_eval (dp h c) x = poly_eval c (x + h) - poly_eval c x.
Proof.
  intros h c. induction c as [|a c IH]; intros x; cbn [dp].
  - rewrite !pe_nil. ring.
  - rewrite padd_eval, cons0_eval, pscale_eval, IH, shp_eval, !pe_cons. ring.
Qed.

Lemma dp_len : forall h c, (List.length (dp h c) <= List.length c - 1)%nat.
Proof.
  intros h c. induction c as [|a c IH]; cbn [dp]; [cbn; lia|].
  rewrite padd_len, pscale_len. pose proof (shp_len h c).
  assert (List.length (cons0 (dp h c)) <= List.length c)%nat.
  { destruct (dp h c) as [|b q]; cbn [cons0 List.length] in *; lia. }
  cbn [List.length]. lia.
Qed.

(* the values along x0, x0 + h, x0 + 2h, ... *)
Definition Fc (x0 h : R) (c : list R) : nat -> R :=
  fun j => poly_eval c (x0 + INR j * h).

Lemma Fc_diff : forall x0 h c j,
  Fc x0 h c (S j) - Fc x0 h c j = Fc x0 h (dp h c) j.
Proof.
  intros. unfold Fc. rewrite dp_eval, S_INR.
  replace (x0 + (INR j + 1) * h) with (x0 + INR j * h + h) by ring.
  reflexivity.
Qed.

(* A polynomial with at most k coefficients has zero k-th differences. *)
Lemma diffR_poly : forall x0 h k c, (List.length c <= k)%nat ->
  forall j, diffR k (Fc x0 h c) j = 0.
Proof.
  intros x0 h k. induction k as [|k IH]; intros c Hc j.
  - destruct c; [| cbn in Hc; lia]. cbn. reflexivity.
  - rewrite <- diffR_commute.
    rewrite (diffR_ext k _ (Fc x0 h (dp h c))) by (intros i; apply Fc_diff).
    apply IH. pose proof (dp_len h c). lia.
Qed.

Fixpoint sumR (m : nat) (F : nat -> R) : R :=
  match m with
  | O => 0
  | S m' => sumR m' F + F m'
  end.

Lemma sumR_S : forall m F, sumR (S m) F = sumR m F + F m.
Proof. reflexivity. Qed.

(* Newton: f(p+1) is the sum of the last entries of rows 0 .. m plus the
   (m+1)-th difference below them. *)
Lemma newton : forall f p m, (m <= p)%nat ->
  f (S p) = sumR (S m) (fun k => diffR k f (p - k)) + diffR (S m) f (p - m).
Proof.
  intros f p m. induction m as [|m IH]; intros Hm.
  - rewrite sumR_S. cbn [sumR]. rewrite Nat.sub_0_r. rewrite diffR_S. cbn [diffR]. ring.
  - rewrite IH by lia.
    replace (p - m)%nat with (S (p - S m)) by lia.
    rewrite (sumR_S (S m)). cbv beta.
    rewrite (diffR_S (S m)). ring.
Qed.

(* Padding with zero coefficients. *)
Lemma pad_eval : forall p k x, poly_eval (p ++ repeat 0 k) x = poly_eval p x.
Proof.
  induction p as [|a p IH]; intros k x.
  - cbn [app]. induction k as [|k IHk]; cbn [repeat]; rewrite ?pe_nil, ?pe_cons;
      [reflexivity|]. rewrite IHk, pe_nil. ring.
  - rewrite <- app_comm_cons, !pe_cons, IH. reflexivity.
Qed.

(* Interpolation on the first m nodes, Newton's way. *)
Definition mulX (a : R) (q : list R) : list R := padd (0 :: q) (pscale (- a) q).

Lemma mulX_eval : forall a q x, poly_eval (mulX a q) x = (x - a) * poly_eval q x.
Proof. intros. unfold mulX. rewrite padd_eval, pe_cons, pscale_eval. ring. Qed.

Fixpoint node (x0 h : R) (m : nat) : list R :=
  match m with
  | O => [1]
  | S m' => mulX (x0 + INR m' * h) (node x0 h m')
  end.

Lemma node_len : forall x0 h m, List.length (node x0 h m) = S m.
Proof.
  intros x0 h m. induction m as [|m IH]; [reflexivity|].
  cbn [node]. unfold mulX. rewrite padd_len, pscale_len. cbn [List.length]. lia.
Qed.

Lemma node_zero : forall x0 h m i, (i < m)%nat ->
  poly_eval (node x0 h m) (x0 + INR i * h) = 0.
Proof.
  intros x0 h m. induction m as [|m IH]; intros i Hi; [lia|].
  cbn [node]. rewrite mulX_eval.
  destruct (Nat.eq_dec i m) as [E | E].
  - subst. ring.
  - rewrite IH by lia. ring.
Qed.

Lemma node_nz : forall x0 h, h <> 0 -> forall m j, (m <= j)%nat ->
  poly_eval (node x0 h m) (x0 + INR j * h) <> 0.
Proof.
  intros x0 h Hh m. induction m as [|m IH]; intros j Hj.
  - cbn [node]. rewrite pe_cons, pe_nil. lra.
  - cbn [node]. rewrite mulX_eval.
    replace (x0 + INR j * h - (x0 + INR m * h)) with ((INR j - INR m) * h) by ring.
    apply Rmult_integral_contrapositive_currified; [|apply IH; lia].
    apply Rmult_integral_contrapositive_currified; [|exact Hh].
    apply Rminus_eq_contra. apply not_INR. lia.
Qed.

Fixpoint interp (x0 h : R) (y : nat -> R) (m : nat) : list R :=
  match m with
  | O => []
  | S m' =>
      let p := interp x0 h y m' in
      padd p (pscale ((y m' - poly_eval p (x0 + INR m' * h))
                      / poly_eval (node x0 h m') (x0 + INR m' * h))
                     (node x0 h m'))
  end.

Lemma interp_len : forall x0 h y m, (List.length (interp x0 h y m) <= m)%nat.
Proof.
  intros x0 h y m. induction m as [|m IH]; [cbn; lia|].
  cbn [interp]. rewrite padd_len, pscale_len, node_len. lia.
Qed.

Lemma interp_ok : forall x0 h y, h <> 0 -> forall m i, (i < m)%nat ->
  poly_eval (interp x0 h y m) (x0 + INR i * h) = y i.
Proof.
  intros x0 h y Hh m. induction m as [|m IH]; intros i Hi; [lia|].
  cbn [interp]. rewrite padd_eval, pscale_eval.
  destruct (Nat.eq_dec i m) as [E | E].
  - subst. field. apply node_nz; [exact Hh | lia].
  - rewrite (node_zero x0 h m i) by lia. rewrite IH by lia. ring.
Qed.

(* A function whose m-th differences vanish on [0, N) and which vanishes on
   [0, m) vanishes on [0, N + m). *)
Lemma propagate : forall m Nn (H : nat -> R),
  (forall j, (j < Nn)%nat -> diffR m H j = 0) ->
  (forall i, (i < m)%nat -> H i = 0) ->
  forall i, (i < Nn + m)%nat -> H i = 0.
Proof.
  induction m as [|m IH]; intros Nn H Hd H0 i Hi.
  - apply Hd. lia.
  - assert (HD : forall i, (i < Nn + m)%nat -> H (S i) - H i = 0).
    { apply (IH Nn (fun i => H (S i) - H i)).
      - intros j Hj. rewrite diffR_commute. apply Hd. exact Hj.
      - intros i0 Hi0. rewrite !H0 by lia. ring. }
    clear Hd. induction i as [|i IHi].
    + apply H0. lia.
    + specialize (HD i ltac:(lia)). rewrite IHi in HD by lia. lra.
Qed.

End Poly.

Fixpoint sumZ (m : nat) (F : nat -> Z) : Z :=
  match m with
  | O => 0%Z
  | S m' => (sumZ m' F + F m')%Z
  end.

Lemma sumR_IZR : forall m F G, (forall k, (k < m)%nat -> F k = IZR (G k)) ->
  sumR m F = IZR (sumZ m G).
Proof.
  induction m as [|m IH]; intros F G H; [reflexivity|].
  rewrite sumR_S. cbn [sumZ]. rewrite plus_IZR.
  rewrite (IH F G) by (intros k Hk; apply H; lia). rewrite (H m) by lia.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The math answer                                                     *)
(* ------------------------------------------------------------------ *)

(* row q of the table has a non-zero entry *)
Definition rownz (g : nat -> Z) (N0 q : nat) : Prop :=
  exists j, (j + q < N0)%nat /\ diffZ q g j <> 0%Z.

Definition DInv (g : nat -> Z) (N0 r dn : nat) : Prop :=
  (dn <= r)%nat /\ (dn = 0%nat \/ rownz g N0 dn) /\
  (forall q, (dn < q <= r)%nat -> ~ rownz g N0 q).

Definition wsum (g : nat -> Z) (N0 dn : nat) : Z :=
  sumZ (S dn) (fun q => diffZ q g (N0 - 1 - q)).

Lemma not_rownz : forall g N0 q, ~ rownz g N0 q ->
  forall j, (j + q < N0)%nat -> diffZ q g j = 0%Z.
Proof.
  intros g N0 q H j Hj. destruct (Z.eq_dec (diffZ q g j) 0) as [E | E]; [exact E|].
  exfalso. apply H. exists j. auto.
Qed.

Lemma math_main : forall (v : list Z) (dn : nat),
  (1 <= List.length v)%nat ->
  DInv (fun j => nth j v 0%Z) (List.length v) (List.length v - 1) dn ->
  ada_spec v (N.of_nat dn, wsum (fun j => nth j v 0%Z) (List.length v) dn).
Proof.
  intros v dn Hn [P1 [P2 P3]].
  set (g := fun j => nth j v 0%Z) in *.
  set (N0 := List.length v) in *.
  unfold ada_spec. intros x0 h Hh.
  assert (Hh0 : h <> 0%R) by lra.
  (* produces, in terms of Fc *)
  assert (Hprod_iff : forall c, produces c x0 h v <->
            forall j, (j < N0)%nat -> Fc x0 h c j = IZR (g j)).
  { intros c. unfold produces, Fc. reflexivity. }
  (* a producing polynomial with at most k coefficients kills row k *)
  assert (Hkill : forall c k j, produces c x0 h v -> (List.length c <= k)%nat ->
            (j + k < N0)%nat -> diffZ k g j = 0%Z).
  { intros c k j Hp Hc Hj. apply eq_IZR. rewrite <- diffR_IZR.
    rewrite (diffR_local k (fun i => IZR (g i)) (Fc x0 h c) j).
    - apply diffR_poly. exact Hc.
    - intros i Hi. symmetry. apply Hprod_iff; [exact Hp | lia]. }
  split; [split|].
  - (* existence *)
    set (I := interp x0 h (fun i => IZR (g i)) (S dn)).
    exists (I ++ repeat 0%R (S dn - List.length I)).
    split.
    + unfold len. rewrite length_app, repeat_length.
      pose proof (interp_len x0 h (fun i => IZR (g i)) (S dn)). fold I in H. lia.
    + apply Hprod_iff. intros j Hj. unfold Fc. rewrite pad_eval. fold (Fc x0 h I j).
      assert (HZ : forall i, (i < (N0 - S dn) + S dn)%nat ->
                (Fc x0 h I i - IZR (g i))%R = 0%R).
      { apply propagate.
        - intros j0 Hj0. rewrite diffR_sub, diffR_IZR, diffR_poly
            by (apply interp_len).
          rewrite (not_rownz g N0 (S dn)); [lra | | lia].
          apply P3. lia.
        - intros i Hi. unfold Fc, I. rewrite interp_ok by assumption. lra. }
      specialize (HZ j ltac:(lia)). lra.
  - (* minimality *)
    intros d' [c [Hlen Hp]]. unfold len in Hlen.
    destruct (Nat.le_gt_cases (S dn) (List.length c)) as [Hc | Hc]; [lia|].
    exfalso. destruct P2 as [P2 | [j [Hj Hnz]]]; [lia|].
    apply Hnz. apply (Hkill c dn j Hp); lia.
  - (* the value at the next node *)
    intros c Hlen Hp. unfold len in Hlen.
    assert (Hc : List.length c = S dn) by lia.
    replace (INR (List.length v)) with (INR (S (N0 - 1))) by (f_equal; unfold N0; lia).
    fold (Fc x0 h c (S (N0 - 1))).
    rewrite (newton (Fc x0 h c) (N0 - 1) dn) by lia.
    rewrite diffR_poly by lia. rewrite Rplus_0_r.
    unfold wsum. apply sumR_IZR. intros k Hk.
    rewrite <- diffR_IZR. apply diffR_local.
    intros i Hi. apply Hprod_iff; [exact Hp | lia].
Qed.

(* ------------------------------------------------------------------ *)
(* Bounds                                                              *)
(* ------------------------------------------------------------------ *)

Lemma diffZ_bound : forall (g : nat -> Z) M,
  (forall j, Z.abs (g j) <= M) ->
  forall k j, Z.abs (diffZ k g j) <= 2 ^ Z.of_nat k * M.
Proof.
  intros g M Hg k. induction k as [|k IH]; intros j.
  - cbn [diffZ]. change (Z.of_nat 0) with 0. rewrite Z.pow_0_r, Z.mul_1_l. apply Hg.
  - rewrite diffZ_S. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (IH (S j)). pose proof (IH j). lia.
Qed.

Lemma diffZ_small : forall (v : list Z),
  Forall (fun x => -2000000 <= x <= 2000000) v ->
  forall k j, (k <= 9)%nat -> Z.abs (diffZ k (fun j => nth j v 0) j) <= 1024000000.
Proof.
  intros v Hv k j Hk.
  assert (Hg : forall j, Z.abs (nth j v 0) <= 2000000).
  { intros j0. destruct (Nat.lt_ge_cases j0 (List.length v)) as [L | L].
    - rewrite Forall_forall in Hv. specialize (Hv _ (nth_In v 0 L)). lia.
    - rewrite nth_overflow by exact L. lia. }
  pose proof (diffZ_bound _ _ Hg k j) as B.
  assert (2 ^ Z.of_nat k <= 2 ^ 9).
  { apply Z.pow_le_mono_r; lia. }
  assert (0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  lia.
Qed.

Lemma sumZ_bound : forall m F B, 0 <= B ->
  (forall k, (k < m)%nat -> Z.abs (F k) <= B) ->
  Z.abs (sumZ m F) <= Z.of_nat m * B.
Proof.
  induction m as [|m IH]; intros F B HB H; [cbn; lia|].
  cbn [sumZ]. pose proof (IH F B HB ltac:(intros; apply H; lia)).
  pose proof (H m ltac:(lia)). lia.
Qed.

Lemma mod_zero_small : forall D, - wB < D < wB -> D mod wB = 0 -> D = 0.
Proof. intros D HD H. rewrite wB_val in *. Z.to_euclidean_division_equations. lia. Qed.

(* ------------------------------------------------------------------ *)
(* Loop specifications                                                 *)
(* ------------------------------------------------------------------ *)

Lemma row_loop_spec : forall (g : nat -> Z) (N0 r : nat) (n m : int),
  (φ n) = Z.of_nat N0 -> (φ m) = Z.of_nat (N0 - 1 - r) -> (r + 1 < N0)%nat ->
  (N0 <= 10)%nat ->
  (forall k j, (k < N0)%nat -> Z.abs (diffZ k g j) <= 1024000000) ->
  forall z (j : int) (t : array int) (nz : bool) (H : Acc (Zwf 0) (gap m j)),
  gap m j = z -> (φ j) <= (φ m) -> PArray.length t = n ->
  (forall i : int, (φ i) < (φ j) ->
     (φ (t.[i])) = diffZ (S r) g (Z.to_nat (φ i)) mod wB) ->
  (forall i : int, (φ j) <= (φ i) < (φ n) ->
     (φ (t.[i])) = diffZ (Nat.min r (N0 - 1 - Z.to_nat (φ i))) g (Z.to_nat (φ i)) mod wB) ->
  (nz = true <-> exists i, (i < Z.to_nat (φ j))%nat /\ diffZ (S r) g i <> 0) ->
  PArray.length (fst (row_loop m j t nz H)) = n /\
  (forall i : int, (φ i) < (φ n) ->
     (φ ((fst (row_loop m j t nz H)).[i]))
     = diffZ (Nat.min (S r) (N0 - 1 - Z.to_nat (φ i))) g (Z.to_nat (φ i)) mod wB) /\
  (snd (row_loop m j t nz H) = true <-> rownz g N0 (S r)).
Proof.
  intros g N0 r n m Hn Hm Hr HN Hb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j t nz H Hz Hjm Hlen Ha Hbb Hnz.
  rewrite row_loop_eq.
  destruct (bdec (j <? m)%uint63) as [Hj | Hj].
  - pose proof Hj as Hj'. rewrite ltb_spec in Hj'.
    pose proof (to_Z_bounded j) as Bj.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (Nj1 : Z.to_nat (φ (j + 1)) = S (Z.to_nat (φ j))) by lia.
    set (jj := Z.to_nat (φ j)) in *.
    assert (Ejj : (φ j) = Z.of_nat jj) by (unfold jj; lia).
    assert (Hjn : (j <? PArray.length t)%uint63 = true)
      by (rewrite ltb_spec, Hlen; lia).
    (* the new cell *)
    assert (Hx : (φ (t.[j + 1] - t.[j]))%uint63 = diffZ (S r) g jj mod wB).
    { rewrite sub_spec.
      rewrite (Hbb (j + 1)%uint63) by lia. rewrite (Hbb j) by lia.
      rewrite Nj1. fold jj.
      replace (Nat.min r (N0 - 1 - S jj)) with r by lia.
      replace (Nat.min r (N0 - 1 - jj)) with r by lia.
      rewrite diffZ_S. symmetry. apply Zminus_mod. }
    assert (HbD : Z.abs (diffZ (S r) g jj) <= 1024000000) by (apply Hb; lia).
    cbv zeta.
    eapply IH; [ | reflexivity | lia | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hj.
    + rewrite alength_set. exact Hlen.
    + intros i Hi. rewrite Hj1 in Hi.
      destruct (Z.eq_dec (φ i) (φ j)) as [E | E].
      * assert (i = j) by (apply to_Z_inj; exact E). subst i.
        rewrite aget_set_same by exact Hjn. rewrite Hx. reflexivity.
      * rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity).
        apply Ha. lia.
    + intros i Hi. rewrite Hj1 in Hi.
      rewrite aget_set_other by (intro F; subst i; lia).
      apply Hbb. lia.
    + rewrite Nj1.
      destruct ((t.[j + 1] - t.[j])%uint63 =? 0)%uint63 eqn:Ex.
      * rewrite eqb_spec in Ex. rewrite Ex in Hx. change (φ 0) with 0%Z in Hx.
        assert (HD0 : diffZ (S r) g jj = 0%Z).
        { apply mod_zero_small; [rewrite wB_val; lia | auto]. }
        cbn [negb]. rewrite Bool.orb_false_r. rewrite Hnz.
        split; intros [i [Hi1 Hi2]]; exists i; (split; [|exact Hi2]).
        -- lia.
        -- destruct (Nat.eq_dec i jj); [subst; contradiction | lia].
      * rewrite eqb_false_spec in Ex. cbn [negb]. rewrite Bool.orb_true_r.
        split; [intros _ | reflexivity].
        exists jj. split; [lia|]. intro E0. apply Ex.
        apply to_Z_inj. rewrite Hx, E0. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj.
    assert (Ejm : (φ j) = (φ m)) by lia.
    cbn [fst snd]. split; [exact Hlen|]. split.
    + intros i Hi. pose proof (to_Z_bounded i).
      destruct (Z_lt_le_dec (φ i) (φ j)) as [L | L].
      * rewrite Ha by exact L.
        replace (Nat.min (S r) (N0 - 1 - Z.to_nat (φ i))) with (S r) by lia.
        reflexivity.
      * rewrite Hbb by lia.
        replace (Nat.min (S r) (N0 - 1 - Z.to_nat (φ i)))
          with (Nat.min r (N0 - 1 - Z.to_nat (φ i))) by lia.
        reflexivity.
    + rewrite Hnz. unfold rownz.
      split; intros [i [Hi1 Hi2]]; exists i; split; auto; lia.
Qed.

Lemma rows_loop_spec : forall (g : nat -> Z) (N0 : nat) (n : int),
  (φ n) = Z.of_nat N0 -> (2 <= N0 <= 10)%nat ->
  (forall k j, (k < N0)%nat -> Z.abs (diffZ k g j) <= 1024000000) ->
  forall z (k : int) (t : array int) (d : int) (H : Acc (Zwf 0) (gap n k)),
  gap n k = z -> 1 <= (φ k) <= (φ n) -> PArray.length t = n ->
  (forall i : int, (φ i) < (φ n) ->
     (φ (t.[i])) = diffZ (Nat.min (Z.to_nat (φ k) - 1) (N0 - 1 - Z.to_nat (φ i))) g
                 (Z.to_nat (φ i)) mod wB) ->
  DInv g N0 (Z.to_nat (φ k) - 1) (Z.to_nat (φ d)) ->
  PArray.length (fst (rows_loop n k t d H)) = n /\
  (forall i : int, (φ i) < (φ n) ->
     (φ ((fst (rows_loop n k t d H)).[i]))
     = diffZ (N0 - 1 - Z.to_nat (φ i)) g (Z.to_nat (φ i)) mod wB) /\
  DInv g N0 (N0 - 1) (Z.to_nat (φ (snd (rows_loop n k t d H)))).
Proof.
  intros g N0 n Hn HN Hb z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k t d H Hz Hk Hlen Ht Hd.
  rewrite rows_loop_eq.
  destruct (bdec (k <? n)%uint63) as [Hkn | Hkn].
  - pose proof Hkn as Hkn'. rewrite ltb_spec in Hkn'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    assert (Hnk : (φ (n - k)) = ((φ n) - (φ k))%Z) by sia.
    set (r := (Z.to_nat (φ k) - 1)%nat) in *.
    assert (Er : (φ k) = Z.of_nat (S r)) by (unfold r; lia).
    cbv zeta.
    destruct (row_loop_spec g N0 r n (n - k) Hn ltac:(rewrite Hnk; lia)
                ltac:(lia) ltac:(lia) Hb _ 0 t false
                (Zwf_well_founded 0 (gap (n - k) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; lia) Hlen
                ltac:(intros i Hi; change (φ 0) with 0%Z in Hi;
                      pose proof (to_Z_bounded i); lia)
                ltac:(intros i Hi; apply Ht; lia)
                ltac:(change (φ 0) with 0%Z; cbn;
                      split; [discriminate | intros [i [Hi _]]; lia]))
      as [Rl [Rt Rnz]].
    eapply IH; [ | reflexivity | lia | exact Rl | | ].
    + rewrite <- Hz. apply dec_step. exact Hkn.
    + intros i Hi. rewrite Rt by exact Hi.
      replace (Z.to_nat (φ (k + 1)) - 1)%nat with (S r) by lia. reflexivity.
    + replace (Z.to_nat (φ (k + 1)) - 1)%nat with (S r) by lia.
      destruct Hd as [D1 [D2 D3]].
      destruct (snd (row_loop (n - k) 0 t false (Zwf_well_founded 0 (gap (n - k) 0))))
        eqn:Es.
      * replace (Z.to_nat (φ k)) with (S r) by lia.
        split; [lia|]. split.
        -- right. apply Rnz. reflexivity.
        -- intros q Hq. lia.
      * split; [lia|]. split; [exact D2|].
        intros q Hq. destruct (Nat.eq_dec q (S r)) as [E | E].
        -- subst q. intro F. apply Rnz in F. discriminate.
        -- apply D3. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hkn.
    assert (Ekn : (φ k) = (φ n)) by lia.
    cbn [fst snd]. split; [exact Hlen|]. split.
    + intros i Hi. rewrite Ht by exact Hi.
      replace (Nat.min (Z.to_nat (φ k) - 1) (N0 - 1 - Z.to_nat (φ i)))
        with (N0 - 1 - Z.to_nat (φ i))%nat by lia.
      reflexivity.
    + replace (N0 - 1)%nat with (Z.to_nat (φ k) - 1)%nat by lia. exact Hd.
Qed.

Lemma sum_loop_spec : forall (T : nat -> Z) (t : array int) (top e : int),
  (forall k : int, (φ k) < (φ e) -> (φ (t.[(top - k)%uint63])) = T (Z.to_nat (φ k)) mod wB) ->
  forall z (k acc : int) (H : Acc (Zwf 0) (gap e k)),
  gap e k = z -> 0 <= (φ k) <= (φ e) ->
  (φ acc) = sumZ (Z.to_nat (φ k)) T mod wB ->
  (φ (sum_loop t top e k acc H)) = sumZ (Z.to_nat (φ e)) T mod wB.
Proof.
  intros T t top e Ht z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k acc H Hz Hk Hacc.
  rewrite sum_loop_eq.
  destruct (bdec (k <? e)%uint63) as [Hke | Hke].
  - pose proof Hke as Hke'. rewrite ltb_spec in Hke'.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | ].
    + rewrite <- Hz. apply dec_step. exact Hke.
    + rewrite add_spec, Hacc, Ht by exact Hke'.
      replace (Z.to_nat (φ (k + 1))) with (S (Z.to_nat (φ k))) by lia.
      cbn [sumZ]. rewrite <- Zplus_mod. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hke.
    replace (φ e) with (φ k) by lia. exact Hacc.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

(* Reading an in-bounds cell of an array representing v. *)
Lemma repr_get : forall (x : array sint) (v : list Z), repr x v ->
  forall i : int, ((φ i) < Z.of_nat (List.length v))%Z ->
  Sint63.to_Z x.[i] = nth (Z.to_nat (φ i)) v 0%Z.
Proof.
  intros x v [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_sint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr. rewrite Hr.
  symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma repr_length : forall (x : array sint) (v : list Z), repr x v ->
  (φ (PArray.length x)) = Z.of_nat (List.length v).
Proof. intros x v [Hl _]. symmetry. exact Hl. Qed.

Lemma sint_mod : forall w : int, (Sint63.to_Z w mod wB)%Z = (φ w).
Proof. intros w. apply Sint63.to_Z_mod_Uint63to_Z. Qed.

Lemma ada_impl_correct : forall (v : list Z) (x : array sint),
  valid_input v -> repr x v ->
  exists o : N * Z, repr (ada_impl x) o /\ ada_spec v o.
Proof.
  intros v x Hv Hx.
  destruct Hv as [Hvn Hvv _]. unfold len in Hvn.
  set (N0 := List.length v) in *.
  set (g := fun j => nth j v 0%Z).
  pose proof (repr_length x v Hx) as Lx.
  assert (Hb : forall k j, (k < N0)%nat -> Z.abs (diffZ k g j) <= 1024000000).
  { intros k j Hk. apply diffZ_small; [exact Hvv | lia]. }
  set (n := PArray.length x) in *.
  assert (Hcl : PArray.length (acopy x) = n) by (unfold n; exact (acopy_length x)).
  destruct (rows_loop_spec g N0 n Lx ltac:(lia) Hb _ 1 (acopy x) 0
              (Zwf_well_founded 0 (gap n 1)) eq_refl
              ltac:(change (φ 1) with 1%Z; lia) Hcl)
    as [Rl [Rt Rd]].
  { intros i Hi.
    rewrite acopy_get.
    change (Z.to_nat (φ 1) - 1)%nat with 0%nat. rewrite Nat.min_0_l. cbn [diffZ].
    unfold g. rewrite <- (repr_get x v Hx i) by lia. symmetry. apply sint_mod. }
  { change (Z.to_nat (φ 1) - 1)%nat with 0%nat. change (Z.to_nat (φ 0)) with 0%nat.
    split; [lia|]. split; [left; reflexivity|]. intros q Hq. lia. }
  destruct (rows_loop n 1 (acopy x) 0 (Zwf_well_founded 0 (gap n 1)))
    as [tf d] eqn:E.
  cbn [fst snd] in Rl, Rt, Rd.
  exists (N.of_nat (Z.to_nat (φ d)), wsum g N0 (Z.to_nat (φ d))).
  split.
  2: { apply math_main; [lia | exact Rd]. }
  destruct Rd as [D1 _].
  pose proof (to_Z_bounded d) as Bd.
  assert (Ed : (φ d) = Z.of_nat (Z.to_nat (φ d))) by lia.
  set (dn := Z.to_nat (φ d)) in *.
  assert (He : (φ (d + 1))%uint63 = ((φ d) + 1)%Z) by sia.
  set (T := fun q => diffZ q g (N0 - 1 - q)).
  assert (Hs := sum_loop_spec T tf (n - 1) (d + 1)).
  specialize (Hs ltac:(intros k Hk; pose proof (to_Z_bounded k);
                        assert (Hi : (φ (n - 1 - k))%uint63 = (Z.of_nat N0 - 1 - (φ k))%Z) by sia;
                        rewrite Rt by lia;
                        replace (Z.to_nat (φ (n - 1 - k))%uint63) with (N0 - 1 - Z.to_nat (φ k))%nat by lia;
                        replace (N0 - 1 - (N0 - 1 - Z.to_nat (φ k)))%nat with (Z.to_nat (φ k)) by lia;
                        reflexivity)
                  _ 0%uint63 0%uint63 (Zwf_well_founded 0 (gap (d + 1) 0)) eq_refl
                  ltac:(change (φ 0) with 0%Z; lia)
                  ltac:(change (φ 0) with 0%Z; reflexivity)).
  replace (Z.to_nat (φ (d + 1))%uint63) with (S dn) in Hs by lia.
  fold (wsum g N0 dn) in Hs.
  unfold ada_impl.
  lazymatch goal with |- context [rows_loop ?a ?b ?c ?e ?f] =>
    replace (rows_loop a b c e f) with (tf, d) by (symmetry; exact E) end.
  cbv beta iota.
  split; cbn [fst snd].
  - unfold repr, repr_uint. lia.
  - unfold repr, repr_sint.
    assert (HW : Z.abs (wsum g N0 dn) <= 10 * 1024000000).
    { unfold wsum. pose proof (sumZ_bound (S dn) T 1024000000 ltac:(lia)
                     ltac:(intros q Hq; unfold T; apply Hb; lia)) as HT.
      unfold T in HT. lia. }
    transitivity (Sint63.to_Z (sum_loop tf (n - 1) (d + 1) 0 0
                    (Zwf_well_founded 0 (gap (d + 1) 0)))); [reflexivity|].
    rewrite Sint63.to_Z_cmodwB, Hs, Sint63.cmod_mod.
    apply Sint63.cmod_small.
    rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z.
    lia.
Qed.

Definition ada_correct : forall (v : list Z) (x : array sint),
  valid_input v -> repr x v ->
  exists o : N * Z, repr (ada x) o /\ ada_spec v o
  := ada_impl_correct.
