(* Correctness proofs for bitwise_implem.v. *)
From Bitwise.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Permutation.
Import ListNotations.

Open Scope Z_scope.
Unset Lia Cache.

From Bitwise Require Export bitwise_implem.
Open Scope Z_scope.


(* ================================================================== *)
(* Part 1. Math side: the doubled circle, windows, next-cut pointers   *)
(* ================================================================== *)

Lemma firstn_add_gen : forall {A} (p q : nat) (l : list A),
  firstn (p + q) l = firstn p l ++ firstn q (skipn p l).
Proof.
  intros A p. induction p as [| p IH]; intros q l; [reflexivity|].
  destruct l as [| x l]; simpl.
  - destruct q; reflexivity.
  - f_equal. apply IH.
Qed.

Section Circle.

Variable a : list N.
Variable k : N.

Definition nZ : Z := Z.of_nat (List.length a).
Definition KK : nat := N.to_nat k.

(* the value at position p of the circle unrolled *)
Definition d (p : Z) : N := nth (Z.to_nat (p mod nZ)) a 0%N.
Definition dd : list N := a ++ a.
(* the window [x, y) of the doubled circle *)
Definition sec (x y : Z) : list N :=
  firstn (Z.to_nat (y - x)) (skipn (Z.to_nat x) dd).

(* every bit of m occurs in some value of positions [x, y) *)
Definition good (m : N) (x y : Z) : Prop :=
  forall i, N.testbit m i = true ->
    exists p, x <= p < y /\ N.testbit (d p) i = true.

Definition covers (m : N) (s : list N) : Prop :=
  forall i, N.testbit m i = true -> exists v, In v s /\ N.testbit v i = true.

Definition feasible (m : N) : Prop :=
  exists secs, division a k secs /\ Forall (covers m) secs.

Hypothesis Hn : 1 <= nZ.

Lemma good_mono : forall m x x' y y',
  x <= x' -> y' <= y -> good m x' y' -> good m x y.
Proof.
  intros m x x' y y' H1 H2 G i Hi. destruct (G i Hi) as (p & Hp & Hb).
  exists p. split; [lia | exact Hb].
Qed.

Lemma d_shift : forall p, d (p + nZ) = d p.
Proof.
  intros p. unfold d. replace (p + nZ) with (p + 1 * nZ) by ring.
  rewrite Z_mod_plus_full. reflexivity.
Qed.

Lemma good_shift : forall m x y, good m x y -> good m (x + nZ) (y + nZ).
Proof.
  intros m x y G i Hi. destruct (G i Hi) as (p & Hp & Hb).
  exists (p + nZ). rewrite d_shift. split; [lia | exact Hb].
Qed.

Lemma good_unshift : forall m x y, good m x y -> good m (x - nZ) (y - nZ).
Proof.
  intros m x y G i Hi. destruct (G i Hi) as (p & Hp & Hb).
  exists (p - nZ). replace (d (p - nZ)) with (d p).
  - split; [lia | exact Hb].
  - rewrite <- (d_shift (p - nZ)). f_equal. ring.
Qed.

Lemma good_full : forall m x, good m x (x + nZ) -> good m 0 nZ.
Proof.
  intros m x G i Hi. destruct (G i Hi) as (p & Hp & Hb).
  exists (p mod nZ). split; [apply Z.mod_pos_bound; lia|].
  unfold d in *. rewrite Z.mod_mod by lia. exact Hb.
Qed.

Lemma length_dd : List.length dd = (2 * List.length a)%nat.
Proof. unfold dd. rewrite length_app. lia. Qed.

Lemma nth_dd : forall p, 0 <= p < 2 * nZ -> nth (Z.to_nat p) dd 0%N = d p.
Proof.
  intros p Hp. unfold dd, d, nZ in *.
  destruct (Z.ltb_spec p (Z.of_nat (List.length a))).
  - rewrite app_nth1 by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite app_nth2 by lia.
    replace (p mod Z.of_nat (List.length a)) with (p - Z.of_nat (List.length a)).
    + f_equal. lia.
    + replace p with ((p - Z.of_nat (List.length a)) + 1 * Z.of_nat (List.length a)) at 2 by ring.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma sec_length : forall x y, 0 <= x <= y -> y <= 2 * nZ ->
  List.length (sec x y) = Z.to_nat (y - x).
Proof.
  intros x y H1 H2. unfold sec. rewrite length_firstn, length_skipn, length_dd.
  unfold nZ in *. lia.
Qed.

Lemma sec_nth : forall x y j, 0 <= x -> 0 <= j -> x + j < y -> y <= 2 * nZ ->
  nth (Z.to_nat j) (sec x y) 0%N = d (x + j).
Proof.
  intros x y j H1 H2 H3 H4. unfold sec. rewrite nth_firstn.
  destruct (Nat.ltb_spec (Z.to_nat j) (Z.to_nat (y - x))); [|lia].
  rewrite nth_skipn. rewrite <- nth_dd by lia. f_equal. lia.
Qed.

Lemma covers_sec : forall m x y, 0 <= x <= y -> y <= 2 * nZ ->
  (covers m (sec x y) <-> good m x y).
Proof.
  intros m x y H1 H2. split.
  - intros C i Hi. destruct (C i Hi) as (v & Hv & Hb).
    destruct (In_nth _ _ 0%N Hv) as (j & Hj & Ej).
    rewrite sec_length in Hj by lia.
    exists (x + Z.of_nat j). split; [lia|].
    rewrite <- sec_nth with (y := y) by lia.
    rewrite Nat2Z.id. rewrite Ej. exact Hb.
  - intros G i Hi. destruct (G i Hi) as (p & Hp & Hb).
    exists (d p). split; [|exact Hb].
    replace (d p) with (nth (Z.to_nat (p - x)) (sec x y) 0%N).
    + apply nth_In. rewrite sec_length by lia. lia.
    + rewrite sec_nth by lia. f_equal. ring.
Qed.

Lemma sec_app : forall x y z, 0 <= x <= y -> y <= z ->
  sec x y ++ sec y z = sec x z.
Proof.
  intros x y z H1 H2. unfold sec.
  replace (Z.to_nat (z - x)) with (Z.to_nat (y - x) + Z.to_nat (z - y))%nat by lia.
  rewrite firstn_add_gen, skipn_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Lemma sec_split : forall s1 rest x e, 0 <= x <= e -> e <= 2 * nZ ->
  s1 ++ rest = sec x e ->
  x + Z.of_nat (List.length s1) <= e /\
  s1 = sec x (x + Z.of_nat (List.length s1)) /\
  rest = sec (x + Z.of_nat (List.length s1)) e.
Proof.
  intros s1 rest x e H1 H2 E.
  assert (L : List.length (s1 ++ rest) = Z.to_nat (e - x))
    by (rewrite E; apply sec_length; lia).
  rewrite length_app in L.
  split; [lia|]. split.
  - assert (E1 : s1 = firstn (List.length s1) (s1 ++ rest)).
    { rewrite firstn_app, Nat.sub_diag, firstn_all. simpl. rewrite app_nil_r. reflexivity. }
    rewrite E1 at 1. rewrite E. unfold sec. rewrite firstn_firstn. f_equal. lia.
  - assert (E1 : rest = skipn (List.length s1) (s1 ++ rest)).
    { rewrite skipn_app, Nat.sub_diag, skipn_all. reflexivity. }
    rewrite E1. rewrite E. unfold sec. rewrite skipn_firstn_comm, skipn_skipn.
    f_equal; [lia|]. f_equal. lia.
Qed.

Lemma rotate_sec : forall r, (r < List.length a)%nat ->
  rotate r a = sec (Z.of_nat r) (Z.of_nat r + nZ).
Proof.
  intros r Hr. unfold sec, dd, rotate, nZ.
  rewrite Nat2Z.id. replace (Z.to_nat (Z.of_nat r + Z.of_nat (List.length a) - Z.of_nat r))
    with (List.length a) by lia.
  rewrite skipn_app. replace (r - List.length a)%nat with 0%nat by lia. simpl.
  rewrite firstn_app. rewrite length_skipn.
  rewrite (firstn_all2 (skipn r a)) by (rewrite length_skipn; lia).
  f_equal. f_equal. lia.
Qed.

(* next-cut pointers for mask m : F x is the end of the shortest window
   from x covering m, the sentinel 2n+1 when there is none *)
Definition ptr_spec (m : N) (F : Z -> Z) : Prop :=
  F (2 * nZ + 1) = 2 * nZ + 1 /\
  forall x, 0 <= x <= 2 * nZ ->
    x < F x <= 2 * nZ + 1 /\
    (F x <= 2 * nZ -> good m x (F x)) /\
    (forall y, x < y <= 2 * nZ -> good m x y -> F x <= y).

Fixpoint iter (F : Z -> Z) (j : nat) (x : Z) : Z :=
  match j with O => x | S j => iter F j (F x) end.

Lemma iter_S' : forall F j x, iter F (S j) x = F (iter F j x).
Proof.
  intros F j. induction j as [| j IH]; intros x; [reflexivity|].
  change (iter F (S (S j)) x) with (iter F (S j) (F x)). rewrite IH. reflexivity.
Qed.

Lemma iter_add : forall F p q x, iter F (p + q) x = iter F q (iter F p x).
Proof.
  intros F p. induction p as [| p IH]; intros q x; [reflexivity|].
  simpl. apply IH.
Qed.

Section Ptr.
Variable m : N.
Variable F : Z -> Z.
Hypothesis HF : ptr_spec m F.

Lemma F_range : forall x, 0 <= x <= 2 * nZ + 1 -> x <= F x <= 2 * nZ + 1.
Proof.
  intros x Hx. destruct HF as [H0 H1].
  destruct (Z.eq_dec x (2 * nZ + 1)) as [E | E].
  - subst x. lia.
  - destruct (H1 x ltac:(lia)) as [H _]. lia.
Qed.

Lemma F_lt : forall x, 0 <= x <= 2 * nZ -> x < F x.
Proof. intros x Hx. destruct HF as [_ H1]. destruct (H1 x Hx) as [H _]. lia. Qed.

Lemma F_mono : forall x y, 0 <= x <= y -> y <= 2 * nZ + 1 -> F x <= F y.
Proof.
  intros x y H1 H2. destruct HF as [H0 Hc].
  destruct (Z.eq_dec y (2 * nZ + 1)) as [E | E].
  - subst y. rewrite H0. pose proof (F_range x ltac:(lia)). lia.
  - destruct (Hc y ltac:(lia)) as (Hy & Gy & My).
    destruct (Z.eq_dec (F y) (2 * nZ + 1)) as [E' | E'].
    + rewrite E'. pose proof (F_range x ltac:(lia)). lia.
    + destruct (Hc x ltac:(lia)) as (_ & _ & Mx).
      apply Mx; [lia|]. eapply good_mono; [| | apply Gy; lia]; lia.
Qed.

Lemma iter_range : forall j x, 0 <= x <= 2 * nZ + 1 ->
  x <= iter F j x <= 2 * nZ + 1.
Proof.
  intros j. induction j as [| j IH]; intros x Hx; cbn [iter]; [lia|].
  pose proof (F_range x Hx). pose proof (IH (F x) ltac:(lia)). lia.
Qed.

Lemma iter_mono : forall j x y, 0 <= x <= y -> y <= 2 * nZ + 1 ->
  iter F j x <= iter F j y.
Proof.
  intros j. induction j as [| j IH]; intros x y H1 H2; cbn [iter]; [lia|].
  pose proof (F_range x ltac:(lia)). pose proof (F_range y ltac:(lia)).
  pose proof (F_mono x y H1 H2). apply IH; lia.
Qed.

Lemma iter_mono_j : forall j j' x, (j <= j')%nat -> 0 <= x <= 2 * nZ + 1 ->
  iter F j x <= iter F j' x.
Proof.
  intros j j' x Hj Hx. replace j' with (j + (j' - j))%nat by lia.
  rewrite iter_add. pose proof (iter_range j x Hx).
  apply iter_range. lia.
Qed.

(* ---- soundness: a short enough chain gives a division ---- *)

Fixpoint secs_from (j : nat) (x e : Z) : list (list N) :=
  match j with
  | O => []
  | S j' => match j' with
            | O => [sec x e]
            | S _ => sec x (F x) :: secs_from j' (F x) e
            end
  end.

Lemma secs_from_ok : forall j x e, (1 <= j)%nat -> 0 <= x <= 2 * nZ + 1 ->
  iter F j x <= e -> e <= 2 * nZ ->
  List.length (secs_from j x e) = j /\ concat (secs_from j x e) = sec x e /\
  Forall (fun s => s <> []) (secs_from j x e) /\
  Forall (covers m) (secs_from j x e).
Proof.
  intros j. induction j as [| j IH]; intros x e Hj Hx Hi He; [lia|].
  destruct HF as [H0 Hc].
  assert (Hx2 : x <= 2 * nZ).
  { destruct (Z.eq_dec x (2 * nZ + 1)) as [E|E]; [|lia].
    exfalso. subst x. pose proof (iter_range j (F (2 * nZ + 1))) as R.
    cbn [iter] in Hi. rewrite H0 in Hi, R. specialize (R ltac:(lia)). lia. }
  destruct (Hc x ltac:(lia)) as (Hfx & Gx & _).
  cbn [iter] in Hi. pose proof (iter_range j (F x) ltac:(lia)) as R.
  assert (Hfe : F x <= e) by lia.
  assert (Gx' : good m x (F x)) by (apply Gx; lia).
  destruct j as [| j].
  - simpl. split; [reflexivity|]. split; [apply app_nil_r|].
    split; constructor; try constructor.
    + intro E. pose proof (sec_length x e ltac:(lia) He) as L. rewrite E in L. simpl in L. lia.
    + apply covers_sec; [lia | exact He |]. eapply good_mono; [| | exact Gx']; lia.
  - destruct (IH (F x) e ltac:(lia) ltac:(lia) Hi He) as (L & C & NE & CV).
    change (secs_from (S (S j)) x e) with (sec x (F x) :: secs_from (S j) (F x) e).
    split; [cbn [List.length]; lia|]. split.
    + cbn [concat]. rewrite C. apply sec_app; lia.
    + split; constructor; auto.
      * intro E. pose proof (sec_length x (F x) ltac:(lia) ltac:(lia)) as L'.
        rewrite E in L'. simpl in L'. lia.
      * apply covers_sec; [lia | lia | exact Gx'].
Qed.

Lemma soundness : (1 <= KK)%nat -> forall s, 0 <= s < nZ ->
  iter F KK s <= s + nZ -> feasible m.
Proof.
  intros HK s Hs Hi.
  destruct (secs_from_ok KK s (s + nZ) HK ltac:(lia) Hi ltac:(lia))
    as (L & C & NE & CV).
  exists (secs_from KK s (s + nZ)). split; [|exact CV].
  split; [| split; [exact NE|]].
  - unfold len, KK in *. rewrite L. apply N2Nat.id.
  - exists (Z.to_nat s). split; [unfold nZ in Hs; lia|].
    rewrite rotate_sec by (unfold nZ in Hs; lia). rewrite C. f_equal; lia.
Qed.

(* ---- completeness: a division bounds the greedy chain ---- *)

Lemma compl : forall secs x e, 0 <= x <= e -> e <= 2 * nZ ->
  concat secs = sec x e -> Forall (fun s => s <> []) secs ->
  Forall (covers m) secs -> iter F (List.length secs) x <= e.
Proof.
  intros secs. induction secs as [| s1 rest IH]; intros x e H1 H2 C NE CV.
  - simpl. lia.
  - simpl in C. inversion NE as [| ? ? NE1 NE2]; subst.
    inversion CV as [| ? ? CV1 CV2]; subst.
    destruct (sec_split s1 (concat rest) x e H1 H2 C) as (Le & E1 & E2).
    set (l := Z.of_nat (List.length s1)) in *.
    assert (Hl : 1 <= l) by (unfold l; destruct s1; [congruence | simpl; lia]).
    rewrite E1 in CV1. apply covers_sec in CV1; [| lia | lia].
    destruct HF as [_ Hc]. destruct (Hc x ltac:(lia)) as (Hfx & _ & Mx).
    pose proof (Mx (x + l) ltac:(lia) CV1) as Hf.
    pose proof (IH (x + l) e ltac:(lia) H2 E2 NE2 CV2) as Hi.
    simpl. eapply Z.le_trans; [| exact Hi]. apply iter_mono; lia.
Qed.

Lemma completeness : feasible m ->
  exists s, 0 <= s < nZ /\ iter F KK s <= s + nZ.
Proof.
  intros (secs & (Hl & NE & r & Hr & C) & CV).
  exists (Z.of_nat r). split; [unfold nZ; lia|].
  rewrite rotate_sec in C by exact Hr.
  pose proof (compl secs (Z.of_nat r) (Z.of_nat r + nZ) ltac:(lia)
                ltac:(unfold nZ in *; lia) C NE CV) as H.
  unfold KK. unfold len in Hl. rewrite <- Hl, Nat2N.id. exact H.
Qed.

(* ---- restriction of the starts to [0, F 0] ---- *)

Lemma shift_down : forall x, nZ <= x <= 2 * nZ -> F x <= 2 * nZ ->
  F (x - nZ) <= F x - nZ.
Proof.
  intros x Hx Hf. destruct HF as [_ Hc].
  destruct (Hc x ltac:(lia)) as (Hfx & Gx & _).
  destruct (Hc (x - nZ) ltac:(lia)) as (_ & _ & M).
  apply M; [lia|]. apply good_unshift. apply Gx. exact Hf.
Qed.

Lemma iter_shift_down : forall j x, nZ <= x <= 2 * nZ + 1 ->
  iter F j x <= 2 * nZ -> iter F j (x - nZ) <= iter F j x - nZ.
Proof.
  intros j. induction j as [| j IH]; intros x Hx Hi; cbn [iter] in *; [lia|].
  pose proof (F_range x ltac:(lia)) as Rx.
  pose proof (iter_range j (F x) ltac:(lia)) as R.
  assert (Hx2 : x <= 2 * nZ).
  { destruct (Z.eq_dec x (2 * nZ + 1)) as [E|E]; [|lia].
    subst x. destruct HF as [H0 _]. rewrite H0 in R, Hi. lia. }
  pose proof (shift_down x ltac:(lia) ltac:(lia)) as Sd.
  pose proof (F_range (x - nZ) ltac:(lia)) as Rx'.
  apply Z.le_trans with (iter F j (F x - nZ)); [apply iter_mono; lia|].
  apply IH; lia.
Qed.

Lemma ivt : forall (g : nat -> Z) c K, g O < c -> c <= g K ->
  exists t, (t < K)%nat /\ g t < c /\ c <= g (S t).
Proof.
  intros g c K. induction K as [| K IH]; intros H0 HK; [lia|].
  destruct (Z.le_gt_cases c (g K)) as [E|E].
  - destruct (IH H0 E) as (t & Ht & H1 & H2). exists t. split; [lia | auto].
  - exists K. split; [lia | split; lia].
Qed.

Lemma restrict : (1 <= KK)%nat ->
  (exists s, 0 <= s < nZ /\ iter F KK s <= s + nZ) ->
  exists s, 0 <= s <= F 0 /\ s < nZ /\ iter F KK s <= s + nZ.
Proof.
  intros HK (s & Hs & Hi).
  destruct HF as [H0 Hc].
  (* F 0 <= n *)
  assert (HF0 : F 0 <= nZ).
  { destruct (Hc s ltac:(lia)) as (Hfs & Gs & _).
    pose proof (iter_mono_j 1 KK s HK ltac:(lia)) as I1. simpl in I1.
    assert (G : good m s (s + nZ)) by (eapply good_mono; [| | apply Gs]; lia).
    apply good_full in G.
    destruct (Hc 0 ltac:(lia)) as (_ & _ & M0). apply M0; [lia | exact G]. }
  destruct (Z.lt_ge_cases (iter F KK s) nZ) as [Ek | Ek].
  - exists 0. pose proof (F_range 0 ltac:(lia)).
    split; [lia|]. split; [lia|].
    pose proof (iter_mono KK 0 s ltac:(lia) ltac:(lia)). lia.
  - destruct (ivt (fun j => iter F j s) nZ KK ltac:(simpl; lia) Ek)
      as (t & Ht & Hlt & Hge).
    set (q := iter F (S t) s) in *.
    pose proof (iter_range t s ltac:(lia)) as Rt.
    assert (Hq : q = F (iter F t s)) by (unfold q; apply iter_S').
    (* q <= F n <= F 0 + n *)
    assert (Hup : F nZ <= F 0 + nZ).
    { destruct (Hc 0 ltac:(lia)) as (Hf0 & G0 & _).
      destruct (Hc nZ ltac:(lia)) as (_ & _ & Mn).
      apply Mn; [lia|]. replace nZ with (0 + nZ) at 1 by ring.
      apply good_shift. apply G0. lia. }
    pose proof (F_mono (iter F t s) nZ ltac:(lia) ltac:(lia)) as Hm.
    assert (HqK : q <= iter F KK s)
      by (unfold q; apply iter_mono_j; lia).
    exists (q - nZ). split; [lia|]. split; [lia|].
    set (r := (KK - S t)%nat).
    assert (EK : KK = (r + S t)%nat) by (unfold r; lia).
    rewrite EK, iter_add.
    assert (Eq : iter F r q = iter F KK s)
      by (unfold q; rewrite <- iter_add; f_equal; lia).
    pose proof (iter_shift_down r q ltac:(lia) ltac:(lia)) as Sd.
    rewrite Eq in Sd.
    pose proof (iter_range r (q - nZ) ltac:(lia)) as Rr.
    eapply Z.le_trans; [apply (iter_mono (S t) _ s); lia|].
    fold q. lia.
Qed.

Lemma feasible_iff : (1 <= KK)%nat ->
  (feasible m <-> exists s, 0 <= s <= Z.min (F 0) (nZ - 1) /\ iter F KK s <= s + nZ).
Proof.
  intros HK. split.
  - intros Hf. destruct (restrict HK (completeness Hf)) as (s & H1 & H2 & H3).
    exists s. split; [lia | exact H3].
  - intros (s & Hs & Hi). apply (soundness HK s); lia.
Qed.

End Ptr.

(* ---- the pointer cells, one position at a time ---- *)

Definition cellv (m : N) (x h : Z) : Prop :=
  x < h <= 2 * nZ + 1 /\ (h <= 2 * nZ -> good m x h) /\
  (forall y, x < y <= 2 * nZ -> good m x y -> h <= y).

(* g - 1 is the first position >= x holding bit b, g = 2n+1 if none *)
Definition nextb (b : N) (x g : Z) : Prop :=
  x < g <= 2 * nZ + 1 /\
  (g <= 2 * nZ -> x <= g - 1 /\ N.testbit (d (g - 1)) b = true) /\
  (forall p, x <= p < 2 * nZ -> N.testbit (d p) b = true -> g <= p + 1).

Lemma nextb_init : forall b, nextb b (2 * nZ) (2 * nZ + 1).
Proof. intros b. split; [lia|]. split; [lia|]. intros p Hp. lia. Qed.

Lemma nextb_step : forall b x g, 0 <= x -> x + 1 <= 2 * nZ ->
  nextb b (x + 1) g ->
  nextb b x (if N.testbit (d x) b then x + 1 else g).
Proof.
  intros b x g H0 H1 (Hg & Hb & Hm).
  destruct (N.testbit (d x) b) eqn:E.
  - split; [lia|]. split.
    + intros _. split; [lia|]. replace (x + 1 - 1) with x by ring. exact E.
    + intros p Hp _. lia.
  - split; [lia|]. split.
    + intros Hle. destruct (Hb Hle). split; [lia | auto].
    + intros p Hp Hbp. destruct (Z.eq_dec p x) as [Ep|Ep].
      * subst p. congruence.
      * apply Hm; [lia | exact Hbp].
Qed.

Lemma good_lor : forall A b x y,
  good (N.lor A (2 ^ b)) x y <->
  good A x y /\ exists p, x <= p < y /\ N.testbit (d p) b = true.
Proof.
  intros A b x y. split.
  - intros G. split.
    + intros i Hi. apply G. rewrite N.lor_spec, Hi. reflexivity.
    + apply G. rewrite N.lor_spec, N.pow2_bits_eqb, N.eqb_refl.
      apply Bool.orb_true_r.
  - intros [G (p & Hp & Hb)] i Hi. rewrite N.lor_spec, N.pow2_bits_eqb in Hi.
    destruct (N.testbit A i) eqn:EA.
    + apply G. exact EA.
    + simpl in Hi. apply N.eqb_eq in Hi. subst i. exists p. auto.
Qed.

Lemma cellv_max : forall A b x f g, 0 <= x ->
  cellv A x f -> nextb b x g -> cellv (N.lor A (2 ^ b)) x (Z.max f g).
Proof.
  intros A b x f g H0 (Hf & Gf & Mf) (Hg & Gg & Mg).
  split; [lia|]. split.
  - intros Hle. apply good_lor. split.
    + eapply good_mono; [| | apply Gf]; lia.
    + destruct (Gg ltac:(lia)) as [H1 H2]. exists (g - 1). split; [lia | exact H2].
  - intros y Hy G. apply good_lor in G. destruct G as [G (p & Hp & Hb)].
    pose proof (Mf y Hy G). pose proof (Mg p ltac:(lia) Hb). lia.
Qed.

Lemma cellv_end : forall m, cellv m (2 * nZ) (2 * nZ + 1).
Proof. intros m. split; [lia|]. split; [lia|]. intros y Hy. lia. Qed.

Lemma cellv_zero : forall x, cellv 0 x (x + 1) \/ x > 2 * nZ.
Proof.
  intros x. destruct (Z.le_gt_cases x (2 * nZ)); [left | right; lia].
  split; [lia|]. split.
  - intros _ i Hi. rewrite N.bits_0 in Hi. discriminate.
  - intros y Hy _. lia.
Qed.

(* ---- the greedy on the bits ---- *)

Definition sub (x y : N) : Prop :=
  forall i, N.testbit x i = true -> N.testbit y i = true.

Lemma sub_le : forall x y, sub x y -> (x <= y)%N.
Proof.
  intros x y H.
  assert (E : N.land x y = x).
  { apply N.bits_inj. intros i. rewrite N.land_spec.
    destruct (N.testbit x i) eqn:E; [rewrite (H i E)|]; reflexivity. }
  rewrite <- E. apply N.land_le_r.
Qed.

Lemma power_bits_gen : forall s acc i,
  N.testbit (fold_left N.lor s acc) i =
  (N.testbit acc i || existsb (fun v => N.testbit v i) s)%bool.
Proof.
  intros s. induction s as [| v s IH]; intros acc i; simpl.
  - rewrite Bool.orb_false_r. reflexivity.
  - rewrite IH, N.lor_spec. symmetry. apply Bool.orb_assoc.
Qed.

Lemma covers_power : forall m s, covers m s <-> sub m (power s).
Proof.
  intros m s. unfold covers, sub, power. split.
  - intros C i Hi. rewrite power_bits_gen, N.bits_0. simpl.
    apply existsb_exists. apply C. exact Hi.
  - intros S i Hi. specialize (S i Hi). rewrite power_bits_gen, N.bits_0 in S.
    simpl in S. apply existsb_exists in S. exact S.
Qed.

Lemma and_bits_gen : forall rest acc i,
  N.testbit (fold_left (fun acc t => N.land acc (power t)) rest acc) i =
  (N.testbit acc i && forallb (fun t => N.testbit (power t) i) rest)%bool.
Proof.
  intros rest. induction rest as [| t rest IH]; intros acc i; simpl.
  - rewrite Bool.andb_true_r. reflexivity.
  - rewrite IH, N.land_spec. symmetry. apply Bool.andb_assoc.
Qed.

Lemma and_bits : forall secs i, secs <> [] ->
  (N.testbit (and_powers secs) i = true <->
   forall s, In s secs -> N.testbit (power s) i = true).
Proof.
  intros secs i Hne. destruct secs as [| s0 rest]; [congruence|].
  unfold and_powers. rewrite and_bits_gen, Bool.andb_true_iff, forallb_forall.
  split.
  - intros [H1 H2] s [E | E]; [subst; exact H1 | apply H2; exact E].
  - intros H. split; [apply H; left; reflexivity|].
    intros s E. apply H. right. exact E.
Qed.

Definition Ginv (j A : N) : Prop :=
  (forall secs, division a k secs -> (and_powers secs / 2 ^ j <= A / 2 ^ j)%N) /\
  (A mod 2 ^ j = 0)%N /\ feasible A.

Lemma division_ne : forall secs, (1 <= k)%N -> division a k secs -> secs <> [].
Proof.
  intros secs Hk (Hl & _) E. subst secs. unfold len in Hl. simpl in Hl. lia.
Qed.

Lemma lor_add : forall A j, (A mod 2 ^ (j + 1) = 0)%N ->
  N.lor A (2 ^ j) = (A + 2 ^ j)%N.
Proof.
  intros A j H.
  assert (E : N.land A (2 ^ j) = 0%N).
  { apply N.bits_inj. intros i. rewrite N.land_spec, N.pow2_bits_eqb, N.bits_0.
    destruct (N.eqb_spec j i) as [Ei|Ei].
    - subst i. rewrite <- (N.mod_pow2_bits_low A (j + 1) j) by lia.
      rewrite H, N.bits_0. reflexivity.
    - apply Bool.andb_false_r. }
  rewrite N.add_nocarry_lxor by exact E. symmetry. apply N.lxor_lor. exact E.
Qed.

Lemma Ginv_step : forall j A, (1 <= k)%N -> Ginv (j + 1) A ->
  (feasible (N.lor A (2 ^ j)) -> Ginv j (N.lor A (2 ^ j))) /\
  (~ feasible (N.lor A (2 ^ j)) -> Ginv j A).
Proof.
  intros j A Hk (Hle & Hmod & Hfe).
  rewrite (lor_add A j Hmod).
  set (P := (2 ^ j)%N) in *.
  assert (HP : P <> 0%N) by (unfold P; apply N.pow_nonzero; lia).
  assert (Hpow : (2 ^ (j + 1) = 2 * P)%N)
    by (unfold P; rewrite N.pow_add_r, N.pow_1_r; lia).
  rewrite Hpow in Hle, Hmod.
  pose proof (N.div_mod A (2 * P) ltac:(lia)) as EA.
  rewrite Hmod, N.add_0_r in EA.
  set (qa := (A / (2 * P))%N) in *.
  assert (HA : A = (2 * qa * P)%N) by (rewrite EA at 1; ring).
  assert (HAP : (A / P = 2 * qa)%N) by (rewrite HA; apply N.div_mul; exact HP).
  assert (HcP : ((A + P) / P = 2 * qa + 1)%N)
    by (replace (A + P)%N with ((2 * qa + 1) * P)%N by (rewrite HA; ring);
        apply N.div_mul; exact HP).
  assert (Hcm : ((A + P) mod P = 0)%N)
    by (replace (A + P)%N with ((2 * qa + 1) * P)%N by (rewrite HA; ring);
        apply N.mod_mul; exact HP).
  assert (Hdiv : forall v, (v / (2 * P) = v / P / 2)%N)
    by (intros v; rewrite N.div_div by lia; f_equal; ring).
  split.
  - intros Hfc. unfold Ginv. change (2 ^ j)%N with P.
    split; [| split; [exact Hcm | exact Hfc]].
    intros secs Hd. specialize (Hle secs Hd). rewrite Hdiv in Hle.
    rewrite HcP.
    set (u := (and_powers secs / P)%N) in *.
    pose proof (N.div_mod u 2 ltac:(lia)) as U1. pose proof (N.mod_lt u 2 ltac:(lia)) as U2.
    clear - Hle U1 U2. lia.
  - intros Hnf. unfold Ginv. change (2 ^ j)%N with P.
    split; [| split; [| exact Hfe]].
    + intros secs Hd. pose proof (Hle secs Hd) as H1. rewrite Hdiv in H1.
      rewrite HAP.
      set (v := and_powers secs) in *.
      set (u := (v / P)%N) in *.
      pose proof (N.div_mod u 2 ltac:(lia)) as U1. pose proof (N.mod_lt u 2 ltac:(lia)) as U2.
      destruct (N.le_gt_cases u (2 * qa)) as [Hu|Hu]; [exact Hu|].
      exfalso. apply Hnf.
      assert (Eu : u = (2 * qa + 1)%N) by (clear - H1 U1 U2 Hu; lia).
      assert (Hs : sub (A + P) v).
      { intros i Hi. destruct (N.le_gt_cases j i) as [Hji | Hji].
        - rewrite <- (N.sub_add j i Hji).
          rewrite <- N.div_pow2_bits. fold P. fold u. rewrite Eu, <- HcP.
          unfold P. rewrite N.div_pow2_bits. rewrite (N.sub_add j i Hji). exact Hi.
        - rewrite <- (N.mod_pow2_bits_low (A + P) j i Hji) in Hi. fold P in Hi.
          rewrite Hcm, N.bits_0 in Hi. discriminate. }
      exists secs. split; [exact Hd|].
      apply Forall_forall. intros s Hin. apply covers_power.
      intros i Hi. apply Hs in Hi. unfold v in Hi.
      exact (proj1 (and_bits secs i (division_ne secs Hk Hd)) Hi s Hin).
    + rewrite HA. apply N.mod_mul. exact HP.
Qed.

Lemma Ginv_final : forall A, (1 <= k)%N -> Ginv 0 A -> best_and_spec k a A.
Proof.
  intros A Hk (Hle & _ & (secs & Hd & Hc)).
  assert (Hs : sub A (and_powers secs)).
  { intros i Hi. apply and_bits; [exact (division_ne secs Hk Hd)|].
    intros s Hin. rewrite Forall_forall in Hc. specialize (Hc s Hin).
    apply covers_power in Hc. apply Hc. exact Hi. }
  pose proof (sub_le _ _ Hs) as H1. pose proof (Hle secs Hd) as H2.
  rewrite N.pow_0_r, !N.div_1_r in H2.
  split.
  - exists secs. split; [exact Hd | lia].
  - intros secs' Hd'. pose proof (Hle secs' Hd') as H3.
    rewrite N.pow_0_r, !N.div_1_r in H3. exact H3.
Qed.

Lemma value_small : forall v, (v <= 10 ^ 9)%N -> forall i, (30 <= i)%N ->
  N.testbit v i = false.
Proof.
  intros v Hv i Hi. destruct (N.eq_dec v 0) as [E|E].
  - subst v. apply N.bits_0.
  - apply N.bits_above_log2.
    assert (H : (v < 2 ^ 30)%N) by (eapply N.le_lt_trans; [exact Hv | reflexivity]).
    apply N.log2_lt_pow2 in H; lia.
Qed.

Lemma Ginv_init : valid_input k a -> feasible 0 -> Ginv 30 0.
Proof.
  intros Hv Hf. split; [| split; [reflexivity | exact Hf]].
  intros secs Hd. rewrite N.div_0_l by (apply N.pow_nonzero; lia).
  assert (E : (and_powers secs / 2 ^ 30 = 0)%N).
  { apply N.bits_inj. intros i. rewrite N.div_pow2_bits, N.bits_0.
    destruct (N.testbit (and_powers secs) (i + 30)) eqn:Eb; [|reflexivity].
    exfalso.
    assert (Hk : (1 <= k)%N) by (destruct Hv as [Hk _ _]; lia).
    pose proof (division_ne secs Hk Hd) as Hne.
    destruct secs as [| s0 rest]; [congruence|].
    apply (and_bits _ _ Hne) with (s := s0) in Eb; [| left; reflexivity].
    unfold power in Eb. rewrite power_bits_gen, N.bits_0 in Eb. simpl in Eb.
    apply existsb_exists in Eb. destruct Eb as (v & Hin & Hb).
    destruct Hd as (_ & _ & r & Hr & C).
    assert (Ha : In v a).
    { apply (Permutation_in (l := rotate r a)).
      - unfold rotate. rewrite <- (firstn_skipn r a) at 3. apply Permutation_app_comm.
      - rewrite <- C. apply in_concat. exists s0. split; [left; reflexivity | exact Hin]. }
    destruct Hv as [_ _ Hvals]. rewrite Forall_forall in Hvals.
    rewrite (value_small v (Hvals v Ha) (i + 30) ltac:(lia)) in Hb. discriminate. }
  rewrite E. lia.
Qed.

End Circle.

(* ================================================================== *)
(* Part 2. The program                                                 *)
(* ================================================================== *)

Open Scope uint63_scope.
Open Scope array_scope.

Lemma scan_eq : forall a P n b i nb Q H,
  scan a P n b i nb Q H =
  match bdec (0 <? i) with
  | left Hi =>
      let x := i - 1 in
      let nb' := if hasbit (cell a n x) b then i else nb in
      let p := P.[x] in
      scan a P n b x nb' (Q.[x <- if p <? nb' then nb' else p])
        (Acc_inv H (dec_down i Hi))
  | right _ => Q
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma dedup_eq : forall Q V S w i w' V' S' H,
  dedup Q V S w i w' V' S' H =
  match bdec (i <? w) with
  | left Hi =>
      let v := Q.[V.[i]] in
      let s := S.[i] in
      if andb (0 <? w') (V'.[w' - 1] =? v) then
        dedup Q V S w (i + 1) w' V' (S'.[w' - 1 <- s])
          (Acc_inv H (dec_step w i Hi))
      else
        dedup Q V S w (i + 1) (w' + 1) (V'.[w' <- v]) (S'.[w' <- s])
          (Acc_inv H (dec_step w i Hi))
  | right _ => (w', V', S')
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma levels_eq : forall Q t w V S V' S' H,
  levels Q t w V S V' S' H =
  match bdec (0 <? t) with
  | left Ht =>
      let '(w2, V2, S2) := dedup Q V S w 0 0 V' S' (Zwf_well_founded 0 (gap w 0)) in
      levels Q (t - 1) w2 V2 S2 V S (Acc_inv H (dec_down t Ht))
  | right _ => (w, V, S, V', S')
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma check_eq : forall V S n w j H,
  check V S n w j H =
  match bdec (j <? w) with
  | left Hj =>
      if V.[j] <=? S.[j] + n then true
      else check V S n w (j + 1) (Acc_inv H (dec_step w j Hj))
  | right _ => false
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_eq : forall L j V S H,
  init L j V S H =
  match bdec (j <? L) with
  | left Hj => init L (j + 1) (V.[j <- j]) (S.[j <- j]) (Acc_inv H (dec_step L j Hj))
  | right _ => (V, S)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bits_eq : forall a n k b ans P Q V S V' S' H,
  bits a n k b ans P Q V S V' S' H =
  match bdec (0 <? b) with
  | left Hb =>
      let j := b - 1 in
      let Q1 := newptr a P Q n j in
      let '(ok, V1, S1, V2, S2) := test Q1 n k V S V' S' in
      if ok then bits a n k j (ans lor (1 << j)) Q1 P V1 S1 V2 S2 (Acc_inv H (dec_down b Hb))
      else bits a n k j ans P Q1 V1 S1 V2 S2 (Acc_inv H (dec_down b Hb))
  | right _ => ans
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma init_ptr_eq : forall m x P H,
  init_ptr m x P H =
  match bdec (x <? m) with
  | left Hx => init_ptr m (x + 1) (P.[x <- x + 1]) (Acc_inv H (dec_step m x Hx))
  | right _ => P
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ================================================================== *)
(* Part 3. Proofs of the program                                       *)
(* ================================================================== *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Definition Fq (Q : array int) (x : Z) : Z := (φ (Q.[of_Z x])).

Lemma Fq_phi : forall Q x, Fq Q (φ x) = (φ (Q.[x])).
Proof. intros Q x. unfold Fq. rewrite of_to_Z. reflexivity. Qed.

Lemma phi_of_Z : forall y, (0 <= y < 4194304)%Z -> (φ (of_Z y)) = y.
Proof. intros y Hy. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma Fq_set : forall (Q : array int) (x v : int) (y : Z),
  ((φ x) < (φ (PArray.length Q)))%Z -> (0 <= y < 4194304)%Z ->
  Fq (Q.[x <- v]) y = if (y =? (φ x))%Z then (φ v) else Fq Q y.
Proof.
  intros Q x v y Hx Hy. unfold Fq. destruct (Z.eqb_spec y (φ x)) as [E|E].
  - subst y. rewrite of_to_Z. f_equal.
    exact (get_set_same int Q x v ltac:(rewrite ltb_spec; exact Hx)).
  - assert (Ne : x <> of_Z y).
    { intro F. apply E. rewrite F. symmetry. apply phi_of_Z. exact Hy. }
    f_equal. exact (get_set_other int Q x (of_Z y) v Ne).
Qed.

Lemma hasbit_spec : forall v b, ((φ b) < 63)%Z ->
  hasbit v b = N.testbit (Z.to_N (φ v)) (Z.to_N (φ b)).
Proof.
  intros v b Hb. unfold hasbit.
  pose proof (to_Z_bounded b) as Bb. pose proof (to_Z_bounded v) as Bv.
  assert (E : (φ ((v >> b) land 1)) = Z.b2z (Z.testbit (φ v) (φ b))).
  { rewrite land_spec', lsr_spec. replace (φ 1) with (Z.ones 1) by reflexivity.
    rewrite Z.land_ones by lia. rewrite Z.testbit_spec' by lia. reflexivity. }
  rewrite <- Z.testbit_of_N' by lia. rewrite Z2N.id by lia.
  destruct (Z.testbit (φ v) (φ b)); simpl in E.
  - apply eqb_spec. apply to_Z_inj. rewrite E. reflexivity.
  - apply eqb_false_spec. intro F. rewrite F in E. discriminate.
Qed.

(* ---- the pointer update ---- *)

Section Scan.
Variable al : list N.
Variables (xa P : array int) (n bI : int) (A : N).
Hypothesis Hnl : (φ n) = nZ al.
Hypothesis Hn1 : (1 <= nZ al)%Z.
Hypothesis Hn5 : (nZ al <= 500000)%Z.
Hypothesis Hcell : forall x : int, ((φ x) < 2 * nZ al)%Z ->
  Z.to_N (φ (cell xa n x)) = d al (φ x).
Hypothesis Hb : ((φ bI) < 63)%Z.
Hypothesis HP : ptr_spec al A (Fq P).

Lemma scan_spec : forall z i nb Q H, (φ i) = z -> ((φ i) <= 2 * nZ al)%Z ->
  (φ (PArray.length Q)) = (2 * nZ al + 2)%Z ->
  nextb al (Z.to_N (φ bI)) (φ i) (φ nb) ->
  (forall x, (φ i) <= x <= 2 * nZ al -> cellv al (N.lor A (2 ^ Z.to_N (φ bI))) x (Fq Q x))%Z ->
  Fq Q (2 * nZ al + 1) = (2 * nZ al + 1)%Z ->
  ptr_spec al (N.lor A (2 ^ Z.to_N (φ bI))) (Fq (scan xa P n bI i nb Q H)) /\
  (φ (PArray.length (scan xa P n bI i nb Q H))) = (2 * nZ al + 2)%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i nb Q H Hz Hi HQ Hnb Hcells Hend.
  rewrite scan_eq. destruct (bdec (0 <? i)) as [Hi0 | Hi0].
  - cbv zeta. pose proof Hi0 as Hi0'. rewrite ltb_spec in Hi0'. change (φ 0) with 0%Z in Hi0'.
    assert (Hx : (φ (i - 1)) = ((φ i) - 1)%Z) by sia.
    set (x := i - 1) in *.
    set (nb' := if hasbit (cell xa n x) bI then i else nb).
    assert (Enb : (φ nb') = if N.testbit (d al (φ x)) (Z.to_N (φ bI)) then ((φ x) + 1)%Z else (φ nb)).
    { unfold nb'. rewrite hasbit_spec by exact Hb. rewrite Hcell by lia.
      destruct (N.testbit (d al (φ x)) (Z.to_N (φ bI))); [lia | reflexivity]. }
    assert (Hnb' : nextb al (Z.to_N (φ bI)) (φ x) (φ nb')).
    { rewrite Enb. apply nextb_step; [pose proof (to_Z_bounded x); lia | lia |].
      replace ((φ x) + 1)%Z with (φ i) by lia. exact Hnb. }
    set (h := if P.[x] <? nb' then nb' else P.[x]).
    assert (Eh : (φ h) = Z.max (Fq P (φ x)) (φ nb')).
    { unfold h. rewrite Fq_phi. destruct (P.[x] <? nb') eqn:E;
        [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E]; lia. }
    assert (Hch : cellv al (N.lor A (2 ^ Z.to_N (φ bI))) (φ x) (φ h)).
    { rewrite Eh. apply cellv_max; [pose proof (to_Z_bounded x); lia | | exact Hnb'].
      destruct HP as [_ HPc]. apply HPc. pose proof (to_Z_bounded x); lia. }
    assert (HxQ : ((φ x) < (φ (PArray.length Q)))%Z) by lia.
    eapply IH; [ | reflexivity | lia | | exact Hnb' | | ].
    + rewrite <- Hz. apply dec_down. exact Hi0.
    + rewrite alength_set. exact HQ.
    + intros y Hy. rewrite Fq_set by lia.
      destruct (Z.eqb_spec y (φ x)) as [E|E].
      * subst y. exact Hch.
      * apply Hcells. lia.
    + rewrite Fq_set by lia. destruct (Z.eqb_spec (2 * nZ al + 1) (φ x)); [lia | exact Hend].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi0. change (φ 0) with 0%Z in Hi0.
    split; [| exact HQ]. split; [exact Hend|].
    intros x Hx'. exact (Hcells x ltac:(lia)).
Qed.

Lemma newptr_spec : forall Q, (φ (PArray.length Q)) = (2 * nZ al + 2)%Z ->
  ptr_spec al (N.lor A (2 ^ Z.to_N (φ bI))) (Fq (newptr xa P Q n bI)) /\
  (φ (PArray.length (newptr xa P Q n bI))) = (2 * nZ al + 2)%Z.
Proof.
  intros Q HQ. unfold newptr.
  assert (H2 : (φ (2 * n)) = (2 * nZ al)%Z) by sia.
  assert (H21 : (φ (2 * n + 1)) = (2 * nZ al + 1)%Z) by sia.
  apply scan_spec with (z := (φ (2 * n))); [reflexivity | lia | | | | ].
  - rewrite !alength_set. exact HQ.
  - rewrite H2, H21. apply nextb_init.
  - intros x Hx. rewrite H2 in Hx. replace x with (2 * nZ al)%Z by lia.
    rewrite Fq_set by (rewrite ?alength_set; lia).
    destruct (Z.eqb_spec (2 * nZ al) (φ (2 * n + 1))); [lia|].
    rewrite Fq_set by lia. destruct (Z.eqb_spec (2 * nZ al) (φ (2 * n))); [|lia].
    rewrite H21. apply cellv_end.
  - rewrite Fq_set by (rewrite ?alength_set; lia).
    destruct (Z.eqb_spec (2 * nZ al + 1) (φ (2 * n + 1))); [exact H21 | lia].
Qed.

End Scan.

(* ---- the initial pointers, mask 0 ---- *)

Lemma init_ptr_spec : forall (m : int) z x P H, gap m x = z ->
  ((φ x) <= (φ m))%Z -> ((φ m) < (φ (PArray.length P)))%Z -> ((φ m) < 4194303)%Z ->
  (forall y, 0 <= y < (φ x) -> Fq P y = y + 1)%Z ->
  (forall y, 0 <= y < (φ m) -> Fq (init_ptr m x P H) y = y + 1)%Z /\
  PArray.length (init_ptr m x P H) = PArray.length P.
Proof.
  intros m z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x P H Hz Hxm HmP Hm Hc. rewrite init_ptr_eq.
  destruct (bdec (x <? m)) as [Hx | Hx].
  - pose proof Hx as Hx'. rewrite ltb_spec in Hx'.
    assert (Hx1 : (φ (x + 1)) = ((φ x) + 1)%Z) by sia.
    destruct (IH (gap m (x + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hx)
                (x + 1) (P.[x <- x + 1]) (Acc_inv H (dec_step m x Hx)) eq_refl
                ltac:(lia) ltac:(rewrite alength_set; lia) Hm) as [R1 R2].
    + intros y Hy. rewrite Fq_set by lia.
      destruct (Z.eqb_spec y (φ x)) as [E|E]; [lia|]. apply Hc. lia.
    + split; [exact R1|]. rewrite R2. apply alength_set.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hx.
    split; [|reflexivity]. intros y Hy. apply Hc. lia.
Qed.

(* ---- the simultaneous walk ---- *)

Ltac fqs := rewrite Fq_set by (rewrite ?alength_set; lia).

(* level l : the entries j < w are pairwise the group (max start S[j],
   common position V[j] after l steps) of the starts 0 .. L *)
Definition LInv (F : Z -> Z) (L : Z) (l : nat) (V S : array int) (w : Z) : Prop :=
  (0 <= w <= L + 1)%Z /\
  (forall j, 0 <= j < w -> 0 <= Fq S j <= L /\ Fq V j = iter F l (Fq S j))%Z /\
  (forall s, 0 <= s <= L -> exists j, 0 <= j < w /\ s <= Fq S j /\ Fq V j = iter F l s)%Z /\
  (forall j1 j2, 0 <= j1 <= j2 -> j2 < w -> Fq S j1 <= Fq S j2)%Z.

Section Dedup.
Variables (Q VV SS : array int) (L : Z) (l : nat) (w : int) (nn : Z).
Hypothesis HL : LInv (Fq Q) L l VV SS (φ w).
Hypothesis Hnn : (L + 1 <= nn)%Z.
Hypothesis Hnn2 : (nn <= 4194303)%Z.

Definition DInv (i w' : int) (V' S' : array int) : Prop :=
  ((φ w') <= (φ i) <= (φ w))%Z /\
  (φ (PArray.length V')) = nn /\ (φ (PArray.length S')) = nn /\
  (forall j, 0 <= j < (φ w') ->
     0 <= Fq S' j <= L /\ Fq V' j = iter (Fq Q) (Datatypes.S l) (Fq S' j))%Z /\
  (forall i', 0 <= i' < (φ i) -> exists j, 0 <= j < (φ w') /\
     Fq SS i' <= Fq S' j /\ Fq V' j = Fq Q (Fq VV i'))%Z /\
  (forall j1 j2, 0 <= j1 <= j2 -> j2 < (φ w') -> Fq S' j1 <= Fq S' j2)%Z /\
  (forall j i'', 0 <= j < (φ w') -> (φ i) <= i'' < (φ w) -> Fq S' j <= Fq SS i'')%Z.

Lemma dedup_inv : forall z i w' V' S' H, gap w i = z -> DInv i w' V' S' ->
  forall w2 V2 S2, dedup Q VV SS w i w' V' S' H = (w2, V2, S2) ->
  LInv (Fq Q) L (Datatypes.S l) V2 S2 (φ w2) /\
  (φ (PArray.length V2)) = nn /\ (φ (PArray.length S2)) = nn.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i w' V' S' H Hz Hd w2 V2 S2 E.
  rewrite dedup_eq in E.
  pose proof HL as (HL0 & HL1 & HL2 & HL3).
  destruct Hd as (D0 & DV & DS & D1 & D2 & D3 & D4).
  pose proof (to_Z_bounded i) as Bi. pose proof (to_Z_bounded w') as Bw'.
  destruct (bdec (i <? w)) as [Hi | Hi].
  - cbv zeta in E. pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    destruct (HL1 (φ i) ltac:(lia)) as (Hs & Hv).
    rewrite !Fq_phi in Hs. rewrite !Fq_phi in Hv.
    assert (Ev : (φ (Q.[VV.[i]])) = iter (Fq Q) (Datatypes.S l) (φ (SS.[i]))).
    { rewrite iter_S', <- Hv, Fq_phi. reflexivity. }
    assert (Ev' : Fq Q (Fq VV (φ i)) = (φ (Q.[VV.[i]]))) by (rewrite !Fq_phi; reflexivity).
    assert (Hmono : forall i'', ((φ i) <= i'' < (φ w))%Z -> ((φ (SS.[i])) <= Fq SS i'')%Z).
    { intros i'' Hi''. rewrite <- Fq_phi. apply HL3; lia. }
    assert (D4i : forall j, (0 <= j < (φ w'))%Z -> (Fq S' j <= (φ (SS.[i])))%Z).
    { intros j Hj. rewrite <- Fq_phi. apply D4; lia. }
    destruct (andb (0 <? w') (V'.[w' - 1] =? Q.[VV.[i]])) eqn:Em.
    + apply andb_prop in Em. destruct Em as [Ew Eq].
      rewrite ltb_spec in Ew. change (φ 0) with 0%Z in Ew. rewrite eqb_spec in Eq.
      assert (Hw1 : (φ (w' - 1)) = ((φ w') - 1)%Z) by sia.
      assert (EV1 : Fq V' ((φ w') - 1) = (φ (Q.[VV.[i]])))
        by (rewrite <- Hw1, Fq_phi, Eq; reflexivity).
      eapply IH; [ | reflexivity | | exact E ].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * refine (conj _ (conj DV (conj _ (conj _ (conj _ (conj _ _)))))).
        -- lia.
        -- rewrite alength_set. exact DS.
        -- intros j Hj. fqs. destruct (Z.eqb_spec j (φ (w' - 1))) as [Ej|Ej].
           ++ split; [lia|]. rewrite Ej, Hw1, EV1. exact Ev.
           ++ apply D1; lia.
        -- intros i' Hi'2. destruct (Z.eq_dec i' (φ i)) as [Ei|Ei].
           ++ exists ((φ w') - 1)%Z. split; [lia|]. fqs.
              destruct (Z.eqb_spec ((φ w') - 1) (φ (w' - 1))); [|lia].
              rewrite Ei, Fq_phi, EV1, Ev'. split; [lia | reflexivity].
           ++ destruct (D2 i' ltac:(lia)) as (j & Hj & Hj1 & Hj2).
              exists j. split; [lia|]. fqs.
              destruct (Z.eqb_spec j (φ (w' - 1))) as [Ej|Ej].
              ** split; [| exact Hj2]. pose proof (D4i j Hj). lia.
              ** split; [exact Hj1 | exact Hj2].
        -- intros j1 j2 Hj1 Hj2. fqs. fqs.
           destruct (Z.eqb_spec j1 (φ (w' - 1))), (Z.eqb_spec j2 (φ (w' - 1))).
           ++ lia.
           ++ lia.
           ++ apply D4i. lia.
           ++ apply D3; lia.
        -- intros j i'' Hj Hi''. fqs. destruct (Z.eqb_spec j (φ (w' - 1))).
           ++ apply Hmono. lia.
           ++ apply D4; lia.
    + assert (Hw1 : (φ (w' + 1)) = ((φ w') + 1)%Z) by sia.
      eapply IH; [ | reflexivity | | exact E ].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
        -- lia.
        -- rewrite alength_set. exact DV.
        -- rewrite alength_set. exact DS.
        -- intros j Hj. fqs. fqs. destruct (Z.eqb_spec j (φ w')) as [Ej|Ej].
           ++ split; [lia | exact Ev].
           ++ apply D1; lia.
        -- intros i' Hi'2. destruct (Z.eq_dec i' (φ i)) as [Ei|Ei].
           ++ exists (φ w'). split; [lia|]. fqs. fqs.
              rewrite Z.eqb_refl. rewrite Ei, Fq_phi, Ev'. split; [lia | reflexivity].
           ++ destruct (D2 i' ltac:(lia)) as (j & Hj & Hj1 & Hj2).
              exists j. split; [lia|]. fqs. fqs.
              destruct (Z.eqb_spec j (φ w')) as [Ej|Ej]; [lia|].
              split; [exact Hj1 | exact Hj2].
        -- intros j1 j2 Hj1 Hj2. fqs. fqs.
           destruct (Z.eqb_spec j1 (φ w')), (Z.eqb_spec j2 (φ w')).
           ++ lia.
           ++ lia.
           ++ apply D4i. lia.
           ++ apply D3; lia.
        -- intros j i'' Hj Hi''. fqs. destruct (Z.eqb_spec j (φ w')).
           ++ apply Hmono. lia.
           ++ apply D4; lia.
  - injection E as <- <- <-.
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    split; [| split; [exact DV | exact DS]].
    refine (conj _ (conj D1 (conj _ D3))).
    + lia.
    + intros s Hs. destruct (HL2 s Hs) as (j & Hj & Hj1 & Hj2).
      destruct (D2 j ltac:(lia)) as (j' & Hj' & Hj'1 & Hj'2).
      exists j'. split; [exact Hj'|]. split; [lia|].
      rewrite Hj'2, Hj2, iter_S'. reflexivity.
Qed.

Lemma dedup_spec : forall (V' S' : array int) H,
  (φ (PArray.length V')) = nn -> (φ (PArray.length S')) = nn ->
  forall w2 V2 S2, dedup Q VV SS w 0 0 V' S' H = (w2, V2, S2) ->
  LInv (Fq Q) L (Datatypes.S l) V2 S2 (φ w2) /\
  (φ (PArray.length V2)) = nn /\ (φ (PArray.length S2)) = nn.
Proof.
  intros V' S' H HV HS. apply (dedup_inv _ 0 0 V' S' H eq_refl).
  pose proof HL as (HL0 & _). pose proof (to_Z_bounded w).
  change (φ 0) with 0%Z.
  refine (conj _ (conj HV (conj HS (conj _ (conj _ (conj _ _)))))); intros; lia.
Qed.

End Dedup.

Lemma levels_spec : forall (Q : array int) (L nn : Z) (K : nat),
  (L + 1 <= nn)%Z -> (nn <= 4194303)%Z ->
  forall z t w V S V' S' H l, (φ t) = z -> (l + Z.to_nat (φ t))%nat = K ->
  LInv (Fq Q) L l V S (φ w) ->
  (φ (PArray.length V)) = nn -> (φ (PArray.length S)) = nn ->
  (φ (PArray.length V')) = nn -> (φ (PArray.length S')) = nn ->
  forall w2 V2 S2 V3 S3, levels Q t w V S V' S' H = (w2, V2, S2, V3, S3) ->
  LInv (Fq Q) L K V2 S2 (φ w2) /\
  (φ (PArray.length V2)) = nn /\ (φ (PArray.length S2)) = nn /\
  (φ (PArray.length V3)) = nn /\ (φ (PArray.length S3)) = nn.
Proof.
  intros Q L nn K Hnn Hnn2 z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t w V S V' S' H l Hz Hl HL HV HS HV' HS' w2 V2 S2 V3 S3 E.
  rewrite levels_eq in E. destruct (bdec (0 <? t)) as [Ht | Ht].
  - pose proof Ht as Ht'. rewrite ltb_spec in Ht'. change (φ 0) with 0%Z in Ht'.
    assert (Ht1 : (φ (t - 1)) = ((φ t) - 1)%Z) by sia.
    destruct (dedup Q V S w 0 0 V' S' (Zwf_well_founded 0 (gap w 0)))
      as [[w4 V4] S4] eqn:Ed.
    destruct (dedup_spec Q V S L l w nn HL Hnn Hnn2 V' S' _ HV' HS' w4 V4 S4 Ed)
      as (HL4 & HV4 & HS4).
    eapply IH; [ | reflexivity | | exact HL4 | exact HV4 | exact HS4 | exact HV | exact HS | exact E].
    + rewrite <- Hz. apply dec_down. exact Ht.
    + rewrite Ht1. lia.
  - injection E as <- <- <- <- <-.
    rewrite <- Bool.not_true_iff_false, ltb_spec in Ht. change (φ 0) with 0%Z in Ht.
    pose proof (to_Z_bounded t).
    replace K with l by lia. auto.
Qed.

Lemma init_spec : forall (L : int), ((φ L) <= 4194303)%Z ->
  forall z j V S H, gap L j = z -> ((φ j) <= (φ L))%Z ->
  ((φ L) <= (φ (PArray.length V)))%Z -> ((φ L) <= (φ (PArray.length S)))%Z ->
  (forall y, 0 <= y < (φ j) -> Fq V y = y /\ Fq S y = y)%Z ->
  forall V1 S1, init L j V S H = (V1, S1) ->
  (forall y, 0 <= y < (φ L) -> Fq V1 y = y /\ Fq S1 y = y)%Z /\
  PArray.length V1 = PArray.length V /\ PArray.length S1 = PArray.length S.
Proof.
  intros L HLb z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j V S H Hz Hj HV HS Hc V1 S1 E.
  rewrite init_eq in E. destruct (bdec (j <? L)) as [Hj' | Hj'].
  - pose proof Hj' as Hj''. rewrite ltb_spec in Hj''.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    destruct (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hj') (j + 1)
               (V.[j <- j]) (S.[j <- j]) _ eq_refl ltac:(lia)
               ltac:(rewrite alength_set; lia) ltac:(rewrite alength_set; lia)
               ltac:(intros y Hy; fqs; fqs; destruct (Z.eqb_spec y (φ j));
                     [subst; auto | apply Hc; lia])
               V1 S1 E) as (R1 & R2 & R3).
    split; [exact R1|]. rewrite R2, R3, !alength_set. auto.
  - injection E as <- <-. rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    split; [| auto]. intros y Hy. apply Hc. lia.
Qed.

Lemma check_spec : forall (V S : array int) (n w : int),
  ((φ n) <= 4194303)%Z ->
  (forall jj, 0 <= jj < (φ w) -> 0 <= Fq S jj <= 4194303)%Z ->
  forall z j H, gap w j = z -> (0 <= (φ j))%Z ->
  (check V S n w j H = true <->
   exists jj, ((φ j) <= jj < (φ w))%Z /\ (Fq V jj <= Fq S jj + (φ n))%Z).
Proof.
  intros V S n w Hn HS z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j H Hz Hj. rewrite check_eq. destruct (bdec (j <? w)) as [Hj' | Hj'].
  - pose proof Hj' as Hj''. rewrite ltb_spec in Hj''.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    pose proof (HS (φ j) ltac:(lia)) as Hsj. rewrite Fq_phi in Hsj.
    assert (Hadd : (φ (S.[j] + n)) = ((φ (S.[j])) + (φ n))%Z) by sia.
    destruct (V.[j] <=? S.[j] + n) eqn:E.
    + rewrite leb_spec, Hadd in E. split; [intros _|reflexivity].
      exists (φ j). split; [lia|]. rewrite !Fq_phi. exact E.
    + rewrite <- Bool.not_true_iff_false, leb_spec, Hadd in E.
      rewrite (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hj') (j + 1) _ eq_refl ltac:(lia)).
      split; intros (jj & Hjj & Hc); exists jj; (split; [|exact Hc]).
      * lia.
      * destruct (Z.eq_dec jj (φ j)) as [Ej|Ej]; [|lia].
        exfalso. subst jj. rewrite !Fq_phi in Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hj'.
    split; [discriminate|]. intros (jj & Hjj & _). lia.
Qed.

(* ---- the feasibility test ---- *)

Lemma Fq_0 : forall Q, Fq Q 0 = (φ (Q.[0])).
Proof. intros Q. reflexivity. Qed.

Lemma test_spec : forall (al : list N) (kN c : N) (Q : array int) (n kI : int)
    (V S V' S' : array int),
  (φ n) = nZ al -> (1 <= nZ al)%Z -> (nZ al <= 500000)%Z ->
  (1 <= KK kN)%nat -> Z.to_nat (φ kI) = KK kN ->
  ptr_spec al c (Fq Q) ->
  (φ (PArray.length V)) = nZ al -> (φ (PArray.length S)) = nZ al ->
  (φ (PArray.length V')) = nZ al -> (φ (PArray.length S')) = nZ al ->
  forall ok V1 S1 V2 S2, test Q n kI V S V' S' = (ok, V1, S1, V2, S2) ->
  (ok = true <-> feasible al kN c) /\
  (φ (PArray.length V1)) = nZ al /\ (φ (PArray.length S1)) = nZ al /\
  (φ (PArray.length V2)) = nZ al /\ (φ (PArray.length S2)) = nZ al.
Proof.
  intros al kN c Q n kI V S V' S' Hn Hn1 Hn5 HK HkI HF HV HS HV' HS'
    ok V1 S1 V2 S2 E.
  unfold test in E. cbv zeta in E.
  pose proof HF as [_ HFc]. destruct (HFc 0%Z ltac:(lia)) as (HF0 & _ & _).
  rewrite Fq_0 in HF0.
  set (Lz := Z.min (Fq Q 0) (nZ al - 1)).
  assert (HL1 : (φ ((if Q.[0] <? n - 1 then Q.[0] else n - 1) + 1)) = (Lz + 1)%Z).
  { unfold Lz. rewrite Fq_0. destruct (Q.[0] <? n - 1) eqn:El;
      [rewrite ltb_spec in El | rewrite <- Bool.not_true_iff_false, ltb_spec in El];
      sia. }
  revert E.
  set (L1 := (if Q.[0] <? n - 1 then Q.[0] else n - 1) + 1) in *.
  destruct (init L1 0 V S _) as [V4 S4] eqn:Ei.
  destruct (init_spec L1 ltac:(lia) _ 0 V S _ eq_refl ltac:(change (φ 0) with 0%Z; lia)
              ltac:(lia) ltac:(lia)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy; lia) V4 S4 Ei)
    as (Hc4 & HV4 & HS4).
  rewrite HL1 in Hc4.
  assert (HL : LInv (Fq Q) Lz 0 V4 S4 (Lz + 1)).
  { refine (conj _ (conj _ (conj _ _))).
    - lia.
    - intros j Hj. destruct (Hc4 j ltac:(lia)) as [E1 E2]. rewrite E1, E2. split; [lia | reflexivity].
    - intros s Hs. exists s. destruct (Hc4 s ltac:(lia)) as [E1 E2].
      rewrite E1, E2. split; [lia | split; [lia | reflexivity]].
    - intros j1 j2 Hj1 Hj2. rewrite (proj2 (Hc4 j1 ltac:(lia))), (proj2 (Hc4 j2 ltac:(lia))). lia. }
  rewrite <- HL1 in HL.
  destruct (levels Q kI _ V4 S4 V' S' _) as [[[[w V5] S5] V6] S6] eqn:El.
  intros E. injection E as <- <- <- <- <-.
  destruct (levels_spec Q Lz (nZ al) (KK kN) ltac:(lia) ltac:(lia) _ kI _ V4 S4 V' S' _ 0%nat
              eq_refl ltac:(lia) HL ltac:(rewrite HV4; exact HV) ltac:(rewrite HS4; exact HS)
              HV' HS' w V5 S5 V6 S6 El) as ((HW0 & HW1 & HW2 & HW3) & HV5 & HS5 & HV6 & HS6).
  split; [| auto].
  rewrite (check_spec V5 S5 n w ltac:(lia)
             ltac:(intros jj Hjj; destruct (HW1 jj Hjj); lia) _ 0 _ eq_refl
             ltac:(change (φ 0) with 0%Z; lia)).
  rewrite (feasible_iff al kN Hn1 c (Fq Q) HF HK). fold Lz.
  change (φ 0) with 0%Z. rewrite Hn. split.
  - intros (jj & Hjj & Hc). destruct (HW1 jj ltac:(lia)) as [B1 B2].
    exists (Fq S5 jj). split; [lia|]. rewrite <- B2. exact Hc.
  - intros (s & Hs & Hc). destruct (HW2 s Hs) as (jj & Hjj & B1 & B2).
    exists jj. split; [lia|]. rewrite B2. lia.
Qed.

(* ---- the greedy ---- *)

Section Bits.
Variables (al : list N) (kN : N) (xa : array int) (n kI : int).
Hypothesis Hv : valid_input kN al.
Hypothesis Hnl : (φ n) = nZ al.
Hypothesis Hcell : forall x : int, ((φ x) < 2 * nZ al)%Z ->
  Z.to_N (φ (cell xa n x)) = d al (φ x).
Hypothesis HkI : Z.to_nat (φ kI) = KK kN.

Lemma vi_facts : (1 <= nZ al)%Z /\ (nZ al <= 500000)%Z /\ (1 <= KK kN)%nat /\ (1 <= kN)%N.
Proof.
  destruct Hv as [Hk Hn _]. unfold len, nZ, KK in *. lia.
Qed.

Lemma bits_spec : forall z b ans P Q V S V' S' H A, (φ b) = z -> ((φ b) <= 30)%Z ->
  (φ ans) = Z.of_N A -> Ginv al kN (Z.to_N (φ b)) A -> ptr_spec al A (Fq P) ->
  (φ (PArray.length P)) = (2 * nZ al + 2)%Z -> (φ (PArray.length Q)) = (2 * nZ al + 2)%Z ->
  (φ (PArray.length V)) = nZ al -> (φ (PArray.length S)) = nZ al ->
  (φ (PArray.length V')) = nZ al -> (φ (PArray.length S')) = nZ al ->
  Ginv al kN 0 (Z.to_N (φ (bits xa n kI b ans P Q V S V' S' H))).
Proof.
  destruct vi_facts as (Hn1 & Hn5 & HK & Hk1).
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros b ans P Q V S V' S' H A Hz Hb Ha HG HP HlP HlQ HV HS HV' HS'.
  rewrite bits_eq. destruct (bdec (0 <? b)) as [Hb0 | Hb0].
  - cbv zeta. pose proof Hb0 as Hb0'. rewrite ltb_spec in Hb0'. change (φ 0) with 0%Z in Hb0'.
    assert (Hj : (φ (b - 1)) = ((φ b) - 1)%Z) by sia.
    destruct (newptr_spec al xa P n (b - 1) A Hnl Hn1 Hn5 Hcell ltac:(lia) HP Q HlQ)
      as (HQ1 & HlQ1).
    set (Q1 := newptr xa P Q n (b - 1)) in *.
    set (c := N.lor A (2 ^ Z.to_N (φ (b - 1)))) in *.
    destruct (test Q1 n kI V S V' S') as [[[[ok V1] S1] V2] S2] eqn:Et.
    destruct (test_spec al kN c Q1 n kI V S V' S' Hnl Hn1 Hn5 HK HkI HQ1 HV HS HV' HS'
                ok V1 S1 V2 S2 Et) as (Hok & HV1 & HS1 & HV2 & HS2).
    assert (HG' : Ginv al kN (Z.to_N (φ (b - 1)) + 1) A)
      by (replace (Z.to_N (φ (b - 1)) + 1)%N with (Z.to_N (φ b)) by lia; exact HG).
    destruct (Ginv_step al kN _ A Hk1 HG') as [Hacc Hrej].
    fold c in Hacc, Hrej.
    destruct ok.
    + assert (Hc : (φ (ans lor (1 << (b - 1)))) = Z.of_N c).
      { rewrite lor_spec', lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
        rewrite Z.mod_small by (rewrite wB_val; split; [apply Z.pow_nonneg; lia|];
                                apply Z.le_lt_trans with (2 ^ 30)%Z;
                                [apply Z.pow_le_mono_r; lia | reflexivity]).
        unfold c. rewrite N2Z.inj_lor, N2Z.inj_pow, Ha. f_equal. f_equal.
        rewrite Z2N.id; [reflexivity | lia]. }
      eapply IH; [ | reflexivity | lia | exact Hc | apply Hacc; apply Hok; reflexivity
                 | exact HQ1 | exact HlQ1 | exact HlP | exact HV1 | exact HS1 | exact HV2 | exact HS2].
      rewrite <- Hz. apply dec_down. exact Hb0.
    + eapply IH; [ | reflexivity | lia | exact Ha
                 | apply Hrej; intro F; apply Hok in F; discriminate
                 | exact HP | exact HlP | exact HlQ1 | exact HV1 | exact HS1 | exact HV2 | exact HS2].
      rewrite <- Hz. apply dec_down. exact Hb0.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hb0. change (φ 0) with 0%Z in Hb0.
    replace (φ b) with 0%Z in HG by lia. rewrite Ha, N2Z.id. exact HG.
Qed.

End Bits.

(* ---- the contract ---- *)

Lemma repr_cells : forall (xa : array uint) (al : list N), repr xa al ->
  (φ (PArray.length xa)) = Z.of_nat (List.length al) /\
  forall i : int, ((φ i) < Z.of_nat (List.length al))%Z ->
    Z.to_N (φ (xa.[i])) = nth (Z.to_nat (φ i)) al 0%N.
Proof.
  intros xa al [Hl Hc]. split; [symmetry; exact Hl|].
  intros i Hi. pose proof (to_Z_bounded i) as Bi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr. rewrite Z2Nat.id in Hr by lia. rewrite of_to_Z in Hr.
  transitivity m; [exact Hr|]. symmetry. apply nth_error_nth. exact Hm.
Qed.

Lemma iter_succ : forall al (F : Z -> Z),
  (forall y, 0 <= y <= 2 * nZ al -> F y = y + 1)%Z ->
  forall j x, (0 <= x)%Z -> (x + Z.of_nat j <= 2 * nZ al + 1)%Z ->
  iter F j x = (x + Z.of_nat j)%Z.
Proof.
  intros al F HF j. induction j as [| j IH]; intros x H0 H1; cbn [iter]; [lia|].
  rewrite HF by lia. rewrite IH by lia. lia.
Qed.

Lemma best_and_impl_correct : forall (k : N) (a : list N) (xk : uint) (xa : array uint),
  valid_input k a -> repr xk k -> repr xa a ->
  exists v : N, repr (best_and_impl xk xa) v /\ best_and_spec k a v.
Proof.
  intros k a xk xa Hv Hk Ha.
  destruct (repr_cells xa a Ha) as [Hl Hc].
  pose proof Hv as Hv'. destruct Hv' as [Hvk Hvn _]. unfold len in Hvk, Hvn.
  assert (Hn1 : (1 <= nZ a)%Z) by (unfold nZ; lia).
  assert (Hn5 : (nZ a <= 500000)%Z) by (unfold nZ; lia).
  assert (Hnl : (φ (PArray.length xa)) = nZ a) by exact Hl.
  assert (HK : (1 <= KK k)%nat) by (unfold KK; lia).
  assert (HkI : Z.to_nat (φ xk) = KK k).
  { unfold repr, repr_uint in Hk. unfold KK. rewrite <- Hk. lia. }
  assert (HKn : (Z.of_nat (KK k) <= nZ a)%Z) by (unfold KK, nZ; lia).
  exists (Z.to_N (φ (best_and_impl xk xa))). split; [reflexivity|].
  unfold best_and_impl. cbv zeta.
  set (n := PArray.length xa) in *.
  assert (H2 : (φ (2 * n)) = (2 * nZ a)%Z) by sia.
  assert (H21 : (φ (2 * n + 1)) = (2 * nZ a + 1)%Z) by sia.
  assert (H22 : (φ (2 * n + 2)) = (2 * nZ a + 2)%Z) by sia.
  assert (Hmk2 : (φ (PArray.length (PArray.make (2 * n + 2) 0))) = (2 * nZ a + 2)%Z).
  { rewrite alength_make. replace (2 * n + 2 <=? PArray.max_length) with true; [exact H22|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  assert (Hmk1 : (φ (PArray.length (PArray.make n 0))) = nZ a).
  { rewrite alength_make. replace (n <=? PArray.max_length) with true; [exact Hnl|].
    symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia. }
  (* the initial pointers *)
  destruct (init_ptr_spec (2 * n + 1) _ 0 (PArray.make (2 * n + 2) 0)
              (Zwf_well_founded 0 (gap (2 * n + 1) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; lia) ltac:(lia) ltac:(lia)
              ltac:(intros y Hy; change (φ 0) with 0%Z in Hy; lia)) as [HP1 HP2].
  set (P0 := init_ptr (2 * n + 1) 0 (PArray.make (2 * n + 2) 0)
                (Zwf_well_founded 0 (gap (2 * n + 1) 0))) in *.
  assert (HlP0 : (φ (PArray.length P0)) = (2 * nZ a + 2)%Z) by (rewrite HP2; exact Hmk2).
  set (P := P0.[2 * n + 1 <- 2 * n + 1]).
  assert (HlP : (φ (PArray.length P)) = (2 * nZ a + 2)%Z) by (unfold P; rewrite alength_set; exact HlP0).
  assert (HFP : forall y, (0 <= y <= 2 * nZ a)%Z -> Fq P y = (y + 1)%Z).
  { intros y Hy. unfold P. fqs. destruct (Z.eqb_spec y (φ (2 * n + 1))); [lia|].
    apply HP1. lia. }
  assert (HP : ptr_spec a 0 (Fq P)).
  { split.
    - unfold P. fqs. rewrite H21, Z.eqb_refl. reflexivity.
    - intros x Hx. rewrite HFP by lia. destruct (cellv_zero a x) as [C|C]; [exact C | lia]. }
  (* the cells of the circle *)
  assert (Hcell : forall x : int, ((φ x) < 2 * nZ a)%Z ->
            Z.to_N (φ (cell xa n x)) = d a (φ x)).
  { intros x Hx. pose proof (to_Z_bounded x) as Bx. unfold cell, d.
    destruct (x <? n) eqn:E.
    - rewrite ltb_spec in E.
      etransitivity; [exact (Hc x ltac:(fold (nZ a); lia)) |].
      rewrite Z.mod_small by lia. reflexivity.
    - rewrite <- Bool.not_true_iff_false, ltb_spec in E.
      assert (Hxn : (φ (x - n)) = ((φ x) - nZ a)%Z) by sia.
      etransitivity; [exact (Hc (x - n) ltac:(fold (nZ a); lia)) |]. rewrite Hxn.
      replace ((φ x) mod nZ a)%Z with ((φ x) - nZ a)%Z; [reflexivity|].
      replace (φ x) with (((φ x) - nZ a) + 1 * nZ a)%Z at 2 by ring.
      rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. reflexivity. }
  (* the greedy *)
  assert (Hf0 : feasible a k 0).
  { apply (soundness a k Hn1 0 (Fq P) HP HK 0 ltac:(lia)).
    rewrite (iter_succ a (Fq P) HFP) by lia. lia. }
  pose proof (Ginv_init a k Hv Hf0) as HG.
  pose proof (bits_spec a k xa n xk Hv Hnl Hcell HkI _ 30 0 P (PArray.make (2 * n + 2) 0)
                (PArray.make n 0) (PArray.make n 0) (PArray.make n 0) (PArray.make n 0)
                (Zwf_well_founded 0 (φ 30)) 0 eq_refl ltac:(change (φ 30) with 30%Z; lia)
                eq_refl HG HP HlP Hmk2 Hmk1 Hmk1 Hmk1 Hmk1) as HG0.
  apply Ginv_final; [lia | exact HG0].
Qed.

Definition best_and_correct : forall (k : N) (a : list N) (xk : uint) (xa : array uint),
  valid_input k a -> repr xk k -> repr xa a ->
  exists v : N, repr (best_and xk xa) v /\ best_and_spec k a v
  := best_and_impl_correct.
