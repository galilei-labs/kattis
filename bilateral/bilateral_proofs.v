(* Correctness proofs for bilateral_implem.v. *)
(* Implementation of bilateral (bilateral.spec).

   A minimum vertex cover of the bipartite team graph by König's theorem:
   CSR adjacency, maximum matching by augmenting paths (one breadth-first
   alternating search from all free left vertices per phase, augmentation
   along the parent pointers), König's cover read off the failed search.
   The friend (1009) is preferred by computing the cover twice, on the
   graph without the friend's teams (C') and on the whole graph (C): if
   |C'| + 1 <= |C|, C' plus the friend is a smallest invitation, otherwise
   no smallest invitation contains the friend.  Flat Uint63 arrays only;
   every loop terminates on an erased Acc. *)

From Bilateral.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

From Bilateral Require Export bilateral_implem.
Open Scope uint63_scope.
Open Scope array_scope.


(* ------------------------------------------------------------------ *)
(* Unfolding equations of the loops                                    *)
(* ------------------------------------------------------------------ *)

Lemma deg_loop_eq : forall x ex m k d H, deg_loop x ex m k d H =
  match bdec (k <? m)%uint63 with
  | left Hk =>
      let a := x.[k] in
      deg_loop x ex m (k + 1)
        (if (a =? ex)%uint63 then d else let u := (a - 1000)%uint63 in d.[u <- d.[u] + 1])
        (Acc_inv H (dec_step m k Hk))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma off_loop_eq : forall d u o H, off_loop d u o H =
  match bdec (u <? NV)%uint63 with
  | left Hu => off_loop d (u + 1) o.[u + 1 <- o.[u] + d.[u]]
                 (Acc_inv H (dec_step NV u Hu))
  | right _ => o
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_loop_eq : forall x y ex m k pos tg H, fill_loop x y ex m k pos tg H =
  match bdec (k <? m)%uint63 with
  | left Hk =>
      let a := x.[k] in
      if (a =? ex)%uint63 then fill_loop x y ex m (k + 1) pos tg (Acc_inv H (dec_step m k Hk))
      else
        let u := (a - 1000)%uint63 in
        let p := pos.[u] in
        fill_loop x y ex m (k + 1) pos.[u <- p + 1] tg.[p <- y.[k] - 2000]
          (Acc_inv H (dec_step m k Hk))
  | right _ => tg
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma root_loop_eq : forall mL u Q qp t H, root_loop mL u Q qp t H =
  match bdec (u <? NV) with
  | left Hu =>
      if mL.[u] <? NV then root_loop mL (u + 1) Q qp t (Acc_inv H (dec_step NV u Hu))
      else root_loop mL (u + 1) Q.[t <- u] qp.[u <- t + 1] (t + 1)
             (Acc_inv H (dec_step NV u Hu))
  | right _ => (Q, qp, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_eq : forall tg mR u pe p Q qp pr t H, scan tg mR u pe p Q qp pr t H =
  match bdec (p <? pe) with
  | left Hp =>
      let v := tg.[p] in
      if pr.[v] =? 0 then
        let pr := pr.[v <- u + 1] in
        let w := mR.[v] in
        if w <? NV then
          if qp.[w] =? 0 then
            scan tg mR u pe (p + 1) Q.[t <- w] qp.[w <- t + 1] pr (t + 1)
              (Acc_inv H (dec_step pe p Hp))
          else scan tg mR u pe (p + 1) Q qp pr t (Acc_inv H (dec_step pe p Hp))
        else SFound v qp pr
      else scan tg mR u pe (p + 1) Q qp pr t (Acc_inv H (dec_step pe p Hp))
  | right _ => SCont Q qp pr t
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_eq : forall off tg mR h t Q qp pr H, bfs off tg mR h t Q qp pr H =
  match bdec (h <? NV) with
  | left Hh =>
      if h <? t then
        let u := Q.[h] in
        match scan tg mR u off.[u + 1] off.[u] Q qp pr t
                (Zwf_well_founded 0 (gap off.[u + 1] off.[u])) with
        | SFound v qp pr => BFound v qp pr
        | SCont Q qp pr t => bfs off tg mR (h + 1) t Q qp pr (Acc_inv H (dec_step NV h Hh))
        end
      else BFail qp pr
  | right _ => BFail qp pr
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma walk_eq : forall qp pr v mL mR H, walk qp pr v mL mR H =
  let u := pr.[v] - 1 in
  let old := mL.[u] in
  let mL' := mL.[u <- v] in
  let mR' := mR.[v <- u] in
  if old <? NV then
    match bdec (qp.[pr.[old] - 1] <? qp.[pr.[v] - 1]) with
    | left Hd => walk qp pr old mL' mR' (Acc_inv H (wdec qp pr v old Hd))
    | right _ => (mL', mR')
    end
  else (mL', mR').
Proof. intros. destruct H. reflexivity. Qed.

Lemma phases_eq : forall off tg it mL mR H, phases off tg it mL mR H =
  match bdec (it <? NP) with
  | left Hi =>
      let '(Q, qp, t) := root_loop mL 0 (PArray.make NV 0) (PArray.make NV 0) 0
                           (Zwf_well_founded 0 (gap NV 0)) in
      match bfs off tg mR 0 t Q qp (PArray.make NV 0) (Zwf_well_founded 0 (gap NV 0)) with
      | BFound v qp pr =>
          let '(mL, mR) := walk qp pr v mL mR (Zwf_well_founded 0 (wmeas qp pr v)) in
          phases off tg (it + 1) mL mR (Acc_inv H (dec_step NP it Hi))
      | BFail qp pr => (qp, pr)
      end
  | right _ => (PArray.make NV 0, PArray.make NV 0)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma mark_loop_eq : forall qp pr i mk H, mark_loop qp pr i mk H =
  match bdec (i <? NM) with
  | left Hi =>
      mark_loop qp pr (i + 1)
        (if i <? NV then (if qp.[i] =? 0 then mk.[i <- 1] else mk)
         else (if pr.[i - NV] =? 0 then mk else mk.[i <- 1]))
        (Acc_inv H (dec_step NM i Hi))
  | right _ => mk
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma cnt_loop_eq : forall mk i c H, cnt_loop mk i c H =
  match bdec (i <? NM) with
  | left Hi =>
      cnt_loop mk (i + 1) (if mk.[i] =? 0 then c else c + 1) (Acc_inv H (dec_step NM i Hi))
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma out_loop_eq : forall mk i p out H, out_loop mk i p out H =
  match bdec (i <? NM) with
  | left Hi =>
      if mk.[i] =? 0 then out_loop mk (i + 1) p out (Acc_inv H (dec_step NM i Hi))
      else out_loop mk (i + 1) (p + 1) out.[p <- 1000 + i] (Acc_inv H (dec_step NM i Hi))
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Plumbing: arrays read as functions Z -> Z, counting                 *)
(* ------------------------------------------------------------------ *)

Open Scope Z_scope.
Open Scope bool_scope.

Lemma wB_val : wB = 9223372036854775808.
Proof. reflexivity. Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t)%uint63 = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_make : forall (n b i : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma alength_make : forall (n : int) (b : int),
  PArray.length (PArray.make n b)
  = if (n <=? PArray.max_length)%uint63 then n else PArray.max_length.
Proof. intros n b. exact (length_make int n b). Qed.

Definition rd (a : array int) (z : Z) : Z := (φ (a.[of_Z z])).

Lemma rd_get : forall (a : array int) (i : int), (φ (a.[i])) = rd a (φ i).
Proof. intros. unfold rd. rewrite of_to_Z. reflexivity. Qed.

Lemma rd_set : forall (a : array int) (i b : int) (z : Z),
  0 <= z < wB -> (φ i) < (φ (PArray.length a)) ->
  rd (a.[i <- b]) z = if Z.eq_dec z (φ i) then (φ b) else rd a z.
Proof.
  intros a i b z Hz Hi. unfold rd. destruct (Z.eq_dec z (φ i)) as [E|E].
  - subst. rewrite of_to_Z. rewrite aget_set_same; [reflexivity|].
    rewrite ltb_spec. exact Hi.
  - rewrite aget_set_other; [reflexivity|]. intro F. apply E.
    rewrite F, of_Z_spec, Z.mod_small; lia.
Qed.

Lemma rd_make : forall (n b : int) (z : Z), rd (PArray.make n b) z = (φ b).
Proof. intros. unfold rd. rewrite aget_make. reflexivity. Qed.

Lemma len_set : forall (a : array int) (i b : int),
  PArray.length a.[i <- b] = PArray.length a.
Proof. intros. exact (length_set int a i b). Qed.

Lemma len_make : forall (n b : int), (φ n) <= 4194303 ->
  (φ (PArray.length (PArray.make n b))) = (φ n).
Proof.
  intros n b H. rewrite alength_make.
  replace (n <=? PArray.max_length)%uint63 with true; [reflexivity|].
  symmetry. rewrite leb_spec. exact H.
Qed.

Lemma len_bound : forall (a : array int), (φ (PArray.length a)) <= 4194303.
Proof.
  intros a. pose proof (leb_length int a) as H.
  rewrite leb_spec in H. exact H.
Qed.

Lemma phi_nonneg : forall i : int, 0 <= (φ i).
Proof. intros i. pose proof (to_Z_bounded i). lia. Qed.

Lemma phi_lt : forall i : int, (φ i) < wB.
Proof. intros i. pose proof (to_Z_bounded i). lia. Qed.

Lemma eqb_Z : forall a b : int, (a =? b)%uint63 = ((φ a) =? (φ b))%Z.
Proof.
  intros a b. destruct (a =? b)%uint63 eqn:E; symmetry.
  - rewrite eqb_spec in E. subst. apply Z.eqb_refl.
  - rewrite Z.eqb_neq. intro F. rewrite <- Bool.not_true_iff_false, eqb_spec in E.
    apply E, to_Z_inj, F.
Qed.

Lemma ltb_Z : forall a b : int, (a <? b)%uint63 = ((φ a) <? (φ b))%Z.
Proof.
  intros a b. destruct (a <? b)%uint63 eqn:E; symmetry.
  - rewrite ltb_spec in E. apply Z.ltb_lt. exact E.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E. apply Z.ltb_ge. lia.
Qed.

Lemma leb_Z : forall a b : int, (a <=? b)%uint63 = ((φ a) <=? (φ b))%Z.
Proof.
  intros a b. destruct (a <=? b)%uint63 eqn:E; symmetry.
  - rewrite leb_spec in E. apply Z.leb_le. exact E.
  - rewrite <- Bool.not_true_iff_false, leb_spec in E. apply Z.leb_gt. lia.
Qed.

Fixpoint count (f : Z -> bool) (n : nat) : nat :=
  match n with
  | O => O
  | S n => (count f n + (if f (Z.of_nat n) then 1 else 0))%nat
  end.

Definition cZ (f : Z -> bool) (z : Z) : Z := Z.of_nat (count f (Z.to_nat z)).

Lemma cZ_0 : forall f, cZ f 0 = 0.
Proof. reflexivity. Qed.

Lemma cZ_S : forall f z, 0 <= z -> cZ f (z + 1) = cZ f z + (if f z then 1 else 0).
Proof.
  intros f z Hz. unfold cZ. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
  rewrite Z2Nat.id by lia. destruct (f z); lia.
Qed.

Lemma count_le : forall f n, (count f n <= n)%nat.
Proof. intros f n. induction n; simpl; [lia|]. destruct (f (Z.of_nat n)); lia. Qed.

Lemma cZ_bounds : forall f z, 0 <= z -> 0 <= cZ f z <= z.
Proof. intros f z Hz. unfold cZ. pose proof (count_le f (Z.to_nat z)). lia. Qed.

Lemma count_ext : forall f g n,
  (forall k, (k < n)%nat -> f (Z.of_nat k) = g (Z.of_nat k)) -> count f n = count g n.
Proof.
  intros f g n. induction n; intros H; simpl; [reflexivity|].
  rewrite IHn by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma cZ_ext : forall f g z,
  (forall y, 0 <= y < z -> f y = g y) -> cZ f z = cZ g z.
Proof.
  intros f g z H. unfold cZ. f_equal. apply count_ext. intros k Hk. apply H. lia.
Qed.

Lemma count_upd_le : forall f g n z0,
  (forall k, (k < n)%nat -> Z.of_nat k <> z0 -> g (Z.of_nat k) = f (Z.of_nat k)) ->
  (count g n <= count f n + 1)%nat /\
  (0 <= z0 < Z.of_nat n -> f z0 = false -> g z0 = true -> count g n = S (count f n)).
Proof.
  intros f g n z0. induction n; intros H; simpl.
  - split; [lia|]. intros. lia.
  - destruct IHn as [IH1 IH2]; [intros; apply H; lia|].
    destruct (Z.eq_dec (Z.of_nat n) z0) as [E|E].
    + subst z0. split.
      * assert (count g n = count f n).
        { apply count_ext. intros k Hk. apply H; lia. }
        destruct (g (Z.of_nat n)), (f (Z.of_nat n)); lia.
      * intros _ Hf Hg. rewrite Hf, Hg.
        assert (count g n = count f n).
        { apply count_ext. intros k Hk. apply H; lia. }
        lia.
    + rewrite H by lia. split.
      * destruct (f (Z.of_nat n)); lia.
      * intros Hz Hf Hg. rewrite IH2 by (auto; lia). destruct (f (Z.of_nat n)); lia.
Qed.

Lemma cZ_upd : forall f g z z0, 0 <= z0 < z ->
  (forall y, 0 <= y < z -> y <> z0 -> g y = f y) -> f z0 = false -> g z0 = true ->
  cZ g z = cZ f z + 1.
Proof.
  intros f g z z0 Hz H Hf Hg. unfold cZ.
  destruct (count_upd_le f g (Z.to_nat z) z0) as [_ E].
  - intros k Hk Hk0. apply H; lia.
  - rewrite E by (auto; lia). lia.
Qed.

Lemma cZ_upd_le : forall f g z z0, 0 <= z ->
  (forall y, 0 <= y < z -> y <> z0 -> g y = f y) -> cZ g z <= cZ f z + 1.
Proof.
  intros f g z z0 Hz H. unfold cZ.
  destruct (count_upd_le f g (Z.to_nat z) z0) as [E _].
  - intros k Hk Hk0. apply H; lia.
  - lia.
Qed.

Lemma count_lt : forall f n z0, 0 <= z0 < Z.of_nat n -> f z0 = false -> (count f n < n)%nat.
Proof.
  intros f n z0. induction n; intros Hz Hf; simpl; [lia|].
  destruct (Z.eq_dec (Z.of_nat n) z0) as [E|E].
  - subst. rewrite Hf. pose proof (count_le f n). lia.
  - pose proof (IHn ltac:(lia) Hf). destruct (f (Z.of_nat n)); lia.
Qed.

Lemma cZ_lt : forall f z z0, 0 <= z0 < z -> f z0 = false -> cZ f z < z.
Proof.
  intros f z z0 Hz Hf. unfold cZ.
  pose proof (count_lt f (Z.to_nat z) z0 ltac:(lia) Hf). lia.
Qed.

Lemma count_mono : forall f g n,
  (forall k, (k < n)%nat -> f (Z.of_nat k) = true -> g (Z.of_nat k) = true) ->
  (count f n <= count g n)%nat.
Proof.
  intros f g n. induction n; intros H; simpl; [lia|].
  pose proof (IHn ltac:(intros; apply H; auto; lia)).
  destruct (f (Z.of_nat n)) eqn:E.
  - rewrite (H n) by (auto; lia). lia.
  - destruct (g (Z.of_nat n)); lia.
Qed.

Lemma cZ_mono : forall f g z,
  (forall y, 0 <= y < z -> f y = true -> g y = true) -> cZ f z <= cZ g z.
Proof.
  intros f g z H. unfold cZ.
  pose proof (count_mono f g (Z.to_nat z) ltac:(intros k Hk; apply H; lia)). lia.
Qed.

Lemma count_mono_n : forall f n n', (n <= n')%nat -> (count f n <= count f n')%nat.
Proof.
  intros f n n' H. induction H; [lia|]. simpl. lia.
Qed.

Lemma cZ_mono_n : forall f z z', 0 <= z <= z' -> cZ f z <= cZ f z'.
Proof.
  intros f z z' H. unfold cZ. pose proof (count_mono_n f (Z.to_nat z) (Z.to_nat z')). lia.
Qed.

Lemma count_or : forall f g n,
  (forall y, f y = true -> g y = true -> False) ->
  count (fun y => orb (f y) (g y)) n = (count f n + count g n)%nat.
Proof.
  intros f g n H. induction n; simpl; [reflexivity|]. rewrite IHn.
  destruct (f (Z.of_nat n)) eqn:E1, (g (Z.of_nat n)) eqn:E2; simpl;
    [exfalso; eapply H; eauto | lia | lia | lia].
Qed.

Fixpoint psum (g : Z -> Z) (n : nat) : Z :=
  match n with
  | O => 0
  | S n => psum g n + g (Z.of_nat n)
  end.

Definition pZ (g : Z -> Z) (z : Z) : Z := psum g (Z.to_nat z).

Lemma pZ_S : forall g z, 0 <= z -> pZ g (z + 1) = pZ g z + g z.
Proof.
  intros g z Hz. unfold pZ. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. simpl.
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma pZ_mono : forall g a b, (forall y, 0 <= y -> 0 <= g y) -> 0 <= a <= b -> pZ g a <= pZ g b.
Proof.
  intros g a b Hg Hab. unfold pZ.
  assert (forall n n', (n <= n')%nat -> psum g n <= psum g n').
  { intros n n' H. induction H; [lia|]. simpl. pose proof (Hg (Z.of_nat m) ltac:(lia)). lia. }
  apply H. lia.
Qed.

Lemma phi_NV : (φ NV) = 1000. Proof. reflexivity. Qed.
Lemma phi_NP : (φ NP) = 1001. Proof. reflexivity. Qed.
Lemma phi_NM : (φ NM) = 2000. Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The adjacency (CSR) of the teams not owned by ex                    *)
(* ------------------------------------------------------------------ *)

(* Left vertex u is joined to right vertex v. *)
Definition Gx (x y : array int) (ex : int) (u v : Z) : Prop :=
  exists j, 0 <= j < (φ (PArray.length x)) /\ rd x j <> (φ ex) /\
            rd x j = 1000 + u /\ rd y j = 2000 + v.

Definition own_p (x : array int) (ex : int) (u : Z) : Z -> bool :=
  fun j => negb (rd x j =? (φ ex)) && (rd x j =? 1000 + u).

Definition dg (x : array int) (ex : int) (u : Z) : Z :=
  cZ (own_p x ex u) (φ (PArray.length x)).

Definition SS (x : array int) (ex : int) : Z -> Z := pZ (dg x ex).

Definition below_p (x : array int) (ex : int) (U : Z) : Z -> bool :=
  fun j => negb (rd x j =? (φ ex)) && (1000 <=? rd x j) && (rd x j <? 1000 + U).

Section Graph.
Variables (x y : array int) (ex : int).
Local Notation M := (φ (PArray.length x)).
Hypothesis Hlen : PArray.length y = PArray.length x.
Hypothesis Hrange : forall j, 0 <= j < M -> 1000 <= rd x j <= 1999 /\ 2000 <= rd y j <= 2999.

Lemma own_kept : forall u j, rd x j <> (φ ex) -> own_p x ex u j = (rd x j =? 1000 + u).
Proof. intros u j H. unfold own_p. apply Z.eqb_neq in H. rewrite H. reflexivity. Qed.

Lemma own_notkept : forall u j, rd x j = (φ ex) -> own_p x ex u j = false.
Proof. intros u j H. unfold own_p. rewrite H, Z.eqb_refl. reflexivity. Qed.

Lemma dg_nonneg : forall u, 0 <= dg x ex u.
Proof. intros u. unfold dg. pose proof (cZ_bounds (own_p x ex u) M (phi_nonneg _)). lia. Qed.

Lemma SS_S : forall u, 0 <= u -> SS x ex (u + 1) = SS x ex u + dg x ex u.
Proof. intros u Hu. unfold SS. apply pZ_S. exact Hu. Qed.

Lemma SS_mono : forall a b, 0 <= a <= b -> SS x ex a <= SS x ex b.
Proof. intros a b H. unfold SS. apply pZ_mono; [intros; apply dg_nonneg | exact H]. Qed.

Lemma SS_0 : SS x ex 0 = 0.
Proof. reflexivity. Qed.

Lemma SS_below : forall U, 0 <= U -> SS x ex U = cZ (below_p x ex U) M.
Proof.
  intros U HU. pattern U. apply natlike_ind; [| | exact HU].
  - unfold SS, pZ. simpl. unfold cZ.
    assert (E : forall n, count (below_p x ex 0) n = 0%nat).
    { induction n; [reflexivity|]. cbn [count]. rewrite IHn. unfold below_p.
      destruct (rd x (Z.of_nat n) =? (φ ex)), (1000 <=? rd x (Z.of_nat n)) eqn:E1,
        (rd x (Z.of_nat n) <? 1000 + 0) eqn:E2; cbn [negb andb orb]; try reflexivity.
      rewrite Z.leb_le in E1. rewrite Z.ltb_lt in E2. lia. }
    rewrite E. reflexivity.
  - intros V HV IH. rewrite <- Z.add_1_r, SS_S by exact HV. rewrite IH. unfold dg, cZ.
    rewrite <- Nat2Z.inj_add, <- count_or.
    + f_equal. apply count_ext. intros k Hk. unfold below_p, own_p.
      destruct (rd x (Z.of_nat k) =? (φ ex)); cbn [negb andb orb]; [reflexivity|].
      destruct (Z.leb_spec 1000 (rd x (Z.of_nat k))),
               (Z.ltb_spec (rd x (Z.of_nat k)) (1000 + V)),
               (Z.ltb_spec (rd x (Z.of_nat k)) (1000 + (V + 1))),
               (Z.eqb_spec (rd x (Z.of_nat k)) (1000 + V)); cbn [negb andb orb]; try reflexivity; lia.
    + intros j. unfold below_p, own_p.
      destruct (rd x j =? (φ ex)); cbn [negb andb orb]; [discriminate|].
      destruct (Z.leb_spec 1000 (rd x j)), (Z.ltb_spec (rd x j) (1000 + V)),
               (Z.eqb_spec (rd x j) (1000 + V)); cbn [negb andb orb]; try discriminate; lia.
Qed.

Lemma SS_nonneg : forall u, 0 <= u -> 0 <= SS x ex u.
Proof. intros u Hu. rewrite <- SS_0. apply SS_mono. lia. Qed.

Lemma SS_bound : forall U, 0 <= U -> SS x ex U <= M.
Proof.
  intros U HU. rewrite SS_below by exact HU.
  pose proof (cZ_bounds (below_p x ex U) M (phi_nonneg _)). lia.
Qed.

Lemma deg_loop_spec : forall z k d H, gap (PArray.length x) k = z ->
  (φ k) <= M -> (φ (PArray.length d)) = 1000 ->
  (forall u, 0 <= u < 1000 -> rd d u = cZ (own_p x ex u) (φ k)) ->
  forall u, 0 <= u < 1000 -> rd (deg_loop x ex (PArray.length x) k d H) u = dg x ex u.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k d H Hz Hk Hd Hinv.
  rewrite deg_loop_eq.
  destruct (bdec (k <? PArray.length x)%uint63) as [Hk' | Hk'].
  - pose proof Hk' as Hk''. rewrite ltb_spec in Hk''.
    assert (Hk1 : (φ (k + 1)) = (φ k) + 1) by sia.
    pose proof (Hrange (φ k) ltac:(pose proof (phi_nonneg k); lia)) as [Rx Ry].
    pose proof (phi_nonneg k) as Pk.
    cbv zeta.
    destruct (x.[k] =? ex)%uint63 eqn:Ea.
    + rewrite eqb_spec in Ea.
      eapply IH; [ | reflexivity | lia | exact Hd | ].
      * rewrite <- Hz. apply dec_step. exact Hk'.
      * intros u Hu. rewrite Hk1, cZ_S by lia. rewrite own_notkept by (rewrite <- rd_get, Ea; reflexivity).
        rewrite Hinv by exact Hu. lia.
    + rewrite eqb_Z, Z.eqb_neq in Ea. rewrite rd_get in Ea.
      assert (Hu0 : (φ (x.[k] - 1000)) = rd x (φ k) - 1000) by (rewrite <- rd_get in Rx |- *; sia).
      eapply IH; [ | reflexivity | lia | | ].
      * rewrite <- Hz. apply dec_step. exact Hk'.
      * rewrite len_set. exact Hd.
      * intros u Hu. rewrite Hk1, cZ_S by lia. rewrite own_kept by exact Ea.
        rewrite rd_set by (rewrite ?Hd, ?Hu0; lia || (rewrite wB_val; lia)).
        rewrite Hu0. destruct (Z.eq_dec u (rd x (φ k) - 1000)) as [E|E].
        -- subst u. replace (rd x (φ k) =? 1000 + (rd x (φ k) - 1000)) with true
             by (symmetry; apply Z.eqb_eq; lia).
           assert (B := cZ_bounds (own_p x ex (rd x (φ k) - 1000)) (φ k) Pk).
           rewrite add_spec, rd_get, Hu0, Hinv by lia.
           change (φ 1) with 1. rewrite Z.mod_small; [lia|].
           rewrite wB_val. pose proof (len_bound x). lia.
        -- replace (rd x (φ k) =? 1000 + u) with false by (symmetry; apply Z.eqb_neq; lia).
           rewrite Hinv by exact Hu. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk'.
    intros u Hu. rewrite Hinv by exact Hu. unfold dg. f_equal. lia.
Qed.

Lemma own_step : forall k u, 0 <= k -> rd x k <> (φ ex) ->
  cZ (own_p x ex u) (k + 1) =
  cZ (own_p x ex u) k + (if Z.eq_dec u (rd x k - 1000) then 1 else 0).
Proof.
  intros k u Hk H. rewrite cZ_S by exact Hk. rewrite own_kept by exact H.
  destruct (Z.eq_dec u (rd x k - 1000)) as [E|E].
  - replace (rd x k =? 1000 + u) with true by (symmetry; apply Z.eqb_eq; lia). reflexivity.
  - replace (rd x k =? 1000 + u) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
Qed.

Lemma own_step_nk : forall k u, 0 <= k -> rd x k = (φ ex) ->
  cZ (own_p x ex u) (k + 1) = cZ (own_p x ex u) k.
Proof.
  intros k u Hk H. rewrite cZ_S by exact Hk. rewrite own_notkept by exact H. lia.
Qed.

Lemma own_le_dg : forall k u, 0 <= k <= M -> cZ (own_p x ex u) k <= dg x ex u.
Proof. intros k u H. unfold dg. apply cZ_mono_n. lia. Qed.

Lemma SS_disj : forall u u0 p, 0 <= u < 1000 -> 0 <= u0 < 1000 -> u <> u0 ->
  SS x ex u <= p < SS x ex (u + 1) -> SS x ex u0 <= p < SS x ex (u0 + 1) -> False.
Proof.
  intros u u0 p Hu Hu0 Hne H1 H2.
  destruct (Z.lt_ge_cases u u0).
  - pose proof (SS_mono (u + 1) u0 ltac:(lia)). lia.
  - pose proof (SS_mono (u0 + 1) u ltac:(lia)). lia.
Qed.

Lemma off_loop_spec : forall (d : array int),
  (forall u, 0 <= u < 1000 -> rd d u = dg x ex u) ->
  forall z u o H, gap NV u = z ->
  0 <= (φ u) <= 1000 -> (φ (PArray.length o)) = 1001 ->
  (forall u', 0 <= u' <= (φ u) -> rd o u' = SS x ex u') ->
  (φ (PArray.length (off_loop d u o H))) = 1001 /\
  forall u', 0 <= u' <= 1000 -> rd (off_loop d u o H) u' = SS x ex u'.
Proof.
  intros d Hd z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u o H Hz Hu Ho Hinv.
  rewrite off_loop_eq.
  destruct (bdec (u <? NV)%uint63) as [Hu' | Hu'].
  - pose proof Hu' as Hu''. rewrite ltb_spec, phi_NV in Hu''.
    assert (Hu1 : (φ (u + 1)) = (φ u) + 1) by sia.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply dec_step. exact Hu'.
    + rewrite len_set. exact Ho.
    + intros u' Hu'1. rewrite rd_set by (rewrite ?Ho, ?Hu1; rewrite ?wB_val; lia).
      rewrite Hu1. destruct (Z.eq_dec u' ((φ u) + 1)) as [E|E].
      * subst u'. rewrite add_spec, !rd_get, Hinv, Hd by lia.
        rewrite SS_S by lia. apply Z.mod_small.
        pose proof (SS_bound ((φ u) + 1) ltac:(lia)). rewrite SS_S in H0 by lia.
        pose proof (dg_nonneg (φ u)). pose proof (SS_mono 0 (φ u) ltac:(lia)).
        rewrite SS_0 in H2. pose proof (len_bound x). rewrite wB_val. lia.
      * apply Hinv. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV in Hu'.
    split; [exact Ho|]. intros u' Hu'1. apply Hinv. lia.
Qed.

Definition FillOK (r : array int) : Prop :=
  (φ (PArray.length r)) = M /\
  (forall u p, 0 <= u < 1000 -> SS x ex u <= p < SS x ex (u + 1) ->
     0 <= rd r p < 1000 /\ Gx x y ex u (rd r p)) /\
  (forall j, 0 <= j < M -> rd x j <> (φ ex) ->
     exists p, SS x ex (rd x j - 1000) <= p < SS x ex (rd x j - 1000 + 1) /\
               rd r p = rd y j - 2000).

Lemma fill_loop_spec : forall z k pos tg H, gap (PArray.length x) k = z ->
  (φ k) <= M -> (φ (PArray.length pos)) = 1001 -> (φ (PArray.length tg)) = M ->
  (forall u, 0 <= u < 1000 -> rd pos u = SS x ex u + cZ (own_p x ex u) (φ k)) ->
  (forall u p, 0 <= u < 1000 -> SS x ex u <= p < SS x ex u + cZ (own_p x ex u) (φ k) ->
     0 <= rd tg p < 1000 /\ Gx x y ex u (rd tg p)) ->
  (forall j, 0 <= j < (φ k) -> rd x j <> (φ ex) ->
     exists p, SS x ex (rd x j - 1000) <= p <
               SS x ex (rd x j - 1000) + cZ (own_p x ex (rd x j - 1000)) (φ k)
               /\ rd tg p = rd y j - 2000) ->
  FillOK (fill_loop x y ex (PArray.length x) k pos tg H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k pos tg H Hz Hk Hpl Htl F1 F2 F3.
  rewrite fill_loop_eq.
  pose proof (phi_nonneg k) as Pk.
  destruct (bdec (k <? PArray.length x)%uint63) as [Hk' | Hk'].
  - pose proof Hk' as Hk''. rewrite ltb_spec in Hk''.
    assert (Hk1 : (φ (k + 1)) = (φ k) + 1) by sia.
    pose proof (Hrange (φ k) ltac:(lia)) as [Rx Ry].
    cbv zeta.
    destruct (x.[k] =? ex)%uint63 eqn:Ea.
    + rewrite eqb_spec in Ea.
      assert (Ea' : rd x (φ k) = (φ ex)) by (rewrite <- rd_get, Ea; reflexivity).
      eapply IH; [ | reflexivity | lia | exact Hpl | exact Htl | | | ].
      * rewrite <- Hz. apply dec_step. exact Hk'.
      * intros u Hu. rewrite Hk1, own_step_nk by (exact Pk || exact Ea'). apply F1, Hu.
      * intros u p Hu Hp. rewrite Hk1, own_step_nk in Hp by (exact Pk || exact Ea').
        apply F2; auto.
      * intros j Hj Hjx. rewrite Hk1, own_step_nk by (exact Pk || exact Ea').
        destruct (Z.eq_dec j (φ k)) as [E|E]; [subst; contradiction|].
        apply F3; [lia | exact Hjx].
    + rewrite eqb_Z, Z.eqb_neq, rd_get in Ea.
      set (u0 := rd x (φ k) - 1000).
      assert (Hu0 : (φ (x.[k] - 1000)) = u0) by (unfold u0; rewrite <- rd_get in Rx |- *; sia).
      assert (Hu0r : 0 <= u0 < 1000) by (unfold u0; lia).
      assert (Hp0 : (φ (pos.[x.[k] - 1000])) = SS x ex u0 + cZ (own_p x ex u0) (φ k))
        by (rewrite rd_get, Hu0; apply F1; exact Hu0r).
      set (c0 := cZ (own_p x ex u0) (φ k)) in *.
      assert (Hc0n : 0 <= c0) by (unfold c0; apply cZ_bounds; exact Pk).
      assert (Hc0 : c0 + 1 <= dg x ex u0).
      { pose proof (own_step (φ k) u0 Pk Ea) as E.
        destruct (Z.eq_dec u0 (rd x (φ k) - 1000)) as [_|F]; [|exfalso; apply F; reflexivity].
        fold c0 in E. rewrite <- E. apply own_le_dg. lia. }
      assert (HS1 : SS x ex (u0 + 1) = SS x ex u0 + dg x ex u0) by (apply SS_S; lia).
      assert (HSb : SS x ex (u0 + 1) <= M) by (apply SS_bound; lia).
      assert (Hy : (φ (y.[k] - 2000)) = rd y (φ k) - 2000)
        by (rewrite <- rd_get in Ry |- *; sia).
      set (p0 := SS x ex u0 + c0) in *.
      assert (Hp0b : 0 <= p0 < M).
      { unfold p0. pose proof (SS_mono 0 u0 ltac:(lia)). rewrite SS_0 in H0.
        pose proof (cZ_bounds (own_p x ex u0) (φ k) Pk). fold c0 in H1. lia. }
      (* the range of u, extended by one step *)
      assert (Ext : forall u, 0 <= u < 1000 ->
                cZ (own_p x ex u) ((φ k) + 1) = cZ (own_p x ex u) (φ k) + (if Z.eq_dec u u0 then 1 else 0)).
      { intros u Hu. rewrite own_step by (exact Pk || exact Ea). reflexivity. }
      assert (Rng : forall u p, 0 <= u < 1000 ->
                SS x ex u <= p < SS x ex u + cZ (own_p x ex u) ((φ k) + 1) ->
                SS x ex u <= p < SS x ex (u + 1)).
      { intros u p Hu Hp. rewrite SS_S by lia.
        pose proof (own_le_dg ((φ k) + 1) u ltac:(lia)). lia. }
      assert (Rng0 : SS x ex u0 <= p0 < SS x ex (u0 + 1))
        by (unfold p0; lia).
      eapply IH; [ | reflexivity | lia | | | | | ].
      * rewrite <- Hz. apply dec_step. exact Hk'.
      * rewrite len_set. exact Hpl.
      * rewrite len_set. exact Htl.
      * intros u Hu. rewrite Hk1, Ext by exact Hu.
        rewrite rd_set by (rewrite ?Hpl, ?Hu0; rewrite ?wB_val; lia).
        rewrite Hu0. destruct (Z.eq_dec u u0) as [E|E].
        -- subst u. rewrite add_spec, Hp0. change (φ 1) with 1.
           rewrite Z.mod_small; [lia|]. rewrite wB_val. pose proof (len_bound x). lia.
        -- rewrite F1 by exact Hu. lia.
      * intros u p Hu Hp. rewrite Hk1 in Hp.
        pose proof (Rng u p Hu Hp) as Hr.
        pose proof (SS_nonneg u ltac:(lia)). pose proof (SS_bound (u + 1) ltac:(lia)).
        rewrite rd_set by (rewrite ?Htl, ?Hp0; rewrite ?wB_val; pose proof (len_bound x); lia).
        rewrite Hp0. fold p0. destruct (Z.eq_dec p p0) as [E|E].
        -- subst p. destruct (Z.eq_dec u u0) as [Eu|Eu];
             [| exfalso; exact (SS_disj u u0 p0 Hu Hu0r Eu Hr Rng0)].
           subst u. rewrite Hy. split; [lia|].
           exists (φ k). repeat split; try lia; exact Ea.
        -- apply F2; [exact Hu|]. rewrite Ext in Hp by exact Hu.
           destruct (Z.eq_dec u u0); [subst u; unfold p0 in E; lia | lia].
      * intros j Hj Hjx. rewrite Hk1 in Hj |- *.
        destruct (Z.eq_dec j (φ k)) as [E|E].
        -- subst j. fold u0. exists p0. split.
           ++ rewrite Ext by exact Hu0r. destruct (Z.eq_dec u0 u0) as [_|F]; [|congruence].
              unfold p0. lia.
           ++ rewrite rd_set by (rewrite ?Htl, ?Hp0; rewrite ?wB_val; pose proof (len_bound x); lia).
              rewrite Hp0. fold p0. destruct (Z.eq_dec p0 p0) as [_|F]; [|congruence].
              exact Hy.
        -- destruct (F3 j ltac:(lia) Hjx) as (p & Hp & Hv).
           pose proof (Hrange j ltac:(lia)) as [Rxj _].
           exists p. rewrite Ext by lia.
           assert (Hp' : SS x ex (rd x j - 1000) <= p < SS x ex (rd x j - 1000 + 1)).
           { rewrite SS_S by lia. pose proof (own_le_dg (φ k) (rd x j - 1000) ltac:(lia)). lia. }
           assert (Hne : p <> p0).
           { intro Ep. subst p. destruct (Z.eq_dec (rd x j - 1000) u0) as [Eu|Eu].
             - rewrite Eu in Hp. unfold p0 in Hp. lia.
             - exact (SS_disj (rd x j - 1000) u0 p0 ltac:(lia) Hu0r Eu Hp' Rng0). }
           split; [destruct (Z.eq_dec (rd x j - 1000) u0); lia|].
           pose proof (SS_nonneg (rd x j - 1000) ltac:(lia)).
           pose proof (SS_bound (rd x j - 1000 + 1) ltac:(lia)).
           rewrite rd_set by (rewrite ?Htl, ?Hp0; rewrite ?wB_val; pose proof (len_bound x); lia).
           rewrite Hp0. fold p0. destruct (Z.eq_dec p p0) as [F|_]; [congruence|]. exact Hv.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk'.
    assert (Ek : (φ k) = M) by lia.
    split; [exact Htl|]. split.
    + intros u p Hu Hp. apply F2; [exact Hu|]. rewrite SS_S in Hp by lia. unfold dg in Hp.
      rewrite Ek. exact Hp.
    + intros j Hj Hjx. destruct (F3 j ltac:(lia) Hjx) as (p & Hp & Hv).
      pose proof (Hrange j Hj) as [Rxj _].
      exists p. rewrite SS_S by lia. unfold dg. rewrite <- Ek. split; [lia | exact Hv].
Qed.

End Graph.

(* ------------------------------------------------------------------ *)
(* The search queue                                                    *)
(* ------------------------------------------------------------------ *)

Definition visb (qp : array int) : Z -> bool := fun u => negb (rd qp u =? 0).
Definition matb (mL : array int) : Z -> bool := fun u => rd mL u <? 1000.
Definition sizeL (mL : array int) : Z := cZ (matb mL) 1000.

Lemma phi_add1 : forall i : int, (φ i) < 4194304 -> (φ (i + 1))%uint63 = (φ i) + 1.
Proof. intros i H. rewrite add_spec. change ((φ 1)%uint63) with 1. apply Z.mod_small.
  pose proof (phi_nonneg i). rewrite wB_val. lia. Qed.

Lemma phi_sub1 : forall i : int, (φ i) <> 0 -> (φ (i - 1))%uint63 = (φ i) - 1.
Proof. intros i H. rewrite sub_spec. change ((φ 1)%uint63) with 1. apply Z.mod_small.
  pose proof (to_Z_bounded i). lia. Qed.

Lemma rd_nonneg : forall a z, 0 <= rd a z.
Proof. intros. unfold rd. apply phi_nonneg. Qed.

Definition QInv (t : Z) (Q qp : array int) : Prop :=
  (φ (PArray.length Q)) = 1000 /\ (φ (PArray.length qp)) = 1000 /\
  (forall i, 0 <= i < t -> 0 <= rd Q i < 1000 /\ rd qp (rd Q i) = i + 1) /\
  (forall u, 0 <= u < 1000 -> rd qp u <> 0 -> rd qp u <= t /\ rd Q (rd qp u - 1) = u) /\
  t = cZ (visb qp) 1000.

Lemma QInv_t : forall t Q qp, QInv t Q qp -> 0 <= t <= 1000.
Proof.
  intros t Q qp (_ & _ & _ & _ & E). subst. apply cZ_bounds. lia.
Qed.

Lemma push_ok : forall (t w : int) (Q qp : array int),
  QInv (φ t) Q qp -> 0 <= (φ w) < 1000 -> rd qp (φ w) = 0 ->
  (φ (t + 1)) = (φ t) + 1 /\ (φ t) < 1000 /\
  QInv ((φ t) + 1) Q.[t <- w] qp.[w <- (t + 1)%uint63] /\
  (forall u, 0 <= u < 1000 ->
     rd qp.[w <- (t + 1)%uint63] u = if Z.eq_dec u (φ w) then (φ t) + 1 else rd qp u).
Proof.
  intros t w Q qp HQ Hw H0.
  pose proof HQ as (HlQ & Hlq & Q2 & Q3 & Q4).
  assert (Ht : (φ t) < 1000).
  { rewrite Q4. apply (cZ_lt _ _ (φ w)); [lia|]. unfold visb. rewrite H0. reflexivity. }
  assert (Ht1 : (φ (t + 1)) = (φ t) + 1) by sia.
  assert (Rq : forall u, 0 <= u < 1000 ->
     rd qp.[w <- (t + 1)%uint63] u = if Z.eq_dec u (φ w) then (φ t) + 1 else rd qp u).
  { intros u Hu. rewrite rd_set by (rewrite ?Hlq; rewrite ?wB_val; lia).
    destruct (Z.eq_dec u (φ w)); [exact Ht1 | reflexivity]. }
  assert (RQ : forall i, 0 <= i < 1000 ->
     rd Q.[t <- w] i = if Z.eq_dec i (φ t) then (φ w) else rd Q i).
  { intros i Hi. rewrite rd_set by (rewrite ?HlQ; rewrite ?wB_val; lia). reflexivity. }
  split; [exact Ht1|]. split; [exact Ht|]. split; [|exact Rq].
  split; [rewrite len_set; exact HlQ|].
  split; [rewrite len_set; exact Hlq|].
  split; [|split].
  - intros i Hi. rewrite RQ by lia. destruct (Z.eq_dec i (φ t)) as [E|E].
    + rewrite Rq by lia. destruct (Z.eq_dec (φ w) (φ w)); [lia|congruence].
    + destruct (Q2 i ltac:(lia)) as [B1 B2]. split; [exact B1|].
      rewrite Rq by lia. destruct (Z.eq_dec (rd Q i) (φ w)) as [E2|E2]; [|exact B2].
      rewrite E2, H0 in B2. lia.
  - intros u Hu Hne. rewrite Rq in Hne |- * by exact Hu.
    destruct (Z.eq_dec u (φ w)) as [E|E].
    + split; [lia|]. rewrite RQ by lia. replace ((φ t) + 1 - 1) with (φ t) by lia.
      destruct (Z.eq_dec (φ t) (φ t)); [lia|congruence].
    + destruct (Q3 u Hu Hne) as [B1 B2]. split; [lia|].
      pose proof (rd_nonneg qp u).
      rewrite RQ by lia. destruct (Z.eq_dec (rd qp u - 1) (φ t)); [lia|exact B2].
  - rewrite (cZ_upd (visb qp) (visb qp.[w <- (t + 1)%uint63]) 1000 (φ w)); [lia|lia| | |].
    + intros u Hu Hne. unfold visb. rewrite Rq by exact Hu.
      destruct (Z.eq_dec u (φ w)); [congruence|reflexivity].
    + unfold visb. rewrite H0. reflexivity.
    + unfold visb. rewrite Rq by lia. destruct (Z.eq_dec (φ w) (φ w)); [|congruence].
      replace ((φ t) + 1 =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (phi_nonneg t); lia).
      reflexivity.
Qed.

Definition RootOK (mL : array int) (r : array int * array int * int) : Prop :=
  match r with (Q, qp, t) =>
    QInv (φ t) Q qp /\
    (forall u, 0 <= u < 1000 -> 1000 <= rd mL u -> rd qp u <> 0) /\
    (forall u, 0 <= u < 1000 -> rd qp u <> 0 -> 1000 <= rd mL u)
  end.

Lemma root_loop_spec : forall mL z u Q qp t H, gap NV u = z ->
  0 <= (φ u) <= 1000 -> QInv (φ t) Q qp ->
  (forall u', (φ u) <= u' < 1000 -> rd qp u' = 0) ->
  (forall u', 0 <= u' < (φ u) -> 1000 <= rd mL u' -> rd qp u' <> 0) ->
  (forall u', 0 <= u' < 1000 -> rd qp u' <> 0 -> 1000 <= rd mL u') ->
  RootOK mL (root_loop mL u Q qp t H).
Proof.
  intros mL z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u Q qp t H Hz Hu HQ Hfree Hroots Hvis.
  rewrite root_loop_eq.
  destruct (bdec (u <? NV)%uint63) as [Hu' | Hu'].
  - pose proof Hu' as Hu''. rewrite ltb_spec, phi_NV in Hu''.
    assert (Hu1 : (φ (u + 1)) = (φ u) + 1) by sia.
    destruct (mL.[u] <? NV)%uint63 eqn:Em.
    + rewrite ltb_spec, phi_NV, rd_get in Em.
      eapply IH; [ | reflexivity | lia | exact HQ | | | exact Hvis].
      * rewrite <- Hz. apply dec_step. exact Hu'.
      * intros u' Hu'1. apply Hfree. lia.
      * intros u' Hu'1 Hr. destruct (Z.eq_dec u' (φ u)); [subst; lia|]. apply Hroots; lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV, rd_get in Em.
      destruct (push_ok t u Q qp HQ ltac:(lia) ltac:(apply Hfree; lia)) as (Ht1 & Ht & HQ' & Rq).
      eapply IH; [ | reflexivity | lia | rewrite Ht1; exact HQ' | | | ].
      * rewrite <- Hz. apply dec_step. exact Hu'.
      * intros u' Hu'1. rewrite Rq by lia. destruct (Z.eq_dec u' (φ u)); [lia|]. apply Hfree. lia.
      * intros u' Hu'1 Hr. rewrite Rq by lia. destruct (Z.eq_dec u' (φ u)); [lia|]. apply Hroots; lia.
      * intros u' Hu'1 Hr. rewrite Rq in Hr by lia. destruct (Z.eq_dec u' (φ u)); [subst; lia|].
        apply Hvis; auto.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV in Hu'.
    split; [exact HQ|]. split; [|exact Hvis].
    intros u' Hu'1 Hr. apply Hroots; lia.
Qed.

Lemma cZ_false : forall f z, 0 <= z -> (forall y, 0 <= y < z -> f y = false) -> cZ f z = 0.
Proof.
  intros f z Hz H. rewrite (cZ_ext f (fun _ => false)) by exact H.
  unfold cZ. generalize (Z.to_nat z). intros n. induction n; simpl; [reflexivity|].
  rewrite Nat.add_0_r. exact IHn.
Qed.

Ltac rset := rewrite rd_set by (rewrite ?len_set, ?wB_val; lia).

Lemma QInv0 : QInv 0 (PArray.make NV 0%uint63) (PArray.make NV 0%uint63).
Proof.
  split; [rewrite len_make by (rewrite phi_NV; lia); reflexivity|].
  split; [rewrite len_make by (rewrite phi_NV; lia); reflexivity|].
  split; [intros; lia|]. split.
  - intros u _ Hn. rewrite rd_make in Hn. contradiction.
  - symmetry. apply cZ_false; [lia|]. intros y _. unfold visb. rewrite rd_make. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The output list                                                     *)
(* ------------------------------------------------------------------ *)

(* The employees 1000 + i, i < n, whose index is selected by f. *)
Fixpoint ml (f : Z -> bool) (n : nat) : list Z :=
  match n with
  | O => []
  | S n => ml f n ++ (if f (Z.of_nat n) then [1000 + Z.of_nat n] else [])
  end.

Lemma ml_In : forall f n a, In a (ml f n) <-> exists i, 0 <= i < Z.of_nat n /\ f i = true /\ a = 1000 + i.
Proof.
  intros f n a. induction n; simpl.
  - split; [intros []|]. intros (i & Hi & _). lia.
  - rewrite in_app_iff, IHn. split.
    + intros [(i & Hi & Hf & Ha) | H].
      * exists i. split; [lia|auto].
      * destruct (f (Z.of_nat n)) eqn:E; [|destruct H].
        destruct H as [H|[]]. exists (Z.of_nat n). split; [lia|auto].
    + intros (i & Hi & Hf & Ha). destruct (Z.eq_dec i (Z.of_nat n)) as [E|E].
      * right. subst i. rewrite Hf. left. auto.
      * left. exists i. split; [lia|auto].
Qed.

Lemma ml_NoDup : forall f n, NoDup (ml f n).
Proof.
  intros f n. induction n; cbn [ml]; [constructor|].
  apply NoDup_app; [exact IHn| |].
  - destruct (f (Z.of_nat n)); [|constructor]. constructor; [intros []|constructor].
  - intros a Ha Hb. destruct (f (Z.of_nat n)); [|destruct Hb].
    destruct Hb as [Hb|[]]. subst a. apply ml_In in Ha. destruct Ha as (i & Hi & _ & Ha). lia.
Qed.

Lemma ml_length : forall f n, List.length (ml f n) = count f n.
Proof.
  intros f n. induction n; simpl; [reflexivity|].
  rewrite length_app, IHn. destruct (f (Z.of_nat n)); reflexivity.
Qed.

Lemma NoDup_map_on : forall {A B} (f : A -> B) (l : list A), NoDup l ->
  (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup (map f l).
Proof.
  intros A B f l Hl. induction Hl as [|a l Ha Hl IH]; intros Hi; simpl; constructor.
  - intros F. apply in_map_iff in F. destruct F as (b & Hb & Hbl).
    assert (b = a) by (apply Hi; simpl; auto). subst. contradiction.
  - apply IH. intros a0 b0 H1 H2 E. apply Hi; simpl; auto.
Qed.

Definition mkb (mk : array int) : Z -> bool := fun i => negb (rd mk i =? 0).

(* ------------------------------------------------------------------ *)
(* The matching, over an abstract graph given by its adjacency         *)
(* ------------------------------------------------------------------ *)

Section Match.
Variable G : Z -> Z -> Prop.
Variables off tg : array int.
Hypothesis Hoff : (φ (PArray.length off)) = 1001.
Hypothesis C1 : forall u, 0 <= u < 1000 ->
  0 <= rd off u <= rd off (u + 1) /\ rd off (u + 1) <= (φ (PArray.length tg)).
Hypothesis C2 : forall u p, 0 <= u < 1000 -> rd off u <= p < rd off (u + 1) ->
  0 <= rd tg p < 1000 /\ G u (rd tg p).
Hypothesis C3 : forall u v, G u v ->
  0 <= u < 1000 /\ 0 <= v < 1000 /\ exists p, rd off u <= p < rd off (u + 1) /\ rd tg p = v.

(* mL / mR: the mates of the left / right vertices, >= 1000 for none. *)
Definition Mat (mL mR : array int) : Prop :=
  (φ (PArray.length mL)) = 1000 /\ (φ (PArray.length mR)) = 1000 /\
  (forall u w, 0 <= u < 1000 -> 0 <= w < 1000 -> (rd mL u = w <-> rd mR w = u)) /\
  (forall w, 0 <= w < 1000 -> rd mR w < 1000 -> G (rd mR w) w).

Definition PInv (mL : array int) (qp pr : array int) : Prop :=
  (φ (PArray.length pr)) = 1000 /\
  (forall v, 0 <= v < 1000 -> rd pr v <> 0 ->
     0 <= rd pr v - 1 < 1000 /\ rd qp (rd pr v - 1) <> 0 /\ G (rd pr v - 1) v) /\
  (forall u, 0 <= u < 1000 -> rd qp u <> 0 -> rd mL u < 1000 ->
     rd pr (rd mL u) <> 0 /\ rd qp (rd pr (rd mL u) - 1) < rd qp u).

Definition P2 (mR qp pr : array int) : Prop :=
  forall v, 0 <= v < 1000 -> rd pr v <> 0 -> rd mR v < 1000 /\ rd qp (rd mR v) <> 0.

Definition Roots (mL qp : array int) : Prop :=
  forall u, 0 <= u < 1000 -> 1000 <= rd mL u -> rd qp u <> 0.

Definition BInv (mL mR : array int) (h t : Z) (Q qp pr : array int) : Prop :=
  0 <= h <= t /\ QInv t Q qp /\ Roots mL qp /\ PInv mL qp pr /\ P2 mR qp pr /\
  (forall i, 0 <= i < h -> forall v, G (rd Q i) v -> rd pr v <> 0).

Definition FoundOK (mL mR : array int) (v : int) (qp pr : array int) : Prop :=
  (φ (PArray.length qp)) = 1000 /\ 0 <= (φ v) < 1000 /\ rd pr (φ v) <> 0 /\
  1000 <= rd mR (φ v) /\ PInv mL qp pr.

Definition FailOK (mL mR : array int) (qp pr : array int) : Prop :=
  (φ (PArray.length qp)) = 1000 /\ (φ (PArray.length pr)) = 1000 /\
  Roots mL qp /\ P2 mR qp pr /\
  (forall u v, 0 <= u < 1000 -> rd qp u <> 0 -> G u v -> rd pr v <> 0).

Definition ScanOK (mL mR : array int) (h : Z) (r : sres) : Prop :=
  match r with
  | SFound v qp pr => FoundOK mL mR v qp pr
  | SCont Q qp pr t => BInv mL mR (h + 1) (φ t) Q qp pr
  end.

Lemma scan_spec : forall mL mR (h : Z) (u : int), Mat mL mR -> 0 <= (φ u) < 1000 ->
  forall z (pe p : int) Q qp pr t H, gap pe p = z ->
  (φ pe) = rd off ((φ u) + 1) ->
  BInv mL mR h (φ t) Q qp pr -> h < (φ t) -> rd Q h = (φ u) ->
  rd off (φ u) <= (φ p) <= rd off ((φ u) + 1) ->
  (forall p', rd off (φ u) <= p' < (φ p) -> rd pr (rd tg p') <> 0) ->
  ScanOK mL mR h (scan tg mR u pe p Q qp pr t H).
Proof.
  intros mL mR h u HM Hu z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros pe p Q qp pr t H Hz Hpe HB Hht HQh Hp Hpart.
  pose proof HM as (HlL & HlR & M1 & M2).
  pose proof HB as (Hh & HQ & HRo & HP & HP2 & HP4).
  pose proof HQ as (HlQ & Hlq & Q2 & Q3 & Q4).
  pose proof HP as (Hlp & P1 & P3).
  assert (Hqu : rd qp (φ u) = h + 1) by (rewrite <- HQh; apply Q2; lia).
  pose proof (C1 (φ u) Hu) as [Co1 Co2].
  pose proof (phi_nonneg t) as Pt.
  rewrite scan_eq.
  destruct (bdec (p <? pe)%uint63) as [Hp' | Hp'].
  - pose proof Hp' as Hp''. rewrite ltb_spec, Hpe in Hp''.
    assert (Hp1 : (φ (p + 1)) = (φ p) + 1) by sia.
    destruct (C2 (φ u) (φ p) Hu ltac:(lia)) as [Hvr HG].
    cbv zeta.
    rewrite <- rd_get in Hvr, HG.
    set (v := tg.[p]) in *.
    assert (Hdec : Zwf 0 (gap pe (p + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hp').
    destruct (pr.[v] =? 0)%uint63 eqn:Epr.
    + rewrite eqb_Z, Z.eqb_eq, rd_get in Epr. change (φ 0) with 0 in Epr.
      assert (Rpr : forall z0, 0 <= z0 < 1000 ->
                rd pr.[v <- (u + 1)%uint63] z0 = if Z.eq_dec z0 (φ v) then (φ u) + 1 else rd pr z0).
      { intros z0 Hz0. rset. destruct (Z.eq_dec z0 (φ v)); [sia|reflexivity]. }
      assert (Sup : forall z0, 0 <= z0 < 1000 -> rd pr z0 <> 0 -> rd pr.[v <- (u + 1)%uint63] z0 <> 0).
      { intros z0 Hz0 Hn. rewrite Rpr by exact Hz0. destruct (Z.eq_dec z0 (φ v)); lia. }
      assert (HP' : PInv mL qp pr.[v <- (u + 1)%uint63]).
      { split; [rewrite len_set; exact Hlp|]. split.
        - intros v2 Hv2 Hn. rewrite Rpr in Hn |- * by exact Hv2.
          destruct (Z.eq_dec v2 (φ v)) as [E|E].
          + subst v2. replace ((φ u) + 1 - 1) with (φ u) by lia. split; [lia|]. split; [lia|]. exact HG.
          + apply P1; auto.
        - intros u2 Hu2 Hq Hm. destruct (P3 u2 Hu2 Hq Hm) as [Pa Pb].
          assert (rd mL u2 <> (φ v)) by (intro E; rewrite E in Pa; lia).
          rewrite Rpr by (pose proof (rd_nonneg mL u2); lia).
          destruct (Z.eq_dec (rd mL u2) (φ v)); [contradiction|]. split; auto. }
      destruct (mR.[v] <? NV)%uint63 eqn:Ew.
      * rewrite ltb_spec, phi_NV, rd_get in Ew.
        assert (HW : 0 <= (φ (mR.[v])) < 1000) by (rewrite rd_get; pose proof (rd_nonneg mR (φ v)); lia).
        assert (HMw : rd mL (rd mR (φ v)) = (φ v))
          by (apply (proj2 (M1 (rd mR (φ v)) (φ v) ltac:(pose proof (rd_nonneg mR (φ v)); lia) ltac:(lia))); reflexivity).
        destruct (qp.[mR.[v]] =? 0)%uint63 eqn:Eq.
        -- rewrite eqb_Z, Z.eqb_eq in Eq. change (φ 0) with 0 in Eq. rewrite rd_get in Eq.
           destruct (push_ok t (mR.[v]) Q qp HQ HW Eq) as (Ht1 & Ht & HQ' & Rq).
           rewrite rd_get in HW, Rq, Eq.
           assert (Rq1 : forall u2, 0 <= u2 < 1000 -> u2 <> rd mR (φ v) ->
                     rd qp.[mR.[v] <- (t + 1)%uint63] u2 = rd qp u2).
           { intros u2 Hu2 Hn. rewrite Rq by exact Hu2. destruct (Z.eq_dec u2 (rd mR (φ v))); [congruence|reflexivity]. }
           assert (Rq2 : rd qp.[mR.[v] <- (t + 1)%uint63] (rd mR (φ v)) = (φ t) + 1).
           { rewrite Rq by exact HW. destruct (Z.eq_dec (rd mR (φ v)) (rd mR (φ v))); [reflexivity|congruence]. }
           assert (Hqw : forall u2, 0 <= u2 < 1000 -> rd qp u2 <> 0 -> rd qp.[mR.[v] <- (t + 1)%uint63] u2 = rd qp u2).
           { intros u2 Hu2 Hn. rewrite Rq by exact Hu2. destruct (Z.eq_dec u2 (rd mR (φ v))); [subst; lia|reflexivity]. }
           assert (SupQ : forall u2, 0 <= u2 < 1000 -> rd qp u2 <> 0 -> rd qp.[mR.[v] <- (t + 1)%uint63] u2 <> 0)
             by (intros u2 Hu2 Hn; rewrite Hqw; auto).
           eapply IH; [exact Hdec | reflexivity | exact Hpe | | lia | | lia | ].
           ++ split; [lia|]. split; [rewrite Ht1; exact HQ'|]. split; [|split; [|split]].
              ** intros u2 Hu2 Hr. apply SupQ; auto.
              ** destruct HP' as (Hlp' & P1' & P3'). split; [exact Hlp'|]. split.
                 --- intros v2 Hv2 Hn. destruct (P1' v2 Hv2 Hn) as (Ra & Rb & Rc).
                     split; [exact Ra|]. split; [apply SupQ; auto|exact Rc].
                 --- intros u2 Hu2 Hq Hm.
                     destruct (Z.eq_dec u2 (rd mR (φ v))) as [E|E].
                     +++ subst u2. rewrite HMw. rewrite Rpr by lia.
                         destruct (Z.eq_dec (φ v) (φ v)) as [_|F]; [|congruence].
                         split; [lia|]. replace ((φ u) + 1 - 1) with (φ u) by lia.
                         rewrite Rq2.
                         assert ((φ u) <> rd mR (φ v)) by (intro E; rewrite <- E in Eq; lia).
                         rewrite Rq1 by (auto; lia). lia.
                     +++ rewrite Rq1 in Hq by auto.
                         destruct (P3' u2 Hu2 Hq Hm) as [Pa Pb]. split; [exact Pa|].
                         destruct (P1' (rd mL u2) ltac:(pose proof (rd_nonneg mL u2); lia) Pa) as (Ra & Rb & Rc).
                         rewrite !Hqw by auto. exact Pb.
              ** intros v2 Hv2 Hn. rewrite Rpr in Hn by exact Hv2.
                 destruct (Z.eq_dec v2 (φ v)) as [E|E].
                 --- subst v2. split; [lia|]. rewrite Rq by lia.
                     destruct (Z.eq_dec (rd mR (φ v)) (rd mR (φ v))); [lia|congruence].
                 --- destruct (HP2 v2 Hv2 Hn) as [Pa Pb]. split; [exact Pa|].
                     apply SupQ; [pose proof (rd_nonneg mR v2); lia | exact Pb].
              ** intros i Hi v2 HGv. rewrite rd_set in HGv by (rewrite ?wB_val; lia).
                 destruct (Z.eq_dec i (φ t)) as [E|E]; [lia|].
                 pose proof (C3 _ _ HGv) as (_ & Hv2 & _).
                 apply Sup; [exact Hv2|]. exact (HP4 i Hi v2 HGv).
           ++ rewrite rd_set by (rewrite ?wB_val; lia). destruct (Z.eq_dec h (φ t)); [lia | exact HQh].
           ++ intros p' Hp'1. rewrite Hp1 in Hp'1. destruct (Z.eq_dec p' (φ p)) as [E|E].
              ** subst p'. rewrite <- rd_get. fold v. rewrite Rpr by exact Hvr.
                 destruct (Z.eq_dec (φ v) (φ v)); lia.
              ** pose proof (Hpart p' ltac:(lia)) as Hn.
                 destruct (C2 (φ u) p' Hu ltac:(lia)) as [Hr _]. apply Sup; auto.
        -- rewrite eqb_Z, Z.eqb_neq in Eq. change (φ 0) with 0 in Eq. rewrite !rd_get in Eq.
           eapply IH; [exact Hdec | reflexivity | exact Hpe | | exact Hht | exact HQh | lia | ].
           ++ split; [lia|]. split; [exact HQ|]. split; [exact HRo|]. split; [exact HP'|]. split.
              ** intros v2 Hv2 Hn. rewrite Rpr in Hn by exact Hv2.
                 destruct (Z.eq_dec v2 (φ v)) as [E|E].
                 --- subst v2. split; [lia | exact Eq].
                 --- apply HP2; auto.
              ** intros i Hi v2 HGv. pose proof (C3 _ _ HGv) as (_ & Hv2 & _).
                 apply Sup; [exact Hv2|]. exact (HP4 i Hi v2 HGv).
           ++ intros p' Hp'1. rewrite Hp1 in Hp'1. destruct (Z.eq_dec p' (φ p)) as [E|E].
              ** subst p'. rewrite <- rd_get. fold v. rewrite Rpr by exact Hvr.
                 destruct (Z.eq_dec (φ v) (φ v)); lia.
              ** pose proof (Hpart p' ltac:(lia)) as Hn.
                 destruct (C2 (φ u) p' Hu ltac:(lia)) as [Hr _]. apply Sup; auto.
      * rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV, rd_get in Ew.
        split; [exact Hlq|]. split; [exact Hvr|]. split.
        -- rewrite Rpr by exact Hvr. destruct (Z.eq_dec (φ v) (φ v)); lia.
        -- split; [lia | exact HP'].
    + rewrite eqb_Z, Z.eqb_neq, rd_get in Epr. change (φ 0) with 0 in Epr.
      eapply IH; [exact Hdec | reflexivity | exact Hpe | exact HB | exact Hht | exact HQh | lia | ].
      intros p' Hp'1. rewrite Hp1 in Hp'1. destruct (Z.eq_dec p' (φ p)) as [E|E].
      * subst p'. rewrite <- rd_get. exact Epr.
      * apply Hpart. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, Hpe in Hp'.
    split; [lia|]. split; [exact HQ|]. split; [exact HRo|]. split; [exact HP|]. split; [exact HP2|].
    intros i Hi v2 HGv. destruct (Z.eq_dec i h) as [E|E].
    + subst i. rewrite HQh in HGv. destruct (C3 _ _ HGv) as (_ & _ & p' & Hp'1 & Hv).
      rewrite <- Hv. apply Hpart. lia.
    + apply (HP4 i ltac:(lia) v2 HGv).
Qed.

Definition BfsOK (mL mR : array int) (r : bres) : Prop :=
  match r with
  | BFound v qp pr => FoundOK mL mR v qp pr
  | BFail qp pr => FailOK mL mR qp pr
  end.

Lemma bfs_spec : forall mL mR, Mat mL mR ->
  forall z h t Q qp pr H, gap NV h = z ->
  BInv mL mR (φ h) (φ t) Q qp pr ->
  BfsOK mL mR (bfs off tg mR h t Q qp pr H).
Proof.
  intros mL mR HM z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h t Q qp pr H Hz HB.
  pose proof HB as (Hh & HQ & HRo & HP & HP2 & HP4).
  pose proof HQ as (HlQ & Hlq & Q2 & Q3 & Q4).
  pose proof (QInv_t _ _ _ HQ) as Ht.
  assert (Fail : (φ t) <= (φ h) -> FailOK mL mR qp pr).
  { intros Hth. destruct HP as (Hlp & _ & _).
    split; [exact Hlq|]. split; [exact Hlp|]. split; [exact HRo|]. split; [exact HP2|].
    intros u v Hu Hq HG. destruct (Q3 u Hu Hq) as [Qa Qb]. pose proof (rd_nonneg qp u).
    apply (HP4 (rd qp u - 1)); [lia|]. rewrite Qb. exact HG. }
  rewrite bfs_eq.
  destruct (bdec (h <? NV)%uint63) as [Hh' | Hh'].
  - destruct (h <? t)%uint63 eqn:Eht.
    + rewrite ltb_spec in Eht. pose proof Hh' as Hh''. rewrite ltb_spec, phi_NV in Hh''.
      cbv zeta.
      destruct (Q2 (φ h) ltac:(lia)) as [Hur Hqu].
      rewrite <- rd_get in Hur.
      assert (Hu1 : (φ (Q.[h] + 1)) = (φ (Q.[h])) + 1) by (apply phi_add1; lia).
      pose proof (C1 (φ (Q.[h])) Hur) as [Co1 Co2].
      pose proof (scan_spec mL mR (φ h) (Q.[h]) HM Hur _ (off.[Q.[h] + 1]) (off.[Q.[h]]) Q qp pr t
        (Zwf_well_founded 0 (gap off.[Q.[h] + 1] off.[Q.[h]])) eq_refl
        ltac:(rewrite (rd_get off (Q.[h] + 1)), Hu1; reflexivity) HB Eht (eq_sym (rd_get Q h))
        ltac:(rewrite (rd_get off (Q.[h])); lia)
        ltac:(intros p' Hp'; rewrite (rd_get off (Q.[h])) in Hp'; lia)) as Hs.
      revert Hs.
      destruct (scan tg mR Q.[h] off.[Q.[h] + 1] off.[Q.[h]] Q qp pr t
                  (Zwf_well_founded 0 (gap off.[Q.[h] + 1] off.[Q.[h]])))
        as [v qp' pr' | Q' qp' pr' t']; intros Hs.
      * exact Hs.
      * assert (Hh1 : (φ (h + 1)) = (φ h) + 1) by (apply phi_add1; lia).
        eapply IH; [ | reflexivity | rewrite Hh1; exact Hs].
        rewrite <- Hz. apply dec_step. exact Hh'.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Eht. apply Fail. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV in Hh'. apply Fail. lia.
Qed.

Definition WInv (mL0 qp pr : array int) (v : Z) (mL mR : array int) : Prop :=
  (φ (PArray.length mL)) = 1000 /\ (φ (PArray.length mR)) = 1000 /\ 0 <= v < 1000 /\ rd pr v <> 0 /\
  (forall u w, 0 <= u < 1000 -> 0 <= w < 1000 -> w <> v -> (rd mL u = w <-> rd mR w = u)) /\
  (forall u, 0 <= u < 1000 -> rd mL u <> v) /\
  (forall w, 0 <= w < 1000 -> rd mR w < 1000 -> G (rd mR w) w) /\
  (forall u, 0 <= u < 1000 -> rd mL u <> rd mL0 u ->
     rd qp u <> 0 /\ rd qp (rd pr v - 1) < rd qp u) /\
  sizeL mL = sizeL mL0.

Lemma walk_spec : forall mL0 qp pr, (φ (PArray.length qp)) = 1000 -> PInv mL0 qp pr ->
  forall z v mL mR H, wmeas qp pr v = z -> WInv mL0 qp pr (φ v) mL mR ->
  match walk qp pr v mL mR H with (mL', mR') => Mat mL' mR' /\ sizeL mL' = sizeL mL0 + 1 end.
Proof.
  intros mL0 qp pr Hlq HP z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v mL mR H Hz HW.
  pose proof HP as (Hlp & P1 & P3).
  destruct HW as (HlL & HlR & Hv & Hpv & W1 & W1b & W2 & W3 & W5).
  destruct (P1 (φ v) Hv Hpv) as (Hur & Hqu & HG).
  set (U := rd pr (φ v) - 1) in *.
  assert (HU : (φ (pr.[v] - 1)) = U).
  { unfold U. rewrite <- rd_get in Hpv |- *. pose proof (phi_nonneg (pr.[v])). sia. }
  assert (Hold : rd mL U = rd mL0 U).
  { destruct (Z.eq_dec (rd mL U) (rd mL0 U)) as [E|E]; [exact E|].
    destruct (W3 U Hur E) as [_ F]. lia. }
  assert (RL1 : forall z0, 0 <= z0 < 1000 -> z0 <> U -> rd mL.[pr.[v] - 1 <- v] z0 = rd mL z0).
  { intros z0 Hz0 Hn. rset. rewrite HU. destruct (Z.eq_dec z0 U); [congruence|reflexivity]. }
  assert (RL2 : rd mL.[pr.[v] - 1 <- v] U = (φ v)).
  { rset. rewrite HU. destruct (Z.eq_dec U U); [reflexivity|congruence]. }
  assert (RR1 : forall z0, 0 <= z0 < 1000 -> z0 <> (φ v) -> rd mR.[v <- (pr.[v] - 1)%uint63] z0 = rd mR z0).
  { intros z0 Hz0 Hn. rset. destruct (Z.eq_dec z0 (φ v)); [congruence|reflexivity]. }
  assert (RR2 : rd mR.[v <- (pr.[v] - 1)%uint63] (φ v) = U).
  { rset. destruct (Z.eq_dec (φ v) (φ v)); [exact HU|congruence]. }
  assert (HO : (φ (mL.[pr.[v] - 1])) = rd mL U) by (rewrite rd_get, HU; reflexivity).
  pose proof (rd_nonneg mL U) as HOn.
  (* the new state is consistent except at the old mate of U *)
  assert (NW1 : forall u w, 0 <= u < 1000 -> 0 <= w < 1000 -> w <> rd mL U ->
            (rd mL.[pr.[v] - 1 <- v] u = w <-> rd mR.[v <- (pr.[v] - 1)%uint63] w = u)).
  { intros u w Hu Hw Hne. destruct (Z.eq_dec w (φ v)) as [Ew|Ew].
    - subst w. rewrite RR2. destruct (Z.eq_dec u U) as [Eu|Eu].
      + subst u. rewrite RL2. tauto.
      + rewrite RL1 by auto. split; [intro F; exfalso; exact (W1b u Hu F) | intro F; congruence].
    - rewrite RR1 by auto. destruct (Z.eq_dec u U) as [Eu|Eu].
      + subst u. rewrite RL2. split; [intro F; congruence|].
        intro F. apply (W1 U w Hur Hw Ew) in F. congruence.
      + rewrite RL1 by auto. apply W1; auto. }
  assert (NW2 : forall w, 0 <= w < 1000 -> rd mR.[v <- (pr.[v] - 1)%uint63] w < 1000 ->
            G (rd mR.[v <- (pr.[v] - 1)%uint63] w) w).
  { intros w Hw Hl. destruct (Z.eq_dec w (φ v)) as [Ew|Ew].
    - subst w. rewrite RR2. exact HG.
    - rewrite RR1 in Hl |- * by auto. apply W2; auto. }
  rewrite walk_eq. cbv zeta.
  destruct (mL.[pr.[v] - 1] <? NV)%uint63 eqn:Eo.
  - rewrite ltb_spec, phi_NV, HO in Eo.
    rewrite Hold in Eo.
    destruct (P3 U Hur Hqu Eo) as [Po1 Po2].
    rewrite <- Hold in Po1, Po2, Eo.
    assert (HO1 : (φ (pr.[mL.[pr.[v] - 1]] - 1)) = rd pr (rd mL U) - 1).
    { rewrite <- HO in Po1 |- *. rewrite <- (rd_get pr) in Po1 |- *. apply phi_sub1. exact Po1. }
    assert (Hguard : (qp.[pr.[mL.[pr.[v] - 1]] - 1] <? qp.[pr.[v] - 1])%uint63 = true).
    { rewrite ltb_spec, !rd_get, HO1, HU. exact Po2. }
    destruct (bdec (qp.[pr.[mL.[pr.[v] - 1]] - 1] <? qp.[pr.[v] - 1])%uint63) as [Hd|Hd];
      [| rewrite Hguard in Hd; discriminate].
    eapply IH; [rewrite <- Hz; apply wdec; exact Hd | reflexivity | ].
    rewrite HO. clear HO HO1 HU Hguard Hd Hz IH.
    split; [rewrite len_set; exact HlL|]. split; [rewrite len_set; exact HlR|].
    split; [split; [exact HOn | exact Eo]|]. split; [exact Po1|].
    split; [exact NW1|]. split; [|split; [exact NW2|split]].
    + intros u2 Hu2 F. destruct (Z.eq_dec u2 U) as [Eu|Eu].
      * subst u2. rewrite RL2 in F. exact (W1b U Hur (eq_sym F)).
      * rewrite RL1 in F by auto.
        assert (Hne0 : rd mL U <> (φ v)) by (intro E; exact (W1b U Hur E)).
        assert (A : rd mR (rd mL U) = u2)
          by (apply (proj1 (W1 u2 (rd mL U) Hu2 ltac:(lia) Hne0)); exact F).
        assert (B : rd mR (rd mL U) = U)
          by (apply (proj1 (W1 U (rd mL U) Hur ltac:(lia) Hne0)); reflexivity).
        congruence.
    + intros u2 Hu2 Hn. destruct (Z.eq_dec u2 U) as [Eu|Eu].
      * subst u2. split; [exact Hqu | exact Po2].
      * rewrite RL1 in Hn by auto. destruct (W3 u2 Hu2 Hn) as [Wa Wb]. split; [exact Wa|].
        fold U in Wb. lia.
    + rewrite <- W5. unfold sizeL. apply cZ_ext. intros y Hy. unfold matb.
      destruct (Z.eq_dec y U) as [Ey|Ey].
      * subst y. rewrite RL2. apply Z.ltb_lt in Eo. rewrite Eo. apply Z.ltb_lt. lia.
      * rewrite RL1 by auto. reflexivity.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV, HO in Eo.
    clear HO HU Hz IH.
    split.
    + split; [rewrite len_set; exact HlL|]. split; [rewrite len_set; exact HlR|].
      split; [|exact NW2].
      intros u w Hu Hw. apply NW1; auto. lia.
    + rewrite <- W5. unfold sizeL.
      apply (cZ_upd (matb mL) (matb mL.[pr.[v] - 1 <- v]) 1000 U); [lia | | | ].
      * intros y Hy Hne. unfold matb. rewrite RL1 by auto. reflexivity.
      * unfold matb. apply Z.ltb_ge. lia.
      * unfold matb. rewrite RL2. apply Z.ltb_lt. lia.
Qed.

Lemma phases_spec : forall z it mL mR H, gap NP it = z -> Mat mL mR -> sizeL mL = (φ it) ->
  match phases off tg it mL mR H with
  | (qp, pr) => exists mL' mR', Mat mL' mR' /\ FailOK mL' mR' qp pr
  end.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros it mL mR H Hz HM Hs.
  pose proof HM as (HlL & HlR & M1 & M2).
  rewrite phases_eq.
  destruct (bdec (it <? NP)%uint63) as [Hi | Hi].
  - pose proof (root_loop_spec mL _ 0%uint63 (PArray.make NV 0%uint63) (PArray.make NV 0%uint63) 0%uint63
      (Zwf_well_founded 0 (gap NV 0%uint63)) eq_refl ltac:(change ((φ 0)%uint63) with 0; lia) QInv0
      ltac:(intros; apply rd_make)
      ltac:(change ((φ 0)%uint63) with 0; intros; lia)
      ltac:(intros u' _ Hn; rewrite rd_make in Hn; contradiction)) as HR.
    revert HR.
    destruct (root_loop mL 0%uint63 (PArray.make NV 0%uint63) (PArray.make NV 0%uint63) 0%uint63
                (Zwf_well_founded 0 (gap NV 0%uint63))) as [[Q qp] t].
    intros (HQ & HRo & HVis).
    pose proof HQ as (HlQ & Hlq & _).
    assert (HB : BInv mL mR ((φ 0)%uint63) (φ t) Q qp (PArray.make NV 0%uint63)).
    { change ((φ 0)%uint63) with 0. split; [pose proof (phi_nonneg t); lia|].
      split; [exact HQ|]. split; [exact HRo|]. split; [|split].
      - split; [rewrite len_make by (rewrite phi_NV; lia); reflexivity|]. split.
        + intros v _ Hn. rewrite rd_make in Hn. contradiction.
        + intros u Hu Hq Hm. pose proof (HVis u Hu Hq). lia.
      - intros v _ Hn. rewrite rd_make in Hn. contradiction.
      - intros; lia. }
    pose proof (bfs_spec mL mR HM _ 0%uint63 t Q qp (PArray.make NV 0%uint63)
                  (Zwf_well_founded 0 (gap NV 0%uint63)) eq_refl HB) as Hb.
    revert Hb.
    destruct (bfs off tg mR 0%uint63 t Q qp (PArray.make NV 0%uint63)
                (Zwf_well_founded 0 (gap NV 0%uint63))) as [v qp' pr' | qp' pr'];
      intros Hb.
    + destruct Hb as (Hlq' & Hv & Hpv & HmR & HP).
      pose proof (walk_spec mL qp' pr' Hlq' HP _ v mL mR
                    (Zwf_well_founded 0 (wmeas qp' pr' v)) eq_refl) as Hw.
      revert Hw.
      destruct (walk qp' pr' v mL mR (Zwf_well_founded 0 (wmeas qp' pr' v))) as [mL' mR'].
      intros Hw. destruct Hw as [HM' Hs'].
      { split; [exact HlL|]. split; [exact HlR|]. split; [exact Hv|]. split; [exact Hpv|].
        split; [|split; [|split; [exact M2|split]]].
        - intros u w Hu Hw _. apply M1; auto.
        - intros u Hu F. apply (M1 u (φ v) Hu Hv) in F. lia.
        - intros u _ F. congruence.
        - reflexivity. }
      pose proof (cZ_bounds (matb mL') 1000 ltac:(lia)) as Bs. unfold sizeL in Hs'.
      unfold sizeL in Hs. rewrite Hs in Hs'.
      pose proof Hi as Hi'. rewrite ltb_spec, phi_NP in Hi'.
      assert (Hi1 : (φ (it + 1)) = (φ it) + 1) by (apply phi_add1; lia).
      eapply IH; [ | reflexivity | exact HM' | ].
      * rewrite <- Hz. apply dec_step. exact Hi.
      * unfold sizeL. rewrite Hi1. exact Hs'.
    + exists mL, mR. split; [exact HM | exact Hb].
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NP in Hi.
    exfalso. pose proof (cZ_bounds (matb mL) 1000 ltac:(lia)). unfold sizeL in Hs. lia.
Qed.


(* König's theorem, constructive half: the cover read off a failed search
   is no larger than any vertex cover. *)
Lemma konig : forall mL mR qp pr, Mat mL mR -> FailOK mL mR qp pr ->
  forall f : Z -> bool,
  (forall i, 0 <= i < 2000 -> (f i = true <->
      ((i < 1000 /\ rd qp i = 0) \/ (1000 <= i /\ rd pr (i - 1000) <> 0)))) ->
  (forall u v, G u v -> In (1000 + u) (ml f 2000) \/ In (2000 + v) (ml f 2000)) /\
  (forall c : list Z, NoDup c -> (forall u v, G u v -> In (1000 + u) c \/ In (2000 + v) c) ->
     (List.length (ml f 2000) <= List.length c)%nat).
Proof.
  intros mL mR qp pr HM HF f Hf.
  destruct HM as (HlL & HlR & M1 & M2).
  destruct HF as (Hlq & Hlp & HRo & HP2 & Hcl).
  split.
  - intros u v HG. destruct (C3 u v HG) as (Hu & Hv & _).
    destruct (Z.eq_dec (rd qp u) 0) as [E|E].
    + left. apply ml_In. exists u. split; [lia|]. split; [apply Hf; [lia|left; split; [lia|exact E]]|lia].
    + right. apply ml_In. exists (1000 + v). split; [lia|]. split; [|lia].
      apply Hf; [lia|]. right. split; [lia|]. replace (1000 + v - 1000) with v by lia.
      exact (Hcl u v Hu E HG).
  - intros c Hc Hcov.
    set (wf := fun a => if a <? 2000 then rd mL (a - 1000) else a - 2000).
    set (F := fun a => if in_dec Z.eq_dec (2000 + wf a) c then 2000 + wf a
                       else 1000 + rd mR (wf a)).
    assert (wfL : forall a, a < 2000 -> wf a = rd mL (a - 1000))
      by (intros a0 Ha0; unfold wf; destruct (Z.ltb_spec a0 2000); lia).
    assert (wfR : forall a, 2000 <= a -> wf a = a - 2000)
      by (intros a0 Ha0; unfold wf; destruct (Z.ltb_spec a0 2000); lia).
    (* every selected employee has a matched right vertex *)
    assert (Hw : forall a, In a (ml f 2000) ->
              0 <= wf a < 1000 /\ rd mR (wf a) < 1000 /\
              ((a < 2000 /\ rd mR (wf a) = a - 1000 /\ rd qp (a - 1000) = 0) \/
               (2000 <= a /\ rd qp (rd mR (wf a)) <> 0))).
    { intros a Ha. apply ml_In in Ha. destruct Ha as (i & Hi & Hfi & Ha).
      apply Hf in Hfi; [|lia].
      destruct Hfi as [[Hi1 Hq] | [Hi1 Hp]].
      + rewrite wfL by lia. replace (a - 1000) with i by lia.
        assert (Hm : rd mL i < 1000).
        { destruct (Z_lt_le_dec (rd mL i) 1000) as [L|L]; [exact L|].
          exfalso. exact (HRo i ltac:(lia) L Hq). }
        pose proof (rd_nonneg mL i).
        assert (E : rd mR (rd mL i) = i)
          by (apply (proj1 (M1 i (rd mL i) ltac:(lia) ltac:(lia))); reflexivity).
        rewrite E. split; [lia|]. split; [lia|]. left. split; [lia|]. split; [lia|exact Hq].
      + rewrite wfR by lia. replace (a - 2000) with (i - 1000) by lia.
        destruct (HP2 (i - 1000) ltac:(lia) Hp) as [Pa Pb].
        split; [lia|]. split; [exact Pa|]. right. split; [lia|exact Pb]. }
    assert (Hinj : forall a b, In a (ml f 2000) -> In b (ml f 2000) -> F a = F b -> a = b).
    { intros a b Ha Hb E.
      destruct (Hw a Ha) as (Wa1 & Wa2 & Wa3). destruct (Hw b Hb) as (Wb1 & Wb2 & Wb3).
      assert (Ew : wf a = wf b).
      { unfold F in E. revert E.
        destruct (in_dec Z.eq_dec (2000 + wf a) c), (in_dec Z.eq_dec (2000 + wf b) c);
          intro E; try lia.
        pose proof (rd_nonneg mR (wf a)). pose proof (rd_nonneg mR (wf b)).
        assert (A1 : rd mL (rd mR (wf a)) = wf a)
          by (apply (proj2 (M1 (rd mR (wf a)) (wf a) ltac:(lia) ltac:(lia))); reflexivity).
        assert (A2 : rd mL (rd mR (wf b)) = wf b)
          by (apply (proj2 (M1 (rd mR (wf b)) (wf b) ltac:(lia) ltac:(lia))); reflexivity).
        assert (E1 : rd mR (wf a) = rd mR (wf b)) by lia.
        rewrite E1 in A1. congruence. }
      destruct Wa3 as [(Ha1 & Ha2 & Ha3) | (Ha1 & Ha2)], Wb3 as [(Hb1 & Hb2 & Hb3) | (Hb1 & Hb2)].
      - rewrite Ew in Ha2. lia.
      - rewrite Ew in Ha2. rewrite Ha2 in Hb2. contradiction.
      - rewrite <- Ew in Hb2. rewrite Hb2 in Ha2. contradiction.
      - rewrite wfR in Ew by lia. rewrite wfR in Ew by lia. lia. }
    rewrite <- (length_map F).
    apply NoDup_incl_length.
    + apply NoDup_map_on; [apply ml_NoDup | exact Hinj].
    + intros b Hb. apply in_map_iff in Hb. destruct Hb as (a & Hb & Ha). subst b.
      destruct (Hw a Ha) as (Wa1 & Wa2 & _).
      pose proof (M2 (wf a) Wa1 Wa2) as HG.
      unfold F. destruct (in_dec Z.eq_dec (2000 + wf a) c) as [I|I]; [exact I|].
      destruct (Hcov _ _ HG) as [J|J]; [exact J|contradiction].
Qed.

End Match.

(* ------------------------------------------------------------------ *)
(* The marks, the engine                                               *)
(* ------------------------------------------------------------------ *)

Definition MK (qp pr : array int) (j : Z) : Prop :=
  (j < 1000 /\ rd qp j = 0) \/ (1000 <= j /\ rd pr (j - 1000) <> 0).

Lemma mark_loop_spec : forall qp pr z i mk H, gap NM i = z ->
  0 <= (φ i) <= 2000 -> (φ (PArray.length mk)) = 2000 ->
  (forall j, 0 <= j < (φ i) -> (rd mk j <> 0 <-> MK qp pr j)) ->
  (forall j, (φ i) <= j < 2000 -> rd mk j = 0) ->
  (φ (PArray.length (mark_loop qp pr i mk H))) = 2000 /\
  forall j, 0 <= j < 2000 -> (rd (mark_loop qp pr i mk H) j <> 0 <-> MK qp pr j).
Proof.
  intros qp pr z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i mk H Hz Hi Hl Hinv Hzero.
  rewrite mark_loop_eq.
  destruct (bdec (i <? NM)%uint63) as [Hi' | Hi'].
  - pose proof Hi' as Hi''. rewrite ltb_spec, phi_NM in Hi''.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by (apply phi_add1; lia).
    assert (Hdec : Zwf 0 (gap NM (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hi').
    assert (Set1 : forall j, 0 <= j < 2000 ->
              rd mk.[i <- 1%uint63] j = if Z.eq_dec j (φ i) then 1 else rd mk j).
    { intros j Hj. rset. reflexivity. }
    assert (Keep : forall j, 0 <= j < (φ i) + 1 -> (rd mk j <> 0 <-> MK qp pr j) -> ~ MK qp pr (φ i) ->
              (rd mk j <> 0 <-> MK qp pr j)) by auto.
    destruct (i <? NV)%uint63 eqn:Ein.
    + rewrite ltb_spec, phi_NV in Ein.
      destruct (qp.[i] =? 0)%uint63 eqn:Eq.
      * rewrite eqb_Z, Z.eqb_eq, rd_get in Eq. change (φ 0) with 0 in Eq.
        eapply IH; [exact Hdec | reflexivity | lia | rewrite len_set; exact Hl | | ].
        -- intros j Hj. rewrite Set1 by lia. destruct (Z.eq_dec j (φ i)) as [E|E].
           ++ subst j. split; [intros _; left; split; [lia|exact Eq] | lia].
           ++ apply Hinv. lia.
        -- intros j Hj. rewrite Set1 by lia. destruct (Z.eq_dec j (φ i)); [lia|]. apply Hzero. lia.
      * rewrite eqb_Z, Z.eqb_neq, rd_get in Eq. change (φ 0) with 0 in Eq.
        eapply IH; [exact Hdec | reflexivity | lia | exact Hl | | ].
        -- intros j Hj. destruct (Z.eq_dec j (φ i)) as [E|E].
           ++ subst j. rewrite Hzero by lia. split; [lia|].
              intros [[_ F]|[F _]]; [contradiction|lia].
           ++ apply Hinv. lia.
        -- intros j Hj. apply Hzero. lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NV in Ein.
      assert (Hs : (φ (i - NV)) = (φ i) - 1000) by (rewrite sub_spec, phi_NV, Z.mod_small; [lia|rewrite wB_val; lia]).
      destruct (pr.[i - NV] =? 0)%uint63 eqn:Eq.
      * rewrite eqb_Z, Z.eqb_eq, rd_get, Hs in Eq. change (φ 0) with 0 in Eq.
        eapply IH; [exact Hdec | reflexivity | lia | exact Hl | | ].
        -- intros j Hj. destruct (Z.eq_dec j (φ i)) as [E|E].
           ++ subst j. rewrite Hzero by lia. split; [lia|].
              intros [[F _]|[_ F]]; [lia|contradiction].
           ++ apply Hinv. lia.
        -- intros j Hj. apply Hzero. lia.
      * rewrite eqb_Z, Z.eqb_neq, rd_get, Hs in Eq. change (φ 0) with 0 in Eq.
        eapply IH; [exact Hdec | reflexivity | lia | rewrite len_set; exact Hl | | ].
        -- intros j Hj. rewrite Set1 by lia. destruct (Z.eq_dec j (φ i)) as [E|E].
           ++ subst j. split; [intros _; right; split; [lia|exact Eq] | lia].
           ++ apply Hinv. lia.
        -- intros j Hj. rewrite Set1 by lia. destruct (Z.eq_dec j (φ i)); [lia|]. apply Hzero. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NM in Hi'.
    split; [exact Hl|]. intros j Hj. apply Hinv. lia.
Qed.

Lemma engine_spec : forall x y ex, PArray.length y = PArray.length x ->
  (forall j, 0 <= j < (φ (PArray.length x)) -> 1000 <= rd x j <= 1999 /\ 2000 <= rd y j <= 2999) ->
  (φ (PArray.length (engine x y ex))) = 2000 /\
  (forall u v, Gx x y ex u v ->
     In (1000 + u) (ml (mkb (engine x y ex)) 2000) \/ In (2000 + v) (ml (mkb (engine x y ex)) 2000)) /\
  (forall c, NoDup c -> (forall u v, Gx x y ex u v -> In (1000 + u) c \/ In (2000 + v) c) ->
     (List.length (ml (mkb (engine x y ex)) 2000) <= List.length c)%nat).
Proof.
  intros x y ex Hlen Hrange.
  pose proof (len_bound x) as Bx.
  unfold engine. cbv zeta.
  pose proof (deg_loop_spec x y ex Hlen Hrange _ 0%uint63 (PArray.make NV 0%uint63)
    (Zwf_well_founded 0 (gap (PArray.length x) 0%uint63)) eq_refl
    ltac:(change ((φ 0)%uint63) with 0; pose proof (phi_nonneg (PArray.length x)); lia)
    ltac:(rewrite len_make by (rewrite phi_NV; lia); reflexivity)
    ltac:(intros u _; rewrite rd_make; reflexivity)) as Hd.
  set (d := deg_loop x ex (PArray.length x) 0%uint63 (PArray.make NV 0%uint63)
              (Zwf_well_founded 0 (gap (PArray.length x) 0%uint63))) in *.
  assert (Ho0 : forall u', 0 <= u' <= (φ 0)%uint63 -> rd (PArray.make NP 0%uint63) u' = SS x ex u').
  { intros u' Hu'. change ((φ 0)%uint63) with 0 in Hu'. replace u' with 0 by lia.
    rewrite rd_make, SS_0. reflexivity. }
  destruct (off_loop_spec x y ex Hlen d Hd _ 0%uint63 (PArray.make NP 0%uint63)
    (Zwf_well_founded 0 (gap NV 0%uint63)) eq_refl ltac:(change ((φ 0)%uint63) with 0; lia)
    ltac:(rewrite len_make by (rewrite phi_NP; lia); reflexivity) Ho0) as [Hlo Hoff].
  set (off := off_loop d 0%uint63 (PArray.make NP 0%uint63) (Zwf_well_founded 0 (gap NV 0%uint63))) in *.
  pose proof (fill_loop_spec x y ex Hlen Hrange _ 0%uint63 off (PArray.make (PArray.length x) 0%uint63)
    (Zwf_well_founded 0 (gap (PArray.length x) 0%uint63)) eq_refl
    ltac:(change ((φ 0)%uint63) with 0; pose proof (phi_nonneg (PArray.length x)); lia)
    Hlo ltac:(rewrite len_make by lia; reflexivity)
    ltac:(intros u Hu; rewrite Hoff by lia; change ((φ 0)%uint63) with 0; rewrite cZ_0; lia)
    ltac:(intros u p Hu Hp; change ((φ 0)%uint63) with 0 in Hp; rewrite cZ_0 in Hp; lia)
    ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj; lia)) as HF.
  set (tg := fill_loop x y ex (PArray.length x) 0%uint63 off (PArray.make (PArray.length x) 0%uint63)
               (Zwf_well_founded 0 (gap (PArray.length x) 0%uint63))) in *.
  destruct HF as (Htl & FS & FC).
  assert (C1 : forall u, 0 <= u < 1000 ->
     0 <= rd off u <= rd off (u + 1) /\ rd off (u + 1) <= (φ (PArray.length tg))).
  { intros u Hu. rewrite !Hoff by lia. rewrite Htl.
    pose proof (SS_nonneg x y ex Hlen u ltac:(lia)). pose proof (SS_S x ex u ltac:(lia)).
    pose proof (dg_nonneg x y ex Hlen u). pose proof (SS_bound x y ex Hlen (u + 1) ltac:(lia)).
    lia. }
  assert (C2 : forall u p, 0 <= u < 1000 -> rd off u <= p < rd off (u + 1) ->
     0 <= rd tg p < 1000 /\ Gx x y ex u (rd tg p)).
  { intros u p Hu Hp. rewrite !Hoff in Hp by lia. apply FS; auto. }
  assert (C3 : forall u v, Gx x y ex u v ->
     0 <= u < 1000 /\ 0 <= v < 1000 /\ exists p, rd off u <= p < rd off (u + 1) /\ rd tg p = v).
  { intros u v HG. pose proof HG as (j & Hj & Hk & Hxu & Hyv).
    destruct (Hrange j Hj) as [Rx Ry].
    split; [lia|]. split; [lia|].
    destruct (FC j Hj Hk) as (p & Hp & Hv).
    exists p. rewrite !Hoff by lia. replace (rd x j - 1000) with u in Hp by lia.
    split; [exact Hp | lia]. }
  assert (HM0 : Mat (Gx x y ex) (PArray.make NV NV) (PArray.make NV NV)).
  { split; [rewrite len_make by (rewrite phi_NV; lia); reflexivity|].
    split; [rewrite len_make by (rewrite phi_NV; lia); reflexivity|].
    split.
    - intros u w Hu Hw. rewrite !rd_make, phi_NV. lia.
    - intros w _ F. rewrite rd_make, phi_NV in F. lia. }
  assert (HS0 : sizeL (PArray.make NV NV) = (φ 0)%uint63).
  { unfold sizeL. apply cZ_false; [lia|]. intros y0 _. unfold matb. rewrite rd_make, phi_NV. reflexivity. }
  pose proof (phases_spec (Gx x y ex) off tg C1 C2 C3 _ 0%uint63 (PArray.make NV NV) (PArray.make NV NV)
    (Zwf_well_founded 0 (gap NP 0%uint63)) eq_refl HM0 HS0) as Hph.
  revert Hph.
  destruct (phases off tg 0%uint63 (PArray.make NV NV) (PArray.make NV NV)
              (Zwf_well_founded 0 (gap NP 0%uint63))) as [qp pr].
  intros (mL & mR & HM & HFl).
  pose proof HFl as (Hlq & Hlp & _).
  destruct (mark_loop_spec qp pr _ 0%uint63 (PArray.make NM 0%uint63) (Zwf_well_founded 0 (gap NM 0%uint63))
    eq_refl ltac:(change ((φ 0)%uint63) with 0; lia)
    ltac:(rewrite len_make by (rewrite phi_NM; lia); reflexivity)
    ltac:(intros j Hj; change ((φ 0)%uint63) with 0 in Hj; lia)
    ltac:(intros j _; apply rd_make)) as [Hlm Hm].
  split; [exact Hlm|].
  apply (konig (Gx x y ex) off tg C3 mL mR qp pr HM HFl).
  intros i Hi. unfold mkb. rewrite Bool.negb_true_iff, Z.eqb_neq. apply Hm. exact Hi.
Qed.

(* ------------------------------------------------------------------ *)
(* Counting the marks, building the output                             *)
(* ------------------------------------------------------------------ *)

Lemma cZ_ml : forall f, cZ f 2000 = Z.of_nat (List.length (ml f 2000)).
Proof. intros f. unfold cZ. rewrite ml_length. reflexivity. Qed.

Lemma cnt_loop_spec : forall mk z i c H, gap NM i = z -> 0 <= (φ i) <= 2000 ->
  (φ c) = cZ (mkb mk) (φ i) -> (φ (cnt_loop mk i c H)) = cZ (mkb mk) 2000.
Proof.
  intros mk z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c H Hz Hi Hc.
  rewrite cnt_loop_eq.
  destruct (bdec (i <? NM)%uint63) as [Hi' | Hi'].
  - pose proof Hi' as Hi''. rewrite ltb_spec, phi_NM in Hi''.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by (apply phi_add1; lia).
    pose proof (cZ_bounds (mkb mk) (φ i) ltac:(lia)) as B.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hi' | reflexivity | lia | ].
    rewrite Hi1, cZ_S by lia. change (mkb mk (φ i)) with (negb (rd mk (φ i) =? 0)).
    destruct (mk.[i] =? 0)%uint63 eqn:E; rewrite eqb_Z, rd_get in E; change (φ 0) with 0 in E;
      rewrite E; cbn [negb].
    + lia.
    + rewrite phi_add1 by lia. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NM in Hi'.
    rewrite Hc. f_equal. lia.
Qed.

Lemma ml_S : forall f z, 0 <= z ->
  ml f (Z.to_nat (z + 1)) = ml f (Z.to_nat z) ++ (if f z then [1000 + z] else []).
Proof.
  intros f z Hz. rewrite Z2Nat.inj_add, Nat.add_1_r by lia. cbn [ml].
  rewrite Z2Nat.id by lia. reflexivity.
Qed.

Lemma ml_len_cZ : forall f z, 0 <= z -> Z.of_nat (List.length (ml f (Z.to_nat z))) = cZ f z.
Proof. intros f z Hz. unfold cZ. rewrite ml_length. reflexivity. Qed.

Lemma out_loop_spec : forall mk L z i p out H, gap NM i = z -> 0 <= (φ i) <= 2000 ->
  (φ (PArray.length out)) = L -> cZ (mkb mk) 2000 <= L ->
  (φ p) = cZ (mkb mk) (φ i) ->
  (forall n, (n < List.length (ml (mkb mk) (Z.to_nat (φ i))))%nat ->
     nth_error (ml (mkb mk) (Z.to_nat (φ i))) n = Some (rd out (Z.of_nat n))) ->
  (φ (PArray.length (out_loop mk i p out H))) = L /\
  forall n, (n < List.length (ml (mkb mk) 2000))%nat ->
     nth_error (ml (mkb mk) 2000) n = Some (rd (out_loop mk i p out H) (Z.of_nat n)).
Proof.
  intros mk L z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i p out H Hz Hi Hl HL Hp Hinv.
  rewrite out_loop_eq.
  destruct (bdec (i <? NM)%uint63) as [Hi' | Hi'].
  - pose proof Hi' as Hi''. rewrite ltb_spec, phi_NM in Hi''.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by (apply phi_add1; lia).
    assert (Hdec : Zwf 0 (gap NM (i + 1)) z) by (rewrite <- Hz; apply dec_step; exact Hi').
    pose proof (cZ_bounds (mkb mk) (φ i) ltac:(lia)) as B.
    pose proof (ml_S (mkb mk) (φ i) ltac:(lia)) as MS.
    pose proof (ml_len_cZ (mkb mk) (φ i) ltac:(lia)) as ML.
    destruct (mk.[i] =? 0)%uint63 eqn:E.
    + rewrite eqb_Z, rd_get in E. change (φ 0) with 0 in E.
      assert (Hf : mkb mk (φ i) = false) by (unfold mkb; rewrite E; reflexivity).
      rewrite Hf, app_nil_r in MS.
      eapply IH; [exact Hdec | reflexivity | lia | exact Hl | exact HL | | ].
      * rewrite Hi1, cZ_S, Hf by lia. lia.
      * rewrite Hi1, MS. exact Hinv.
    + rewrite eqb_Z, rd_get in E. change (φ 0) with 0 in E.
      assert (Hf : mkb mk (φ i) = true) by (unfold mkb; rewrite E; reflexivity).
      rewrite Hf in MS.
      assert (Hup : cZ (mkb mk) ((φ i) + 1) = cZ (mkb mk) (φ i) + 1) by (rewrite cZ_S, Hf by lia; reflexivity).
      pose proof (cZ_mono_n (mkb mk) ((φ i) + 1) 2000 ltac:(lia)) as Mn.
      assert (Hpl : (φ p) < L) by lia.
      eapply IH; [exact Hdec | reflexivity | lia | rewrite len_set; exact Hl | exact HL | | ].
      * rewrite Hi1, Hup, phi_add1 by lia. lia.
      * rewrite Hi1, MS. intros n Hn. rewrite length_app in Hn. simpl List.length in Hn.
        destruct (Nat.lt_ge_cases n (List.length (ml (mkb mk) (Z.to_nat (φ i))))) as [Lt|Ge].
        -- rewrite nth_error_app1 by exact Lt. rewrite Hinv by exact Lt.
           rset. destruct (Z.eq_dec (Z.of_nat n) (φ p)); [lia|reflexivity].
        -- assert (En : n = List.length (ml (mkb mk) (Z.to_nat (φ i)))) by lia.
           rewrite nth_error_app2 by lia. rewrite <- En, Nat.sub_diag. simpl nth_error.
           rset. destruct (Z.eq_dec (Z.of_nat n) (φ p)) as [_|F]; [|lia].
           f_equal. rewrite add_spec, Z.mod_small; [reflexivity|].
           change ((φ 1000)%uint63) with 1000. rewrite wB_val. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec, phi_NM in Hi'.
    assert (E : Z.to_nat (φ i) = 2000%nat) by lia. rewrite E in Hinv.
    split; [exact Hl | exact Hinv].
Qed.

Lemma count_marks_spec : forall mk,
  (φ (count_marks mk)) = Z.of_nat (List.length (ml (mkb mk) 2000)).
Proof.
  intros mk. unfold count_marks. rewrite cnt_loop_spec with (z := gap NM 0%uint63);
    [apply cZ_ml | reflexivity | change ((φ 0)%uint63) with 0; lia | reflexivity].
Qed.

Lemma ml_count_bound : forall f, (List.length (ml f 2000) <= 2000)%nat.
Proof. intros f. rewrite ml_length. apply count_le. Qed.

Definition outN (mk : array int) : list N := map Z.to_N (ml (mkb mk) 2000).

Lemma repr_out : forall (r : array int) (l : list Z),
  (φ (PArray.length r)) = Z.of_nat (List.length l) ->
  (forall n, (n < List.length l)%nat -> nth_error l n = Some (rd r (Z.of_nat n))) ->
  repr (r : array uint) (map Z.to_N l).
Proof.
  intros r l Hl Hn. split.
  - rewrite length_map. exact (eq_sym Hl).
  - intros k Hk. rewrite length_map in Hk. exists (Z.to_N (rd r (Z.of_nat k))). split.
    + rewrite nth_error_map, Hn by exact Hk. reflexivity.
    + reflexivity.
Qed.

Lemma build_spec : forall mk, repr (build mk : array uint) (outN mk).
Proof.
  intros mk. unfold build, outN.
  pose proof (count_marks_spec mk) as Hc. pose proof (ml_count_bound (mkb mk)) as Hb.
  destruct (out_loop_spec mk (φ (count_marks mk)) _ 0%uint63 0%uint63
              (PArray.make (count_marks mk) 0%uint63) (Zwf_well_founded 0 (gap NM 0%uint63)) eq_refl
              ltac:(change ((φ 0)%uint63) with 0; lia)
              ltac:(rewrite len_make by lia; reflexivity)
              ltac:(rewrite cZ_ml; lia)
              ltac:(change ((φ 0)%uint63) with 0; reflexivity)
              ltac:(intros n Hn; change ((φ 0)%uint63) with 0 in Hn; simpl in Hn; lia)) as [Hl Hn].
  apply repr_out; [rewrite Hl; exact Hc | exact Hn].
Qed.

Lemma outN_NoDup : forall mk, NoDup (outN mk).
Proof.
  intros mk. unfold outN. apply NoDup_map_on; [apply ml_NoDup|].
  intros a b Ha Hb E. apply ml_In in Ha, Hb.
  destruct Ha as (i & Hi & _ & Ha). destruct Hb as (j & Hj & _ & Hb).
  apply Z2N.inj in E; lia.
Qed.

Lemma outN_In : forall mk (a : N), In (Z.of_N a) (ml (mkb mk) 2000) -> In a (outN mk).
Proof.
  intros mk a H. unfold outN. apply in_map_iff. exists (Z.of_N a). split; [apply N2Z.id | exact H].
Qed.

Lemma outN_len : forall mk, List.length (outN mk) = List.length (ml (mkb mk) 2000).
Proof. intros mk. unfold outN. apply length_map. Qed.

(* ------------------------------------------------------------------ *)
(* Back to the contract's lists                                        *)
(* ------------------------------------------------------------------ *)

Lemma Forall_combine_iff : forall (P : N * N -> Prop) (a b : list N),
  List.length a = List.length b ->
  (Forall P (combine a b) <->
   forall k, (k < List.length a)%nat -> P (nth k a 0%N, nth k b 0%N)).
Proof.
  intros P a b Hl. rewrite Forall_forall. split.
  - intros H k Hk. apply H. rewrite <- combine_nth by exact Hl. apply nth_In.
    rewrite length_combine. lia.
  - intros H t Ht. apply (In_nth _ _ (0%N, 0%N)) in Ht. destruct Ht as (k & Hk & Ht).
    rewrite length_combine in Hk. rewrite combine_nth in Ht by exact Hl. subst t. apply H. lia.
Qed.

Lemma NoDup_remove_N : forall (a : N) l, NoDup l -> NoDup (remove N.eq_dec a l).
Proof.
  intros a l H. induction H as [|x l Hx Hl IH]; simpl; [constructor|].
  destruct (N.eq_dec a x); [exact IH|]. constructor; [|exact IH].
  intro F. apply in_remove in F. tauto.
Qed.

Lemma repr_in : forall (x : array@{Set} uint) (l : list N), repr x l ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l) /\
  forall k, (k < List.length l)%nat -> rd x (Z.of_nat k) = Z.of_N (nth k l 0%N).
Proof.
  intros x l [Hl Hc]. split; [exact (eq_sym Hl)|].
  intros k Hk. destruct (Hc k Hk) as (m & Hm & Hr).
  rewrite (nth_error_nth l k 0%N Hm). rewrite <- Hr.
  unfold rd. rewrite Z2N.id; [reflexivity|]. apply phi_nonneg.
Qed.

Section Final.
Variables (st lo : list N) (x y : array uint).
Hypothesis Hv : valid_input st lo.
Hypothesis Hx : repr x st.
Hypothesis Hy : repr y lo.

(* The covering condition on the teams not owned by ex. *)
Definition covers (ex : Z) (c : list N) : Prop :=
  forall k, (k < List.length st)%nat -> Z.of_N (nth k st 0%N) <> ex ->
    In (nth k st 0%N) c \/ In (nth k lo 0%N) c.

Lemma lens : List.length lo = List.length st.
Proof. destruct Hv as [_ Hp _ _ _]. unfold len in Hp. lia. Qed.

Lemma st_range : forall k, (k < List.length st)%nat -> (1000 <= nth k st 0%N <= 1999)%N.
Proof.
  intros k Hk. destruct Hv as [_ _ Hs _ _]. rewrite Forall_forall in Hs.
  apply Hs. apply nth_In. exact Hk.
Qed.

Lemma lo_range : forall k, (k < List.length st)%nat -> (2000 <= nth k lo 0%N <= 2999)%N.
Proof.
  intros k Hk. destruct Hv as [_ _ _ Hs _]. rewrite Forall_forall in Hs.
  apply Hs. apply nth_In. rewrite lens. exact Hk.
Qed.

Lemma Hlen_xy : PArray.length y = PArray.length x.
Proof.
  destruct (repr_in x st Hx) as [Lx _]. destruct (repr_in y lo Hy) as [Ly _].
  apply to_Z_inj. rewrite Lx, Ly, lens. reflexivity.
Qed.

Lemma Hrange_xy : forall j, 0 <= j < (φ (PArray.length x)) ->
  1000 <= rd x j <= 1999 /\ 2000 <= rd y j <= 2999.
Proof.
  intros j Hj. destruct (repr_in x st Hx) as [Lx Rx]. destruct (repr_in y lo Hy) as [Ly Ry].
  rewrite Lx in Hj. replace j with (Z.of_nat (Z.to_nat j)) by lia.
  rewrite Rx, Ry by (rewrite ?lens; lia).
  pose proof (st_range (Z.to_nat j) ltac:(lia)). pose proof (lo_range (Z.to_nat j) ltac:(lia)).
  lia.
Qed.

Lemma Gx_team : forall (ex : int) u v, Gx x y ex u v <->
  exists k, (k < List.length st)%nat /\ Z.of_N (nth k st 0%N) <> (φ ex) /\
            Z.of_N (nth k st 0%N) = 1000 + u /\ Z.of_N (nth k lo 0%N) = 2000 + v.
Proof.
  intros ex u v. destruct (repr_in x st Hx) as [Lx Rx]. destruct (repr_in y lo Hy) as [Ly Ry].
  split.
  - intros (j & Hj0 & Hk & Hu & Hw).
    assert (Hj : 0 <= j < Z.of_nat (List.length st)) by (rewrite <- Lx; exact Hj0).
    exists (Z.to_nat j).
    replace j with (Z.of_nat (Z.to_nat j)) in Hk, Hu, Hw by lia.
    rewrite Rx in Hk, Hu by lia. rewrite Ry in Hw by (rewrite lens; lia).
    split; [lia|]. auto.
  - intros (k & Hk & Hne & Hu & Hw). exists (Z.of_nat k).
    rewrite Rx by exact Hk. rewrite Ry by (rewrite lens; exact Hk).
    split; [assert (0 <= Z.of_nat k < (φ (PArray.length@{Set} x))) by (rewrite Lx; lia); assumption|]. auto.
Qed.

Lemma engine_N : forall ex : int,
  covers (φ ex) (outN (engine x y ex)) /\
  (forall c', NoDup c' -> covers (φ ex) c' ->
     (List.length (outN (engine x y ex)) <= List.length c')%nat) /\
  (φ (PArray.length (engine x y ex))) = 2000.
Proof.
  intros ex.
  destruct (engine_spec x y ex Hlen_xy Hrange_xy) as (Hl & Hcov & Hmin).
  split; [|split; [|exact Hl]].
  - intros k Hk Hne.
    pose proof (st_range k Hk). pose proof (lo_range k Hk).
    assert (HG : Gx x y ex (Z.of_N (nth k st 0%N) - 1000) (Z.of_N (nth k lo 0%N) - 2000)).
    { apply Gx_team. exists k. split; [exact Hk|]. split; [exact Hne|]. split; lia. }
    destruct (Hcov _ _ HG) as [I|I]; [left|right]; apply outN_In;
      [replace (Z.of_N (nth k st 0%N)) with (1000 + (Z.of_N (nth k st 0%N) - 1000)) by lia
      |replace (Z.of_N (nth k lo 0%N)) with (2000 + (Z.of_N (nth k lo 0%N) - 2000)) by lia];
      exact I.
  - intros c' Hc' Hcov'. rewrite outN_len.
    rewrite <- (length_map Z.of_N c').
    apply Hmin.
    + apply NoDup_map_on; [exact Hc'|]. intros a b _ _ E. lia.
    + intros u v HG. apply Gx_team in HG. destruct HG as (k & Hk & Hne & Hu & Hw).
      destruct (Hcov' k Hk Hne) as [I|I]; [left|right];
        [rewrite <- Hu | rewrite <- Hw]; apply in_map; exact I.
Qed.

Lemma invitation_covers : forall c, invitation st lo c <-> NoDup c /\ covers 0 c.
Proof.
  intros c. unfold invitation, teams. rewrite Forall_combine_iff by (symmetry; exact lens).
  split.
  - intros [Hn Hc]. split; [exact Hn|]. intros k Hk _. exact (Hc k Hk).
  - intros [Hn Hc]. split; [exact Hn|]. intros k Hk. apply Hc; [exact Hk|].
    pose proof (st_range k Hk). lia.
Qed.

Lemma len_le : forall (a b : list N), (List.length a <= List.length b)%nat -> (len a <= len b)%N.
Proof. intros a b H. unfold len. lia. Qed.

Lemma main_correct :
  exists c : list N, repr (bilateral_impl x y) c /\ bilateral_spec st lo c.
Proof.
  destruct (engine_N 1009%uint63) as (Cov1 & Min1 & L1).
  destruct (engine_N 0%uint63) as (Cov0 & Min0 & L0).
  change ((φ 1009)%uint63) with 1009 in Cov1, Min1.
  change ((φ 0)%uint63) with 0 in Cov0, Min0.
  set (mk1 := engine x y 1009%uint63) in *.
  set (mk0 := engine x y 0%uint63) in *.
  assert (Inv0 : invitation st lo (outN mk0))
    by (apply invitation_covers; split; [apply outN_NoDup | exact Cov0]).
  assert (Small0 : forall c', invitation st lo c' -> (len (outN mk0) <= len c')%N).
  { intros c' Hc'. apply invitation_covers in Hc'. destruct Hc' as [Hn Hc].
    apply len_le. apply Min0; assumption. }
  pose proof (count_marks_spec mk1) as K1. pose proof (count_marks_spec mk0) as K0.
  pose proof (ml_count_bound (mkb mk1)) as B1. pose proof (ml_count_bound (mkb mk0)) as B0.
  rewrite <- outN_len in K1, K0, B1, B0.
  unfold bilateral_impl. cbv zeta. fold mk1 mk0.
  destruct (count_marks mk1 + 1 <=? count_marks mk0)%uint63 eqn:Eb.
  - rewrite leb_spec, phi_add1 in Eb by lia. rewrite K1, K0 in Eb.
    set (mk := mk1.[9 <- 1]%uint63).
    assert (Rmk : forall i, 0 <= i < 2000 -> rd mk i = if Z.eq_dec i 9 then 1 else rd mk1 i).
    { intros i Hi. unfold mk. rewrite rd_set by (rewrite ?wB_val; change ((φ 9)%uint63) with 9; lia).
      reflexivity. }
    assert (Sub : forall a, In a (outN mk1) -> In a (outN mk)).
    { intros a Ha. unfold outN in Ha |- *. apply in_map_iff in Ha. destruct Ha as (b & Hb & Hbl).
      apply in_map_iff. exists b. split; [exact Hb|].
      apply ml_In in Hbl. apply ml_In. destruct Hbl as (i & Hi & Hf & Hbi).
      exists i. split; [exact Hi|]. split; [|exact Hbi].
      unfold mkb in Hf |- *. rewrite Rmk by lia. destruct (Z.eq_dec i 9); [reflexivity|exact Hf]. }
    assert (Fr : In friend (outN mk)).
    { unfold friend. replace 1009%N with (Z.to_N 1009) by reflexivity.
      unfold outN. apply in_map. apply ml_In. exists 9. split; [lia|]. split; [|lia].
      unfold mkb. rewrite Rmk by lia. reflexivity. }
    assert (Len : (List.length (outN mk) <= List.length (outN mk1) + 1)%nat).
    { rewrite !outN_len.
      pose proof (cZ_upd_le (mkb mk1) (mkb mk) 2000 9 ltac:(lia)) as U.
      rewrite !cZ_ml in U. apply Nat2Z.inj_le. rewrite Nat2Z.inj_add. apply U.
      intros i Hi Hne. unfold mkb. rewrite Rmk by lia. destruct (Z.eq_dec i 9); [contradiction|reflexivity]. }
    exists (outN mk). split; [apply build_spec|].
    assert (InvM : invitation st lo (outN mk)).
    { apply invitation_covers. split; [apply outN_NoDup|].
      intros k Hk _. destruct (N.eq_dec (nth k st 0%N) 1009) as [E|E].
      - left. rewrite E. exact Fr.
      - destruct (Cov1 k Hk ltac:(lia)) as [I|I]; [left|right]; apply Sub; exact I. }
    split; [split; [exact InvM|] | intros _; exact Fr].
    intros c' Hc'. pose proof (Small0 c' Hc'). unfold len in *. lia.
  - exists (outN mk0). split; [apply build_spec|].
    split; [split; [exact Inv0 | exact Small0]|].
    intros (cs & (Ics & Scs) & Fcs). exfalso.
    rewrite <- Bool.not_true_iff_false, leb_spec, phi_add1 in Eb by lia. rewrite K1, K0 in Eb.
    destruct Ics as [Ncs Ccs]. unfold teams in Ccs.
    rewrite Forall_combine_iff in Ccs by (symmetry; exact lens).
    set (r := remove N.eq_dec friend cs).
    assert (Hr : (List.length (outN mk1) <= List.length r)%nat).
    { apply Min1; [apply NoDup_remove_N; exact Ncs|].
      intros k Hk Hne. pose proof (lo_range k Hk).
      destruct (Ccs k Hk) as [I|I]; [left|right]; apply in_in_remove; auto; unfold friend; lia. }
    pose proof (remove_length_lt N.eq_dec cs friend Fcs) as Hlt. fold r in Hlt.
    pose proof (Scs (outN mk0) Inv0) as H0. unfold len in H0. lia.
Qed.

End Final.

Definition bilateral_correct :
  forall (st lo : list N) (x y : array uint),
  valid_input st lo -> repr x st -> repr y lo ->
  exists c : list N, repr (bilateral x y) c /\ bilateral_spec st lo c
  := main_correct.
