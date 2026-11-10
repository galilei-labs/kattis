From Indoorienteering.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf Bool Permutation.
From Stdlib Require Import FinFun.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* Termination devices                                                 *)
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

(* The measure of a search node: remaining depth r, next candidate v. *)
Definition meas (n r v : int) : Z := ((φ r) * ((φ n) + 1) + ((φ n) - (φ v)))%Z.

Lemma dec_sib : forall n r v : int,
  (r =? 0) = false -> (v <? n) = true -> Zwf 0 (meas n r (v + 1)) (meas n r v).
Proof.
  intros n r v Hr Hv. rewrite ltb_spec in Hv.
  assert (H1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded n).
  unfold Zwf, meas. rewrite H1. nia.
Qed.

Lemma dec_child : forall n r v : int,
  (r =? 0) = false -> (v <? n) = true -> Zwf 0 (meas n (r - 1) 0) (meas n r v).
Proof.
  intros n r v Hr Hv. rewrite ltb_spec in Hv.
  rewrite eqb_false_spec in Hr.
  assert (Hr' : (φ r) <> 0%Z) by (intro E; apply Hr; apply to_Z_inj; exact E).
  assert (H1 : (φ (r - 1)) = ((φ r) - 1)%Z) by (pose proof (to_Z_bounded r); sia).
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded n). pose proof (to_Z_bounded v).
  unfold Zwf, meas. rewrite H1. change (φ 0) with 0%Z. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* The hash table: one flat int array, 0 = empty slot, linear probing  *)
(* without wrap-around (a probe that runs off the end fails).          *)
(* ------------------------------------------------------------------ *)

Definition hmul : int := 7046029254386353131.

(* multiplicative hashing: the top bits of k * hmul *)
Definition hidx (sh k : int) : int := (k * hmul) >> sh.

(* the first slot from i on that is empty or holds k; PArray.length t
   when there is none *)
Fixpoint find (t : array int) (k i : int)
    (H : Acc (Zwf 0) (gap (PArray.length t) i)) {struct H} : int :=
  match bdec (i <? PArray.length t) with
  | left Hi =>
      let x := t.[i] in
      if (x =? 0) || (x =? k) then i
      else find t k (i + 1) (Acc_inv H (dec_step _ _ Hi))
  | right _ => i
  end.

Definition find0 (sh : int) (t : array int) (k : int) : int :=
  find t k (hidx sh k) (Zwf_well_founded 0 _).

Definition lookup (sh : int) (t : array int) (k : int) : bool :=
  let j := find0 sh t k in
  (j <? PArray.length t) && (t.[j] =? k).

(* the table with k in it, and true; or t unchanged and false when the
   probe ran off the end *)
Definition insert (sh : int) (t : array int) (k : int) : array int * bool :=
  let j := find0 sh t k in
  if j <? PArray.length t then
    (if t.[j] =? 0 then (t.[j <- k], true) else (t, true))
  else (t, false).

(* ------------------------------------------------------------------ *)
(* The two half-path searches for one middle point m                   *)
(* ------------------------------------------------------------------ *)

(* the packed key of (set S, length l): S * 2^50 + l + 1, never 0 *)
Definition key (S l : int) : int := ((S << 50) + l) + 1.

Section Search.

(* D: the flat n x n distance matrix; a: the anchor (n - 1); m: the middle
   point; fp: the mask of the n - 2 other points; need: the mask the first
   side's sets must contain (the symmetry); fr2 = fp minus need: the points
   of the second side; base2 = need; k2: the second side's depth; sh: the
   hash shift; size: the table length. *)
Variables (D : array int) (n L a m fp need fr2 base2 k2 sh size : int).

(* Second side: from the current point c, with the free points free, the
   length so far len and r points still to choose, candidates from v on:
   is there a completion back to the anchor whose probe key is in t? *)
Fixpoint pdfs (t : array int) (c free len r v : int)
    (H : Acc (Zwf 0) (meas n r v)) {struct H} : bool :=
  match bdec (r =? 0) with
  | left _ =>
      let l := len + D.[c * n + a] in
      if l <=? L then lookup sh t (key (base2 lxor free) (L - l)) else false
  | right Hr =>
      match bdec (v <? n) with
      | left Hv =>
          let bv := 1 << v in
          if (free land bv) =? 0 then
            pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else
            let l := len + D.[c * n + v] in
            if l <=? L then
              if pdfs t v (free lxor bv) l (r - 1) 0 (Acc_inv H (dec_child n r v Hr Hv))
              then true
              else pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
            else pdfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
      | right _ => false
      end
  end.

(* A first-side half-path of key k reaches the table: inserted, or, when
   the probe runs off the end, the table is first probed by the whole
   second side ("flush") and k goes into a fresh one. *)
Definition leafins (t : array int) (k : int) : array int * bool :=
  match insert sh t k with
  | (t1, true) => (t1, false)
  | (t1, false) =>
      if pdfs t1 m fr2 0 k2 0 (Zwf_well_founded 0 _) then (t1, true)
      else (fst (insert sh (PArray.make size 0) k), false)
  end.

(* First side: from the anchor to m; returns the table and "found". *)
Fixpoint idfs (t : array int) (c free len r v : int)
    (H : Acc (Zwf 0) (meas n r v)) {struct H} : array int * bool :=
  match bdec (r =? 0) with
  | left _ =>
      let l := len + D.[c * n + m] in
      if l <=? L then leafins t (key (fp lxor free) l) else (t, false)
  | right Hr =>
      match bdec (v <? n) with
      | left Hv =>
          let bv := 1 << v in
          if (free land bv) =? 0 then
            idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else if (r =? 1) && negb ((need land (free lxor bv)) =? 0) then
            idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
          else
            let l := len + D.[c * n + v] in
            if l <=? L then
              match idfs t v (free lxor bv) l (r - 1) 0
                      (Acc_inv H (dec_child n r v Hr Hv)) with
              | (t1, true) => (t1, true)
              | (t1, false) =>
                  idfs t1 c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
              end
            else idfs t c free len r (v + 1) (Acc_inv H (dec_sib n r v Hr Hv))
      | right _ => (t, false)
      end
  end.

End Search.

(* One middle point m: build the table of the first side, then probe it. *)
Definition search_m (D : array int) (n L a k1 k2 sh size m : int) : bool :=
  let fp := ((1 << a) - 1) lxor (1 << m) in
  let need := if ((n land 1) =? 0) && (4 <=? n)
              then 1 << (if m =? 0 then 1 else 0) else 0 in
  let fr2 := fp lxor need in
  match idfs D n L a m fp need fr2 need k2 sh size (PArray.make size 0)
          a fp 0 k1 0 (Zwf_well_founded 0 _) with
  | (_, true) => true
  | (t, false) => pdfs D n L a need sh t m fr2 0 k2 0 (Zwf_well_founded 0 _)
  end.

Fixpoint mloop (D : array int) (n L a k1 k2 sh size m : int)
    (H : Acc (Zwf 0) (gap a m)) {struct H} : bool :=
  match bdec (m <? a) with
  | left Hm =>
      if search_m D n L a k1 k2 sh size m then true
      else mloop D n L a k1 k2 sh size (m + 1) (Acc_inv H (dec_step a m Hm))
  | right _ => false
  end.

(* The input matrix, flattened: cell i holds x.[i / n].[i mod n]. *)
Fixpoint fill (x : array (array int)) (n N i : int) (D : array int)
    (H : Acc (Zwf 0) (gap N i)) {struct H} : array int :=
  match bdec (i <? N) with
  | left Hi => fill x n N (i + 1) D.[i <- x.[i / n].[i mod n]] (Acc_inv H (dec_step N i Hi))
  | right _ => D
  end.

(* log2 of the table capacity: at least twice the first side's half-paths *)
Definition logcap (n : int) : int :=
  if n <=? 8 then 7 else if n =? 9 then 9 else if n =? 10 then 11
  else if n =? 11 then 13 else if n =? 12 then 15 else if n =? 13 then 17
  else 20.

Definition indoor (x : array (array uint)) (L : uint) : bool :=
  let n := PArray.length x in
  let N := n * n in
  let D := fill x n N 0 (PArray.make N 0) (Zwf_well_founded 0 _) in
  let a := n - 1 in
  let k1 := (n - 2) / 2 in
  let k2 := n - 2 - k1 in
  let b := logcap n in
  mloop D n L a k1 k2 (63 - b) ((1 << b) + 256) 0 (Zwf_well_founded 0 _).

(* ================================================================== *)
(* Proofs                                                              *)
(* ================================================================== *)

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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

Lemma eqb_true : forall x y : int, (x =? y) = true <-> x = y.
Proof. intros. apply Uint63.eqb_spec. Qed.

Lemma eqb_false : forall x y : int, (x =? y) = false <-> x <> y.
Proof. intros. apply eqb_false_spec. Qed.

Lemma int_neq : forall x y : int, (φ x) <> (φ y) -> x <> y.
Proof. intros x y H E. apply H. rewrite E. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The hash table                                                      *)
(* ------------------------------------------------------------------ *)

Lemma find_eq : forall t k i H,
  find t k i H =
  match bdec (i <? PArray.length t) with
  | left Hi =>
      let x := t.[i] in
      if (x =? 0) || (x =? k) then i
      else find t k (i + 1) (Acc_inv H (dec_step _ _ Hi))
  | right _ => i
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma find_spec : forall (t : array int) (k : int) (z : Z) (i : int) H,
  gap (PArray.length t) i = z ->
  let j := find t k i H in
  ((φ i) <= (φ j))%Z /\
  (forall s : int, ((φ i) <= (φ s) < (φ j))%Z ->
     ((φ s) < (φ (PArray.length t)))%Z /\ t.[s] <> 0 /\ t.[s] <> k) /\
  (((φ j) < (φ (PArray.length t)))%Z -> t.[j] = 0 \/ t.[j] = k).
Proof.
  intros t k z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i H Hz j. subst j. rewrite find_eq.
  destruct (bdec (i <? PArray.length t)) as [Hi | Hi].
  - pose proof Hi as Hi'. rewrite ltb_spec in Hi'. cbv zeta.
    destruct ((t.[i] =? 0) || (t.[i] =? k)) eqn:E.
    + split; [lia|]. split; [intros s Hs; lia|].
      intros _. apply orb_true_iff in E. destruct E as [E|E]; apply eqb_true in E; auto.
    + apply orb_false_iff in E. destruct E as [E1 E2].
      apply eqb_false in E1. apply eqb_false in E2.
      assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
      destruct (IH (gap (PArray.length t) (i + 1)) ltac:(rewrite <- Hz; apply dec_step; exact Hi)
                  (i + 1) (Acc_inv H (dec_step _ _ Hi)) eq_refl) as (A & B & C).
      split; [lia|]. split; [|exact C].
      intros s Hs. destruct (Z.eq_dec (φ s) (φ i)) as [Es|Es].
      * apply to_Z_inj in Es. subst s. auto.
      * apply B. lia.
  - split; [lia|]. split; [intros s Hs; lia|].
    intros Hj. rewrite <- Bool.not_true_iff_false, ltb_spec in Hi. lia.
Qed.

Section Hash.
Variable sh : int.

(* k is reachable from its hash slot: slot j holds k and every slot between
   is occupied by another key *)
Definition LK (t : array int) (k : int) : Prop :=
  exists j : int, ((φ (hidx sh k)) <= (φ j) < (φ (PArray.length t)))%Z /\ t.[j] = k /\
    forall s : int, ((φ (hidx sh k)) <= (φ s) < (φ j))%Z -> t.[s] <> 0 /\ t.[s] <> k.

Lemma find0_spec : forall t k,
  let j := find0 sh t k in
  ((φ (hidx sh k)) <= (φ j))%Z /\
  (forall s : int, ((φ (hidx sh k)) <= (φ s) < (φ j))%Z ->
     ((φ s) < (φ (PArray.length t)))%Z /\ t.[s] <> 0 /\ t.[s] <> k) /\
  (((φ j) < (φ (PArray.length t)))%Z -> t.[j] = 0 \/ t.[j] = k).
Proof. intros t k. unfold find0. eapply find_spec. reflexivity. Qed.

Lemma find0_unique : forall t k j, k <> 0 ->
  ((φ (hidx sh k)) <= (φ j) < (φ (PArray.length t)))%Z -> (t.[j] = 0 \/ t.[j] = k) ->
  (forall s : int, ((φ (hidx sh k)) <= (φ s) < (φ j))%Z -> t.[s] <> 0 /\ t.[s] <> k) ->
  find0 sh t k = j.
Proof.
  intros t k j Hk Hj Hc Hb.
  destruct (find0_spec t k) as (A & B & C).
  set (j' := find0 sh t k) in *.
  destruct (Z.lt_trichotomy (φ j') (φ j)) as [E|[E|E]].
  - destruct (C ltac:(lia)) as [F|F]; destruct (Hb j' ltac:(lia)); contradiction.
  - apply to_Z_inj. exact E.
  - destruct (B j ltac:(lia)) as (_ & F1 & F2). destruct Hc; contradiction.
Qed.

Lemma lookup_iff : forall t k, k <> 0 -> lookup sh t k = true <-> LK t k.
Proof.
  intros t k Hk. unfold lookup. split.
  - intros E. apply andb_true_iff in E. destruct E as [E1 E2].
    rewrite ltb_spec in E1. apply eqb_true in E2.
    destruct (find0_spec t k) as (A & B & C).
    exists (find0 sh t k). split; [lia|]. split; [exact E2|].
    intros s Hs. destruct (B s Hs) as (_ & ? & ?). auto.
  - intros (j & Hj & Hjk & Hb).
    rewrite (find0_unique t k j Hk Hj (or_intror Hjk) Hb).
    apply andb_true_iff. split; [rewrite ltb_spec; lia | apply eqb_true; exact Hjk].
Qed.

Lemma insert_fail : forall t k t', insert sh t k = (t', false) -> t' = t.
Proof.
  intros t k t'. unfold insert.
  destruct (find0 sh t k <? PArray.length t); [destruct (t.[_] =? 0)|]; congruence.
Qed.

Lemma insert_ok : forall t k t', k <> 0 -> insert sh t k = (t', true) ->
  PArray.length t' = PArray.length t /\
  lookup sh t' k = true /\
  (forall k', k' <> 0 -> lookup sh t k' = true -> lookup sh t' k' = true) /\
  (forall s, t'.[s] = t.[s] \/ t'.[s] = k).
Proof.
  intros t k t' Hk. unfold insert.
  destruct (find0_spec t k) as (A & B & C).
  set (j := find0 sh t k) in *.
  destruct (j <? PArray.length t) eqn:Ej; [|congruence].
  rewrite ltb_spec in Ej.
  destruct (t.[j] =? 0) eqn:E0; intros Heq; injection Heq as <-.
  - apply eqb_true in E0.
    assert (Ej' : (j <? PArray.length t) = true) by (rewrite ltb_spec; lia).
    split; [apply alength_set|].
    split.
    + apply lookup_iff; [exact Hk|]. exists j. rewrite alength_set.
      split; [lia|]. split; [apply aget_set_same; exact Ej'|].
      intros s Hs. rewrite aget_set_other by (apply int_neq; lia).
      destruct (B s Hs) as (_ & ? & ?). auto.
    + split.
      * intros k' Hk' Hl. apply lookup_iff in Hl; [|exact Hk'].
        apply lookup_iff; [exact Hk'|].
        destruct Hl as (j' & Hj' & Hjk' & Hb').
        assert (Hne : forall s, ((φ (hidx sh k')) <= (φ s) <= (φ j'))%Z -> j <> s).
        { intros s Hs Es. subst s.
          destruct (Z.eq_dec (φ j) (φ j')) as [F|F].
          - apply to_Z_inj in F. subst j'. congruence.
          - destruct (Hb' j ltac:(lia)). contradiction. }
        exists j'. rewrite alength_set. split; [exact Hj'|].
        split; [rewrite aget_set_other by (apply Hne; lia); exact Hjk'|].
        intros s Hs. rewrite aget_set_other by (apply Hne; lia). apply Hb'. exact Hs.
      * intros s. destruct (j =? s) eqn:Es.
        -- apply eqb_true in Es. subst s. right. apply aget_set_same; exact Ej'.
        -- apply eqb_false in Es. left. apply aget_set_other. exact Es.
  - apply eqb_false in E0. destruct (C Ej) as [F|F]; [contradiction|].
    split; [reflexivity|]. split.
    + apply lookup_iff; [exact Hk|]. exists j. split; [lia|]. split; [exact F|].
      intros s Hs. destruct (B s Hs) as (_ & ? & ?). auto.
    + split; [auto|]. intros s. left. reflexivity.
Qed.

Lemma insert_fresh : forall size k, k <> 0 ->
  ((φ (hidx sh k)) < (φ size))%Z -> ((φ size) <= 4194303)%Z ->
  snd (insert sh (PArray.make size 0) k) = true.
Proof.
  intros size k Hk Hh Hs.
  assert (Hl : PArray.length (PArray.make size 0) = size).
  { rewrite alength_make. replace (size <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia. }
  unfold insert.
  rewrite (find0_unique (PArray.make size 0) k (hidx sh k) Hk).
  - replace (hidx sh k <? PArray.length (PArray.make size 0)) with true.
    + rewrite aget_make. reflexivity.
    + symmetry. rewrite ltb_spec, Hl. exact Hh.
  - rewrite Hl. pose proof (to_Z_bounded (hidx sh k)). lia.
  - left. apply aget_make.
  - intros s Hs0. lia.
Qed.

End Hash.

(* ------------------------------------------------------------------ *)
(* Paths on the math side                                              *)
(* ------------------------------------------------------------------ *)

Section Paths.
Variable d : list (list N).
Local Open Scope N_scope.

(* the length of the path from s through the points of l, in order *)
Fixpoint pl (s : N) (l : list N) : N :=
  match l with
  | [] => 0
  | x :: t => dist d s x + pl x t
  end.

(* the length of the path from s through l and then to e *)
Definition ell (s : N) (l : list N) (e : N) : N := pl s l + dist d (last l s) e.

Lemma last_cons : forall (x : N) t dflt, last (x :: t) dflt = last t x.
Proof.
  intros x t. revert x. induction t as [|y t IH]; intros x dflt; [reflexivity|].
  change (last (x :: y :: t) dflt) with (last (y :: t) dflt).
  rewrite IH. rewrite IH. reflexivity.
Qed.

Lemma last_app_cons : forall (l1 l2 : list N) x dflt,
  last (l1 ++ x :: l2) dflt = last l2 x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x dflt.
  - apply last_cons.
  - rewrite <- app_comm_cons, last_cons. apply IH.
Qed.

Lemma last_snoc : forall (l : list N) x dflt, last (l ++ [x]) dflt = x.
Proof. intros l x dflt. rewrite last_app_cons. reflexivity. Qed.

Lemma pl_app : forall l1 l2 s, pl s (l1 ++ l2) = pl s l1 + pl (last l1 s) l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 s; [simpl; lia|].
  rewrite <- app_comm_cons. cbn [pl]. rewrite IH, last_cons. lia.
Qed.

Lemma pl_snoc : forall l w s, pl s (l ++ [w]) = pl s l + dist d (last l s) w.
Proof. intros l w s. rewrite pl_app. simpl. lia. Qed.

Lemma ell_eq : forall s l e, ell s l e = pl s (l ++ [e]).
Proof. intros s l e. unfold ell. rewrite pl_snoc. reflexivity. Qed.

Lemma pl_le_app : forall s l1 l2, pl s l1 <= pl s (l1 ++ l2).
Proof. intros s l1 l2. rewrite pl_app. lia. Qed.

Lemma pl_le_ell : forall s l e, pl s l <= ell s l e.
Proof. intros s l e. unfold ell. lia. Qed.

Lemma path_length_pl : forall l s, path_length d (s :: l) = pl s l.
Proof.
  induction l as [|x l IH]; intros s; [reflexivity|].
  change (path_length d (s :: x :: l)) with (dist d s x + path_length d (x :: l)).
  rewrite IH. reflexivity.
Qed.

Lemma race_cons : forall x t, race_length d (x :: t) = pl x t + dist d (last t x) x.
Proof.
  intros x t. unfold race_length. rewrite path_length_pl, last_cons. reflexivity.
Qed.

Lemma race_split : forall a xs m ys,
  race_length d (a :: xs ++ m :: ys) = ell a xs m + ell m ys a.
Proof.
  intros a xs m ys. rewrite race_cons, pl_app, last_app_cons. unfold ell.
  simpl. lia.
Qed.

Lemma race_rot1 : forall x t, race_length d (x :: t) = race_length d (t ++ [x]).
Proof.
  intros x [|y t]; [reflexivity|].
  rewrite <- app_comm_cons, !race_cons, pl_snoc, last_snoc.
  cbn [pl]. rewrite last_cons. lia.
Qed.

Lemma race_rot : forall l1 l2, race_length d (l1 ++ l2) = race_length d (l2 ++ l1).
Proof.
  induction l1 as [|x l1 IH]; intros l2.
  - rewrite app_nil_r. reflexivity.
  - rewrite <- app_comm_cons, race_rot1, <- app_assoc, IH, <- app_assoc. reflexivity.
Qed.

Hypothesis Hsym : forall i j, dist d i j = dist d j i.

Lemma pl_rev_snoc : forall l s e, pl s (l ++ [e]) = pl e (rev l ++ [s]).
Proof.
  induction l as [|x l IH]; intros s e.
  - simpl. rewrite Hsym. reflexivity.
  - rewrite <- app_comm_cons. cbn [pl]. rewrite IH. cbn [rev].
    rewrite (pl_snoc (rev l ++ [x]) s e), last_snoc, (Hsym x s). lia.
Qed.

Lemma ell_rev : forall s l e, ell s l e = ell e (rev l) s.
Proof. intros s l e. rewrite !ell_eq. apply pl_rev_snoc. Qed.

End Paths.

(* ------------------------------------------------------------------ *)
(* Masks                                                               *)
(* ------------------------------------------------------------------ *)

(* the mask S with the bits of ys flipped, in order *)
Fixpoint rmv (S : Z) (ys : list N) : Z :=
  match ys with
  | [] => S
  | y :: t => rmv (Z.lxor S (2 ^ Z.of_N y)) t
  end.

Definition memb (v : N) (ys : list N) : bool := existsb (N.eqb v) ys.

Lemma memb_iff : forall v ys, memb v ys = true <-> In v ys.
Proof.
  intros v ys. unfold memb. rewrite existsb_exists. split.
  - intros (x & Hx & E). apply N.eqb_eq in E. subst. exact Hx.
  - intros Hv. exists v. split; [exact Hv | apply N.eqb_refl].
Qed.

Lemma memb_app : forall v l1 l2, memb v (l1 ++ l2) = memb v l1 || memb v l2.
Proof. intros. unfold memb. apply existsb_app. Qed.

Lemma rmv_snoc : forall l y S, rmv S (l ++ [y]) = Z.lxor (rmv S l) (2 ^ Z.of_N y).
Proof. induction l as [|x l IH]; intros y S; simpl; [reflexivity | apply IH]. Qed.

Lemma rmv_nonneg : forall ys S, (0 <= S)%Z -> (0 <= rmv S ys)%Z.
Proof.
  induction ys as [|y t IH]; intros S HS; simpl; [exact HS|].
  apply IH. apply Z.lxor_nonneg. split; intros _; [apply Z.pow_nonneg; lia | exact HS].
Qed.

Lemma rmv_bits : forall ys S, NoDup ys ->
  (forall y, In y ys -> Z.testbit S (Z.of_N y) = true) ->
  forall v : N, Z.testbit (rmv S ys) (Z.of_N v) = Z.testbit S (Z.of_N v) && negb (memb v ys).
Proof.
  induction ys as [|y t IH]; intros S Hnd Hin v.
  - simpl. rewrite andb_true_r. reflexivity.
  - inversion Hnd as [|? ? Hy Hnd']. subst.
    simpl rmv. rewrite IH; [| exact Hnd' |].
    + rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia.
      unfold memb. simpl existsb. fold (memb v t).
      destruct (N.eqb_spec v y) as [E|E].
      * subst v. rewrite Z.eqb_refl, (Hin y (or_introl eq_refl)). reflexivity.
      * replace (Z.of_N y =? Z.of_N v)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite xorb_false_r. reflexivity.
    + intros x Hx. rewrite Z.lxor_spec, Z.pow2_bits_eqb by lia.
      rewrite (Hin x (or_intror Hx)).
      replace (Z.of_N y =? Z.of_N x)%Z with false; [reflexivity|].
      symmetry. apply Z.eqb_neq. intro E. apply Hy. replace y with x by lia. exact Hx.
Qed.

Lemma mask_lt : forall S : Z, (0 <= S)%Z ->
  (forall i, (0 <= i)%Z -> Z.testbit S i = true -> (i < 13)%Z) -> (S < 2 ^ 13)%Z.
Proof.
  intros S HS Hb.
  assert (E : Z.land S (Z.ones 13) = S).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_ones by lia.
    destruct (Z.testbit S i) eqn:T.
    - pose proof (Hb i Hi T). rewrite (proj2 (Z.leb_le 0 i) Hi), (proj2 (Z.ltb_lt i 13) H). reflexivity.
    - reflexivity. }
  rewrite Z.land_ones in E by lia. rewrite <- E. apply Z.mod_pos_bound. lia.
Qed.

Lemma bit_spec : forall v : int, ((φ v) < 63)%Z -> (φ (1 << v)) = (2 ^ (φ v))%Z.
Proof.
  intros v Hv. rewrite lsl_spec. change (φ 1) with 1%Z. rewrite Z.mul_1_l.
  pose proof (to_Z_bounded v). apply Z.mod_small. split; [apply Z.pow_nonneg; lia|].
  rewrite wB_val. change 9223372036854775808%Z with (2 ^ 63)%Z.
  apply Z.pow_lt_mono_r; lia.
Qed.

Lemma land_bit_test : forall (x v : int), ((φ v) < 63)%Z ->
  ((x land (1 << v)) =? 0) = negb (Z.testbit (φ x) (φ v)).
Proof.
  intros x v Hv. pose proof (to_Z_bounded v) as Bv.
  destruct (Z.testbit (φ x) (φ v)) eqn:T; simpl.
  - apply eqb_false. intro E. assert (E' : (φ (x land (1 << v))) = 0%Z) by (rewrite E; reflexivity).
    rewrite land_spec', bit_spec in E' by exact Hv.
    assert (F : Z.testbit (Z.land (φ x) (2 ^ (φ v))) (φ v) = true)
      by (rewrite Z.land_spec, T, Z.pow2_bits_eqb, Z.eqb_refl by lia; reflexivity).
    rewrite E' in F. rewrite Z.testbit_0_l in F. discriminate.
  - apply eqb_true. apply to_Z_inj. rewrite land_spec', bit_spec by exact Hv.
    change (φ 0) with 0%Z. apply Z.bits_inj'. intros i Hi.
    rewrite Z.land_spec, Z.pow2_bits_eqb, Z.testbit_0_l by lia.
    destruct (Z.eqb_spec (φ v) i) as [E|E]; [subst i; rewrite T; reflexivity | apply andb_false_r].
Qed.

Lemma add_small : forall x y : int, ((φ x) + (φ y) < wB)%Z -> (φ (x + y)) = ((φ x) + (φ y))%Z.
Proof. intros x y H. rewrite add_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.

Lemma key_spec : forall S l : int, ((φ S) < 2 ^ 13)%Z -> ((φ l) < 2 ^ 50 - 1)%Z ->
  (φ (key S l)) = ((φ S) * 2 ^ 50 + (φ l) + 1)%Z.
Proof.
  intros S l HS Hl. pose proof (to_Z_bounded S). pose proof (to_Z_bounded l).
  unfold key.
  assert (E1 : (φ (S << 50)) = ((φ S) * 2 ^ 50)%Z).
  { rewrite lsl_spec. change (φ 50) with 50%Z. apply Z.mod_small. rewrite wB_val. lia. }
  assert (E2 : (φ (S << 50 + l)) = ((φ S) * 2 ^ 50 + (φ l))%Z)
    by (rewrite add_small; rewrite E1; [reflexivity | rewrite wB_val; lia]).
  rewrite add_small; rewrite E2; change (φ 1) with 1%Z; [reflexivity | rewrite wB_val; lia].
Qed.

Definition tN (v : int) : N := Z.to_N (φ v).

Lemma tN_spec : forall v, Z.of_N (tN v) = (φ v).
Proof. intros v. unfold tN. pose proof (to_Z_bounded v). lia. Qed.

Definition HeadGe (v : int) (ys : list N) : Prop :=
  match ys with [] => True | w :: _ => ((φ v) <= Z.of_N w)%Z end.

Lemma nodup_snoc : forall (l : list N) x, NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros l x Hl Hx. apply Permutation_NoDup with (x :: l).
  - apply Permutation_cons_append.
  - constructor; assumption.
Qed.

(* splitting a completion on its first point: v itself, or a later one *)
Lemma split_head : forall (Q : list N -> Prop) (chosen : list N) (v : int),
  (φ (v + 1)) = ((φ v) + 1)%Z ->
  (forall l, Q (chosen ++ l) -> l <> []) ->
  (exists ys, HeadGe v ys /\ Q (chosen ++ ys)) <->
  (exists ys, Q ((chosen ++ [tN v]) ++ ys)) \/
  (exists ys, HeadGe (v + 1) ys /\ Q (chosen ++ ys)).
Proof.
  intros Q chosen v Hv1 Hne. split.
  - intros ([|w t] & Hh & Hq); [exfalso; exact (Hne [] Hq eq_refl)|].
    simpl in Hh. destruct (Z.eq_dec (Z.of_N w) (φ v)) as [E|E].
    + left. exists t. rewrite <- app_assoc.
      replace (tN v) with w by (rewrite <- tN_spec in E; lia). exact Hq.
    + right. exists (w :: t). split; [simpl; lia | exact Hq].
  - intros [(t & Hq) | (ys & Hh & Hq)].
    + exists (tN v :: t). split; [simpl; rewrite tN_spec; lia|].
      rewrite <- app_assoc in Hq. exact Hq.
    + exists ys. split; [destruct ys; simpl in *; lia | exact Hq].
Qed.

(* the same split, for a property of every completion *)
Lemma split_head_all : forall (F P : list N -> Prop) (chosen : list N) (v : int),
  (φ (v + 1)) = ((φ v) + 1)%Z ->
  (forall l, F (chosen ++ l) -> l <> []) ->
  (forall xs, F ((chosen ++ [tN v]) ++ xs) -> P ((chosen ++ [tN v]) ++ xs)) ->
  (forall xs, HeadGe (v + 1) xs -> F (chosen ++ xs) -> P (chosen ++ xs)) ->
  forall xs, HeadGe v xs -> F (chosen ++ xs) -> P (chosen ++ xs).
Proof.
  intros F P chosen v Hv1 Hne Hc Hs [|w xs] Hh Hf; [exfalso; exact (Hne [] Hf eq_refl)|].
  simpl in Hh. destruct (Z.eq_dec (Z.of_N w) (φ v)) as [E|E].
  - replace w with (tN v) in * by (rewrite <- tN_spec in E; lia).
    replace (chosen ++ tN v :: xs) with ((chosen ++ [tN v]) ++ xs) in *
      by (rewrite <- app_assoc; reflexivity).
    apply Hc. exact Hf.
  - apply Hs; [simpl; lia | exact Hf].
Qed.

(* ------------------------------------------------------------------ *)
(* The searches for one middle point                                   *)
(* ------------------------------------------------------------------ *)

Lemma bool_A : forall f nd x y : bool,
  (x = true -> f = true) -> (y = true -> f = true /\ nd = false) ->
  xorb f (f && negb x) = xorb nd (f && negb nd && negb y) ->
  (x = true -> y = false) /\ (f = true -> x = true \/ y = true).
Proof. intros [] [] [] []; simpl; intuition congruence. Qed.

Lemma bool_B : forall f nd x y : bool,
  (nd = true -> f = true) -> (x = true -> f = true) ->
  (y = true -> f = true /\ nd = false) -> (nd = true -> x = true) ->
  (f = true -> x = true \/ y = true) -> (x = true -> y = false) ->
  xorb f (f && negb x) = xorb nd (f && negb nd && negb y).
Proof. intros [] [] [] []; simpl; intuition congruence. Qed.

Lemma nodup_app_disj : forall (l1 l2 : list N) v,
  NoDup (l1 ++ l2) -> In v l1 -> In v l2 -> False.
Proof.
  induction l1 as [|x l1 IH]; intros l2 v Hnd H1 H2; [destruct H1|].
  inversion Hnd as [|? ? Hx Hnd']. subst.
  destruct H1 as [E|H1]; [subst x; apply Hx; apply in_or_app; right; exact H2|].
  exact (IH l2 v Hnd' H1 H2).
Qed.

Section Spec.
Variable d : list (list N).
Variables (D : array int) (n L a m fp need fr2 k1 k2 sh size : int).

Hypothesis Hn : (φ n) = Z.of_nat (List.length d).
Hypothesis Hn2 : (2 <= (φ n) <= 14)%Z.
Hypothesis HL : (1 <= (φ L) <= 10 ^ 15)%Z.
Hypothesis Hdist : forall i j, (Z.of_N (dist d i j) <= (φ L))%Z.
Hypothesis HD : forall i j : int, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
  (φ (D.[i * n + j])) = Z.of_N (dist d (tN i) (tN j)).
Hypothesis Ha : (φ a) = ((φ n) - 1)%Z.
Hypothesis Hm : ((φ m) < (φ a))%Z.
Hypothesis Hfp : forall i, (0 <= i)%Z ->
  Z.testbit (φ fp) i = (i <? (φ a))%Z && negb (i =? (φ m))%Z.
Hypothesis Hneed : forall i, Z.testbit (φ need) i = true -> Z.testbit (φ fp) i = true.
Hypothesis Hfr2 : forall i, Z.testbit (φ fr2) i = Z.testbit (φ fp) i && negb (Z.testbit (φ need) i).
Hypothesis Hsh : forall k, ((φ (hidx sh k)) < (φ size))%Z.
Hypothesis Hsize : ((φ size) <= 4194303)%Z.

Local Notation sN := (tN m).
Local Notation aN := (tN a).

(* a first half: from the anchor through xs to m *)
Definition FH (xs : list N) : Prop :=
  NoDup xs /\ Z.of_nat (List.length xs) = (φ k1) /\
  (forall x, In x xs -> Z.testbit (φ fp) (Z.of_N x) = true) /\
  (forall v : N, Z.testbit (φ need) (Z.of_N v) = true -> In v xs) /\
  (Z.of_N (ell d aN xs sN) <= (φ L))%Z.

(* a second half: from m through ys back to the anchor *)
Definition SH (ys : list N) : Prop :=
  NoDup ys /\ Z.of_nat (List.length ys) = (φ k2) /\
  (forall y, In y ys -> Z.testbit (φ fr2) (Z.of_N y) = true) /\
  (Z.of_N (ell d sN ys aN) <= (φ L))%Z.

(* the key a first half is stored under, and the key a second half probes *)
Definition K1 (xs : list N) : Z :=
  (Z.lxor (φ fp) (rmv (φ fp) xs) * 2 ^ 50 + Z.of_N (ell d aN xs sN) + 1)%Z.
Definition K2 (ys : list N) : Z :=
  (Z.lxor (φ need) (rmv (φ fr2) ys) * 2 ^ 50 + ((φ L) - Z.of_N (ell d sN ys aN)) + 1)%Z.

Definition KeyIn (t : array int) (z : Z) : Prop :=
  exists k : int, (φ k) = z /\ lookup sh t k = true.

Lemma fp_point : forall i, (0 <= i)%Z -> Z.testbit (φ fp) i = true ->
  (i < (φ a))%Z /\ i <> (φ m).
Proof.
  intros i Hi T. rewrite Hfp in T by exact Hi.
  apply andb_true_iff in T. destruct T as [T1 T2]. apply Z.ltb_lt in T1.
  apply negb_true_iff, Z.eqb_neq in T2. auto.
Qed.

Lemma fr2_fp : forall i, Z.testbit (φ fr2) i = true -> Z.testbit (φ fp) i = true.
Proof. intros i T. rewrite Hfr2 in T. apply andb_true_iff in T. apply T. Qed.

Lemma fr2_point : forall y : N, Z.testbit (φ fr2) (Z.of_N y) = true ->
  (Z.of_N y < (φ a))%Z /\ Z.of_N y <> (φ m).
Proof. intros y T. apply fp_point; [lia | apply fr2_fp; exact T]. Qed.

Lemma mask_bound : forall (B S : int) ys,
  (forall i, Z.testbit (φ B) i = true -> Z.testbit (φ fp) i = true) ->
  (forall i, Z.testbit (φ S) i = true -> Z.testbit (φ fp) i = true) ->
  NoDup ys -> (forall y, In y ys -> Z.testbit (φ S) (Z.of_N y) = true) ->
  (0 <= Z.lxor (φ B) (rmv (φ S) ys) < 2 ^ 13)%Z.
Proof.
  intros B S ys HB HS Hnd Hin.
  pose proof (to_Z_bounded B). pose proof (to_Z_bounded S).
  assert (Hnn : (0 <= Z.lxor (φ B) (rmv (φ S) ys))%Z).
  { apply Z.lxor_nonneg. split; intros _; [apply rmv_nonneg|]; lia. }
  split; [exact Hnn|]. apply mask_lt; [exact Hnn|].
  intros i Hi T. rewrite Z.lxor_spec in T.
  replace i with (Z.of_N (Z.to_N i)) in T by lia.
  rewrite rmv_bits in T by assumption.
  replace (Z.of_N (Z.to_N i)) with i in T by lia.
  assert (F : Z.testbit (φ fp) i = true).
  { destruct (Z.testbit (φ B) i) eqn:TB; [apply HB; exact TB|].
    destruct (Z.testbit (φ S) i) eqn:TS; [apply HS; exact TS | discriminate]. }
  destruct (fp_point i Hi F). lia.
Qed.

Lemma nonneg_lt_wB : forall z : Z, (0 <= z < 2 ^ 63)%Z -> exists k : int, (φ k) = z.
Proof.
  intros z Hz. exists (of_Z z). rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia.
Qed.

Lemma len_step : forall (len : int) (c v : int) (chosen : list N) (s : N),
  tN c = last chosen s -> ((φ c) < (φ n))%Z -> ((φ v) < (φ n))%Z ->
  (φ len) = Z.of_N (pl d s chosen) -> ((φ len) <= (φ L))%Z ->
  (φ (len + D.[c * n + v])) = Z.of_N (pl d s (chosen ++ [tN v])).
Proof.
  intros len c v chosen s Hc Hcn Hvn Hlen HlenL.
  pose proof (HD c v Hcn Hvn) as E. pose proof (Hdist (tN c) (tN v)).
  rewrite add_small; rewrite E, Hlen; [|rewrite wB_val; lia].
  rewrite pl_snoc, <- Hc. lia.
Qed.

Lemma len_leaf : forall (len : int) (c e : int) (chosen : list N) (s : N),
  tN c = last chosen s -> ((φ c) < (φ n))%Z -> ((φ e) < (φ n))%Z ->
  (φ len) = Z.of_N (pl d s chosen) -> ((φ len) <= (φ L))%Z ->
  (φ (len + D.[c * n + e])) = Z.of_N (ell d s chosen (tN e)).
Proof.
  intros len c e chosen s Hc Hcn Hen Hlen HlenL.
  rewrite (len_step len c e chosen s Hc Hcn Hen Hlen HlenL), pl_snoc.
  unfold ell. reflexivity.
Qed.

Lemma ell_ge_prefix : forall s l1 w l2 e,
  (pl d s (l1 ++ [w]) <= ell d s (l1 ++ w :: l2) e)%N.
Proof.
  intros s l1 w l2 e. eapply N.le_trans; [|apply pl_le_ell].
  replace (l1 ++ w :: l2) with ((l1 ++ [w]) ++ l2) by (rewrite <- app_assoc; reflexivity).
  apply pl_le_app.
Qed.

Lemma bit_v : forall v : int, ((φ v) < (φ n))%Z -> (φ (1 << v)) = (2 ^ (φ v))%Z.
Proof. intros v Hv. apply bit_spec. lia. Qed.

(* The second-side search, at a node: chosen is the path so far (after m),
   c its last point, free the second side's points not yet chosen. *)
Lemma pdfs_spec : forall (t : array int) (z : Z) (chosen : list N) (c free len r v : int) H,
  meas n r v = z ->
  tN c = last chosen sN -> ((φ c) < (φ n))%Z ->
  (φ free) = rmv (φ fr2) chosen ->
  NoDup chosen -> (forall y, In y chosen -> Z.testbit (φ fr2) (Z.of_N y) = true) ->
  (φ len) = Z.of_N (pl d sN chosen) -> ((φ len) <= (φ L))%Z ->
  (Z.of_nat (List.length chosen) + (φ r) = (φ k2))%Z ->
  ((φ v) <= (φ n))%Z ->
  (pdfs D n L a need sh t c free len r v H = true <->
   exists ys, HeadGe v ys /\ SH (chosen ++ ys) /\ KeyIn t (K2 (chosen ++ ys))).
Proof.
  intros t z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros chosen c free len r v H Hz Hc Hcn Hfree Hnd Hin Hlen HlenL Hk Hv.
  destruct H as [Hacc]. cbn [pdfs].
  destruct (bdec (r =? 0)) as [Hr | Hr].
  - (* leaf: back to the anchor, probe *)
    apply eqb_true in Hr. subst r. change (φ 0) with 0%Z in Hk.
    assert (Hl : (φ (len + D.[c * n + a])) = Z.of_N (ell d sN chosen aN))
      by (apply len_leaf; auto; lia).
    assert (Hnil : forall ys, SH (chosen ++ ys) -> ys = []).
    { intros ys (_ & Hl' & _). rewrite length_app in Hl'.
      destruct ys; [reflexivity | simpl in Hl'; lia]. }
    destruct (len + D.[c * n + a] <=? L) eqn:EL.
    + rewrite leb_spec in EL.
      set (l := len + D.[c * n + a]) in *.
      assert (Hb := mask_bound need fr2 chosen Hneed fr2_fp Hnd Hin).
      assert (EsubL : (φ (L - l)) = ((φ L) - (φ l))%Z).
      { rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded l). lia. }
      assert (Hkey : (φ (key (need lxor free) (L - l))) = K2 chosen).
      { rewrite key_spec; rewrite ?lxor_spec', ?Hfree, ?EsubL;
          [unfold K2; rewrite Hl; reflexivity | lia | pose proof (to_Z_bounded l); lia]. }
      split.
      * intros E. exists []. rewrite app_nil_r. split; [exact I|]. split.
        -- unfold SH. split; [exact Hnd|]. split; [lia|]. split; [exact Hin|]. lia.
        -- exists (key (need lxor free) (L - l)). auto.
      * intros (ys & _ & Hsh' & (k & Hk' & Hlk)).
        rewrite (Hnil ys Hsh'), app_nil_r in Hk'.
        replace (key (need lxor free) (L - l)) with k; [exact Hlk|].
        apply to_Z_inj. lia.
    + split; [discriminate|]. intros (ys & _ & Hsh' & _).
      pose proof (Hnil ys Hsh') as E. subst ys. rewrite app_nil_r in Hsh'.
      destruct Hsh' as (_ & _ & _ & HE).
      rewrite <- Bool.not_true_iff_false, leb_spec in EL. lia.
  - (* inner node *)
    assert (Hrpos : (0 < (φ r))%Z).
    { apply eqb_false in Hr. pose proof (to_Z_bounded r).
      destruct (Z.eq_dec (φ r) 0) as [E|E]; [|lia].
      exfalso. apply Hr. apply to_Z_inj. exact E. }
    assert (Hne : forall ys, SH (chosen ++ ys) -> ys <> []).
    { intros ys (_ & Hl' & _) E. subst ys. rewrite app_nil_r in Hl'. lia. }
    destruct (bdec (v <? n)) as [Hvn | Hvn].
    2:{ split; [discriminate|].
        intros ([|w ys] & Hh & Hs & _); [exfalso; exact (Hne [] Hs eq_refl)|].
        simpl in Hh. destruct Hs as (_ & _ & Hin' & _).
        pose proof (fr2_point w (Hin' w ltac:(apply in_or_app; right; left; reflexivity))).
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hvn. lia. }
    pose proof Hvn as Hvn'. rewrite ltb_spec in Hvn'.
    assert (Hv1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
    assert (Hsib : forall H',
      pdfs D n L a need sh t c free len r (v + 1) H' = true <->
      exists ys, HeadGe (v + 1) ys /\ SH (chosen ++ ys) /\ KeyIn t (K2 (chosen ++ ys))).
    { intros H'. eapply IH; [rewrite <- Hz; apply dec_sib; assumption | reflexivity
        | assumption | assumption | assumption | assumption | assumption
        | assumption | assumption | assumption | lia]. }
    pose proof (split_head (fun l => SH l /\ KeyIn t (K2 l)) chosen v Hv1
                  (fun l Hq => Hne l (proj1 Hq))) as Hsplit.
    cbv beta in Hsplit. rewrite Hsplit. clear Hsplit.
    assert (Hcp : forall ys, SH ((chosen ++ [tN v]) ++ ys) ->
      ~ In (tN v) chosen /\ Z.testbit (φ fr2) (φ v) = true /\
      (Z.of_N (pl d sN (chosen ++ [tN v])) <= (φ L))%Z).
    { intros ys (Hnd' & _ & Hin' & HE). rewrite <- app_assoc in Hnd', Hin', HE.
      split; [intro F; apply (NoDup_remove_2 _ _ _ Hnd'); apply in_or_app; left; exact F|].
      split; [rewrite <- (tN_spec v); apply Hin'; apply in_or_app; right; left; reflexivity|].
      change ([tN v] ++ ys) with (tN v :: ys) in HE.
      pose proof (ell_ge_prefix sN chosen (tN v) ys aN). lia. }
    rewrite land_bit_test by lia. rewrite Hfree.
    assert (Hbit : Z.testbit (rmv (φ fr2) chosen) (φ v)
                   = Z.testbit (φ fr2) (φ v) && negb (memb (tN v) chosen)).
    { rewrite <- (tN_spec v). apply rmv_bits; assumption. }
    rewrite Hbit.
    destruct (Z.testbit (φ fr2) (φ v) && negb (memb (tN v) chosen)) eqn:Tb.
    + (* v is free *)
      apply andb_true_iff in Tb. destruct Tb as [Tf Tm].
      apply negb_true_iff in Tm.
      assert (Tm' : ~ In (tN v) chosen) by (rewrite <- memb_iff, Tm; discriminate).
      cbn [negb].
      assert (Hl : (φ (len + D.[c * n + v])) = Z.of_N (pl d sN (chosen ++ [tN v])))
        by (apply len_step; auto).
      destruct (len + D.[c * n + v] <=? L) eqn:EL.
      * rewrite leb_spec in EL.
        assert (Hr1 : (φ (r - 1)) = ((φ r) - 1)%Z) by sia.
        assert (Hchild : forall H',
          pdfs D n L a need sh t v (free lxor (1 << v)) (len + D.[c * n + v]) (r - 1) 0 H' = true <->
          exists ys, HeadGe 0 ys /\ SH ((chosen ++ [tN v]) ++ ys) /\
                     KeyIn t (K2 ((chosen ++ [tN v]) ++ ys))).
        { intros H'. eapply IH; [rewrite <- Hz; apply dec_child; assumption | reflexivity
            | rewrite last_snoc; reflexivity | exact Hvn'
            | rewrite lxor_spec', bit_v, Hfree, rmv_snoc, tN_spec by exact Hvn'; reflexivity
            | apply nodup_snoc; assumption
            | intros y Hy; apply in_app_or in Hy; destruct Hy as [Hy|[Hy|[]]];
                [apply Hin; exact Hy | subst y; rewrite tN_spec; exact Tf]
            | exact Hl | exact EL
            | rewrite length_app; simpl; lia | change (φ 0) with 0%Z; lia]. }
        destruct (pdfs D n L a need sh t v (free lxor (1 << v)) (len + D.[c * n + v]) (r - 1) 0 _) eqn:Ec.
        -- split; [intros _ | reflexivity]. left.
           apply Hchild in Ec. destruct Ec as (ys & _ & Hq). exists ys. exact Hq.
        -- rewrite Hsib. split; [intros Hs; right; exact Hs|].
           intros [(ys & Hq) | Hs]; [|exact Hs].
           exfalso. assert (F : pdfs D n L a need sh t v (free lxor (1 << v))
                       (len + D.[c * n + v]) (r - 1) 0
                       (Acc_inv (Acc_intro (meas n r v) Hacc) (dec_child n r v Hr Hvn)) = true).
           { apply Hchild. exists ys. split; [destruct ys; simpl; [exact I | lia]|exact Hq]. }
           rewrite Ec in F. discriminate.
      * rewrite Hsib. split; [intros Hs; right; exact Hs|].
        intros [(ys & Hq) | Hs]; [|exact Hs].
        exfalso. destruct (Hcp ys (proj1 Hq)) as (_ & _ & HE).
        rewrite <- Bool.not_true_iff_false, leb_spec in EL. lia.
    + (* v is not free *)
      cbn [negb]. rewrite Hsib. split; [intros Hs; right; exact Hs|].
      intros [(ys & Hq) | Hs]; [|exact Hs].
      exfalso. destruct (Hcp ys (proj1 Hq)) as (Hm' & Hf & _).
      rewrite Hf in Tb. rewrite <- memb_iff in Hm'.
      apply Bool.not_true_iff_false in Hm'. rewrite Hm' in Tb. discriminate.
Qed.

Lemma HeadGe0 : forall ys, HeadGe 0 ys.
Proof. intros [|w ys]; simpl; [exact I | change (φ 0) with 0%Z; lia]. Qed.

(* the whole second side, probing t *)
Lemma pdfs_top : forall t H,
  pdfs D n L a need sh t m fr2 0 k2 0 H = true <->
  exists ys, SH ys /\ KeyIn t (K2 ys).
Proof.
  intros t H. rewrite (pdfs_spec t _ [] m fr2 0 k2 0 H eq_refl).
  { split.
    + intros (ys & _ & Hq). exists ys. exact Hq.
    + intros (ys & Hq). exists ys. split; [apply HeadGe0 | exact Hq]. }
  all: first [reflexivity | lia | constructor | (intros y []) |
              (change (φ 0) with 0%Z; lia) | (simpl; lia)].
Qed.

Definition Valid (k : int) : Prop := exists xs, FH xs /\ (φ k) = K1 xs.
Definition GoodZ (z : Z) : Prop := exists ys, SH ys /\ z = K2 ys.
Definition Inv (t : array int) : Prop :=
  PArray.length t = size /\ forall s, t.[s] <> 0 -> Valid t.[s].
Definition OK (t : array int) (k : int) : Prop :=
  lookup sh t k = true \/ ~ GoodZ (φ k).
Definition Match : Prop := exists xs ys, FH xs /\ SH ys /\ K1 xs = K2 ys.

Lemma K2_pos : forall ys, SH ys -> (1 <= K2 ys)%Z.
Proof.
  intros ys (Hnd & _ & Hin & HE).
  pose proof (mask_bound need fr2 ys Hneed fr2_fp Hnd Hin). unfold K2. lia.
Qed.

Lemma OK_zero : forall t k, (φ k) = 0%Z -> OK t k.
Proof.
  intros t k E. right. intros (ys & Hs & Ez). pose proof (K2_pos ys Hs). lia.
Qed.

Lemma flush_true : forall t H, Inv t ->
  pdfs D n L a need sh t m fr2 0 k2 0 H = true -> Match.
Proof.
  intros t H [_ Hv] E. apply pdfs_top in E. destruct E as (ys & Hs & (k & Ek & Hl)).
  pose proof (K2_pos ys Hs).
  assert (Hk0 : k <> 0) by (intro F; subst k; change (φ 0) with 0%Z in Ek; lia).
  apply lookup_iff in Hl; [|exact Hk0]. destruct Hl as (j & _ & Hj & _).
  destruct (Hv j ltac:(rewrite Hj; exact Hk0)) as (xs & Hf & Ex).
  exists xs, ys. split; [exact Hf|]. split; [exact Hs|]. rewrite Hj in Ex. lia.
Qed.

Lemma flush_false : forall t H k,
  pdfs D n L a need sh t m fr2 0 k2 0 H = false -> OK t k -> ~ GoodZ (φ k).
Proof.
  intros t H k E [Hl | Hg]; [|exact Hg].
  intros (ys & Hs & Ez). rewrite <- Bool.not_true_iff_false in E. apply E.
  apply pdfs_top. exists ys. split; [exact Hs|]. exists k. auto.
Qed.

Lemma insert_inv : forall t k t', Inv t -> Valid k -> k <> 0 ->
  insert sh t k = (t', true) ->
  Inv t' /\ lookup sh t' k = true /\ (forall k', OK t k' -> OK t' k').
Proof.
  intros t k t' [Hlt Hvt] Hk Hk0 Ei.
  destruct (insert_ok sh t k t' Hk0 Ei) as (Hl & Hlk & Hmono & Hs).
  split; [split; [congruence|]|].
  - intros s Hs0. destruct (Hs s) as [E|E]; rewrite E in *; [apply Hvt; exact Hs0 | exact Hk].
  - split; [exact Hlk|]. intros k' [Hl' | Hg]; [|right; exact Hg].
    destruct (Z.eq_dec (φ k') 0) as [E|E]; [apply OK_zero; exact E|].
    left. apply Hmono; [apply int_neq; change (φ 0) with 0%Z; exact E | exact Hl'].
Qed.

Lemma fresh_inv : forall k, Valid k -> k <> 0 ->
  exists t2, fst (insert sh (PArray.make size 0) k) = t2 /\
    Inv t2 /\ lookup sh t2 k = true.
Proof.
  intros k Hk Hk0.
  pose proof (insert_fresh sh size k Hk0 (Hsh k) Hsize) as Hs.
  destruct (insert sh (PArray.make size 0) k) as [t2 b] eqn:Ei. simpl in Hs. subst b.
  assert (Hinv0 : Inv (PArray.make size 0)).
  { split.
    - rewrite alength_make. replace (size <=? PArray.max_length) with true; [reflexivity|].
      symmetry. rewrite leb_spec, max_length_val. lia.
    - intros s Hs. rewrite aget_make in Hs. congruence. }
  destruct (insert_inv _ k t2 Hinv0 Hk Hk0 Ei) as (Hi & Hl & _).
  exists t2. auto.
Qed.

(* The first-side search, at a node: chosen is the path so far (after the
   anchor), c its last point, free the points of fp not yet chosen. *)
Lemma idfs_spec : forall (t : array int) (z : Z) (chosen : list N) (c free len r v : int) H t' f,
  meas n r v = z ->
  tN c = last chosen aN -> ((φ c) < (φ n))%Z ->
  (φ free) = rmv (φ fp) chosen ->
  NoDup chosen -> (forall x, In x chosen -> Z.testbit (φ fp) (Z.of_N x) = true) ->
  (φ len) = Z.of_N (pl d aN chosen) -> ((φ len) <= (φ L))%Z ->
  (Z.of_nat (List.length chosen) + (φ r) = (φ k1))%Z ->
  ((φ v) <= (φ n))%Z ->
  ((φ r) = 0%Z -> forall w : N, Z.testbit (φ need) (Z.of_N w) = true -> In w chosen) ->
  Inv t ->
  idfs D n L a m fp need fr2 need k2 sh size t c free len r v H = (t', f) ->
  (f = true -> Match) /\
  (f = false -> Inv t' /\ (forall k, OK t k -> OK t' k) /\
     forall xs, HeadGe v xs -> FH (chosen ++ xs) ->
       exists k, (φ k) = K1 (chosen ++ xs) /\ OK t' k).
Proof.
  intros t z. revert t.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t chosen c free len r v H t' f Hz Hc Hcn Hfree Hnd Hin Hlen HlenL Hk Hv
    Hneed0 Hinv Hres.
  destruct H as [Hacc]. cbn [idfs] in Hres.
  destruct (bdec (r =? 0)) as [Hr | Hr].
  - (* leaf: on to m, insert *)
    apply eqb_true in Hr. subst r. change (φ 0) with 0%Z in Hk, Hneed0.
    specialize (Hneed0 eq_refl).
    assert (Hmn : ((φ m) < (φ n))%Z) by lia.
    assert (Hl : (φ (len + D.[c * n + m])) = Z.of_N (ell d aN chosen sN))
      by (apply len_leaf; auto).
    assert (Hnil : forall xs, FH (chosen ++ xs) -> xs = []).
    { intros xs (_ & Hl' & _). rewrite length_app in Hl'.
      destruct xs; [reflexivity | simpl in Hl'; lia]. }
    destruct (len + D.[c * n + m] <=? L) eqn:EL.
    + rewrite leb_spec in EL.
      set (l := len + D.[c * n + m]) in *.
      assert (Hb := mask_bound fp fp chosen (fun i T => T) (fun i T => T) Hnd Hin).
      set (k := key (fp lxor free) l) in *.
      assert (Hkey : (φ k) = K1 chosen).
      { unfold k. rewrite key_spec; rewrite ?lxor_spec', ?Hfree;
          [unfold K1; rewrite Hl; reflexivity | lia | lia]. }
      assert (HFH : FH chosen).
      { split; [exact Hnd|]. split; [lia|]. split; [exact Hin|]. split; [exact Hneed0|]. lia. }
      assert (Hval : Valid k) by (exists chosen; auto).
      assert (Hk0 : k <> 0).
      { intro E. rewrite E in Hkey. change (φ 0) with 0%Z in Hkey. unfold K1 in Hkey. lia. }
      assert (Hleaf : forall t2, lookup sh t2 k = true ->
        forall xs, HeadGe v xs -> FH (chosen ++ xs) ->
          exists k', (φ k') = K1 (chosen ++ xs) /\ OK t2 k').
      { intros t2 Hl2 xs _ Hf. rewrite (Hnil xs Hf), app_nil_r.
        exists k. split; [exact Hkey | left; exact Hl2]. }
      unfold leafins in Hres.
      destruct (insert sh t k) as [t1 b] eqn:Ei. destruct b.
      * injection Hres as <- <-. split; [discriminate|]. intros _.
        destruct (insert_inv t k t1 Hinv Hval Hk0 Ei) as (Hi & Hlk & Hmono).
        split; [exact Hi|]. split; [exact Hmono | apply Hleaf; exact Hlk].
      * apply insert_fail in Ei. subst t1.
        destruct (pdfs D n L a need sh t m fr2 0 k2 0 _) eqn:Ep.
        -- injection Hres as <- <-. split; [intros _; exact (flush_true t _ Hinv Ep) | discriminate].
        -- injection Hres as <- <-. split; [discriminate|]. intros _.
           destruct (fresh_inv k Hval Hk0) as (t2 & Et2 & Hi2 & Hl2). rewrite Et2.
           split; [exact Hi2|]. split.
           ++ intros k' Hok. right. exact (flush_false t _ k' Ep Hok).
           ++ apply Hleaf. exact Hl2.
    + injection Hres as <- <-. split; [discriminate|]. intros _.
      split; [exact Hinv|]. split; [auto|].
      intros xs _ Hf. pose proof (Hnil xs Hf) as E. subst xs.
      rewrite app_nil_r in Hf. destruct Hf as (_ & _ & _ & _ & HE).
      rewrite <- Bool.not_true_iff_false, leb_spec in EL. lia.
  - (* inner node *)
    assert (Hrpos : (0 < (φ r))%Z).
    { pose proof (proj1 (eqb_false r 0) Hr) as Hr'. pose proof (to_Z_bounded r).
      destruct (Z.eq_dec (φ r) 0) as [E|E]; [|lia].
      exfalso. apply Hr'. apply to_Z_inj. exact E. }
    assert (Hne : forall xs, FH (chosen ++ xs) -> xs <> []).
    { intros xs (_ & Hl' & _) E. subst xs. rewrite app_nil_r in Hl'. lia. }
    destruct (bdec (v <? n)) as [Hvn | Hvn].
    2:{ injection Hres as <- <-. split; [discriminate|]. intros _.
        split; [exact Hinv|]. split; [auto|].
        intros [|w xs] Hh Hf; [exfalso; exact (Hne [] Hf eq_refl)|].
        simpl in Hh. destruct Hf as (_ & _ & Hin' & _).
        pose proof (fp_point (Z.of_N w) ltac:(lia)
                      (Hin' w ltac:(apply in_or_app; right; left; reflexivity))).
        rewrite <- Bool.not_true_iff_false, ltb_spec in Hvn. lia. }
    pose proof Hvn as Hvn'. rewrite ltb_spec in Hvn'.
    assert (Hv1 : (φ (v + 1)) = ((φ v) + 1)%Z) by sia.
    assert (Hsib : forall t0 H' t2 f2, Inv t0 ->
      idfs D n L a m fp need fr2 need k2 sh size t0 c free len r (v + 1) H' = (t2, f2) ->
      (f2 = true -> Match) /\
      (f2 = false -> Inv t2 /\ (forall k, OK t0 k -> OK t2 k) /\
         forall xs, HeadGe (v + 1) xs -> FH (chosen ++ xs) ->
           exists k, (φ k) = K1 (chosen ++ xs) /\ OK t2 k)).
    { intros t0 H' t2 f2 Hi0 Hr0.
      exact (IH _ ltac:(rewrite <- Hz; apply dec_sib; assumption) t0 chosen c free len r
               (v + 1) H' t2 f2 eq_refl Hc Hcn Hfree Hnd Hin Hlen HlenL Hk ltac:(lia)
               Hneed0 Hi0 Hr0). }
    assert (Hcp : forall xs, FH ((chosen ++ [tN v]) ++ xs) ->
      ~ In (tN v) chosen /\ Z.testbit (φ fp) (φ v) = true /\
      (Z.of_N (pl d aN (chosen ++ [tN v])) <= (φ L))%Z).
    { intros xs (Hnd' & _ & Hin' & _ & HE). rewrite <- app_assoc in Hnd', Hin', HE.
      split; [intro F; apply (NoDup_remove_2 _ _ _ Hnd'); apply in_or_app; left; exact F|].
      split; [rewrite <- (tN_spec v); apply Hin'; apply in_or_app; right; left; reflexivity|].
      change ([tN v] ++ xs) with (tN v :: xs) in HE.
      pose proof (ell_ge_prefix aN chosen (tN v) xs sN). lia. }
    (* the sibling alone *)
    assert (Hsib_only :
      (forall xs, FH ((chosen ++ [tN v]) ++ xs) -> False) ->
      forall H',
      idfs D n L a m fp need fr2 need k2 sh size t c free len r (v + 1) H' = (t', f) ->
      (f = true -> Match) /\
      (f = false -> Inv t' /\ (forall k, OK t k -> OK t' k) /\
         forall xs, HeadGe v xs -> FH (chosen ++ xs) ->
           exists k, (φ k) = K1 (chosen ++ xs) /\ OK t' k)).
    { intros Hno H' Hr'. destruct (Hsib t H' t' f Hinv Hr') as [S1 S2].
      split; [exact S1|]. intros Hf0. destruct (S2 Hf0) as (A & B & C).
      split; [exact A|]. split; [exact B|].
      refine (split_head_all FH (fun l => exists k, (φ k) = K1 l /\ OK t' k) chosen v
                Hv1 Hne _ C).
      intros xs Hf. exfalso. exact (Hno xs Hf). }
    rewrite land_bit_test in Hres by lia. rewrite Hfree in Hres.
    assert (Hbit : Z.testbit (rmv (φ fp) chosen) (φ v)
                   = Z.testbit (φ fp) (φ v) && negb (memb (tN v) chosen)).
    { rewrite <- (tN_spec v). apply rmv_bits; assumption. }
    rewrite Hbit in Hres.
    destruct (Z.testbit (φ fp) (φ v) && negb (memb (tN v) chosen)) eqn:Tb;
      cbn [negb] in Hres.
    + (* v is free *)
      apply andb_true_iff in Tb. destruct Tb as [Tf Tm].
      apply negb_true_iff in Tm.
      assert (Tm' : ~ In (tN v) chosen) by (rewrite <- memb_iff, Tm; discriminate).
      assert (Hnd1 : NoDup (chosen ++ [tN v])) by (apply nodup_snoc; assumption).
      assert (Hin1 : forall x, In x (chosen ++ [tN v]) -> Z.testbit (φ fp) (Z.of_N x) = true).
      { intros y Hy. apply in_app_or in Hy. destruct Hy as [Hy|[Hy|[]]];
          [apply Hin; exact Hy | subst y; rewrite tN_spec; exact Tf]. }
      assert (Hfree1 : (φ (free lxor (1 << v))) = rmv (φ fp) (chosen ++ [tN v])).
      { rewrite lxor_spec', bit_v, Hfree, rmv_snoc, tN_spec by exact Hvn'. reflexivity. }
      (* the bits of need outside chosen ++ [v] *)
      assert (Hneedbits : (need land (free lxor (1 << v))) = 0 ->
        forall w : N, Z.testbit (φ need) (Z.of_N w) = true -> In w (chosen ++ [tN v])).
      { intros E w Tw. assert (E' : (φ (need land (free lxor (1 << v)))) = 0%Z) by (rewrite E; reflexivity).
        rewrite land_spec', Hfree1 in E'.
        assert (F : Z.testbit (Z.land (φ need) (rmv (φ fp) (chosen ++ [tN v]))) (Z.of_N w) = false)
          by (rewrite E'; apply Z.testbit_0_l).
        rewrite Z.land_spec, Tw, rmv_bits, (Hneed _ Tw) in F by assumption.
        cbn [andb] in F. apply negb_false_iff, memb_iff in F. exact F. }
      destruct ((r =? 1) && negb ((need land (free lxor (1 << v))) =? 0)) eqn:Ep.
      * (* pruned: the last choice would miss need *)
        refine (Hsib_only _ _ Hres).
        intros xs Hf. apply andb_true_iff in Ep. destruct Ep as [E1 E2].
        apply eqb_true in E1. subst r. change (φ 1) with 1%Z in Hk.
        apply negb_true_iff, eqb_false in E2. apply E2.
        destruct Hf as (_ & Hl' & _ & Hnf & _).
        rewrite !length_app in Hl'. simpl in Hl'.
        destruct xs; [|simpl in Hl'; lia]. rewrite app_nil_r in Hnf.
        apply to_Z_inj. rewrite land_spec', Hfree1. change (φ 0) with 0%Z.
        apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.testbit_0_l.
        destruct (Z.testbit (φ need) i) eqn:Tn; [|reflexivity].
        replace i with (Z.of_N (Z.to_N i)) in * by lia.
        rewrite rmv_bits by assumption.
        pose proof (Hnf _ Tn) as Hw. apply memb_iff in Hw. rewrite Hw.
        rewrite andb_false_r. reflexivity.
      * assert (Hneed1 : (φ (r - 1)) = 0%Z -> forall w : N,
          Z.testbit (φ need) (Z.of_N w) = true -> In w (chosen ++ [tN v])).
        { intros E0. apply Hneedbits.
          apply andb_false_iff in Ep. destruct Ep as [E1|E1].
          - exfalso. apply eqb_false in E1. apply E1. apply to_Z_inj.
            change (φ 1) with 1%Z. pose proof (to_Z_bounded r). rewrite sub_spec in E0.
            change (φ 1) with 1%Z in E0. rewrite Z.mod_small in E0 by lia. lia.
          - apply negb_false_iff, eqb_true in E1. exact E1. }
        assert (Hl : (φ (len + D.[c * n + v])) = Z.of_N (pl d aN (chosen ++ [tN v])))
          by (apply len_step; auto).
        destruct (len + D.[c * n + v] <=? L) eqn:EL.
        -- rewrite leb_spec in EL.
           assert (Hr1 : (φ (r - 1)) = ((φ r) - 1)%Z) by sia.
           assert (Hk1 : (Z.of_nat (List.length (chosen ++ [tN v])) + (φ (r - 1)) = (φ k1))%Z)
             by (rewrite length_app; simpl; lia).
           assert (Hc1 : tN v = last (chosen ++ [tN v]) aN) by (rewrite last_snoc; reflexivity).
           assert (Hdec : Zwf 0 (meas n (r - 1) 0) z) by (rewrite <- Hz; apply dec_child; assumption).
           destruct (idfs D n L a m fp need fr2 need k2 sh size t v (free lxor (1 << v))
                       (len + D.[c * n + v]) (r - 1) 0 _) as [t1 f1] eqn:Ec.
           pose proof (IH _ Hdec t (chosen ++ [tN v]) v (free lxor (1 << v))
                         (len + D.[c * n + v]) (r - 1) 0 _ t1 f1 eq_refl Hc1 Hvn' Hfree1
                         Hnd1 Hin1 Hl EL Hk1 ltac:(change (φ 0) with 0%Z; lia) Hneed1 Hinv Ec)
             as [C1 C2].
           destruct f1.
           ++ injection Hres as <- <-. split; [intros _; apply C1; reflexivity | discriminate].
           ++ destruct (C2 eq_refl) as (A1 & B1 & L1).
              destruct (Hsib t1 _ t' f A1 Hres) as [S1 S2].
              split; [exact S1|]. intros Hf0. destruct (S2 Hf0) as (A2 & B2 & L2).
              split; [exact A2|]. split; [intros k Hok; apply B2, B1, Hok|].
              refine (split_head_all FH (fun l => exists k, (φ k) = K1 l /\ OK t' k) chosen v
                        Hv1 Hne _ L2).
              intros xs Hf. destruct (L1 xs (HeadGe0 xs) Hf) as (k & Ek & Hok).
              exists k. split; [exact Ek | apply B2; exact Hok].
        -- refine (Hsib_only _ _ Hres).
           intros xs Hf. destruct (Hcp xs Hf) as (_ & _ & HE).
           rewrite <- Bool.not_true_iff_false, leb_spec in EL. lia.
    + (* v is not free *)
      refine (Hsib_only _ _ Hres).
      intros xs Hf. destruct (Hcp xs Hf) as (Hm' & Hf' & _).
      rewrite Hf' in Tb. rewrite <- memb_iff in Hm'.
      apply Bool.not_true_iff_false in Hm'. rewrite Hm' in Tb. discriminate.
Qed.

Lemma inv_make : Inv (PArray.make size 0).
Proof.
  split.
  - rewrite alength_make. replace (size <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. lia.
  - intros s Hs. rewrite aget_make in Hs. congruence.
Qed.

(* the search for one middle point decides Match *)
Lemma search_core : forall H H',
  ((φ k1) = 0%Z -> forall w : N, Z.testbit (φ need) (Z.of_N w) = true -> False) ->
  (match idfs D n L a m fp need fr2 need k2 sh size (PArray.make size 0) a fp 0 k1 0 H with
   | (_, true) => true
   | (t, false) => pdfs D n L a need sh t m fr2 0 k2 0 H'
   end = true <-> Match).
Proof.
  intros H H' Hk10.
  destruct (idfs D n L a m fp need fr2 need k2 sh size (PArray.make size 0) a fp 0 k1 0 H)
    as [t f] eqn:E.
  assert (Han : ((φ a) < (φ n))%Z) by lia.
  destruct (idfs_spec (PArray.make size 0) _ [] a fp 0 k1 0 H t f eq_refl eq_refl Han
              eq_refl (NoDup_nil _) ltac:(intros x []) ltac:(reflexivity)
              ltac:(change (φ 0) with 0%Z; lia) ltac:(simpl; lia)
              ltac:(change (φ 0) with 0%Z; lia)
              ltac:(intros E0 w Tw; exfalso; exact (Hk10 E0 w Tw))
              inv_make E) as [P1 P2].
  destruct f.
  - split; [intros _; apply P1; reflexivity | reflexivity].
  - destruct (P2 eq_refl) as (Hi & _ & Hl). split.
    + intros Ep. exact (flush_true t H' Hi Ep).
    + intros (xs & ys & Hx & Hy & Exy).
      destruct (Hl xs (HeadGe0 xs) Hx) as (k & Ek & [Hok | Hng]).
      * apply pdfs_top. exists ys. split; [exact Hy|]. exists k.
        split; [cbn [app] in Ek; lia | exact Hok].
      * exfalso. apply Hng. exists ys. split; [exact Hy | cbn [app] in Ek; lia].
Qed.

Lemma bits1 : forall xs, NoDup xs ->
  (forall x, In x xs -> Z.testbit (φ fp) (Z.of_N x) = true) ->
  forall v : N, Z.testbit (Z.lxor (φ fp) (rmv (φ fp) xs)) (Z.of_N v)
    = xorb (Z.testbit (φ fp) (Z.of_N v)) (Z.testbit (φ fp) (Z.of_N v) && negb (memb v xs)).
Proof. intros xs Hnd Hin v. rewrite Z.lxor_spec, rmv_bits by assumption. reflexivity. Qed.

Lemma bits2 : forall ys, NoDup ys ->
  (forall y, In y ys -> Z.testbit (φ fr2) (Z.of_N y) = true) ->
  forall v : N, Z.testbit (Z.lxor (φ need) (rmv (φ fr2) ys)) (Z.of_N v)
    = xorb (Z.testbit (φ need) (Z.of_N v))
           (Z.testbit (φ fp) (Z.of_N v) && negb (Z.testbit (φ need) (Z.of_N v)) && negb (memb v ys)).
Proof. intros ys Hnd Hin v. rewrite Z.lxor_spec, rmv_bits, Hfr2 by assumption. reflexivity. Qed.

Lemma memb_true : forall v l, In v l -> memb v l = true.
Proof. intros v l H. apply memb_iff. exact H. Qed.

(* Soundness: a match is a race of length L *)
Lemma match_race : Match ->
  exists p, visiting_order d p /\ race_length d p = tN L.
Proof.
  intros (xs & ys & Hx & Hy & E).
  destruct Hx as (Ndx & Lx & Inx & Nx & Ex). destruct Hy as (Ndy & Ly & Iny & Ey).
  pose proof (mask_bound fp fp xs (fun i T => T) (fun i T => T) Ndx Inx) as Bx.
  pose proof (mask_bound need fr2 ys Hneed fr2_fp Ndy Iny) as By.
  unfold K1, K2 in E.
  assert (EM : Z.lxor (φ fp) (rmv (φ fp) xs) = Z.lxor (φ need) (rmv (φ fr2) ys) /\
               Z.of_N (ell d aN xs sN) = ((φ L) - Z.of_N (ell d sN ys aN))%Z) by lia.
  destruct EM as [EM EL].
  assert (Hbits : forall v : N, (In v xs -> ~ In v ys) /\
            (Z.testbit (φ fp) (Z.of_N v) = true -> In v xs \/ In v ys)).
  { intros v. pose proof (f_equal (fun z => Z.testbit z (Z.of_N v)) EM) as Ev.
    cbv beta in Ev. rewrite bits1, bits2 in Ev by assumption.
    destruct (bool_A (Z.testbit (φ fp) (Z.of_N v)) (Z.testbit (φ need) (Z.of_N v))
                (memb v xs) (memb v ys)
                ltac:(intros T; apply memb_iff in T; apply Inx; exact T)
                ltac:(intros T; apply memb_iff in T; pose proof (Iny v T) as T';
                      rewrite Hfr2 in T'; apply andb_true_iff in T';
                      destruct T' as [T1 T2]; apply negb_true_iff in T2; auto)
                Ev) as [D1 D2].
    split.
    - intros H1 H2. apply memb_true in H1. apply memb_true in H2.
      rewrite (D1 H1) in H2. discriminate.
    - intros T. destruct (D2 T) as [T'|T']; apply memb_iff in T'; auto. }
  assert (Hpx : forall x, In x xs -> (Z.of_N x < (φ a))%Z /\ Z.of_N x <> (φ m))
    by (intros x Hx; apply fp_point; [lia | apply Inx; exact Hx]).
  assert (Hpy : forall y, In y ys -> (Z.of_N y < (φ a))%Z /\ Z.of_N y <> (φ m))
    by (intros y Hy; apply fr2_point; apply Iny; exact Hy).
  pose proof (tN_spec a) as Ea. pose proof (tN_spec m) as Em.
  exists (aN :: xs ++ sN :: ys). split; [split|].
  - constructor.
    + intro F. apply in_app_or in F. destruct F as [F|[F|F]].
      * destruct (Hpx _ F). lia.
      * rewrite F in Em. lia.
      * destruct (Hpy _ F). lia.
    + apply NoDup_app; [exact Ndx | |].
      * constructor; [|exact Ndy]. intro F. destruct (Hpy _ F). lia.
      * intros v Hv [F|F]; [subst v; destruct (Hpx _ Hv); lia|].
        exact (proj1 (Hbits v) Hv F).
  - intros i. unfold len. split.
    + intros [F|F]; [subst i; lia|].
      apply in_app_or in F. destruct F as [F|[F|F]].
      * destruct (Hpx _ F). lia.
      * subst i. lia.
      * destruct (Hpy _ F). lia.
    + intros Hi.
      destruct (Z.eq_dec (Z.of_N i) (φ a)) as [E1|E1]; [left; lia|].
      right. apply in_or_app.
      destruct (Z.eq_dec (Z.of_N i) (φ m)) as [E2|E2]; [right; left; lia|].
      assert (T : Z.testbit (φ fp) (Z.of_N i) = true).
      { rewrite Hfp by lia. apply andb_true_iff. split; [apply Z.ltb_lt; lia|].
        apply negb_true_iff, Z.eqb_neq. exact E2. }
      destruct (proj2 (Hbits i) T); [left | right; right]; assumption.
  - rewrite race_split. pose proof (to_Z_bounded L).
    change (tN L) with (Z.to_N (φ L)). lia.
Qed.

(* Completeness: a race of length L cut at m, with need on the first side *)
Lemma cycle_match : forall xs ys,
  NoDup (aN :: xs ++ sN :: ys) ->
  (forall i, In i (aN :: xs ++ sN :: ys) <-> (Z.of_N i < (φ n))%Z) ->
  Z.of_nat (List.length xs) = (φ k1) -> Z.of_nat (List.length ys) = (φ k2) ->
  (forall w : N, Z.testbit (φ need) (Z.of_N w) = true -> In w xs) ->
  (forall w : N, Z.testbit (φ need) (Z.of_N w) = true -> ~ In w ys) ->
  Z.of_N (race_length d (aN :: xs ++ sN :: ys)) = (φ L) ->
  Match.
Proof.
  intros xs ys Hnd Hcov Lx Ly Nx Ny Hrace.
  rewrite race_split in Hrace.
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Ha' Hnd].
  pose proof (NoDup_app_remove_r _ _ Hnd) as Ndx.
  pose proof (NoDup_app_remove_l _ _ Hnd) as Ndsy.
  apply NoDup_cons_iff in Ndsy. destruct Ndsy as [Hsy Ndy].
  pose proof (NoDup_remove_2 _ _ _ Hnd) as Hsxy.
  pose proof (NoDup_remove_1 _ _ _ Hnd) as Ndxy.
  pose proof (tN_spec a) as Ea. pose proof (tN_spec m) as Em.
  assert (Hpt : forall v, In v (xs ++ ys) -> Z.testbit (φ fp) (Z.of_N v) = true).
  { intros v Hv. rewrite Hfp by lia.
    assert (Hvn : (Z.of_N v < (φ n))%Z).
    { apply Hcov. right. apply in_app_or in Hv. apply in_or_app.
      destruct Hv; [left | right; right]; assumption. }
    assert (Hva : Z.of_N v <> (φ a)).
    { intro F. apply Ha'. assert (E' : v = aN) by lia. rewrite <- E'.
      apply in_app_or in Hv. apply in_or_app. destruct Hv; [left | right; right]; assumption. }
    assert (Hvm : Z.of_N v <> (φ m)) by (intro F; apply Hsxy; replace sN with v by lia; exact Hv).
    apply andb_true_iff. split; [apply Z.ltb_lt; lia | apply negb_true_iff, Z.eqb_neq; exact Hvm]. }
  assert (Inx : forall x, In x xs -> Z.testbit (φ fp) (Z.of_N x) = true)
    by (intros x Hx; apply Hpt; apply in_or_app; left; exact Hx).
  assert (Iny : forall y, In y ys -> Z.testbit (φ fr2) (Z.of_N y) = true).
  { intros y Hy. rewrite Hfr2. rewrite Hpt by (apply in_or_app; right; exact Hy).
    destruct (Z.testbit (φ need) (Z.of_N y)) eqn:T; [exfalso; exact (Ny y T Hy) | reflexivity]. }
  exists xs, ys. split; [|split].
  - split; [exact Ndx|]. split; [exact Lx|]. split; [exact Inx|]. split; [exact Nx|]. lia.
  - split; [exact Ndy|]. split; [exact Ly|]. split; [exact Iny|]. lia.
  - unfold K1, K2.
    replace (Z.lxor (φ fp) (rmv (φ fp) xs)) with (Z.lxor (φ need) (rmv (φ fr2) ys)); [lia|].
    apply Z.bits_inj'. intros i Hi.
    replace i with (Z.of_N (Z.to_N i)) by lia.
    rewrite bits1, bits2 by assumption.
    set (v := Z.to_N i). symmetry.
    apply bool_B.
    + apply Hneed.
    + intros T. apply memb_iff in T. apply Inx. exact T.
    + intros T. apply memb_iff in T. pose proof (Iny v T) as T'.
      rewrite Hfr2 in T'. apply andb_true_iff in T'.
      destruct T' as [T1 T2]. apply negb_true_iff in T2. auto.
    + intros T. apply memb_iff. apply Nx. exact T.
    + intros T. rewrite Hfp in T by lia. apply andb_true_iff in T.
      destruct T as [T1 T2]. apply Z.ltb_lt in T1. apply negb_true_iff, Z.eqb_neq in T2.
      assert (Hin : In v (aN :: xs ++ sN :: ys)) by (apply Hcov; lia).
      destruct Hin as [F|F]; [lia|]. apply in_app_or in F.
      destruct F as [F|[F|F]]; [left; apply memb_iff; exact F | lia |
                                right; apply memb_iff; exact F].
    + intros T. apply memb_iff in T. apply Bool.not_true_iff_false. intro T'.
      apply memb_iff in T'. exact (nodup_app_disj xs ys v Ndxy T T').
Qed.

End Spec.

(* ------------------------------------------------------------------ *)
(* The masks of one middle point                                       *)
(* ------------------------------------------------------------------ *)

Lemma fp_bits : forall A M : int, ((φ A) <= 13)%Z -> ((φ M) < (φ A))%Z ->
  forall i, (0 <= i)%Z ->
  Z.testbit (φ (((1 << A) - 1) lxor (1 << M))) i = (i <? (φ A))%Z && negb (i =? (φ M))%Z.
Proof.
  intros A M HA HM i Hi. pose proof (to_Z_bounded M).
  assert (E1 : (φ ((1 << A) - 1)) = Z.ones (φ A)).
  { rewrite sub_spec, bit_spec by lia. change (φ 1) with 1%Z.
    rewrite Z.ones_equiv. apply Z.mod_small.
    assert (0 < 2 ^ (φ A) <= 2 ^ 13)%Z by (split; [apply Z.pow_pos_nonneg | apply Z.pow_le_mono_r]; lia).
    rewrite wB_val. lia. }
  rewrite lxor_spec', E1, bit_spec by lia.
  rewrite Z.lxor_spec, Z.testbit_ones, Z.pow2_bits_eqb by lia.
  rewrite (proj2 (Z.leb_le 0 i) Hi). simpl andb.
  destruct (Z.eqb_spec (φ M) i) as [E|E]; destruct (Z.eqb_spec i (φ M)) as [E'|E'];
    first [lia | (subst i; rewrite (proj2 (Z.ltb_lt (φ M) (φ A)) HM); reflexivity)
               | (rewrite xorb_false_r, andb_true_r; reflexivity)].
Qed.

Section Main.
Variable d : list (list N).
Variables (D : array int) (n L : int).

Hypothesis Hn : (φ n) = Z.of_nat (List.length d).
Hypothesis Hn2 : (2 <= (φ n) <= 14)%Z.
Hypothesis HL : (1 <= (φ L) <= 10 ^ 15)%Z.
Hypothesis Hdist : forall i j, (Z.of_N (dist d i j) <= (φ L))%Z.
Hypothesis Hsym : forall i j, dist d i j = dist d j i.
Hypothesis HD : forall i j : int, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
  (φ (D.[i * n + j])) = Z.of_N (dist d (tN i) (tN j)).

Local Notation a := (n - 1).
Local Notation fpm m := (((1 << (n - 1)) - 1) lxor (1 << m)).
Local Notation evn := (((n land 1) =? 0) && (4 <=? n)).
Local Notation p0 m := (if m =? 0 then 1 else 0).
Local Notation needm m := (if evn then 1 << p0 m else 0).
Local Notation fr2m m := (fpm m lxor needm m).

Lemma Ha_val : (φ a) = ((φ n) - 1)%Z.
Proof. rewrite sub_spec. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma evn_spec : evn = true -> (4 <= (φ n))%Z.
Proof. intros E. apply andb_true_iff in E. destruct E as [_ E]. rewrite leb_spec in E. exact E. Qed.

Lemma p0_spec : forall m : int,
  ((φ (p0 m)) = if ((φ m) =? 0)%Z then 1 else 0)%Z.
Proof.
  intros m. destruct (m =? 0) eqn:E; destruct ((φ m) =? 0)%Z eqn:E'; try reflexivity.
  - apply eqb_true in E. subst m. discriminate.
  - apply Z.eqb_eq in E'. apply eqb_false in E. exfalso. apply E. apply to_Z_inj. exact E'.
Qed.

Lemma fpm_bits : forall m : int, ((φ m) < (φ a))%Z -> forall i, (0 <= i)%Z ->
  Z.testbit (φ (fpm m)) i = (i <? (φ a))%Z && negb (i =? (φ m))%Z.
Proof. intros m Hm i Hi. apply fp_bits; [rewrite Ha_val; lia | exact Hm | exact Hi]. Qed.

Lemma needm_bits : forall m : int, forall i,
  Z.testbit (φ (needm m)) i = evn && ((φ (p0 m)) =? i)%Z.
Proof.
  intros m i. destruct evn.
  - rewrite bit_spec by (rewrite p0_spec; destruct ((φ m) =? 0)%Z; lia).
    destruct (Z.le_gt_cases 0 i).
    + apply Z.pow2_bits_eqb. rewrite p0_spec. destruct ((φ m) =? 0)%Z; lia.
    + rewrite Z.testbit_neg_r by lia. simpl. symmetry. apply Z.eqb_neq.
      rewrite p0_spec. destruct ((φ m) =? 0)%Z; lia.
  - change (φ 0) with 0%Z. apply Z.testbit_0_l.
Qed.

Lemma needm_fp : forall m : int, ((φ m) < (φ a))%Z ->
  forall i, Z.testbit (φ (needm m)) i = true -> Z.testbit (φ (fpm m)) i = true.
Proof.
  intros m Hm i T. rewrite needm_bits in T. apply andb_true_iff in T. destruct T as [Te T].
  apply Z.eqb_eq in T. pose proof (evn_spec Te) as H4. pose proof Ha_val.
  rewrite p0_spec in T. pose proof (to_Z_bounded m).
  rewrite fpm_bits by (try exact Hm; destruct ((φ m) =? 0)%Z; lia).
  apply andb_true_iff. split.
  - apply Z.ltb_lt. destruct ((φ m) =? 0)%Z; lia.
  - apply negb_true_iff, Z.eqb_neq. destruct ((φ m) =? 0)%Z eqn:E;
      [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia.
Qed.

Lemma fr2m_bits : forall m : int, ((φ m) < (φ a))%Z -> forall i,
  Z.testbit (φ (fr2m m)) i = Z.testbit (φ (fpm m)) i && negb (Z.testbit (φ (needm m)) i).
Proof.
  intros m Hm i. rewrite lxor_spec', Z.lxor_spec.
  destruct (Z.testbit (φ (needm m)) i) eqn:T.
  - rewrite (needm_fp m Hm i T). reflexivity.
  - rewrite xorb_false_r, andb_true_r. reflexivity.
Qed.

Lemma search_m_spec : forall (m k1 k2 sh size : int),
  ((φ m) < (φ a))%Z -> (φ k1) = (((φ n) - 2) / 2)%Z ->
  (forall k, ((φ (hidx sh k)) < (φ size))%Z) -> ((φ size) <= 4194303)%Z ->
  (search_m D n L a k1 k2 sh size m = true <->
   Match d L a m (fpm m) (needm m) (fr2m m) k1 k2).
Proof.
  intros m k1 k2 sh size Hm Hk1 Hsh Hsize.
  unfold search_m. cbv zeta.
  apply (search_core d D n L a m (fpm m) (needm m) (fr2m m) k1 k2 sh size Hn2 HL Hdist HD
           Ha_val Hm (fpm_bits m Hm) (needm_fp m Hm) (fr2m_bits m Hm) Hsh Hsize).
  intros E0 w T. rewrite needm_bits in T. apply andb_true_iff in T. destruct T as [Te _].
  pose proof (evn_spec Te). rewrite Hk1 in E0.
  assert ((φ n) - 2 < 2)%Z by (apply Z.div_small_iff in E0; lia). lia.
Qed.

Lemma mloop_spec : forall (k1 k2 sh size : int),
  (φ k1) = (((φ n) - 2) / 2)%Z ->
  (forall k, ((φ (hidx sh k)) < (φ size))%Z) -> ((φ size) <= 4194303)%Z ->
  forall z m H, gap a m = z ->
  (mloop D n L a k1 k2 sh size m H = true <->
   exists m' : int, ((φ m) <= (φ m') < (φ a))%Z /\
     Match d L a m' (fpm m') (needm m') (fr2m m') k1 k2).
Proof.
  intros k1 k2 sh size Hk1 Hsh Hsize z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros m H Hz. destruct H as [Hacc]. cbn [mloop].
  destruct (bdec (m <? a)) as [Hm | Hm].
  - pose proof Hm as Hm'. rewrite ltb_spec in Hm'.
    assert (Hm1 : (φ (m + 1)) = ((φ m) + 1)%Z) by sia.
    destruct (search_m D n L a k1 k2 sh size m) eqn:Es.
    + split; [intros _|reflexivity]. exists m. split; [lia|].
      apply (search_m_spec m k1 k2 sh size Hm' Hk1 Hsh Hsize). exact Es.
    + rewrite (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hm) (m + 1) _ eq_refl).
      split.
      * intros (m' & Hr & Hmt). exists m'. split; [lia | exact Hmt].
      * intros (m' & Hr & Hmt). exists m'. split; [|exact Hmt].
        destruct (Z.eq_dec (φ m') (φ m)) as [E|E]; [|lia].
        apply to_Z_inj in E. subst m'.
        apply (search_m_spec m k1 k2 sh size Hm' Hk1 Hsh Hsize) in Hmt. congruence.
  - split; [discriminate|]. intros (m' & Hr & _).
    rewrite <- Bool.not_true_iff_false, ltb_spec in Hm. lia.
Qed.

Lemma length_cover : forall q : list N, NoDup q ->
  (forall i, In i q <-> (Z.of_N i < (φ n))%Z) -> List.length q = Z.to_nat (φ n).
Proof.
  intros q Hnd Hcov.
  set (sq := map N.of_nat (seq 0 (Z.to_nat (φ n)))).
  assert (Hs : forall i, In i sq <-> (Z.of_N i < (φ n))%Z).
  { intros i. unfold sq. rewrite in_map_iff. split.
    - intros (k & <- & Hk). apply in_seq in Hk. lia.
    - intros Hi. exists (N.to_nat i). split; [apply N2Nat.id|]. apply in_seq. lia. }
  assert (Nsq : NoDup sq).
  { apply Injective_map_NoDup; [intros x y E; lia | apply seq_NoDup]. }
  assert (Lsq : List.length sq = Z.to_nat (φ n)) by (unfold sq; rewrite length_map, length_seq; reflexivity).
  apply Nat.le_antisymm.
  - rewrite <- Lsq. apply NoDup_incl_length; [exact Hnd|]. intros i Hi. apply Hs, Hcov, Hi.
  - rewrite <- Lsq. apply NoDup_incl_length; [exact Nsq|]. intros i Hi. apply Hcov, Hs, Hi.
Qed.

(* Completeness: a race of length L gives a match at some middle point *)
Lemma complete : forall k1 k2 : int,
  (φ k1) = (((φ n) - 2) / 2)%Z -> (φ k2) = ((φ n) - 2 - (φ k1))%Z ->
  (exists p, visiting_order d p /\ race_length d p = tN L) ->
  exists m' : int, (0 <= (φ m') < (φ a))%Z /\
    Match d L a m' (fpm m') (needm m') (fr2m m') k1 k2.
Proof.
  intros k1 k2 Hk1 Hk2 (p & (Hnd & Hcov0) & Hr).
  pose proof Ha_val as Ha.
  assert (Hcov : forall i, In i p <-> (Z.of_N i < (φ n))%Z).
  { intros i. rewrite Hcov0. unfold len. lia. }
  clear Hcov0.
  assert (HaIn : In (tN a) p) by (apply Hcov; rewrite tN_spec; lia).
  destruct (in_split _ _ HaIn) as (l1 & l2 & Ep). subst p.
  assert (Hperm : Permutation (l1 ++ tN a :: l2) (tN a :: l2 ++ l1))
    by (exact (Permutation_app_comm l1 (tN a :: l2))).
  assert (Hndq : NoDup (tN a :: l2 ++ l1)) by (exact (Permutation_NoDup Hperm Hnd)).
  assert (Hcovq : forall i, In i (tN a :: l2 ++ l1) <-> (Z.of_N i < (φ n))%Z).
  { intros i. rewrite <- Hcov. split; apply Permutation_in; [symmetry|]; exact Hperm. }
  assert (Hrq : race_length d (tN a :: l2 ++ l1) = tN L).
  { rewrite <- Hr. rewrite (race_rot d l1 (tN a :: l2)). reflexivity. }
  clear Hnd Hcov Hr Hperm HaIn.
  set (rest := l2 ++ l1) in *.
  pose proof (length_cover _ Hndq Hcovq) as Hlq. simpl in Hlq.
  assert (Hk1b : (0 <= (φ k1) <= (φ n) - 2)%Z).
  { rewrite Hk1. split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; lia. }
  destruct (skipn (Z.to_nat (φ k1)) rest) as [|m0 ys] eqn:Es.
  { exfalso. pose proof (length_skipn (Z.to_nat (φ k1)) rest) as F.
    rewrite Es in F. simpl in F. lia. }
  set (xs := firstn (Z.to_nat (φ k1)) rest).
  assert (Erest : rest = xs ++ m0 :: ys) by (rewrite <- Es; symmetry; apply firstn_skipn).
  assert (Lx : Z.of_nat (List.length xs) = (φ k1)).
  { unfold xs. rewrite length_firstn. lia. }
  assert (Ly : Z.of_nat (List.length ys) = (φ k2)).
  { pose proof (length_skipn (Z.to_nat (φ k1)) rest) as F. rewrite Es in F. simpl in F. lia. }
  rewrite Erest in Hndq, Hcovq, Hrq. clearbody xs. clear Es Erest Hlq rest.
  assert (Hm0 : (Z.of_N m0 < (φ a))%Z).
  { assert (Hin : In m0 (tN a :: xs ++ m0 :: ys))
      by (right; apply in_or_app; right; left; reflexivity).
    pose proof (proj1 (Hcovq m0) Hin).
    destruct (Z.eq_dec (Z.of_N m0) (φ a)) as [E|E]; [|lia].
    exfalso. apply NoDup_cons_iff in Hndq. destruct Hndq as [F _]. apply F.
    replace (tN a) with m0 by (rewrite <- (tN_spec a) in E; lia).
    apply in_or_app; right; left; reflexivity. }
  set (m' := of_Z (Z.of_N m0)).
  assert (Em' : (φ m') = Z.of_N m0).
  { unfold m'. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. }
  assert (Etm : tN m' = m0) by (unfold tN; rewrite Em'; lia).
  rewrite <- Etm in Hndq, Hcovq, Hrq.
  assert (Hm' : ((φ m') < (φ a))%Z) by lia.
  exists m'. split; [pose proof (to_Z_bounded m'); lia|].
  pose proof (fpm_bits m' Hm') as Hfp. pose proof (needm_fp m' Hm') as Hneed.
  pose proof (fr2m_bits m' Hm') as Hfr2.
  assert (HrZ : Z.of_N (race_length d (tN a :: xs ++ tN m' :: ys)) = (φ L))
    by (rewrite Hrq; unfold tN; lia).
  assert (Ev : evn = true \/ evn = false) by (destruct evn; auto).
  destruct Ev as [Ev|Ev].
  - (* n even, at least 4: the symmetry point p0 *)
    pose proof (evn_spec Ev) as H4.
    set (pv := Z.to_N (φ (p0 m'))).
    assert (Epv : Z.of_N pv = (φ (p0 m'))) by (unfold pv; rewrite p0_spec; destruct ((φ m') =? 0)%Z; lia).
    assert (Hnb : forall w : N, Z.testbit (φ (needm m')) (Z.of_N w) = true <-> w = pv).
    { intros w. rewrite needm_bits, Ev. simpl andb. rewrite Z.eqb_eq. lia. }
    assert (Hpv : In pv (xs ++ ys)).
    { assert (Hin : In pv (tN a :: xs ++ tN m' :: ys)) by (apply Hcovq; rewrite p0_spec in Epv; destruct ((φ m') =? 0)%Z; lia).
      destruct Hin as [F|F].
      - exfalso. rewrite <- F, tN_spec, p0_spec in Epv. destruct ((φ m') =? 0)%Z; lia.
      - apply in_app_or in F. apply in_or_app. destruct F as [F|[F|F]]; [left; exact F | | right; exact F].
        exfalso. rewrite <- F, tN_spec, p0_spec in Epv.
        destruct ((φ m') =? 0)%Z eqn:E; [apply Z.eqb_eq in E | apply Z.eqb_neq in E]; lia. }
    pose proof (NoDup_cons_iff (tN a) (xs ++ tN m' :: ys)) as Hc. apply Hc in Hndq.
    destruct Hndq as [Hna Hndr]. clear Hc.
    pose proof (NoDup_remove_1 _ _ _ Hndr) as Ndxy.
    apply in_app_or in Hpv. destruct Hpv as [Hpv|Hpv].
    + apply (cycle_match d n L a m' (fpm m') (needm m') (fr2m m') k1 k2 0 Hn2 Ha Hm' Hfp Hneed Hfr2
               xs ys); try assumption.
      * constructor; assumption.
      * intros w T. apply Hnb in T. subst w. exact Hpv.
      * intros w T F. apply Hnb in T. subst w. exact (nodup_app_disj xs ys pv Ndxy Hpv F).
    + (* reverse the race *)
      assert (Ekk : (φ k1) = (φ k2)).
      { assert (Hev : ((φ n) mod 2 = 0)%Z).
        { apply andb_true_iff in Ev. destruct Ev as [E _]. apply eqb_true in E.
          assert (E' : (φ (n land 1)) = 0%Z) by (rewrite E; reflexivity).
          rewrite land_spec' in E'. change (φ 1) with (Z.ones 1) in E'.
          rewrite Z.land_ones in E' by lia. exact E'. }
        rewrite Hk2, Hk1. Z.to_euclidean_division_equations. lia. }
      assert (Hperm : Permutation (tN a :: xs ++ tN m' :: ys) (tN a :: rev ys ++ tN m' :: rev xs)).
      { apply perm_skip.
        replace (rev ys ++ tN m' :: rev xs) with (rev (xs ++ tN m' :: ys))
          by (rewrite rev_app_distr; simpl; rewrite <- app_assoc; reflexivity).
        apply Permutation_rev. }
      apply (cycle_match d n L a m' (fpm m') (needm m') (fr2m m') k1 k2 0 Hn2 Ha Hm' Hfp Hneed Hfr2
               (rev ys) (rev xs)).
      * apply (Permutation_NoDup Hperm). constructor; assumption.
      * intros i. rewrite <- Hcovq. split; apply Permutation_in; [symmetry|]; exact Hperm.
      * rewrite length_rev. lia.
      * rewrite length_rev. lia.
      * intros w T. apply Hnb in T. subst w. apply in_rev in Hpv. exact Hpv.
      * intros w T F. apply Hnb in T. subst w. apply in_rev in F.
        exact (nodup_app_disj xs ys pv Ndxy F Hpv).
      * rewrite race_split in HrZ |- *.
        rewrite <- (ell_rev d Hsym), <- (ell_rev d Hsym). lia.
  - (* no symmetry: need is empty *)
    assert (Hnb : forall w : N, Z.testbit (φ (needm m')) (Z.of_N w) = false).
    { intros w. rewrite needm_bits, Ev. reflexivity. }
    apply (cycle_match d n L a m' (fpm m') (needm m') (fr2m m') k1 k2 0 Hn2 Ha Hm' Hfp Hneed Hfr2
             xs ys); try assumption.
    + intros w T. rewrite Hnb in T. discriminate.
    + intros w T. rewrite Hnb in T. discriminate.
Qed.

Lemma main_iff : forall (k1 k2 sh size : int) H,
  (φ k1) = (((φ n) - 2) / 2)%Z -> (φ k2) = ((φ n) - 2 - (φ k1))%Z ->
  (forall k, ((φ (hidx sh k)) < (φ size))%Z) -> ((φ size) <= 4194303)%Z ->
  (mloop D n L a k1 k2 sh size 0 H = true <->
   exists p, visiting_order d p /\ race_length d p = tN L).
Proof.
  intros k1 k2 sh size H Hk1 Hk2 Hsh Hsize.
  rewrite (mloop_spec k1 k2 sh size Hk1 Hsh Hsize _ 0 H eq_refl). split.
  - intros (m' & Hr & Hm).
    assert (Hm' : ((φ m') < (φ a))%Z) by lia.
    exact (match_race d n L a m' (fpm m') (needm m') (fr2m m') k1 k2 0 Hn Hn2 HL Ha_val Hm'
             (fpm_bits m' Hm') (needm_fp m' Hm') (fr2m_bits m' Hm') Hm).
  - intros G. destruct (complete k1 k2 Hk1 Hk2 G) as (m' & Hr & Hm).
    exists m'. split; [change (φ 0) with 0%Z; lia | exact Hm].
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The input: the flat matrix, the bounds                              *)
(* ------------------------------------------------------------------ *)

Lemma fill_spec : forall (x : array (array int)) (n N : int) (z : Z) (i : int) (D : array int) H,
  gap N i = z -> ((φ i) <= (φ N))%Z -> PArray.length D = N ->
  (forall j : int, ((φ j) < (φ i))%Z -> D.[j] = x.[j / n].[j mod n]) ->
  PArray.length (fill x n N i D H) = N /\
  forall j : int, ((φ j) < (φ N))%Z -> (fill x n N i D H).[j] = x.[j / n].[j mod n].
Proof.
  intros x n N z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i D H Hz Hi HlD Hc. destruct H as [Hacc]. cbn [fill].
  destruct (bdec (i <? N)) as [Hk | Hk].
  - pose proof Hk as Hk'. rewrite ltb_spec in Hk'.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    apply (IH _ ltac:(rewrite <- Hz; apply dec_step; exact Hk)); [reflexivity | lia | |].
    + rewrite alength_set. exact HlD.
    + intros j Hj. destruct (Z.eq_dec (φ j) (φ i)) as [E|E].
      * apply to_Z_inj in E. subst j. apply aget_set_same. rewrite HlD. exact Hk.
      * rewrite aget_set_other by (apply int_neq; lia). apply Hc. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hk.
    split; [exact HlD|]. intros j Hj. apply Hc. lia.
Qed.

Lemma idx_arith : forall i j n : int, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z -> ((φ n) <= 14)%Z ->
  (i * n + j) / n = i /\ (i * n + j) mod n = j /\ ((φ (i * n + j)) < (φ (n * n)))%Z.
Proof.
  intros i j n Hi Hj Hn.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j). pose proof (to_Z_bounded n).
  assert (E1 : (φ (i * n)) = ((φ i) * (φ n))%Z).
  { rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. }
  assert (E2 : (φ (i * n + j)) = ((φ i) * (φ n) + (φ j))%Z).
  { rewrite add_spec, E1. apply Z.mod_small. rewrite wB_val. nia. }
  assert (E3 : (φ (n * n)) = ((φ n) * (φ n))%Z).
  { rewrite mul_spec. apply Z.mod_small. rewrite wB_val. nia. }
  split; [|split].
  - apply to_Z_inj. rewrite div_spec, E2.
    rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - apply to_Z_inj. rewrite mod_spec, E2.
    rewrite Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite E2, E3. nia.
Qed.

Lemma row_len : forall (d : list (list N)) k row,
  Forall (fun r => len r = len d) d -> nth_error d k = Some row ->
  List.length row = List.length d.
Proof.
  intros d k row Hrows Hk. apply nth_error_In in Hk.
  rewrite Forall_forall in Hrows. pose proof (Hrows row Hk) as E. unfold len in E. lia.
Qed.

Lemma repr_cell : forall (x : array (array uint)) (d : list (list N)),
  repr x d -> Forall (fun r => len r = len d) d ->
  forall i j : int, ((φ i) < Z.of_nat (List.length d))%Z -> ((φ j) < Z.of_nat (List.length d))%Z ->
  (φ (x.[i].[j])) = Z.of_N (dist d (tN i) (tN j)).
Proof.
  intros x d [Hl Hc] Hrows i j Hi Hj.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (row & Hrow & [Hrl Hrc]).
  pose proof (row_len d _ row Hrows Hrow) as Hrlen.
  destruct (Hrc (Z.to_nat (φ j)) ltac:(lia)) as (e & He & Hre).
  unfold repr, repr_uint in Hre.
  rewrite !Z2Nat.id in Hre by lia. rewrite !of_to_Z in Hre.
  unfold dist, tN. rewrite !Z_N_nat.
  rewrite (nth_error_nth _ _ _ Hrow), (nth_error_nth _ _ _ He).
  rewrite <- Hre. symmetry. apply Z2N.id. apply to_Z_bounded.
Qed.

Lemma dist_out : forall d : list (list N), Forall (fun r => len r = len d) d ->
  forall i j, (len d <= i \/ len d <= j)%N -> dist d i j = 0%N.
Proof.
  intros d Hrows i j Hij. unfold dist, len in *.
  destruct (Nat.lt_ge_cases (N.to_nat i) (List.length d)) as [Hi|Hi].
  - assert (Hj : (List.length d <= N.to_nat j)%nat) by lia.
    rewrite nth_overflow; [reflexivity|].
    pose proof (nth_In d [] Hi) as Hin. rewrite Forall_forall in Hrows.
    pose proof (Hrows _ Hin) as E. unfold len in E. lia.
  - rewrite (nth_overflow d [] Hi). destruct (N.to_nat j); reflexivity.
Qed.

Lemma dist_le_all : forall d L, valid_input d L -> forall i j, (dist d i j <= L)%N.
Proof.
  intros d L Hv i j. destruct Hv as [_ HL Hrows Hdiag Hdst _ _].
  destruct (N.lt_ge_cases i (len d)) as [Hi|Hi]; [destruct (N.lt_ge_cases j (len d)) as [Hj|Hj]|].
  - destruct (N.eq_dec i j) as [E|E].
    + subst j. rewrite Hdiag by exact Hi. lia.
    + apply Hdst; assumption.
  - rewrite dist_out by (auto; lia). lia.
  - rewrite dist_out by (auto; lia). lia.
Qed.

Lemma dist_sym_all : forall d L, valid_input d L -> forall i j, dist d i j = dist d j i.
Proof.
  intros d L Hv i j. destruct Hv as [_ _ Hrows _ _ Hsy _].
  destruct (N.lt_ge_cases i (len d)) as [Hi|Hi]; [destruct (N.lt_ge_cases j (len d)) as [Hj|Hj]|].
  - apply Hsy; assumption.
  - rewrite !dist_out by (auto; lia). reflexivity.
  - rewrite !dist_out by (auto; lia). reflexivity.
Qed.

Lemma logcap_range : forall n, (7 <= (φ (logcap n)) <= 20)%Z.
Proof.
  intros n. unfold logcap.
  repeat (match goal with |- context [if ?c then _ else _] => destruct c end);
    split; cbv; congruence.
Qed.

Lemma hidx_bound : forall b k, (7 <= (φ b) <= 20)%Z ->
  ((φ (hidx (63 - b) k)) < (φ ((1 << b) + 256)))%Z.
Proof.
  intros b k Hb. unfold hidx.
  assert (Es : (φ (63 - b)) = (63 - (φ b))%Z).
  { rewrite sub_spec. change (φ 63) with 63%Z. apply Z.mod_small. lia. }
  assert (Eb : (φ ((1 << b) + 256)) = (2 ^ (φ b) + 256)%Z).
  { rewrite add_spec, bit_spec by lia. change (φ 256) with 256%Z. apply Z.mod_small.
    assert (2 ^ (φ b) <= 2 ^ 20)%Z by (apply Z.pow_le_mono_r; lia). rewrite wB_val. lia. }
  rewrite lsr_spec, Es, Eb.
  pose proof (to_Z_bounded (k * hmul)) as B.
  assert (E63 : (2 ^ (63 - (φ b)) * 2 ^ (φ b) = 9223372036854775808)%Z).
  { rewrite <- Z.pow_add_r by lia. replace (63 - (φ b) + (φ b))%Z with 63%Z by lia. reflexivity. }
  assert (Hdiv : ((φ (k * hmul)) / 2 ^ (63 - (φ b)) < 2 ^ (φ b))%Z).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia | lia]. }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma bool_match_of_iff : forall (b : bool) (P : Prop),
  (b = true <-> P) -> match b with true => P | false => ~ P end.
Proof.
  intros [|] P [H1 H2]; [exact (H1 eq_refl)|intros HP; discriminate (H2 HP)].
Qed.

Lemma indoor_correct : forall (d : list (list N)) (Ln : N)
  (x : array (array uint)) (y : uint),
  valid_input d Ln -> repr x d -> repr y Ln ->
  exists b : bool, repr (indoor x y) b /\ indoorienteering_spec d Ln b.
Proof.
  intros d Ln x y Hv Hx Hy.
  exists (indoor x y). split; [reflexivity|].
  unfold repr, repr_uint in Hy. subst Ln.
  pose proof (dist_le_all d _ Hv) as Hle. pose proof (dist_sym_all d _ Hv) as Hsym.
  pose proof Hv as Hv'. destruct Hv' as [Hvn HvL Hrows _ _ _ _].
  unfold len in Hvn, HvL.
  pose proof (to_Z_bounded y) as By.
  assert (Hn : (φ (PArray.length x)) = Z.of_nat (List.length d)).
  { destruct Hx as [Hl _]. symmetry. exact Hl. }
  assert (Hn2 : (2 <= (φ (PArray.length x)) <= 14)%Z) by lia.
  assert (HL : (1 <= (φ y) <= 10 ^ 15)%Z) by lia.
  assert (Hdist : forall i j, (Z.of_N (dist d i j) <= (φ y))%Z)
    by (intros i j; pose proof (Hle i j); lia).
  unfold indoorienteering_spec, indoor. cbv zeta. apply bool_match_of_iff.
  set (n := PArray.length x) in *.
  assert (HNl : PArray.length (PArray.make (n * n) 0) = n * n).
  { rewrite alength_make. replace (n * n <=? PArray.max_length) with true; [reflexivity|].
    symmetry. rewrite leb_spec, max_length_val. rewrite mul_spec, Z.mod_small; [nia|].
    rewrite wB_val. nia. }
  destruct (fill_spec x n (n * n) _ 0 (PArray.make (n * n) 0)
              (Zwf_well_founded 0 (gap (n * n) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded (n * n)); lia) HNl
              ltac:(intros j Hj; change (φ 0) with 0%Z in Hj; pose proof (to_Z_bounded j); lia))
    as [_ Hfill].
  set (D := fill x n (n * n) 0 (PArray.make (n * n) 0) (Zwf_well_founded 0 (gap (n * n) 0))) in *.
  assert (HD : forall i j : int, ((φ i) < (φ n))%Z -> ((φ j) < (φ n))%Z ->
            (φ (D.[i * n + j])) = Z.of_N (dist d (tN i) (tN j))).
  { intros i j Hi Hj. destruct (idx_arith i j n Hi Hj ltac:(lia)) as (E1 & E2 & E3).
    rewrite Hfill by exact E3. rewrite E1, E2.
    exact (repr_cell x d Hx Hrows i j ltac:(lia) ltac:(lia)). }
  pose proof (logcap_range n) as Hb.
  assert (Hn2' : (2 <= (φ n))%Z) by lia.
  assert (Hk1 : (φ ((n - 2) / 2)) = (((φ n) - 2) / 2)%Z).
  { rewrite div_spec, sub_spec. change (φ 2) with 2%Z. rewrite (Z.mod_small ((φ n) - 2)) by lia.
    reflexivity. }
  assert (Hk2 : (φ (n - 2 - (n - 2) / 2)) = ((φ n) - 2 - (φ ((n - 2) / 2)))%Z).
  { rewrite Hk1. rewrite !sub_spec. change (φ 2) with 2%Z.
    rewrite (Z.mod_small ((φ n) - 2)) by lia. rewrite div_spec, sub_spec.
    change (φ 2) with 2%Z. rewrite (Z.mod_small ((φ n) - 2)) by lia.
    apply Z.mod_small. split; [|lia].
    assert (((φ n) - 2) / 2 <= (φ n) - 2)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  assert (Hsize : ((φ ((1 << logcap n) + 256)) <= 4194303)%Z).
  { rewrite add_spec, bit_spec by lia. change (φ 256) with 256%Z.
    assert (2 ^ (φ (logcap n)) <= 2 ^ 20)%Z by (apply Z.pow_le_mono_r; lia).
    rewrite Z.mod_small; [lia|]. rewrite wB_val. lia. }
  rewrite (main_iff d D n y Hn Hn2 HL Hdist Hsym HD ((n - 2) / 2) (n - 2 - (n - 2) / 2)
             (63 - logcap n) ((1 << logcap n) + 256) _ Hk1 Hk2
             (fun k => hidx_bound (logcap n) k Hb) Hsize).
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition indoorienteering : array (array uint) -> uint -> bool := indoor.

Definition indoorienteering_correct :
  forall (d : list (list N)) (L : N) (x : array (array uint)) (y : uint),
  valid_input d L -> repr x d -> repr y L ->
  exists b : bool, repr (indoorienteering x y) b /\
                   indoorienteering_spec d L b
  := indoor_correct.
