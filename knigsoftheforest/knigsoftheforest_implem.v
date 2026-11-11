From Knigsoftheforest.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import FinFun.
From Stdlib Require Import Permutation.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

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

Definition gap (m j : int) : Z := ((φ m) - (φ j))%Z.

Lemma dec_step : forall m i : int,
  (i <? m) = true -> Zwf 0 (gap m (i + 1)) (gap m i).
Proof.
  intros m i H. rewrite ltb_spec in H.
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, gap. lia.
Qed.

Lemma dec_up : forall i : int,
  (0 <? i) = true -> Zwf 0 (φ ((i - 1) / 2)) (φ i).
Proof.
  intros i H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  unfold Zwf. sia.
Qed.

(* The larger child of the node whose left child is l, in a heap of size s. *)
Definition pick (h : array int) (s l : int) : int :=
  if l + 1 <? s then (if h.[l] <? h.[l + 1] then l + 1 else l) else l.

Lemma dec_down : forall (h : array int) (s i : int),
  (i <? s / 2) = true -> Zwf 0 ((φ s) - (φ (pick h s (2 * i + 1))))%Z ((φ s) - (φ i))%Z.
Proof.
  intros h s i H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded i).
  assert (Hs2 : (φ (s / 2)) = ((φ s) / 2)%Z) by sia.
  assert (Hl : (φ (2 * i + 1)) = (2 * (φ i) + 1)%Z) by sia.
  unfold pick, Zwf.
  destruct (2 * i + 1 + 1 <? s) eqn:E1; [destruct (h.[2 * i + 1] <? h.[2 * i + 1 + 1])|];
    rewrite ?ltb_spec in E1; sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* CLRS max-heap on the first s cells of h, keyed on the values. *)
Fixpoint sift_up (h : array int) (i : int) (H : Acc (Zwf 0) (φ i)) {struct H}
    : array int :=
  match bdec (0 <? i) with
  | left Hi =>
      let q := (i - 1) / 2 in
      let vi := h.[i] in
      let vq := h.[q] in
      match bdec (vq <? vi) with
      | left _ => sift_up h.[i <- vq].[q <- vi] q (Acc_inv H (dec_up i Hi))
      | right _ => h
      end
  | right _ => h
  end.

Fixpoint sift_down (h : array int) (s i : int) (H : Acc (Zwf 0) ((φ s) - (φ i))%Z)
    {struct H} : array int :=
  match bdec (i <? s / 2) with
  | left Hi =>
      let c := pick h s (2 * i + 1) in
      let vi := h.[i] in
      let vc := h.[c] in
      match bdec (vi <? vc) with
      | left _ => sift_down h.[i <- vc].[c <- vi] s c (Acc_inv H (dec_down h s i Hi))
      | right _ => h
      end
  | right _ => h
  end.

(* Insert v into the heap of size s (the new size is s + 1). *)
Definition insert (h : array int) (s v : int) : array int :=
  sift_up h.[s <- v] s (Zwf_well_founded 0 (φ s)).

(* Remove the maximum h.[0] of the heap of size s >= 1 (new size s - 1). *)
Definition extract (h : array int) (s : int) : array int :=
  let s1 := s - 1 in
  sift_down h.[0 <- h.[s1]] s1 0 (Zwf_well_founded 0 ((φ s1) - (φ 0))%Z).

(* One moose: in the pool of 2011 (the heap), or the newcomer of its year
   (the table, indexed by year - 2011). *)
Definition step (st : array int * int * array int) (yr sv : int)
    : array int * int * array int :=
  let '(h, s, t) := st in
  if yr =? 2011 then (insert h s sv, s + 1, t)
  else (h, s, t.[yr - 2011 <- sv]).

Fixpoint fill (ys ps : array int) (m i : int) (st : array int * int * array int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int * int * array int :=
  match bdec (i <? m) with
  | left Hi => fill ys ps m (i + 1) (step st ys.[i] ps.[i]) (Acc_inv H (dec_step m i Hi))
  | right _ => st
  end.

(* Year 2011 + d: the strongest moose of the pool wins. *)
Fixpoint sim (t h : array int) (n p s d : int) (H : Acc (Zwf 0) (gap n d)) {struct H}
    : option int :=
  match bdec (d <? n) with
  | left Hd =>
      if s =? 0 then None else
      let top := h.[0] in
      if top =? p then Some (2011 + d)
      else if d + 1 <? n then
        sim t (insert (extract h s) (s - 1) t.[d + 1]) n p s (d + 1)
          (Acc_inv H (dec_step n d Hd))
      else None
  | right _ => None
  end.

Definition knigs_impl (k n y p : uint) (ys ps : array uint) : option uint :=
  let m := PArray.length ys in
  let st0 := step (PArray.make (m + 1) 0, 0, PArray.make n 0) y p in
  let '(h, s, t) := fill ys ps m 0 st0 (Zwf_well_founded 0 (gap m 0)) in
  sim t h n p s 0 (Zwf_well_founded 0 (gap n 0)).

Lemma sift_up_eq : forall h i H,
  sift_up h i H =
  match bdec (0 <? i) with
  | left Hi =>
      let q := (i - 1) / 2 in
      let vi := h.[i] in
      let vq := h.[q] in
      match bdec (vq <? vi) with
      | left _ => sift_up h.[i <- vq].[q <- vi] q (Acc_inv H (dec_up i Hi))
      | right _ => h
      end
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sift_down_eq : forall h s i H,
  sift_down h s i H =
  match bdec (i <? s / 2) with
  | left Hi =>
      let c := pick h s (2 * i + 1) in
      let vi := h.[i] in
      let vc := h.[c] in
      match bdec (vi <? vc) with
      | left _ => sift_down h.[i <- vc].[c <- vi] s c (Acc_inv H (dec_down h s i Hi))
      | right _ => h
      end
  | right _ => h
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma fill_eq : forall ys ps m i st H,
  fill ys ps m i st H =
  match bdec (i <? m) with
  | left Hi => fill ys ps m (i + 1) (step st ys.[i] ps.[i]) (Acc_inv H (dec_step m i Hi))
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma sim_eq : forall t h n p s d H,
  sim t h n p s d H =
  match bdec (d <? n) with
  | left Hd =>
      if s =? 0 then None else
      let top := h.[0] in
      if top =? p then Some (2011 + d)
      else if d + 1 <? n then
        sim t (insert (extract h s) (s - 1) t.[d + 1]) n p s (d + 1)
          (Acc_inv H (dec_step n d Hd))
      else None
  | right _ => None
  end.
Proof. intros. destruct H. reflexivity. Qed.

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

Lemma alength_bound : forall (t : array int), ((φ (PArray.length t)) <= 4194303)%Z.
Proof.
  intros t. pose proof (leb_length int t) as H.
  rewrite leb_spec, max_length_val in H. exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* Heaps as functions on Z                                             *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.

Ltac zdiv := Z.to_euclidean_division_equations; lia.

Definition par (j : Z) : Z := (j - 1) / 2.

Lemma par_lt : forall j, 0 < j -> 0 <= par j < j.
Proof. intros j H. unfold par. zdiv. Qed.

Definition hp (f : Z -> Z) (s : Z) : Prop :=
  forall j, 0 < j < s -> f j <= f (par j).

Definition inv_up (f : Z -> Z) (s i : Z) : Prop :=
  (forall j, 0 < j < s -> j <> i -> f j <= f (par j)) /\
  (0 < i -> forall c, 0 < c < s -> par c = i -> f c <= f (par i)).

Definition inv_dn (f : Z -> Z) (s i : Z) : Prop :=
  (forall j, 0 < j < s -> par j <> i -> f j <= f (par j)) /\
  (0 < i -> forall c, 0 < c < s -> par c = i -> f c <= f (par i)).

Definition upd (f : Z -> Z) (a v : Z) : Z -> Z :=
  fun j => if Z.eqb j a then v else f j.

Definition swapf (f : Z -> Z) (a b : Z) : Z -> Z := upd (upd f a (f b)) b (f a).

Definition cnt (f : Z -> Z) (s : Z) : list Z :=
  map (fun t => f (Z.of_nat t)) (seq 0 (Z.to_nat s)).

Definition eqon (s : Z) (f g : Z -> Z) : Prop := forall j, 0 <= j < s -> f j = g j.

Lemma hp_eqon : forall s f g, eqon s f g -> hp f s -> hp g s.
Proof.
  intros s f g E H j Hj. pose proof (par_lt j (proj1 Hj)).
  rewrite <- (E j), <- (E (par j)) by lia. apply H; lia.
Qed.

Lemma inv_up_eqon : forall s i f g, eqon s f g -> inv_up f s i -> inv_up g s i.
Proof.
  intros s i f g E [Ha Hb]. split.
  - intros j Hj Hji. pose proof (par_lt j (proj1 Hj)).
    rewrite <- (E j), <- (E (par j)) by lia. apply Ha; lia.
  - intros Hi c Hc Hpc. pose proof (par_lt c (proj1 Hc)). pose proof (par_lt i Hi).
    rewrite <- (E c), <- (E (par i)) by lia. apply Hb; lia.
Qed.

Lemma inv_dn_eqon : forall s i f g, eqon s f g -> inv_dn f s i -> inv_dn g s i.
Proof.
  intros s i f g E [Ha Hb]. split.
  - intros j Hj Hji. pose proof (par_lt j (proj1 Hj)).
    rewrite <- (E j), <- (E (par j)) by lia. apply Ha; lia.
  - intros Hi c Hc Hpc. pose proof (par_lt c (proj1 Hc)). pose proof (par_lt i Hi).
    rewrite <- (E c), <- (E (par i)) by lia. apply Hb; lia.
Qed.

Lemma cnt_eqon : forall s f g, eqon s f g -> cnt f s = cnt g s.
Proof.
  intros s f g E. unfold cnt. apply map_ext_in. intros t Ht.
  rewrite in_seq in Ht. apply E. lia.
Qed.

Lemma cnt_length : forall f s, 0 <= s -> Z.of_nat (List.length (cnt f s)) = s.
Proof. intros f s H. unfold cnt. rewrite length_map, length_seq. lia. Qed.

Lemma in_cnt : forall f s v, In v (cnt f s) <-> exists j, 0 <= j < s /\ f j = v.
Proof.
  intros f s v. unfold cnt. rewrite in_map_iff. split.
  - intros [t [Ht Hin]]. rewrite in_seq in Hin. exists (Z.of_nat t). split; [lia | exact Ht].
  - intros [j [Hj Hv]]. exists (Z.to_nat j). rewrite in_seq. split; [|lia].
    rewrite Z2Nat.id by lia. exact Hv.
Qed.

Lemma cnt_swap : forall f s a b, 0 <= a < s -> 0 <= b < s ->
  Permutation (cnt (swapf f a b) s) (cnt f s).
Proof.
  intros f s a b Ha Hb.
  set (na := Z.to_nat a). set (nb := Z.to_nat b).
  set (tau := fun t : nat => if Nat.eqb t nb then na else if Nat.eqb t na then nb else t).
  assert (E : cnt (swapf f a b) s
              = map (fun t => f (Z.of_nat t)) (map tau (seq 0 (Z.to_nat s)))).
  { unfold cnt. rewrite map_map. apply map_ext. intro t.
    unfold swapf, upd, tau.
    destruct (Nat.eqb_spec t nb); destruct (Z.eqb_spec (Z.of_nat t) b); try lia;
      [f_equal; lia|].
    destruct (Nat.eqb_spec t na); destruct (Z.eqb_spec (Z.of_nat t) a); try lia;
      f_equal; lia. }
  rewrite E. unfold cnt. apply Permutation_map.
  apply NoDup_Permutation.
  - apply Injective_map_NoDup; [|apply seq_NoDup].
    intros x y. unfold tau.
    destruct (Nat.eqb_spec x nb), (Nat.eqb_spec x na), (Nat.eqb_spec y nb),
      (Nat.eqb_spec y na); lia.
  - apply seq_NoDup.
  - intro x. rewrite in_map_iff. split.
    + intros [y [Hy Hin]]. rewrite in_seq in *. subst x. unfold tau.
      destruct (Nat.eqb_spec y nb), (Nat.eqb_spec y na); lia.
    + intros Hin. exists (tau x). rewrite in_seq in *. unfold tau.
      repeat match goal with |- context [Nat.eqb ?u ?v] => destruct (Nat.eqb_spec u v) end;
        lia.
Qed.

Lemma cnt_upd_end : forall f s v, 0 <= s ->
  Permutation (cnt (upd f s v) (s + 1)) (v :: cnt f s).
Proof.
  intros f s v Hs. unfold cnt.
  replace (Z.to_nat (s + 1)) with (S (Z.to_nat s)) by lia.
  rewrite seq_S, map_app. simpl.
  replace (map (fun t => upd f s v (Z.of_nat t)) (seq 0 (Z.to_nat s)))
    with (map (fun t => f (Z.of_nat t)) (seq 0 (Z.to_nat s))).
  - unfold upd at 1. rewrite Z2Nat.id, Z.eqb_refl by lia.
    apply Permutation_sym, Permutation_cons_append.
  - apply map_ext_in. intros t Ht. rewrite in_seq in Ht. unfold upd.
    destruct (Z.eqb_spec (Z.of_nat t) s); [lia | reflexivity].
Qed.

Lemma cnt_extract : forall f s, 1 <= s ->
  Permutation (cnt f s) (f 0 :: cnt (upd f 0 (f (s - 1))) (s - 1)).
Proof.
  intros f s Hs. unfold cnt.
  replace (Z.to_nat s) with (S (Z.to_nat (s - 1))) by lia.
  rewrite seq_S, map_app.
  destruct (Z.to_nat (s - 1)) as [|n] eqn:En.
  - simpl. replace (s - 1) with 0 by lia. reflexivity.
  - assert (Hm : map (fun t => upd f 0 (f (s - 1)) (Z.of_nat t)) (seq 1 n)
                 = map (fun t => f (Z.of_nat t)) (seq 1 n)).
    { apply map_ext_in. intros t Ht. rewrite in_seq in Ht. unfold upd.
      destruct (Z.eqb_spec (Z.of_nat t) 0); [lia | reflexivity]. }
    assert (Hu : upd f 0 (f (s - 1)) (Z.of_nat 0) = f (s - 1)) by reflexivity.
    change (seq 0 (S n)) with (0%nat :: seq 1 n). cbn [map app].
    rewrite Hm, Hu. replace (Z.of_nat (0 + S n)) with (s - 1) by lia.
    apply perm_skip. apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma hp_max : forall f s, hp f s -> forall j, 0 <= j < s -> f j <= f 0.
Proof.
  intros f s H.
  assert (A : forall n j, (Z.to_nat j <= n)%nat -> 0 <= j < s -> f j <= f 0).
  { induction n as [|n IH]; intros j Hn Hj.
    - replace j with 0 by lia. lia.
    - destruct (Z.eq_dec j 0) as [->|Hj0]; [lia|].
      pose proof (par_lt j ltac:(lia)).
      pose proof (H j ltac:(lia)). pose proof (IH (par j) ltac:(lia) ltac:(lia)). lia. }
  intros j Hj. exact (A _ j (le_n _) Hj).
Qed.

Lemma up_step : forall f s i, inv_up f s i -> 0 < i < s -> f (par i) < f i ->
  inv_up (swapf f i (par i)) s (par i).
Proof.
  intros f s i [Ha Hb] Hi Hlt. pose proof (par_lt i (proj1 Hi)) as Pi.
  unfold swapf, upd. split.
  - intros j Hj Hjq. pose proof (par_lt j (proj1 Hj)) as Pj.
    destruct (Z.eqb_spec j (par i)); [lia|].
    destruct (Z.eqb_spec j i) as [->|Hji].
    + rewrite Z.eqb_refl. lia.
    + assert (A1 : f j <= f (par j)) by (apply Ha; lia).
      destruct (Z.eqb_spec (par j) (par i)) as [E|E].
      * rewrite E in A1. lia.
      * destruct (Z.eqb_spec (par j) i) as [E2|E2].
        -- apply Hb; lia.
        -- exact A1.
  - intros Hq c Hc Hpc. pose proof (par_lt c (proj1 Hc)) as Pc.
    pose proof (par_lt (par i) Hq) as Pq.
    destruct (Z.eqb_spec (par (par i)) (par i)); [lia|].
    destruct (Z.eqb_spec (par (par i)) i); [lia|].
    assert (A1 : f (par i) <= f (par (par i))) by (apply Ha; lia).
    destruct (Z.eqb_spec c (par i)); [lia|].
    destruct (Z.eqb_spec c i) as [->|Hci]; [exact A1|].
    assert (A2 : f c <= f (par c)) by (apply Ha; lia).
    rewrite Hpc in A2. lia.
Qed.

Lemma up_done : forall f s i, inv_up f s i -> 0 <= i ->
  (i = 0 \/ f i <= f (par i)) -> hp f s.
Proof.
  intros f s i [Ha Hb] Hi H j Hj.
  destruct (Z.eq_dec j i) as [->|Hji]; [|apply Ha; lia].
  destruct H as [H|H]; [lia | exact H].
Qed.

Lemma up_init : forall f s v, hp f s -> 0 <= s -> inv_up (upd f s v) (s + 1) s.
Proof.
  intros f s v H Hs. unfold upd. split.
  - intros j Hj Hjs. pose proof (par_lt j (proj1 Hj)).
    destruct (Z.eqb_spec j s); [lia|]. destruct (Z.eqb_spec (par j) s); [lia|].
    apply H; lia.
  - intros Hs0 c Hc Hpc. unfold par in Hpc. zdiv.
Qed.

Lemma dn_step : forall f s i c, inv_dn f s i -> 0 <= i -> 0 < c < s -> par c = i ->
  (forall j, 0 < j < s -> par j = i -> f j <= f c) -> f i < f c ->
  inv_dn (swapf f i c) s c.
Proof.
  intros f s i c [Ha Hb] Hi Hc Hpc Hmax Hlt.
  pose proof (par_lt c (proj1 Hc)) as Pc.
  unfold swapf, upd. split.
  - intros j Hj Hjc. pose proof (par_lt j (proj1 Hj)) as Pj.
    destruct (Z.eqb_spec j c) as [->|Hjc'].
    + rewrite Hpc. destruct (Z.eqb_spec i c); [lia|]. rewrite Z.eqb_refl. lia.
    + destruct (Z.eqb_spec j i) as [->|Hji].
      * destruct (Z.eqb_spec (par i) c); [lia|].
        destruct (Z.eqb_spec (par i) i); [lia|]. apply Hb; lia.
      * destruct (Z.eqb_spec (par j) c); [lia|].
        destruct (Z.eqb_spec (par j) i) as [E|E].
        -- apply Hmax; lia.
        -- apply Ha; lia.
  - intros Hc0 d Hd Hpd. pose proof (par_lt d (proj1 Hd)) as Pd.
    rewrite Hpc. rewrite Z.eqb_refl.
    destruct (Z.eqb_spec i c); [lia|].
    destruct (Z.eqb_spec d c); [lia|]. destruct (Z.eqb_spec d i); [lia|].
    assert (A : f d <= f (par d)) by (apply Ha; lia). rewrite Hpd in A. exact A.
Qed.

Lemma dn_done : forall f s i, inv_dn f s i ->
  (forall j, 0 < j < s -> par j = i -> f j <= f i) -> hp f s.
Proof.
  intros f s i [Ha Hb] H j Hj.
  destruct (Z.eq_dec (par j) i) as [E|E]; [rewrite E; apply H; auto | apply Ha; auto].
Qed.

Lemma dn_init : forall f s, hp f s -> 1 <= s -> inv_dn (upd f 0 (f (s - 1))) (s - 1) 0.
Proof.
  intros f s H Hs. unfold upd. split.
  - intros j Hj Hj0. pose proof (par_lt j (proj1 Hj)).
    destruct (Z.eqb_spec j 0); [lia|]. destruct (Z.eqb_spec (par j) 0); [lia|].
    apply H; lia.
  - intros Hi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The machine heap                                                    *)
(* ------------------------------------------------------------------ *)

Definition rd (h : array int) (j : Z) : Z := (φ (h.[of_Z j])).

Lemma rd_int : forall h (a : int), rd h (φ a) = (φ (h.[a])).
Proof. intros h a. unfold rd. rewrite of_to_Z. reflexivity. Qed.

Lemma of_Z_small : forall j, 0 <= j < wB -> (φ (of_Z j)) = j.
Proof. intros j Hj. rewrite of_Z_spec. apply Z.mod_small. exact Hj. Qed.

Lemma rd_set : forall (h : array int) (a v : int) j,
  (φ a) < (φ (PArray.length h)) -> 0 <= j < wB ->
  rd (h.[a <- v]) j = upd (rd h) (φ a) (φ v) j.
Proof.
  intros h a v j Ha Hj. unfold rd, upd.
  destruct (Z.eqb_spec j (φ a)) as [->|Hne].
  - rewrite of_to_Z, aget_set_same; [reflexivity|]. rewrite ltb_spec. exact Ha.
  - rewrite aget_set_other; [reflexivity|]. intro E. apply Hne.
    rewrite E, of_Z_small by exact Hj. reflexivity.
Qed.

Lemma eqon_set : forall (h : array int) (a v : int) s,
  (φ a) < (φ (PArray.length h)) -> s <= (φ (PArray.length h)) ->
  eqon s (rd (h.[a <- v])) (upd (rd h) (φ a) (φ v)).
Proof.
  intros h a v s Ha Hs j Hj. pose proof (alength_bound h). apply rd_set; [exact Ha|].
  rewrite wB_val. lia.
Qed.

Lemma eqon_swap : forall (h : array int) (a b : int) s,
  (φ a) < (φ (PArray.length h)) -> (φ b) < (φ (PArray.length h)) -> s <= (φ (PArray.length h)) ->
  eqon s (rd (h.[a <- h.[b]].[b <- h.[a]])) (swapf (rd h) (φ a) (φ b)).
Proof.
  intros h a b s Ha Hb Hs j Hj. pose proof (alength_bound h).
  unfold swapf. rewrite rd_set by (rewrite ?alength_set; first [exact Hb | rewrite wB_val; lia]).
  unfold upd. destruct (Z.eqb_spec j (φ b)); [rewrite rd_int; reflexivity|].
  rewrite rd_set by (first [exact Ha | rewrite wB_val; lia]).
  unfold upd. rewrite !rd_int. reflexivity.
Qed.

Lemma sift_up_spec : forall s z (i : int) (h : array int) (H : Acc (Zwf 0) (φ i)),
  (φ i) = z -> s <= (φ (PArray.length h)) -> 0 <= (φ i) < s -> inv_up (rd h) s (φ i) ->
  PArray.length (sift_up h i H) = PArray.length h /\ hp (rd (sift_up h i H)) s /\
  Permutation (cnt (rd (sift_up h i H)) s) (cnt (rd h) s).
Proof.
  intros s z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i h H Hz Hs Hi Hinv. rewrite sift_up_eq.
  destruct (bdec (0 <? i)%uint63) as [Hi0|Hi0]; cbv zeta.
  - pose proof Hi0 as Hi0'. rewrite ltb_spec in Hi0'. change (φ 0) with 0 in Hi0'.
    assert (Hq : (φ ((i - 1) / 2)) = par (φ i)) by (unfold par; sia).
    pose proof (par_lt (φ i) Hi0') as Pi.
    destruct (bdec (h.[(i - 1) / 2] <? h.[i])%uint63) as [Hlt|Hge].
    + rewrite ltb_spec, <- !rd_int, Hq in Hlt.
      assert (E := eqon_swap h i ((i - 1) / 2) s ltac:(lia) ltac:(lia) Hs).
      rewrite Hq in E.
      destruct (IH ((φ ((i - 1) / 2))%uint63) ltac:(rewrite <- Hz; apply dec_up; exact Hi0)
                ((i - 1) / 2)%uint63 (h.[i <- h.[(i - 1) / 2]].[(i - 1) / 2 <- h.[i]])
                (Acc_inv H (dec_up i Hi0)) eq_refl)
        as (L & P & Q).
      * rewrite !alength_set. exact Hs.
      * lia.
      * rewrite Hq. apply (inv_up_eqon s _ (swapf (rd h) (φ i) (par (φ i)))).
        -- intros j Hj. symmetry. apply E. exact Hj.
        -- apply up_step; [exact Hinv | lia | exact Hlt].
      * split; [etransitivity; [exact L|]; rewrite !alength_set; reflexivity|].
        split; [exact P|].
        eapply perm_trans; [exact Q|].
        rewrite (cnt_eqon s _ _ E). apply cnt_swap; lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, <- !rd_int, Hq in Hge.
      split; [reflexivity|]. split; [|apply Permutation_refl].
      apply (up_done _ _ (φ i) Hinv); lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi0. change (φ 0) with 0 in Hi0.
    split; [reflexivity|]. split; [|apply Permutation_refl].
    apply (up_done _ _ (φ i) Hinv); lia.
Qed.

Lemma children : forall i j, 0 <= i -> 0 < j -> par j = i -> j = 2 * i + 1 \/ j = 2 * i + 2.
Proof. intros i j Hi Hj H. unfold par in H. zdiv. Qed.

Lemma pick_spec : forall (h : array int) (s i : int), (i <? s / 2)%uint63 = true ->
  par (φ (pick h s (2 * i + 1))) = (φ i) /\ 0 < (φ (pick h s (2 * i + 1))) < (φ s) /\
  forall j, 0 < j < (φ s) -> par j = (φ i) -> rd h j <= rd h (φ (pick h s (2 * i + 1))).
Proof.
  intros h s i H. rewrite ltb_spec in H.
  pose proof (to_Z_bounded s). pose proof (to_Z_bounded i).
  assert (Hs2 : (φ (s / 2)) = (φ s) / 2) by sia.
  assert (Hl : (φ (2 * i + 1)) = 2 * (φ i) + 1) by sia.
  assert (Hl1 : (φ (2 * i + 1 + 1)) = 2 * (φ i) + 2) by sia.
  assert (Pl : par (2 * (φ i) + 1) = (φ i)) by (unfold par; zdiv).
  assert (Pl1 : par (2 * (φ i) + 2) = (φ i)) by (unfold par; zdiv).
  unfold pick.
  destruct (2 * i + 1 + 1 <? s)%uint63 eqn:E1.
  - rewrite ltb_spec in E1.
    destruct (h.[2 * i + 1] <? h.[2 * i + 1 + 1])%uint63 eqn:E2.
    + rewrite ltb_spec in E2. rewrite Hl1. split; [exact Pl1|]. split; [lia|].
      intros j Hj Hpj. destruct (children (φ i) j ltac:(lia) ltac:(lia) Hpj) as [->| ->].
      * rewrite <- Hl, <- Hl1, !rd_int. lia.
      * lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in E2.
      rewrite Hl. split; [exact Pl|]. split; [lia|].
      intros j Hj Hpj. destruct (children (φ i) j ltac:(lia) ltac:(lia) Hpj) as [->| ->].
      * lia.
      * rewrite <- Hl, <- Hl1, !rd_int. lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in E1.
    rewrite Hl. split; [exact Pl|]. split; [lia|].
    intros j Hj Hpj. destruct (children (φ i) j ltac:(lia) ltac:(lia) Hpj) as [->| ->];
      lia.
Qed.

Lemma sift_down_spec : forall z (s i : int) (h : array int) (H : Acc (Zwf 0) ((φ s) - (φ i))),
  (φ s) - (φ i) = z -> (φ s) <= (φ (PArray.length h)) -> inv_dn (rd h) (φ s) (φ i) ->
  PArray.length (sift_down h s i H) = PArray.length h /\ hp (rd (sift_down h s i H)) (φ s) /\
  Permutation (cnt (rd (sift_down h s i H)) (φ s)) (cnt (rd h) (φ s)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros s i h H Hz Hs Hinv. rewrite sift_down_eq.
  pose proof (to_Z_bounded i) as Bi.
  destruct (bdec (i <? s / 2)%uint63) as [Hi|Hi]; cbv zeta.
  - destruct (pick_spec h s i Hi) as (Pc & Bc & Mc).
    set (c := pick h s (2 * i + 1)) in *.
    destruct (bdec (h.[i] <? h.[c])%uint63) as [Hlt|Hge].
    + rewrite ltb_spec, <- !rd_int in Hlt.
      pose proof Hi as Hi'. rewrite ltb_spec in Hi'.
      assert (Hs2 : (φ (s / 2)) = (φ s) / 2) by sia.
      assert (E := eqon_swap h i c (φ s) ltac:(lia) ltac:(lia) Hs).
      destruct (IH ((φ s) - (φ c)) ltac:(rewrite <- Hz; apply dec_down; exact Hi)
                s c (h.[i <- h.[c]].[c <- h.[i]])
                (Acc_inv H (dec_down h s i Hi)) eq_refl)
        as (L & P & Q).
      * rewrite !alength_set. exact Hs.
      * apply (inv_dn_eqon _ _ (swapf (rd h) (φ i) (φ c))).
        -- intros j Hj. symmetry. apply E. exact Hj.
        -- apply dn_step; auto. lia.
      * split; [etransitivity; [exact L|]; rewrite !alength_set; reflexivity|].
        split; [exact P|].
        eapply perm_trans; [exact Q|].
        rewrite (cnt_eqon _ _ _ E). apply cnt_swap; lia.
    + rewrite <- Bool.not_true_iff_false, ltb_spec, <- !rd_int in Hge.
      split; [reflexivity|]. split; [|apply Permutation_refl].
      apply (dn_done _ _ (φ i) Hinv). intros j Hj Hpj.
      pose proof (Mc j Hj Hpj). lia.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hi.
    assert (Hs2 : (φ (s / 2)) = (φ s) / 2) by sia.
    split; [reflexivity|]. split; [|apply Permutation_refl].
    apply (dn_done _ _ (φ i) Hinv). intros j Hj Hpj.
    destruct (children (φ i) j ltac:(lia) ltac:(lia) Hpj); zdiv.
Qed.

Lemma insert_spec : forall (h : array int) (s v : int),
  (φ s) < (φ (PArray.length h)) -> hp (rd h) (φ s) ->
  PArray.length (insert h s v) = PArray.length h /\ hp (rd (insert h s v)) ((φ s) + 1) /\
  Permutation (cnt (rd (insert h s v)) ((φ s) + 1)) ((φ v) :: cnt (rd h) (φ s)).
Proof.
  intros h s v Hs Hh. unfold insert.
  pose proof (to_Z_bounded s) as Bs.
  assert (E := eqon_set h s v ((φ s) + 1) Hs ltac:(lia)).
  destruct (sift_up_spec ((φ s) + 1) (φ s) s h.[s <- v] (Zwf_well_founded 0 (φ s)) eq_refl)
    as (L & P & Q).
  - rewrite alength_set. lia.
  - lia.
  - apply (inv_up_eqon _ _ (upd (rd h) (φ s) (φ v))).
    + intros j Hj. symmetry. apply E. exact Hj.
    + apply up_init; [exact Hh | lia].
  - split; [rewrite L, alength_set; reflexivity|]. split; [exact P|].
    eapply perm_trans; [exact Q|]. rewrite (cnt_eqon _ _ _ E). apply cnt_upd_end. lia.
Qed.

Lemma extract_spec : forall (h : array int) (s : int),
  1 <= (φ s) <= (φ (PArray.length h)) -> hp (rd h) (φ s) ->
  PArray.length (extract h s) = PArray.length h /\ hp (rd (extract h s)) ((φ s) - 1) /\
  Permutation (cnt (rd h) (φ s)) ((φ (h.[0])) :: cnt (rd (extract h s)) ((φ s) - 1)).
Proof.
  intros h s Hs Hh. unfold extract.
  assert (Hs1 : (φ (s - 1)) = (φ s) - 1) by sia.
  assert (E := eqon_set h 0 h.[s - 1] ((φ s) - 1) ltac:(change (φ 0) with 0; lia) ltac:(lia)).
  change (φ 0) with 0 in E.
  destruct (sift_down_spec ((φ (s - 1)) - (φ 0)) (s - 1) 0 h.[0 <- h.[s - 1]]
              (Zwf_well_founded 0 ((φ (s - 1)) - (φ 0))) eq_refl) as (L & P & Q).
  - rewrite alength_set. lia.
  - change (φ 0) with 0. rewrite Hs1.
    apply (inv_dn_eqon _ _ (upd (rd h) 0 (rd h ((φ s) - 1)))).
    + intros j Hj. symmetry. rewrite E by exact Hj. rewrite <- Hs1, rd_int. reflexivity.
    + apply dn_init; [exact Hh | lia].
  - split; [etransitivity; [exact L|]; rewrite alength_set; reflexivity|].
    rewrite <- Hs1 in E. split; [rewrite <- Hs1; exact P|].
    eapply perm_trans; [apply cnt_extract; lia|].
    rewrite <- Hs1.
    change (rd h 0) with (rd h (φ 0)). rewrite rd_int. apply perm_skip.
    eapply perm_trans; [|apply Permutation_sym; exact Q].
    rewrite (cnt_eqon _ _ _ E). rewrite rd_int. apply Permutation_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Generic list facts                                                  *)
(* ------------------------------------------------------------------ *)

Lemma nodup_filter_nth : forall (f : N -> bool) (l : list N) i j,
  NoDup (filter f l) -> (i < List.length l)%nat -> (j < List.length l)%nat ->
  nth i l 0%N = nth j l 0%N -> f (nth i l 0%N) = true -> i = j.
Proof.
  intros f l. induction l as [|a l IH]; intros i j ND Hi Hj E F; simpl in *; [lia|].
  destruct i as [|i], j as [|j]; auto.
  - exfalso. rewrite F in ND. inversion ND as [|? ? Hn _]; subst. apply Hn.
    apply filter_In. split; [first [rewrite E | idtac]; apply nth_In; lia | exact F].
  - exfalso. rewrite <- E in ND. rewrite F in ND.
    inversion ND as [|? ? Hn _]; subst. apply Hn.
    apply filter_In. split; [apply nth_In; lia | exact F].
  - f_equal. apply IH; auto; try lia.
    destruct (f a); [inversion ND; auto | exact ND].
Qed.

Lemma in_entry : forall (l : list N) x, In x l -> exists c, (c < len l)%N /\ entry l c = x.
Proof.
  intros l x H. destruct (In_nth l x 0%N H) as [i [Hi Ei]].
  exists (N.of_nat i). unfold len, entry. rewrite Nat2N.id. split; [lia | exact Ei].
Qed.

Lemma filter_len_split : forall (f : N -> bool) (l : list N),
  (List.length (filter f l) + List.length (filter (fun x => negb (f x)) l))%nat
  = List.length l.
Proof.
  intros f l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a); simpl; lia.
Qed.

Lemma max_exists : forall (f : N -> N) (l : list N), l <> [] ->
  exists x, In x l /\ forall z, In z l -> (f z <= f x)%N.
Proof.
  intros f l. induction l as [|a l IH]; intros Hne; [congruence|].
  destruct l as [|b l'].
  - exists a. split; [left; reflexivity|]. intros z [<-|[]]. lia.
  - destruct (IH ltac:(discriminate)) as [x [Hx Hm]].
    destruct (N.le_ge_cases (f a) (f x)).
    + exists x. split; [right; exact Hx|]. intros z [<-|Hz]; [lia | apply Hm; exact Hz].
    + exists a. split; [left; reflexivity|].
      intros z [<-|Hz]; [lia | pose proof (Hm z Hz); lia].
Qed.

Definition yrsl (d : nat) : list N := map (fun j => (2011 + N.of_nat j)%N) (seq 0 d).

Lemma in_yrsl : forall d Y, In Y (yrsl d) <-> (2011 <= Y < 2011 + N.of_nat d)%N.
Proof.
  intros d Y. unfold yrsl. rewrite in_map_iff. split.
  - intros [j [<- Hj]]. rewrite in_seq in Hj. lia.
  - intros HY. exists (N.to_nat (Y - 2011)). rewrite in_seq. lia.
Qed.

Lemma nodup_yrsl : forall d, NoDup (yrsl d).
Proof.
  intros d. apply Injective_map_NoDup; [|apply seq_NoDup].
  intros a b E. lia.
Qed.

Lemma len_yrsl : forall d, List.length (yrsl d) = d.
Proof. intros d. unfold yrsl. rewrite length_map, length_seq. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The math side: the schedule exists and is unique                   *)
(* ------------------------------------------------------------------ *)

Section Problem.

Variables (k n y p : N) (ys ps : list N).
Hypothesis Hv : valid_input k n y p ys ps.

Local Notation yrs := (y :: ys).
Local Notation strs := (p :: ps).
Local Notation M := (len (y :: ys)).

Lemma len_ys_ps : List.length ps = List.length ys.
Proof. pose proof (vi_ys_len _ _ _ _ _ _ Hv). pose proof (vi_ps_len _ _ _ _ _ _ Hv).
  unfold len in *. lia. Qed.

Lemma M_val : M = (n + k - 1)%N.
Proof.
  pose proof (vi_ys_len _ _ _ _ _ _ Hv). pose proof (vi_n _ _ _ _ _ _ Hv).
  pose proof (vi_k _ _ _ _ _ _ Hv). unfold len in *. simpl List.length. lia.
Qed.

Lemma yr_range : forall c, (c < M)%N -> (2011 <= entry yrs c <= 2011 + n - 1)%N.
Proof.
  intros c Hc.
  assert (F : Forall (fun z => (2011 <= z <= 2011 + n - 1)%N) yrs)
    by (constructor; [exact (vi_y _ _ _ _ _ _ Hv) | exact (vi_ys _ _ _ _ _ _ Hv)]).
  rewrite Forall_nth in F. unfold entry. apply F. unfold len in Hc. lia.
Qed.

Lemma str_range : forall c, (c < M)%N -> (entry strs c <= 2 ^ 31 - 1)%N.
Proof.
  intros c Hc.
  assert (F : Forall (fun z => (z <= 2 ^ 31 - 1)%N) strs)
    by (constructor; [exact (vi_p _ _ _ _ _ _ Hv) | exact (vi_ps _ _ _ _ _ _ Hv)]).
  rewrite Forall_nth in F. unfold entry. apply F. pose proof len_ys_ps.
  unfold len in Hc. simpl List.length in *. lia.
Qed.

Lemma str_inj : forall c1 c2, (c1 < M)%N -> (c2 < M)%N ->
  entry strs c1 = entry strs c2 -> c1 = c2.
Proof.
  intros c1 c2 H1 H2 E. pose proof (vi_strengths _ _ _ _ _ _ Hv) as ND.
  rewrite (NoDup_nth _ 0%N) in ND. unfold entry in E. pose proof len_ys_ps.
  unfold len in H1, H2. simpl List.length in *.
  assert (N.to_nat c1 = N.to_nat c2) by (apply ND; simpl List.length; lia).
  lia.
Qed.

Lemma nc_uniq : forall c1 c2, (c1 < M)%N -> (c2 < M)%N ->
  entry yrs c1 = entry yrs c2 -> entry yrs c1 <> 2011%N -> c1 = c2.
Proof.
  intros c1 c2 H1 H2 E Hne. pose proof (vi_newcomers _ _ _ _ _ _ Hv) as ND.
  unfold entry in E, Hne. unfold len in H1, H2.
  assert (N.to_nat c1 = N.to_nat c2); [|lia].
  eapply nodup_filter_nth; [exact ND | lia | lia | exact E |].
  rewrite Bool.negb_true_iff, N.eqb_neq. exact Hne.
Qed.

Lemma year_ex : forall Z, (2011 <= Z <= 2010 + n)%N ->
  exists c, (c < M)%N /\ entry yrs c = Z.
Proof.
  intros Z HZ. destruct (N.eq_dec Z 2011) as [->|HZ2].
  - pose proof (vi_pool _ _ _ _ _ _ Hv) as Hp. pose proof (vi_k _ _ _ _ _ _ Hv).
    destruct (filter (N.eqb 2011) yrs) as [|x l] eqn:Ef; [unfold len in Hp; simpl in Hp; lia|].
    assert (Hx : In x (filter (N.eqb 2011) yrs)) by (rewrite Ef; left; reflexivity).
    rewrite filter_In, N.eqb_eq in Hx. destruct Hx as [Hx <-].
    exact (in_entry _ _ Hx).
  - set (Lf := filter (fun z => negb (z =? 2011)%N) yrs).
    assert (HLf : List.length Lf = (N.to_nat n - 1)%nat).
    { pose proof (filter_len_split (N.eqb 2011) yrs) as Hs.
      replace (filter (fun x => negb (N.eqb 2011 x)) yrs) with Lf in Hs
        by (apply filter_ext; intro a; rewrite N.eqb_sym; reflexivity).
      pose proof (vi_pool _ _ _ _ _ _ Hv) as Hp. pose proof M_val as HM.
      pose proof (vi_n _ _ _ _ _ _ Hv). pose proof (vi_k _ _ _ _ _ _ Hv).
      unfold len in Hp, HM. lia. }
    set (R := map (fun j => (2012 + N.of_nat j)%N) (seq 0 (N.to_nat n - 1))).
    assert (HR : List.length R = (N.to_nat n - 1)%nat)
      by (unfold R; rewrite length_map, length_seq; reflexivity).
    assert (Inc : incl Lf R).
    { intros x Hx. unfold Lf in Hx. rewrite filter_In, Bool.negb_true_iff, N.eqb_neq in Hx.
      destruct Hx as [Hx Hx2]. destruct (in_entry _ _ Hx) as [c [Hc Ec]].
      pose proof (yr_range c Hc). unfold R. rewrite in_map_iff.
      exists (N.to_nat (x - 2012)). rewrite in_seq. lia. }
    pose proof (@NoDup_length_incl _ Lf R (vi_newcomers _ _ _ _ _ _ Hv) ltac:(lia) Inc)
      as Inc2.
    assert (HZR : In Z R) by (unfold R; rewrite in_map_iff;
      exists (N.to_nat (Z - 2012)); rewrite in_seq; lia).
    specialize (Inc2 Z HZR). unfold Lf in Inc2. rewrite filter_In in Inc2.
    exact (in_entry _ _ (proj1 Inc2)).
Qed.

Definition ms : list N := map N.of_nat (seq 0 (N.to_nat M)).

Lemma in_ms : forall c, In c ms <-> (c < M)%N.
Proof.
  intros c. unfold ms. rewrite in_map_iff. split.
  - intros [j [<- Hj]]. rewrite in_seq in Hj. lia.
  - intros Hc. exists (N.to_nat c). rewrite in_seq. lia.
Qed.

Lemma nodup_ms : NoDup ms.
Proof.
  unfold ms. apply Injective_map_NoDup; [|apply seq_NoDup].
  intros a b E. lia.
Qed.

Lemma contender_W : forall w d c,
  contender yrs w (2011 + N.of_nat d) c <->
  (c < M)%N /\ (entry yrs c <= 2011 + N.of_nat d)%N /\ ~ In c (map w (yrsl d)).
Proof.
  intros w d c. unfold contender. split.
  - intros [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
    intros Hin. rewrite in_map_iff in Hin. destruct Hin as [Y' [E HY']].
    rewrite in_yrsl in HY'. exact (H3 Y' HY' E).
  - intros [H1 [H2 H3]]. split; [exact H1|]. split; [exact H2|].
    intros Y' HY' E. apply H3. rewrite in_map_iff. exists Y'. split; [exact E|].
    rewrite in_yrsl. exact HY'.
Qed.

Lemma some_contender : forall w d, (2011 + N.of_nat d <= 2010 + n)%N ->
  exists c, contender yrs w (2011 + N.of_nat d) c.
Proof.
  intros w d Hd.
  set (Y := (2011 + N.of_nat d)%N).
  set (L := filter (fun c => entry yrs c <=? Y)%N ms).
  assert (Hlen : (S d <= List.length L)%nat).
  { rewrite <- (len_yrsl (S d)), <- (length_map (entry yrs) L).
    apply NoDup_incl_length; [apply nodup_yrsl|].
    intros x Hx. rewrite in_yrsl in Hx.
    destruct (year_ex x ltac:(unfold Y in *; lia)) as [c [Hc Ec]].
    apply in_map_iff. exists c. split; [exact Ec|].
    apply filter_In. split; [apply in_ms; exact Hc | apply N.leb_le; unfold Y; lia]. }
  set (W := map w (yrsl d)).
  destruct (existsb (fun c => negb (existsb (N.eqb c) W)) L) eqn:Eb.
  - rewrite existsb_exists in Eb. destruct Eb as [c [Hc Hn]].
    exists c. apply contender_W. unfold L in Hc. rewrite filter_In, in_ms, N.leb_le in Hc.
    split; [tauto|]. split; [tauto|].
    intros Hin. assert (existsb (N.eqb c) W = true)
      by (apply existsb_exists; exists c; split; [exact Hin | apply N.eqb_refl]).
    rewrite H in Hn. discriminate.
  - exfalso.
    assert (Inc : incl L W).
    { intros c Hc. destruct (existsb (N.eqb c) W) eqn:E2.
      - rewrite existsb_exists in E2. destruct E2 as [x [Hx Ex]].
        rewrite N.eqb_eq in Ex. subst x. exact Hx.
      - assert (existsb (fun c => negb (existsb (N.eqb c) W)) L = true)
          by (apply existsb_exists; exists c; split; [exact Hc | rewrite E2; reflexivity]).
        congruence. }
    pose proof (@NoDup_incl_length _ _ _ (NoDup_filter _ nodup_ms) Inc) as Hl.
    unfold W in Hl. rewrite length_map, len_yrsl in Hl. fold L in Hl. lia.
Qed.

Lemma max_contender : forall w d, (2011 + N.of_nat d <= 2010 + n)%N ->
  exists x, contender yrs w (2011 + N.of_nat d) x /\
    forall c, contender yrs w (2011 + N.of_nat d) c -> (entry strs c <= entry strs x)%N.
Proof.
  intros w d Hd.
  set (W := map w (yrsl d)).
  set (C := filter (fun c => andb (entry yrs c <=? 2011 + N.of_nat d)%N
                             (negb (existsb (N.eqb c) W))) ms).
  assert (Cin : forall c, In c C <-> contender yrs w (2011 + N.of_nat d) c).
  { intros c. unfold C. rewrite filter_In, contender_W, in_ms, Bool.andb_true_iff,
      N.leb_le, Bool.negb_true_iff.
    assert (existsb (N.eqb c) W = false <-> ~ In c W).
    { split.
      - intros E Hin. assert (existsb (N.eqb c) W = true)
          by (apply existsb_exists; exists c; split; [exact Hin | apply N.eqb_refl]).
        congruence.
      - intros Hn. destruct (existsb (N.eqb c) W) eqn:E; [|reflexivity].
        exfalso. rewrite existsb_exists in E. destruct E as [x [Hx Ex]].
        rewrite N.eqb_eq in Ex. subst x. exact (Hn Hx). }
    fold W. tauto. }
  destruct (some_contender w d Hd) as [c0 Hc0].
  destruct (max_exists (entry strs) C) as [x [Hx Hm]].
  - intros E. apply Cin in Hc0. rewrite E in Hc0. destruct Hc0.
  - exists x. split; [apply Cin; exact Hx|]. intros c Hc. apply Hm. apply Cin. exact Hc.
Qed.

Lemma contender_ext : forall w w' Y c,
  (forall Y', (2011 <= Y' < Y)%N -> w Y' = w' Y') ->
  contender yrs w Y c <-> contender yrs w' Y c.
Proof.
  intros w w' Y c E. unfold contender. split; intros [A [B C]]; (split; [exact A|]);
    (split; [exact B|]); intros Y' HY'; [rewrite <- E | rewrite E]; auto.
Qed.

Definition sched_at (w : N -> N) (Y : N) : Prop :=
  contender yrs w Y (w Y) /\
  forall c, contender yrs w Y c -> (entry strs c <= entry strs (w Y))%N.

Lemma sched_upto : forall d, (N.of_nat d <= n)%N ->
  exists w, forall Y, (2011 <= Y < 2011 + N.of_nat d)%N -> sched_at w Y.
Proof.
  induction d as [|d IH]; intros Hd.
  - exists (fun _ => 0%N). intros Y HY. lia.
  - destruct (IH ltac:(lia)) as [w Hw].
    destruct (max_contender w d ltac:(lia)) as [x [Hx Hm]].
    set (w' := fun Z => if (Z =? 2011 + N.of_nat d)%N then x else w Z).
    assert (Eo : forall Z, Z <> (2011 + N.of_nat d)%N -> w' Z = w Z)
      by (intros Z HZ; unfold w'; rewrite (proj2 (N.eqb_neq _ _) HZ); reflexivity).
    assert (Ex : w' (2011 + N.of_nat d)%N = x) by (unfold w'; rewrite N.eqb_refl; reflexivity).
    exists w'. intros Y HY.
    assert (Ext : forall Y', (2011 <= Y' < Y)%N -> (Y < 2011 + N.of_nat (S d))%N ->
              w Y' = w' Y' /\ (Y' < 2011 + N.of_nat d)%N).
    { intros Y' HY' HY2. destruct (N.eq_dec Y' (2011 + N.of_nat d)).
      - lia.
      - rewrite Eo by assumption. split; [reflexivity | lia]. }
    unfold sched_at.
    destruct (N.eq_dec Y (2011 + N.of_nat d)) as [->|HY'].
    + rewrite Ex.
      assert (CE : forall c, contender yrs w (2011 + N.of_nat d) c <->
                             contender yrs w' (2011 + N.of_nat d) c)
        by (intros c; apply contender_ext; intros Y' HY'; apply (Ext Y' HY'); lia).
      split; [apply CE; exact Hx|]. intros c Hc. apply Hm. apply CE. exact Hc.
    + rewrite Eo by exact HY'.
      destruct (Hw Y ltac:(lia)) as [C1 M1].
      assert (CE : forall c, contender yrs w Y c <-> contender yrs w' Y c)
        by (intros c; apply contender_ext; intros Y' HY2; apply (Ext Y' HY2); lia).
      split; [apply CE; exact C1|]. intros c Hc. apply M1. apply CE. exact Hc.
Qed.

Lemma sched_exists : exists w, schedule n yrs strs w.
Proof.
  destruct (sched_upto (N.to_nat n) ltac:(lia)) as [w Hw].
  exists w. intros Y HY. unfold data_year in HY. apply Hw. lia.
Qed.

Lemma sched_uniq : forall w w', schedule n yrs strs w -> schedule n yrs strs w' ->
  forall Y, data_year n Y -> w Y = w' Y.
Proof.
  intros w w' Hw Hw'.
  assert (A : forall d Y, (2011 <= Y < 2011 + N.of_nat d)%N -> data_year n Y -> w Y = w' Y).
  { induction d as [|d IH]; intros Y HY HdY; [lia|].
    destruct (N.lt_ge_cases Y (2011 + N.of_nat d)); [apply IH; auto; lia|].
    assert (Ext : forall Y', (2011 <= Y' < Y)%N -> w Y' = w' Y').
    { intros Y' HY'. apply IH; [lia|]. unfold data_year in *. lia. }
    destruct (Hw Y HdY) as [C1 M1]. destruct (Hw' Y HdY) as [C2 M2].
    pose proof (M1 (w' Y) (proj2 (contender_ext w w' Y _ Ext) C2)).
    pose proof (M2 (w Y) (proj1 (contender_ext w w' Y _ Ext) C1)).
    apply str_inj; [exact (proj1 C1) | exact (proj1 C2) | lia]. }
  intros Y HY. apply (A (N.to_nat Y)); [unfold data_year in HY; lia | exact HY].
Qed.

(* ------------------------------------------------------------------ *)
(* The machine side                                                    *)
(* ------------------------------------------------------------------ *)

Lemma uint_val : forall (x : uint) (v : N), repr x v -> (φ x) = Z.of_N v.
Proof.
  intros x v H. cbv [repr repr_uint] in H. rewrite <- H.
  pose proof (to_Z_bounded x). rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma rget : forall (x : array@{Set} uint) (l : list N), repr x l ->
  forall i : int, (φ i) < Z.of_nat (List.length l) ->
  (φ (PArray.get@{Set} x i)) = Z.of_N (nth (Z.to_nat (φ i)) l 0%N).
Proof.
  intros x l [Hl Hc] i Hi.
  destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (m & Hm & Hr).
  cbv [repr repr_uint] in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded i); lia).
  rewrite of_to_Z in Hr.
  assert (Hn : nth (Z.to_nat (φ i)) l 0%N = m) by (apply nth_error_nth; exact Hm).
  rewrite Hn. rewrite <- Hr.
  pose proof (to_Z_bounded (x.[i])). rewrite Z2N.id by lia. reflexivity.
Qed.

Lemma rlen : forall (x : array@{Set} uint) (l : list N), repr x l ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma entry_succ : forall (a : N) (l : list N) (z : Z), 0 <= z ->
  entry (a :: l) (Z.to_N z + 1) = nth (Z.to_nat z) l 0%N.
Proof.
  intros a l z Hz. unfold entry.
  replace (N.to_nat (Z.to_N z + 1)) with (S (Z.to_nat z)) by lia. reflexivity.
Qed.

Variables (nx yx px : uint) (ysx psx : array uint).
Hypotheses (Rn : repr nx n) (Ry : repr yx y) (Rp : repr px p)
  (Rys : repr ysx ys) (Rps : repr psx ps).

Local Notation Sz c := (Z.of_N (entry (p :: ps) c)).
Local Notation Ez c := (Z.of_N (entry (y :: ys) c)).

Lemma bounds : (1 <= n <= 100000)%N /\ (1 <= k <= 100000)%N /\
  M = (n + k - 1)%N /\ Z.of_nat (List.length ys) = Z.of_N (n + k - 2).
Proof.
  pose proof (vi_n _ _ _ _ _ _ Hv). pose proof (vi_k _ _ _ _ _ _ Hv).
  pose proof (vi_ys_len _ _ _ _ _ _ Hv). pose proof M_val. unfold len in *.
  split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma M_len : Z.of_N M = Z.of_nat (List.length ys) + 1.
Proof. unfold len. simpl List.length. lia. Qed.

Definition FillInv (c : N) (st : array int * int * array int) : Prop :=
  let '(h, s, t) := st in
  (φ (PArray.length h)) = Z.of_N M /\ (φ (PArray.length t)) = Z.of_N n /\
  hp (rd h) (φ s) /\ (φ s) <= Z.of_N c /\ NoDup (cnt (rd h) (φ s)) /\
  (forall v, In v (cnt (rd h) (φ s)) <->
     exists c', (c' < c)%N /\ entry yrs c' = 2011%N /\ Sz c' = v) /\
  (forall c', (c' < c)%N -> entry yrs c' <> 2011%N -> rd t (Ez c' - 2011) = Sz c').

Lemma step_inv : forall c st (yr sv : int), FillInv c st -> (c < M)%N ->
  (φ yr) = Ez c -> (φ sv) = Sz c -> FillInv (c + 1) (step st yr sv).
Proof.
  intros c [[h s] t] yr sv Hi Hc Hyr Hsv.
  destruct Hi as (Lh & Lt & Hh & Hs & ND & Mem & Tb).
  pose proof (yr_range c Hc) as Rc. pose proof (str_range c Hc) as Sc.
  destruct bounds as (Bn & Bk & BM & Bys).
  pose proof (to_Z_bounded s) as Bs.
  unfold step.
  destruct (yr =? 2011)%uint63 eqn:Ey.
  - rewrite eqb_spec in Ey. subst yr. change (φ 2011) with 2011 in Hyr.
    assert (Ec : entry yrs c = 2011%N) by lia.
    destruct (insert_spec h s sv ltac:(lia) Hh) as (L & P & Q).
    assert (Hs1 : (φ (s + 1)) = (φ s) + 1) by sia.
    cbv beta iota zeta delta [FillInv]. rewrite Hs1.
    split; [rewrite L; exact Lh|]. split; [exact Lt|]. split; [exact P|].
    split; [lia|]. split.
    + apply (Permutation_NoDup (Permutation_sym Q)). constructor; [|exact ND].
      intros Hin. apply Mem in Hin. destruct Hin as (c' & Hc' & Ec' & Sc').
      assert (c' = c) by (apply str_inj; lia). lia.
    + split.
      * intros v. split.
        -- intros Hin. apply (Permutation_in _ Q) in Hin. destruct Hin as [<-|Hin].
           ++ exists c. split; [lia|]. split; [exact Ec | lia].
           ++ apply Mem in Hin. destruct Hin as (c' & Hc' & Ec' & Sc').
              exists c'. split; [lia|]. split; assumption.
        -- intros (c' & Hc' & Ec' & Sc'). apply (Permutation_in _ (Permutation_sym Q)).
           destruct (N.eq_dec c' c) as [->|Hne]; [left; lia|].
           right. apply Mem. exists c'. split; [lia|]. split; assumption.
      * intros c' Hc' Ec'. apply Tb; [|exact Ec'].
        destruct (N.eq_dec c' c) as [->|Hne]; [contradiction | lia].
  - rewrite eqb_false_spec in Ey.
    assert (Ec : entry yrs c <> 2011%N).
    { intros E. apply Ey. apply to_Z_inj. rewrite Hyr. change (φ 2011) with 2011. lia. }
    assert (Hix : (φ (yr - 2011)) = Ez c - 2011) by (change (φ 2011) with 2011 in *; sia).
    cbv beta iota zeta delta [FillInv].
    split; [exact Lh|]. split; [rewrite alength_set; exact Lt|]. split; [exact Hh|].
    split; [lia|]. split; [exact ND|]. split.
    + intros v. rewrite Mem. split; intros (c' & Hc' & Ec' & Sc'); exists c';
        (split; [|split; assumption]); [lia|].
      destruct (N.eq_dec c' c) as [->|Hne]; [contradiction | lia].
    + intros c' Hc' Ec'.
      assert (Hc'M : (c' < M)%N) by lia. pose proof (yr_range c' Hc'M).
      rewrite rd_set; [| rewrite Hix, Lt; lia | rewrite wB_val; lia].
      unfold upd. destruct (Z.eqb_spec (Ez c' - 2011) (φ (yr - 2011))) as [E|E].
      * assert (c' = c) by (apply nc_uniq; [exact Hc'M | exact Hc | lia | exact Ec']).
        subst c'. lia.
      * apply Tb; [|exact Ec']. destruct (N.eq_dec c' c) as [->|Hne]; [lia | lia].
Qed.

Lemma fill_inv : forall z (i : int) st (H : Acc (Zwf 0) (gap (PArray.length ysx) i)),
  gap (PArray.length ysx) i = z -> (φ i) <= (φ (PArray.length ysx)) ->
  FillInv (Z.to_N (φ i) + 1) st ->
  FillInv M (fill ysx psx (PArray.length ysx) i st H).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i st H Hz Hi Hinv. rewrite fill_eq.
  pose proof (rlen _ _ Rys) as Ly. pose proof (rlen _ _ Rps) as Lp.
  pose proof len_ys_ps as Lyp.
  destruct bounds as (Bn & Bk & BM & Bys).
  pose proof (to_Z_bounded i) as Bi.
  destruct (bdec (i <? PArray.length ysx)%uint63) as [Hlt|Hge].
  - pose proof Hlt as Hlt'. rewrite ltb_spec in Hlt'.
    assert (Hi1 : (φ (i + 1)) = (φ i) + 1) by sia.
    eapply IH; [rewrite <- Hz; apply dec_step; exact Hlt | reflexivity | lia |].
    replace (Z.to_N (φ (i + 1)) + 1)%N with ((Z.to_N (φ i) + 1) + 1)%N by lia.
    pose proof M_len as HML.
    apply step_inv; [exact Hinv | lia | |].
    + rewrite entry_succ by lia. apply rget; [exact Rys | lia].
    + rewrite entry_succ by lia. apply rget; [exact Rps | lia].
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hge.
    pose proof M_len as HML.
    replace M with (Z.to_N (φ i) + 1)%N; [exact Hinv|]. lia.
Qed.

Definition SimInv (w : N -> N) (d : int) (h : array int) (s : int) (t : array int) : Prop :=
  (φ (PArray.length h)) = Z.of_N M /\ (φ (PArray.length t)) = Z.of_N n /\
  hp (rd h) (φ s) /\ (φ s) <= Z.of_N M /\ NoDup (cnt (rd h) (φ s)) /\
  (forall v, In v (cnt (rd h) (φ s)) <->
     exists c, contender yrs w (2011 + Z.to_N (φ d)) c /\ Sz c = v) /\
  (forall Y', (2011 <= Y' < 2011 + Z.to_N (φ d))%N -> w Y' <> 0%N) /\
  (forall c, (c < M)%N -> entry yrs c <> 2011%N -> rd t (Ez c - 2011) = Sz c).

Lemma sim_inv : forall w, schedule n yrs strs w ->
  forall z (d : int) h s t (H : Acc (Zwf 0) (gap nx d)),
  gap nx d = z -> (φ d) < (φ nx) -> SimInv w d h s t ->
  exists o, repr (sim t h nx px s d H : option uint) o /\
    (forall Y', o = Some Y' <-> data_year n Y' /\ w Y' = 0%N).
Proof.
  intros w Hw z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros d h s t H Hz Hd Hi.
  destruct Hi as (Lh & Lt & Hh & Hs & ND & Mem & Kn & Tb).
  pose proof (uint_val _ _ Rn) as En. pose proof (uint_val _ _ Rp) as Ep.
  destruct bounds as (Bn & Bk & BM & Bys).
  pose proof (to_Z_bounded d) as Bd. pose proof (to_Z_bounded s) as Bs.
  set (Y := (2011 + Z.to_N (φ d))%N) in *.
  assert (HdY : data_year n Y) by (unfold data_year, Y; lia).
  destruct (Hw Y HdY) as [Cw Mw].
  assert (Hin : In (Sz (w Y)) (cnt (rd h) (φ s)))
    by (apply Mem; exists (w Y); split; [exact Cw | reflexivity]).
  assert (Hs0 : 0 < (φ s))
    by (apply in_cnt in Hin; destruct Hin as [j [Hj _]]; lia).
  assert (Htop : (φ (h.[0])) = Sz (w Y)).
  { assert (I0 : In (rd h 0) (cnt (rd h) (φ s)))
      by (apply in_cnt; exists 0; split; [lia | reflexivity]).
    apply Mem in I0. destruct I0 as [c0 [C0 S0]].
    pose proof (Mw c0 C0) as M0.
    destruct (proj1 (in_cnt _ _ _) Hin) as [j [Hj Ej]].
    pose proof (hp_max _ _ Hh j Hj) as Mx.
    assert (c0 = w Y) by (apply str_inj; [exact (proj1 C0) | exact (proj1 Cw) | lia]).
    subst c0. change (φ (h.[0])) with (rd h 0). lia. }
  rewrite sim_eq.
  destruct (bdec (d <? nx)%uint63) as [Hd'|Hd'].
  2:{ exfalso. rewrite <- Bool.not_true_iff_false, ltb_spec in Hd'. lia. }
  assert (Es : (s =? 0)%uint63 = false)
    by (rewrite eqb_false_spec; intro E; rewrite E in Hs0; change (φ 0) with 0 in Hs0; lia).
  rewrite Es. cbv zeta.
  assert (Hd2 : (φ (2011 + d)) = 2011 + (φ d)) by (change (φ 2011) with 2011; sia).
  assert (Ep0 : (φ px) = Sz 0%N) by exact Ep.
  destruct (h.[0] =? px)%uint63 eqn:Et.
  - rewrite eqb_spec in Et.
    assert (HwY : w Y = 0%N).
    { apply str_inj; [exact (proj1 Cw) | unfold len; simpl List.length; lia |].
      rewrite Et in Htop. lia. }
    exists (Some Y). split.
    + cbv [repr repr_option repr_uint]. rewrite Hd2. unfold Y. lia.
    + intros Y'. split.
      * intros E. injection E as <-. split; [exact HdY | exact HwY].
      * intros [HdY' Hw0]. f_equal.
        destruct (N.lt_total Y' Y) as [Hlt|[Heq|Hgt]].
        -- exfalso. apply (Kn Y'); [unfold data_year, Y in *; lia | exact Hw0].
        -- symmetry. exact Heq.
        -- exfalso. destruct (Hw Y' HdY') as [[_ [_ C3]] _].
           apply (C3 Y); [unfold Y in *; lia | rewrite Hw0, HwY; reflexivity].
  - rewrite eqb_false_spec in Et.
    assert (HwY : w Y <> 0%N).
    { intros E. apply Et. apply to_Z_inj. rewrite Htop, Ep0, E. reflexivity. }
    destruct (d + 1 <? nx)%uint63 eqn:Ed.
    + rewrite ltb_spec in Ed.
      assert (Hd1 : (φ (d + 1)) = (φ d) + 1) by sia.
      destruct (extract_spec h s ltac:(lia) Hh) as (L1 & P1 & Q1).
      set (h1 := extract h s) in *.
      destruct (year_ex (Y + 1) ltac:(unfold Y; lia)) as [cn [Hcn Ecn]].
      assert (Ecn2 : entry yrs cn <> 2011%N) by (unfold Y in Ecn; lia).
      assert (Htn : (φ (t.[d + 1])) = Sz cn).
      { rewrite <- rd_int. rewrite <- (Tb cn Hcn Ecn2). f_equal.
        rewrite Ecn, Hd1. unfold Y. lia. }
      assert (Hs1 : (φ (s - 1)) = (φ s) - 1) by sia.
      destruct (insert_spec h1 (s - 1) t.[d + 1] ltac:(rewrite L1; lia)
                  ltac:(rewrite Hs1; exact P1)) as (L2 & P2 & Q2).
      rewrite Hs1 in P2, Q2. replace ((φ s) - 1 + 1) with (φ s) in P2, Q2 by lia.
      pose proof (Permutation_NoDup Q1 ND) as ND'.
      apply NoDup_cons_iff in ND'. destruct ND' as [Hn1 ND1].
      assert (Mem1 : forall v, In v (cnt (rd h1) ((φ s) - 1)) <->
                               In v (cnt (rd h) (φ s)) /\ v <> (φ (h.[0]))).
      { intros v. split.
        - intros Hq. split.
          + apply (Permutation_in _ (Permutation_sym Q1)). right. exact Hq.
          + intros ->. contradiction.
        - intros [Hq Hne]. apply (Permutation_in _ Q1) in Hq.
          destruct Hq as [E|Hq]; [congruence | exact Hq]. }
      eapply IH; [rewrite <- Hz; apply dec_step; exact Hd' | reflexivity | lia |].
      assert (EY1 : (2011 + Z.to_N (φ (d + 1)))%N = (Y + 1)%N)
        by (rewrite Hd1; unfold Y; lia).
      unfold SimInv. rewrite EY1.
      split; [rewrite L2, L1; exact Lh|]. split; [exact Lt|]. split; [exact P2|].
      split; [exact Hs|]. split.
      * apply (Permutation_NoDup (Permutation_sym Q2)). constructor; [|exact ND1].
        rewrite Htn. intros Hq. apply Mem1 in Hq. destruct Hq as [Hq _].
        apply Mem in Hq. destruct Hq as [c [Cc Sc]].
        assert (c = cn) by (apply str_inj; [exact (proj1 Cc) | exact Hcn | lia]).
        subst c. destruct Cc as [_ [Ec _]]. rewrite Ecn in Ec. lia.
      * split; [|split].
        -- intros v. split.
           ++ intros Hq. apply (Permutation_in _ Q2) in Hq. destruct Hq as [<-|Hq].
              ** exists cn. split; [|lia]. split; [exact Hcn|]. split; [lia|].
                 intros Y'' HY'' E.
                 assert (HdY'' : data_year n Y'') by (unfold data_year, Y in *; lia).
                 destruct (Hw Y'' HdY'') as [[_ [Ew _]] _]. rewrite E, Ecn in Ew. lia.
              ** apply Mem1 in Hq. destruct Hq as [Hq Hne]. apply Mem in Hq.
                 destruct Hq as [c [Cc Sc]]. exists c. split; [|exact Sc].
                 destruct Cc as [A [B C]]. split; [exact A|]. split; [lia|].
                 intros Y'' HY'' E. destruct (N.eq_dec Y'' Y) as [->|HY2].
                 --- apply Hne. rewrite <- Sc, Htop, E. reflexivity.
                 --- apply (C Y''); [lia | exact E].
           ++ intros [c [Cc Sc]]. apply (Permutation_in _ (Permutation_sym Q2)).
              destruct Cc as [A [B C]].
              destruct (N.eq_dec (entry yrs c) (Y + 1)) as [Ec|Ec].
              ** left. assert (c = cn)
                   by (apply nc_uniq; [exact A | exact Hcn | congruence | unfold Y in *; lia]).
                 subst c. lia.
              ** right. apply Mem1. split.
                 --- apply Mem. exists c. split; [|exact Sc]. split; [exact A|].
                     split; [lia|]. intros Y'' HY'' E. apply (C Y''); [lia | exact E].
                 --- intros E. assert (c = w Y)
                       by (apply str_inj; [exact A | exact (proj1 Cw) | lia]).
                     apply (C Y); [unfold Y; lia | symmetry; assumption].
        -- intros Y' HY'. destruct (N.eq_dec Y' Y) as [->|HY2];
             [exact HwY | apply Kn; unfold Y in *; lia].
        -- exact Tb.
    + rewrite <- Bool.not_true_iff_false, ltb_spec in Ed.
      assert (Hd1 : (φ (d + 1)) = (φ d) + 1) by sia.
      exists None. split; [exact I|]. intros Y'. split; [discriminate|].
      intros [HdY' Hw0]. unfold data_year in HdY'. exfalso.
      destruct (N.eq_dec Y' Y) as [->|HY2]; [exact (HwY Hw0)|].
      apply (Kn Y'); [unfold Y in *; lia | exact Hw0].
Qed.

Lemma impl_correct : forall kx : uint,
  exists o, repr (knigs_impl kx nx yx px ysx psx) o /\ knigsoftheforest_spec k n y p ys ps o.
Proof.
  intros kx.
  destruct sched_exists as [w Hw].
  destruct bounds as (Bn & Bk & BM & Bys).
  pose proof (rlen _ _ Rys) as Ly. pose proof (uint_val _ _ Rn) as En.
  pose proof (uint_val _ _ Ry) as Ey. pose proof (uint_val _ _ Rp) as Ep.
  unfold knigs_impl. cbv zeta.
  set (m := PArray.length ysx) in *.
  assert (Hm1 : (φ (m + 1)) = Z.of_N M) by (unfold len in *; simpl List.length in *; sia).
  assert (F0 : FillInv 0 (PArray.make (m + 1) 0%uint63, 0%uint63, PArray.make nx 0%uint63)).
  { cbv beta iota zeta delta [FillInv]. change (φ 0) with 0.
    split.
    { rewrite alength_make. replace (m + 1 <=? PArray.max_length)%uint63 with true;
        [exact Hm1|]. symmetry. rewrite leb_spec, max_length_val. lia. }
    split.
    { rewrite alength_make. replace (nx <=? PArray.max_length)%uint63 with true;
        [exact En|]. symmetry. rewrite leb_spec, max_length_val. lia. }
    split; [intros j Hj; lia|]. split; [lia|]. split; [constructor|].
    split; [|intros c' Hc'; lia].
    intros v. split; [intros []| intros (c' & Hc' & _); lia]. }
  assert (F1 := step_inv 0 _ yx px F0 ltac:(unfold len; simpl List.length; lia) Ey Ep).
  assert (F2 := fill_inv _ 0 _ (Zwf_well_founded 0 (gap m 0)) eq_refl
                  ltac:(change (φ 0) with 0; pose proof (to_Z_bounded m); lia) F1).
  fold m in F2. revert F2.
  destruct (fill ysx psx m 0 (step (PArray.make (m + 1) 0%uint63, 0%uint63, PArray.make nx 0%uint63) yx px)
              (Zwf_well_founded 0 (gap m 0))) as [[h s] t].
  intros F2. cbv beta iota zeta delta [FillInv] in F2. destruct F2 as (Lh & Lt & Hh & Hs & ND & Mem & Tb).
  assert (SI : SimInv w 0 h s t).
  { unfold SimInv. change (φ 0) with 0. change (Z.to_N 0) with 0%N.
    rewrite N.add_0_r.
    split; [exact Lh|]. split; [exact Lt|]. split; [exact Hh|]. split; [exact Hs|].
    split; [exact ND|]. split; [|split; [intros Y' HY'; lia | exact Tb]].
    intros v. rewrite Mem. split.
    - intros (c & Hc & Ec & Sc). exists c. split; [|exact Sc].
      split; [exact Hc|]. split; [lia|]. intros Y' HY'. lia.
    - intros (c & [A [B _]] & Sc). exists c. split; [exact A|]. split; [|exact Sc].
      pose proof (yr_range c A). lia. }
  destruct (sim_inv w Hw _ 0 h s t (Zwf_well_founded 0 (gap nx 0)) eq_refl
              ltac:(change (φ 0) with 0; lia) SI) as [o [Ro Io]].
  exists o. split; [exact Ro|]. split; [exists w; exact Hw|].
  intros w' Hw' Y. rewrite Io. pose proof (sched_uniq w w' Hw Hw') as U.
  split; intros [D E]; split; auto; [rewrite <- (U Y D) | rewrite (U Y D)]; exact E.
Qed.

End Problem.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition knigsoftheforest :
  uint -> uint -> uint -> uint -> array uint -> array uint -> option uint := knigs_impl.

Lemma knigsoftheforest_correct :
  forall (k n y p : N) (ys ps : list N)
         (kx nx yx px : uint) (ysx psx : array uint),
  valid_input k n y p ys ps ->
  repr kx k -> repr nx n -> repr yx y -> repr px p ->
  repr ysx ys -> repr psx ps ->
  exists o : option N,
    repr (knigsoftheforest kx nx yx px ysx psx) o /\
    knigsoftheforest_spec k n y p ys ps o.
Proof.
  intros k n y p ys ps kx nx yx px ysx psx Hv _ Rn Ry Rp Rys Rps.
  exact (impl_correct k n y p ys ps Hv nx yx px ysx psx Rn Ry Rp Rys Rps kx).
Qed.
