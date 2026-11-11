(* Implementation of excavatorexpedition (excavatorexpedition.spec):
   longest vertex-weighted path from 0 to V-1 in a DAG (CLRS
   DAG-SHORTEST-PATHS in its longest-path form), Kahn's topological order
   fused with the relaxation sweep.

   Code.  The adjacency is built once as compressed rows by a counting
   sort (cnt_loop: out-degrees, pre_loop: prefix sums, rfill_loop: fill
   from the last edge down, which leaves off.[u] = start of row u,
   off.[V] = E).  ind_loop counts in-degrees from the target array,
   q0_loop enqueues every location of in-degree 0.  kahn_loop pops q.[h]
   = u and relax_loop walks its row: dist.[v] := max(dist.[v], dist.[u] +
   weight v) when dist.[u] is a distance (NEG = -2^62 marks "unreached"),
   decrements the in-degree of v and enqueues v when it reaches 0.  All
   tables are flat `array int`, threaded linearly; no Z, no nat, no list.

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof,
   on the measure wB - i for an index i counting up (kahn_loop included,
   whose bound t moves) or on φ k for the fill counting down.

   Proof.  The rows are characterised by counting (lo u = number of edges
   whose source is below u).  Kahn's loop keeps: the queue holds distinct
   locations, x is enqueued iff its in-degree counter is 0, the counter of
   x is the number of unprocessed edges into x, every distance is NEG or
   the weight of some walk from 0, and every popped location has its row
   relaxed.  At the end, acyclicity (through a pigeonhole on walks) shows
   that every location was popped. *)

From Excavatorexpedition.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import String Ascii Relations.
From Stdlib Require Sint63 PrimString.
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

(* An index counting up below some bound: wB - i decreases. *)
Definition mes (i : int) : Z := (wB - (φ i))%Z.

Lemma mes_dec : forall i m : int, (i <? m) = true -> Zwf 0 (mes (i + 1)) (mes i).
Proof.
  intros i m H. rewrite ltb_spec in H. pose proof (to_Z_bounded m).
  assert (H1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
  unfold Zwf, mes. lia.
Qed.

(* An index counting down to 0. *)
Lemma down_dec : forall k : int, (0 <? k) = true -> Zwf 0 (φ (k - 1)) (φ k).
Proof.
  intros k H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* "unreached": -2^62 read through Sint63 *)
Definition NEG : int := 4611686018427387904.
(* -1 read through Sint63 *)
Definition MONE : int := 9223372036854775807.

(* The weight of location v: +1 for 'X' (88), -1 for '.' (46), 0 at the
   two homes. *)
Definition wt (xs : PrimString.string) (V v : int) : int :=
  if v =? 0 then 0 else if v =? V - 1 then 0 else
  let c := PrimString.get xs v in
  if c =? 88 then 1 else if c =? 46 then MONE else 0.

(* c.[src k] += 1 for k in [k, E). *)
Fixpoint cnt_loop (xsrc : array int) (E k : int) (c : array int)
    (H : Acc (Zwf 0) (mes k)) {struct H} : array int :=
  match bdec (k <? E) with
  | left Hk =>
      let u := xsrc.[k] in
      cnt_loop xsrc E (k + 1) c.[u <- c.[u] + 1] (Acc_inv H (mes_dec k E Hk))
  | right _ => c
  end.

(* Prefix sums: c.[i+1] += c.[i] for i in [i, V). *)
Fixpoint pre_loop (V i : int) (c : array int)
    (H : Acc (Zwf 0) (mes i)) {struct H} : array int :=
  match bdec (i <? V) with
  | left Hi =>
      pre_loop V (i + 1) c.[i + 1 <- c.[i + 1] + c.[i]] (Acc_inv H (mes_dec i V Hi))
  | right _ => c
  end.

(* Counting-sort fill, edges k-1, k-2, ..., 0: the offsets c move down to
   the start of each row. *)
Fixpoint rfill_loop (xsrc xdst : array int) (k : int) (c adj : array int)
    (H : Acc (Zwf 0) (φ k)) {struct H} : array int * array int :=
  match bdec (0 <? k) with
  | left Hk =>
      let k1 := k - 1 in
      let u := xsrc.[k1] in
      let p := c.[u] - 1 in
      rfill_loop xsrc xdst k1 c.[u <- p] adj.[p <- xdst.[k1]] (Acc_inv H (down_dec k Hk))
  | right _ => (c, adj)
  end.

(* In-degrees, read off the target array. *)
Fixpoint ind_loop (adj : array int) (E j : int) (d : array int)
    (H : Acc (Zwf 0) (mes j)) {struct H} : array int :=
  match bdec (j <? E) with
  | left Hj =>
      let v := adj.[j] in
      ind_loop adj E (j + 1) d.[v <- d.[v] + 1] (Acc_inv H (mes_dec j E Hj))
  | right _ => d
  end.

(* The initial queue: every location of in-degree 0. *)
Fixpoint q0_loop (V x : int) (d q : array int) (t : int)
    (H : Acc (Zwf 0) (mes x)) {struct H} : array int * int :=
  match bdec (x <? V) with
  | left Hx =>
      if d.[x] =? 0
      then q0_loop V (x + 1) d q.[t <- x] (t + 1) (Acc_inv H (mes_dec x V Hx))
      else q0_loop V (x + 1) d q t (Acc_inv H (mes_dec x V Hx))
  | right _ => (q, t)
  end.

(* One relaxation: dist.[v] := max(dist.[v], du + weight v), when du is a
   distance. *)
Definition relax1 (xs : PrimString.string) (V du v : int) (dist : array int) : array int :=
  if du =? NEG then dist
  else let cand := du + wt xs V v in
       if Sint63.ltb dist.[v] cand then dist.[v <- cand] else dist.

(* The row [j, hi) of the popped location u (du = dist.[u]): relax every
   edge u -> v, decrement the in-degree of v, enqueue v when it hits 0. *)
Fixpoint relax_loop (xs : PrimString.string) (V : int) (adj : array int)
    (du hi j : int) (d dist q : array int) (t : int)
    (H : Acc (Zwf 0) (mes j)) {struct H}
    : array int * array int * array int * int :=
  match bdec (j <? hi) with
  | left Hj =>
      let v := adj.[j] in
      let dist' := relax1 xs V du v dist in
      let e := d.[v] - 1 in
      if e =? 0 then
        relax_loop xs V adj du hi (j + 1) d.[v <- e] dist' q.[t <- v] (t + 1)
          (Acc_inv H (mes_dec j hi Hj))
      else
        relax_loop xs V adj du hi (j + 1) d.[v <- e] dist' q t
          (Acc_inv H (mes_dec j hi Hj))
  | right _ => (d, dist, q, t)
  end.

(* Kahn's queue, q.[h .. t) pending; the distances of a popped location
   are final. *)
Fixpoint kahn_loop (xs : PrimString.string) (V : int) (off adj : array int)
    (h : int) (d dist q : array int) (t : int)
    (H : Acc (Zwf 0) (mes h)) {struct H} : array int :=
  match bdec (h <? t) with
  | left Hh =>
      let u := q.[h] in
      let lo := off.[u] in
      match relax_loop xs V adj dist.[u] off.[u + 1] lo d dist q t
              (Zwf_well_founded 0 (mes lo)) with
      | (d', dist', q', t') =>
          kahn_loop xs V off adj (h + 1) d' dist' q' t' (Acc_inv H (mes_dec h t Hh))
      end
  | right _ => dist
  end.

Definition excavator_impl (xs : PrimString.string) (xsrc xdst : array int) : int :=
  let V := PrimString.length xs in
  let E := PArray.length xsrc in
  let c := cnt_loop xsrc E 0 (PArray.make (V + 1) 0) (Zwf_well_founded 0 (mes 0)) in
  let c := pre_loop V 0 c (Zwf_well_founded 0 (mes 0)) in
  match rfill_loop xsrc xdst E c (PArray.make E 0) (Zwf_well_founded 0 (φ E)) with
  | (off, adj) =>
      let d := ind_loop adj E 0 (PArray.make V 0) (Zwf_well_founded 0 (mes 0)) in
      match q0_loop V 0 d (PArray.make V 0) 0 (Zwf_well_founded 0 (mes 0)) with
      | (q, t) =>
          let dist := (PArray.make V NEG).[0 <- 0] in
          let dist := kahn_loop xs V off adj 0 d dist q t (Zwf_well_founded 0 (mes 0)) in
          dist.[V - 1]
      end
  end.

(* ------------------------------------------------------------------ *)
(* Unfolding equations                                                 *)
(* ------------------------------------------------------------------ *)

Lemma cnt_loop_eq : forall xsrc E k c H, cnt_loop xsrc E k c H =
  match bdec (k <? E) with
  | left Hk =>
      let u := xsrc.[k] in
      cnt_loop xsrc E (k + 1) c.[u <- c.[u] + 1] (Acc_inv H (mes_dec k E Hk))
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma pre_loop_eq : forall V i c H, pre_loop V i c H =
  match bdec (i <? V) with
  | left Hi =>
      pre_loop V (i + 1) c.[i + 1 <- c.[i + 1] + c.[i]] (Acc_inv H (mes_dec i V Hi))
  | right _ => c
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma rfill_loop_eq : forall xsrc xdst k c adj H, rfill_loop xsrc xdst k c adj H =
  match bdec (0 <? k) with
  | left Hk =>
      let k1 := k - 1 in
      let u := xsrc.[k1] in
      let p := c.[u] - 1 in
      rfill_loop xsrc xdst k1 c.[u <- p] adj.[p <- xdst.[k1]] (Acc_inv H (down_dec k Hk))
  | right _ => (c, adj)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma ind_loop_eq : forall adj E j d H, ind_loop adj E j d H =
  match bdec (j <? E) with
  | left Hj =>
      let v := adj.[j] in
      ind_loop adj E (j + 1) d.[v <- d.[v] + 1] (Acc_inv H (mes_dec j E Hj))
  | right _ => d
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma q0_loop_eq : forall V x d q t H, q0_loop V x d q t H =
  match bdec (x <? V) with
  | left Hx =>
      if d.[x] =? 0
      then q0_loop V (x + 1) d q.[t <- x] (t + 1) (Acc_inv H (mes_dec x V Hx))
      else q0_loop V (x + 1) d q t (Acc_inv H (mes_dec x V Hx))
  | right _ => (q, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma relax_loop_eq : forall xs V adj du hi j d dist q t H,
  relax_loop xs V adj du hi j d dist q t H =
  match bdec (j <? hi) with
  | left Hj =>
      let v := adj.[j] in
      let dist' := relax1 xs V du v dist in
      let e := d.[v] - 1 in
      if e =? 0 then
        relax_loop xs V adj du hi (j + 1) d.[v <- e] dist' q.[t <- v] (t + 1)
          (Acc_inv H (mes_dec j hi Hj))
      else
        relax_loop xs V adj du hi (j + 1) d.[v <- e] dist' q t
          (Acc_inv H (mes_dec j hi Hj))
  | right _ => (d, dist, q, t)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma kahn_loop_eq : forall xs V off adj h d dist q t H,
  kahn_loop xs V off adj h d dist q t H =
  match bdec (h <? t) with
  | left Hh =>
      let u := q.[h] in
      let lo := off.[u] in
      match relax_loop xs V adj dist.[u] off.[u + 1] lo d dist q t
              (Zwf_well_founded 0 (mes lo)) with
      | (d', dist', q', t') =>
          kahn_loop xs V off adj (h + 1) d' dist' q' t' (Acc_inv H (mes_dec h t Hh))
      end
  | right _ => dist
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Uint63 / Sint63 / PArray plumbing                                   *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z -> t.[i <- b].[i] = b.
Proof.
  intros t i b H. assert (H' : (i <? PArray.length t) = true) by (rewrite ltb_spec; exact H).
  exact (get_set_same int t i b H').
Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma aget_set : forall (t : array int) (i j : int) (b : int),
  ((φ i) < (φ (PArray.length t)))%Z ->
  t.[i <- b].[j] = if ((φ i) =? (φ j))%Z then b else t.[j].
Proof.
  intros t i j b H. destruct (Z.eqb_spec (φ i) (φ j)) as [E | E].
  - apply to_Z_inj in E. subst j. apply aget_set_same. exact H.
  - apply aget_set_other. intro F. subst. apply E. reflexivity.
Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros. exact (get_make int b n i). Qed.

Lemma alength_make_small : forall (n : int) (b : int),
  ((φ n) <= 4194303)%Z -> PArray.length (PArray.make n b) = n.
Proof.
  intros n b H.
  assert (L : PArray.length (PArray.make n b)
              = if n <=? PArray.max_length then n else PArray.max_length)
    by exact (length_make int n b).
  assert (E : (n <=? PArray.max_length) = true) by (rewrite leb_spec, max_length_val; exact H).
  rewrite E in L. exact L.
Qed.

Lemma sint_val : forall x : int,
  Sint63.to_Z x = if ((φ x) <? 4611686018427387904)%Z then (φ x) else ((φ x) - wB)%Z.
Proof.
  intros x. rewrite Sint63.to_Z_cmodwB. unfold Sint63.cmod.
  pose proof (to_Z_bounded x). rewrite wB_val in *.
  destruct (Z.ltb_spec (φ x) 4611686018427387904); Z.to_euclidean_division_equations; lia.
Qed.

Lemma sint_small : forall x : int, ((φ x) < 4611686018427387904)%Z -> Sint63.to_Z x = (φ x).
Proof.
  intros x H. rewrite sint_val. destruct (Z.ltb_spec (φ x) 4611686018427387904); lia.
Qed.

Lemma sint_add : forall a b : int,
  (- 4611686018427387904 <= Sint63.to_Z a + Sint63.to_Z b < 4611686018427387904)%Z ->
  Sint63.to_Z (a + b) = (Sint63.to_Z a + Sint63.to_Z b)%Z.
Proof.
  intros a b H. rewrite Sint63.add_spec. apply Sint63.cmod_small.
  rewrite wB_val. change (9223372036854775808 / 2)%Z with 4611686018427387904%Z. lia.
Qed.

Lemma sint_ltb : forall a b : int,
  Sint63.ltb a b = (Sint63.to_Z a <? Sint63.to_Z b)%Z.
Proof.
  intros a b. destruct (Sint63.ltbP a b); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma NEG_val : Sint63.to_Z NEG = (-4611686018427387904)%Z.
Proof. reflexivity. Qed.

Lemma sint_eq : forall a b : int, Sint63.to_Z a = Sint63.to_Z b -> a = b.
Proof.
  intros a b H. apply to_Z_inj. rewrite <- (Sint63.to_Z_mod_Uint63to_Z a),
    <- (Sint63.to_Z_mod_Uint63to_Z b), H. reflexivity.
Qed.

Lemma of_Z_small : forall z, (0 <= z <= 4611686018427387904)%Z -> (φ (of_Z z)) = z.
Proof. intros z H. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val. lia. Qed.

Lemma owner_gen : forall (f : Z -> Z) (z : Z) (n : nat),
  (f 0 <= z)%Z -> (z < f (Z.of_nat n))%Z ->
  exists m, (m < n)%nat /\ (f (Z.of_nat m) <= z < f (Z.of_nat m + 1))%Z.
Proof.
  intros f z n H0. induction n as [|n IH]; intros Hn; [simpl in Hn; lia|].
  destruct (Z.lt_ge_cases z (f (Z.of_nat n))) as [L | L].
  - destruct (IH L) as (m & Hm & Hf). exists m. split; [lia | exact Hf].
  - exists n. split; [lia|]. replace (Z.of_nat n + 1)%Z with (Z.of_nat (S n)) by lia. lia.
Qed.

Lemma idec : forall a b : int, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (Z.eq_dec (φ a) (φ b)) as [E | E].
  - left. apply to_Z_inj. exact E.
  - right. intro F. apply E. rewrite F. reflexivity.
Qed.

Lemma succ_small : forall i : int, ((φ i) <= 400000)%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i H. pose proof (to_Z_bounded i). sia. Qed.

Lemma succ_lt : forall i m : int, ((φ i) < (φ m))%Z -> (φ (i + 1)) = ((φ i) + 1)%Z.
Proof. intros i m H. pose proof (to_Z_bounded m). pose proof (to_Z_bounded i). sia. Qed.

Lemma sub1 : forall a : int, (1 <= (φ a))%Z -> (φ (a - 1)) = ((φ a) - 1)%Z.
Proof. intros a H. pose proof (to_Z_bounded a). sia. Qed.

Lemma to_nat_succ : forall k : int, ((φ (k + 1)) = (φ k) + 1)%Z ->
  Z.to_nat (φ (k + 1)) = S (Z.to_nat (φ k)).
Proof. intros k H. rewrite H. pose proof (to_Z_bounded k). lia. Qed.

(* ------------------------------------------------------------------ *)
(* Counting (Prop side)                                                *)
(* ------------------------------------------------------------------ *)

(* The number of z in [0, n) with f z. *)
Fixpoint cnt (f : Z -> bool) (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S m => (cnt f m + (if f (Z.of_nat m) then 1 else 0))%Z
  end.

Lemma cnt_ext : forall f g n,
  (forall z, (0 <= z < Z.of_nat n)%Z -> f z = g z) -> cnt f n = cnt g n.
Proof.
  intros f g n. induction n as [|n IH]; intros Hfg; simpl; [reflexivity|].
  rewrite IH by (intros z Hz; apply Hfg; lia). rewrite Hfg by lia. reflexivity.
Qed.

Lemma cnt_bounds : forall f n, (0 <= cnt f n <= Z.of_nat n)%Z.
Proof.
  intros f n. induction n as [|n IH]; simpl; [lia|]. destruct (f (Z.of_nat n)); lia.
Qed.

Lemma cnt_le : forall f g n,
  (forall z, (0 <= z < Z.of_nat n)%Z -> f z = true -> g z = true) ->
  (cnt f n <= cnt g n)%Z.
Proof.
  intros f g n. induction n as [|n IH]; intros Hfg; simpl; [lia|].
  pose proof (IH ltac:(intros z Hz; apply Hfg; lia)).
  specialize (Hfg (Z.of_nat n) ltac:(lia)).
  destruct (f (Z.of_nat n)), (g (Z.of_nat n)); try lia; try discriminate (Hfg eq_refl).
Qed.

Lemma cnt_all : forall f n,
  (forall z, (0 <= z < Z.of_nat n)%Z -> f z = true) -> cnt f n = Z.of_nat n.
Proof.
  intros f n. induction n as [|n IH]; intros Hf; simpl; [reflexivity|].
  rewrite IH by (intros z Hz; apply Hf; lia). rewrite Hf by lia. lia.
Qed.

Lemma cnt_none : forall f n,
  (forall z, (0 <= z < Z.of_nat n)%Z -> f z = false) -> cnt f n = 0%Z.
Proof.
  intros f n. induction n as [|n IH]; intros Hf; simpl; [reflexivity|].
  rewrite IH by (intros z Hz; apply Hf; lia). rewrite Hf by lia. lia.
Qed.

Lemma cnt_plus : forall f g n,
  (forall z, (0 <= z < Z.of_nat n)%Z -> f z = true -> g z = false) ->
  cnt (fun z => (f z || g z)%bool) n = (cnt f n + cnt g n)%Z.
Proof.
  intros f g n. induction n as [|n IH]; intros Hfg; simpl; [reflexivity|].
  rewrite IH by (intros z Hz; apply Hfg; lia).
  specialize (Hfg (Z.of_nat n) ltac:(lia)).
  destruct (f (Z.of_nat n)), (g (Z.of_nat n)); simpl; try lia;
    try discriminate (Hfg eq_refl).
Qed.

Lemma cnt_pos : forall f n, (0 < cnt f n)%Z ->
  exists z, (0 <= z < Z.of_nat n)%Z /\ f z = true.
Proof.
  intros f n. induction n as [|n IH]; intros H; simpl in H; [lia|].
  destruct (f (Z.of_nat n)) eqn:E.
  - exists (Z.of_nat n). split; [lia | exact E].
  - destruct (IH ltac:(lia)) as (z & Hz & Hf). exists z. split; [lia | exact Hf].
Qed.

Lemma cnt_upd : forall f g n z0,
  (0 <= z0 < Z.of_nat n)%Z -> g z0 = false ->
  (forall z, (0 <= z < Z.of_nat n)%Z -> z <> z0 -> f z = g z) ->
  cnt g n = (cnt f n - (if f z0 then 1 else 0))%Z.
Proof.
  intros f g n z0. induction n as [|n IH]; intros Hz0 Hg Hfg; simpl; [lia|].
  destruct (Z.eq_dec z0 (Z.of_nat n)) as [E | E].
  - subst z0. rewrite Hg.
    rewrite (cnt_ext f g n) by (intros z Hz; apply Hfg; lia).
    destruct (f (Z.of_nat n)); lia.
  - rewrite (IH ltac:(lia) Hg) by (intros z Hz Hne; apply Hfg; lia).
    rewrite (Hfg (Z.of_nat n) ltac:(lia) ltac:(intro F; apply E; symmetry; exact F)). lia.
Qed.

Lemma cnt_mono_n : forall f m n, (m <= n)%nat -> (cnt f m <= cnt f n)%Z.
Proof.
  intros f m n H. induction H as [|n H IH]; [lia|]. simpl.
  destruct (f (Z.of_nat n)); lia.
Qed.

Lemma cnt_succZ : forall f n, (0 <= n)%Z ->
  cnt f (Z.to_nat (n + 1)) = (cnt f (Z.to_nat n) + (if f n then 1 else 0))%Z.
Proof.
  intros f n Hn. replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  simpl. rewrite Z2Nat.id by lia. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The compressed rows                                                 *)
(* ------------------------------------------------------------------ *)

(* cell z of an array, as a Z *)
Definition sv (a : array int) (z : Z) : Z := (φ (a.[of_Z z])).

Lemma sv_int : forall a k, sv a (φ k) = (φ (a.[k])).
Proof. intros. unfold sv. rewrite of_to_Z. reflexivity. Qed.

(* the number of edges among the first n whose source is u *)
Definition cntu (a : array int) (n u : Z) : Z := cnt (fun z => (sv a z =? u)%Z) (Z.to_nat n).
(* the number of edges among the first n whose source is below u *)
Definition lo (a : array int) (n u : Z) : Z := cnt (fun z => (sv a z <? u)%Z) (Z.to_nat n).

Lemma ltb_ge_int : forall a b : int, (a <? b) = false -> ((φ b) <= (φ a))%Z.
Proof. intros a b H. rewrite <- Bool.not_true_iff_false, ltb_spec in H. lia. Qed.

Section Csr.

Variables (xsrc xdst : array int) (V E : int).
Hypothesis HlenS : PArray.length xsrc = E.
Hypothesis HlenD : PArray.length xdst = E.
Hypothesis HV : (2 <= (φ V) <= 400000)%Z.
Hypothesis HE : ((φ E) <= 400000)%Z.
Hypothesis Hsrc : forall k, ((φ k) < (φ E))%Z -> ((φ (xsrc.[k])) < (φ V))%Z.

Lemma sv_src : forall z, (0 <= z < (φ E))%Z -> (0 <= sv xsrc z < (φ V))%Z.
Proof.
  intros z Hz. unfold sv. pose proof (to_Z_bounded (xsrc.[of_Z z])).
  split; [lia|]. apply Hsrc. rewrite of_Z_spec, Z.mod_small; rewrite ?wB_val; lia.
Qed.

Lemma lo_mono : forall a b, (a <= b)%Z -> (lo xsrc (φ E) a <= lo xsrc (φ E) b)%Z.
Proof. intros a b H. apply cnt_le. intros z _ Hz. rewrite Z.ltb_lt in *. lia. Qed.

Lemma lo_succ : forall u, lo xsrc (φ E) (u + 1) = (lo xsrc (φ E) u + cntu xsrc (φ E) u)%Z.
Proof.
  intros u. unfold lo, cntu. rewrite <- cnt_plus.
  - apply cnt_ext. intros z _. destruct (Z.ltb_spec (sv xsrc z) (u + 1)),
      (Z.ltb_spec (sv xsrc z) u), (Z.eqb_spec (sv xsrc z) u); simpl; lia.
  - intros z _ H. rewrite Z.ltb_lt in H. apply Z.eqb_neq. lia.
Qed.

Lemma lo_0 : lo xsrc (φ E) 0 = 0%Z.
Proof.
  apply cnt_none. intros z Hz. pose proof (sv_src z ltac:(lia)). apply Z.ltb_ge. lia.
Qed.

Lemma lo_V : forall u, ((φ V) <= u)%Z -> lo xsrc (φ E) u = (φ E).
Proof.
  intros u Hu. unfold lo. rewrite cnt_all; [pose proof (to_Z_bounded E); lia|].
  intros z Hz. pose proof (sv_src z ltac:(lia)). apply Z.ltb_lt. lia.
Qed.

Lemma cntu_V : forall n u, (0 <= n <= (φ E))%Z -> ((φ V) <= u)%Z -> cntu xsrc n u = 0%Z.
Proof.
  intros n u Hn Hu. apply cnt_none. intros z Hz.
  pose proof (sv_src z ltac:(lia)). apply Z.eqb_neq. lia.
Qed.

Lemma cntu_le : forall n u, (0 <= n <= (φ E))%Z -> (cntu xsrc n u <= cntu xsrc (φ E) u)%Z.
Proof. intros n u Hn. apply cnt_mono_n. lia. Qed.

Lemma lo_disj : forall u u' a b, (0 <= u)%Z -> (0 <= u')%Z -> u <> u' ->
  (lo xsrc (φ E) u <= a < lo xsrc (φ E) (u + 1))%Z ->
  (lo xsrc (φ E) u' <= b < lo xsrc (φ E) (u' + 1))%Z -> a <> b.
Proof.
  intros u u' a b Hu Hu' Hne Ha Hb.
  destruct (Z.lt_ge_cases u u') as [L | L].
  - pose proof (lo_mono (u + 1) u' ltac:(lia)). lia.
  - pose proof (lo_mono (u' + 1) u ltac:(lia)). lia.
Qed.

(* counting the sources *)
Lemma cnt_loop_spec : forall z k c H, mes k = z ->
  ((φ k) <= (φ E))%Z ->
  (φ (PArray.length c)) = ((φ V) + 1)%Z ->
  (forall i, ((φ i) <= (φ V))%Z -> (φ (c.[i])) = cntu xsrc (φ k) (φ i)) ->
  (φ (PArray.length (cnt_loop xsrc E k c H))) = ((φ V) + 1)%Z /\
  forall i, ((φ i) <= (φ V))%Z -> (φ ((cnt_loop xsrc E k c H).[i])) = cntu xsrc (φ E) (φ i).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k c H Hz Hk Hl Hc. rewrite cnt_loop_eq.
  destruct (bdec (k <? E)) as [Hk' | Hk'].
  - pose proof Hk' as L. rewrite ltb_spec in L.
    assert (Hk1 : (φ (k + 1)) = ((φ k) + 1)%Z) by sia.
    cbv zeta. eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply mes_dec with E. exact Hk'.
    + rewrite alength_set. exact Hl.
    + intros i Hi. pose proof (Hsrc k L) as Hs.
      unfold cntu. rewrite Hk1, cnt_succZ by (pose proof (to_Z_bounded k); lia).
      rewrite sv_int. fold (cntu xsrc (φ k) (φ i)). rewrite aget_set by lia.
      destruct (Z.eqb_spec (φ (xsrc.[k])) (φ i)) as [E1 | E1].
      * apply to_Z_inj in E1. rewrite E1 in *.
        pose proof (cnt_bounds (fun z => (sv xsrc z =? (φ i))%Z) (Z.to_nat (φ k))).
        rewrite add_spec, Hc by lia. fold (cntu xsrc (φ k) (φ i)) in *.
        change (φ 1) with 1%Z. rewrite Z.mod_small; rewrite ?wB_val; lia.
      * rewrite Hc by lia. lia.
  - apply ltb_ge_int in Hk'. assert ((φ k) = (φ E)) by lia.
    split; [exact Hl|]. intros i Hi. rewrite Hc by lia. rewrite H0. reflexivity.
Qed.

(* prefix sums *)
Lemma pre_loop_spec : forall z i c H, mes i = z ->
  ((φ i) <= (φ V))%Z ->
  (φ (PArray.length c)) = ((φ V) + 1)%Z ->
  (forall u, ((φ u) <= (φ V))%Z ->
     (φ (c.[u])) = if ((φ u) <=? (φ i))%Z then lo xsrc (φ E) ((φ u) + 1) else cntu xsrc (φ E) (φ u)) ->
  (φ (PArray.length (pre_loop V i c H))) = ((φ V) + 1)%Z /\
  forall u, ((φ u) <= (φ V))%Z -> (φ ((pre_loop V i c H).[u])) = lo xsrc (φ E) ((φ u) + 1).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i c H Hz Hi Hl Hc. rewrite pre_loop_eq.
  destruct (bdec (i <? V)) as [Hi' | Hi'].
  - pose proof Hi' as L. rewrite ltb_spec in L.
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z) by sia.
    eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply mes_dec with V. exact Hi'.
    + rewrite alength_set. exact Hl.
    + intros u Hu. rewrite aget_set by lia. rewrite Hi1.
      destruct (Z.eqb_spec (φ (i + 1)) (φ u)) as [E1 | E1].
      * rewrite <- E1, Hi1. rewrite Z.leb_refl.
        pose proof (Hc (i + 1) ltac:(lia)) as C1. pose proof (Hc i ltac:(lia)) as C0.
        rewrite Hi1 in C1. rewrite Z.leb_refl in C0.
        replace ((φ i) + 1 <=? (φ i))%Z with false in C1 by (symmetry; apply Z.leb_gt; lia).
        rewrite ?Z.eqb_refl, add_spec, C1, C0.
        rewrite (lo_succ ((φ i) + 1)).
        pose proof (cnt_bounds (fun z => (sv xsrc z =? (φ i) + 1)%Z) (Z.to_nat (φ E))).
        pose proof (cnt_bounds (fun z => (sv xsrc z <? (φ i) + 1)%Z) (Z.to_nat (φ E))).
        unfold cntu, lo in *. pose proof (to_Z_bounded E).
        rewrite Z.mod_small; rewrite ?wB_val; lia.
      * replace ((φ i) + 1 =? (φ u))%Z with false by (symmetry; apply Z.eqb_neq; lia).
        rewrite Hc by lia.
        destruct (Z.leb_spec (φ u) (φ i)), (Z.leb_spec (φ u) ((φ i) + 1)); try reflexivity; lia.
  - apply ltb_ge_int in Hi'. split; [exact Hl|]. intros u Hu. rewrite Hc by lia.
    destruct (Z.leb_spec (φ u) (φ i)); [reflexivity | lia].
Qed.

(* the counting-sort fill, from the last edge down *)
Lemma rfill_loop_spec : forall z k c adj H, (φ k) = z ->
  ((φ k) <= (φ E))%Z ->
  (φ (PArray.length c)) = ((φ V) + 1)%Z ->
  PArray.length adj = E ->
  (forall u, ((φ u) <= (φ V))%Z ->
     (φ (c.[u])) = (lo xsrc (φ E) (φ u) + cntu xsrc (φ k) (φ u))%Z) ->
  (forall u j, ((φ u) < (φ V))%Z -> ((φ (c.[u])) <= (φ j) < lo xsrc (φ E) ((φ u) + 1))%Z ->
     exists k', ((φ k) <= (φ k') < (φ E))%Z /\ xsrc.[k'] = u /\ xdst.[k'] = adj.[j]) ->
  (forall k', ((φ k) <= (φ k') < (φ E))%Z ->
     exists j, ((φ (c.[xsrc.[k']])) <= (φ j) < lo xsrc (φ E) ((φ (xsrc.[k'])) + 1))%Z /\
               adj.[j] = xdst.[k']) ->
  let r := rfill_loop xsrc xdst k c adj H in
  (φ (PArray.length (fst r))) = ((φ V) + 1)%Z /\ PArray.length (snd r) = E /\
  (forall u, ((φ u) <= (φ V))%Z -> (φ ((fst r).[u])) = lo xsrc (φ E) (φ u)) /\
  (forall u j, ((φ u) < (φ V))%Z -> (lo xsrc (φ E) (φ u) <= (φ j) < lo xsrc (φ E) ((φ u) + 1))%Z ->
     exists k', ((φ k') < (φ E))%Z /\ xsrc.[k'] = u /\ xdst.[k'] = (snd r).[j]) /\
  (forall k', ((φ k') < (φ E))%Z ->
     exists j, (lo xsrc (φ E) (φ (xsrc.[k'])) <= (φ j) < lo xsrc (φ E) ((φ (xsrc.[k'])) + 1))%Z /\
               (snd r).[j] = xdst.[k']).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros k c adj H Hz Hk Hl Hla Hc H2 H3. rewrite rfill_loop_eq.
  destruct (bdec (0 <? k)) as [Hk' | Hk'].
  - pose proof Hk' as L. rewrite ltb_spec in L. change (φ 0) with 0%Z in L.
    assert (Hk1 : (φ (k - 1)) = ((φ k) - 1)%Z) by sia.
    cbv zeta.
    set (k1 := k - 1) in *. set (u := xsrc.[k1]).
    assert (Hu : ((φ u) < (φ V))%Z) by (apply Hsrc; lia).
    pose proof (to_Z_bounded u) as Bu.
    assert (Hcnt : cntu xsrc (φ k) (φ u) = (cntu xsrc (φ k1) (φ u) + 1)%Z).
    { unfold cntu. replace (φ k) with ((φ k1) + 1)%Z by lia.
      rewrite cnt_succZ by lia. rewrite sv_int. fold u. rewrite Z.eqb_refl. reflexivity. }
    assert (Hcu := Hc u ltac:(lia)).
    pose proof (cnt_bounds (fun z => (sv xsrc z =? (φ u))%Z) (Z.to_nat (φ k1))) as B1.
    fold (cntu xsrc (φ k1) (φ u)) in B1.
    pose proof (cntu_le (φ k) (φ u) ltac:(lia)) as B2.
    pose proof (lo_succ (φ u)) as LS.
    pose proof (lo_mono ((φ u) + 1) (φ V) ltac:(lia)) as LM. rewrite (lo_V (φ V)) in LM by lia.
    pose proof (lo_mono 0 (φ u) ltac:(lia)) as LM0. rewrite lo_0 in LM0.
    set (p := c.[u] - 1).
    assert (Hp : (φ p) = (lo xsrc (φ E) (φ u) + cntu xsrc (φ k1) (φ u))%Z) by (unfold p; sia).
    assert (Hpb : ((φ p) < lo xsrc (φ E) ((φ u) + 1))%Z) by lia.
    assert (HpE : ((φ p) < (φ E))%Z) by lia.
    (* the row of any other source does not contain p *)
    assert (Hdisj : forall u' j, ((φ u') < (φ V))%Z -> u' <> u ->
              (lo xsrc (φ E) (φ u') <= (φ j) < lo xsrc (φ E) ((φ u') + 1))%Z -> j <> p).
    { intros u' j Hu' Hne Hj F. subst j.
      pose proof (to_Z_bounded u').
      apply (lo_disj (φ u) (φ u') (φ p) (φ p)); try lia;
      try (intro F; apply Hne; apply to_Z_inj; auto). }
    assert (Hcge : forall u', ((φ u') <= (φ V))%Z -> (lo xsrc (φ E) (φ u') <= (φ (c.[u'])))%Z).
    { intros u' Hu'. rewrite Hc by lia.
      pose proof (cnt_bounds (fun z => (sv xsrc z =? (φ u'))%Z) (Z.to_nat (φ k))). unfold cntu. lia. }
    eapply IH; [ | reflexivity | lia | | | | | ].
    + rewrite <- Hz. unfold k1. apply down_dec. exact Hk'.
    + rewrite alength_set. exact Hl.
    + rewrite alength_set. exact Hla.
    + intros u' Hu'. rewrite aget_set by lia.
      destruct (Z.eqb_spec (φ u) (φ u')) as [E1 | E1].
      * apply to_Z_inj in E1. subst u'. lia.
      * rewrite Hc by lia. f_equal. unfold cntu. replace (φ k) with ((φ k1) + 1)%Z by lia.
        rewrite cnt_succZ by lia. rewrite sv_int. fold u.
        replace ((φ u) =? (φ u'))%Z with false by (symmetry; apply Z.eqb_neq; exact E1). lia.
    + intros u' j Hu' Hj. rewrite (aget_set c) in Hj by lia.
      destruct (Z.eqb_spec (φ u) (φ u')) as [E1 | E1].
      * apply to_Z_inj in E1. subst u'.
        destruct (Z.eq_dec (φ j) (φ p)) as [E2 | E2].
        -- apply to_Z_inj in E2. subst j. exists k1. split; [lia|]. split; [reflexivity|].
           rewrite aget_set_same by lia. reflexivity.
        -- destruct (H2 u j ltac:(lia) ltac:(lia)) as (k' & Hk'' & Hs & Hd).
           exists k'. split; [lia|]. split; [exact Hs|].
           rewrite aget_set_other by (intro F; apply E2; subst; reflexivity). exact Hd.
      * assert (Hne : u' <> u) by (intro F; subst; apply E1; reflexivity).
        pose proof (Hcge u' ltac:(lia)).
        destruct (H2 u' j Hu' Hj) as (k' & Hk'' & Hs & Hd).
        exists k'. split; [lia|]. split; [exact Hs|].
        rewrite aget_set_other by (intro F; apply (Hdisj u' j Hu' Hne); [lia | auto]).
        exact Hd.
    + intros k' Hk''. destruct (Z.eq_dec (φ k') (φ k1)) as [E1 | E1].
      * apply to_Z_inj in E1. subst k'. exists p. fold u.
        rewrite aget_set_same by lia. rewrite aget_set_same by lia.
        split; [lia | reflexivity].
      * destruct (H3 k' ltac:(lia)) as (j & Hj & Hd).
        exists j. rewrite (aget_set c) by lia.
        assert (Hjp : j <> p).
        { destruct (Z.eqb_spec (φ u) (φ (xsrc.[k']))) as [E2 | E2].
          - apply to_Z_inj in E2. rewrite <- E2 in Hj. intro F. subst j. lia.
          - pose proof (Hsrc k' ltac:(lia)). pose proof (Hcge (xsrc.[k']) ltac:(lia)).
            apply (Hdisj (xsrc.[k'])); [lia | | lia].
            intro F. apply E2. rewrite F. reflexivity. }
        split.
        -- destruct (Z.eqb_spec (φ u) (φ (xsrc.[k']))) as [E2 | E2].
           ++ apply to_Z_inj in E2. rewrite <- E2 in Hj |- *.
              assert ((φ j) <> (φ p)) by (intro F; apply Hjp; apply to_Z_inj; exact F). lia.
           ++ exact Hj.
        -- rewrite aget_set_other by (intro F; apply Hjp; auto). exact Hd.
  - apply ltb_ge_int in Hk'. change (φ 0) with 0%Z in Hk'.
    assert (Hk0 : (φ k) = 0%Z) by (pose proof (to_Z_bounded k); lia).
    simpl. split; [exact Hl|]. split; [exact Hla|].
    assert (C0 : forall u, cntu xsrc (φ k) u = 0%Z) by (intros; unfold cntu; rewrite Hk0; reflexivity).
    split; [intros u Hu; rewrite Hc, C0 by lia; lia|].
    split.
    + intros u j Hu Hj.
      destruct (H2 u j Hu ltac:(rewrite Hc, C0 by lia; lia)) as (k' & ? & ? & ?).
      exists k'. split; [lia|]. auto.
    + intros k' Hk''. destruct (H3 k' ltac:(lia)) as (j & Hj & Hd). exists j.
      rewrite Hc, C0 in Hj by (apply Z.lt_le_incl, Hsrc; lia). split; [lia | exact Hd].
Qed.

End Csr.

(* in-degrees *)
Lemma ind_loop_spec : forall (adj : array int) (V E : int),
  PArray.length adj = E -> ((φ V) <= 400000)%Z ->
  (forall j, ((φ j) < (φ E))%Z -> ((φ (adj.[j])) < (φ V))%Z) ->
  forall z j d H, mes j = z -> ((φ j) <= (φ E))%Z ->
  PArray.length d = V ->
  (forall x, ((φ x) < (φ V))%Z -> (φ (d.[x])) = cnt (fun z => (sv adj z =? (φ x))%Z) (Z.to_nat (φ j))) ->
  PArray.length (ind_loop adj E j d H) = V /\
  forall x, ((φ x) < (φ V))%Z ->
    (φ ((ind_loop adj E j d H).[x])) = cnt (fun z => (sv adj z =? (φ x))%Z) (Z.to_nat (φ E)).
Proof.
  intros adj V E Hla HV Hadj z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j d H Hz Hj Hl Hd. rewrite ind_loop_eq.
  destruct (bdec (j <? E)) as [Hj' | Hj'].
  - pose proof Hj' as L. rewrite ltb_spec in L.
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    cbv zeta. eapply IH; [ | reflexivity | lia | | ].
    + rewrite <- Hz. apply mes_dec with E. exact Hj'.
    + rewrite alength_set. exact Hl.
    + intros x Hx. pose proof (Hadj j L) as Hs.
      rewrite Hj1, cnt_succZ by (pose proof (to_Z_bounded j); lia).
      rewrite sv_int. rewrite aget_set by (rewrite Hl; lia).
      destruct (Z.eqb_spec (φ (adj.[j])) (φ x)) as [E1 | E1].
      * apply to_Z_inj in E1. rewrite E1 in *.
        pose proof (cnt_bounds (fun z => (sv adj z =? (φ x))%Z) (Z.to_nat (φ j))).
        rewrite add_spec, Hd by lia.
        change (φ 1) with 1%Z. rewrite Z.mod_small; rewrite ?wB_val; lia.
      * rewrite Hd by lia. lia.
  - apply ltb_ge_int in Hj'. assert ((φ j) = (φ E)) by lia.
    split; [exact Hl|]. intros x Hx. rewrite Hd by lia. rewrite H0. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Queues: bounded existentials as booleans                            *)
(* ------------------------------------------------------------------ *)

Definition ati (q : array int) (i : nat) : int := q.[of_Z (Z.of_nat i)].

(* x is among q.[0 .. t) *)
Definition enqb (q : array int) (t x : int) : bool :=
  existsb (fun i => ati q i =? x) (seq 0 (Z.to_nat (φ t))).

Lemma existsb_seq : forall (f : nat -> bool) n,
  existsb f (seq 0 n) = true <-> exists i, (i < n)%nat /\ f i = true.
Proof.
  intros f n. rewrite existsb_exists. split.
  - intros (i & Hi & Hf). apply in_seq in Hi. exists i. split; [lia | exact Hf].
  - intros (i & Hi & Hf). exists i. split; [apply in_seq; lia | exact Hf].
Qed.

Lemma existsb_int : forall (g : int -> bool) (t : int),
  existsb (fun i => g (of_Z (Z.of_nat i))) (seq 0 (Z.to_nat (φ t))) = true <->
  exists i : int, ((φ i) < (φ t))%Z /\ g i = true.
Proof.
  intros g t. rewrite existsb_seq. pose proof (to_Z_bounded t). split.
  - intros (i & Hi & Hg). exists (of_Z (Z.of_nat i)). split; [|exact Hg].
    rewrite of_Z_spec, Z.mod_small; lia.
  - intros (i & Hi & Hg). exists (Z.to_nat (φ i)). pose proof (to_Z_bounded i).
    split; [lia|]. rewrite Z2Nat.id by lia. rewrite of_to_Z. exact Hg.
Qed.

Lemma enqb_spec : forall q t x,
  enqb q t x = true <-> exists i, ((φ i) < (φ t))%Z /\ q.[i] = x.
Proof.
  intros q t x. unfold enqb, ati.
  rewrite (existsb_int (fun i => q.[i] =? x)). split; intros (i & Hi & H); exists i;
    split; auto; [apply Uint63.eqb_spec in H | apply Uint63.eqb_spec]; auto.
Qed.

Lemma bool_iff : forall a b : bool, (a = true <-> b = true) -> a = b.
Proof. intros [] [] H; try reflexivity; [symmetry|]; apply H; reflexivity. Qed.

Lemma enqb_snoc : forall q t v x, ((φ t) < (φ (PArray.length q)))%Z ->
  enqb q.[t <- v] (t + 1) x = (enqb q t x || (v =? x))%bool.
Proof.
  intros q t v x Ht. pose proof (to_Z_bounded (PArray.length q)).
  assert (Ht1 : (φ (t + 1)) = ((φ t) + 1)%Z) by sia.
  apply bool_iff. rewrite Bool.orb_true_iff, !enqb_spec, Uint63.eqb_spec. split.
  - intros (i & Hi & Hq). destruct (Z.eq_dec (φ i) (φ t)) as [E | E].
    + apply to_Z_inj in E. subst i. rewrite aget_set_same in Hq by lia. right. exact Hq.
    + left. exists i. split; [lia|]. rewrite aget_set_other in Hq by (intro F; subst; lia).
      exact Hq.
  - intros [(i & Hi & Hq) | Hv].
    + exists i. split; [lia|]. rewrite aget_set_other by (intro F; subst; lia). exact Hq.
    + exists t. split; [lia|]. rewrite aget_set_same by lia. exact Hv.
Qed.

Lemma enqb_ext : forall q q' t x, (forall i, ((φ i) < (φ t))%Z -> q'.[i] = q.[i]) ->
  enqb q' t x = enqb q t x.
Proof.
  intros q q' t x Hq. apply bool_iff. rewrite !enqb_spec.
  split; intros (i & Hi & H); exists i; split; auto; [rewrite <- Hq | rewrite Hq]; auto.
Qed.

Lemma enqb_0 : forall q x, enqb q 0 x = false.
Proof. reflexivity. Qed.

(* the initial queue *)
Lemma q0_loop_spec : forall (V : int) (d : array int),
  ((φ V) <= 400000)%Z ->
  forall z x q t H, mes x = z -> ((φ x) <= (φ V))%Z -> ((φ t) <= (φ x))%Z ->
  PArray.length q = V ->
  (forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ x))%Z) ->
  (forall i i', ((φ i) < (φ t))%Z -> ((φ i') < (φ t))%Z -> q.[i] = q.[i'] -> i = i') ->
  (forall y, ((φ y) < (φ V))%Z -> (enqb q t y = true <-> ((φ y) < (φ x))%Z /\ (φ (d.[y])) = 0%Z)) ->
  let r := q0_loop V x d q t H in
  PArray.length (fst r) = V /\ ((φ (snd r)) <= (φ V))%Z /\
  (forall i, ((φ i) < (φ (snd r)))%Z -> ((φ ((fst r).[i])) < (φ V))%Z) /\
  (forall i i', ((φ i) < (φ (snd r)))%Z -> ((φ i') < (φ (snd r)))%Z -> (fst r).[i] = (fst r).[i'] -> i = i') /\
  (forall y, ((φ y) < (φ V))%Z -> (enqb (fst r) (snd r) y = true <-> (φ (d.[y])) = 0%Z)).
Proof.
  intros V d HV z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x q t H Hz Hx Ht Hl Hb Hi He. rewrite q0_loop_eq.
  destruct (bdec (x <? V)) as [Hx' | Hx'].
  - pose proof Hx' as L. rewrite ltb_spec in L.
    assert (Hx1 : (φ (x + 1)) = ((φ x) + 1)%Z) by sia.
    assert (Hdec : Zwf 0 (mes (x + 1)) z) by (rewrite <- Hz; apply mes_dec with V; exact Hx').
    destruct (d.[x] =? 0) eqn:Ed.
    + apply Uint63.eqb_spec in Ed.
      assert (Ht1 : (φ (t + 1)) = ((φ t) + 1)%Z) by sia.
      assert (Hnot : enqb q t x = false).
      { apply Bool.not_true_iff_false. rewrite He by lia. lia. }
      eapply IH; [exact Hdec | reflexivity | lia | lia | | | | ].
      * rewrite alength_set. exact Hl.
      * intros i Hi'. rewrite aget_set by (rewrite Hl; lia).
        destruct (Z.eqb_spec (φ t) (φ i)); [lia|]. pose proof (Hb i ltac:(lia)). lia.
      * intros i i' Hi1 Hi2. rewrite !aget_set by (rewrite Hl; lia).
        destruct (Z.eqb_spec (φ t) (φ i)) as [E1 | E1], (Z.eqb_spec (φ t) (φ i')) as [E2 | E2].
        -- intros _. apply to_Z_inj. lia.
        -- intros F. exfalso. assert (enqb q t x = true); [|congruence].
           apply enqb_spec. exists i'. split; [lia | auto].
        -- intros F. exfalso. assert (enqb q t x = true); [|congruence].
           apply enqb_spec. exists i. split; [lia | auto].
        -- apply Hi; lia.
      * intros y Hy. rewrite enqb_snoc by (rewrite Hl; lia).
        rewrite Bool.orb_true_iff, He, Uint63.eqb_spec by lia. rewrite Hx1. split.
        -- intros [[A B] | A]; [split; [lia | exact B] | subst; split; [lia | rewrite Ed; reflexivity]].
        -- intros [A B]. destruct (Z.eq_dec (φ y) (φ x)) as [E | E].
           ++ right. apply to_Z_inj. auto.
           ++ left. split; [lia | exact B].
    + assert (Ed' : (φ (d.[x])) <> 0%Z).
      { intro F. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in Ed. apply Ed.
        apply to_Z_inj. exact F. }
      eapply IH; [exact Hdec | reflexivity | lia | lia | exact Hl | | exact Hi | ].
      * intros i Hi'. pose proof (Hb i Hi'). lia.
      * intros y Hy. rewrite He by lia. rewrite Hx1. split.
        -- intros [A B]. split; [lia | exact B].
        -- intros [A B]. split; [|exact B]. destruct (Z.eq_dec (φ y) (φ x)) as [E | E].
           ++ apply to_Z_inj in E. subst. contradiction.
           ++ lia.
  - apply ltb_ge_int in Hx'. simpl.
    split; [exact Hl|]. split; [lia|]. split; [intros i Hi'; pose proof (Hb i Hi'); lia|].
    split; [exact Hi|]. intros y Hy. rewrite He by lia. split; [intros [_ B]; exact B | intros B; split; [lia | exact B]].
Qed.

(* ------------------------------------------------------------------ *)
(* Kahn's loop with the relaxation                                     *)
(* ------------------------------------------------------------------ *)

Section Kahn.

Variables (xs : PrimString.string) (V E : int) (off adj : array int).
(* Wk x z: some walk from 0 to x has weight z *)
Variable Wk : int -> Z -> Prop.

Hypothesis HV : (2 <= (φ V) <= 400000)%Z.
Hypothesis HE : ((φ E) <= 400000)%Z.
Hypothesis Hoffl : (φ (PArray.length off)) = ((φ V) + 1)%Z.
Hypothesis Hadjl : PArray.length adj = E.
Hypothesis Hoff0 : (φ (off.[0])) = 0%Z.
Hypothesis HoffV : (φ (off.[V])) = (φ E).
Hypothesis Hmono : forall a b, ((φ a) <= (φ b) <= (φ V))%Z -> ((φ (off.[a])) <= (φ (off.[b])))%Z.
Hypothesis Hadj : forall j, ((φ j) < (φ E))%Z -> ((φ (adj.[j])) < (φ V))%Z.
Hypothesis Hw : forall v, ((φ v) < (φ V))%Z -> (-1 <= Sint63.to_Z (wt xs V v) <= 1)%Z.
Hypothesis HW0 : Wk 0 0%Z.
Hypothesis HWs : forall u z j, ((φ u) < (φ V))%Z -> Wk u z ->
  ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
  Wk (adj.[j]) (z + Sint63.to_Z (wt xs V (adj.[j])))%Z.
Hypothesis HWb : forall x z, Wk x z -> (- (φ V) <= z <= (φ V))%Z.
Hypothesis Hacyc : forall P : int -> Prop,
  (forall x, ((φ x) < (φ V))%Z -> P x -> exists u j, ((φ u) < (φ V))%Z /\ P u /\
     ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z /\ adj.[j] = x) ->
  forall x, ((φ x) < (φ V))%Z -> ~ P x.

Definition inr (u : int) (z : Z) : bool :=
  (((φ (off.[u])) <=? z)%Z && (z <? (φ (off.[u + 1])))%Z)%bool.
Definition inr2 (u j : int) (z : Z) : bool :=
  (((φ (off.[u])) <=? z)%Z && (z <? (φ j))%Z)%bool.
(* z lies in the row of a popped location *)
Definition popd (q : array int) (h : int) (z : Z) : bool :=
  existsb (fun i => inr (ati q i) z) (seq 0 (Z.to_nat (φ h))).
(* the number of unprocessed edges into x *)
Definition unp (P : Z -> bool) (x : int) : Z :=
  cnt (fun z => ((sv adj z =? (φ x))%Z && negb (P z))%bool) (Z.to_nat (φ E)).
(* every edge out of u is relaxed *)
Definition Rlx (dist : array int) (u : int) : Prop :=
  dist.[u] <> NEG -> forall j, ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
  (Sint63.to_Z (dist.[u]) + Sint63.to_Z (wt xs V (adj.[j])) <= Sint63.to_Z (dist.[adj.[j]]))%Z.

Definition KInv (h : int) (P : Z -> bool) (d dist q : array int) (t : int) : Prop :=
  PArray.length d = V /\ PArray.length dist = V /\ PArray.length q = V /\
  ((φ h) <= (φ t) <= (φ V))%Z /\
  (forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ V))%Z) /\
  (forall i i', ((φ i) < (φ t))%Z -> ((φ i') < (φ t))%Z -> q.[i] = q.[i'] -> i = i') /\
  (forall x, ((φ x) < (φ V))%Z -> (enqb q t x = true <-> (φ (d.[x])) = 0%Z)) /\
  (forall x, ((φ x) < (φ V))%Z -> (φ (d.[x])) = unp P x) /\
  (forall x, ((φ x) < (φ V))%Z -> dist.[x] = NEG \/ Wk x (Sint63.to_Z (dist.[x]))) /\
  (0 <= Sint63.to_Z (dist.[0]))%Z.

Lemma succ_V : forall u, ((φ u) < (φ V))%Z -> (φ (u + 1)) = ((φ u) + 1)%Z.
Proof. intros u H. pose proof (to_Z_bounded u). sia. Qed.

Lemma off_E : forall u, ((φ u) <= (φ V))%Z -> ((φ (off.[u])) <= (φ E))%Z.
Proof. intros u H. rewrite <- HoffV. apply Hmono. lia. Qed.

Lemma rng_E : forall u j, ((φ u) < (φ V))%Z -> ((φ j) < (φ (off.[u + 1])))%Z -> ((φ j) < (φ E))%Z.
Proof. intros u j Hu Hj. pose proof (off_E (u + 1) ltac:(rewrite succ_V; lia)). lia. Qed.

Lemma rng_disj : forall u u' a b, ((φ u) < (φ V))%Z -> ((φ u') < (φ V))%Z -> u <> u' ->
  ((φ (off.[u])) <= a < (φ (off.[u + 1])))%Z ->
  ((φ (off.[u'])) <= b < (φ (off.[u' + 1])))%Z -> a <> b.
Proof.
  intros u u' a b Hu Hu' Hne Ha Hb F. subst b.
  destruct (Z.lt_total (φ u) (φ u')) as [L | [L | L]].
  - pose proof (Hmono (u + 1) u' ltac:(rewrite succ_V; lia)). lia.
  - apply Hne. apply to_Z_inj. exact L.
  - pose proof (Hmono (u' + 1) u ltac:(rewrite succ_V; lia)). lia.
Qed.

Lemma owner : forall z, (0 <= z < (φ E))%Z -> exists u, ((φ u) < (φ V))%Z /\ inr u z = true.
Proof.
  intros z Hz.
  set (f := fun k : Z => (φ (off.[of_Z k]))).
  assert (Hf0 : f 0%Z = 0%Z) by exact Hoff0.
  assert (HfV : f (φ V) = (φ E)) by (unfold f; rewrite of_to_Z; exact HoffV).
  destruct (owner_gen f z (Z.to_nat (φ V)) ltac:(lia) ltac:(rewrite Z2Nat.id; lia))
    as (m & Hm & Hfm).
  exists (of_Z (Z.of_nat m)).
  assert (Hm' : (φ (of_Z (Z.of_nat m))) = Z.of_nat m) by (apply of_Z_small; lia).
  split; [lia|]. unfold inr.
  replace (of_Z (Z.of_nat m) + 1) with (of_Z (Z.of_nat m + 1)).
  - unfold f in Hfm. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  - apply to_Z_inj. rewrite succ_V by lia. rewrite Hm', of_Z_small by lia. reflexivity.
Qed.

Lemma popd_spec : forall q h z,
  popd q h z = true <-> exists i, ((φ i) < (φ h))%Z /\ inr (q.[i]) z = true.
Proof. intros q h z. unfold popd, ati. apply (existsb_int (fun i => inr (q.[i]) z)). Qed.

Lemma popd_ext : forall q q' h z, (forall i, ((φ i) < (φ h))%Z -> q'.[i] = q.[i]) ->
  popd q' h z = popd q h z.
Proof.
  intros q q' h z Hq. apply bool_iff. rewrite !popd_spec. split.
  - intros (i & Hi & H). exists i. split; [exact Hi|]. rewrite Hq in H by exact Hi. exact H.
  - intros (i & Hi & H). exists i. split; [exact Hi|]. rewrite Hq by exact Hi. exact H.
Qed.

Lemma popd_snoc : forall q h z, ((φ (h + 1)) = (φ h) + 1)%Z ->
  popd q (h + 1) z = (popd q h z || inr (q.[h]) z)%bool.
Proof.
  intros q h z Hh. apply bool_iff. rewrite Bool.orb_true_iff, !popd_spec. split.
  - intros (i & Hi & H). destruct (Z.eq_dec (φ i) (φ h)) as [E1 | E1].
    + apply to_Z_inj in E1. subst. right. exact H.
    + left. exists i. split; [lia | exact H].
  - intros [(i & Hi & H) | H].
    + exists i. split; [lia | exact H].
    + exists h. split; [lia | exact H].
Qed.

Lemma popd_0 : forall q z, popd q 0 z = false.
Proof. reflexivity. Qed.

Lemma unp_ext : forall P1 P2 x, (forall z, P1 z = P2 z) -> unp P1 x = unp P2 x.
Proof. intros P1 P2 x H. unfold unp. apply cnt_ext. intros z _. rewrite H. reflexivity. Qed.

Lemma KInv_ext : forall h P1 P2 d dist q t, (forall z, P1 z = P2 z) ->
  KInv h P1 d dist q t -> KInv h P2 d dist q t.
Proof.
  intros h P1 P2 d dist q t HP K.
  destruct K as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split; [|split; assumption].
  intros x Hx. rewrite A8 by exact Hx. apply unp_ext. exact HP.
Qed.

(* pigeonhole: t distinct locations and one more fit in V *)
Lemma pigeon : forall (q : array int) (t v : int), ((φ t) <= (φ V))%Z ->
  (forall i, ((φ i) < (φ t))%Z -> ((φ (q.[i])) < (φ V))%Z) ->
  (forall i i', ((φ i) < (φ t))%Z -> ((φ i') < (φ t))%Z -> q.[i] = q.[i'] -> i = i') ->
  ((φ v) < (φ V))%Z -> (forall i, ((φ i) < (φ t))%Z -> q.[i] <> v) ->
  ((φ t) + 1 <= (φ V))%Z.
Proof.
  intros q t v Ht Hb Hi Hv Hne.
  pose proof (to_Z_bounded t) as Bt.
  set (f := fun i : nat => (φ (ati q i))).
  set (L := (φ v) :: map f (seq 0 (Z.to_nat (φ t)))).
  assert (Hof : forall i : nat, (i < Z.to_nat (φ t))%nat -> (φ (of_Z (Z.of_nat i))) = Z.of_nat i)
    by (intros i Hi'; apply of_Z_small; lia).
  assert (HN : NoDup L).
  { constructor.
    - intro F. apply in_map_iff in F. destruct F as (i & Hfi & Hin). apply in_seq in Hin.
      unfold f, ati in Hfi. apply to_Z_inj in Hfi.
      apply (Hne (of_Z (Z.of_nat i))); [rewrite Hof; lia | exact Hfi].
    - apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
      intros a b Ha Hb' Hab. apply in_seq in Ha, Hb'. unfold f, ati in Hab.
      apply to_Z_inj in Hab. apply Hi in Hab; [| rewrite Hof; lia | rewrite Hof; lia].
      assert (Z.of_nat a = Z.of_nat b) by (rewrite <- (Hof a), <- (Hof b), Hab by lia; reflexivity).
      lia. }
  assert (HI : incl L (map Z.of_nat (seq 0 (Z.to_nat (φ V))))).
  { intros y Hy. apply in_map_iff.
    assert (Hy' : (0 <= y < (φ V))%Z).
    { destruct Hy as [Hy | Hy].
      - subst. pose proof (to_Z_bounded v). lia.
      - apply in_map_iff in Hy. destruct Hy as (i & Hfi & Hin). apply in_seq in Hin.
        subst y. unfold f, ati. pose proof (to_Z_bounded (q.[of_Z (Z.of_nat i)])).
        split; [lia|]. apply Hb. rewrite Hof; lia. }
    exists (Z.to_nat y). split; [lia | apply in_seq; lia]. }
  pose proof (NoDup_incl_length HN HI) as HL.
  unfold L in HL. simpl in HL. rewrite !length_map, !length_seq in HL. lia.
Qed.

(* one relaxation *)
Lemma relax1_spec : forall du v dist,
  ((φ v) < (φ (PArray.length dist)))%Z -> ((φ v) < (φ V))%Z ->
  (du = NEG \/ (- (φ V) <= Sint63.to_Z du <= (φ V))%Z) ->
  let r := relax1 xs V du v dist in
  PArray.length r = PArray.length dist /\
  (forall x, x <> v -> r.[x] = dist.[x]) /\
  (Sint63.to_Z (dist.[v]) <= Sint63.to_Z (r.[v]))%Z /\
  (du <> NEG -> (Sint63.to_Z du + Sint63.to_Z (wt xs V v) <= Sint63.to_Z (r.[v]))%Z) /\
  (r.[v] = dist.[v] \/
   (du <> NEG /\ Sint63.to_Z (r.[v]) = (Sint63.to_Z du + Sint63.to_Z (wt xs V v))%Z)).
Proof.
  intros du v dist Hvl Hv Hdu. unfold relax1. pose proof (Hw v Hv) as Hwv.
  destruct (du =? NEG) eqn:En.
  - apply Uint63.eqb_spec in En. subst du.
    split; [reflexivity|]. split; [intros; reflexivity|]. split; [lia|].
    split; [intro F; contradiction F; reflexivity|]. left; reflexivity.
  - assert (Hne : du <> NEG) by (intro F; subst; rewrite Uint63.eqb_refl in En; discriminate).
    destruct Hdu as [Hdu | Hdu]; [contradiction|].
    assert (Hc : Sint63.to_Z (du + wt xs V v) = (Sint63.to_Z du + Sint63.to_Z (wt xs V v))%Z)
      by (apply sint_add; lia).
    cbv zeta. rewrite sint_ltb, Hc.
    destruct (Z.ltb_spec (Sint63.to_Z (dist.[v])) (Sint63.to_Z du + Sint63.to_Z (wt xs V v))).
    + rewrite alength_set. rewrite aget_set_same by exact Hvl.
      split; [reflexivity|].
      split; [intros x Hx; apply aget_set_other; intro F; apply Hx; symmetry; exact F|].
      split; [lia|]. split; [intros _; lia|]. right. split; [exact Hne | exact Hc].
    + split; [reflexivity|]. split; [intros; reflexivity|]. split; [lia|].
      split; [intros _; lia|]. left; reflexivity.
Qed.

Lemma Rlx_mono : forall dist dist' x, ((φ x) < (φ V))%Z -> Rlx dist x ->
  dist'.[x] = dist.[x] ->
  (forall y, ((φ y) < (φ V))%Z -> (Sint63.to_Z (dist.[y]) <= Sint63.to_Z (dist'.[y]))%Z) ->
  Rlx dist' x.
Proof.
  intros dist dist' x Hx R Ex Hm Hn j Hj. rewrite Ex in *.
  pose proof (R Hn j Hj). pose proof (Hm (adj.[j]) (Hadj j (rng_E x j Hx ltac:(lia)))). lia.
Qed.

Lemma relax_spec : forall h u du hi z j d dist q t H,
  mes j = z ->
  ((φ h) < (φ t))%Z -> q.[h] = u -> ((φ u) < (φ V))%Z -> hi = off.[u + 1] ->
  ((φ (off.[u])) <= (φ j) <= (φ hi))%Z -> dist.[u] = du ->
  KInv h (fun z => (popd q h z || inr2 u j z)%bool) d dist q t ->
  (forall i, ((φ i) < (φ h))%Z -> Rlx dist (q.[i])) ->
  (du <> NEG -> forall j', ((φ (off.[u])) <= (φ j') < (φ j))%Z ->
     (Sint63.to_Z du + Sint63.to_Z (wt xs V (adj.[j'])) <= Sint63.to_Z (dist.[adj.[j']]))%Z) ->
  match relax_loop xs V adj du hi j d dist q t H with
  | (d', dist', q', t') =>
      KInv (h + 1) (popd q' (h + 1)) d' dist' q' t' /\
      (forall i, ((φ i) < (φ (h + 1)))%Z -> Rlx dist' (q'.[i]))
  end.
Proof.
  intros h u du hi z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j d dist q t H Hz Hht Hqh Hu Hhi Hj Hdu K R Rc.
  rewrite relax_loop_eq.
  destruct (bdec (j <? hi)) as [Hj' | Hj'].
  - (* one edge u -> v *)
    pose proof Hj' as L. rewrite ltb_spec in L.
    assert (Hdec : Zwf 0 (mes (j + 1)) z) by (rewrite <- Hz; apply mes_dec with hi; exact Hj').
    subst hi.
    assert (HjE : ((φ j) < (φ E))%Z) by (apply (rng_E u j Hu L)).
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by (apply succ_lt with E; exact HjE).
    cbv zeta.
    set (v := adj.[j]).
    assert (Hv : ((φ v) < (φ V))%Z) by (apply Hadj; exact HjE).
    destruct K as (Kd & Kdist & Kq & Kht & Kqb & Kqi & Ken & Kcnt & Ksnd & K0).
    set (P := fun z => (popd q h z || inr2 u j z)%bool) in *.
    assert (HPj : P (φ j) = false).
    { unfold P. apply Bool.orb_false_iff. split.
      - apply Bool.not_true_iff_false. intro F. apply popd_spec in F.
        destruct F as (i & Hi & Hin).
        assert (Hne : q.[i] <> u).
        { intro F. rewrite <- Hqh in F. apply Kqi in F; [subst; lia | lia | lia]. }
        assert (Hqi : ((φ (q.[i])) < (φ V))%Z) by (apply Kqb; lia).
        unfold inr in Hin. apply andb_prop in Hin. destruct Hin as [A B].
        rewrite Z.leb_le in A. rewrite Z.ltb_lt in B.
        apply (rng_disj (q.[i]) u (φ j) (φ j) Hqi Hu Hne); [lia | lia | reflexivity].
      - unfold inr2. apply Bool.andb_false_intro2. apply Z.ltb_ge. lia. }
    set (P' := fun z => (popd q h z || inr2 u (j + 1) z)%bool).
    assert (HP'j : P' (φ j) = true).
    { unfold P', inr2. rewrite Hj1. apply Bool.orb_true_iff. right.
      apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
    assert (HPP : forall z, z <> (φ j) -> P' z = P z).
    { intros z0 Hz0. unfold P, P', inr2. rewrite Hj1.
      destruct (Z.ltb_spec z0 ((φ j) + 1)), (Z.ltb_spec z0 (φ j)); try reflexivity; lia. }
    assert (Hunp : forall x, unp P' x = (unp P x - (if ((φ v) =? (φ x))%Z then 1 else 0))%Z).
    { intros x. unfold unp.
      rewrite (cnt_upd (fun z => ((sv adj z =? (φ x))%Z && negb (P z))%bool)
                       (fun z => ((sv adj z =? (φ x))%Z && negb (P' z))%bool) _ (φ j)).
      - rewrite HPj. simpl negb. rewrite Bool.andb_true_r, sv_int. reflexivity.
      - pose proof (to_Z_bounded j). lia.
      - rewrite HP'j. apply Bool.andb_false_r.
      - intros z0 _ Hz0. rewrite HPP by exact Hz0. reflexivity. }
    assert (Hdv : (φ (d.[v])) = unp P v) by (apply Kcnt; exact Hv).
    assert (Hdv1 : (1 <= (φ (d.[v])))%Z).
    { pose proof (Hunp v) as U. rewrite Z.eqb_refl in U.
      pose proof (cnt_bounds (fun z => ((sv adj z =? (φ v))%Z && negb (P' z))%bool) (Z.to_nat (φ E))) as B.
      fold (unp P' v) in B. lia. }
    assert (Hnenq : enqb q t v = false).
    { apply Bool.not_true_iff_false. rewrite Ken by exact Hv. lia. }
    assert (Hvq : forall i, ((φ i) < (φ t))%Z -> q.[i] <> v).
    { intros i Hi F.
      assert (enqb q t v = true) by (apply enqb_spec; exists i; split; [exact Hi | exact F]).
      rewrite Hnenq in H0. discriminate. }
    assert (Hvu : v <> u) by (intro F; apply (Hvq h Hht); rewrite Hqh; symmetry; exact F).
    set (e := d.[v] - 1).
    assert (He : (φ e) = ((φ (d.[v])) - 1)%Z) by (apply sub1; exact Hdv1).
    (* the distances *)
    assert (Hdu' : du = NEG \/ (- (φ V) <= Sint63.to_Z du <= (φ V))%Z).
    { destruct (Ksnd u Hu) as [A | A];
        [left; rewrite <- Hdu; exact A | right; rewrite <- Hdu; exact (HWb _ _ A)]. }
    destruct (relax1_spec du v dist ltac:(rewrite Kdist; exact Hv) Hv Hdu')
      as (D1 & D2 & D3 & D4 & D5).
    set (dist' := relax1 xs V du v dist) in *.
    assert (Dm : forall y, ((φ y) < (φ V))%Z ->
              (Sint63.to_Z (dist.[y]) <= Sint63.to_Z (dist'.[y]))%Z).
    { intros y Hy. destruct (idec y v) as [E1 | E1];
        [rewrite E1; exact D3 | rewrite D2 by exact E1; lia]. }
    assert (Dsnd : forall x, ((φ x) < (φ V))%Z -> dist'.[x] = NEG \/ Wk x (Sint63.to_Z (dist'.[x]))).
    { intros x Hx. destruct (idec x v) as [E1 | E1].
      - rewrite E1. destruct D5 as [A | [A B]].
        + rewrite A. apply Ksnd. exact Hv.
        + right. rewrite B. unfold v. apply (HWs u); [exact Hu | | lia].
          destruct (Ksnd u Hu) as [C | C];
            [rewrite Hdu in C; contradiction | rewrite <- Hdu; exact C].
      - rewrite D2 by exact E1. apply Ksnd. exact Hx. }
    assert (D0 : (0 <= Sint63.to_Z (dist'.[0]))%Z)
      by (pose proof (Dm 0 ltac:(change (φ 0) with 0%Z; lia)); lia).
    assert (Du : dist'.[u] = du)
      by (rewrite D2 by (intro F; apply Hvu; symmetry; exact F); exact Hdu).
    assert (Rold : forall i, ((φ i) < (φ h))%Z -> Rlx dist' (q.[i])).
    { intros i Hi. apply (Rlx_mono dist); [apply Kqb; lia | apply R; exact Hi | | exact Dm].
      apply D2. apply Hvq. lia. }
    assert (Rcur : du <> NEG -> forall j', ((φ (off.[u])) <= (φ j') < (φ (j + 1)))%Z ->
       (Sint63.to_Z du + Sint63.to_Z (wt xs V (adj.[j'])) <= Sint63.to_Z (dist'.[adj.[j']]))%Z).
    { intros Hn j' Hj''. rewrite Hj1 in Hj''. destruct (Z.eq_dec (φ j') (φ j)) as [E1 | E1].
      - apply to_Z_inj in E1. rewrite E1. exact (D4 Hn).
      - pose proof (Rc Hn j' ltac:(lia)).
        pose proof (Dm (adj.[j']) (Hadj j' ltac:(lia))). lia. }
    (* the in-degrees *)
    assert (Hdl : PArray.length (d.[v <- e]) = V) by (rewrite alength_set; exact Kd).
    assert (Hd'v : (d.[v <- e]).[v] = e) by (apply aget_set_same; rewrite Kd; exact Hv).
    assert (Hd'x : forall x, x <> v -> (d.[v <- e]).[x] = d.[x])
      by (intros x Hx; apply aget_set_other; intro F; apply Hx; symmetry; exact F).
    assert (Dcnt : forall x, ((φ x) < (φ V))%Z -> (φ ((d.[v <- e]).[x])) = unp P' x).
    { intros x Hx. rewrite Hunp. destruct (idec x v) as [E1 | E1].
      - rewrite E1. rewrite Hd'v, He, Z.eqb_refl, Hdv. reflexivity.
      - rewrite Hd'x by exact E1. rewrite Kcnt by exact Hx.
        replace ((φ v) =? (φ x))%Z with false
          by (symmetry; apply Z.eqb_neq; intro F; apply E1; apply to_Z_inj; symmetry; exact F).
        lia. }
    destruct (e =? 0) eqn:Ee.
    + (* v is enqueued *)
      apply Uint63.eqb_spec in Ee.
      assert (Ht1 : ((φ t) + 1 <= (φ V))%Z)
        by (apply (pigeon q t v); [lia | exact Kqb | exact Kqi | exact Hv | exact Hvq]).
      assert (Ht1' : (φ (t + 1)) = ((φ t) + 1)%Z) by (apply succ_lt with V; lia).
      assert (Hqa : forall i, ((φ i) < (φ t))%Z -> (q.[t <- v]).[i] = q.[i])
        by (intros i Hi; apply aget_set_other; intro F; subst; lia).
      eapply IH; [exact Hdec | reflexivity | lia | | exact Hu | reflexivity | lia | exact Du
                 | | | exact Rcur].
      * rewrite Hqa by exact Hht. exact Hqh.
      * apply (KInv_ext h P').
        { intros z0. unfold P'. rewrite (popd_ext q (q.[t <- v]) h z0); [reflexivity|].
          intros i Hi. apply Hqa. lia. }
        split; [exact Hdl|]. split; [rewrite D1; exact Kdist|].
        split; [rewrite alength_set; exact Kq|]. split; [lia|].
        split.
        { intros i Hi. rewrite (aget_set q) by (rewrite Kq; lia).
          destruct (Z.eqb_spec (φ t) (φ i)); [exact Hv | apply Kqb; lia]. }
        split.
        { intros i i' Hi Hi'. rewrite !(aget_set q) by (rewrite Kq; lia).
          destruct (Z.eqb_spec (φ t) (φ i)) as [E1 | E1], (Z.eqb_spec (φ t) (φ i')) as [E2 | E2].
          - intros _. apply to_Z_inj. lia.
          - intros F. exfalso. apply (Hvq i'); [lia | symmetry; exact F].
          - intros F. exfalso. apply (Hvq i); [lia | exact F].
          - apply Kqi; lia. }
        split.
        { intros x Hx. rewrite enqb_snoc by (rewrite Kq; lia).
          rewrite Bool.orb_true_iff, Uint63.eqb_spec.
          destruct (idec x v) as [E1 | E1].
          - rewrite E1, Hd'v, Ee. split; [intros _; reflexivity | intros _; right; reflexivity].
          - rewrite Hd'x by exact E1. rewrite <- Ken by exact Hx. split.
            + intros [A | A]; [exact A | exfalso; apply E1; symmetry; exact A].
            + intros A; left; exact A. }
        split; [exact Dcnt|]. split; [exact Dsnd | exact D0].
      * intros i Hi. rewrite Hqa by lia. apply Rold. exact Hi.
    + (* v keeps a positive in-degree *)
      assert (Ee' : (φ e) <> 0%Z).
      { intro F. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in Ee.
        apply Ee. apply to_Z_inj. exact F. }
      eapply IH; [exact Hdec | reflexivity | exact Hht | exact Hqh | exact Hu | reflexivity
                 | lia | exact Du | | exact Rold | exact Rcur].
      split; [exact Hdl|]. split; [rewrite D1; exact Kdist|]. split; [exact Kq|].
      split; [exact Kht|]. split; [exact Kqb|]. split; [exact Kqi|].
      split.
      { intros x Hx. destruct (idec x v) as [E1 | E1].
        - rewrite E1, Hd'v, Hnenq. split; [discriminate | intro F; contradiction].
        - rewrite Hd'x by exact E1. apply Ken. exact Hx. }
      split; [exact Dcnt|]. split; [exact Dsnd | exact D0].
  - (* end of the row *)
    apply ltb_ge_int in Hj'. subst hi. cbv iota beta.
    assert (Hjhi : (φ j) = (φ (off.[u + 1]))) by lia.
    assert (Hh1 : (φ (h + 1)) = ((φ h) + 1)%Z) by (apply succ_lt with t; exact Hht).
    destruct K as (Kd & Kdist & Kq & Kht & Kqb & Kqi & Ken & Kcnt & Ksnd & K0).
    split.
    + split; [exact Kd|]. split; [exact Kdist|]. split; [exact Kq|]. split; [lia|].
      split; [exact Kqb|]. split; [exact Kqi|]. split; [exact Ken|].
      split; [|split; [exact Ksnd | exact K0]].
      intros x Hx. rewrite Kcnt by exact Hx. apply unp_ext. intros z0.
      rewrite popd_snoc by exact Hh1. rewrite Hqh. unfold inr, inr2. rewrite Hjhi. reflexivity.
    + intros i Hi. rewrite Hh1 in Hi. destruct (Z.eq_dec (φ i) (φ h)) as [E1 | E1].
      * apply to_Z_inj in E1. rewrite E1, Hqh. unfold Rlx. rewrite Hdu.
        intros Hn j' Hj''. apply Rc; [exact Hn | lia].
      * apply R. lia.
Qed.

Lemma kahn_spec : forall z h d dist q t H, mes h = z ->
  KInv h (popd q h) d dist q t -> (forall i, ((φ i) < (φ h))%Z -> Rlx dist (q.[i])) ->
  let r := kahn_loop xs V off adj h d dist q t H in
  PArray.length r = V /\ (forall x, ((φ x) < (φ V))%Z -> Rlx r x) /\
  (forall x, ((φ x) < (φ V))%Z -> r.[x] = NEG \/ Wk x (Sint63.to_Z (r.[x]))) /\
  (0 <= Sint63.to_Z (r.[0]))%Z.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros h d dist q t H Hz K R. rewrite kahn_loop_eq.
  destruct (bdec (h <? t)) as [Hh | Hh].
  - pose proof Hh as L. rewrite ltb_spec in L.
    assert (Hdec : Zwf 0 (mes (h + 1)) z) by (rewrite <- Hz; apply mes_dec with t; exact Hh).
    cbv zeta.
    assert (Hu : ((φ (q.[h])) < (φ V))%Z)
      by (destruct K as (_ & _ & _ & _ & Kqb & _); apply Kqb; exact L).
    pose proof (relax_spec h (q.[h]) (dist.[q.[h]]) (off.[q.[h] + 1]) (mes (off.[q.[h]]))
                  (off.[q.[h]]) d dist q t (Zwf_well_founded 0 (mes (off.[q.[h]])))
                  eq_refl L eq_refl Hu eq_refl) as RS.
    specialize (RS ltac:(pose proof (Hmono (q.[h]) (q.[h] + 1) ltac:(rewrite succ_V; lia)); lia)
                eq_refl).
    specialize (RS ltac:(apply (KInv_ext h (popd q h)); [|exact K]; intros z0; unfold inr2;
                         destruct (Z.leb_spec (φ (off.[q.[h]])) z0),
                                  (Z.ltb_spec z0 (φ (off.[q.[h]])));
                         try lia; rewrite ?Bool.orb_false_r; reflexivity)
                R ltac:(intros _ j' Hj'; lia)).
    revert RS.
    destruct (relax_loop xs V adj (dist.[q.[h]]) (off.[q.[h] + 1]) (off.[q.[h]]) d dist q t
                (Zwf_well_founded 0 (mes (off.[q.[h]])))) as [[[d' dist'] q'] t'].
    intros [K' R']. eapply IH; [exact Hdec | reflexivity | exact K' | exact R'].
  - apply ltb_ge_int in Hh.
    destruct K as (Kd & Kdist & Kq & Kht & Kqb & Kqi & Ken & Kcnt & Ksnd & K0).
    assert (Hth : (φ h) = (φ t)) by lia.
    split; [exact Kdist|]. split; [|split; [exact Ksnd | exact K0]].
    assert (CL : forall y, ((φ y) < (φ V))%Z -> enqb q t y = false ->
              exists u j, ((φ u) < (φ V))%Z /\ enqb q t u = false /\
                ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z /\ adj.[j] = y).
    { intros y Hy Hey.
      assert (Hdy : (φ (d.[y])) <> 0%Z).
      { intro F. rewrite <- Ken in F by exact Hy. rewrite Hey in F. discriminate. }
      pose proof (Kcnt y Hy) as Cy. unfold unp in Cy.
      pose proof (to_Z_bounded (d.[y])).
      destruct (cnt_pos _ _ ltac:(rewrite <- Cy; lia)) as (z0 & Hz0 & Hf).
      apply andb_prop in Hf. destruct Hf as [Hf1 Hf2].
      apply Z.eqb_eq in Hf1. apply Bool.negb_true_iff in Hf2.
      pose proof (to_Z_bounded E).
      destruct (owner z0 ltac:(lia)) as (u & Hu & Hin).
      assert (Hz0' : (φ (of_Z z0)) = z0) by (apply of_Z_small; lia).
      exists u, (of_Z z0). split; [exact Hu|]. split.
      - destruct (enqb q t u) eqn:Eu; [exfalso | reflexivity].
        apply enqb_spec in Eu. destruct Eu as (i & Hi & Hqi).
        assert (Hp : popd q h z0 = true)
          by (apply popd_spec; exists i; split; [lia | rewrite Hqi; exact Hin]).
        rewrite Hf2 in Hp. discriminate.
      - unfold inr in Hin. apply andb_prop in Hin. destruct Hin as [A B].
        rewrite Z.leb_le in A. rewrite Z.ltb_lt in B.
        split; [lia|]. apply to_Z_inj. unfold sv in Hf1. exact Hf1. }
    intros x Hx.
    assert (Hall : enqb q t x = true).
    { destruct (enqb q t x) eqn:Ex; [reflexivity | exfalso].
      exact (Hacyc (fun y => enqb q t y = false) CL x Hx Ex). }
    apply enqb_spec in Hall. destruct Hall as (i & Hi & Hqi). rewrite <- Hqi. apply R. lia.
Qed.

End Kahn.

(* ------------------------------------------------------------------ *)
(* The math side: weights, walks                                       *)
(* ------------------------------------------------------------------ *)

(* the contribution of location v to the happiness *)
Definition wm (s : string) (v : N) : Z :=
  ((if (negb ((v =? 0)%N || (v =? slen s - 1)%N) && is_site s "X"%char v)%bool then 1 else 0)
   - (if (negb ((v =? 0)%N || (v =? slen s - 1)%N) && is_site s "."%char v)%bool then 1 else 0))%Z.

Fixpoint wsum (s : string) (p : list N) : Z :=
  match p with
  | [] => 0%Z
  | v :: r => (wm s v + wsum s r)%Z
  end.

Lemma count_sites_cons : forall s c v p,
  count_sites s c (v :: p) =
  ((if (negb ((v =? 0)%N || (v =? slen s - 1)%N) && is_site s c v)%bool then 1 else 0)
   + count_sites s c p)%Z.
Proof.
  intros s c v p. unfold count_sites. simpl.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [List.length]; lia.
Qed.

Lemma happiness_wsum : forall s p, happiness s p = wsum s p.
Proof.
  intros s p. induction p as [|v p IH]; [reflexivity|].
  unfold happiness in *. rewrite !count_sites_cons. simpl wsum. unfold wm. lia.
Qed.

Lemma wsum_app : forall s p q, wsum s (p ++ q) = (wsum s p + wsum s q)%Z.
Proof. intros s p q. induction p as [|v p IH]; simpl; lia. Qed.

Lemma wm_bound : forall s v, (-1 <= wm s v <= 1)%Z.
Proof.
  intros s v. unfold wm.
  destruct (negb ((v =? 0)%N || (v =? slen s - 1)%N) && is_site s "X"%char v)%bool,
           (negb ((v =? 0)%N || (v =? slen s - 1)%N) && is_site s "."%char v)%bool; lia.
Qed.

Lemma wm_0 : forall s, wm s 0%N = 0%Z.
Proof. reflexivity. Qed.

Lemma wsum_bound : forall s p, (- Z.of_nat (List.length p) <= wsum s p <= Z.of_nat (List.length p))%Z.
Proof.
  intros s p. induction p as [|v p IH]; simpl; [lia|]. pose proof (wm_bound s v). lia.
Qed.

Lemma walk_tail : forall src dst x p, walk src dst (x :: p) -> walk src dst p.
Proof. intros src dst x p W. destruct p as [|y p]; [exact I | exact (proj2 W)]. Qed.

Lemma walk_reach : forall src dst p x y,
  walk src dst (x :: p) -> In y p -> clos_trans N (edge src dst) x y.
Proof.
  intros src dst p. induction p as [|a p IH]; intros x y W Hy; [destruct Hy|].
  destruct W as [Ea W']. destruct Hy as [Hy | Hy].
  - subst. apply t_step. exact Ea.
  - apply t_trans with a; [apply t_step; exact Ea | apply IH; [exact W' | exact Hy]].
Qed.

Lemma walk_nodup : forall src dst, (forall u, ~ clos_trans N (edge src dst) u u) ->
  forall p, walk src dst p -> NoDup p.
Proof.
  intros src dst Hac p. induction p as [|x p IH]; intros W; constructor.
  - intro Hin. apply (Hac x). exact (walk_reach src dst p x x W Hin).
  - apply IH. exact (walk_tail src dst x p W).
Qed.

Lemma walk_lt : forall src dst n, Forall (fun t => (t < n)%N) dst ->
  forall p x, walk src dst (x :: p) -> Forall (fun y => (y < n)%N) p.
Proof.
  intros src dst n Hd p. induction p as [|a p IH]; intros x W; constructor.
  - destruct W as [(k & _ & Hk) _]. apply nth_error_In in Hk.
    rewrite Forall_forall in Hd. exact (Hd a Hk).
  - apply (IH a). exact (proj2 W).
Qed.

Lemma nodup_len : forall (c : list N) n, NoDup c ->
  Forall (fun a => (a < N.of_nat n)%N) c -> (List.length c <= n)%nat.
Proof.
  intros c n ND F.
  assert (HI : incl c (map N.of_nat (seq 0 n))).
  { intros a Ha. rewrite Forall_forall in F. specialize (F a Ha).
    apply in_map_iff. exists (N.to_nat a). split; [lia | apply in_seq; lia]. }
  pose proof (NoDup_incl_length ND HI) as HL. rewrite length_map, length_seq in HL. exact HL.
Qed.

Lemma walk_snoc : forall src dst p x y, p <> [] -> walk src dst p ->
  last p 0%N = x -> edge src dst x y -> walk src dst (p ++ [y]).
Proof.
  intros src dst p. induction p as [|a p IH]; intros x y Hne W Hl Ee; [contradiction|].
  destruct p as [|b p].
  - simpl in Hl. subst. split; [exact Ee | exact I].
  - destruct W as [Eab W'].
    change (last (a :: b :: p) 0%N) with (last (b :: p) 0%N) in Hl.
    change ((a :: b :: p) ++ [y]) with (a :: ((b :: p) ++ [y])).
    split; [exact Eab|]. exact (IH x y ltac:(discriminate) W' Hl Ee).
Qed.

Lemma ascii_eqb_N : forall a b, Ascii.eqb a b = N.eqb (N_of_ascii a) (N_of_ascii b).
Proof.
  intros a b. destruct (Ascii.eqb_spec a b) as [E | E];
    destruct (N.eqb_spec (N_of_ascii a) (N_of_ascii b)) as [F | F]; try reflexivity.
  - exfalso. apply F. subst. reflexivity.
  - exfalso. apply E. rewrite <- (ascii_N_embedding a), <- (ascii_N_embedding b), F. reflexivity.
Qed.

Lemma wt_bound : forall xs V v, (-1 <= Sint63.to_Z (wt xs V v) <= 1)%Z.
Proof.
  intros xs V v. unfold wt.
  assert (A0 : Sint63.to_Z 0 = 0%Z) by reflexivity.
  assert (A1 : Sint63.to_Z 1 = 1%Z) by reflexivity.
  assert (Am : Sint63.to_Z MONE = (-1)%Z) by reflexivity.
  destruct (v =? 0); [lia|]. destruct (v =? V - 1); [lia|].
  destruct (PrimString.get xs v =? 88); [lia|]. destruct (PrimString.get xs v =? 46); lia.
Qed.

(* the machine weight is the math weight *)
Lemma wt_wm : forall (s : string) (xs : PrimString.string),
  (φ (PrimString.length xs)) = Z.of_nat (String.length s) ->
  (forall k : int, ((φ k) < (φ (PrimString.length xs)))%Z -> exists c,
     String.get (Z.to_nat (φ k)) s = Some c /\ (φ (PrimString.get xs k)) = Z.of_N (N_of_ascii c)) ->
  forall v, ((φ v) < (φ (PrimString.length xs)))%Z ->
  Sint63.to_Z (wt xs (PrimString.length xs) v) = wm s (Z.to_N (φ v)).
Proof.
  intros s xs HlX HgX v Hv. set (V := PrimString.length xs) in *.
  pose proof (to_Z_bounded v) as Bv.
  unfold wt. destruct (v =? 0) eqn:E0.
  - apply Uint63.eqb_spec in E0. subst v. reflexivity.
  - assert (E0' : (Z.to_N (φ v) =? 0)%N = false).
    { apply N.eqb_neq. intro F. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E0.
      apply E0. apply to_Z_inj. change (φ 0) with 0%Z. lia. }
    destruct (v =? V - 1) eqn:E1.
    + apply Uint63.eqb_spec in E1. unfold wm.
      replace (Z.to_N (φ v) =? slen s - 1)%N with true.
      * rewrite Bool.orb_true_r. reflexivity.
      * symmetry. apply N.eqb_eq. rewrite E1. unfold slen.
        rewrite sub1 by lia. lia.
    + assert (E1' : (Z.to_N (φ v) =? slen s - 1)%N = false).
      { apply N.eqb_neq. intro F. rewrite <- Bool.not_true_iff_false, Uint63.eqb_spec in E1.
        apply E1. apply to_Z_inj. rewrite sub1 by lia. unfold slen in F. lia. }
      unfold wm. rewrite E0', E1'. simpl negb. simpl andb.
      destruct (HgX v Hv) as (c & Hc & Hcc).
      unfold is_site. rewrite Z_N_nat, Hc. rewrite !ascii_eqb_N.
      change (N_of_ascii "X"%char) with 88%N. change (N_of_ascii "."%char) with 46%N.
      assert (A88 : (PrimString.get xs v =? 88) = (N_of_ascii c =? 88)%N).
      { apply bool_iff. rewrite Uint63.eqb_spec, N.eqb_eq. split; intro F.
        - rewrite F in Hcc. change (φ 88) with 88%Z in Hcc. lia.
        - apply to_Z_inj. rewrite Hcc, F. reflexivity. }
      assert (A46 : (PrimString.get xs v =? 46) = (N_of_ascii c =? 46)%N).
      { apply bool_iff. rewrite Uint63.eqb_spec, N.eqb_eq. split; intro F.
        - rewrite F in Hcc. change (φ 46) with 46%Z in Hcc. lia.
        - apply to_Z_inj. rewrite Hcc, F. reflexivity. }
      rewrite A88, A46.
      destruct (N.eqb_spec (N_of_ascii c) 88); destruct (N.eqb_spec (N_of_ascii c) 46);
        try lia; reflexivity.
Qed.

(* acyclicity, on the machine side: no nonempty set of locations is closed
   under taking a predecessor *)
Lemma acyc_machine : forall (src dst : list N) (V : int) (off adj : array int),
  (forall u j, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
     edge src dst (Z.to_N (φ u)) (Z.to_N (φ (adj.[j])))) ->
  (forall u, ~ clos_trans N (edge src dst) u u) ->
  forall P : int -> Prop,
  (forall x, ((φ x) < (φ V))%Z -> P x -> exists u j, ((φ u) < (φ V))%Z /\ P u /\
     ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z /\ adj.[j] = x) ->
  forall x, ((φ x) < (φ V))%Z -> ~ P x.
Proof.
  intros src dst V off adj HC2 Hac P CL x Hx Px.
  set (Q := fun a : N => exists y, ((φ y) < (φ V))%Z /\ P y /\ a = Z.to_N (φ y)).
  assert (G : forall n : nat, exists c, List.length c = S n /\ walk src dst c /\ Forall Q c).
  { induction n as [|n IH].
    - exists [Z.to_N (φ x)]. split; [reflexivity|]. split; [exact I|].
      constructor; [|constructor]. exists x. split; [exact Hx|]. split; [exact Px | reflexivity].
    - destruct IH as (c & Hl & W & F). destruct c as [|a c']; [discriminate|].
      pose proof (Forall_inv F) as Qa. destruct Qa as (y & Hy & Py & Ea).
      destruct (CL y Hy Py) as (u & j & Hu & Pu & Hj & Ej).
      exists (Z.to_N (φ u) :: a :: c'). split; [simpl in *; lia|]. split.
      + split; [|exact W]. rewrite Ea, <- Ej. apply HC2; [exact Hu | exact Hj].
      + constructor; [|exact F]. exists u. split; [exact Hu|]. split; [exact Pu | reflexivity]. }
  destruct (G (Z.to_nat (φ V))) as (c & Hl & W & F).
  pose proof (walk_nodup src dst Hac c W) as ND.
  assert (Fl : Forall (fun a => (a < N.of_nat (Z.to_nat (φ V)))%N) c).
  { eapply Forall_impl; [|exact F]. intros a (y & Hy & _ & Ea). subst a.
    pose proof (to_Z_bounded y). lia. }
  pose proof (nodup_len c _ ND Fl). lia.
Qed.

(* reading the inputs *)
Lemma repr_arr : forall (x : array uint) (l : list N), repr x l ->
  (φ (@PArray.length int x)) = Z.of_nat (List.length l) /\
  forall k : int, ((φ k) < (φ (@PArray.length int x)))%Z ->
    nth_error l (Z.to_nat (φ k)) = Some (Z.to_N (φ (@PArray.get int x k))).
Proof.
  intros x l [Hl Hc].
  assert (Hl' : (φ (@PArray.length int x)) = Z.of_nat (List.length l)) by (symmetry; exact Hl).
  split; [exact Hl'|].
  intros k Hk.
  assert (Hk' : ((φ k) < Z.of_nat (List.length l))%Z) by (rewrite <- Hl'; exact Hk).
  destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (m & Hm & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia).
  rewrite of_to_Z in Hr. rewrite Hm, <- Hr. reflexivity.
Qed.

Lemma repr_str : forall (xs : PrimString.string) (s : string), repr xs s ->
  (φ (PrimString.length xs)) = Z.of_nat (String.length s) /\
  (forall k : int, ((φ k) < (φ (PrimString.length xs)))%Z -> exists c,
     String.get (Z.to_nat (φ k)) s = Some c /\ (φ (PrimString.get xs k)) = Z.of_N (N_of_ascii c)).
Proof.
  intros xs s [Hl Hc]. split; [symmetry; exact Hl|].
  intros k Hk. destruct (Hc (Z.to_nat (φ k)) ltac:(lia)) as (c & Hs & Hr).
  exists c. split; [exact Hs|].
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded k); lia).
  rewrite of_to_Z in Hr. rewrite <- Hr. pose proof (to_Z_bounded (PrimString.get xs k)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The contract                                                        *)
(* ------------------------------------------------------------------ *)

Lemma main_aux : forall (s : string) (src dst : list N) (xs : PrimString.string)
    (xsrc xdst : array int),
  valid_input s src dst ->
  (φ (PrimString.length xs)) = Z.of_nat (String.length s) ->
  (forall k : int, ((φ k) < (φ (PrimString.length xs)))%Z -> exists c,
     String.get (Z.to_nat (φ k)) s = Some c /\ (φ (PrimString.get xs k)) = Z.of_N (N_of_ascii c)) ->
  (φ (PArray.length xsrc)) = Z.of_nat (List.length src) ->
  (forall k, ((φ k) < (φ (PArray.length xsrc)))%Z ->
     nth_error src (Z.to_nat (φ k)) = Some (Z.to_N (φ (xsrc.[k])))) ->
  (φ (PArray.length xdst)) = Z.of_nat (List.length dst) ->
  (forall k, ((φ k) < (φ (PArray.length xdst)))%Z ->
     nth_error dst (Z.to_nat (φ k)) = Some (Z.to_N (φ (xdst.[k])))) ->
  excavator_spec s src dst (Sint63.to_Z (excavator_impl xs xsrc xdst)).
Proof.
  intros s src dst xs xsrc xdst Hvi HlX HgX HlS HgS HlD HgD.
  destruct Hvi as [HviV HviE HviL Hvisrc Hvidst _ _ Hvipath Hviac].
  unfold len, slen in HviV, HviE, HviL, Hvisrc, Hvidst.
  pose proof (wt_wm s xs HlX HgX) as Hwm.
  unfold excavator_impl. cbv zeta.
  set (V := PrimString.length xs) in *. set (E := PArray.length xsrc) in *.
  set (nV := String.length s) in *.
  assert (HV : (2 <= (φ V) <= 400000)%Z) by lia.
  assert (HE : ((φ E) <= 400000)%Z) by lia.
  assert (HE1 : (1 <= (φ E))%Z) by lia.
  assert (HlD' : PArray.length xdst = E) by (apply to_Z_inj; rewrite HlD, HlS; lia).
  assert (Hsrc : forall k, ((φ k) < (φ E))%Z -> ((φ (xsrc.[k])) < (φ V))%Z).
  { intros k Hk. pose proof (HgS k Hk) as Hn. apply nth_error_In in Hn.
    rewrite Forall_forall in Hvisrc. specialize (Hvisrc _ Hn).
    pose proof (to_Z_bounded (xsrc.[k])). lia. }
  assert (Hdst : forall k, ((φ k) < (φ E))%Z -> ((φ (xdst.[k])) < (φ V))%Z).
  { intros k Hk. pose proof (HgD k ltac:(rewrite HlD'; exact Hk)) as Hn. apply nth_error_In in Hn.
    rewrite Forall_forall in Hvidst. specialize (Hvidst _ Hn).
    pose proof (to_Z_bounded (xdst.[k])). lia. }
  assert (Hedge : forall k, ((φ k) < (φ E))%Z ->
            edge src dst (Z.to_N (φ (xsrc.[k]))) (Z.to_N (φ (xdst.[k])))).
  { intros k Hk. exists (Z.to_nat (φ k)).
    split; [apply HgS; exact Hk | apply HgD; rewrite HlD'; exact Hk]. }
  assert (Hedge' : forall a b, edge src dst a b -> exists k, ((φ k) < (φ E))%Z /\
            Z.to_N (φ (xsrc.[k])) = a /\ Z.to_N (φ (xdst.[k])) = b).
  { intros a b (n & Ha & Hb).
    assert (Hn : (n < List.length src)%nat) by (apply nth_error_Some; rewrite Ha; discriminate).
    assert (Hk : (φ (of_Z (Z.of_nat n))) = Z.of_nat n) by (apply of_Z_small; lia).
    exists (of_Z (Z.of_nat n)). split; [lia|].
    pose proof (HgS (of_Z (Z.of_nat n)) ltac:(lia)) as A. rewrite Hk, Nat2Z.id, Ha in A.
    pose proof (HgD (of_Z (Z.of_nat n)) ltac:(rewrite HlD'; lia)) as B.
    rewrite Hk, Nat2Z.id, Hb in B.
    injection A as A. injection B as B. split; [symmetry; exact A | symmetry; exact B]. }
  (* the compressed rows *)
  assert (HV1 : (φ (V + 1)) = ((φ V) + 1)%Z) by (apply succ_small; lia).
  pose proof (cnt_loop_spec xsrc xdst V E eq_refl HlD' HE Hsrc _ 0 (PArray.make (V + 1) 0)
                (Zwf_well_founded 0 (mes 0)) eq_refl ltac:(change (φ 0) with 0%Z; lia)
                ltac:(rewrite alength_make_small; lia)
                ltac:(intros i Hi; rewrite aget_make; reflexivity)) as [C1l C1].
  set (c1 := cnt_loop xsrc E 0 (PArray.make (V + 1) 0) (Zwf_well_founded 0 (mes 0))) in *.
  pose proof (pre_loop_spec xsrc xdst V E eq_refl HlD' HV HE _ 0 c1
                (Zwf_well_founded 0 (mes 0)) eq_refl ltac:(change (φ 0) with 0%Z; lia) C1l)
    as PS.
  destruct PS as [C2l C2].
  { intros u Hu. rewrite C1 by exact Hu. change (φ 0) with 0%Z.
    destruct (Z.leb_spec (φ u) 0) as [L | L]; [|reflexivity].
    assert (Hu0 : (φ u) = 0%Z) by (pose proof (to_Z_bounded u); lia). rewrite Hu0.
    rewrite (lo_succ xsrc xdst V E eq_refl HlD' 0), (lo_0 xsrc xdst V E eq_refl HlD' HE Hsrc).
    reflexivity. }
  set (c2 := pre_loop V 0 c1 (Zwf_well_founded 0 (mes 0))) in *.
  pose proof (rfill_loop_spec xsrc xdst V E eq_refl HlD' HE Hsrc _ E c2 (PArray.make E 0)
                (Zwf_well_founded 0 (φ E)) eq_refl ltac:(lia) C2l
                ltac:(apply alength_make_small; lia)) as RS.
  destruct RS as (Ol & Al & Ooff & OC2 & OC3).
  { intros u Hu. rewrite C2 by exact Hu. apply (lo_succ xsrc xdst V E eq_refl HlD'). }
  { intros u j Hu Hj. rewrite C2 in Hj by lia. lia. }
  { intros k' Hk'. lia. }
  revert Ol Al Ooff OC2 OC3.
  destruct (rfill_loop xsrc xdst E c2 (PArray.make E 0) (Zwf_well_founded 0 (φ E))) as [off adj].
  cbn [fst snd]. intros Ol Al Ooff OC2 OC3.
  assert (Hoff0 : (φ (off.[0])) = 0%Z)
    by (rewrite Ooff by lia; exact (lo_0 xsrc xdst V E eq_refl HlD' HE Hsrc)).
  assert (HoffV : (φ (off.[V])) = (φ E))
    by (rewrite Ooff by lia; apply (lo_V xsrc xdst V E eq_refl HlD' HE Hsrc); lia).
  assert (Hmono : forall a b, ((φ a) <= (φ b) <= (φ V))%Z -> ((φ (off.[a])) <= (φ (off.[b])))%Z).
  { intros a b Hab. rewrite !Ooff by lia. apply (lo_mono xsrc xdst V E eq_refl HlD'). lia. }
  assert (Hrng : forall u j, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
            exists k', ((φ k') < (φ E))%Z /\ xsrc.[k'] = u /\ xdst.[k'] = adj.[j]).
  { intros u j Hu Hj. rewrite Ooff in Hj by lia.
    rewrite (Ooff (u + 1)) in Hj by (rewrite succ_small; lia).
    rewrite succ_small in Hj by lia. apply OC2; [exact Hu | exact Hj]. }
  assert (Hadj : forall j, ((φ j) < (φ E))%Z -> ((φ (adj.[j])) < (φ V))%Z).
  { intros j Hj. pose proof (to_Z_bounded j).
    destruct (owner_gen (lo xsrc (φ E)) (φ j) (Z.to_nat (φ V))
                ltac:(rewrite (lo_0 xsrc xdst V E eq_refl HlD' HE Hsrc); lia)
                ltac:(rewrite Z2Nat.id by lia;
                      rewrite (lo_V xsrc xdst V E eq_refl HlD' HE Hsrc) by lia; lia))
      as (m & Hm & Hlo).
    assert (Hm' : (φ (of_Z (Z.of_nat m))) = Z.of_nat m) by (apply of_Z_small; lia).
    destruct (OC2 (of_Z (Z.of_nat m)) j ltac:(lia) ltac:(rewrite Hm'; exact Hlo))
      as (k' & Hk' & _ & Hd). rewrite <- Hd. apply Hdst. exact Hk'. }
  assert (HC2 : forall u j, ((φ u) < (φ V))%Z -> ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
            edge src dst (Z.to_N (φ u)) (Z.to_N (φ (adj.[j])))).
  { intros u j Hu Hj. destruct (Hrng u j Hu Hj) as (k' & Hk' & Hs & Hd).
    rewrite <- Hs, <- Hd. apply Hedge. exact Hk'. }
  (* in-degrees and the initial queue *)
  pose proof (ind_loop_spec adj V E Al ltac:(lia) Hadj _ 0 (PArray.make V 0)
                (Zwf_well_founded 0 (mes 0)) eq_refl ltac:(change (φ 0) with 0%Z; lia)
                ltac:(apply alength_make_small; lia)
                ltac:(intros x Hx; rewrite aget_make; reflexivity)) as [Dl Dc].
  set (d := ind_loop adj E 0 (PArray.make V 0) (Zwf_well_founded 0 (mes 0))) in *.
  pose proof (q0_loop_spec V d ltac:(lia) _ 0 (PArray.make V 0) 0 (Zwf_well_founded 0 (mes 0))
                eq_refl ltac:(change (φ 0) with 0%Z; lia) ltac:(lia)
                ltac:(apply alength_make_small; lia)
                ltac:(intros i Hi; change (φ 0) with 0%Z in Hi; pose proof (to_Z_bounded i); lia)
                ltac:(intros i i' Hi; change (φ 0) with 0%Z in Hi; pose proof (to_Z_bounded i); lia)
                ltac:(intros y Hy; rewrite enqb_0; change (φ 0) with 0%Z; split;
                      [discriminate | intros [A _]; pose proof (to_Z_bounded y); lia]))
    as QS.
  revert QS.
  destruct (q0_loop V 0 d (PArray.make V 0) 0 (Zwf_well_founded 0 (mes 0))) as [q t].
  cbn [fst snd]. intros (Ql & Qt & Qb & Qi & Qe).
  (* walks *)
  set (Wk := fun (x : int) (z : Z) => exists p, walk src dst p /\ hd_error p = Some 0%N /\
               last p 0%N = Z.to_N (φ x) /\ wsum s p = z).
  assert (Hdst' : Forall (fun t => (t < N.of_nat nV)%N) dst) by exact Hvidst.
  assert (Hlen : forall p, walk src dst p -> hd_error p = Some 0%N -> (List.length p <= nV)%nat).
  { intros p W H0. destruct p as [|a p']; [discriminate|]. injection H0 as H0. subst a.
    apply nodup_len; [exact (walk_nodup src dst Hviac _ W)|].
    constructor; [lia | exact (walk_lt src dst _ Hdst' p' 0%N W)]. }
  assert (HW0 : Wk 0 0%Z).
  { exists [0%N]. split; [exact I|]. split; [reflexivity|]. split; [reflexivity|].
    simpl wsum. rewrite ?wm_0. try reflexivity. }
  assert (HWs : forall u z j, ((φ u) < (φ V))%Z -> Wk u z ->
            ((φ (off.[u])) <= (φ j) < (φ (off.[u + 1])))%Z ->
            Wk (adj.[j]) (z + Sint63.to_Z (wt xs V (adj.[j])))%Z).
  { intros u z j Hu (p & Wp & Hp0 & HpL & Hps) Hj.
    assert (HjE : ((φ j) < (φ E))%Z).
    { pose proof (Hmono (u + 1) V ltac:(rewrite succ_small; lia)). lia. }
    assert (Hne : p <> []) by (intro F; subst p; discriminate).
    exists (p ++ [Z.to_N (φ (adj.[j]))]). split.
    - apply (walk_snoc src dst p (Z.to_N (φ u))); [exact Hne | exact Wp | exact HpL |].
      apply HC2; [exact Hu | exact Hj].
    - split; [destruct p as [|a p]; [contradiction | exact Hp0]|].
      split; [apply last_last|].
      rewrite wsum_app. simpl wsum. rewrite Hps, Hwm by (apply Hadj; exact HjE). lia. }
  assert (HWb : forall x z, Wk x z -> (- (φ V) <= z <= (φ V))%Z).
  { intros x z (p & Wp & Hp0 & _ & Hps). subst z.
    pose proof (Hlen p Wp Hp0). pose proof (wsum_bound s p). lia. }
  assert (Hacyc := acyc_machine src dst V off adj HC2 Hviac).
  (* the main loop *)
  set (dist0 := (PArray.make V NEG).[0 <- 0]).
  assert (HmV : PArray.length (PArray.make V NEG) = V) by (apply alength_make_small; lia).
  assert (K0 : KInv V E adj Wk 0 (popd off q 0) d dist0 q t).
  { split; [exact Dl|]. split; [unfold dist0; rewrite alength_set; exact HmV|].
    split; [exact Ql|]. split; [change (φ 0) with 0%Z; pose proof (to_Z_bounded t); lia|].
    split; [exact Qb|]. split; [exact Qi|]. split; [exact Qe|].
    split.
    { intros x Hx. rewrite Dc by exact Hx. unfold unp. apply cnt_ext. intros z _.
      rewrite popd_0. simpl negb. rewrite Bool.andb_true_r. reflexivity. }
    split.
    { intros x Hx. unfold dist0. destruct (idec x 0) as [E0 | E0].
      - right. rewrite E0. rewrite aget_set_same by (rewrite HmV; lia). exact HW0.
      - left. rewrite aget_set_other by (intro F; apply E0; symmetry; exact F).
        apply aget_make. }
    unfold dist0. rewrite aget_set_same by (rewrite HmV; lia).
    change (Sint63.to_Z 0) with 0%Z. lia. }
  pose proof (kahn_spec xs V E off adj Wk HV HE Al Hoff0 HoffV Hmono Hadj
                (fun v _ => wt_bound xs V v) HWs HWb Hacyc _ 0 d dist0 q t (Zwf_well_founded 0 (mes 0))
                eq_refl K0
                ltac:(intros i Hi; change (φ 0) with 0%Z in Hi; pose proof (to_Z_bounded i); lia))
    as (Rl & Rr & Rs & R0).
  set (r := kahn_loop xs V off adj 0 d dist0 q t (Zwf_well_founded 0 (mes 0))) in *.
  (* every walk from 0 is beaten by the distances *)
  assert (Hreach : forall x, ((φ x) < (φ V))%Z -> r.[x] <> NEG ->
            (- (φ V) <= Sint63.to_Z (r.[x]))%Z).
  { intros x Hx Hn. destruct (Rs x Hx) as [F | W]; [contradiction|].
    pose proof (HWb _ _ W). lia. }
  assert (OPT : forall p a, walk src dst (a :: p) -> (a < N.of_nat nV)%N ->
            r.[of_Z (Z.of_N a)] <> NEG ->
            (Sint63.to_Z (r.[of_Z (Z.of_N a)]) + wsum s p
               <= Sint63.to_Z (r.[of_Z (Z.of_N (last (a :: p) 0%N))]))%Z /\
            r.[of_Z (Z.of_N (last (a :: p) 0%N))] <> NEG).
  { intros p. induction p as [|b p IH]; intros a W Ha Hn.
    - simpl. split; [lia | exact Hn].
    - destruct W as [Eab W']. destruct (Hedge' a b Eab) as (k & Hk & Ea & Eb).
      assert (Hia : (φ (of_Z (Z.of_N a))) = Z.of_N a) by (apply of_Z_small; lia).
      assert (Hxa : xsrc.[k] = of_Z (Z.of_N a)).
      { apply to_Z_inj. rewrite Hia, <- Ea. pose proof (to_Z_bounded (xsrc.[k])). lia. }
      assert (Hb : (b < N.of_nat nV)%N) by (rewrite <- Eb; pose proof (Hdst k Hk); lia).
      assert (Hib : (φ (of_Z (Z.of_N b))) = Z.of_N b) by (apply of_Z_small; lia).
      assert (Hxb : xdst.[k] = of_Z (Z.of_N b)).
      { apply to_Z_inj. rewrite Hib, <- Eb. pose proof (to_Z_bounded (xdst.[k])). lia. }
      destruct (OC3 k Hk) as (j & Hj & Haj). rewrite Hxa, Hia in Hj.
      rewrite Hxb in Haj.
      assert (Hrg : ((φ (off.[of_Z (Z.of_N a)])) <= (φ j) < (φ (off.[of_Z (Z.of_N a) + 1])))%Z).
      { rewrite Ooff by lia. rewrite (Ooff (of_Z (Z.of_N a) + 1)) by (rewrite succ_small; lia).
        rewrite succ_small by lia. rewrite Hia. exact Hj. }
      pose proof (Rr (of_Z (Z.of_N a)) ltac:(lia) Hn j Hrg) as Rx.
      rewrite Haj in Rx. rewrite Hwm in Rx by lia.
      replace (Z.to_N (φ (of_Z (Z.of_N b)))) with b in Rx by (rewrite Hib; lia).
      pose proof (Hreach (of_Z (Z.of_N a)) ltac:(lia) Hn) as Ba.
      pose proof (wm_bound s b) as Bb.
      assert (Hnb : r.[of_Z (Z.of_N b)] <> NEG).
      { intro F. rewrite F, NEG_val in Rx. lia. }
      destruct (IH b W' Hb Hnb) as [I1 I2].
      change (last (a :: b :: p) 0%N) with (last (b :: p) 0%N). simpl wsum.
      split; [lia | exact I2]. }
  assert (Hn0 : r.[0] <> NEG) by (intro F; rewrite F, NEG_val in R0; lia).
  assert (HiV : of_Z (Z.of_N (N.of_nat nV - 1)) = V - 1).
  { apply to_Z_inj. rewrite of_Z_small by lia. rewrite sub1 by lia. lia. }
  destruct Hvipath as (p & Wp & Hp0 & HpL).
  destruct p as [|a p']; [discriminate|]. injection Hp0 as Ha0. subst a.
  destruct (OPT p' 0%N Wp ltac:(lia) Hn0) as [_ O2].
  unfold slen in HpL. fold nV in HpL. rewrite HpL, HiV in O2.
  split.
  - destruct (Rs (V - 1) ltac:(rewrite sub1; lia)) as [F | (q' & Wq & Hq0 & HqL & Hqs)];
      [contradiction|].
    exists q'. split.
    + split; [exact Wq|]. split; [exact Hq0|]. rewrite HqL. unfold slen. fold nV.
      rewrite sub1 by lia. lia.
    + rewrite happiness_wsum. exact Hqs.
  - intros p0 (W0 & H00 & HL0). rewrite happiness_wsum.
    destruct p0 as [|a p0']; [discriminate|]. injection H00 as Ha0. subst a.
    destruct (OPT p0' 0%N W0 ltac:(lia) Hn0) as [P1 _].
    unfold slen in HL0. fold nV in HL0. rewrite HL0, HiV in P1.
    change (of_Z (Z.of_N 0)) with 0 in P1. simpl wsum. rewrite ?wm_0. lia.
Qed.

Lemma excavator_impl_correct :
  forall (s : string) (src dst : list N)
         (xs : PrimString.string) (xsrc xdst : array uint),
  valid_input s src dst -> repr xs s -> repr xsrc src -> repr xdst dst ->
  exists h : Z, repr (excavator_impl xs xsrc xdst : sint) h /\ excavator_spec s src dst h.
Proof.
  intros s src dst xs xsrc xdst Hv Hxs Hs Hd.
  destruct (repr_str xs s Hxs) as [HlX HgX].
  destruct (repr_arr xsrc src Hs) as [HlS HgS].
  destruct (repr_arr xdst dst Hd) as [HlD HgD].
  exists (Sint63.to_Z (excavator_impl xs xsrc xdst)). split; [reflexivity|].
  exact (main_aux s src dst xs xsrc xdst Hv HlX HgX HlS HgS HlD HgD).
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition excavator : PrimString.string -> array uint -> array uint -> sint :=
  excavator_impl.

Definition excavator_correct :
  forall (s : string) (src dst : list N)
         (xs : PrimString.string) (xsrc xdst : array uint),
  valid_input s src dst -> repr xs s -> repr xsrc src -> repr xdst dst ->
  exists h : Z, repr (excavator xs xsrc xdst) h /\ excavator_spec s src dst h
  := excavator_impl_correct.
