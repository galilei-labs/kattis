(* Implementation of water (water.spec): incremental Edmonds-Karp. *)

From Water.spec Require Import Prelude.
From StdGalilei Require Import repr.
From Stdlib Require Import ZArith NArith List Bool Uint63 PArray ZifyUint63 Lia Zwf.
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

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* Vertices are the stations 1..n themselves; the residual network is the
   flat (n+1)*(n+1) array r, cell u*m+v (m = n+1), row and column 0
   unused.  r.[u*m+v] = cap(u,v) - f(u,v). *)

(* Adds capacity c between a and b (both directions). *)
Definition add_pipe (m : int) (r : array int) (a b c : int) : array int :=
  let i1 := a * m + b in
  let r1 := r.[i1 <- r.[i1] + c] in
  let i2 := b * m + a in
  r1.[i2 <- r1.[i2] + c].

Fixpoint init_loop (pa pb pc : array int) (m p j : int) (r : array int)
    (H : Acc (Zwf 0) (gap p j)) {struct H} : array int :=
  match bdec (j <? p) with
  | left Hj =>
      init_loop pa pb pc m p (j + 1) (add_pipe m r pa.[j] pb.[j] pc.[j])
        (Acc_inv H (dec_step p j Hj))
  | right _ => r
  end.

Definition big : int := 4611686018427387903.

(* Scans the neighbours v (from v up to n) of the dequeued vertex u. *)
Fixpoint scan (r : array int) (m u bu v : int) (par bott q : array int)
    (tail : int) (H : Acc (Zwf 0) (gap m v)) {struct H}
    : array int * array int * array int * int :=
  match bdec (v <? m) with
  | left Hv =>
      let x := r.[u * m + v] in
      if (par.[v] =? 0) && (0 <? x) then
        scan r m u bu (v + 1) par.[v <- u]
          bott.[v <- if bu <? x then bu else x] q.[tail <- v] (tail + 1)
          (Acc_inv H (dec_step m v Hv))
      else
        scan r m u bu (v + 1) par bott q tail (Acc_inv H (dec_step m v Hv))
  | right _ => (par, bott, q, tail)
  end.

Fixpoint bfs_loop (r : array int) (m head : int) (par bott q : array int)
    (tail : int) (H : Acc (Zwf 0) (gap m head)) {struct H}
    : array int * array int :=
  match bdec (head <? m) with
  | left Hh =>
      if (head <? tail) && (par.[2] =? 0) then
        let u := q.[head] in
        match scan r m u bott.[u] 1 par bott q tail
                (Zwf_well_founded 0 (gap m 1)) with
        | (par', bott', q', tail') =>
            bfs_loop r m (head + 1) par' bott' q' tail'
              (Acc_inv H (dec_step m head Hh))
        end
      else (par, bott)
  | right _ => (par, bott)
  end.

(* par.[v] = 0: v not reached; par.[1] = 1; otherwise the BFS parent.
   bott.[v]: the bottleneck of the tree path from 1 to v. *)
Definition bfs (r : array int) (m : int) : array int * array int :=
  bfs_loop r m 0 (PArray.make m 0).[1 <- 1] (PArray.make m 0).[1 <- big]
    (PArray.make m 0).[0 <- 1] 1 (Zwf_well_founded 0 (gap m 0)).

(* Pushes d units along the tree path from cur back to 1. *)
Fixpoint walk (par : array int) (m d : int) (r : array int) (cur i : int)
    (H : Acc (Zwf 0) (gap m i)) {struct H} : array int :=
  match bdec (i <? m) with
  | left Hi =>
      if cur =? 1 then r
      else
        let u := par.[cur] in
        let i1 := u * m + cur in
        let r1 := r.[i1 <- r.[i1] - d] in
        let i2 := cur * m + u in
        let r2 := r1.[i2 <- r1.[i2] + d] in
        walk par m d r2 u (i + 1) (Acc_inv H (dec_step m i Hi))
  | right _ => r
  end.

(* Augments along shortest paths until 2 is unreachable. *)
Fixpoint augment (m B : int) (r : array int) (val i : int)
    (H : Acc (Zwf 0) (gap B i)) {struct H} : array int * int :=
  match bdec (i <? B) with
  | left Hi =>
      match bfs r m with
      | (par, bott) =>
          if par.[2] =? 0 then (r, val)
          else
            let d := bott.[2] in
            augment m B (walk par m d r 2 0 (Zwf_well_founded 0 (gap m 0)))
              (val + d) (i + 1) (Acc_inv H (dec_step B i Hi))
      end
  | right _ => (r, val)
  end.

Definition budget : int := 1099511627776.

Fixpoint imp_loop (ia ib ic : array int) (m k t : int) (r : array int)
    (val : int) (out : array int) (H : Acc (Zwf 0) (gap k t)) {struct H}
    : array int :=
  match bdec (t <? k) with
  | left Ht =>
      let r1 := add_pipe m r ia.[t] ib.[t] ic.[t] in
      match augment m budget r1 val 0 (Zwf_well_founded 0 (gap budget 0)) with
      | (r2, val2) =>
          imp_loop ia ib ic m k (t + 1) r2 val2 out.[t + 1 <- val2]
            (Acc_inv H (dec_step k t Ht))
      end
  | right _ => out
  end.

Definition water_impl (n : int) (pa pb pc ia ib ic : array int) : array int :=
  let m := n + 1 in
  let p := PArray.length pa in
  let r := init_loop pa pb pc m p 0 (PArray.make (m * m) 0)
             (Zwf_well_founded 0 (gap p 0)) in
  match augment m budget r 0 0 (Zwf_well_founded 0 (gap budget 0)) with
  | (r1, v0) =>
      let k := PArray.length ia in
      imp_loop ia ib ic m k 0 r1 v0 (PArray.make (k + 1) 0).[0 <- v0]
        (Zwf_well_founded 0 (gap k 0))
  end.

(* ------------------------------------------------------------------ *)
(* Prop side: sums over the stations                                   *)
(* ------------------------------------------------------------------ *)

Lemma ss_S : forall g m,
  sum_stations g (S m) = (sum_stations g m + g (N.of_nat (S m)))%Z.
Proof. reflexivity. Qed.

Lemma ss_ext : forall g h m,
  (forall x, (1 <= x <= N.of_nat m)%N -> g x = h x) ->
  sum_stations g m = sum_stations h m.
Proof.
  intros g h m. induction m as [| m IH]; intros H; [reflexivity|].
  rewrite !ss_S. rewrite IH by (intros x Hx; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma ss_add : forall g h m,
  sum_stations (fun x => g x + h x)%Z m = (sum_stations g m + sum_stations h m)%Z.
Proof. intros g h m. induction m as [| m IH]; simpl; lia. Qed.

Lemma ss_opp : forall g m,
  sum_stations (fun x => - g x)%Z m = (- sum_stations g m)%Z.
Proof. intros g m. induction m as [| m IH]; simpl; lia. Qed.

Lemma ss_const : forall c m,
  sum_stations (fun _ => c) m = (Z.of_nat m * c)%Z.
Proof.
  intros c m. induction m as [| m IH]; [reflexivity|].
  rewrite ss_S, IH, Nat2Z.inj_succ, Z.mul_succ_l. reflexivity.
Qed.

Lemma ss_zero : forall g m,
  (forall x, (1 <= x <= N.of_nat m)%N -> g x = 0%Z) -> sum_stations g m = 0%Z.
Proof.
  intros g m H. rewrite (ss_ext g (fun _ => 0%Z)) by exact H.
  rewrite ss_const. lia.
Qed.

Lemma ss_le : forall g h m,
  (forall x, (1 <= x <= N.of_nat m)%N -> (g x <= h x)%Z) ->
  (sum_stations g m <= sum_stations h m)%Z.
Proof.
  intros g h m. induction m as [| m IH]; intros H; [simpl; lia|].
  rewrite !ss_S.
  specialize (IH ltac:(intros x Hx; apply H; lia)).
  specialize (H (N.of_nat (S m)) ltac:(lia)). lia.
Qed.

Lemma ss_point : forall g m p,
  (1 <= p <= N.of_nat m)%N ->
  (forall x, (1 <= x <= N.of_nat m)%N -> x <> p -> g x = 0%Z) ->
  sum_stations g m = g p.
Proof.
  intros g m. induction m as [| m IH]; intros p Hp H; [lia|].
  rewrite ss_S. destruct (N.eq_dec p (N.of_nat (S m))) as [E | E].
  - subst p. rewrite ss_zero; [lia|].
    intros x Hx. apply H; lia.
  - rewrite (IH p) by (try lia; intros x Hx Hxp; apply H; lia).
    rewrite (H (N.of_nat (S m))) by lia. lia.
Qed.

Lemma ss_swap : forall (h : N -> N -> Z) m m',
  sum_stations (fun u => sum_stations (fun v => h u v) m) m'
  = sum_stations (fun v => sum_stations (fun u => h u v) m') m.
Proof.
  intros h m m'. induction m' as [| m' IH]; simpl.
  - symmetry. apply ss_zero. reflexivity.
  - rewrite IH. rewrite <- ss_add. reflexivity.
Qed.

(* The value of a flow is what crosses any cut (S, not S) separating 1
   from 2. *)
Lemma cut_identity : forall n cap g (S : N -> bool),
  is_flow n cap g -> S 1%N = true -> S 2%N = false -> (2 <= n)%N ->
  net_out n g 1 =
  sum_stations (fun u => if S u then
     sum_stations (fun v => if S v then 0%Z else g u v) (N.to_nat n)
     else 0%Z) (N.to_nat n).
Proof.
  intros n cap g S [Hanti [_ Hcons]] HS1 HS2 Hn.
  set (m := N.to_nat n).
  assert (Hm : N.of_nat m = n) by (unfold m; lia).
  set (h := fun u v => if S u then if S v then g u v else 0%Z else 0%Z).
  set (D := sum_stations (fun u => sum_stations (fun v => h u v) m) m).
  assert (HD : D = 0%Z).
  { assert (E : D = (- D)%Z).
    { unfold D at 1. rewrite ss_swap.
      rewrite (ss_ext _ (fun v => - sum_stations (fun u => h v u) m)%Z).
      - rewrite ss_opp. reflexivity.
      - intros v Hv. rewrite <- ss_opp. apply ss_ext. intros u Hu.
        unfold h. destruct (S u), (S v); try reflexivity.
        apply Hanti; unfold station; lia. }
    lia. }
  transitivity (sum_stations (fun u => if S u then net_out n g u else 0%Z) m).
  - symmetry. rewrite (ss_point _ m 1%N).
    2: lia.
    2: { intros x Hx Hx1. destruct (S x) eqn:E; [|reflexivity].
         apply Hcons; [unfold station; lia | exact Hx1 | intro F; rewrite F in E; congruence]. }
    rewrite HS1. reflexivity.
  - rewrite (ss_ext _ (fun u => sum_stations (fun v => h u v) m +
       (if S u then sum_stations (fun v => if S v then 0 else g u v) m else 0))%Z).
    + rewrite ss_add. fold D. rewrite HD. reflexivity.
    + intros u Hu. unfold h, net_out. fold m. destruct (S u).
      * rewrite <- ss_add. apply ss_ext. intros v Hv. destruct (S v); lia.
      * rewrite ss_zero; reflexivity.
Qed.

Lemma cut_bound : forall n cap g (S : N -> bool),
  is_flow n cap g -> S 1%N = true -> S 2%N = false -> (2 <= n)%N ->
  (net_out n g 1 <=
  sum_stations (fun u => if S u then
     sum_stations (fun v => if S v then 0%Z else Z.of_N (cap u v)) (N.to_nat n)
     else 0%Z) (N.to_nat n))%Z.
Proof.
  intros n cap g S Hf HS1 HS2 Hn.
  rewrite (cut_identity n cap g S Hf HS1 HS2 Hn).
  destruct Hf as [_ [Hcap _]].
  apply ss_le. intros u Hu. destruct (S u); [|lia].
  apply ss_le. intros v Hv. destruct (S v); [lia|].
  apply Hcap; unfold station; lia.
Qed.

(* Pigeonhole: t distinct stations. *)
Lemma pigeon : forall (t : nat) (g : nat -> N) (n : N),
  (forall i, (i < t)%nat -> (1 <= g i <= n)%N) ->
  (forall i j, (i < t)%nat -> (j < t)%nat -> g i = g j -> i = j) ->
  (N.of_nat t <= n)%N.
Proof.
  intros t g n Hr Hi.
  set (l := map (fun i => N.to_nat (g i)) (seq 0 t)).
  assert (Hnd : NoDup l).
  { apply NoDup_map_NoDup_ForallPairs; [|apply seq_NoDup].
    intros a b Ha Hb E. apply in_seq in Ha, Hb. apply Hi; try lia. }
  assert (Hincl : incl l (seq 1 (N.to_nat n))).
  { intros x Hx. unfold l in Hx. apply in_map_iff in Hx.
    destruct Hx as (i & <- & Hin). apply in_seq in Hin.
    apply in_seq. specialize (Hr i ltac:(lia)). lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as HL.
  unfold l in HL. rewrite length_map, !length_seq in HL. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Uint63 / PArray plumbing                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
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

Definition nv (x : int) : N := Z.to_N (φ x).

Lemma Zof_nv : forall x, Z.of_N (nv x) = (φ x).
Proof. intros x. unfold nv. rewrite Z2N.id; [reflexivity | apply to_Z_bounded]. Qed.

Lemma of_Z_nv : forall x : int, of_Z (Z.of_N (nv x)) = x.
Proof. intros x. rewrite Zof_nv. apply of_to_Z. Qed.

Lemma nv_inj : forall x y, nv x = nv y -> x = y.
Proof. intros x y E. rewrite <- (of_Z_nv x), <- (of_Z_nv y), E. reflexivity. Qed.

(* The cell u of a one-dimensional table. *)
Definition cell (a : array int) (u : N) : Z := (φ (a.[of_Z (Z.of_N u)])).

Lemma cell_int : forall a x, cell a (nv x) = (φ (a.[x])).
Proof. intros a x. unfold cell. rewrite of_Z_nv. reflexivity. Qed.

Lemma cell_nonneg : forall a u, (0 <= cell a u)%Z.
Proof. intros a u. unfold cell. apply to_Z_bounded. Qed.

Lemma cell_set : forall a x e u,
  ((φ x) < (φ (PArray.length a)))%Z -> (Z.of_N u < wB)%Z ->
  cell (a.[x <- e]) u = if (u =? nv x)%N then (φ e) else cell a u.
Proof.
  intros a x e u Hx Hu. unfold cell. destruct (N.eqb_spec u (nv x)) as [E | E].
  - subst u. rewrite of_Z_nv. rewrite aget_set_same; [reflexivity|].
    rewrite ltb_spec. exact Hx.
  - rewrite aget_set_other; [reflexivity|].
    intro F. apply E. rewrite F. unfold nv. rewrite of_Z_spec, Z.mod_small by lia.
    lia.
Qed.

Lemma idx_inj : forall M A B X Y : Z,
  (0 <= B < M)%Z -> (0 <= Y < M)%Z -> (0 <= A)%Z -> (0 <= X)%Z ->
  (A * M + B = X * M + Y)%Z -> A = X /\ B = Y.
Proof.
  intros M A B X Y HB HY HA HX E.
  assert (A = X) by nia. subst. lia.
Qed.

Lemma small_idx : forall X Y M : Z,
  (0 <= X < M)%Z -> (0 <= Y < M)%Z -> (M <= 101)%Z ->
  (0 <= X * M)%Z /\ (X * M + Y < M * M)%Z /\ (M * M <= 10201)%Z.
Proof. intros X Y M HX HY HM. nia. Qed.

Section Net.

Variable n : N.
Variable m : int.
Hypothesis Hm : (φ m) = (Z.of_N n + 1)%Z.
Hypothesis Hn : (2 <= n <= 100)%N.

(* The residual capacity from u to v. *)
Definition Rs (r : array int) (u v : N) : Z :=
  (φ (r.[of_Z (Z.of_N u * (φ m) + Z.of_N v)])).

Lemma Rs_nonneg : forall r u v, (0 <= Rs r u v)%Z.
Proof. intros r u v. unfold Rs. apply to_Z_bounded. Qed.

Lemma idx_eq : forall x y, ((φ x) < (φ m))%Z -> ((φ y) < (φ m))%Z ->
  x * m + y = of_Z (Z.of_N (nv x) * (φ m) + Z.of_N (nv y)).
Proof.
  intros x y Hx Hy. rewrite !Zof_nv. apply to_Z_inj.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  pose proof (small_idx (φ x) (φ y) (φ m) ltac:(lia) ltac:(lia) ltac:(lia)).
  rewrite of_Z_spec, add_spec, mul_spec, wB_val.
  rewrite !(Z.mod_small ((φ x) * (φ m))) by lia.
  rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma Rs_int : forall r x y, ((φ x) < (φ m))%Z -> ((φ y) < (φ m))%Z ->
  (φ (r.[x * m + y])) = Rs r (nv x) (nv y).
Proof. intros r x y Hx Hy. unfold Rs. rewrite idx_eq by assumption. reflexivity. Qed.

Lemma Rs_set : forall r x y e a b,
  ((φ x) < (φ m))%Z -> ((φ y) < (φ m))%Z ->
  (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  (Z.of_N a < (φ m))%Z -> (Z.of_N b < (φ m))%Z ->
  Rs (r.[x * m + y <- e]) a b
  = if (a =? nv x)%N && (b =? nv y)%N then (φ e) else Rs r a b.
Proof.
  intros r x y e a b Hx Hy Hl Ha Hb. unfold Rs. rewrite idx_eq by assumption.
  pose proof (to_Z_bounded x). pose proof (to_Z_bounded y).
  pose proof (small_idx (φ x) (φ y) (φ m) ltac:(lia) ltac:(lia) ltac:(lia)).
  pose proof (small_idx (Z.of_N a) (Z.of_N b) (φ m) ltac:(lia) ltac:(lia) ltac:(lia)).
  destruct (N.eqb_spec a (nv x)) as [Ea | Ea];
  destruct (N.eqb_spec b (nv y)) as [Eb | Eb]; simpl.
  - subst a b. rewrite aget_set_same; [reflexivity|].
    rewrite ltb_spec, Hl, of_Z_spec, !Zof_nv, wB_val, Z.mod_small by lia. lia.
  - rewrite aget_set_other; [reflexivity|]. intro F.
    apply (f_equal to_Z) in F. rewrite !of_Z_spec, !Zof_nv, wB_val in F.
    rewrite !Z.mod_small in F by lia.
    apply idx_inj in F; try lia. apply Eb. unfold nv. lia.
  - rewrite aget_set_other; [reflexivity|]. intro F.
    apply (f_equal to_Z) in F. rewrite !of_Z_spec, !Zof_nv, wB_val in F.
    rewrite !Z.mod_small in F by lia.
    apply idx_inj in F; try lia. apply Ea. unfold nv. lia.
  - rewrite aget_set_other; [reflexivity|]. intro F.
    apply (f_equal to_Z) in F. rewrite !of_Z_spec, !Zof_nv, wB_val in F.
    rewrite !Z.mod_small in F by lia.
    apply idx_inj in F; try lia. apply Ea. unfold nv. lia.
Qed.

(* The flow carried by a residual table. *)
Definition Fl (cap : N -> N -> N) (r : array int) (u v : N) : Z :=
  (Z.of_N (cap u v) - Rs r u v)%Z.

Definition Cmax : Z := 15000000.

Definition capok (cap : N -> N -> N) : Prop :=
  (forall u v, cap u v = cap v u) /\
  (forall u v, station n u -> station n v -> (Z.of_N (cap u v) <= Cmax)%Z).

Record Inv (cap : N -> N -> N) (r : array int) (val : Z) : Prop := {
  inv_len : (φ (PArray.length r)) = ((φ m) * (φ m))%Z;
  inv_sym : forall u v, station n u -> station n v ->
              (Rs r u v + Rs r v u = 2 * Z.of_N (cap u v))%Z;
  inv_cons : forall u, station n u -> u <> 1%N -> u <> 2%N ->
              net_out n (Fl cap r) u = 0%Z;
  inv_val : net_out n (Fl cap r) 1 = val
}.

Lemma Inv_flow : forall cap r val, capok cap -> Inv cap r val ->
  is_flow n cap (Fl cap r).
Proof.
  intros cap r val [Hs _] HI. split; [|split].
  - intros u v Hu Hv. unfold Fl. pose proof (inv_sym _ _ _ HI u v Hu Hv).
    rewrite (Hs v u). lia.
  - intros u v Hu Hv. unfold Fl. pose proof (Rs_nonneg r u v). lia.
  - intros u Hu H1 H2. exact (inv_cons _ _ _ HI u Hu H1 H2).
Qed.

Lemma Rs_bound : forall cap r val, capok cap -> Inv cap r val ->
  forall u v, station n u -> station n v -> (Rs r u v <= 2 * Cmax)%Z.
Proof.
  intros cap r val [_ Hb] HI u v Hu Hv.
  pose proof (inv_sym _ _ _ HI u v Hu Hv). pose proof (Rs_nonneg r v u).
  pose proof (Hb u v Hu Hv). lia.
Qed.

Lemma val_bound : forall cap r val, capok cap -> Inv cap r val ->
  (val <= 100 * Cmax)%Z.
Proof.
  intros cap r val [_ Hb] HI. rewrite <- (inv_val _ _ _ HI). unfold net_out.
  eapply Z.le_trans.
  - apply (ss_le _ (fun _ => Cmax)). intros v Hv. unfold Fl.
    pose proof (Rs_nonneg r 1 v). pose proof (Hb 1%N v ltac:(unfold station; lia)
      ltac:(unfold station; lia)). lia.
  - rewrite ss_const. unfold Cmax. lia.
Qed.

Lemma Inv_ext : forall cap cap' r val,
  (forall u v, station n u -> station n v -> cap u v = cap' u v) ->
  Inv cap r val -> Inv cap' r val.
Proof.
  intros cap cap' r val E HI.
  assert (Hnet : forall u, station n u ->
            net_out n (Fl cap' r) u = net_out n (Fl cap r) u).
  { intros u Hu. unfold net_out. apply ss_ext. intros v Hv. unfold Fl.
    rewrite E; [reflexivity | exact Hu | unfold station; lia]. }
  constructor.
  - exact (inv_len _ _ _ HI).
  - intros u v Hu Hv. rewrite <- E by assumption. exact (inv_sym _ _ _ HI u v Hu Hv).
  - intros u Hu H1 H2. rewrite Hnet by assumption. exact (inv_cons _ _ _ HI u Hu H1 H2).
  - rewrite Hnet by (clear - Hn; unfold station; lia). exact (inv_val _ _ _ HI).
Qed.

(* A flow that saturates a cut is maximum. *)
Lemma Inv_maxflow : forall cap r val (S : N -> bool),
  capok cap -> Inv cap r val -> S 1%N = true -> S 2%N = false ->
  (forall u v, station n u -> station n v -> S u = true -> S v = false ->
     Rs r u v = 0%Z) ->
  (0 <= val)%Z ->
  max_flow n cap (Z.to_N val).
Proof.
  intros cap r val S Hc HI HS1 HS2 Hcut Hv.
  pose proof (Inv_flow cap r val Hc HI) as Hf.
  split.
  - exists (Fl cap r). split; [exact Hf|]. rewrite Z2N.id by exact Hv.
    exact (inv_val _ _ _ HI).
  - intros g Hg. rewrite Z2N.id by exact Hv. rewrite <- (inv_val _ _ _ HI).
    rewrite (cut_identity n cap (Fl cap r) S Hf HS1 HS2 ltac:(lia)).
    eapply Z.le_trans; [apply (cut_bound n cap g S Hg HS1 HS2 ltac:(lia))|].
    apply ss_le. intros u Hu. destruct (S u) eqn:Su; [|lia].
    apply ss_le. intros v Hv'. destruct (S v) eqn:Sv; [lia|].
    unfold Fl. rewrite Hcut; [lia | unfold station; lia | unfold station; lia
      | exact Su | exact Sv].
Qed.


(* ------------------------------------------------------------------ *)
(* Adding a pipe                                                       *)
(* ------------------------------------------------------------------ *)

Definition pterm (a b c u v : N) : N :=
  if (a =? u)%N && (b =? v)%N || (a =? v)%N && (b =? u)%N then c else 0%N.

Lemma pterm_sym : forall a b c u v, pterm a b c u v = pterm a b c v u.
Proof. intros. unfold pterm. rewrite orb_comm. reflexivity. Qed.

Lemma station_lt : forall u, station n u -> (Z.of_N u < (φ m))%Z.
Proof. intros u Hu. unfold station in Hu. lia. Qed.

Lemma station_int : forall x, station n (nv x) -> ((φ x) < (φ m))%Z.
Proof. intros x Hx. apply station_lt in Hx. rewrite Zof_nv in Hx. exact Hx. Qed.

Ltac eqbs := repeat match goal with
  | |- context [(?x =? ?y)%N] => destruct (N.eqb_spec x y)
  end.

Lemma Rs_add_pipe : forall r xa xb xc a b,
  (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  station n (nv xa) -> station n (nv xb) -> nv xa <> nv xb ->
  station n a -> station n b ->
  (Rs r (nv xa) (nv xb) + (φ xc) < wB)%Z ->
  (Rs r (nv xb) (nv xa) + (φ xc) < wB)%Z ->
  Rs (add_pipe m r xa xb xc) a b
  = (Rs r a b + Z.of_N (pterm (nv xa) (nv xb) (nv xc) a b))%Z.
Proof.
  intros r xa xb xc a b Hl Ha Hb Hab Sa Sb O1 O2.
  pose proof (station_int _ Ha) as Ia. pose proof (station_int _ Hb) as Ib.
  pose proof (station_lt _ Sa). pose proof (station_lt _ Sb).
  cbv beta zeta delta [add_pipe].
  assert (E1 : (φ (r.[xa * m + xb] + xc)) = (Rs r (nv xa) (nv xb) + (φ xc))%Z).
  { rewrite add_spec, Rs_int by assumption. pose proof (Rs_nonneg r (nv xa) (nv xb)).
    pose proof (to_Z_bounded xc). rewrite Z.mod_small by lia. reflexivity. }
  set (r1 := r.[xa * m + xb <- r.[xa * m + xb] + xc]).
  assert (L1 : (φ (PArray.length r1)) = ((φ m) * (φ m))%Z) by (unfold r1; rewrite alength_set; exact Hl).
  assert (R1 : forall u v, (Z.of_N u < (φ m))%Z -> (Z.of_N v < (φ m))%Z ->
     Rs r1 u v = if (u =? nv xa)%N && (v =? nv xb)%N
                 then (Rs r (nv xa) (nv xb) + (φ xc))%Z else Rs r u v).
  { intros u v Hu Hv. unfold r1. rewrite Rs_set by assumption. rewrite E1. reflexivity. }
  assert (E2 : (φ (r1.[xb * m + xa] + xc)) = (Rs r (nv xb) (nv xa) + (φ xc))%Z).
  { rewrite add_spec, Rs_int by assumption. rewrite R1 by (rewrite Zof_nv; assumption).
    destruct (N.eqb_spec (nv xb) (nv xa)); [congruence|]. simpl.
    pose proof (Rs_nonneg r (nv xb) (nv xa)).
    pose proof (to_Z_bounded xc). rewrite Z.mod_small by lia. reflexivity. }
  rewrite Rs_set by assumption. rewrite E2, R1 by assumption.
  unfold pterm. rewrite <- (Zof_nv xc).
  eqbs; simpl; subst; try congruence; try lia.
Qed.

Lemma add_pipe_inv : forall cap r val xa xb xc,
  Inv cap r val ->
  station n (nv xa) -> station n (nv xb) -> nv xa <> nv xb ->
  capok (fun u v => (cap u v + pterm (nv xa) (nv xb) (nv xc) u v)%N) ->
  Inv (fun u v => (cap u v + pterm (nv xa) (nv xb) (nv xc) u v)%N)
      (add_pipe m r xa xb xc) val.
Proof.
  intros cap r val xa xb xc HI Ha Hb Hab Hc.
  destruct Hc as [_ Hcb].
  pose proof (inv_len _ _ _ HI) as Hl.
  pose proof (inv_sym _ _ _ HI (nv xa) (nv xb) Ha Hb) as S1.
  pose proof (inv_sym _ _ _ HI (nv xb) (nv xa) Hb Ha) as S2.
  pose proof (Hcb (nv xa) (nv xb) Ha Hb) as C1.
  pose proof (Hcb (nv xb) (nv xa) Hb Ha) as C2.
  assert (P1 : pterm (nv xa) (nv xb) (nv xc) (nv xa) (nv xb) = nv xc).
  { unfold pterm. rewrite !N.eqb_refl. reflexivity. }
  assert (P2 : pterm (nv xa) (nv xb) (nv xc) (nv xb) (nv xa) = nv xc).
  { rewrite pterm_sym. exact P1. }
  rewrite P1, N2Z.inj_add, Zof_nv in C1. rewrite P2, N2Z.inj_add, Zof_nv in C2.
  pose proof (Rs_nonneg r (nv xa) (nv xb)) as N1. pose proof (Rs_nonneg r (nv xb) (nv xa)) as N2.
  assert (O1 : (Rs r (nv xa) (nv xb) + (φ xc) < wB)%Z).
  { clear - S1 C1 N1 N2. rewrite wB_val. unfold Cmax in *.
    set (A := Rs r (nv xa) (nv xb)) in *. set (B := Rs r (nv xb) (nv xa)) in *.
    set (c := Z.of_N (cap (nv xa) (nv xb))) in *. lia. }
  assert (O2 : (Rs r (nv xb) (nv xa) + (φ xc) < wB)%Z).
  { clear - S2 C2 N1 N2. rewrite wB_val. unfold Cmax in *.
    set (A := Rs r (nv xa) (nv xb)) in *. set (B := Rs r (nv xb) (nv xa)) in *.
    set (c := Z.of_N (cap (nv xb) (nv xa))) in *. lia. }
  assert (Hnet : forall u, station n u ->
    net_out n (Fl (fun u v => (cap u v + pterm (nv xa) (nv xb) (nv xc) u v)%N)
                  (add_pipe m r xa xb xc)) u = net_out n (Fl cap r) u).
  { intros u Hu. unfold net_out. apply ss_ext. intros v Hv. unfold Fl.
    assert (Sv : station n v) by (clear - Hv; unfold station; lia).
    rewrite (Rs_add_pipe r xa xb xc u v Hl Ha Hb Hab Hu Sv O1 O2).
    rewrite N2Z.inj_add. ring. }
  constructor.
  - cbv beta zeta delta [add_pipe]. rewrite !alength_set. exact Hl.
  - intros u v Hu Hv.
    rewrite (Rs_add_pipe r xa xb xc u v Hl Ha Hb Hab Hu Hv O1 O2).
    rewrite (Rs_add_pipe r xa xb xc v u Hl Ha Hb Hab Hv Hu O1 O2).
    rewrite (pterm_sym _ _ _ v u), N2Z.inj_add.
    pose proof (inv_sym _ _ _ HI u v Hu Hv) as Hs. clear - Hs. lia.
  - intros u Hu H1 H2. rewrite Hnet by assumption. exact (inv_cons _ _ _ HI u Hu H1 H2).
  - rewrite Hnet by (clear - Hn; unfold station; lia). exact (inv_val _ _ _ HI).
Qed.

(* ------------------------------------------------------------------ *)
(* The breadth-first search                                            *)
(* ------------------------------------------------------------------ *)

Definition vis (par : array int) (u : N) : Prop := cell par u <> 0%Z.

(* the vertex at position i of the queue *)
Definition qat (q : array int) (i : Z) : N := Z.to_N (cell q (Z.to_N i)).

Record BInv (r par bott q : array int) (head tail : Z) (rk : N -> Z) : Prop := {
  bi_lpar : (φ (PArray.length par)) = (φ m);
  bi_lbott : (φ (PArray.length bott)) = (φ m);
  bi_lq : (φ (PArray.length q)) = (φ m);
  bi_ht : (0 <= head <= tail)%Z;
  bi_tn : (tail <= Z.of_N n)%Z;
  bi_src : vis par 1;
  bi_q : forall i, (0 <= i < tail)%Z ->
           station n (qat q i) /\ vis par (qat q i) /\ rk (qat q i) = i;
  bi_rk : forall v, station n v -> vis par v ->
           (0 <= rk v < tail)%Z /\ qat q (rk v) = v;
  bi_bpos : forall v, station n v -> vis par v -> (0 < cell bott v)%Z;
  bi_par : forall v, station n v -> v <> 1%N -> vis par v ->
           station n (Z.to_N (cell par v)) /\ vis par (Z.to_N (cell par v)) /\
           (rk (Z.to_N (cell par v)) < rk v)%Z /\
           (cell bott v <= Rs r (Z.to_N (cell par v)) v)%Z /\
           (cell bott v <= cell bott (Z.to_N (cell par v)))%Z;
  bi_closed : forall i, (0 <= i < head)%Z -> forall v, station n v ->
           (0 < Rs r (qat q i) v)%Z -> vis par v
}.

Lemma cell_set_st : forall a x e w,
  (φ (PArray.length a)) = (φ m) -> ((φ x) < (φ m))%Z -> station n w ->
  cell (a.[x <- e]) w = if (w =? nv x)%N then (φ e) else cell a w.
Proof.
  intros a x e w Hl Hx Hw. apply cell_set; [lia|].
  unfold station in Hw. rewrite wB_val. lia.
Qed.

Lemma qat_set : forall q tail v i,
  (φ (PArray.length q)) = (φ m) -> ((φ tail) < (φ m))%Z -> (0 <= i <= (φ tail))%Z ->
  qat (q.[tail <- v]) i = if (i =? (φ tail))%Z then nv v else qat q i.
Proof.
  intros q tail v i Hl Ht Hi. unfold qat. rewrite cell_set.
  - destruct (N.eqb_spec (Z.to_N i) (nv tail)) as [E | E];
    destruct (Z.eqb_spec i (φ tail)) as [E' | E']; try reflexivity.
    + exfalso. apply E'. unfold nv in E. lia.
    + exfalso. apply E. unfold nv. lia.
  - lia.
  - rewrite wB_val. pose proof (to_Z_bounded tail). lia.
Qed.

Lemma Z2N_phi_station : forall x, station n (nv x) -> (φ x) <> 0%Z.
Proof. intros x Hx. unfold station, nv in Hx. lia. Qed.

Lemma BInv_push : forall r par bott q head tail rk u v bu x,
  BInv r par bott q head (φ tail) rk -> (head < (φ tail))%Z ->
  qat q head = nv u -> (φ bu) = cell bott (nv u) ->
  station n (nv v) -> cell par (nv v) = 0%Z ->
  (φ x) = Rs r (nv u) (nv v) -> (0 < (φ x))%Z ->
  let par' := par.[v <- u] in
  let bott' := bott.[v <- if bu <? x then bu else x] in
  let q' := q.[tail <- v] in
  BInv r par' bott' q' head (φ (tail + 1))
     (fun w => if (w =? nv v)%N then (φ tail) else rk w)
  /\ qat q' head = nv u /\ (φ bu) = cell bott' (nv u) /\ (head < (φ (tail + 1)))%Z
  /\ (forall w, station n w -> vis par w -> vis par' w) /\ vis par' (nv v).
Proof.
  intros r par bott q head tail rk u v bu x HB Hht Hqu Hbu Hv Hv0 Hx Hx0.
  intros par' bott' q'.
  set (mn := if bu <? x then bu else x) in *.
  destruct HB as [Lp Lb Lq Ht Htn Hsrc Hq Hrk Hbp Hpar Hcl].
  pose proof (station_int _ Hv) as Iv.
  (* u: station, visited, rank head *)
  destruct (Hq head ltac:(lia)) as (Su & Vu & Ru). rewrite Hqu in Su, Vu, Ru.
  pose proof (station_int _ Su) as Iu.
  assert (Nuv : nv u <> nv v) by (intro E; rewrite E in Vu; contradiction).
  assert (Nv1 : nv v <> 1%N).
  { intro E. apply Hsrc. rewrite <- E. exact Hv0. }
  (* the new tail fits *)
  assert (Htn' : ((φ tail) + 1 <= Z.of_N n)%Z).
  { set (g := fun i : nat => if (Z.of_nat i <? (φ tail))%Z then qat q (Z.of_nat i) else nv v).
    assert (P := pigeon (S (Z.to_nat (φ tail))) g n).
    assert (Hg1 : forall i, (i < S (Z.to_nat (φ tail)))%nat -> (1 <= g i <= n)%N).
    { intros i Hi. unfold g. destruct (Z.ltb_spec (Z.of_nat i) (φ tail)).
      - destruct (Hq (Z.of_nat i) ltac:(lia)) as (S1 & _). exact S1.
      - exact Hv. }
    assert (Hg2 : forall i j, (i < S (Z.to_nat (φ tail)))%nat ->
                    (j < S (Z.to_nat (φ tail)))%nat -> g i = g j -> i = j).
    { intros i j Hi Hj E. unfold g in E.
      destruct (Z.ltb_spec (Z.of_nat i) (φ tail)), (Z.ltb_spec (Z.of_nat j) (φ tail)).
      - destruct (Hq (Z.of_nat i) ltac:(lia)) as (_ & _ & R1).
        destruct (Hq (Z.of_nat j) ltac:(lia)) as (_ & _ & R2).
        rewrite E in R1. lia.
      - destruct (Hq (Z.of_nat i) ltac:(lia)) as (_ & V1 & _).
        rewrite E in V1. contradiction.
      - destruct (Hq (Z.of_nat j) ltac:(lia)) as (_ & V1 & _).
        rewrite <- E in V1. contradiction.
      - lia. }
    specialize (P Hg1 Hg2). lia. }
  assert (Ht1 : (φ (tail + 1)) = ((φ tail) + 1)%Z) by (rewrite add_spec; change (φ 1) with 1%Z;
    rewrite Z.mod_small; [reflexivity | rewrite wB_val; lia]).
  assert (Itail : ((φ tail) < (φ m))%Z) by lia.
  (* cells of the new tables *)
  assert (Cp : forall w, station n w ->
            cell par' w = if (w =? nv v)%N then (φ u) else cell par w)
    by (intros w Hw; apply cell_set_st; assumption).
  assert (Cb : forall w, station n w ->
            cell bott' w = if (w =? nv v)%N then (φ mn) else cell bott w)
    by (intros w Hw; apply cell_set_st; assumption).
  assert (Cq : forall i, (0 <= i <= (φ tail))%Z ->
            qat q' i = if (i =? (φ tail))%Z then nv v else qat q i)
    by (intros i Hi; apply qat_set; assumption).
  assert (Hmn : (0 < (φ mn))%Z /\ ((φ mn) <= (φ bu))%Z /\ ((φ mn) <= (φ x))%Z).
  { pose proof (Hbp (nv u) Su Vu). unfold mn.
    destruct (bu <? x) eqn:E;
      [rewrite ltb_spec in E | rewrite <- not_true_iff_false, ltb_spec in E]; lia. }
  assert (Grow : forall w, station n w -> vis par w -> vis par' w).
  { intros w Hw Vw. unfold vis. rewrite Cp by exact Hw.
    destruct (N.eqb_spec w (nv v)); [|exact Vw].
    apply Z2N_phi_station. exact Su. }
  assert (Vv : vis par' (nv v)).
  { unfold vis. rewrite Cp, N.eqb_refl by exact Hv. apply Z2N_phi_station. exact Su. }
  assert (Back : forall w, station n w -> vis par' w -> w <> nv v -> vis par w).
  { intros w Hw Vw Nw. unfold vis in *. rewrite Cp in Vw by exact Hw.
    destruct (N.eqb_spec w (nv v)); [contradiction | exact Vw]. }
  assert (Nvis : forall w, vis par w -> w <> nv v)
    by (intros w Vw E; subst w; contradiction).
  split; [constructor|].
  - unfold par'. rewrite alength_set. exact Lp.
  - unfold bott'. rewrite alength_set. exact Lb.
  - unfold q'. rewrite alength_set. exact Lq.
  - lia.
  - lia.
  - apply Grow; [unfold station; lia | exact Hsrc].
  - intros i Hi. rewrite Ht1 in Hi. rewrite Cq by lia.
    destruct (Z.eqb_spec i (φ tail)) as [E | E].
    + rewrite N.eqb_refl. split; [exact Hv | split; [exact Vv | lia]].
    + destruct (Hq i ltac:(lia)) as (S1 & V1 & R1).
      split; [exact S1|]. split; [apply Grow; assumption|].
      destruct (N.eqb_spec (qat q i) (nv v)) as [E2 | E2];
        [rewrite E2 in V1; contradiction | exact R1].
  - intros w Hw Vw. rewrite Ht1.
    destruct (N.eqb_spec w (nv v)) as [E | E].
    + subst w. split; [lia|]. rewrite Cq by lia. rewrite Z.eqb_refl. reflexivity.
    + destruct (Hrk w Hw (Back w Hw Vw E)) as (R1 & Q1).
      split; [lia|]. rewrite Cq by lia.
      destruct (Z.eqb_spec (rk w) (φ tail)); [lia | exact Q1].
  - intros w Hw Vw. rewrite Cb by exact Hw.
    destruct (N.eqb_spec w (nv v)) as [E | E]; [lia|].
    exact (Hbp w Hw (Back w Hw Vw E)).
  - intros w Hw Hw1 Vw. cbv beta. rewrite (Cp w Hw).
    assert (B0 : (nv u =? nv v)%N = false) by (apply N.eqb_neq; exact Nuv).
    destruct (N.eqb_spec w (nv v)) as [E | E].
    + subst w. change (Z.to_N (φ u)) with (nv u).
      rewrite (Cb (nv v) Hv), (Cb (nv u) Su), N.eqb_refl, B0.
      split; [exact Su|]. split; [apply Grow; assumption|]. lia.
    + destruct (Hpar w Hw Hw1 (Back w Hw Vw E)) as (S1 & V1 & R1 & B1 & B2).
      set (p := Z.to_N (cell par w)) in *.
      assert (Bp : (p =? nv v)%N = false) by (apply N.eqb_neq; exact (Nvis _ V1)).
      assert (Bw : (w =? nv v)%N = false) by (apply N.eqb_neq; exact E).
      rewrite (Cb w Hw), (Cb p S1), Bp, Bw.
      split; [exact S1|]. split; [apply Grow; assumption|].
      split; [exact R1|]. split; assumption.
  - intros i Hi w Hw Hr. rewrite Cq in Hr by lia.
    destruct (Z.eqb_spec i (φ tail)) as [E | E]; [lia|].
    apply Grow; [exact Hw|]. exact (Hcl i Hi w Hw Hr).
  - split; [rewrite Cq by lia; destruct (Z.eqb_spec head (φ tail)); [lia | exact Hqu]|].
    split; [rewrite (Cb (nv u) Su), (proj2 (N.eqb_neq _ _) Nuv); exact Hbu|].
    split; [lia|]. split; assumption.
Qed.

Lemma scan_eq : forall r m u bu v par bott q tail H,
  scan r m u bu v par bott q tail H =
  match bdec (v <? m) with
  | left Hv =>
      let x := r.[u * m + v] in
      if (par.[v] =? 0) && (0 <? x) then
        scan r m u bu (v + 1) par.[v <- u]
          bott.[v <- if bu <? x then bu else x] q.[tail <- v] (tail + 1)
          (Acc_inv H (dec_step m v Hv))
      else
        scan r m u bu (v + 1) par bott q tail (Acc_inv H (dec_step m v Hv))
  | right _ => (par, bott, q, tail)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma bfs_loop_eq : forall r m head par bott q tail H,
  bfs_loop r m head par bott q tail H =
  match bdec (head <? m) with
  | left Hh =>
      if (head <? tail) && (par.[2] =? 0) then
        let u := q.[head] in
        match scan r m u bott.[u] 1 par bott q tail
                (Zwf_well_founded 0 (gap m 1)) with
        | (par', bott', q', tail') =>
            bfs_loop r m (head + 1) par' bott' q' tail'
              (Acc_inv H (dec_step m head Hh))
        end
      else (par, bott)
  | right _ => (par, bott)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma scan_spec : forall r, (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  forall u bu head (z : Z) v par bott q tail rk (H : Acc (Zwf 0) (gap m v)),
  gap m v = z ->
  BInv r par bott q head (φ tail) rk -> (head < (φ tail))%Z ->
  qat q head = nv u -> (φ bu) = cell bott (nv u) ->
  (1 <= (φ v))%Z ->
  (forall w, station n w -> (Z.of_N w < (φ v))%Z -> (0 < Rs r (nv u) w)%Z -> vis par w) ->
  forall par' bott' q' tail',
  scan r m u bu v par bott q tail H = (par', bott', q', tail') ->
  exists rk', BInv r par' bott' q' head (φ tail') rk' /\ (head < (φ tail'))%Z /\
    qat q' head = nv u /\
    (forall w, station n w -> (0 < Rs r (nv u) w)%Z -> vis par' w).
Proof.
  intros r Hr u bu head z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v par bott q tail rk H Hz HB Hht Hqu Hbu Hv1 Hcl par' bott' q' tail' Hres.
  rewrite scan_eq in Hres.
  destruct (bdec (v <? m)) as [Hv | Hv].
  - pose proof Hv as Hv'. rewrite ltb_spec in Hv'.
    assert (Hv2 : (φ (v + 1)) = ((φ v) + 1)%Z).
    { rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [reflexivity|].
      rewrite wB_val. lia. }
    assert (Sv : station n (nv v)) by (unfold station, nv; lia).
    destruct (bi_q _ _ _ _ _ _ _ HB head ltac:(pose proof (bi_ht _ _ _ _ _ _ _ HB); lia))
      as (Su & _).
    rewrite Hqu in Su.
    pose proof (station_int _ Su) as Iu.
    cbv zeta in Hres.
    destruct ((par.[v] =? 0) && (0 <? r.[u * m + v])) eqn:C.
    + apply andb_prop in C. destruct C as [C1 C2].
      rewrite eqb_spec in C1. rewrite ltb_spec in C2. change (φ 0) with 0%Z in C2.
      assert (Hv0 : cell par (nv v) = 0%Z) by (rewrite cell_int, C1; reflexivity).
      assert (Hx : (φ (r.[u * m + v])) = Rs r (nv u) (nv v)) by (apply Rs_int; lia).
      destruct (BInv_push r par bott q head tail rk u v bu (r.[u * m + v])
                  HB Hht Hqu Hbu Sv Hv0 Hx C2) as (HB' & Hqu' & Hbu' & Hht' & Grow & Vv).
      eapply IH; [ | reflexivity | exact HB' | exact Hht' | exact Hqu' | exact Hbu'
                   | rewrite Hv2; lia | | exact Hres].
      * rewrite <- Hz. apply dec_step. exact Hv.
      * intros w Hw Hwv Hrw. rewrite Hv2 in Hwv.
        destruct (N.eq_dec w (nv v)) as [E | E]; [rewrite E; exact Vv|].
        apply Grow; [exact Hw|]. apply Hcl; [exact Hw | | exact Hrw].
        unfold nv in E. lia.
    + eapply IH; [ | reflexivity | exact HB | exact Hht | exact Hqu | exact Hbu
                   | rewrite Hv2; lia | | exact Hres].
      * rewrite <- Hz. apply dec_step. exact Hv.
      * intros w Hw Hwv Hrw. rewrite Hv2 in Hwv.
        destruct (Z.eq_dec (Z.of_N w) (φ v)) as [E | E].
        -- assert (Ew : w = nv v) by (unfold nv; lia). subst w.
           rewrite <- (Rs_int r u v) in Hrw by lia.
           unfold vis. rewrite cell_int. intro F.
           assert (Fb : (par.[v] =? 0) = true) by (rewrite eqb_spec; apply to_Z_inj; exact F).
           assert (Fx : (0 <? r.[u * m + v]) = true) by (rewrite ltb_spec; exact Hrw).
           rewrite Fb, Fx in C. discriminate.
        -- apply Hcl; [exact Hw | lia | exact Hrw].
  - injection Hres as <- <- <- <-.
    rewrite <- not_true_iff_false, ltb_spec in Hv.
    exists rk. split; [exact HB|]. split; [exact Hht|]. split; [exact Hqu|].
    intros w Hw Hrw. apply Hcl; [exact Hw | | exact Hrw]. unfold station in Hw. lia.
Qed.

Lemma BInv_next : forall r par bott q head tail rk,
  BInv r par bott q head tail rk -> (head < tail)%Z ->
  (forall w, station n w -> (0 < Rs r (qat q head) w)%Z -> vis par w) ->
  BInv r par bott q (head + 1) tail rk.
Proof.
  intros r par bott q head tail rk HB Hht Hcl.
  destruct HB. constructor; try assumption.
  - lia.
  - intros i Hi w Hw Hr. destruct (Z.eq_dec i head) as [E | E].
    + subst i. exact (Hcl w Hw Hr).
    + exact (bi_closed0 i ltac:(lia) w Hw Hr).
Qed.

Definition BPost (r par bott : array int) (rk : N -> Z) : Prop :=
  vis par 1 /\
  (forall v, station n v -> vis par v -> (0 <= rk v < Z.of_N n)%Z /\ (0 < cell bott v)%Z) /\
  (forall v, station n v -> v <> 1%N -> vis par v ->
           station n (Z.to_N (cell par v)) /\ vis par (Z.to_N (cell par v)) /\
           (rk (Z.to_N (cell par v)) < rk v)%Z /\
           (cell bott v <= Rs r (Z.to_N (cell par v)) v)%Z /\
           (cell bott v <= cell bott (Z.to_N (cell par v)))%Z) /\
  (cell par 2 = 0%Z -> forall u v, station n u -> station n v -> vis par u ->
     (0 < Rs r u v)%Z -> vis par v).

Lemma BInv_post : forall r par bott q head tail rk,
  BInv r par bott q head tail rk -> (tail <= head \/ cell par 2 <> 0)%Z ->
  BPost r par bott rk.
Proof.
  intros r par bott q head tail rk HB Hend.
  destruct HB. split; [assumption|]. split; [|split; [assumption|]].
  - intros v Hv Vv. destruct (bi_rk0 v Hv Vv). split; [lia|]. exact (bi_bpos0 v Hv Vv).
  - intros H2 u v Hu Hv Vu Hr. destruct Hend as [Hend | Hend]; [|exfalso; exact (Hend H2)].
    destruct (bi_rk0 u Hu Vu) as [R1 Q1].
    apply (bi_closed0 (rk u) ltac:(lia) v Hv). rewrite Q1. exact Hr.
Qed.

Lemma bfs_loop_spec : forall r, (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  forall (z : Z) head par bott q tail rk (H : Acc (Zwf 0) (gap m head)),
  gap m head = z -> BInv r par bott q (φ head) (φ tail) rk ->
  forall par' bott', bfs_loop r m head par bott q tail H = (par', bott') ->
  exists rk', BPost r par' bott' rk'.
Proof.
  intros r Hr z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros head par bott q tail rk H Hz HB par' bott' Hres.
  rewrite bfs_loop_eq in Hres.
  pose proof (bi_ht _ _ _ _ _ _ _ HB) as Hht. pose proof (bi_tn _ _ _ _ _ _ _ HB) as Htn.
  destruct (bdec (head <? m)) as [Hh | Hh].
  - destruct ((head <? tail) && (par.[2] =? 0)) eqn:C.
    + apply andb_prop in C. destruct C as [C1 C2]. rewrite ltb_spec in C1.
      cbv zeta in Hres.
      destruct (scan r m q.[head] bott.[q.[head]] 1 par bott q tail
                  (Zwf_well_founded 0 (gap m 1))) as [[[par1 bott1] q1] tail1] eqn:Hs.
      assert (Hqu : qat q (φ head) = nv (q.[head])).
      { unfold qat. replace (Z.to_N (φ head)) with (nv head) by reflexivity.
        rewrite cell_int. reflexivity. }
      assert (Hbu : (φ (bott.[q.[head]])) = cell bott (nv (q.[head])))
        by (rewrite cell_int; reflexivity).
      destruct (scan_spec r Hr (q.[head]) (bott.[q.[head]]) (φ head) _ 1 par bott q tail rk
                  (Zwf_well_founded 0 (gap m 1)) eq_refl HB C1 Hqu Hbu
                  ltac:(change (φ 1) with 1%Z; lia)
                  ltac:(intros w Hw Hw1; change (φ 1) with 1%Z in Hw1; unfold station in Hw; lia)
                  par1 bott1 q1 tail1 Hs) as (rk1 & HB1 & Hht1 & Hqu1 & Hcl1).
      assert (Hh1 : (φ (head + 1)) = ((φ head) + 1)%Z).
      { rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [reflexivity|].
        rewrite wB_val. lia. }
      eapply IH; [ | reflexivity | | exact Hres].
      * rewrite <- Hz. apply dec_step. exact Hh.
      * rewrite Hh1. apply BInv_next; [exact HB1 | exact Hht1 |].
        rewrite Hqu1. exact Hcl1.
    + injection Hres as <- <-. exists rk. apply (BInv_post r par bott q (φ head) (φ tail) rk HB).
      apply andb_false_iff in C. destruct C as [C | C].
      * left. rewrite <- not_true_iff_false, ltb_spec in C. lia.
      * right. intro F. rewrite <- not_true_iff_false, eqb_spec in C. apply C.
        apply to_Z_inj. exact F.
  - exfalso. rewrite <- not_true_iff_false, ltb_spec in Hh. lia.
Qed.

Lemma big_val : (φ big) = 4611686018427387903%Z.
Proof. reflexivity. Qed.

Lemma alength_make_m : forall b : int, (φ (PArray.length (PArray.make m b))) = (φ m).
Proof.
  intros b. rewrite alength_make.
  replace (m <=? PArray.max_length) with true; [reflexivity|].
  symmetry. rewrite leb_spec. change (φ PArray.max_length) with 4194303%Z. lia.
Qed.

Lemma bfs_spec : forall r, (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  forall par bott, bfs r m = (par, bott) -> exists rk, BPost r par bott rk.
Proof.
  intros r Hr par bott Hres. unfold bfs in Hres.
  eapply (bfs_loop_spec r Hr _ 0 _ _ _ 1 (fun _ => 0%Z)); [reflexivity | | exact Hres].
  assert (I1 : ((φ 1) < (φ m))%Z) by (change (φ 1) with 1%Z; lia).
  assert (I0 : ((φ 0) < (φ m))%Z) by (change (φ 0) with 0%Z; lia).
  set (par0 := (PArray.make m 0).[1 <- 1]).
  assert (Cp : forall w, station n w -> cell par0 w = if (w =? 1)%N then 1%Z else 0%Z).
  { intros w Hw. unfold par0. rewrite cell_set_st by (try apply alength_make_m; assumption).
    change (nv 1) with 1%N. unfold cell. rewrite aget_make. reflexivity. }
  assert (Vp : forall w, station n w -> vis par0 w -> w = 1%N).
  { intros w Hw Vw. unfold vis in Vw. rewrite Cp in Vw by exact Hw.
    destruct (N.eqb_spec w 1); [assumption | contradiction]. }
  assert (S1 : station n 1) by (unfold station; lia).
  assert (V1 : vis par0 1) by (unfold vis; rewrite Cp by exact S1; discriminate).
  assert (Q0 : qat ((PArray.make m 0).[0 <- 1]) 0 = 1%N).
  { unfold qat. change (Z.to_N 0) with (nv 0). rewrite cell_int.
    rewrite aget_set_same; [reflexivity|]. rewrite ltb_spec, alength_make_m. exact I0. }
  constructor.
  - unfold par0. rewrite alength_set. apply alength_make_m.
  - rewrite alength_set. apply alength_make_m.
  - rewrite alength_set. apply alength_make_m.
  - change (φ 0) with 0%Z. change (φ 1) with 1%Z. lia.
  - change (φ 1) with 1%Z. lia.
  - exact V1.
  - intros i Hi. change (φ 1) with 1%Z in Hi. replace i with 0%Z by lia.
    rewrite Q0. split; [exact S1 | split; [exact V1 | reflexivity]].
  - intros v Hv Vv. pose proof (Vp v Hv Vv). subst v. change (φ 1) with 1%Z.
    split; [lia | exact Q0].
  - intros v Hv Vv. pose proof (Vp v Hv Vv). subst v.
    unfold cell. rewrite aget_set_same.
    + rewrite big_val. lia.
    + rewrite ltb_spec, alength_make_m. exact I1.
  - intros v Hv Hv1 Vv. exfalso. exact (Hv1 (Vp v Hv Vv)).
  - intros i Hi. change (φ 0) with 0%Z in Hi. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Pushing along the tree path                                         *)
(* ------------------------------------------------------------------ *)

Lemma Rs_push : forall r xu xc d a b,
  (φ (PArray.length r)) = ((φ m) * (φ m))%Z ->
  station n (nv xu) -> station n (nv xc) -> nv xu <> nv xc ->
  station n a -> station n b ->
  ((φ d) <= Rs r (nv xu) (nv xc))%Z ->
  (Rs r (nv xc) (nv xu) + (φ d) < wB)%Z ->
  Rs ((r.[xu * m + xc <- r.[xu * m + xc] - d]).[xc * m + xu <-
        (r.[xu * m + xc <- r.[xu * m + xc] - d]).[xc * m + xu] + d]) a b
  = (Rs r a b + (if (a =? nv xc)%N && (b =? nv xu)%N then (φ d) else 0)
              - (if (a =? nv xu)%N && (b =? nv xc)%N then (φ d) else 0))%Z.
Proof.
  intros r xu xc d a b Hl Hu Hc Huc Sa Sb O1 O2.
  pose proof (station_int _ Hu) as Iu. pose proof (station_int _ Hc) as Ic.
  pose proof (station_lt _ Sa). pose proof (station_lt _ Sb).
  assert (E1 : (φ (r.[xu * m + xc] - d)) = (Rs r (nv xu) (nv xc) - (φ d))%Z).
  { rewrite sub_spec, Rs_int by assumption. pose proof (to_Z_bounded d).
    pose proof (Rs_bound_triv := to_Z_bounded (r.[xu * m + xc])).
    rewrite Rs_int in Rs_bound_triv by assumption.
    rewrite Z.mod_small by lia. reflexivity. }
  set (r1 := r.[xu * m + xc <- r.[xu * m + xc] - d]).
  assert (L1 : (φ (PArray.length r1)) = ((φ m) * (φ m))%Z) by (unfold r1; rewrite alength_set; exact Hl).
  assert (R1 : forall u v, (Z.of_N u < (φ m))%Z -> (Z.of_N v < (φ m))%Z ->
     Rs r1 u v = if (u =? nv xu)%N && (v =? nv xc)%N
                 then (Rs r (nv xu) (nv xc) - (φ d))%Z else Rs r u v).
  { intros u v Hu' Hv'. unfold r1. rewrite Rs_set by assumption. rewrite E1. reflexivity. }
  assert (E2 : (φ (r1.[xc * m + xu] + d)) = (Rs r (nv xc) (nv xu) + (φ d))%Z).
  { rewrite add_spec, Rs_int by assumption. rewrite R1 by (rewrite Zof_nv; assumption).
    destruct (N.eqb_spec (nv xc) (nv xu)); [congruence|]. simpl.
    pose proof (Rs_nonneg r (nv xc) (nv xu)).
    pose proof (to_Z_bounded d). rewrite Z.mod_small by lia. reflexivity. }
  rewrite Rs_set by assumption. rewrite E2, R1 by assumption.
  eqbs; simpl; subst; try congruence; try lia.
Qed.

Lemma ss_ind : forall p c, station n p ->
  sum_stations (fun v => if (v =? p)%N then c else 0%Z) (N.to_nat n) = c.
Proof.
  intros p c Hp. rewrite (ss_point _ _ p).
  - rewrite N.eqb_refl. reflexivity.
  - unfold station in Hp. lia.
  - intros x _ Hx. destruct (N.eqb_spec x p); [contradiction | reflexivity].
Qed.

Lemma net_push : forall cap (r r2 : array int) (U C : N) (d : Z),
  station n U -> station n C ->
  (forall a b, station n a -> station n b ->
     Rs r2 a b = (Rs r a b + (if (a =? C)%N && (b =? U)%N then d else 0)
                  - (if (a =? U)%N && (b =? C)%N then d else 0))%Z) ->
  forall x, station n x ->
  net_out n (Fl cap r2) x
  = (net_out n (Fl cap r) x + (if (x =? U)%N then d else 0)
     - (if (x =? C)%N then d else 0))%Z.
Proof.
  intros cap r r2 U C d HU HC HR x Hx. unfold net_out.
  rewrite (ss_ext _ (fun v => Fl cap r x v +
      ((if (x =? U)%N then (if (v =? C)%N then d else 0) else 0) +
       - (if (x =? C)%N then (if (v =? U)%N then d else 0) else 0)))%Z).
  - rewrite ss_add, ss_add, ss_opp.
    destruct (N.eqb_spec x U), (N.eqb_spec x C); cbv iota;
      rewrite ?ss_ind by assumption; rewrite ?ss_const; lia.
  - intros v Hv. unfold Fl. rewrite HR by (try assumption; unfold station; lia).
    destruct (N.eqb_spec x U), (N.eqb_spec x C), (N.eqb_spec v U), (N.eqb_spec v C);
      simpl; lia.
Qed.

Record WInv (cap : N -> N -> N) (r0 par bott : array int) (rk : N -> Z)
    (val d : Z) (r : array int) (cur i : int) : Prop := {
  wi_len : (φ (PArray.length r)) = ((φ m) * (φ m))%Z;
  wi_sym : forall u v, station n u -> station n v ->
              (Rs r u v + Rs r v u = 2 * Z.of_N (cap u v))%Z;
  wi_cons : forall x, station n x -> x <> 1%N -> x <> 2%N -> x <> nv cur ->
              net_out n (Fl cap r) x = 0%Z;
  wi_cur : nv cur <> 1%N -> nv cur <> 2%N -> net_out n (Fl cap r) (nv cur) = d;
  wi_val : net_out n (Fl cap r) 1 = (val + (if (nv cur =? 1)%N then d else 0))%Z;
  wi_unch : forall a b, station n a -> station n b ->
              (rk a < rk (nv cur) \/ rk b < rk (nv cur))%Z -> Rs r a b = Rs r0 a b;
  wi_st : station n (nv cur);
  wi_vis : vis par (nv cur);
  wi_d : (d <= cell bott (nv cur))%Z;
  wi_i : ((φ i) + rk (nv cur) < (φ m))%Z
}.

Lemma walk_eq : forall par m d r cur i H,
  walk par m d r cur i H =
  match bdec (i <? m) with
  | left Hi =>
      if cur =? 1 then r
      else
        let u := par.[cur] in
        let i1 := u * m + cur in
        let r1 := r.[i1 <- r.[i1] - d] in
        let i2 := cur * m + u in
        let r2 := r1.[i2 <- r1.[i2] + d] in
        walk par m d r2 u (i + 1) (Acc_inv H (dec_step m i Hi))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma walk_spec : forall cap r0 par bott rk (val : Z) (d : int),
  capok cap -> BPost r0 par bott rk -> (0 < (φ d))%Z ->
  forall (z : Z) r cur i (H : Acc (Zwf 0) (gap m i)),
  gap m i = z ->
  WInv cap r0 par bott rk val (φ d) r cur i ->
  Inv cap (walk par m d r cur i H) (val + (φ d)).
Proof.
  intros cap r0 par bott rk val d Hc HP Hd z.
  destruct HP as (_ & Hrk & Hpar & _).
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r cur i H Hz HW.
  rewrite walk_eq.
  destruct HW as [Wl Ws Wc Wcur Wv Wu Wst Wvis Wd Wi].
  pose proof (Hrk _ Wst Wvis) as [Rk0 _].
  destruct (bdec (i <? m)) as [Hi | Hi].
  2: { exfalso. rewrite <- not_true_iff_false, ltb_spec in Hi. lia. }
  destruct (cur =? 1) eqn:C1.
  - rewrite eqb_spec in C1. subst cur. change (nv 1) with 1%N in *.
    constructor.
    + exact Wl.
    + exact Ws.
    + intros x Hx H1 H2. exact (Wc x Hx H1 H2 H1).
    + rewrite Wv. reflexivity.
  - assert (Nc1 : nv cur <> 1%N).
    { intro E. rewrite eqb_false_spec in C1. apply C1. apply nv_inj. exact E. }
    cbv zeta.
    set (u := par.[cur]).
    destruct (Hpar _ Wst Nc1 Wvis) as (Su & Vu & Ru & Bu1 & Bu2).
    assert (Eu : Z.to_N (cell par (nv cur)) = nv u) by (unfold u; rewrite cell_int; reflexivity).
    rewrite Eu in Su, Vu, Ru, Bu1, Bu2.
    assert (Nuc : nv u <> nv cur) by (intro E; rewrite E in Ru; lia).
    assert (Huc : Rs r (nv u) (nv cur) = Rs r0 (nv u) (nv cur))
      by (apply Wu; [exact Su | exact Wst | left; exact Ru]).
    pose proof (Ws _ _ Su Wst) as Sym. pose proof (Rs_nonneg r (nv cur) (nv u)).
    destruct Hc as [Hcs Hcb]. pose proof (Hcb _ _ Su Wst) as Cb.
    assert (O1 : ((φ d) <= Rs r (nv u) (nv cur))%Z) by lia.
    assert (O2 : (Rs r (nv cur) (nv u) + (φ d) < wB)%Z).
    { clear - Sym Cb O1. rewrite wB_val. unfold Cmax in *.
      set (A := Rs r (nv u) (nv cur)) in *. set (B := Rs r (nv cur) (nv u)) in *.
      set (c := Z.of_N (cap (nv u) (nv cur))) in *. lia. }
    set (r2 := (r.[u * m + cur <- r.[u * m + cur] - d]).[cur * m + u <-
                (r.[u * m + cur <- r.[u * m + cur] - d]).[cur * m + u] + d]).
    assert (HR : forall a b, station n a -> station n b ->
       Rs r2 a b = (Rs r a b + (if (a =? nv cur)%N && (b =? nv u)%N then (φ d) else 0)
                    - (if (a =? nv u)%N && (b =? nv cur)%N then (φ d) else 0))%Z)
      by (intros a b Ha Hb; unfold r2; apply Rs_push; assumption).
    pose proof (net_push cap r r2 (nv u) (nv cur) (φ d) Su Wst HR) as HN.
    assert (S1 : station n 1) by (unfold station; lia).
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z).
    { rewrite ltb_spec in Hi. rewrite add_spec. change (φ 1) with 1%Z.
      rewrite Z.mod_small; [reflexivity|]. rewrite wB_val. lia. }
    eapply IH; [ rewrite <- Hz; apply dec_step; exact Hi | reflexivity | ].
    constructor.
    + unfold r2. rewrite !alength_set. exact Wl.
    + intros a b Ha Hb. rewrite (HR a b Ha Hb), (HR b a Hb Ha).
      pose proof (Ws a b Ha Hb) as Sab. clear - Sab Nuc.
      destruct (N.eqb_spec a (nv cur)), (N.eqb_spec b (nv u)),
               (N.eqb_spec a (nv u)), (N.eqb_spec b (nv cur)); cbv [andb]; lia.
    + intros x Hx H1 H2 Hxu. rewrite (HN x Hx).
      destruct (N.eqb_spec x (nv u)) as [E | _]; [contradiction|].
      destruct (N.eqb_spec x (nv cur)) as [E | E].
      * subst x. rewrite (Wcur H1 H2). lia.
      * rewrite (Wc x Hx H1 H2 E). lia.
    + intros H1 H2. rewrite (HN _ Su), N.eqb_refl.
      destruct (N.eqb_spec (nv u) (nv cur)) as [E | _]; [contradiction|].
      rewrite (Wc _ Su H1 H2 Nuc). lia.
    + rewrite (HN 1%N S1), Wv. clear - Nc1 Nuc.
      destruct (N.eqb_spec 1 (nv u)), (N.eqb_spec 1 (nv cur)),
               (N.eqb_spec (nv cur) 1), (N.eqb_spec (nv u) 1); cbv [andb]; lia.
    + intros a b Ha Hb Hab. rewrite (HR a b Ha Hb).
      rewrite (Wu a b Ha Hb) by lia. clear - Hab Ru.
      destruct (N.eqb_spec a (nv cur)), (N.eqb_spec b (nv u)),
               (N.eqb_spec a (nv u)), (N.eqb_spec b (nv cur)); cbv [andb]; subst; lia.
    + exact Su.
    + exact Vu.
    + lia.
    + lia.
Qed.

(* ------------------------------------------------------------------ *)
(* One maximisation                                                    *)
(* ------------------------------------------------------------------ *)

Lemma augment_eq : forall m B r val i H,
  augment m B r val i H =
  match bdec (i <? B) with
  | left Hi =>
      match bfs r m with
      | (par, bott) =>
          if par.[2] =? 0 then (r, val)
          else
            let d := bott.[2] in
            augment m B (walk par m d r 2 0 (Zwf_well_founded 0 (gap m 0)))
              (val + d) (i + 1) (Acc_inv H (dec_step B i Hi))
      end
  | right _ => (r, val)
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma budget_val : (φ budget) = 1099511627776%Z.
Proof. reflexivity. Qed.

Lemma augment_spec : forall cap, capok cap ->
  forall (z : Z) r val i (H : Acc (Zwf 0) (gap budget i)),
  gap budget i = z -> Inv cap r (φ val) -> ((φ i) <= (φ val))%Z ->
  forall r' val', augment m budget r val i H = (r', val') ->
  Inv cap r' (φ val') /\ max_flow n cap (Z.to_N (φ val')).
Proof.
  intros cap Hc z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros r val i H Hz HI Hiv r' val' Hres.
  rewrite augment_eq in Hres.
  pose proof (val_bound cap r _ Hc HI) as Vb.
  destruct (bdec (i <? budget)) as [Hi | Hi].
  2: { exfalso. rewrite <- not_true_iff_false, ltb_spec, budget_val in Hi.
       unfold Cmax in Vb. lia. }
  pose proof (inv_len _ _ _ HI) as Hl.
  destruct (bfs r m) as [par bott] eqn:Hb.
  destruct (bfs_spec r Hl par bott Hb) as [rk HP].
  pose proof HP as (Hsrc & Hrk & Hpar & Hcl).
  assert (S2 : station n 2) by (unfold station; lia).
  assert (C2 : cell par 2 = (φ (par.[2]))) by reflexivity.
  destruct (par.[2] =? 0) eqn:C.
  - injection Hres as <- <-. split; [exact HI|].
    rewrite eqb_spec in C.
    assert (Hp2 : cell par 2 = 0%Z) by (rewrite C2, C; reflexivity).
    apply (Inv_maxflow cap r (φ val) (fun u => negb (cell par u =? 0)%Z) Hc HI).
    + cbv beta. destruct (Z.eqb_spec (cell par 1) 0) as [E | E];
        [exfalso; exact (Hsrc E) | reflexivity].
    + cbv beta. rewrite Hp2. reflexivity.
    + intros u v Hu Hv Su Sv. cbv beta in Su, Sv.
      destruct (Z.eqb_spec (cell par u) 0) as [E | E]; [discriminate|].
      destruct (Z.eqb_spec (cell par v) 0) as [E' | E']; [|discriminate].
      pose proof (Rs_nonneg r u v) as Nn.
      destruct (Z.eq_dec (Rs r u v) 0) as [E2 | E2]; [exact E2|].
      assert (Pos : (0 < Rs r u v)%Z) by (clear - Nn E2; lia).
      exfalso. exact (Hcl Hp2 u v Hu Hv E Pos E').
    + pose proof (to_Z_bounded val). lia.
  - cbv zeta in Hres.
    rewrite eqb_false_spec in C.
    assert (V2 : vis par 2).
    { unfold vis. rewrite C2. intro F. apply C. apply to_Z_inj. exact F. }
    destruct (Hrk 2%N S2 V2) as [Rk2 Bd].
    assert (Hd : (φ (bott.[2])) = cell bott 2) by reflexivity.
    destruct (Hpar 2%N S2 ltac:(discriminate) V2) as (Sp & _ & _ & Bp & _).
    pose proof (Rs_bound cap r _ Hc HI _ _ Sp S2) as Rb.
    assert (Hvd : (φ (val + bott.[2])) = ((φ val) + (φ (bott.[2])))%Z).
    { rewrite add_spec. rewrite Z.mod_small; [reflexivity|].
      pose proof (to_Z_bounded val). rewrite wB_val. unfold Cmax in *. lia. }
    assert (Hi1 : (φ (i + 1)) = ((φ i) + 1)%Z).
    { pose proof Hi as Hi'. rewrite ltb_spec, budget_val in Hi'.
      rewrite add_spec. change (φ 1) with 1%Z.
      rewrite Z.mod_small; [reflexivity|]. rewrite wB_val. pose proof (to_Z_bounded i). lia. }
    eapply IH; [ rewrite <- Hz; apply dec_step; exact Hi | reflexivity | | | exact Hres].
    + rewrite Hvd. apply (walk_spec cap r par bott rk (φ val) (bott.[2]) Hc HP
        ltac:(lia) _ r 2 0 _ eq_refl).
      constructor.
      * exact Hl.
      * exact (inv_sym _ _ _ HI).
      * intros x Hx H1 H2 _. exact (inv_cons _ _ _ HI x Hx H1 H2).
      * change (nv 2) with 2%N. intros _ F. exfalso. exact (F eq_refl).
      * change (nv 2) with 2%N. rewrite (inv_val _ _ _ HI).
        replace ((2 =? 1)%N) with false by reflexivity. lia.
      * intros a b _ _ _. reflexivity.
      * exact S2.
      * exact V2.
      * change (nv 2) with 2%N. lia.
      * change (nv 2) with 2%N. change (φ 0) with 0%Z. lia.
    + rewrite Hi1, Hvd. lia.
Qed.

End Net.

(* ------------------------------------------------------------------ *)
(* Capacities                                                          *)
(* ------------------------------------------------------------------ *)

Lemma sum_below_ext : forall g h t,
  (forall j, (j < t)%nat -> g (N.of_nat j) = h (N.of_nat j)) ->
  sum_below g t = sum_below h t.
Proof.
  intros g h t. induction t as [| t IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros j Hj; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sum_below_le : forall g t B,
  (forall j, (j < t)%nat -> (g (N.of_nat j) <= B)%N) ->
  (sum_below g t <= B * N.of_nat t)%N.
Proof.
  intros g t B. induction t as [| t IH]; intros H; simpl; [lia|].
  specialize (IH ltac:(intros j Hj; apply H; lia)).
  specialize (H t ltac:(lia)). lia.
Qed.

Lemma cap_upto_term : forall a b c t u v,
  cap_upto a b c t u v =
  sum_below (fun j => pterm (Prelude.get a j) (Prelude.get b j) (Prelude.get c j) u v) (N.to_nat t).
Proof. reflexivity. Qed.

Lemma cap_upto_sym : forall a b c t u v, cap_upto a b c t u v = cap_upto a b c t v u.
Proof.
  intros. rewrite !cap_upto_term. apply sum_below_ext. intros j _. apply pterm_sym.
Qed.

Lemma cap_upto_succ : forall a b c t u v,
  cap_upto a b c (t + 1) u v
  = (cap_upto a b c t u v + pterm (Prelude.get a t) (Prelude.get b t) (Prelude.get c t) u v)%N.
Proof.
  intros. rewrite !cap_upto_term.
  replace (N.to_nat (t + 1)) with (S (N.to_nat t)) by lia. simpl.
  rewrite N2Nat.id. reflexivity.
Qed.

Lemma cap_upto_le : forall a b c t u v,
  (forall j, (j < t)%N -> (Prelude.get c j <= 1000)%N) ->
  (cap_upto a b c t u v <= 1000 * t)%N.
Proof.
  intros a b c t u v H. rewrite cap_upto_term.
  replace (1000 * t)%N with (1000 * N.of_nat (N.to_nat t))%N by lia.
  apply sum_below_le. intros j Hj. unfold pterm.
  destruct (_ || _); [apply H; lia | lia].
Qed.

Definition capT (pa pb pc ia ib ic : list N) (t1 t2 : N) (u v : N) : N :=
  (cap_upto pa pb pc t1 u v + cap_upto ia ib ic t2 u v)%N.

Lemma capT_ok : forall n pa pb pc ia ib ic t1 t2,
  valid_input n pa pb pc ia ib ic -> (t1 <= len pa)%N -> (t2 <= len ia)%N ->
  capok n (capT pa pb pc ia ib ic t1 t2).
Proof.
  intros n pa pb pc ia ib ic t1 t2 Hv H1 H2. split.
  - intros u v. unfold capT. rewrite (cap_upto_sym pa), (cap_upto_sym ia). reflexivity.
  - intros u v _ _. unfold capT, Cmax.
    pose proof (cap_upto_le pa pb pc t1 u v
      ltac:(intros j Hj; apply (vi_pcap _ _ _ _ _ _ _ Hv); lia)).
    pose proof (cap_upto_le ia ib ic t2 u v
      ltac:(intros j Hj; apply (vi_icap _ _ _ _ _ _ _ Hv); lia)).
    pose proof (vi_p _ _ _ _ _ _ _ Hv) as Hp. pose proof (vi_n _ _ _ _ _ _ _ Hv).
    pose proof (vi_k _ _ _ _ _ _ _ Hv).
    assert (Hp' : (len pa <= 4950)%N).
    { eapply N.le_trans; [exact Hp|].
      assert (n * (n - 1) <= 9900)%N by nia.
      apply N.Div0.div_le_upper_bound. lia. }
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the inputs                                                  *)
(* ------------------------------------------------------------------ *)

Lemma repr_len_u : forall (x : array@{Set} int) (l : list N),
  @repr (array uint) (list N) _ x l ->
  (φ (PArray.length@{Set} x)) = Z.of_nat (List.length l).
Proof. intros x l [Hl _]. symmetry. exact Hl. Qed.

Lemma repr_get_u : forall (x : array@{Set} int) (l : list N),
  @repr (array uint) (list N) _ x l ->
  forall j : int, ((φ j) < Z.of_nat (List.length l))%Z ->
  nv (PArray.get@{Set} x j) = Prelude.get l (nv j).
Proof.
  intros x l [_ Hc] j Hj.
  destruct (Hc (Z.to_nat (φ j)) ltac:(lia)) as (v & Hv & Hr).
  unfold repr, repr_uint in Hr.
  rewrite Z2Nat.id in Hr by (pose proof (to_Z_bounded j); lia).
  rewrite of_to_Z in Hr.
  assert (Hr' : Z.to_N (φ (PArray.get@{Set} x j)) = v) by exact Hr.
  unfold nv. rewrite Hr'.
  unfold Prelude.get. replace (N.to_nat (Z.to_N (φ j))) with (Z.to_nat (φ j)) by lia.
  symmetry. apply nth_error_nth. exact Hv.
Qed.

Lemma capok_ext : forall n f g, (forall u v, f u v = g u v) -> capok n g -> capok n f.
Proof.
  intros n f g E [Hs Hb]. split.
  - intros u v. rewrite !E. apply Hs.
  - intros u v Hu Hv. rewrite E. apply Hb; assumption.
Qed.

Lemma nv_succ : forall t : int, ((φ t) < 9223372036854775807)%Z -> nv (t + 1) = (nv t + 1)%N.
Proof.
  intros t Ht. unfold nv. rewrite add_spec. change (φ 1) with 1%Z.
  rewrite Z.mod_small by (rewrite wB_val; pose proof (to_Z_bounded t); lia).
  pose proof (to_Z_bounded t). lia.
Qed.

Lemma init_loop_eq : forall pa pb pc m p j r H,
  init_loop pa pb pc m p j r H =
  match bdec (j <? p) with
  | left Hj =>
      init_loop pa pb pc m p (j + 1) (add_pipe m r pa.[j] pb.[j] pc.[j])
        (Acc_inv H (dec_step p j Hj))
  | right _ => r
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma imp_loop_eq : forall ia ib ic m k t r val out H,
  imp_loop ia ib ic m k t r val out H =
  match bdec (t <? k) with
  | left Ht =>
      let r1 := add_pipe m r ia.[t] ib.[t] ic.[t] in
      match augment m budget r1 val 0 (Zwf_well_founded 0 (gap budget 0)) with
      | (r2, val2) =>
          imp_loop ia ib ic m k (t + 1) r2 val2 out.[t + 1 <- val2]
            (Acc_inv H (dec_step k t Ht))
      end
  | right _ => out
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Main.

Variables (n : N) (pa pb pc ia ib ic : list N).
Variables (xn : int) (xpa xpb xpc xia xib xic : array@{Set} int).
Hypothesis Hv : valid_input n pa pb pc ia ib ic.
Hypothesis Rn : @repr uint N _ xn n.
Hypotheses (Rpa : @repr (array uint) (list N) _ xpa pa)
           (Rpb : @repr (array uint) (list N) _ xpb pb)
           (Rpc : @repr (array uint) (list N) _ xpc pc).
Hypotheses (Ria : @repr (array uint) (list N) _ xia ia)
           (Rib : @repr (array uint) (list N) _ xib ib)
           (Ric : @repr (array uint) (list N) _ xic ic).

Lemma Hn : (2 <= n <= 100)%N.
Proof. exact (vi_n _ _ _ _ _ _ _ Hv). Qed.

Lemma Hm : (φ (xn + 1)) = (Z.of_N n + 1)%Z.
Proof.
  pose proof Hn as H. unfold repr, repr_uint in Rn.
  rewrite add_spec. change (φ 1) with 1%Z.
  pose proof (to_Z_bounded xn).
  rewrite Z.mod_small by (rewrite wB_val; lia). lia.
Qed.

Lemma Lpa : (φ (PArray.length xpa)) = Z.of_N (len pa).
Proof. unfold len. rewrite nat_N_Z. exact (repr_len_u _ _ Rpa). Qed.

Lemma Lia : (φ (PArray.length xia)) = Z.of_N (len ia).
Proof. unfold len. rewrite nat_N_Z. exact (repr_len_u _ _ Ria). Qed.

(* the j-th pipe of a section, read off the machine arrays *)
Lemma pipe_read : forall (xa xb xc : array@{Set} int) (a b c : list N) (j : int),
  @repr (array uint) (list N) _ xa a -> @repr (array uint) (list N) _ xb b ->
  @repr (array uint) (list N) _ xc c ->
  len b = len a -> len c = len a ->
  ((φ j) < Z.of_N (len a))%Z ->
  nv (xa.[j]) = Prelude.get a (nv j) /\ nv (xb.[j]) = Prelude.get b (nv j) /\
  nv (xc.[j]) = Prelude.get c (nv j).
Proof.
  intros xa xb xc a b c j Ra Rb Rc Lb Lc Hj. unfold len in *.
  split; [|split]; (eapply repr_get_u; [eassumption | lia]).
Qed.

Lemma init_spec : forall (z : Z) j r H,
  gap (PArray.length xpa) j = z -> ((φ j) <= (φ (PArray.length xpa)))%Z ->
  Inv n (xn + 1) (capT pa pb pc ia ib ic (nv j) 0) r 0 ->
  Inv n (xn + 1) (capT pa pb pc ia ib ic (len pa) 0)
    (init_loop xpa xpb xpc (xn + 1) (PArray.length xpa) j r H) 0.
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros j r H Hz Hj HI. rewrite init_loop_eq.
  pose proof Lpa as Lp.
  destruct (bdec (j <? PArray.length xpa)) as [Hj' | Hj'].
  - pose proof Hj' as Hjl. rewrite ltb_spec in Hjl.
    destruct (pipe_read xpa xpb xpc pa pb pc j Rpa Rpb Rpc
                (vi_pb _ _ _ _ _ _ _ Hv) (vi_pc _ _ _ _ _ _ _ Hv) ltac:(lia))
      as (Ea & Eb & Ec).
    destruct (vi_pab _ _ _ _ _ _ _ Hv (nv j) ltac:(unfold nv; lia)) as [Hab Hbn].
    assert (Hj1 : nv (j + 1) = (nv j + 1)%N)
      by (apply nv_succ; pose proof (vi_p _ _ _ _ _ _ _ Hv); lia).
    eapply IH; [ rewrite <- Hz; apply dec_step; exact Hj' | reflexivity
               | rewrite add_spec; change (φ 1) with 1%Z;
                 rewrite Z.mod_small by (rewrite wB_val; pose proof (to_Z_bounded j); lia); lia | ].
    assert (E : forall u v, capT pa pb pc ia ib ic (nv (j + 1)) 0 u v
       = (capT pa pb pc ia ib ic (nv j) 0 u v
          + pterm (nv xpa.[j]) (nv xpb.[j]) (nv xpc.[j]) u v)%N).
    { intros u v. unfold capT. rewrite Hj1, cap_upto_succ, Ea, Eb, Ec. lia. }
    apply (Inv_ext n (xn + 1) Hn
             (fun u v => (capT pa pb pc ia ib ic (nv j) 0 u v
                + pterm (nv xpa.[j]) (nv xpb.[j]) (nv xpc.[j]) u v)%N)).
    + intros u v _ _. symmetry. apply E.
    + apply (add_pipe_inv n (xn + 1) Hm Hn); [exact HI | | | |].
      * rewrite Ea. unfold station. lia.
      * rewrite Eb. unfold station. lia.
      * rewrite Ea, Eb. lia.
      * apply (capok_ext n _ (capT pa pb pc ia ib ic (nv (j + 1)) 0)).
        -- intros u v. symmetry. apply E.
        -- apply capT_ok; [exact Hv | unfold nv; lia | lia].
  - rewrite <- not_true_iff_false, ltb_spec in Hj'.
    replace (len pa) with (nv j) by (unfold nv; lia). exact HI.
Qed.

Lemma imp_spec : forall (z : Z) t r val out H,
  gap (PArray.length xia) t = z -> ((φ t) <= (φ (PArray.length xia)))%Z ->
  Inv n (xn + 1) (capT pa pb pc ia ib ic (len pa) (nv t)) r (φ val) ->
  (φ (PArray.length out)) = ((φ (PArray.length xia)) + 1)%Z ->
  (forall s, (s <= nv t)%N ->
     max_flow n (capacity pa pb pc ia ib ic s) (Z.to_N (cell out s))) ->
  (φ (PArray.length (imp_loop xia xib xic (xn + 1) (PArray.length xia) t r val out H)))
    = ((φ (PArray.length xia)) + 1)%Z /\
  forall s, (s <= len ia)%N ->
    max_flow n (capacity pa pb pc ia ib ic s)
      (Z.to_N (cell (imp_loop xia xib xic (xn + 1) (PArray.length xia) t r val out H) s)).
Proof.
  intros z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros t r val out H Hz Ht HI Hlo Hout. rewrite imp_loop_eq.
  pose proof Lia as Lk. pose proof (vi_k _ _ _ _ _ _ _ Hv) as Hk.
  destruct (bdec (t <? PArray.length xia)) as [Ht' | Ht'].
  - pose proof Ht' as Htl. rewrite ltb_spec in Htl.
    destruct (pipe_read xia xib xic ia ib ic t Ria Rib Ric
                (vi_ib _ _ _ _ _ _ _ Hv) (vi_ic _ _ _ _ _ _ _ Hv) ltac:(lia))
      as (Ea & Eb & Ec).
    destruct (vi_iab _ _ _ _ _ _ _ Hv (nv t) ltac:(unfold nv; lia)) as [Hab Hbn].
    assert (Ht1 : nv (t + 1) = (nv t + 1)%N) by (apply nv_succ; lia).
    assert (Ht1' : (φ (t + 1)) = ((φ t) + 1)%Z).
    { rewrite add_spec. change (φ 1) with 1%Z.
      rewrite Z.mod_small by (rewrite wB_val; pose proof (to_Z_bounded t); lia). lia. }
    cbv zeta.
    assert (E : forall u v, capT pa pb pc ia ib ic (len pa) (nv (t + 1)) u v
       = (capT pa pb pc ia ib ic (len pa) (nv t) u v
          + pterm (nv xia.[t]) (nv xib.[t]) (nv xic.[t]) u v)%N).
    { intros u v. unfold capT. rewrite Ht1, cap_upto_succ, Ea, Eb, Ec. lia. }
    assert (Cok : capok n (capT pa pb pc ia ib ic (len pa) (nv (t + 1))))
      by (apply capT_ok; [exact Hv | lia | unfold nv; lia]).
    assert (HI1 : Inv n (xn + 1) (capT pa pb pc ia ib ic (len pa) (nv (t + 1)))
                    (add_pipe (xn + 1) r xia.[t] xib.[t] xic.[t]) (φ val)).
    { apply (Inv_ext n (xn + 1) Hn
             (fun u v => (capT pa pb pc ia ib ic (len pa) (nv t) u v
                + pterm (nv xia.[t]) (nv xib.[t]) (nv xic.[t]) u v)%N)).
      + intros u v _ _. symmetry. apply E.
      + apply (add_pipe_inv n (xn + 1) Hm Hn); [exact HI | | | |].
        * rewrite Ea. unfold station. lia.
        * rewrite Eb. unfold station. lia.
        * rewrite Ea, Eb. lia.
        * apply (capok_ext n _ _ (fun u v => eq_sym (E u v))). exact Cok. }
    destruct (augment (xn + 1) budget (add_pipe (xn + 1) r xia.[t] xib.[t] xic.[t]) val 0
                (Zwf_well_founded 0 (gap budget 0))) as [r2 val2] eqn:Ha.
    destruct (augment_spec n (xn + 1) Hm Hn _ Cok _ _ val 0 _ eq_refl HI1
                ltac:(change (φ 0) with 0%Z; pose proof (to_Z_bounded val); lia)
                r2 val2 Ha) as [HI2 Hmf].
    eapply IH; [ rewrite <- Hz; apply dec_step; exact Ht' | reflexivity | lia | exact HI2
               | rewrite alength_set; exact Hlo | ].
    intros s Hs. rewrite cell_set.
    2: { rewrite Hlo, Ht1'. lia. }
    2: { rewrite Ht1 in Hs. unfold nv in Hs. rewrite wB_val. lia. }
    destruct (N.eqb_spec s (nv (t + 1))) as [Es | Es].
    + subst s. exact Hmf.
    + apply Hout. rewrite Ht1 in Hs, Es. lia.
  - rewrite <- not_true_iff_false, ltb_spec in Ht'.
    split; [exact Hlo|]. intros s Hs. apply Hout. unfold nv. lia.
Qed.

Lemma Inv_init : Inv n (xn + 1) (capT pa pb pc ia ib ic (nv 0) 0)
  (PArray.make ((xn + 1) * (xn + 1)) 0) 0.
Proof.
  pose proof Hm as Hm'. pose proof Hn as Hn'.
  assert (Hmm : (φ ((xn + 1) * (xn + 1))) = ((φ (xn + 1)) * (φ (xn + 1)))%Z).
  { rewrite mul_spec, Z.mod_small; [reflexivity|]. rewrite wB_val, Hm'. nia. }
  assert (L : (φ (PArray.length (PArray.make ((xn + 1) * (xn + 1)) 0)))
              = ((φ (xn + 1)) * (φ (xn + 1)))%Z).
  { rewrite alength_make.
    replace ((xn + 1) * (xn + 1) <=? PArray.max_length) with true; [exact Hmm|].
    symmetry. rewrite leb_spec, Hmm, Hm'. change (φ PArray.max_length) with 4194303%Z. nia. }
  assert (R0 : forall u v, Rs (xn + 1) (PArray.make ((xn + 1) * (xn + 1)) 0) u v = 0%Z)
    by (intros u v; unfold Rs; rewrite aget_make; reflexivity).
  assert (C0 : forall u v, capT pa pb pc ia ib ic (nv 0) 0 u v = 0%N) by reflexivity.
  constructor.
  - exact L.
  - intros u v _ _. rewrite !R0, C0. reflexivity.
  - intros u _ _ _. unfold net_out. apply ss_zero. intros x _. unfold Fl.
    rewrite R0, C0. reflexivity.
  - unfold net_out. apply ss_zero. intros x _. unfold Fl. rewrite R0, C0. reflexivity.
Qed.

Lemma water_main : exists o : list N,
  @repr (array uint) (list N) _ (water_impl xn xpa xpb xpc xia xib xic) o /\
  water_spec n pa pb pc ia ib ic o.
Proof.
  pose proof Lpa as Lp. pose proof Lia as Lk. pose proof (vi_k _ _ _ _ _ _ _ Hv) as Hk.
  pose proof (vi_p _ _ _ _ _ _ _ Hv) as Hp.
  unfold water_impl. cbv zeta.
  pose proof (init_spec _ 0 _ (Zwf_well_founded 0 (gap (PArray.length xpa) 0)) eq_refl
                ltac:(change (φ 0) with 0%Z; apply to_Z_bounded) Inv_init) as HI0.
  match goal with |- context [augment ?a ?b ?c ?d ?e ?f] =>
    destruct (augment a b c d e f) as [r1 v0] eqn:Ha end.
  destruct (augment_spec n (xn + 1) Hm Hn _ (capT_ok n pa pb pc ia ib ic (len pa) 0 Hv
              ltac:(lia) ltac:(lia)) _ _ 0 0 _ eq_refl HI0 ltac:(lia) r1 v0 Ha)
    as [HI1 Hmf0].
  assert (Hk1 : (φ (PArray.length xia + 1)) = ((φ (PArray.length xia)) + 1)%Z).
  { rewrite add_spec. change (φ 1) with 1%Z. rewrite Z.mod_small; [reflexivity|].
    rewrite wB_val. lia. }
  set (out0 := (PArray.make (PArray.length xia + 1) 0).[0 <- v0]).
  assert (Lo : (φ (PArray.length out0)) = ((φ (PArray.length xia)) + 1)%Z).
  { unfold out0. rewrite alength_set, alength_make.
    replace (PArray.length xia + 1 <=? PArray.max_length) with true; [exact Hk1|].
    symmetry. rewrite leb_spec, Hk1. change (φ PArray.max_length) with 4194303%Z. lia. }
  destruct (imp_spec _ 0 r1 v0 out0 (Zwf_well_founded 0 (gap (PArray.length xia) 0)) eq_refl
              ltac:(change (φ 0) with 0%Z; apply to_Z_bounded) HI1 Lo) as [Hlen Hall].
  { intros s Hs. change (nv 0) with 0%N in Hs. replace s with 0%N by lia.
    unfold out0. rewrite cell_set.
    - change (0 =? nv 0)%N with true. exact Hmf0.
    - rewrite alength_make.
      replace (PArray.length xia + 1 <=? PArray.max_length) with true.
      + change (φ 0) with 0%Z. lia.
      + symmetry. rewrite leb_spec, Hk1. change (φ PArray.max_length) with 4194303%Z. lia.
    - rewrite wB_val. lia. }
  set (out := imp_loop xia xib xic (xn + 1) (PArray.length xia) 0 r1 v0 out0
                (Zwf_well_founded 0 (gap (PArray.length xia) 0))) in *.
  set (K := (List.length ia + 1)%nat).
  assert (HK : Z.of_nat K = (φ (PArray.length out))) by (unfold K; unfold len in Lk; lia).
  set (o := map (fun i => Z.to_N (cell out (N.of_nat i))) (seq 0 K)).
  assert (Ho : forall i, (i < K)%nat -> nth_error o i = Some (Z.to_N (cell out (N.of_nat i)))).
  { intros i Hi. unfold o. rewrite nth_error_map, nth_error_seq.
    destruct (Nat.ltb_spec i K); [reflexivity | lia]. }
  assert (Hol : List.length o = K) by (unfold o; rewrite length_map, length_seq; reflexivity).
  exists o. split.
  - split.
    + rewrite Hol. exact HK.
    + intros i Hi. rewrite Hol in Hi. exists (Z.to_N (cell out (N.of_nat i))).
      split; [exact (Ho i Hi)|].
      assert (Hc : Z.to_N (φ (PArray.get@{Set} out (of_nat i))) = Z.to_N (cell out (N.of_nat i)))
        by (unfold cell; rewrite nat_N_Z; reflexivity).
      exact Hc.
  - split.
    + unfold len. rewrite Hol. unfold K. lia.
    + intros t Ht. unfold len in Ht. rewrite Hol in Ht.
      unfold Prelude.get. erewrite nth_error_nth; [|apply Ho; lia].
      rewrite N2Nat.id. apply Hall. unfold K in Ht. unfold len. lia.
Qed.

End Main.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition water : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint := water_impl.

Lemma water_correct :
  forall (n : N) (pa pb pc ia ib ic : list N)
         (xn : uint) (xpa xpb xpc xia xib xic : array uint),
  valid_input n pa pb pc ia ib ic ->
  repr xn n -> repr xpa pa -> repr xpb pb -> repr xpc pc ->
  repr xia ia -> repr xib ib -> repr xic ic ->
  exists o : list N, repr (water xn xpa xpb xpc xia xib xic) o /\
    water_spec n pa pb pc ia ib ic o.
Proof.
  intros n pa pb pc ia ib ic xn xpa xpb xpc xia xib xic Hv Rn Rpa Rpb Rpc Ria Rib Ric.
  exact (water_main n pa pb pc ia ib ic xn xpa xpb xpc xia xib xic Hv Rn
           Rpa Rpb Rpc Ria Rib Ric).
Qed.
