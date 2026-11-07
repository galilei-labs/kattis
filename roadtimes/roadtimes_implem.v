(* Implementation of roadtimes.spec: Floyd-Warshall with a successor
   table, then the two-phase simplex method (lexicographic pivoting rule) on
   an exact rational tableau, two solves per query.

   Code.
   - P_RP: the n x n matrix is flattened (fill2); Floyd-Warshall on two flat
     n*n tables, distances D (no road: INF = 2^30) and successors X, the k
     loop outermost, in place (fw_cell).  scan_roads numbers the roads
     (positive entries) in row-major order: I.[i*n+j] is the index of road
     (i, j), P.[e] its position.  walk follows the successors from s to d
     (erased Acc on D.[cur*n+d], which strictly decreases along the walk) and
     counts the roads used in a flat array cnt of length E.
   - The LP (bound_rows, deliv_row, build_T): one variable per road,
     x_e = (minutes on road e) - (its length) in [0, length_e]; columns
     x_e (e < E), the slack y_e of x_e <= length_e (E + e), the artificial
     variable of delivery k (2E + k); rows x_e + y_e = length_e and, for
     delivery k, sum_e cnt_k(e) x_e + a_k = t_k - D_k (row negated but a_k
     when the right-hand side is negative).  One flat array of rationals
     (QArith Q, kept reduced by zgcd), m = E + R rows of w = 2E + R + 1
     cells, the last column being the right-hand side.
   - P_SP: the simplex.  enter: first allowed column of negative reduced
     cost; leave: lexicographic minimum ratio, the lexicographic vector of a
     row being its right-hand side followed by its entries in the columns of
     the initial basis (E .. N-1); pivot: in place, row by row.  sloop
     recurses on an erased Acc of the pivot relation.  P_SV: phase 1
     minimises the sum of the artificial variables once; phase 2 runs, for
     each query, from a copy of the phase-1 tableau, with the columns of
     zero phase-1 reduced cost before the artificial ones allowed, on the
     cost vector of the query route (min) and on its opposite (max).
   - The answer of a query is D_q + min and D_q - min(-cost), each turned
     into a float by q2f: floor(q * 2^36) as an int, divided by 2^36.
   - Every loop is the forl / loop combinator (erased Acc (Zwf 0) on
     hi - i), or an erased Acc on a Z measure (walk, zofi, iofz), or the
     erased Acc of sloop.  No nat in the code; Z only inside the LP values
     (rationals) and the conversions zofi / iofz around them.

   Proof.
   - P_SM: the simplex on functions nat -> nat -> R.  The invariant Valid
     (the tableau has the solutions of the initial system, its basis
     columns are unit columns, the reduced costs vanish on the basis and
     express the cost on the solutions, every row is lexicographically
     positive) is kept by a pivot chosen by the rule (pivot_valid), and the
     reduced-cost vector strictly increases (pivot_lex).  Termination
     (acc_fin): the reduced costs are determined by the basis
     (determination, through test vectors), bases are finitely many
     (all_keys), so the lexicographically increasing chain is finite.
     Reading the answer: the basic solution is feasible and attains the
     objective, nothing feasible is below it (opt_lb, phase1_zero,
     phase2_opt); an unbounded column contradicts boundedness (no_ray).
   - P_SP / P_SL / P_SV: the array program computes these functions
     (cellZ_set, scale_row_spec, elim_all_spec, pivot_corr, lexless_spec,
     leave_all, enter_all), acc_VS builds the Acc proof, phase2_min states
     the result: the value is the minimum of the cost over the feasible
     set, attained.
   - P_G, P_FWM, P_FWP, P_FWQ, P_WK: Floyd-Warshall keeps, after k rounds,
     D[a][b] <= D[a][c] + D[c][b] for c < k, D <= road lengths, and
     D[a][b] >= len(a, X[a][b]) + D[X[a][b]][b] (inv_step); hence D is below
     the length of every route (inv_route) and the successor walk builds a
     route of length <= D, i.e. a shortest one, i.e. the unique one.  A
     shortest route has no repeated city (shortest_nodup), so D_q < INF.
   - P_BLD: the tableau built is the formula T0f, unit columns, non-negative
     right-hand sides (build_ok: the hypotheses P1ok of the driver).
   - P_MS3: x in [0, length] satisfying the delivery rows <-> speed limits
     in [30, 60] explaining the deliveries (v = 60 len / (len + x)), and
     the duration of a route is its length plus the x of its roads
     (dur_gen, possible_iff); the LP is bounded and feasible
     (vi_consistent); so D_q + min is the least possible duration and
     D_q - min(-cost) the greatest (query_sem); q2f is within 2^-35
     (q2f_spec, through ReprFloat).
   - P_MF: the answer array, cell by cell. *)
From Speck Require Import Prelude.
From Stdlib Require Import Uint63 PArray ZifyUint63 Arith ZArith NArith List Bool Lia Zwf.
From Stdlib Require Import Reals Lra QArith Qreals PrimFloat ListDec Decidable.
From Stdlib Require Sint63.
From Respeced Require Import Repr ZBig ReprFloat.
From Flocq Require Core.Raux Core.Zaux.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ================================================================== *)
Section P_B.
Open Scope uint63_scope.


(* ------------------------------------------------------------------ *)
(* The termination device and the loop combinator                     *)
(* ------------------------------------------------------------------ *)

Definition odec {A : Type} (o : option A) : {x : A | o = Some x} + {o = None} :=
  match o as o0 return {x : A | o0 = Some x} + {o0 = None} with
  | Some x => inleft (exist _ x eq_refl)
  | None => inright eq_refl
  end.

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

(* for i = lo .. hi-1: s := f i s *)
Definition forl (lo hi : int) (f : int -> St -> St) (s : St) : St :=
  loop hi (fun _ _ => true) f lo s.

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

Lemma for_inv : forall (P : int -> St -> Prop) (lo hi : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P lo s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P j t -> P (j + 1) (f j t)) ->
  P hi (forl lo hi f s).
Proof.
  intros P lo hi f s Hle Hp Hstep. unfold forl.
  destruct (loop_inv P hi lo (fun _ _ => true) f s Hle Hp) as (j & _ & Pj & [E | [_ E]]).
  - intros j t Hj Pt _. apply Hstep; auto.
  - apply to_Z_inj in E. subst j. exact Pj.
  - discriminate.
Qed.

(* the same, with the invariant indexed by Z *)
Lemma for_invZ : forall (P : Z -> St -> Prop) (lo hi : int) f s,
  (to_Z lo <= to_Z hi)%Z -> P (to_Z lo) s ->
  (forall j t, (to_Z lo <= to_Z j < to_Z hi)%Z -> P (to_Z j) t -> P (to_Z j + 1)%Z (f j t)) ->
  P (to_Z hi) (forl lo hi f s).
Proof.
  intros P lo hi f s Hle Hp Hstep.
  apply (for_inv (fun j t => P (to_Z j) t)); auto.
  intros j t Hj Pt. pose proof (to_Z_bounded hi).
  replace (to_Z (j + 1)) with (to_Z j + 1)%Z by sia. apply Hstep; auto.
Qed.

End Loop.

(* ------------------------------------------------------------------ *)
(* PArray plumbing                                                     *)
(* ------------------------------------------------------------------ *)


Set Universe Polymorphism.
Lemma gssQ : forall (t : array Q) (i : int) (v : Q),
  (to_Z i < to_Z (PArray.length t))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. apply Uint63.ltb_spec in H. exact (get_set_same Q t i v H). Qed.

Lemma gsoQ : forall (t : array Q) (i j : int) (v : Q), i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other Q t i j v H). Qed.

Lemma gsoZQ : forall (t : array Q) (i j : int) (v : Q), to_Z i <> to_Z j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. apply gsoQ. intros E. apply H. rewrite E. reflexivity. Qed.

Lemma lsetQ : forall (t : array Q) (i : int) (v : Q), PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set Q t i v). Qed.

Lemma lmakeQ : forall (n : int) (v : Q), (to_Z n <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make Q n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma gmakeQ : forall (n i : int) (v : Q), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make Q v n i). Qed.

Lemma lboundQ : forall (t : array Q), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length Q t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma gcopyQ : forall (t : array Q) i, (PArray.copy t).[i] = t.[i].
Proof. intros. exact (get_copy Q t i). Qed.

Lemma lcopyQ : forall (t : array Q), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros. exact (length_copy Q t). Qed.


Lemma gssI : forall (t : array int) (i : int) (v : int),
  (to_Z i < to_Z (PArray.length t))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. apply Uint63.ltb_spec in H. exact (get_set_same int t i v H). Qed.

Lemma gsoI : forall (t : array int) (i j : int) (v : int), i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other int t i j v H). Qed.

Lemma gsoZI : forall (t : array int) (i j : int) (v : int), to_Z i <> to_Z j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. apply gsoI. intros E. apply H. rewrite E. reflexivity. Qed.

Lemma lsetI : forall (t : array int) (i : int) (v : int), PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set int t i v). Qed.

Lemma lmakeI : forall (n : int) (v : int), (to_Z n <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make int n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma gmakeI : forall (n i : int) (v : int), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make int v n i). Qed.

Lemma lboundI : forall (t : array int), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length int t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma gcopyI : forall (t : array int) i, (PArray.copy t).[i] = t.[i].
Proof. intros. exact (get_copy int t i). Qed.

Lemma lcopyI : forall (t : array int), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros. exact (length_copy int t). Qed.


Lemma gssBo : forall (t : array bool) (i : int) (v : bool),
  (to_Z i < to_Z (PArray.length t))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. apply Uint63.ltb_spec in H. exact (get_set_same bool t i v H). Qed.

Lemma gsoBo : forall (t : array bool) (i j : int) (v : bool), i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other bool t i j v H). Qed.

Lemma gsoZBo : forall (t : array bool) (i j : int) (v : bool), to_Z i <> to_Z j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. apply gsoBo. intros E. apply H. rewrite E. reflexivity. Qed.

Lemma lsetBo : forall (t : array bool) (i : int) (v : bool), PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set bool t i v). Qed.

Lemma lmakeBo : forall (n : int) (v : bool), (to_Z n <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make bool n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma gmakeBo : forall (n i : int) (v : bool), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make bool v n i). Qed.

Lemma lboundBo : forall (t : array bool), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length bool t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma gcopyBo : forall (t : array bool) i, (PArray.copy t).[i] = t.[i].
Proof. intros. exact (get_copy bool t i). Qed.

Lemma lcopyBo : forall (t : array bool), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros. exact (length_copy bool t). Qed.


Lemma gssF : forall (t : array float) (i : int) (v : float),
  (to_Z i < to_Z (PArray.length t))%Z -> t.[i <- v].[i] = v.
Proof. intros t i v H. apply Uint63.ltb_spec in H. exact (get_set_same float t i v H). Qed.

Lemma gsoF : forall (t : array float) (i j : int) (v : float), i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (get_set_other float t i j v H). Qed.

Lemma gsoZF : forall (t : array float) (i j : int) (v : float), to_Z i <> to_Z j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. apply gsoF. intros E. apply H. rewrite E. reflexivity. Qed.

Lemma lsetF : forall (t : array float) (i : int) (v : float), PArray.length t.[i <- v] = PArray.length t.
Proof. intros. exact (length_set float t i v). Qed.

Lemma lmakeF : forall (n : int) (v : float), (to_Z n <= 4194303)%Z -> PArray.length (PArray.make n v) = n.
Proof.
  intros n v H.
  assert (E : PArray.length (PArray.make n v) = if n <=? max_length then n else max_length)
    by exact (length_make float n v).
  etransitivity; [exact E|].
  replace (n <=? max_length) with true; [reflexivity|].
  symmetry. rewrite Uint63.leb_spec. exact H.
Qed.

Lemma gmakeF : forall (n i : int) (v : float), (PArray.make n v).[i] = v.
Proof. intros. exact (get_make float v n i). Qed.

Lemma lboundF : forall (t : array float), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length float t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma gcopyF : forall (t : array float) i, (PArray.copy t).[i] = t.[i].
Proof. intros. exact (get_copy float t i). Qed.

Lemma lcopyF : forall (t : array float), PArray.length (PArray.copy t) = PArray.length t.
Proof. intros. exact (length_copy float t). Qed.


Unset Universe Polymorphism.

Lemma to_Z_of_Z_small : forall z, (0 <= z < wB)%Z -> to_Z (of_Z z) = z.
Proof. intros z Hz. rewrite of_Z_spec. apply Z.mod_small; exact Hz. Qed.

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma of_Z_to_Z : forall i : int, of_Z (to_Z i) = i.
Proof. intros i. apply of_to_Z. Qed.

(* ------------------------------------------------------------------ *)
(* int <-> Z without nat                                               *)
(* ------------------------------------------------------------------ *)

Lemma dec_half : forall i : int, (i =? 0) = false -> Zwf 0 (to_Z (i / 2)) (to_Z i).
Proof.
  intros i H. assert (to_Z i <> 0%Z).
  { intros E. assert (i = 0) by (apply to_Z_inj; exact E). subst i. discriminate. }
  pose proof (to_Z_bounded i). unfold Zwf. sia.
Qed.

Fixpoint zofi_rec (i : int) (H : Acc (Zwf 0) (to_Z i)) {struct H} : Z :=
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.

Definition zofi (i : int) : Z := zofi_rec i (Zwf_well_founded 0 (to_Z i)).

Lemma zofi_rec_eq : forall i H, zofi_rec i H =
  match bdec (i =? 0) with
  | left _ => 0%Z
  | right Hn =>
      let r := zofi_rec (i / 2) (Acc_inv H (dec_half i Hn)) in
      let bit := if i mod 2 =? 0 then 0%Z else 1%Z in
      (2 * r + bit)%Z
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma zofi_spec : forall i, zofi i = to_Z i.
Proof.
  assert (G : forall n i H, to_Z i = n -> zofi_rec i H = to_Z i).
  { intros n. induction n as [n IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros i H En. rewrite zofi_rec_eq. destruct (bdec (i =? 0)) as [E | E].
    - apply Uint63.eqb_spec in E. subst i. reflexivity.
    - cbv zeta. rewrite (IH (to_Z (i / 2))); [| rewrite <- En; apply dec_half; exact E | reflexivity].
      pose proof (to_Z_bounded i).
      destruct (i mod 2 =? 0) eqn:Em.
      + apply Uint63.eqb_spec in Em. apply (f_equal to_Z) in Em. sia.
      + apply Uint63.eqb_false_spec in Em.
        assert (to_Z (i mod 2) <> 0%Z) by (intros E'; apply Em, to_Z_inj; exact E'). sia. }
  intros i. unfold zofi. apply (G _ i _ eq_refl).
Qed.

(* signed reading *)
Definition zofs (i : int) : Z :=
  if (i <? 4611686018427387904) then zofi i else (zofi i - 9223372036854775808)%Z.

Lemma zofs_spec : forall i, zofs i = Sint63.to_Z i.
Proof.
  intros i. unfold zofs. rewrite zofi_spec. unfold Sint63.to_Z.
  change Sint63Axioms.min_int with (4611686018427387904 : int).
  pose proof (to_Z_bounded i).
  destruct (i <? 4611686018427387904) eqn:E1; [reflexivity|].
  rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in E1.
  change (to_Z 4611686018427387904) with 4611686018427387904%Z in E1.
  assert (to_Z (0 - i) = 9223372036854775808 - to_Z i)%Z by sia. lia.
Qed.

Lemma dec_zhalf : forall z, (0 <? z)%Z = true -> Zwf 0 (z / 2) z.
Proof. intros z H. apply Z.ltb_lt in H. unfold Zwf. split; [lia|apply Z.div_lt]; lia. Qed.

Fixpoint iofz_rec (z : Z) (H : Acc (Zwf 0) z) {struct H} : int :=
  match bdec (0 <? z)%Z with
  | left Hz =>
      let r := iofz_rec (z / 2) (Acc_inv H (dec_zhalf z Hz)) in
      if Z.eqb (z mod 2) 0 then r + r else r + r + 1
  | right _ => 0
  end.

Definition iofz (z : Z) : int := iofz_rec z (Zwf_well_founded 0 z).

Lemma iofz_rec_eq : forall z H, iofz_rec z H =
  match bdec (0 <? z)%Z with
  | left Hz =>
      let r := iofz_rec (z / 2) (Acc_inv H (dec_zhalf z Hz)) in
      if Z.eqb (z mod 2) 0 then r + r else r + r + 1
  | right _ => 0
  end.
Proof. intros. destruct H; reflexivity. Qed.

Lemma iofz_spec : forall z, (0 <= z < wB)%Z -> to_Z (iofz z) = z.
Proof.
  assert (G : forall z H, (0 <= z < wB)%Z -> to_Z (iofz_rec z H) = z).
  { intros z. induction z as [z IH] using (well_founded_induction (Zwf_well_founded 0)).
    intros H Hz. rewrite iofz_rec_eq. destruct (bdec (0 <? z)%Z) as [E|E].
    - cbv zeta. pose proof E as E'. apply Z.ltb_lt in E'.
      assert (Hr : to_Z (iofz_rec (z / 2) (Acc_inv H (dec_zhalf z E))) = (z / 2)%Z).
      { apply IH; [apply dec_zhalf; exact E|]. split; [apply Z.div_pos|]; lia. }
      revert Hr. generalize (iofz_rec (z / 2) (Acc_inv H (dec_zhalf z E))). intros r Hr.
      pose proof (Z.div_mod z 2 ltac:(lia)). pose proof (Z.mod_pos_bound z 2 ltac:(lia)).
      destruct (Z.eqb_spec (z mod 2) 0).
      + rewrite add_spec, Hr. rewrite Z.mod_small; lia.
      + rewrite add_spec, add_spec, Hr. change (to_Z 1) with 1%Z.
        rewrite (Z.mod_small (z/2 + z/2)) by lia. rewrite Z.mod_small; lia.
    - apply Z.ltb_ge in E. replace z with 0%Z by lia. reflexivity. }
  intros z Hz. apply G; exact Hz.
Qed.

(* ------------------------------------------------------------------ *)
(* Rationals                                                           *)
(* ------------------------------------------------------------------ *)

Definition qred (q : Q) : Q :=
  let n := Qnum q in let d := Zpos (Qden q) in let g := zgcd n d in
  Qmake (n / g) (Z.to_pos (d / g)).

Lemma qred_R : forall q, Q2R (qred q) = Q2R q.
Proof.
  intros [n d]. unfold qred, Q2R. simpl. rewrite zgcd_spec.
  set (g := Z.gcd n (Zpos d)).
  assert (G0 : (0 <= g)%Z) by apply Z.gcd_nonneg.
  assert (G1 : g <> 0%Z) by (intros E; apply Z.gcd_eq_0 in E; lia).
  destruct (Z.gcd_divide_l n (Zpos d)) as [a Ha].
  destruct (Z.gcd_divide_r n (Zpos d)) as [b Hb]. fold g in Ha, Hb.
  assert (Ea : (n / g)%Z = a) by (rewrite Ha; apply Z.div_mul; exact G1).
  assert (Eb : (Zpos d / g)%Z = b) by (rewrite Hb; apply Z.div_mul; exact G1).
  rewrite Ea, Eb. assert (Bp : (0 < b)%Z) by nia.
  rewrite Z2Pos.id by exact Bp. rewrite Ha, Hb. rewrite !mult_IZR.
  assert (IZR g <> 0%R) by (apply not_0_IZR; exact G1).
  assert (IZR b <> 0%R) by (apply not_0_IZR; lia).
  field. split; assumption.
Qed.

Definition qadd (a b : Q) : Q := qred (a + b).
Definition qsub (a b : Q) : Q := qred (a - b).
Definition qmul (a b : Q) : Q := qred (a * b).

Lemma qadd_R : forall a b, Q2R (qadd a b) = (Q2R a + Q2R b)%R.
Proof. intros. unfold qadd. rewrite qred_R, Q2R_plus. reflexivity. Qed.
Lemma qsub_R : forall a b, Q2R (qsub a b) = (Q2R a - Q2R b)%R.
Proof. intros. unfold qsub. rewrite qred_R, Q2R_minus. reflexivity. Qed.
Lemma qmul_R : forall a b, Q2R (qmul a b) = (Q2R a * Q2R b)%R.
Proof. intros. unfold qmul. rewrite qred_R, Q2R_mult. reflexivity. Qed.

Lemma Q2R_0 : Q2R 0 = 0%R.
Proof. unfold Q2R. simpl. ring. Qed.

Lemma Q2R_1 : Q2R 1 = 1%R.
Proof. unfold Q2R. simpl. field. Qed.

Lemma Q2R_inject : forall z, Q2R (inject_Z z) = IZR z.
Proof. intros z. unfold Q2R, inject_Z. simpl. field. Qed.

Lemma Qinv_R : forall a, Q2R a <> 0%R -> Q2R (Qinv a) = (/ Q2R a)%R.
Proof.
  intros a H. apply Q2R_inv. intros E. apply H. rewrite (Qeq_eqR _ _ E). apply Q2R_0.
Qed.

Definition qltb (a b : Q) : bool := Z.ltb (Qnum a * Zpos (Qden b)) (Qnum b * Zpos (Qden a)).

Lemma qltb_R : forall a b, qltb a b = true <-> (Q2R a < Q2R b)%R.
Proof.
  intros a b. unfold qltb. rewrite Z.ltb_lt. split; intros H.
  - apply Qlt_Rlt. exact H.
  - apply Rlt_Qlt in H. exact H.
Qed.

Lemma qltb_R_false : forall a b, qltb a b = false <-> (Q2R b <= Q2R a)%R.
Proof.
  intros a b. rewrite <- Bool.not_true_iff_false, qltb_R. split; intros H.
  - apply Rnot_lt_le; exact H.
  - apply Rle_not_lt; exact H.
Qed.

Definition qzerob (a : Q) : bool := Z.eqb (Qnum a) 0.

Lemma qzerob_R : forall a, qzerob a = true <-> Q2R a = 0%R.
Proof.
  intros [n d]. unfold qzerob, Q2R. simpl. rewrite Z.eqb_eq. split; intros H.
  - subst. ring.
  - assert (Hd : IZR (Zpos d) <> 0%R) by apply IZR_nz.
    apply Rmult_integral in H. destruct H as [H|H].
    + apply eq_IZR_R0; exact H.
    + exfalso. apply (Rinv_neq_0_compat _ Hd). exact H.
Qed.

Lemma qzerob_R_false : forall a, qzerob a = false <-> Q2R a <> 0%R.
Proof. intros a. rewrite <- Bool.not_true_iff_false, qzerob_R. tauto. Qed.
End P_B.

(* ================================================================== *)
Section P_SM.
Import ListNotations.
Open Scope R_scope.

(* ------------------------------------------------------------------ *)
(* Finite sums over nat indices                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint sumR (n : nat) (f : nat -> R) : R :=
  match n with O => 0 | S n' => sumR n' f + f n' end.

Lemma sumR_ext : forall n f g, (forall j, (j < n)%nat -> f j = g j) -> sumR n f = sumR n g.
Proof.
  induction n; intros f g H; simpl; [reflexivity|].
  rewrite (IHn f g) by (intros; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma sumR_plus : forall n f g, sumR n (fun j => f j + g j) = sumR n f + sumR n g.
Proof. induction n; intros; simpl; [lra|]. rewrite IHn. lra. Qed.

Lemma sumR_minus : forall n f g, sumR n (fun j => f j - g j) = sumR n f - sumR n g.
Proof. induction n; intros; simpl; [lra|]. rewrite IHn. lra. Qed.

Lemma sumR_scal : forall n a f, sumR n (fun j => a * f j) = a * sumR n f.
Proof. induction n; intros; simpl; [lra|]. rewrite IHn. lra. Qed.

Lemma sumR_zero : forall n f, (forall j, (j < n)%nat -> f j = 0) -> sumR n f = 0.
Proof.
  induction n; intros f H; simpl; [reflexivity|].
  rewrite IHn by (intros; apply H; lia). rewrite H by lia. lra.
Qed.

Lemma sumR_swap : forall n m F,
  sumR n (fun j => sumR m (fun k => F j k)) = sumR m (fun k => sumR n (fun j => F j k)).
Proof.
  induction n; intros; simpl.
  - symmetry; apply sumR_zero; auto.
  - rewrite IHn. rewrite <- sumR_plus. reflexivity.
Qed.

Lemma sumR_delta : forall n a g,
  sumR n (fun j => if Nat.eqb j a then g j else 0) = if Nat.ltb a n then g a else 0.
Proof.
  induction n; intros; simpl; [reflexivity|]. rewrite IHn.
  destruct (Nat.eqb_spec n a); destruct (Nat.ltb_spec a n); destruct (Nat.ltb_spec a (S n));
    subst; try lia; lra.
Qed.

Lemma sumR_nonneg : forall n f, (forall j, (j < n)%nat -> 0 <= f j) -> 0 <= sumR n f.
Proof.
  induction n; intros f H; simpl; [lra|].
  pose proof (IHn f ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)). lra.
Qed.

Lemma sumR_le : forall n f g, (forall j, (j < n)%nat -> f j <= g j) -> sumR n f <= sumR n g.
Proof.
  induction n; intros f g H; simpl; [lra|].
  pose proof (IHn f g ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)). lra.
Qed.

Lemma sumR_nonneg_zero : forall n f, (forall j, (j < n)%nat -> 0 <= f j) -> sumR n f = 0 ->
  forall j, (j < n)%nat -> f j = 0.
Proof.
  induction n; intros f H E j Hj; [lia|]. simpl in E.
  pose proof (sumR_nonneg n f ltac:(intros; apply H; lia)). pose proof (H n ltac:(lia)).
  destruct (Nat.eq_dec j n).
  - subst. lra.
  - apply IHn; [intros; apply H; lia | lra | lia].
Qed.

Lemma sumR_split : forall a b f, sumR (a + b) f = sumR a f + sumR b (fun i => f (a + i)%nat).
Proof.
  intros a b f. induction b; simpl.
  - rewrite Nat.add_0_r. lra.
  - rewrite Nat.add_succ_r. simpl. rewrite IHb. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Lexicographic order on the first n values of a function             *)
(* ------------------------------------------------------------------ *)

Definition lexgt0 (n : nat) (f : nat -> R) : Prop :=
  exists p, (p < n)%nat /\ (forall q, (q < p)%nat -> f q = 0) /\ 0 < f p.
Definition lexz (n : nat) (f : nat -> R) : Prop := forall q, (q < n)%nat -> f q = 0.
Definition lexge0 (n : nat) (f : nat -> R) : Prop := lexgt0 n f \/ lexz n f.
Definition lexlt (n : nat) (f g : nat -> R) : Prop := lexgt0 n (fun p => g p - f p).

Lemma lexgt0_ext : forall n f g, (forall p, (p < n)%nat -> f p = g p) -> lexgt0 n f -> lexgt0 n g.
Proof.
  intros n f g E (p & Hp & Hz & Hpos). exists p. split; [lia|]. split.
  - intros q Hq. rewrite <- E by lia. apply Hz; lia.
  - rewrite <- E by lia. exact Hpos.
Qed.

Lemma lexge0_ext : forall n f g, (forall p, (p < n)%nat -> f p = g p) -> lexge0 n f -> lexge0 n g.
Proof.
  intros n f g E [H|H].
  - left. eapply lexgt0_ext; eauto.
  - right. intros q Hq. rewrite <- E by lia. apply H; lia.
Qed.

Lemma lexgt0_not_z : forall n f, lexgt0 n f -> ~ lexz n f.
Proof. intros n f (p & Hp & _ & Hpos) Z. rewrite Z in Hpos by lia. lra. Qed.

Lemma lexgt0_add : forall n f g, lexgt0 n f -> lexge0 n g -> lexgt0 n (fun p => f p + g p).
Proof.
  intros n f g (p & Hp & Hz & Hpos) [(p' & Hp' & Hz' & Hpos') | Z].
  - destruct (Nat.lt_trichotomy p p') as [L|[E|L]].
    + exists p. split; [lia|]. split.
      * intros q Hq. rewrite Hz, Hz' by lia. lra.
      * rewrite (Hz' p) by lia. lra.
    + subst. exists p'. split; [lia|]. split.
      * intros q Hq. rewrite Hz, Hz' by lia. lra.
      * lra.
    + exists p'. split; [lia|]. split.
      * intros q Hq. rewrite Hz, Hz' by lia. lra.
      * rewrite (Hz p') by lia. lra.
  - exists p. split; [lia|]. split.
    + intros q Hq. rewrite Hz, Z by lia. lra.
    + rewrite Z by lia. lra.
Qed.

Lemma lexgt0_scale : forall n a f, 0 < a -> lexgt0 n f -> lexgt0 n (fun p => a * f p).
Proof.
  intros n a f Ha (p & Hp & Hz & Hpos). exists p. split; [lia|]. split.
  - intros q Hq. rewrite Hz by lia. ring.
  - apply Rmult_lt_0_compat; assumption.
Qed.

Lemma lexge0_scale : forall n a f, 0 < a -> lexge0 n f -> lexge0 n (fun p => a * f p).
Proof.
  intros n a f Ha [H|H].
  - left. apply lexgt0_scale; auto.
  - right. intros q Hq. rewrite H by lia. ring.
Qed.

Lemma lex_total : forall n f, lexgt0 n f \/ lexz n f \/ lexgt0 n (fun p => - f p).
Proof.
  induction n; intros f.
  - right; left. intros q Hq; lia.
  - destruct (IHn f) as [H|[H|H]].
    + left. destruct H as (p&Hp&Hz&Hpos). exists p. split; [lia|]. auto.
    + destruct (Rtotal_order 0 (f n)) as [L|[E|L]].
      * left. exists n. split; [lia|]. split; auto.
      * right; left. intros q Hq. destruct (Nat.eq_dec q n); [subst; auto | apply H; lia].
      * right; right. exists n. split; [lia|]. split.
        -- intros q Hq. rewrite H by lia. lra.
        -- lra.
    + right; right. destruct H as (p&Hp&Hz&Hpos). exists p. split; [lia|]. auto.
Qed.

Lemma lexlt_trans : forall n f g h, lexlt n f g -> lexlt n g h -> lexlt n f h.
Proof.
  intros n f g h H1 H2. unfold lexlt in *.
  eapply lexgt0_ext; [| apply (lexgt0_add n _ _ H2 (or_introl H1))].
  intros p Hp. simpl. lra.
Qed.

Lemma lexlt_irrefl : forall n f g, (forall p, (p < n)%nat -> f p = g p) -> ~ lexlt n f g.
Proof.
  intros n f g E H. apply (lexgt0_not_z n _ H). intros q Hq. rewrite E by lia. lra.
Qed.

Lemma not_lexlt : forall n f g, ~ lexlt n f g -> lexge0 n (fun p => f p - g p).
Proof.
  intros n f g H. destruct (lex_total n (fun p => g p - f p)) as [A|[A|A]].
  - contradiction.
  - right. intros q Hq. specialize (A q Hq). cbv beta in A. lra.
  - left. eapply lexgt0_ext; [|exact A]. intros; simpl; lra.
Qed.

Lemma lex_first_nonneg : forall n f, (0 < n)%nat -> lexgt0 n f -> 0 <= f O.
Proof.
  intros n f Hn (p & Hp & Hz & Hpos). destruct p.
  - lra.
  - rewrite Hz by lia. lra.
Qed.

(* ------------------------------------------------------------------ *)
(* Acc from finiteness: a relation along which a lexicographic vector   *)
(* strictly increases, and which the key (a finite datum) determines.   *)
(* ------------------------------------------------------------------ *)

Section AccFin.
Variables (S : Type) (Rel : S -> S -> Prop) (V : S -> Prop) (n : nat)
  (Wf : S -> nat -> R) (key : S -> list nat) (KS : list (list nat)).
Hypothesis step : forall s s', V s -> Rel s' s -> V s' /\ lexlt n (Wf s) (Wf s').
Hypothesis keys_in : forall s, V s -> In (key s) KS.
Hypothesis det : forall s1 s2, V s1 -> V s2 -> key s1 = key s2 ->
  forall p, (p < n)%nat -> Wf s1 p = Wf s2 p.

Lemma acc_fin_aux : forall len K s, (length K <= len)%nat -> V s ->
  (forall s', V s' -> lexlt n (Wf s) (Wf s') -> In (key s') K) -> Acc Rel s.
Proof.
  induction len; intros K s HK Vs HA; constructor; intros s' Hr;
    destruct (step s s' Vs Hr) as [Vs' Hlt].
  - destruct K; [|simpl in HK; lia]. exfalso. exact (HA s' Vs' Hlt).
  - apply (IHlen (remove (list_eq_dec Nat.eq_dec) (key s') K)).
    + pose proof (remove_length_lt (list_eq_dec Nat.eq_dec) K (key s') (HA s' Vs' Hlt)). lia.
    + exact Vs'.
    + intros s'' Vs'' Hlt'. apply in_in_remove.
      * intros E. apply (lexlt_irrefl n (Wf s') (Wf s'')); [|exact Hlt'].
        intros p Hp. symmetry. apply det; auto.
      * apply HA; auto. eapply lexlt_trans; eauto.
Qed.

Lemma acc_fin : forall s, V s -> Acc Rel s.
Proof.
  intros s Vs. apply (acc_fin_aux (length KS) KS s (le_n _) Vs).
  intros s' Vs' _. apply keys_in; exact Vs'.
Qed.
End AccFin.

Fixpoint all_keys (m N : nat) : list (list nat) :=
  match m with
  | O => [[]]
  | S m' => flat_map (fun l => map (fun a => a :: l) (seq 0 N)) (all_keys m' N)
  end.

Lemma all_keys_in : forall m N l, length l = m -> (forall a, In a l -> (a < N)%nat) ->
  In l (all_keys m N).
Proof.
  induction m; intros N l Hl Ha; destruct l; simpl in *; try discriminate.
  - left; reflexivity.
  - apply in_flat_map. exists l. split.
    + apply IHm; auto.
    + apply (in_map (fun a => a :: l)). apply in_seq. pose proof (Ha n (or_introl eq_refl)). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The simplex tableau, as functions                                   *)
(* ------------------------------------------------------------------ *)

Section Simplex.
Variables (m E0 : nat).
Local Notation N := (E0 + m)%nat.
Variable t0 : nat -> nat -> R.

Definition lin (row : nat -> R) (x : nat -> R) : R := sumR N (fun j => row j * x j).
Definition Sol (t : nat -> nat -> R) (x : nat -> R) : Prop :=
  forall k, (k < m)%nat -> lin (t k) x = t k N.
Definition lcol (p : nat) : nat := match p with O => N | S p' => (E0 + p')%nat end.
Definition rowvec (t : nat -> nat -> R) (k : nat) : nat -> R := fun p => t k (lcol p).
Definition Wv (o : nat -> R) : nat -> R := fun p => o (lcol p).
Definition delta (k k' : nat) : R := if Nat.eqb k k' then 1 else 0.

Definition unit0 : Prop := forall k i, (k < m)%nat -> (i < m)%nat ->
  t0 k (E0 + i)%nat = delta k i.

Record Valid (c : nat -> R) (t : nat -> nat -> R) (o : nat -> R) (bs : nat -> nat) : Prop := {
  v_sol : forall x, Sol t x <-> Sol t0 x;
  v_bs : forall k, (k < m)%nat -> (bs k < N)%nat;
  v_canon : forall k k', (k < m)%nat -> (k' < m)%nat -> t k (bs k') = delta k k';
  v_ocanon : forall k, (k < m)%nat -> o (bs k) = 0;
  v_obj : forall x, Sol t0 x -> sumR N (fun j => c j * x j) = lin o x - o N;
  v_lex : forall k, (k < m)%nat -> lexgt0 (S m) (rowvec t k)
}.

Definition pt (t : nat -> nat -> R) (r s : nat) : nat -> nat -> R :=
  fun k j => if Nat.eqb k r then t r j / t r s else t k j - t k s * (t r j / t r s).
Definition po (t : nat -> nat -> R) (o : nat -> R) (r s : nat) : nat -> R :=
  fun j => o j - o s * (t r j / t r s).
Definition pb (bs : nat -> nat) (r s : nat) : nat -> nat :=
  fun k => if Nat.eqb k r then s else bs k.

Definition LeaveOK (t : nat -> nat -> R) (r s : nat) : Prop :=
  (r < m)%nat /\ 0 < t r s /\
  forall k, (k < m)%nat -> 0 < t k s ->
    ~ lexlt (S m) (fun p => rowvec t k p / t k s) (fun p => rowvec t r p / t r s).

(* -- lin -- *)

Lemma lin_div : forall f a x, lin (fun j => f j / a) x = lin f x / a.
Proof.
  intros f a x. unfold lin.
  rewrite (sumR_ext _ _ (fun j => / a * (f j * x j))) by (intros; unfold Rdiv; ring).
  rewrite sumR_scal. unfold Rdiv. ring.
Qed.

Lemma lin_sub_scal : forall f g b x, lin (fun j => f j - b * g j) x = lin f x - b * lin g x.
Proof.
  intros f g b x. unfold lin.
  rewrite (sumR_ext _ _ (fun j => f j * x j - b * (g j * x j))) by (intros; ring).
  rewrite sumR_minus, sumR_scal. ring.
Qed.

Lemma lin_ext : forall f g x, (forall j, (j < N)%nat -> f j = g j) -> lin f x = lin g x.
Proof. intros f g x E. unfold lin. apply sumR_ext. intros j Hj. rewrite E by lia. reflexivity. Qed.

Lemma lin_ext_x : forall f x y, (forall j, (j < N)%nat -> x j = y j) -> lin f x = lin f y.
Proof. intros f x y E. unfold lin. apply sumR_ext. intros j Hj. rewrite E by lia. reflexivity. Qed.

(* -- the pivot keeps the solution set -- *)

Lemma pt_sol : forall t r s, (r < m)%nat -> t r s <> 0 ->
  forall x, Sol t x <-> Sol (pt t r s) x.
Proof.
  intros t r s Hr Hp x. unfold Sol, pt. split; intros H k Hk.
  - destruct (Nat.eqb_spec k r).
    + subst. rewrite lin_div, H by exact Hr. reflexivity.
    + rewrite lin_sub_scal, lin_div, H, H by assumption. reflexivity.
  - assert (Hr' : lin (t r) x = t r N).
    { specialize (H r Hr). rewrite Nat.eqb_refl, lin_div in H.
      replace (lin (t r) x) with (lin (t r) x / t r s * t r s) by (field; auto).
      rewrite H. field. auto. }
    destruct (Nat.eqb_spec k r).
    + subst. exact Hr'.
    + specialize (H k Hk). rewrite (proj2 (Nat.eqb_neq k r) n) in H.
      rewrite lin_sub_scal, lin_div, Hr' in H. lra.
Qed.

Lemma pt_canon : forall t bs r s, (r < m)%nat -> t r s <> 0 ->
  (forall k k', (k < m)%nat -> (k' < m)%nat -> t k (bs k') = delta k k') ->
  forall k k', (k < m)%nat -> (k' < m)%nat -> pt t r s k (pb bs r s k') = delta k k'.
Proof.
  intros t bs r s Hr Hp H k k' Hk Hk'. unfold pt, pb, delta.
  destruct (Nat.eqb_spec k' r); destruct (Nat.eqb_spec k r); subst.
  - rewrite Nat.eqb_refl. field. exact Hp.
  - replace (t r s / t r s) with 1 by (field; exact Hp).
    destruct (Nat.eqb_spec k r); [contradiction | ring].
  - rewrite (H r k') by assumption. unfold delta.
    destruct (Nat.eqb_spec r k'); [congruence|]. unfold Rdiv. ring.
  - rewrite (H r k'), (H k k') by assumption. unfold delta.
    destruct (Nat.eqb_spec r k'); [congruence|]. unfold Rdiv. ring.
Qed.

Lemma pt_ocanon : forall t o bs r s, (r < m)%nat -> t r s <> 0 ->
  (forall k k', (k < m)%nat -> (k' < m)%nat -> t k (bs k') = delta k k') ->
  (forall k, (k < m)%nat -> o (bs k) = 0) ->
  forall k, (k < m)%nat -> po t o r s (pb bs r s k) = 0.
Proof.
  intros t o bs r s Hr Hp H Ho k Hk. unfold po, pb.
  destruct (Nat.eqb_spec k r).
  - field. exact Hp.
  - rewrite Ho by assumption. rewrite (H r k) by assumption. unfold delta.
    destruct (Nat.eqb_spec r k); [congruence|]. unfold Rdiv. ring.
Qed.

Lemma pt_obj : forall c t o r s, (r < m)%nat ->
  (forall x, Sol t x <-> Sol t0 x) ->
  (forall x, Sol t0 x -> sumR N (fun j => c j * x j) = lin o x - o N) ->
  forall x, Sol t0 x -> sumR N (fun j => c j * x j) = lin (po t o r s) x - po t o r s N.
Proof.
  intros c t o r s Hr HS Ho x Hx. rewrite Ho by exact Hx. unfold po.
  rewrite lin_sub_scal, lin_div.
  rewrite (proj2 (HS x) Hx r Hr). ring.
Qed.

(* -- test vectors -- *)

(* x with x_j = a j below E0 and x_{E0+i} = b i *)
Definition xa (a b : nat -> R) : nat -> R :=
  fun j => if Nat.ltb j E0 then a j else b (j - E0)%nat.

Lemma lin_xa : forall row a b,
  lin row (xa a b) = sumR E0 (fun j => row j * a j) + sumR m (fun i => row (E0 + i)%nat * b i).
Proof.
  intros row a b. unfold lin. rewrite sumR_split. f_equal.
  - apply sumR_ext. intros j Hj. unfold xa. destruct (Nat.ltb_spec j E0); [reflexivity | lia].
  - apply sumR_ext. intros i Hi. unfold xa. destruct (Nat.ltb_spec (E0 + i) E0); [lia|].
    replace (E0 + i - E0)%nat with i by lia. reflexivity.
Qed.

Lemma sum_delta_l : forall k g, (k < m)%nat ->
  sumR m (fun i => delta k i * g i) = g k.
Proof.
  intros k g Hk.
  rewrite (sumR_ext _ _ (fun i => if Nat.eqb i k then g i else 0)).
  - rewrite sumR_delta. destruct (Nat.ltb_spec k m); [reflexivity | lia].
  - intros i Hi. unfold delta. rewrite Nat.eqb_sym. destruct (Nat.eqb i k); ring.
Qed.

Lemma sum_unit : forall row g k, (k < m)%nat ->
  (forall i, (i < m)%nat -> row (E0 + i)%nat = delta k i) ->
  sumR m (fun i => row (E0 + i)%nat * g i) = g k.
Proof.
  intros row g k Hk H. rewrite <- (sum_delta_l k g Hk). apply sumR_ext.
  intros i Hi. rewrite H by exact Hi. reflexivity.
Qed.

Lemma nonzero_row : forall t bs k, unit0 ->
  (forall x, Sol t0 x -> Sol t x) -> (k < m)%nat -> (bs k < N)%nat -> t k (bs k) = 1 ->
  ~ lexz (S m) (rowvec t k).
Proof.
  intros t bs k U Inc Hk Hb H1 Z.
  assert (ZN : t k N = 0) by (apply (Z O); lia).
  assert (ZI : forall i, (i < m)%nat -> t k (E0 + i)%nat = 0).
  { intros i Hi. apply (Z (S i)). lia. }
  set (x0 := xa (fun _ => 0) (fun i => t0 i N)).
  assert (S0 : Sol t0 x0).
  { intros k' Hk'. unfold x0. rewrite lin_xa.
    rewrite sumR_zero by (intros; ring).
    rewrite (sum_unit (t0 k') (fun i => t0 i N) k' Hk') by (intros; apply U; auto). ring. }
  assert (ZE : forall j, (j < E0)%nat -> t k j = 0).
  { intros j Hj.
    set (xj := xa (fun j' => if Nat.eqb j' j then 1 else 0) (fun i => t0 i N - t0 i j)).
    assert (Sj : Sol t0 xj).
    { intros k' Hk'. unfold xj. rewrite lin_xa.
      rewrite (sum_unit (t0 k') (fun i => t0 i N - t0 i j) k' Hk') by (intros; apply U; auto).
      rewrite (sumR_ext _ _ (fun j' => if Nat.eqb j' j then t0 k' j' else 0))
        by (intros j' _; destruct (Nat.eqb j' j); ring).
      rewrite sumR_delta. destruct (Nat.ltb_spec j E0); [ring | lia]. }
    pose proof (Inc xj Sj k Hk) as Ej. unfold xj in Ej. rewrite lin_xa in Ej.
    rewrite ZN in Ej.
    rewrite (sumR_ext _ _ (fun j' => if Nat.eqb j' j then t k j' else 0)) in Ej
      by (intros j' _; destruct (Nat.eqb j' j); ring).
    rewrite sumR_delta in Ej. destruct (Nat.ltb_spec j E0); [|lia].
    rewrite sumR_zero in Ej by (intros i Hi; rewrite ZI by exact Hi; ring). lra. }
  destruct (Nat.ltb_spec (bs k) E0).
  - rewrite ZE in H1 by assumption. lra.
  - replace (bs k) with (E0 + (bs k - E0))%nat in H1 by lia.
    rewrite ZI in H1 by lia. lra.
Qed.

(* the vector with x_s = lam, x_{bs k} = t k N - lam * t k s, 0 elsewhere *)
Definition tv (t : nat -> nat -> R) (bs : nat -> nat) (lam : R) (s : nat) : nat -> R :=
  fun j => (if Nat.eqb j s then lam else 0) +
           sumR m (fun k => if Nat.eqb j (bs k) then t k N - lam * t k s else 0).

Lemma lin_tv : forall row t bs lam s, (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  lin row (tv t bs lam s) =
  (if Nat.ltb s N then row s * lam else 0) +
  sumR m (fun k => row (bs k) * (t k N - lam * t k s)).
Proof.
  intros row t bs lam s Hb. unfold lin, tv.
  rewrite (sumR_ext _ _ (fun j => (if Nat.eqb j s then row j * lam else 0) +
     sumR m (fun k => if Nat.eqb j (bs k) then row j * (t k N - lam * t k s) else 0))).
  - rewrite sumR_plus, sumR_delta, sumR_swap. f_equal.
    apply sumR_ext. intros k Hk. rewrite sumR_delta.
    destruct (Nat.ltb_spec (bs k) N); [reflexivity|]. specialize (Hb k Hk). lia.
  - intros j Hj. rewrite Rmult_plus_distr_l. f_equal.
    + destruct (Nat.eqb j s); ring.
    + rewrite <- sumR_scal. apply sumR_ext. intros k Hk. destruct (Nat.eqb j (bs k)); ring.
Qed.

Lemma tv_sol : forall t bs lam s,
  (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  (forall k k', (k < m)%nat -> (k' < m)%nat -> t k (bs k') = delta k k') ->
  ((s < N)%nat \/ lam = 0) -> Sol t (tv t bs lam s).
Proof.
  intros t bs lam s Hb Hc Hs k Hk. rewrite lin_tv by exact Hb.
  rewrite (sumR_ext _ _ (fun k' => delta k k' * (t k' N - lam * t k' s)))
    by (intros k' Hk'; rewrite Hc by assumption; reflexivity).
  rewrite sum_delta_l by exact Hk.
  destruct (Nat.ltb_spec s N).
  - ring.
  - destruct Hs as [Hs|Hs]; [lia|]. subst. ring.
Qed.

Lemma lin_tv_o : forall o t bs lam s,
  (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  (forall k, (k < m)%nat -> o (bs k) = 0) -> (s < N)%nat ->
  lin o (tv t bs lam s) = o s * lam.
Proof.
  intros o t bs lam s Hb Ho Hs. rewrite lin_tv by exact Hb.
  rewrite sumR_zero by (intros k Hk; rewrite Ho by exact Hk; ring).
  destruct (Nat.ltb_spec s N); [ring | lia].
Qed.

Lemma lin_tv0 : forall o t bs s,
  (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  (forall k, (k < m)%nat -> o (bs k) = 0) ->
  lin o (tv t bs 0 s) = 0.
Proof.
  intros o t bs s Hb Ho. rewrite lin_tv by exact Hb.
  rewrite sumR_zero by (intros k Hk; rewrite Ho by exact Hk; ring).
  destruct (Nat.ltb s N); ring.
Qed.

(* -- the reduced costs are determined by the basis -- *)

Lemma determination : forall c t1 o1 bs1 t2 o2 bs2,
  Valid c t1 o1 bs1 -> Valid c t2 o2 bs2 -> (forall k, (k < m)%nat -> bs1 k = bs2 k) ->
  forall p, (p < S m)%nat -> Wv o1 p = Wv o2 p.
Proof.
  intros c t1 o1 bs1 t2 o2 bs2 V1 V2 Eb.
  assert (Ho2 : forall k, (k < m)%nat -> o2 (bs1 k) = 0).
  { intros k Hk. rewrite Eb by exact Hk. apply (v_ocanon _ _ _ _ V2); exact Hk. }
  assert (Hb2 : forall k, (k < m)%nat -> (bs1 k < N)%nat) by apply (v_bs _ _ _ _ V1).
  assert (EN : o1 N = o2 N).
  { set (x := tv t1 bs1 0 O).
    assert (Sx : Sol t0 x).
    { apply (v_sol _ _ _ _ V1). apply tv_sol; [exact Hb2 | apply (v_canon _ _ _ _ V1) | right; reflexivity]. }
    pose proof (v_obj _ _ _ _ V1 x Sx) as A. pose proof (v_obj _ _ _ _ V2 x Sx) as B.
    unfold x in A, B.
    rewrite lin_tv0 in A by first [exact Hb2 | apply (v_ocanon _ _ _ _ V1)].
    rewrite lin_tv0 in B by first [exact Hb2 | exact Ho2]. lra. }
  intros p Hp. unfold Wv, lcol. destruct p as [|p]; [exact EN|].
  set (j := (E0 + p)%nat). assert (Hj : (j < N)%nat) by (unfold j; lia).
  set (x := tv t1 bs1 1 j).
  assert (Sx : Sol t0 x).
  { apply (v_sol _ _ _ _ V1). apply tv_sol; [exact Hb2 | apply (v_canon _ _ _ _ V1) | left; exact Hj]. }
  pose proof (v_obj _ _ _ _ V1 x Sx) as A. pose proof (v_obj _ _ _ _ V2 x Sx) as B.
  unfold x in A, B.
  rewrite lin_tv_o in A by first [exact Hb2 | apply (v_ocanon _ _ _ _ V1) | exact Hj].
  rewrite lin_tv_o in B by first [exact Hb2 | exact Ho2 | exact Hj]. lra.
Qed.

(* -- the pivot keeps the invariant and raises the reduced-cost vector -- *)

Lemma pivot_valid : forall c t o bs r s, unit0 -> Valid c t o bs ->
  (s < N)%nat -> o s < 0 -> LeaveOK t r s ->
  Valid c (pt t r s) (po t o r s) (pb bs r s).
Proof.
  intros c t o bs r s U V Hs Hos (Hr & Hp & Hmin).
  assert (Hp0 : t r s <> 0) by lra.
  assert (HS : forall x, Sol (pt t r s) x <-> Sol t0 x).
  { intros x. rewrite <- (pt_sol t r s Hr Hp0 x). apply (v_sol _ _ _ _ V). }
  assert (HB : forall k, (k < m)%nat -> (pb bs r s k < N)%nat).
  { intros k Hk. unfold pb. destruct (Nat.eqb k r); [exact Hs | apply (v_bs _ _ _ _ V); exact Hk]. }
  assert (HC := pt_canon t bs r s Hr Hp0 (v_canon _ _ _ _ V)).
  constructor.
  - exact HS.
  - exact HB.
  - exact HC.
  - apply pt_ocanon; auto; [apply (v_canon _ _ _ _ V) | apply (v_ocanon _ _ _ _ V)].
  - apply pt_obj; auto; [apply (v_sol _ _ _ _ V) | apply (v_obj _ _ _ _ V)].
  - intros k Hk. destruct (Nat.eqb_spec k r).
    + subst. eapply lexgt0_ext; [| apply (lexgt0_scale _ (/ t r s) _ (Rinv_0_lt_compat _ Hp) (v_lex _ _ _ _ V r Hr))].
      intros q Hq. unfold rowvec, pt. rewrite Nat.eqb_refl. unfold Rdiv. ring.
    + assert (Hrow : forall q, rowvec (pt t r s) k q = rowvec t k q - t k s * (rowvec t r q / t r s)).
      { intros q. unfold rowvec, pt. rewrite (proj2 (Nat.eqb_neq k r) n). reflexivity. }
      destruct (Rlt_le_dec 0 (t k s)) as [Pk | Pk].
      * pose proof (not_lexlt _ _ _ (Hmin k Hk Pk)) as G.
        apply (lexge0_scale _ (t k s) _ Pk) in G.
        destruct G as [G|G].
        -- eapply lexgt0_ext; [|exact G]. intros q Hq. rewrite Hrow. field. split; lra.
        -- exfalso. apply (nonzero_row (pt t r s) (pb bs r s) k U).
           ++ intros x Hx. apply HS; exact Hx.
           ++ exact Hk.
           ++ apply HB; exact Hk.
           ++ rewrite HC by assumption. unfold delta. rewrite Nat.eqb_refl. reflexivity.
           ++ intros q Hq. rewrite Hrow. specialize (G q Hq). cbv beta in G.
              replace (rowvec t k q - t k s * (rowvec t r q / t r s))
                with (t k s * (rowvec t k q / t k s - rowvec t r q / t r s)) by (field; split; lra).
              exact G.
      * destruct (Req_dec (t k s) 0) as [Z|Z].
        -- eapply lexgt0_ext; [|exact (v_lex _ _ _ _ V k Hk)]. intros q Hq. rewrite Hrow, Z. ring.
        -- assert (Nk : 0 < - t k s / t r s) by (apply Rdiv_lt_0_compat; lra).
           eapply lexgt0_ext;
             [| exact (lexgt0_add _ _ _ (v_lex _ _ _ _ V k Hk)
                    (or_introl (lexgt0_scale _ _ _ Nk (v_lex _ _ _ _ V r Hr))))].
           intros q Hq. rewrite Hrow. field. lra.
Qed.

Lemma pivot_lex : forall c t o bs r s, Valid c t o bs -> o s < 0 -> LeaveOK t r s ->
  lexlt (S m) (Wv o) (Wv (po t o r s)).
Proof.
  intros c t o bs r s V Hos (Hr & Hp & _).
  assert (Nk : 0 < - o s / t r s) by (apply Rdiv_lt_0_compat; lra).
  unfold lexlt. eapply lexgt0_ext; [| exact (lexgt0_scale _ _ _ Nk (v_lex _ _ _ _ V r Hr))].
  intros q Hq. unfold Wv, po, rowvec. field. lra.
Qed.

(* -- reading the answer off a final tableau -- *)

Definition xb (t : nat -> nat -> R) (bs : nat -> nat) : nat -> R := tv t bs 0 O.

Lemma valid_rhs : forall c t o bs, Valid c t o bs -> forall k, (k < m)%nat -> 0 <= t k N.
Proof.
  intros c t o bs V k Hk. apply (lex_first_nonneg (S m) (rowvec t k)); [lia|].
  apply (v_lex _ _ _ _ V); exact Hk.
Qed.

Lemma xb_sol : forall c t o bs, Valid c t o bs -> Sol t0 (xb t bs).
Proof.
  intros c t o bs V. apply (v_sol _ _ _ _ V). apply tv_sol;
    [apply (v_bs _ _ _ _ V) | apply (v_canon _ _ _ _ V) | right; reflexivity].
Qed.

Lemma xb_nonneg : forall c t o bs, Valid c t o bs -> forall j, 0 <= xb t bs j.
Proof.
  intros c t o bs V j. unfold xb, tv.
  assert (0 <= sumR m (fun k => if Nat.eqb j (bs k) then t k N - 0 * t k O else 0)).
  { apply sumR_nonneg. intros k Hk. destruct (Nat.eqb j (bs k)); [|lra].
    pose proof (valid_rhs c t o bs V k Hk). lra. }
  destruct (Nat.eqb j O); lra.
Qed.

Lemma xb_obj : forall c t o bs, Valid c t o bs ->
  sumR N (fun j => c j * xb t bs j) = - o N.
Proof.
  intros c t o bs V. rewrite (v_obj _ _ _ _ V) by (eapply xb_sol; eauto).
  unfold xb. rewrite lin_tv0 by first [apply (v_bs _ _ _ _ V) | apply (v_ocanon _ _ _ _ V)]. ring.
Qed.

Lemma lin_xb : forall row t bs, (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  lin row (xb t bs) = sumR m (fun k => row (bs k) * t k N).
Proof.
  intros row t bs Hb. unfold xb. rewrite lin_tv by exact Hb.
  rewrite (sumR_ext _ _ (fun k => row (bs k) * t k N)) by (intros; ring).
  destruct (Nat.ltb O N); ring.
Qed.

Lemma opt_lb : forall c t o bs (allowed : nat -> bool), Valid c t o bs ->
  (forall j, (j < N)%nat -> allowed j = true -> 0 <= o j) ->
  forall x, Sol t0 x -> (forall j, (j < N)%nat -> 0 <= x j) ->
  (forall j, (j < N)%nat -> allowed j = false -> x j = 0) ->
  - o N <= sumR N (fun j => c j * x j).
Proof.
  intros c t o bs al V Hal x Sx Hx Hz. rewrite (v_obj _ _ _ _ V) by exact Sx.
  assert (0 <= lin o x).
  { apply sumR_nonneg. intros j Hj. destruct (al j) eqn:E.
    - apply Rmult_le_pos; auto.
    - rewrite Hz by assumption. lra. }
  lra.
Qed.

Definition Bounded (M : R) : Prop :=
  forall x, Sol t0 x -> (forall j, (j < N)%nat -> 0 <= x j) -> forall j, (j < N)%nat -> x j <= M.

Lemma no_ray : forall c t o bs M s, Bounded M -> Valid c t o bs ->
  (s < N)%nat -> o s < 0 -> (forall k, (k < m)%nat -> t k s <= 0) -> False.
Proof.
  intros c t o bs M s HM V Hs Hos Hneg.
  assert (Nb : forall k, (k < m)%nat -> bs k <> s).
  { intros k Hk E. rewrite <- E in Hos. rewrite (v_ocanon _ _ _ _ V) in Hos by exact Hk. lra. }
  set (lam := Rmax 0 M + 1).
  assert (Hl : 0 <= lam) by (unfold lam; pose proof (Rmax_l 0 M); lra).
  set (x := tv t bs lam s).
  assert (Sx : Sol t0 x).
  { apply (v_sol _ _ _ _ V). apply tv_sol; [apply (v_bs _ _ _ _ V) | apply (v_canon _ _ _ _ V) | left; exact Hs]. }
  assert (Px : forall j, (j < N)%nat -> 0 <= x j).
  { intros j Hj. unfold x, tv.
    assert (0 <= sumR m (fun k => if Nat.eqb j (bs k) then t k N - lam * t k s else 0)).
    { apply sumR_nonneg. intros k Hk. destruct (Nat.eqb j (bs k)); [|lra].
      pose proof (valid_rhs c t o bs V k Hk). pose proof (Hneg k Hk).
      assert (0 <= lam * - t k s) by (apply Rmult_le_pos; lra). lra. }
    destruct (Nat.eqb j s); lra. }
  pose proof (HM x Sx Px s Hs) as B.
  assert (Exs : x s = lam).
  { unfold x, tv. rewrite Nat.eqb_refl.
    rewrite sumR_zero; [ring|]. intros k Hk.
    destruct (Nat.eqb_spec s (bs k)); [|reflexivity]. exfalso. apply (Nb k Hk). auto. }
  rewrite Exs in B. unfold lam in B. pose proof (Rmax_r 0 M). lra.
Qed.

(* -- phase 1 and phase 2 -- *)

(* -- a fresh objective row for a cost vector c -- *)

Lemma delta_sym : forall k k', delta k k' = delta k' k.
Proof. intros k k'. unfold delta. rewrite Nat.eqb_sym. reflexivity. Qed.

Lemma canon_valid : forall c t o bs,
  (forall x, Sol t x <-> Sol t0 x) ->
  (forall k, (k < m)%nat -> (bs k < N)%nat) ->
  (forall k k', (k < m)%nat -> (k' < m)%nat -> t k (bs k') = delta k k') ->
  (forall k, (k < m)%nat -> lexgt0 (S m) (rowvec t k)) ->
  (forall j, (j <= N)%nat -> o j = c j - sumR m (fun k => c (bs k) * t k j)) ->
  c N = 0 ->
  Valid c t o bs.
Proof.
  intros c t o bs HS Hb Hc Hl Ho HcN. constructor; auto.
  - intros k' Hk'. rewrite Ho by (pose proof (Hb k' Hk'); lia).
    rewrite (sumR_ext _ _ (fun k => delta k' k * c (bs k))).
    + rewrite sum_delta_l by exact Hk'. ring.
    + intros k Hk. rewrite Hc by assumption. rewrite delta_sym. ring.
  - intros x Hx. pose proof (proj2 (HS x) Hx) as Sx.
    rewrite Ho by lia. rewrite HcN.
    unfold lin.
    rewrite (sumR_ext _ (fun j => o j * x j)
               (fun j => c j * x j - sumR m (fun k => c (bs k) * (t k j * x j)))).
    + rewrite sumR_minus, sumR_swap.
      rewrite (sumR_ext _ (fun k => sumR N (fun j => c (bs k) * (t k j * x j)))
                 (fun k => c (bs k) * t k N)).
      * ring.
      * intros k Hk. rewrite sumR_scal. f_equal. apply Sx. exact Hk.
    + intros j Hj. rewrite Ho by lia. rewrite Rmult_minus_distr_r. f_equal.
      rewrite Rmult_comm, <- sumR_scal. apply sumR_ext. intros k Hk. ring.
Qed.

Lemma unit0_rowlex : forall k, unit0 -> (k < m)%nat -> 0 <= t0 k N -> lexgt0 (S m) (rowvec t0 k).
Proof.
  intros k U Hk Hn. destruct (Rle_lt_or_eq_dec _ _ Hn) as [P|Z].
  - exists O. split; [lia|]. split; [intros; lia|]. exact P.
  - exists (S k). split; [lia|]. split.
    + intros q Hq. destruct q; unfold rowvec, lcol.
      * symmetry; exact Z.
      * rewrite U by lia. unfold delta. destruct (Nat.eqb_spec k q); [lia | reflexivity].
    + unfold rowvec, lcol. rewrite U by lia. unfold delta. rewrite Nat.eqb_refl. lra.
Qed.

Lemma lcol_le : forall p, (p < S m)%nat -> (lcol p <= N)%nat.
Proof using m E0.
  intros p Hp. destruct p; simpl; [apply le_n|].
  apply Nat.add_le_mono_l. apply Nat.lt_le_incl. apply (proj2 (Nat.succ_lt_mono p m)). exact Hp.
Qed.

Lemma Valid_ext : forall c t o bs t' o' bs', Valid c t o bs ->
  (forall k j, (k < m)%nat -> (j <= N)%nat -> t' k j = t k j) ->
  (forall j, (j <= N)%nat -> o' j = o j) ->
  (forall k, (k < m)%nat -> bs' k = bs k) ->
  Valid c t' o' bs'.
Proof.
  intros c t o bs t' o' bs' V Et Eo Eb.
  assert (ES : forall x, Sol t' x <-> Sol t x).
  { intros x. unfold Sol. split; intros H k Hk.
    - rewrite <- Et by lia. rewrite <- (H k Hk). apply lin_ext. intros j Hj. rewrite Et by lia. reflexivity.
    - rewrite Et by lia. rewrite <- (H k Hk). apply lin_ext. intros j Hj. rewrite Et by lia. reflexivity. }
  constructor.
  - intros x. rewrite ES. apply (v_sol _ _ _ _ V).
  - intros k Hk. rewrite Eb by exact Hk. apply (v_bs _ _ _ _ V); exact Hk.
  - intros k k' Hk Hk'. rewrite Eb, Et by (try exact Hk'; try exact Hk; pose proof (v_bs _ _ _ _ V k' Hk'); lia).
    apply (v_canon _ _ _ _ V); assumption.
  - intros k Hk. rewrite Eb, Eo by (try exact Hk; pose proof (v_bs _ _ _ _ V k Hk); lia).
    apply (v_ocanon _ _ _ _ V); exact Hk.
  - intros x Hx. rewrite (v_obj _ _ _ _ V x Hx). rewrite Eo by lia. f_equal.
    apply lin_ext. intros j Hj. rewrite Eo by lia. reflexivity.
  - intros k Hk. eapply lexgt0_ext; [|exact (v_lex _ _ _ _ V k Hk)].
    intros p Hp. unfold rowvec. rewrite Et by (try exact Hk; apply lcol_le; exact Hp). reflexivity.
Qed.

Variable A0 : nat.   (* columns A0 .. N-1 are the artificial ones *)
Definition c1 (j : nat) : R := if Nat.leb A0 j then 1 else 0.
Definition Feas (x : nat -> R) : Prop :=
  Sol t0 x /\ (forall j, (j < N)%nat -> 0 <= x j) /\
  (forall j, (A0 <= j)%nat -> (j < N)%nat -> x j = 0).

Lemma c1_zero : forall x, Feas x -> sumR N (fun j => c1 j * x j) = 0.
Proof.
  intros x (_ & _ & Hz). apply sumR_zero. intros j Hj. unfold c1.
  destruct (Nat.leb_spec A0 j); [rewrite Hz by assumption|]; ring.
Qed.

Lemma phase1_zero : forall t d bs, Valid c1 t d bs ->
  (forall j, (j < N)%nat -> 0 <= d j) -> forall x0, Feas x0 -> d N = 0.
Proof.
  intros t d bs V Hd x0 F0.
  pose proof (xb_obj c1 t d bs V) as A.
  assert (0 <= sumR N (fun j => c1 j * xb t bs j)).
  { apply sumR_nonneg. intros j Hj. apply Rmult_le_pos; [unfold c1; destruct (Nat.leb A0 j); lra|].
    eapply xb_nonneg; eauto. }
  pose proof (c1_zero x0 F0) as B. destruct F0 as (S0 & P0 & _).
  rewrite (v_obj _ _ _ _ V) in B by exact S0.
  assert (0 <= lin d x0) by (apply sumR_nonneg; intros j Hj; apply Rmult_le_pos; auto).
  lra.
Qed.

Lemma phase2_opt : forall t1 d bs1 c t o bs (allowed : nat -> bool),
  Valid c1 t1 d bs1 -> d N = 0 -> (forall j, (j < N)%nat -> 0 <= d j) ->
  Valid c t o bs -> (forall k, (k < m)%nat -> d (bs k) = 0) ->
  (forall j, (j < N)%nat -> allowed j = false -> (A0 <= j)%nat \/ 0 < d j) ->
  (forall j, (j < N)%nat -> allowed j = true -> 0 <= o j) ->
  Feas (xb t bs) /\ sumR N (fun j => c j * xb t bs j) = - o N /\
  forall x, Feas x -> - o N <= sumR N (fun j => c j * x j).
Proof.
  intros t1 d bs1 c t o bs al V1 DN Dpos V Dbs Hal Hopt.
  assert (Fb : Feas (xb t bs)).
  { split; [eapply xb_sol; eauto|]. split; [intros; eapply xb_nonneg; eauto|].
    assert (E : sumR N (fun j => c1 j * xb t bs j) = 0).
    { rewrite (v_obj _ _ _ _ V1) by (eapply xb_sol; eauto).
      rewrite lin_xb by apply (v_bs _ _ _ _ V). rewrite DN.
      rewrite sumR_zero; [ring|]. intros k Hk. rewrite Dbs by exact Hk. ring. }
    intros j Hj HjN.
    pose proof (sumR_nonneg_zero N (fun j => c1 j * xb t bs j)) as Z.
    assert (Z' : c1 j * xb t bs j = 0).
    { apply Z; [| exact E | exact HjN]. intros j' _. apply Rmult_le_pos;
        [unfold c1; destruct (Nat.leb A0 j'); lra | eapply xb_nonneg; eauto]. }
    unfold c1 in Z'. destruct (Nat.leb_spec A0 j); [lra | lia]. }
  split; [exact Fb|]. split; [eapply xb_obj; eauto|].
  intros x Fx. apply (opt_lb c t o bs al V Hopt x (proj1 Fx) (proj1 (proj2 Fx))).
  intros j Hj Ha. destruct (Hal j Hj Ha) as [Ha'|Hd].
  - apply (proj2 (proj2 Fx)); assumption.
  - pose proof (c1_zero x Fx) as E. destruct Fx as (Sx & Px & _).
    rewrite (v_obj _ _ _ _ V1) in E by exact Sx. rewrite DN in E.
    assert (E' : lin d x = 0) by lra.
    pose proof (sumR_nonneg_zero N (fun j => d j * x j)
                  ltac:(intros j' Hj'; apply Rmult_le_pos; auto) E' j Hj) as Z.
    cbv beta in Z. pose proof (Px j Hj).
    destruct (Rmult_integral _ _ Z); lra.
Qed.

End Simplex.
End P_SM.

(* ================================================================== *)
Section P_SP.
Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* The simplex program                                                 *)
(* ------------------------------------------------------------------ *)

Definition SState : Type := (array Q * array Q * array int)%type.
Definition sT (st : SState) : array Q := fst (fst st).
Definition sO (st : SState) : array Q := snd (fst st).
Definition sB (st : SState) : array int := snd st.

(* column of component p of the lexicographic vector of a row:
   p = 0 is the right-hand side (column N), p = i + 1 is column E0 + i *)
Definition lc (N E0 p : int) : int := if p =? 0 then N else E0 + p - 1.

(* the first allowed column of negative reduced cost *)
Definition enter (N : int) (al : array bool) (O : array Q) : option int :=
  loop N (fun _ st => match st with None => true | Some _ => false end)
    (fun j _ => if al.[j] && qltb O.[j] 0 then Some j else None) 0 None.

(* row k before row r in the lexicographic ratio test on column s *)
Definition lexless (T : array Q) (w N E0 m k r s : int) : bool :=
  let tks := T.[k * w + s] in
  let trs := T.[r * w + s] in
  let st := loop (m + 1) (fun _ st => st =? 0)
     (fun p _ => let c := lc N E0 p in
        let a := Qmult T.[k * w + c] trs in
        let b := Qmult T.[r * w + c] tks in
        if qltb a b then 1 else if qltb b a then 2 else 0) 0 0 in
  st =? 1.

(* the leaving row: lexicographic minimum ratio among positive entries *)
Definition leave (T : array Q) (w N E0 m s : int) : option int :=
  forl 0 m (fun k best =>
    if qltb 0 T.[k * w + s] then
      match best with
      | None => Some k
      | Some r => if lexless T w N E0 m k r s then Some k else Some r
      end
    else best) None.

Definition scale_row (T : array Q) (w r : int) (inv : Q) : array Q :=
  forl 0 w (fun j T => T.[r * w + j <- qmul T.[r * w + j] inv]) T.

Definition elim_row (T : array Q) (w r k : int) (f : Q) : array Q :=
  forl 0 w (fun j T => let a := T.[r * w + j] in
      if qzerob a then T else T.[k * w + j <- qsub T.[k * w + j] (Qmult f a)]) T.

Definition elim_all (T : array Q) (w m r s : int) : array Q :=
  forl 0 m (fun k T => if k =? r then T else
      let f := T.[k * w + s] in if qzerob f then T else elim_row T w r k f) T.

Definition elim_obj (O : array Q) (T : array Q) (w r : int) (f : Q) : array Q :=
  forl 0 w (fun j O => let a := T.[r * w + j] in
      if qzerob a then O else O.[j <- qsub O.[j] (Qmult f a)]) O.

Definition pivot (w m : int) (st : SState) (r s : int) : SState :=
  let T := sT st in let O := sO st in let B := sB st in
  let T1 := scale_row T w r (Qinv T.[r * w + s]) in
  let T2 := elim_all T1 w m r s in
  let O2 := elim_obj O T2 w r O.[s] in
  (T2, O2, B.[r <- s]).

Definition SRel (m E0 : int) (al : array bool) (st' st : SState) : Prop :=
  exists s r, enter (E0 + m) al (sO st) = Some s /\
    leave (sT st) (E0 + m + 1) (E0 + m) E0 m s = Some r /\
    st' = pivot (E0 + m + 1) m st r s.

Fixpoint sloop (m E0 : int) (al : array bool) (st : SState)
    (H : Acc (SRel m E0 al) st) {struct H} : SState :=
  match odec (enter (E0 + m) al (sO st)) with
  | inleft (exist _ s Hs) =>
      match odec (leave (sT st) (E0 + m + 1) (E0 + m) E0 m s) with
      | inleft (exist _ r Hr) =>
          sloop m E0 al (pivot (E0 + m + 1) m st r s)
            (Acc_inv H (ex_intro _ s (ex_intro _ r (conj Hs (conj Hr eq_refl)))))
      | inright _ => st
      end
  | inright _ => st
  end.

(* the objective row of cost vector c (length w, c.[N] = 0) for basis B:
   O_j = c_j - sum_k c_{B k} T_kj *)
Definition canon_obj (T : array Q) (B : array int) (c : array Q) (w m : int) : array Q :=
  forl 0 m (fun k O => let f := c.[B.[k]] in
     if qzerob f then O else elim_obj O T w k f) (PArray.copy c).

(* ------------------------------------------------------------------ *)
(* Reading the arrays                                                  *)
(* ------------------------------------------------------------------ *)

Definition cellZ (T : array Q) (w : int) (k j : Z) : R := Q2R T.[of_Z (k * to_Z w + j)].
Definition cell (T : array Q) (w : int) (k j : nat) : R := cellZ T w (Z.of_nat k) (Z.of_nat j).
Definition ovec (O : array Q) (j : nat) : R := Q2R O.[of_Z (Z.of_nat j)].
Definition bvec (B : array int) (k : nat) : nat := Z.to_nat (to_Z B.[of_Z (Z.of_nat k)]).

Lemma idx_inj : forall W k1 j1 k2 j2 : Z, (0 <= j1 < W)%Z -> (0 <= j2 < W)%Z ->
  (k1 * W + j1 = k2 * W + j2)%Z -> k1 = k2 /\ j1 = j2.
Proof. intros W k1 j1 k2 j2 H1 H2 E. assert (k1 = k2) by nia. subst. lia. Qed.

Lemma cellZ_get : forall T w (k c : int), (to_Z k * to_Z w + to_Z c < wB)%Z ->
  Q2R T.[k * w + c] = cellZ T w (to_Z k) (to_Z c).
Proof.
  intros T w k c H. unfold cellZ. f_equal. f_equal. apply to_Z_inj.
  pose proof (to_Z_bounded k). pose proof (to_Z_bounded w). pose proof (to_Z_bounded c).
  rewrite to_Z_of_Z_small by nia. rewrite add_spec, mul_spec.
  rewrite (Z.mod_small (to_Z k * to_Z w)) by nia. apply Z.mod_small. nia.
Qed.

Lemma cellZ_set : forall T w (k0 j0 : int) v (k j : Z),
  (0 <= j < to_Z w)%Z -> (to_Z j0 < to_Z w)%Z -> (0 <= k)%Z ->
  (k * to_Z w + j < to_Z (PArray.length T))%Z ->
  (to_Z k0 * to_Z w + to_Z j0 < to_Z (PArray.length T))%Z ->
  cellZ (T.[k0 * w + j0 <- v]) w k j =
  if (Z.eqb k (to_Z k0) && Z.eqb j (to_Z j0))%bool then Q2R v else cellZ T w k j.
Proof.
  intros T w k0 j0 v k j Hj Hj0 Hk Hi Hi0. unfold cellZ.
  pose proof (lboundQ T). pose proof (to_Z_bounded k0). pose proof (to_Z_bounded w).
  pose proof (to_Z_bounded j0).
  assert (Ei0 : to_Z (k0 * w + j0) = (to_Z k0 * to_Z w + to_Z j0)%Z).
  { rewrite add_spec, mul_spec. rewrite (Z.mod_small (to_Z k0 * to_Z w)) by nia.
    apply Z.mod_small. nia. }
  destruct (Z.eqb_spec k (to_Z k0)); destruct (Z.eqb_spec j (to_Z j0)); simpl.
  - subst. replace (of_Z (to_Z k0 * to_Z w + to_Z j0)) with (k0 * w + j0).
    + rewrite gssQ; [reflexivity|]. rewrite Ei0. lia.
    + apply to_Z_inj. rewrite Ei0, to_Z_of_Z_small by lia. reflexivity.
  - rewrite gsoZQ; [reflexivity|]. rewrite Ei0, to_Z_of_Z_small by nia.
    intros E. apply idx_inj in E; lia.
  - rewrite gsoZQ; [reflexivity|]. rewrite Ei0, to_Z_of_Z_small by nia.
    intros E. apply idx_inj in E; lia.
  - rewrite gsoZQ; [reflexivity|]. rewrite Ei0, to_Z_of_Z_small by nia.
    intros E. apply idx_inj in E; lia.
Qed.

Lemma ovec_get : forall O (j : int), Q2R O.[j] = ovec O (Z.to_nat (to_Z j)).
Proof.
  intros O j. unfold ovec. rewrite Z2Nat.id by (pose proof (to_Z_bounded j); lia).
  rewrite of_Z_to_Z. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* enter                                                               *)
(* ------------------------------------------------------------------ *)

Definition enter_inv (al : array bool) (O : array Q) (N : int) (j : int) (st : option int) : Prop :=
  match st with
  | None => forall j', (to_Z j' < to_Z j)%Z -> al.[j'] = true -> (0 <= Q2R O.[j'])%R
  | Some s => (to_Z s < to_Z N)%Z /\ al.[s] = true /\ (Q2R O.[s] < 0)%R
  end.

Lemma enter_all : forall N al O, enter_inv al O N N (enter N al O).
Proof.
  intros N al O. unfold enter.
  destruct (loop_inv (enter_inv al O N) N 0
     (fun _ st => match st with None => true | Some _ => false end)
     (fun j _ => if al.[j] && qltb O.[j] 0 then Some j else None) None) as (j & Hj & P & E).
  - pose proof (to_Z_bounded N). change (to_Z 0) with 0%Z. lia.
  - intros j' Hj'. pose proof (to_Z_bounded j'). change (to_Z 0) with 0%Z in Hj'. lia.
  - intros j t Hj Pt Ct. destruct t as [s|]; [discriminate|].
    destruct (al.[j] && qltb O.[j] 0) eqn:Ea.
    + simpl. apply andb_true_iff in Ea. destruct Ea as [A1 A2].
      apply qltb_R in A2. rewrite Q2R_0 in A2. split; [lia|]. auto.
    + simpl. intros j' Hj' Al. pose proof (to_Z_bounded N).
      assert (to_Z (j + 1) = to_Z j + 1)%Z by sia.
      destruct (Z.eq_dec (to_Z j') (to_Z j)) as [Ej|Ej].
      * apply to_Z_inj in Ej. subst j'. rewrite Al in Ea. simpl in Ea.
        apply qltb_R_false in Ea. rewrite Q2R_0 in Ea. exact Ea.
      * apply Pt; [lia | exact Al].
  - destruct (loop N _ _ 0 None) as [s|] eqn:L.
    + exact P.
    + destruct E as [E|[_ E]]; [|discriminate].
      simpl in P |- *. intros j' Hj' Al. apply P; [lia | exact Al].
Qed.

(* ------------------------------------------------------------------ *)
(* lexless                                                             *)
(* ------------------------------------------------------------------ *)

Lemma lex_gt_not_lt : forall n f g p, (p < n)%nat ->
  (forall q, (q < p)%nat -> f q = g q) -> (g p < f p)%R -> ~ lexlt n f g.
Proof.
  intros n f g p Hp Hpre Hgt (p' & Hp' & Hz & Hpos). cbv beta in Hz, Hpos.
  destruct (Nat.lt_trichotomy p' p) as [L|[E|L]].
  - rewrite Hpre in Hpos by exact L. lra.
  - subst. lra.
  - specialize (Hz p L). lra.
Qed.

Section Lex.
Variables (T : array Q) (w N E0 m k r s : int).
Hypothesis Hw : to_Z w = (to_Z N + 1)%Z.
Hypothesis HN : to_Z N = (to_Z E0 + to_Z m)%Z.
Hypothesis Hsz : (to_Z m * to_Z w <= 4194303)%Z.
Hypothesis Hk : (to_Z k < to_Z m)%Z.
Hypothesis Hr : (to_Z r < to_Z m)%Z.
Hypothesis Hs : (to_Z s < to_Z N)%Z.

Let mn := Z.to_nat (to_Z m).
Let en := Z.to_nat (to_Z E0).
Let tks := cellZ T w (to_Z k) (to_Z s).
Let trs := cellZ T w (to_Z r) (to_Z s).
Let fk := fun p => (rowvec mn en (cell T w) (Z.to_nat (to_Z k)) p / tks)%R.
Let fr := fun p => (rowvec mn en (cell T w) (Z.to_nat (to_Z r)) p / trs)%R.

Hypothesis Pk : (0 < tks)%R.
Hypothesis Pr : (0 < trs)%R.

Lemma lc_spec : forall p : int, (to_Z p <= to_Z m)%Z ->
  to_Z (lc N E0 p) = Z.of_nat (lcol mn en (Z.to_nat (to_Z p))).
Proof.
  intros p Hp. unfold lc, lcol. pose proof (to_Z_bounded p). pose proof (to_Z_bounded E0).
  pose proof (to_Z_bounded m). pose proof (to_Z_bounded N).
  destruct (p =? 0) eqn:E.
  - apply Uint63.eqb_spec in E. subst p. change (to_Z 0) with 0%Z. simpl.
    unfold mn, en. lia.
  - apply Uint63.eqb_false_spec in E. assert (to_Z p <> 0%Z) by (intros F; apply E, to_Z_inj; exact F).
    destruct (Z.to_nat (to_Z p)) eqn:Ep; [lia|].
    unfold en. assert (to_Z (E0 + p - 1) = to_Z E0 + to_Z p - 1)%Z by sia. lia.
Qed.

Lemma cell_lc : forall (k' : int) (p : int), (to_Z k' < to_Z m)%Z -> (to_Z p <= to_Z m)%Z ->
  Q2R T.[k' * w + lc N E0 p] = rowvec mn en (cell T w) (Z.to_nat (to_Z k')) (Z.to_nat (to_Z p)).
Proof.
  intros k' p Hk' Hp. pose proof (to_Z_bounded k'). pose proof (lc_spec p Hp) as L.
  assert (Lb : (Z.of_nat (lcol mn en (Z.to_nat (to_Z p))) < to_Z w)%Z).
  { unfold lcol, mn, en. pose proof (to_Z_bounded E0); pose proof (to_Z_bounded m).
    destruct (Z.to_nat (to_Z p)) eqn:Ep; lia. }
  rewrite cellZ_get by (rewrite L; nia).
  unfold rowvec, cell. rewrite L. rewrite Z2Nat.id by lia. reflexivity.
Qed.

Definition lexless_inv (p : Z) (st : int) : Prop :=
  (st = 0 /\ forall q, (q < Z.to_nat p)%nat -> fk q = fr q) \/
  (st = 1 /\ lexlt (S mn) fk fr) \/ (st = 2 /\ ~ lexlt (S mn) fk fr).

Lemma lexless_spec : lexless T w N E0 m k r s = true <-> lexlt (S mn) fk fr.
Proof.
  assert (Ek : Q2R T.[k * w + s] = tks).
  { unfold tks. apply cellZ_get. pose proof (to_Z_bounded k). pose proof (to_Z_bounded s). nia. }
  assert (Er : Q2R T.[r * w + s] = trs).
  { unfold trs. apply cellZ_get. pose proof (to_Z_bounded r). pose proof (to_Z_bounded s). nia. }
  unfold lexless.
  pose proof (to_Z_bounded m). pose proof (to_Z_bounded w).
  assert (Hm1 : to_Z (m + 1) = (to_Z m + 1)%Z) by sia.
  destruct (loop_inv (fun p st => lexless_inv (to_Z p) st) (m + 1) 0 (fun _ st => st =? 0)
     (fun p _ => let c := lc N E0 p in
        let a := Qmult T.[k * w + c] T.[r * w + s] in
        let b := Qmult T.[r * w + c] T.[k * w + s] in
        if qltb a b then 1 else if qltb b a then 2 else 0) 0) as (j & Hj & P & E).
  - change (to_Z 0) with 0%Z. lia.
  - left. split; [reflexivity|]. intros q Hq. change (to_Z 0) with 0%Z in Hq. simpl in Hq. lia.
  - intros p t Hp Pt Ct. apply Uint63.eqb_spec in Ct. subst t.
    destruct Pt as [[_ Pre] | [[F _] | [F _]]]; [| apply (f_equal to_Z) in F; discriminate | apply (f_equal to_Z) in F; discriminate].
    change (to_Z 0) with 0%Z in Hp.
    assert (Ep1 : to_Z (p + 1) = (to_Z p + 1)%Z) by sia.
    assert (Hpm : (to_Z p <= to_Z m)%Z) by lia.
    set (pn := Z.to_nat (to_Z p)).
    assert (Hpn : (pn < S mn)%nat) by (unfold pn, mn; lia).
    assert (Ea : Q2R (Qmult T.[k * w + lc N E0 p] T.[r * w + s]) = (fk pn * tks * trs)%R).
    { rewrite Q2R_mult, cell_lc, Er by lia. unfold fk, pn. field. lra. }
    assert (Eb : Q2R (Qmult T.[r * w + lc N E0 p] T.[k * w + s]) = (fr pn * tks * trs)%R).
    { rewrite Q2R_mult, cell_lc, Ek by lia. unfold fr, pn. field. lra. }
    assert (Ptt : (0 < tks * trs)%R) by (apply Rmult_lt_0_compat; lra).
    cbv zeta.
    set (qa := Qmult T.[k * w + lc N E0 p] T.[r * w + s]) in *.
    set (qb := Qmult T.[r * w + lc N E0 p] T.[k * w + s]) in *.
    destruct (qltb qa qb) eqn:L1.
    + right; left. split; [reflexivity|]. apply qltb_R in L1. rewrite Ea, Eb in L1.
      exists pn. split; [exact Hpn|]. split.
      * intros q Hq. rewrite Pre by exact Hq. ring.
      * assert (fk pn < fr pn)%R by nra. lra.
    + destruct (qltb qb qa) eqn:L2.
      * right; right. split; [reflexivity|]. apply qltb_R in L2. rewrite Ea, Eb in L2.
        apply (lex_gt_not_lt _ _ _ pn Hpn Pre). nra.
      * left. split; [reflexivity|]. apply qltb_R_false in L1. apply qltb_R_false in L2.
        rewrite Ea, Eb in L1, L2. intros q Hq. rewrite Ep1 in Hq.
        destruct (Nat.eq_dec q pn) as [Eq|Nq].
        -- subst q. nra.
        -- apply Pre. unfold pn in *. lia.
  - cbv zeta in P, E. destruct P as [[P1 P2] | [[P1 P2] | [P1 P2]]]; rewrite P1.
    + destruct E as [E|[_ E]].
      * split; [discriminate|]. intros L. exfalso. apply (lexlt_irrefl (S mn) fk fr); [|exact L].
        intros q Hq. apply P2. rewrite E, Hm1. unfold mn in Hq. lia.
      * rewrite P1 in E. discriminate.
    + split; [intros _; exact P2 | reflexivity].
    + split; [discriminate | intros L; contradiction].
Qed.

End Lex.

(* ------------------------------------------------------------------ *)
(* leave                                                               *)
(* ------------------------------------------------------------------ *)

Section Leave.
Variables (T : array Q) (w N E0 m s : int).
Hypothesis Hw : to_Z w = (to_Z N + 1)%Z.
Hypothesis HN : to_Z N = (to_Z E0 + to_Z m)%Z.
Hypothesis Hsz : (to_Z m * to_Z w <= 4194303)%Z.
Hypothesis Hs : (to_Z s < to_Z N)%Z.

Let mn := Z.to_nat (to_Z m).
Let en := Z.to_nat (to_Z E0).
Definition tz (k : int) : R := cellZ T w (to_Z k) (to_Z s).
Definition fv (k : int) : nat -> R :=
  fun p => (rowvec mn en (cell T w) (Z.to_nat (to_Z k)) p / tz k)%R.

Definition leave_inv (kz : int) (best : option int) : Prop :=
  match best with
  | None => forall k, (to_Z k < to_Z kz)%Z -> (tz k <= 0)%R
  | Some r => (to_Z r < to_Z kz)%Z /\ (0 < tz r)%R /\
      forall k, (to_Z k < to_Z kz)%Z -> (0 < tz k)%R -> ~ lexlt (S mn) (fv k) (fv r)
  end.

Lemma leave_all : leave_inv m (leave T w N E0 m s).
Proof.
  unfold leave. pose proof (to_Z_bounded m). pose proof (to_Z_bounded w).
  apply for_inv.
  - change (to_Z 0) with 0%Z. lia.
  - intros k Hk. pose proof (to_Z_bounded k). change (to_Z 0) with 0%Z in Hk. lia.
  - intros k best Hk Pb. change (to_Z 0) with 0%Z in Hk.
    assert (Ek1 : to_Z (k + 1) = (to_Z k + 1)%Z) by sia.
    assert (Etk : Q2R T.[k * w + s] = tz k).
    { unfold tz. apply cellZ_get. pose proof (to_Z_bounded s). nia. }
    assert (Same : forall k', (to_Z k' < to_Z (k + 1))%Z -> to_Z k' <> to_Z k -> (to_Z k' < to_Z k)%Z) by lia.
    destruct (qltb 0 T.[k * w + s]) eqn:Ep.
    + apply qltb_R in Ep. rewrite Q2R_0, Etk in Ep.
      destruct best as [r|].
      * destruct Pb as (Hr & Pr & Hmin).
        assert (LS : lexless T w N E0 m k r s = true <-> lexlt (S mn) (fv k) (fv r))
          by (apply lexless_spec; try assumption; try lia).
        destruct (bdec (lexless T w N E0 m k r s)) as [L|L]; rewrite L.
        -- apply LS in L.
           simpl. split; [lia|]. split; [exact Ep|].
           intros k' Hk' Pk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E|E].
           ++ apply to_Z_inj in E. subst k'. apply lexlt_irrefl. intros; reflexivity.
           ++ intros L'. apply (Hmin k' (Same k' Hk' E) Pk'). eapply lexlt_trans; [exact L'|].
              exact L.
        -- simpl. split; [lia|]. split; [exact Pr|].
           intros k' Hk' Pk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E|E].
           ++ apply to_Z_inj in E. subst k'. intros L'. apply LS in L'. congruence.
           ++ apply Hmin; [apply Same|]; assumption.
      * simpl. split; [lia|]. split; [exact Ep|].
        intros k' Hk' Pk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E|E].
        -- apply to_Z_inj in E. subst k'. apply lexlt_irrefl. intros; reflexivity.
        -- exfalso. pose proof (Pb k' (Same k' Hk' E)). lra.
    + apply qltb_R_false in Ep. rewrite Q2R_0, Etk in Ep.
      destruct best as [r|].
      * destruct Pb as (Hr & Pr & Hmin). simpl. split; [lia|]. split; [exact Pr|].
        intros k' Hk' Pk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E|E].
        -- apply to_Z_inj in E. subst k'. lra.
        -- apply Hmin; [apply Same|]; assumption.
      * simpl. intros k' Hk'. destruct (Z.eq_dec (to_Z k') (to_Z k)) as [E|E].
        -- apply to_Z_inj in E. subst k'. exact Ep.
        -- apply Pb. apply Same; assumption.
Qed.

End Leave.

(* ------------------------------------------------------------------ *)
(* the pivot, cell by cell                                             *)
(* ------------------------------------------------------------------ *)

Section Pivot.
Variables (w m r : int).
Hypothesis Hsz : (to_Z m * to_Z w <= 4194303)%Z.
Hypothesis Hr : (to_Z r < to_Z m)%Z.

Definition IR (k j : Z) : Prop := (0 <= k < to_Z m)%Z /\ (0 <= j < to_Z w)%Z.

Lemma cellZ_set_IR : forall T (k0 j0 : int) v k j,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z ->
  IR k j -> IR (to_Z k0) (to_Z j0) ->
  cellZ (T.[k0 * w + j0 <- v]) w k j =
  if (Z.eqb k (to_Z k0) && Z.eqb j (to_Z j0))%bool then Q2R v else cellZ T w k j.
Proof.
  intros T k0 j0 v k j HL [Hk Hj] [Hk0 Hj0]. apply cellZ_set; try lia; rewrite HL; nia.
Qed.

Lemma cellZ_get_IR : forall T (k c : int), IR (to_Z k) (to_Z c) ->
  Q2R T.[k * w + c] = cellZ T w (to_Z k) (to_Z c).
Proof. intros T k c [Hk Hc]. apply cellZ_get. rewrite wB_val. nia. Qed.

Lemma scale_row_spec : forall T inv,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z ->
  to_Z (PArray.length (scale_row T w r inv)) = (to_Z m * to_Z w)%Z /\
  forall k j, IR k j -> cellZ (scale_row T w r inv) w k j =
    if Z.eqb k (to_Z r) then (cellZ T w k j * Q2R inv)%R else cellZ T w k j.
Proof.
  intros T inv HL. unfold scale_row. pose proof (to_Z_bounded w).
  pose (Iv := (fun jz T' => to_Z (PArray.length T') = (to_Z m * to_Z w)%Z /\
     forall k j, IR k j -> cellZ T' w k j =
       if (Z.eqb k (to_Z r) && Z.ltb j jz)%bool then (cellZ T w k j * Q2R inv)%R else cellZ T w k j)).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL|]. intros k j [Hk Hj]. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec j 0); [lia|]. rewrite andb_false_r. reflexivity.
  - intros j T' Hj [HL' P]. change (to_Z 0) with 0%Z in Hj. split; [rewrite lsetQ; exact HL'|].
    intros k j' Hkj. pose proof (to_Z_bounded r).
    rewrite cellZ_set_IR; [| exact HL' | exact Hkj | split; lia].
    rewrite qmul_R, cellZ_get_IR by (split; lia). rewrite P by (split; lia).
    rewrite Z.eqb_refl, Z.ltb_irrefl. simpl.
    destruct (Z.eqb_spec k (to_Z r)); destruct (Z.eqb_spec j' (to_Z j)); simpl.
    + subst. destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); [reflexivity | lia].
    + rewrite P by exact Hkj. rewrite e. rewrite Z.eqb_refl. simpl.
      destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1)); try reflexivity; lia.
    + rewrite P by exact Hkj. destruct (Z.eqb_spec k (to_Z r)); [contradiction|reflexivity].
    + rewrite P by exact Hkj. destruct (Z.eqb_spec k (to_Z r)); [contradiction|reflexivity].
  - destruct G as [HL' P]. split; [exact HL'|]. intros k j Hkj. rewrite P by exact Hkj.
    destruct Hkj as [_ Hj]. destruct (Z.ltb_spec j (to_Z w)); [|lia].
    rewrite andb_true_r. reflexivity.
Qed.

Lemma elim_row_spec : forall T k f,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z ->
  (to_Z k < to_Z m)%Z -> to_Z k <> to_Z r ->
  to_Z (PArray.length (elim_row T w r k f)) = (to_Z m * to_Z w)%Z /\
  forall k' j, IR k' j -> cellZ (elim_row T w r k f) w k' j =
    if Z.eqb k' (to_Z k) then (cellZ T w (to_Z k) j - Q2R f * cellZ T w (to_Z r) j)%R
    else cellZ T w k' j.
Proof.
  intros T k f HL Hk Hkr. unfold elim_row. pose proof (to_Z_bounded w).
  pose proof (to_Z_bounded k). pose proof (to_Z_bounded r).
  pose (Iv := (fun jz T' => to_Z (PArray.length T') = (to_Z m * to_Z w)%Z /\
     forall k' j, IR k' j -> cellZ T' w k' j =
       if (Z.eqb k' (to_Z k) && Z.ltb j jz)%bool
       then (cellZ T w (to_Z k) j - Q2R f * cellZ T w (to_Z r) j)%R else cellZ T w k' j)).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL|]. intros k' j [Hk' Hj]. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec j 0); [lia|]. rewrite andb_false_r. reflexivity.
  - intros j T' Hj [HL' P]. change (to_Z 0) with 0%Z in Hj.
    assert (Ea : Q2R T'.[r * w + j] = cellZ T w (to_Z r) (to_Z j)).
    { rewrite cellZ_get_IR by (split; lia). rewrite P by (split; lia).
      destruct (Z.eqb_spec (to_Z r) (to_Z k)); [lia|reflexivity]. }
    cbv zeta. destruct (qzerob T'.[r * w + j]) eqn:Z0.
    + apply qzerob_R in Z0. rewrite Ea in Z0. split; [exact HL'|].
      intros k' j' Hkj. rewrite P by exact Hkj.
      destruct (Z.eqb_spec k' (to_Z k)); simpl; [|reflexivity].
      destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1)); try reflexivity; try lia.
      subst k'. replace j' with (to_Z j) by lia. rewrite Z0. ring.
    + split; [rewrite lsetQ; exact HL'|].
      intros k' j' Hkj. rewrite cellZ_set_IR; [| exact HL' | exact Hkj | split; lia].
      destruct (Z.eqb_spec k' (to_Z k)); destruct (Z.eqb_spec j' (to_Z j)); simpl.
      * subst. rewrite qsub_R, Q2R_mult, Ea, cellZ_get_IR by (split; lia).
        rewrite P by (split; lia). rewrite Z.eqb_refl, Z.ltb_irrefl. simpl.
        destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); [reflexivity|lia].
      * rewrite P by exact Hkj. subst k'. rewrite Z.eqb_refl. simpl.
        destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1)); try reflexivity; lia.
      * rewrite P by exact Hkj. destruct (Z.eqb_spec k' (to_Z k)); [contradiction|reflexivity].
      * rewrite P by exact Hkj. destruct (Z.eqb_spec k' (to_Z k)); [contradiction|reflexivity].
  - destruct G as [HL' P]. split; [exact HL'|]. intros k' j Hkj. rewrite P by exact Hkj.
    destruct Hkj as [_ Hj]. destruct (Z.ltb_spec j (to_Z w)); [|lia].
    rewrite andb_true_r. reflexivity.
Qed.

Lemma elim_all_spec : forall T s,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z -> (to_Z s < to_Z w)%Z ->
  to_Z (PArray.length (elim_all T w m r s)) = (to_Z m * to_Z w)%Z /\
  forall k j, IR k j -> cellZ (elim_all T w m r s) w k j =
    if Z.eqb k (to_Z r) then cellZ T w k j
    else (cellZ T w k j - cellZ T w k (to_Z s) * cellZ T w (to_Z r) j)%R.
Proof.
  intros T s HL Hs. unfold elim_all. pose proof (to_Z_bounded w). pose proof (to_Z_bounded m).
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded s).
  pose (Iv := (fun kz T' => to_Z (PArray.length T') = (to_Z m * to_Z w)%Z /\
     forall k j, IR k j -> cellZ T' w k j =
       if (Z.ltb k kz && negb (Z.eqb k (to_Z r)))%bool
       then (cellZ T w k j - cellZ T w k (to_Z s) * cellZ T w (to_Z r) j)%R else cellZ T w k j)).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL|]. intros k j [Hk Hj]. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec k 0); [lia|]. reflexivity.
  - intros k T' Hk [HL' P]. change (to_Z 0) with 0%Z in Hk.
    destruct (k =? r) eqn:Ekr.
    + apply Uint63.eqb_spec in Ekr. subst k. split; [exact HL'|].
      intros k' j Hkj. rewrite P by exact Hkj.
      destruct (Z.eqb_spec k' (to_Z r)); simpl.
      * rewrite !andb_false_r. reflexivity.
      * rewrite !andb_true_r. destruct (Z.ltb_spec k' (to_Z r)); destruct (Z.ltb_spec k' (to_Z r + 1));
          try reflexivity; lia.
    + apply Uint63.eqb_false_spec in Ekr.
      assert (Ekr' : to_Z k <> to_Z r) by (intros E; apply Ekr, to_Z_inj; exact E).
      assert (Ef : Q2R T'.[k * w + s] = cellZ T w (to_Z k) (to_Z s)).
      { rewrite cellZ_get_IR by (split; lia). rewrite P by (split; lia).
        destruct (Z.ltb_spec (to_Z k) (to_Z k)); [lia|]. reflexivity. }
      cbv zeta. destruct (qzerob T'.[k * w + s]) eqn:Z0.
      * apply qzerob_R in Z0. rewrite Ef in Z0. split; [exact HL'|].
        intros k' j Hkj. rewrite P by exact Hkj.
        destruct (Z.eqb_spec k' (to_Z r)); simpl; [rewrite !andb_false_r; reflexivity|].
        rewrite !andb_true_r.
        destruct (Z.ltb_spec k' (to_Z k)); destruct (Z.ltb_spec k' (to_Z k + 1)); try reflexivity; try lia.
        replace k' with (to_Z k) by lia. rewrite Z0. ring.
      * destruct (elim_row_spec T' k (T'.[k * w + s]) HL' ltac:(lia) Ekr') as [HL2 P2].
        split; [exact HL2|]. intros k' j Hkj. rewrite P2 by exact Hkj.
        destruct (Z.eqb_spec k' (to_Z k)).
        -- subst k'. rewrite Ef. rewrite P by (destruct Hkj; split; lia).
           rewrite (P (to_Z r) j) by (destruct Hkj; split; lia).
           destruct (Z.ltb_spec (to_Z k) (to_Z k)); [lia|]. simpl.
           rewrite Z.eqb_refl. simpl. rewrite andb_false_r.
           destruct (Z.ltb_spec (to_Z k) (to_Z k + 1)); [|lia].
           destruct (Z.eqb_spec (to_Z k) (to_Z r)); [lia|]. reflexivity.
        -- rewrite P by exact Hkj.
           destruct (Z.ltb_spec k' (to_Z k)); destruct (Z.ltb_spec k' (to_Z k + 1)); try reflexivity; try lia.
  - destruct G as [HL' P]. split; [exact HL'|]. intros k j Hkj. rewrite P by exact Hkj.
    destruct Hkj as [Hk _]. destruct (Z.ltb_spec k (to_Z m)); [|lia].
    destruct (Z.eqb (k) (to_Z r)); reflexivity.
Qed.

Lemma elim_obj_spec : forall O T f,
  to_Z (PArray.length O) = to_Z w -> to_Z (PArray.length T) = (to_Z m * to_Z w)%Z ->
  to_Z (PArray.length (elim_obj O T w r f)) = to_Z w /\
  forall j, (0 <= j < to_Z w)%Z -> Q2R (elim_obj O T w r f).[of_Z j] =
    (Q2R O.[of_Z j] - Q2R f * cellZ T w (to_Z r) j)%R.
Proof.
  intros O T f HO HL. unfold elim_obj. pose proof (to_Z_bounded w). pose proof (to_Z_bounded r).
  pose (Iv := (fun jz O' => to_Z (PArray.length O') = to_Z w /\
     forall j, (0 <= j < to_Z w)%Z -> Q2R O'.[of_Z j] =
       if Z.ltb j jz then (Q2R O.[of_Z j] - Q2R f * cellZ T w (to_Z r) j)%R else Q2R O.[of_Z j])).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HO|]. intros j Hj. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec j 0); [lia|reflexivity].
  - intros j O' Hj [HO' P]. change (to_Z 0) with 0%Z in Hj.
    assert (Ea : Q2R T.[r * w + j] = cellZ T w (to_Z r) (to_Z j)) by (apply cellZ_get_IR; split; lia).
    cbv zeta. destruct (qzerob T.[r * w + j]) eqn:Z0.
    + apply qzerob_R in Z0. rewrite Ea in Z0. split; [exact HO'|].
      intros j' Hj'. rewrite P by exact Hj'.
      destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1)); try reflexivity; try lia.
      replace j' with (to_Z j) by lia. rewrite Z0. ring.
    + split; [rewrite lsetQ; exact HO'|]. intros j' Hj'.
      destruct (Z.eq_dec j' (to_Z j)) as [E|E].
      * subst j'. rewrite of_Z_to_Z. rewrite gssQ by lia.
        rewrite qsub_R, Q2R_mult, Ea. rewrite <- (of_Z_to_Z j) at 1. rewrite P by lia.
        destruct (Z.ltb_spec (to_Z j) (to_Z j)); [lia|].
        destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); [|lia]. rewrite of_Z_to_Z. reflexivity.
      * rewrite gsoZQ by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
        rewrite P by exact Hj'.
        destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1)); try reflexivity; lia.
  - destruct G as [HO' P]. split; [exact HO'|]. intros j Hj. rewrite P by exact Hj.
    destruct (Z.ltb_spec j (to_Z w)); [reflexivity|lia].
Qed.

End Pivot.
End P_SP.

(* ================================================================== *)
Section P_SL.
Import ListNotations.
Open Scope uint63_scope.

Lemma idx_lt : forall a b c d M : Z, (0 <= a < c)%Z -> (0 <= b < d)%Z -> (c * d <= M)%Z ->
  (a * d + b < M)%Z.
Proof. intros a b c d M Ha Hb Hm. nia. Qed.

Lemma cell_ii : forall T w (a b : int), cell T w (Z.to_nat (to_Z a)) (Z.to_nat (to_Z b)) = cellZ T w (to_Z a) (to_Z b).
Proof. intros. unfold cell. rewrite !Z2Nat.id by (pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); lia). reflexivity. Qed.

Lemma cell_ni : forall T w (k : nat) (b : int), cell T w k (Z.to_nat (to_Z b)) = cellZ T w (Z.of_nat k) (to_Z b).
Proof. intros. unfold cell. rewrite Z2Nat.id by (pose proof (to_Z_bounded b); lia). reflexivity. Qed.

Lemma Z_of_to_nat : forall x : int, Z.of_nat (Z.to_nat (to_Z x)) = to_Z x.
Proof. intros x. apply Z2Nat.id. pose proof (to_Z_bounded x). lia. Qed.

Lemma of_Z_of_to_nat : forall x : int, of_Z (Z.of_nat (Z.to_nat (to_Z x))) = x.
Proof. intros x. rewrite Z_of_to_nat. apply of_Z_to_Z. Qed.

Section SL.
Variables (m E0 : int).
Hypothesis Hm1 : (1 <= to_Z m)%Z.
Hypothesis Hwb : (to_Z E0 + to_Z m + 1 <= 4194303)%Z.
Hypothesis Hsz : (to_Z m * (to_Z E0 + to_Z m + 1) <= 4194303)%Z.

Local Notation mn := (Z.to_nat (to_Z m)).
Local Notation en := (Z.to_nat (to_Z E0)).
Local Notation w := (E0 + m + 1).
Local Notation N := (E0 + m).

Lemma N_val : to_Z N = (to_Z E0 + to_Z m)%Z.
Proof. pose proof (to_Z_bounded E0). pose proof (to_Z_bounded m). sia. Qed.

Lemma w_val : to_Z w = (to_Z E0 + to_Z m + 1)%Z.
Proof. pose proof (to_Z_bounded E0). pose proof (to_Z_bounded m). sia. Qed.

Lemma Nnat : Z.of_nat (en + mn) = (to_Z E0 + to_Z m)%Z.
Proof. pose proof (to_Z_bounded E0). pose proof (to_Z_bounded m). lia. Qed.

Lemma Hszw : (to_Z m * to_Z w <= 4194303)%Z.
Proof. rewrite w_val. exact Hsz. Qed.

Definition WFs (st : SState) : Prop :=
  to_Z (PArray.length (sT st)) = (to_Z m * to_Z w)%Z /\
  to_Z (PArray.length (sO st)) = to_Z w /\ to_Z (PArray.length (sB st)) = to_Z m.

Definition ttab (st : SState) : nat -> nat -> R := cell (sT st) w.
Definition oo (st : SState) : nat -> R := ovec (sO st).
Definition bb (st : SState) : nat -> nat := bvec (sB st).

Definition VS (t0 : nat -> nat -> R) (c : nat -> R) (st : SState) : Prop :=
  WFs st /\ Valid mn en t0 c (ttab st) (oo st) (bb st).

Lemma pivot_corr : forall st r s, WFs st -> (to_Z r < to_Z m)%Z -> (to_Z s < to_Z N)%Z ->
  cellZ (sT st) w (to_Z r) (to_Z s) <> 0%R ->
  WFs (pivot w m st r s) /\
  (forall k j, (k < mn)%nat -> (j <= en + mn)%nat ->
     ttab (pivot w m st r s) k j = pt (ttab st) (Z.to_nat (to_Z r)) (Z.to_nat (to_Z s)) k j) /\
  (forall j, (j <= en + mn)%nat ->
     oo (pivot w m st r s) j = po (ttab st) (oo st) (Z.to_nat (to_Z r)) (Z.to_nat (to_Z s)) j) /\
  (forall k, (k < mn)%nat ->
     bb (pivot w m st r s) k = pb (bb st) (Z.to_nat (to_Z r)) (Z.to_nat (to_Z s)) k).
Proof.
  intros [[T O] B] r s (HT & HO & HB) Hr Hs Hp. unfold sT, sO, sB in *. simpl in *.
  pose proof w_val as Ew. pose proof N_val as EN. pose proof Hszw as Hsz'.
  assert (Bj : forall j, (j <= en + mn)%nat -> (0 <= Z.of_nat j < to_Z w)%Z).
  { clear -Ew. intros j Hj. rewrite Ew. pose proof (to_Z_bounded E0). pose proof (to_Z_bounded m). lia. }
  assert (Bk : forall k, (k < mn)%nat -> (0 <= Z.of_nat k < to_Z m)%Z).
  { clear. intros k Hk. pose proof (to_Z_bounded m). lia. }
  assert (Bs : (0 <= to_Z s < to_Z w)%Z).
  { clear -Ew EN Hs. pose proof (to_Z_bounded s). lia. }
  assert (Br : (0 <= to_Z r < to_Z m)%Z).
  { clear -Hr. pose proof (to_Z_bounded r). lia. }
  assert (Epiv : Q2R T.[r * w + s] = cellZ T w (to_Z r) (to_Z s)).
  { apply cellZ_get. rewrite wB_val.
    pose proof (idx_lt (to_Z r) (to_Z s) (to_Z m) (to_Z w) 4194303 Br Bs Hsz'). lia. }
  assert (Hinv : Q2R (Qinv T.[r * w + s]) = (/ cellZ T w (to_Z r) (to_Z s))%R)
    by (rewrite Qinv_R; rewrite Epiv; [reflexivity | exact Hp]).
  destruct (scale_row_spec w m r Hsz' Hr T (Qinv T.[r * w + s]) HT) as [HT1 P1].
  rewrite Hinv in P1.
  set (T1 := scale_row T w r (Qinv T.[r * w + s])) in *.
  destruct (elim_all_spec w m r Hsz' Hr T1 s HT1 (proj2 Bs)) as [HT2 P2].
  set (T2 := elim_all T1 w m r s) in *.
  destruct (elim_obj_spec w m r Hsz' Hr O T2 O.[s] HO HT2) as [HO3 P3].
  unfold pivot, sT, sO, sB. simpl. fold T1. fold T2.
  split; [|split; [|split]].
  - split; [exact HT2|]. split; [exact HO3|].
    etransitivity; [apply f_equal; exact (length_set int B r s) | exact HB].
  - intros k j Hk Hj. unfold ttab, pt, cell, sT. simpl.
    rewrite P2 by (split; [apply Bk | apply Bj]; assumption).
    rewrite !Z_of_to_nat.
    rewrite (P1 (Z.of_nat k) (Z.of_nat j)) by (split; [apply Bk | apply Bj]; assumption).
    rewrite (P1 (Z.of_nat k) (to_Z s)) by (split; [apply Bk; assumption | exact Bs]).
    rewrite (P1 (to_Z r) (Z.of_nat j)) by (split; [exact Br | apply Bj; assumption]).
    rewrite Z.eqb_refl.
    destruct (Z.eqb_spec (Z.of_nat k) (to_Z r)) as [E|E];
      destruct (Nat.eqb_spec k (Z.to_nat (to_Z r))) as [E'|E']; try (exfalso; clear -E E' Br; lia).
    + rewrite <- E. unfold Rdiv. reflexivity.
    + unfold Rdiv. ring.
  - intros j Hj. unfold oo, ovec, po, ttab, cell, sT, sO. simpl.
    rewrite P3 by (apply Bj; assumption).
    rewrite P2 by (split; [exact Br | apply Bj; assumption]). rewrite Z.eqb_refl.
    rewrite (P1 (to_Z r) (Z.of_nat j)) by (split; [exact Br | apply Bj; assumption]). rewrite Z.eqb_refl.
    rewrite !Z_of_to_nat. rewrite of_Z_to_Z. unfold Rdiv. ring.
  - intros k Hk. unfold bb, bvec, pb, sB. simpl.
    destruct (Nat.eqb_spec k (Z.to_nat (to_Z r))) as [E|E].
    + subst k. rewrite of_Z_of_to_nat. rewrite gssI by (rewrite HB; exact (proj2 Br)). reflexivity.
    + rewrite gsoZI; [reflexivity|]. pose proof (Bk k Hk) as Bkk.
      assert (Bkk' : (0 <= Z.of_nat k < wB)%Z) by (clear -Bkk; pose proof (to_Z_bounded m); lia).
      rewrite to_Z_of_Z_small by exact Bkk'. clear -E Br. lia.
Qed.

Lemma enter_some_math : forall al O s, enter N al O = Some s ->
  (Z.to_nat (to_Z s) < en + mn)%nat /\ al.[s] = true /\ (ovec O (Z.to_nat (to_Z s)) < 0)%R.
Proof.
  intros al O s E. pose proof (enter_all N al O) as P. rewrite E in P. simpl in P.
  destruct P as (P1 & P2 & P3). rewrite N_val in P1. pose proof (to_Z_bounded s).
  split; [lia|]. split; [exact P2|]. rewrite <- ovec_get. exact P3.
Qed.

Lemma enter_none_math : forall al O, enter N al O = None ->
  forall j, (j < en + mn)%nat -> al.[of_Z (Z.of_nat j)] = true -> (0 <= ovec O j)%R.
Proof.
  intros al O E j Hj Hal. pose proof (enter_all N al O) as P. rewrite E in P. simpl in P.
  unfold ovec. apply P; [|exact Hal]. rewrite to_Z_of_Z_small by (rewrite wB_val; lia).
  rewrite N_val. lia.
Qed.

Lemma leave_some_math : forall T r s, (to_Z s < to_Z N)%Z ->
  leave T w N E0 m s = Some r ->
  (to_Z r < to_Z m)%Z /\ LeaveOK mn en (cell T w) (Z.to_nat (to_Z r)) (Z.to_nat (to_Z s)).
Proof.
  intros T r s Hs E.
  pose proof (leave_all T w N E0 m s ltac:(rewrite w_val, N_val; lia) N_val Hszw Hs) as P.
  rewrite E in P. simpl in P. destruct P as (P1 & P2 & P3).
  pose proof (to_Z_bounded r). pose proof (to_Z_bounded s).
  split; [exact P1|]. split; [lia|]. split.
  - unfold tz in P2. rewrite cell_ii. exact P2.
  - intros k Hk Pk. rewrite cell_ni in Pk. set (kk := of_Z (Z.of_nat k)).
    assert (Ekk : to_Z kk = Z.of_nat k) by (unfold kk; rewrite to_Z_of_Z_small by (rewrite wB_val; lia); reflexivity).
    assert (Pk' : (0 < tz T w s kk)%R) by (unfold tz; rewrite Ekk; exact Pk).
    pose proof (P3 kk ltac:(lia) Pk') as H3.
    unfold fv, tz in H3. rewrite Ekk in H3. rewrite Nat2Z.id in H3.
    rewrite cell_ni, cell_ii. exact H3.
Qed.

Lemma leave_none_math : forall T s, (to_Z s < to_Z N)%Z ->
  leave T w N E0 m s = None -> forall k, (k < mn)%nat -> (cell T w k (Z.to_nat (to_Z s)) <= 0)%R.
Proof.
  intros T s Hs E k Hk.
  pose proof (leave_all T w N E0 m s ltac:(rewrite w_val, N_val; lia) N_val Hszw Hs) as P.
  rewrite E in P. simpl in P.
  pose proof (P (of_Z (Z.of_nat k))) as H. unfold tz in H.
  rewrite to_Z_of_Z_small in H by (rewrite wB_val; lia).
  rewrite cell_ni. apply H. lia.
Qed.

Lemma step_VS : forall t0 c al st st', unit0 mn en t0 -> VS t0 c st -> SRel m E0 al st' st ->
  VS t0 c st' /\ lexlt (S mn) (Wv mn en (oo st)) (Wv mn en (oo st')).
Proof.
  intros t0 c al st st' U [W V] (s & r & Es & Er & ->).
  destruct (enter_some_math al (sO st) s Es) as (Hs & Hal & Hneg).
  assert (Hs' : (to_Z s < to_Z N)%Z) by (rewrite N_val; pose proof (to_Z_bounded s); lia).
  destruct (leave_some_math (sT st) r s Hs' Er) as [Hr LO].
  pose proof LO as (Hrn & Ppiv & _).
  assert (Hp : cellZ (sT st) w (to_Z r) (to_Z s) <> 0%R).
  { unfold cell in Ppiv. rewrite !Z_of_to_nat in Ppiv. lra. }
  destruct (pivot_corr st r s W Hr Hs' Hp) as (W' & Et & Eo & Eb).
  split; [split; [exact W'|]|].
  - eapply Valid_ext; [| exact Et | exact Eo | exact Eb].
    apply pivot_valid; auto.
  - pose proof (pivot_lex _ _ _ _ _ _ _ _ _ V Hneg LO) as L.
    unfold lexlt in *. eapply lexgt0_ext; [|exact L]. intros p Hp'. unfold Wv.
    rewrite Eo by (apply lcol_le; exact Hp'). reflexivity.
Qed.

Lemma map_seq_eq : forall (f g : nat -> nat) n, map f (seq 0 n) = map g (seq 0 n) ->
  forall k, (k < n)%nat -> f k = g k.
Proof.
  intros f g n E k Hk.
  assert (A : nth k (map f (seq 0 n)) 0%nat = nth k (map g (seq 0 n)) 0%nat) by (rewrite E; reflexivity).
  rewrite !(nth_indep _ _ (f 0%nat)) in A by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth in A by exact Hk.
  rewrite (nth_indep _ _ (g 0%nat)) in A by (rewrite length_map, length_seq; exact Hk).
  rewrite map_nth, seq_nth in A by exact Hk. simpl in A. exact A.
Qed.

Lemma acc_VS : forall t0 c al st, unit0 mn en t0 -> VS t0 c st -> Acc (SRel m E0 al) st.
Proof.
  intros t0 c al st U Vs.
  apply (acc_fin SState (SRel m E0 al) (VS t0 c) (S mn) (fun st => Wv mn en (oo st))
           (fun st => map (bb st) (seq 0 mn)) (all_keys mn (en + mn))).
  - intros s s' Vs1 R1. apply (step_VS t0 c al s s' U Vs1 R1).
  - intros s [_ V]. apply all_keys_in.
    + rewrite length_map, length_seq. reflexivity.
    + intros a Ha. apply in_map_iff in Ha. destruct Ha as (k & <- & Hk).
      apply in_seq in Hk. apply (v_bs _ _ _ _ _ _ _ V). lia.
  - intros s1 s2 [_ V1] [_ V2] E p Hp.
    apply (determination _ _ _ _ _ _ _ _ _ _ V1 V2); [|exact Hp].
    intros k Hk. apply (map_seq_eq _ _ mn E k Hk).
  - exact Vs.
Qed.

Definition SExit (al : array bool) (st : SState) : Prop :=
  enter N al (sO st) = None \/
  exists s, enter N al (sO st) = Some s /\ leave (sT st) w N E0 m s = None.

Lemma sloop_ind : forall al (P : SState -> Prop),
  (forall st st', P st -> SRel m E0 al st' st -> P st') ->
  forall st (H : Acc (SRel m E0 al) st), P st ->
  P (sloop m E0 al st H) /\ SExit al (sloop m E0 al st H).
Proof.
  intros al P Hp. fix IH 2. intros st H Pst. destruct H as [Ha]. simpl.
  destruct (odec (enter (E0 + m) al (sO st))) as [[s Es]|Es].
  - destruct (odec (leave (sT st) (E0 + m + 1) (E0 + m) E0 m s)) as [[r Er]|Er].
    + apply IH. apply (Hp st); [exact Pst|]. exists s, r. auto.
    + split; [exact Pst|]. right. exists s. auto.
  - split; [exact Pst|]. left. exact Es.
Qed.

(* -- the objective row of a cost vector -- *)

Lemma canon_obj_spec : forall T B carr,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z -> to_Z (PArray.length carr) = to_Z w ->
  to_Z (PArray.length (canon_obj T B carr w m)) = to_Z w /\
  forall j, (j <= en + mn)%nat ->
    ovec (canon_obj T B carr w m) j =
    (ovec carr j - sumR mn (fun k => ovec carr (bvec B k) * cell T w k j))%R.
Proof.
  intros T B carr HT Hc. unfold canon_obj. pose proof Hszw as Hsz'. pose proof w_val as Ew.
  pose proof (to_Z_bounded m).
  pose (Iv := fun kz O => to_Z (PArray.length O) = to_Z w /\
     forall j, (0 <= j < to_Z w)%Z -> Q2R O.[of_Z j] =
       (Q2R carr.[of_Z j] - sumR (Z.to_nat kz) (fun k => ovec carr (bvec B k) * cellZ T w (Z.of_nat k) j))%R).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G] end.
  - change (to_Z 0) with 0%Z. lia.
  - rewrite lcopyQ. split; [exact Hc|]. intros j Hj. rewrite gcopyQ. simpl. ring.
  - intros k O' Hk [HO' P]. change (to_Z 0) with 0%Z in Hk.
    replace (Z.to_nat (to_Z k + 1)) with (S (Z.to_nat (to_Z k))) by lia. simpl sumR.
    assert (Ef : Q2R carr.[(B.[k])] = ovec carr (bvec B (Z.to_nat (to_Z k)))).
    { unfold ovec, bvec. rewrite of_Z_of_to_nat. rewrite of_Z_of_to_nat. reflexivity. }
    cbv zeta. destruct (qzerob carr.[B.[k]]) eqn:Z0.
    + apply qzerob_R in Z0. rewrite Ef in Z0. split; [exact HO'|]. intros j Hj.
      rewrite P by exact Hj. rewrite Z0. ring.
    + destruct (elim_obj_spec w m k Hsz' ltac:(lia) O' T (carr.[B.[k]]) HO' HT) as [HO2 P2].
      split; [exact HO2|]. intros j Hj. rewrite P2 by exact Hj. rewrite P by exact Hj.
      rewrite Ef. rewrite Z_of_to_nat. ring.
  - destruct G as [HO P]. split; [exact HO|]. intros j Hj. unfold ovec. rewrite P by (rewrite Ew; lia).
    unfold cell. reflexivity.
Qed.

Lemma canon_VS : forall t0 c' T O B carr,
  VS t0 c' (T, O, B) -> to_Z (PArray.length carr) = to_Z w -> Q2R carr.[N] = 0%R ->
  VS t0 (ovec carr) (T, canon_obj T B carr w m, B).
Proof.
  intros t0 c' T O B carr [(HT & HO & HB) V] Hc HN.
  destruct (canon_obj_spec T B carr HT Hc) as [HO2 P2].
  split; [split; [exact HT|]; split; [exact HO2 | exact HB]|].
  unfold ttab, oo, bb, sT, sO, sB in *. simpl in *.
  apply canon_valid.
  - apply (v_sol _ _ _ _ _ _ _ V).
  - apply (v_bs _ _ _ _ _ _ _ V).
  - apply (v_canon _ _ _ _ _ _ _ V).
  - apply (v_lex _ _ _ _ _ _ _ V).
  - exact P2.
  - unfold ovec. rewrite Nnat. rewrite <- N_val, of_Z_to_Z. exact HN.
Qed.

Lemma copy_VS : forall t0 c T O B, VS t0 c (T, O, B) ->
  VS t0 c (PArray.copy T, O, PArray.copy B).
Proof.
  intros t0 c T O B [(HT & HO & HB) V]. unfold VS, WFs, sT, sO, sB in *. simpl in *.
  split; [split; [rewrite lcopyQ; exact HT|]; split; [exact HO | rewrite lcopyI; exact HB]|].
  eapply Valid_ext; [exact V | | |].
  - intros k j _ _. unfold ttab, cell, cellZ, sT. simpl. rewrite gcopyQ. reflexivity.
  - intros j _. reflexivity.
  - intros k _. unfold bb, bvec, sB. simpl. rewrite gcopyI. reflexivity.
Qed.

Lemma init_VS : forall T B carr,
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z -> to_Z (PArray.length B) = to_Z m ->
  (forall k, (k < mn)%nat -> to_Z B.[of_Z (Z.of_nat k)] = (to_Z E0 + Z.of_nat k)%Z) ->
  unit0 mn en (cell T w) ->
  (forall k, (k < mn)%nat -> (0 <= cell T w k (en + mn))%R) ->
  to_Z (PArray.length carr) = to_Z w -> Q2R carr.[N] = 0%R ->
  VS (cell T w) (ovec carr) (T, canon_obj T B carr w m, B).
Proof.
  intros T B carr HT HB HBv U Hrhs Hc HN.
  destruct (canon_obj_spec T B carr HT Hc) as [HO2 P2].
  split; [split; [exact HT|]; split; [exact HO2 | exact HB]|].
  unfold ttab, oo, bb, sT, sO, sB in *. simpl in *.
  assert (Eb : forall k, (k < mn)%nat -> bvec B k = (en + k)%nat).
  { intros k Hk. unfold bvec. rewrite HBv by exact Hk. pose proof (to_Z_bounded E0). lia. }
  apply canon_valid.
  - intros x. reflexivity.
  - intros k Hk. rewrite Eb by exact Hk. lia.
  - intros k k' Hk Hk'. rewrite Eb by exact Hk'. apply U; assumption.
  - intros k Hk. apply unit0_rowlex; auto.
  - exact P2.
  - unfold ovec. rewrite Nnat. rewrite <- N_val, of_Z_to_Z. exact HN.
Qed.

End SL.
End P_SL.

(* ================================================================== *)
Section P_SV.
Import ListNotations.
Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* The two-phase driver                                                *)
(* ------------------------------------------------------------------ *)

Definition binit (m E0 : int) : array int :=
  forl 0 m (fun k B => B.[k <- E0 + k]) (PArray.make m 0).

(* the phase-1 cost: 1 on the artificial columns A0 .. N-1 *)
Definition cart (w A0 N : int) : array Q :=
  forl A0 N (fun j c => c.[j <- 1%Q]) (PArray.make w 0%Q).

Definition st0 (T0 : array Q) (m E0 A0 : int) : SState :=
  let B0 := binit m E0 in
  (T0, canon_obj T0 B0 (cart (E0 + m + 1) A0 (E0 + m)) (E0 + m + 1) m, B0).

Record P1ok (T0 : array Q) (m E0 A0 : int) : Prop := {
  p_m1 : (1 <= to_Z m)%Z;
  p_wb : (to_Z E0 + to_Z m + 1 <= 4194303)%Z;
  p_sz : (to_Z m * (to_Z E0 + to_Z m + 1) <= 4194303)%Z;
  p_unit : unit0 (Z.to_nat (to_Z m)) (Z.to_nat (to_Z E0)) (cell T0 (E0 + m + 1));
  p_vs : VS m E0 (cell T0 (E0 + m + 1)) (ovec (cart (E0 + m + 1) A0 (E0 + m))) (st0 T0 m E0 A0)
}.

Definition phase1 (T0 : array Q) (m E0 A0 : int) (Hp : P1ok T0 m E0 A0) : SState :=
  sloop m E0 (PArray.make (E0 + m) true) (st0 T0 m E0 A0)
    (acc_VS m E0 (p_m1 _ _ _ _ Hp) (p_wb _ _ _ _ Hp) (p_sz _ _ _ _ Hp)
       (cell T0 (E0 + m + 1)) (ovec (cart (E0 + m + 1) A0 (E0 + m)))
       (PArray.make (E0 + m) true) (st0 T0 m E0 A0) (p_unit _ _ _ _ Hp) (p_vs _ _ _ _ Hp)).

Lemma phase1_spec : forall T0 m E0 A0 (Hp : P1ok T0 m E0 A0),
  VS m E0 (cell T0 (E0 + m + 1)) (ovec (cart (E0 + m + 1) A0 (E0 + m))) (phase1 T0 m E0 A0 Hp) /\
  SExit m E0 (PArray.make (E0 + m) true) (phase1 T0 m E0 A0 Hp).
Proof.
  intros T0 m E0 A0 Hp. unfold phase1.
  apply sloop_ind; [| apply (p_vs _ _ _ _ Hp)].
  intros st st' V R. apply (step_VS m E0 (p_m1 _ _ _ _ Hp) (p_wb _ _ _ _ Hp) (p_sz _ _ _ _ Hp)
    _ _ _ st st' (p_unit _ _ _ _ Hp) V R).
Qed.

Lemma phase1_VS : forall T0 m E0 A0 (Hp : P1ok T0 m E0 A0),
  VS m E0 (cell T0 (E0 + m + 1)) (ovec (cart (E0 + m + 1) A0 (E0 + m))) (phase1 T0 m E0 A0 Hp).
Proof. intros. apply phase1_spec. Qed.

(* the columns phase 2 may bring in: before A0, with zero phase-1 reduced cost *)
Definition al2 (O1 : array Q) (A0 N : int) : array bool :=
  forl 0 N (fun j a => a.[j <- (j <? A0) && qzerob O1.[j]]) (PArray.make N false).

Definition mk2 (st1 : SState) (carr : array Q) (w m : int) : SState :=
  (PArray.copy (sT st1), canon_obj (sT st1) (sB st1) carr w m, PArray.copy (sB st1)).

Lemma mk2_VS : forall T0 m E0 A0 (Hp : P1ok T0 m E0 A0) st1 c carr,
  VS m E0 (cell T0 (E0 + m + 1)) c st1 ->
  ((PArray.length carr =? E0 + m + 1) && qzerob carr.[E0 + m])%bool = true ->
  VS m E0 (cell T0 (E0 + m + 1)) (ovec carr) (mk2 st1 carr (E0 + m + 1) m).
Proof.
  intros T0 m E0 A0 Hp [[T O] B] c carr V Hc. apply andb_true_iff in Hc. destruct Hc as [H1 H2].
  apply Uint63.eqb_spec in H1. apply qzerob_R in H2.
  unfold mk2, sT, sB. simpl.
  apply copy_VS; try apply Hp.
  eapply canon_VS; try apply Hp; [exact V | rewrite H1; reflexivity | exact H2].
Qed.

(* minimum of carr . x over the feasible set, from the phase-1 tableau st1 *)
Definition phase2 (T0 : array Q) (m E0 A0 : int) (Hp : P1ok T0 m E0 A0) (st1 : SState)
    (Hv : VS m E0 (cell T0 (E0 + m + 1)) (ovec (cart (E0 + m + 1) A0 (E0 + m))) st1)
    (al : array bool) (carr : array Q) : Q :=
  match bdec ((PArray.length carr =? E0 + m + 1) && qzerob carr.[E0 + m]) with
  | left Hc =>
      let st3 := sloop m E0 al (mk2 st1 carr (E0 + m + 1) m)
        (acc_VS m E0 (p_m1 _ _ _ _ Hp) (p_wb _ _ _ _ Hp) (p_sz _ _ _ _ Hp)
           (cell T0 (E0 + m + 1)) (ovec carr) al (mk2 st1 carr (E0 + m + 1) m)
           (p_unit _ _ _ _ Hp) (mk2_VS T0 m E0 A0 Hp st1 _ carr Hv Hc)) in
      Qopp (sO st3).[E0 + m]
  | right _ => 0%Q
  end.

(* ------------------------------------------------------------------ *)
(* Correctness of the driver                                           *)
(* ------------------------------------------------------------------ *)

Lemma Valid_c_ext : forall m E0 t0 c c' t o bs,
  (forall j, (j < E0 + m)%nat -> c j = c' j) ->
  Valid m E0 t0 c t o bs -> Valid m E0 t0 c' t o bs.
Proof.
  intros m E0 t0 c c' t o bs E V. destruct V as [Vs Vb Vc Vo Vj Vl]. constructor; auto.
  intros x Hx. rewrite <- (Vj x Hx). apply sumR_ext. intros j Hj. rewrite E by exact Hj. reflexivity.
Qed.

Lemma cart_spec : forall w A0 N, (to_Z A0 <= to_Z N)%Z -> (to_Z N < to_Z w)%Z -> (to_Z w <= 4194303)%Z ->
  to_Z (PArray.length (cart w A0 N)) = to_Z w /\
  forall j, (0 <= j < to_Z w)%Z ->
    Q2R (cart w A0 N).[of_Z j] = if (Z.leb (to_Z A0) j && Z.ltb j (to_Z N))%bool then 1%R else 0%R.
Proof.
  intros w A0 N HA HN Hw. unfold cart. pose proof (to_Z_bounded A0).
  pose (Iv := fun jz (c : array Q) => to_Z (PArray.length c) = to_Z w /\
     forall j, (0 <= j < to_Z w)%Z ->
       Q2R c.[of_Z j] = if (Z.leb (to_Z A0) j && Z.ltb j jz)%bool then 1%R else 0%R).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G; exact G] end.
  - exact HA.
  - rewrite lmakeQ by exact Hw. split; [reflexivity|]. intros j Hj. rewrite gmakeQ, Q2R_0.
    destruct (Z.leb_spec (to_Z A0) j); destruct (Z.ltb_spec j (to_Z A0)); try lia; reflexivity.
  - intros j c Hj [Hc P]. split; [rewrite lsetQ; exact Hc|]. intros j' Hj'.
    destruct (Z.eq_dec j' (to_Z j)) as [E|E].
    + subst j'. rewrite of_Z_to_Z, gssQ by lia. rewrite Q2R_1.
      destruct (Z.leb_spec (to_Z A0) (to_Z j)); destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); try lia; reflexivity.
    + rewrite gsoZQ by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
      rewrite P by exact Hj'.
      destruct (Z.leb_spec (to_Z A0) j'); destruct (Z.ltb_spec j' (to_Z j)); destruct (Z.ltb_spec j' (to_Z j + 1));
        try lia; reflexivity.
Qed.

Lemma al2_spec : forall O1 A0 N, (to_Z N <= 4194303)%Z ->
  forall j, (to_Z j < to_Z N)%Z -> (al2 O1 A0 N).[j] = ((j <? A0) && qzerob O1.[j])%bool.
Proof.
  intros O1 A0 N HN. unfold al2.
  pose (Iv := fun jz (a : array bool) => to_Z (PArray.length a) = to_Z N /\
     forall j, (to_Z j < jz)%Z -> a.[j] = ((j <? A0) && qzerob O1.[j])%bool).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (G : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in G; apply G] end.
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded N). lia.
  - rewrite lmakeBo by exact HN. split; [reflexivity|]. intros j Hj. change (to_Z 0) with 0%Z in Hj.
    pose proof (to_Z_bounded j). lia.
  - intros j a Hj [Ha P]. split; [rewrite lsetBo; exact Ha|]. intros j' Hj'.
    destruct (Z.eq_dec (to_Z j') (to_Z j)) as [E|E].
    + apply to_Z_inj in E. subst j'. apply gssBo. lia.
    + rewrite gsoZBo by lia. apply P. lia.
Qed.

Section Correct.
Variables (T0 : array Q) (m E0 A0 : int) (Hp : P1ok T0 m E0 A0).
Local Notation mn := (Z.to_nat (to_Z m)).
Local Notation en := (Z.to_nat (to_Z E0)).
Local Notation w := (E0 + m + 1).
Local Notation N := (E0 + m).
Local Notation t0 := (cell T0 (E0 + m + 1)).
Local Notation A0n := (Z.to_nat (to_Z A0)).
Hypothesis HA0 : (to_Z A0 <= to_Z E0 + to_Z m)%Z.
Variable M : R.
Hypothesis HB : Bounded mn en t0 M.
Hypothesis Hfeas : exists x0, Feas mn en t0 A0n x0.

Let Hm1 := p_m1 _ _ _ _ Hp.
Let Hwb := p_wb _ _ _ _ Hp.
Let Hsz := p_sz _ _ _ _ Hp.
Let U := p_unit _ _ _ _ Hp.

Lemma cart_c1 : forall j, (j < en + mn)%nat -> ovec (cart w A0 N) j = c1 A0n j.
Proof.
  intros j Hj. pose proof (N_val m E0 Hm1 Hwb) as EN. pose proof (w_val m E0 Hm1 Hwb) as Ew.
  destruct (cart_spec w A0 N ltac:(lia) ltac:(lia) ltac:(lia)) as [_ P].
  unfold ovec, c1. rewrite P by lia.
  destruct (Z.leb_spec (to_Z A0) (Z.of_nat j)); destruct (Z.ltb_spec (Z.of_nat j) (to_Z N));
    destruct (Nat.leb_spec A0n j); simpl; try reflexivity; lia.
Qed.

Definition p1st : SState := phase1 T0 m E0 A0 Hp.
Definition d : nat -> R := oo p1st.

Lemma st1_valid : Valid mn en t0 (c1 A0n) (ttab m E0 p1st) d (bb p1st).
Proof.
  destruct (phase1_VS T0 m E0 A0 Hp) as [_ V]. eapply Valid_c_ext; [|exact V]. exact cart_c1.
Qed.

Lemma d_nonneg : forall j, (j < en + mn)%nat -> (0 <= d j)%R.
Proof.
  pose proof (N_val m E0 Hm1 Hwb) as EN.
  destruct (phase1_spec T0 m E0 A0 Hp) as [[W V] [X|(s & Es & Ls)]].
  - intros j Hj. apply (enter_none_math m E0 Hm1 Hwb _ _ X j Hj). apply gmakeBo.
  - exfalso. destruct (enter_some_math m E0 Hm1 Hwb _ _ s Es) as (Hs & _ & Hneg).
    pose proof (leave_none_math m E0 Hm1 Hwb Hsz _ s ltac:(rewrite EN; pose proof (to_Z_bounded s); lia) Ls) as Hle.
    apply (no_ray _ _ _ _ _ _ _ M (Z.to_nat (to_Z s)) HB V Hs Hneg Hle).
Qed.

Lemma d_N : d (en + mn) = 0%R.
Proof.
  destruct Hfeas as [x0 F0]. apply (phase1_zero mn en t0 A0n _ _ _ st1_valid d_nonneg x0 F0).
Qed.

Theorem phase2_min : forall carr,
  to_Z (PArray.length carr) = to_Z w -> Q2R carr.[N] = 0%R ->
  let v := phase2 T0 m E0 A0 Hp p1st (phase1_VS T0 m E0 A0 Hp) (al2 (sO p1st) A0 N) carr in
  (exists x, Feas mn en t0 A0n x /\ sumR (en + mn) (fun j => ovec carr j * x j) = Q2R v)%R /\
  (forall x, Feas mn en t0 A0n x -> Q2R v <= sumR (en + mn) (fun j => ovec carr j * x j))%R.
Proof.
  intros carr Hl Hz. cbv zeta. unfold phase2.
  pose proof (N_val m E0 Hm1 Hwb) as EN. pose proof (w_val m E0 Hm1 Hwb) as Ew.
  destruct (bdec ((PArray.length carr =? E0 + m + 1) && qzerob carr.[E0 + m])) as [Hc|Hc].
  2:{ exfalso. rewrite <- Bool.not_true_iff_false in Hc. apply Hc. apply andb_true_iff. split.
      - apply Uint63.eqb_spec. apply to_Z_inj. exact Hl.
      - apply qzerob_R. exact Hz. }
  set (al := al2 (sO p1st) A0 N).
  set (st2 := mk2 p1st carr w m).
  match goal with |- context [sloop m E0 al st2 ?H] => set (Hacc := H) end.
  assert (Hal : forall j, (j < en + mn)%nat ->
            al.[of_Z (Z.of_nat j)] = ((of_Z (Z.of_nat j) <? A0) && qzerob (sO p1st).[of_Z (Z.of_nat j)])%bool).
  { intros j Hj. apply al2_spec; [lia|]. rewrite to_Z_of_Z_small by (rewrite wB_val; lia). lia. }
  pose (P := fun st => VS m E0 t0 (ovec carr) st /\ forall k, (k < mn)%nat -> d (bb st k) = 0%R).
  assert (G : P (sloop m E0 al st2 Hacc) /\ SExit m E0 al (sloop m E0 al st2 Hacc)).
  { apply sloop_ind.
    - intros st st' [V Hd] R. split; [apply (step_VS m E0 Hm1 Hwb Hsz _ _ _ st st' U V R)|].
      destruct R as (s & r & Es & Er & ->).
      destruct (enter_some_math m E0 Hm1 Hwb _ _ s Es) as (Hs & Hals & _).
      assert (Hs' : (to_Z s < to_Z N)%Z) by (rewrite EN; pose proof (to_Z_bounded s); lia).
      destruct (leave_some_math m E0 Hm1 Hwb Hsz _ r s Hs' Er) as [Hr LO].
      destruct LO as (_ & Ppiv & _).
      assert (Hp0 : cellZ (sT st) w (to_Z r) (to_Z s) <> 0%R).
      { rewrite cell_ii in Ppiv. lra. }
      destruct (pivot_corr m E0 Hm1 Hwb Hsz st r s (proj1 V) Hr Hs' Hp0) as (_ & _ & _ & Eb).
      intros k Hk. rewrite Eb by exact Hk. unfold pb.
      destruct (Nat.eqb k (Z.to_nat (to_Z r))); [|apply Hd; exact Hk].
      unfold al in Hals. rewrite al2_spec in Hals by lia. apply andb_true_iff in Hals.
      destruct Hals as [_ Hq]. apply qzerob_R in Hq. rewrite ovec_get in Hq. exact Hq.
    - split.
      + apply mk2_VS with (A0 := A0) (c := ovec (cart w A0 N)); [exact Hp | apply phase1_VS | exact Hc].
      + intros k Hk. unfold st2, mk2, bb, bvec, sB. simpl. rewrite gcopyI.
        apply (v_ocanon _ _ _ _ _ _ _ st1_valid). exact Hk. }
  destruct G as [[V3 Hd3] X3].
  set (st3 := sloop m E0 al st2 Hacc) in *.
  destruct V3 as [W3 V3].
  assert (Hopt : forall j, (j < en + mn)%nat -> al.[of_Z (Z.of_nat j)] = true -> (0 <= oo st3 j)%R).
  { destruct X3 as [X|(s & Es & Ls)].
    - intros j Hj Ha. apply (enter_none_math m E0 Hm1 Hwb _ _ X j Hj Ha).
    - exfalso. destruct (enter_some_math m E0 Hm1 Hwb _ _ s Es) as (Hs & _ & Hneg).
      pose proof (leave_none_math m E0 Hm1 Hwb Hsz _ s ltac:(rewrite EN; pose proof (to_Z_bounded s); lia) Ls) as Hle.
      apply (no_ray _ _ _ _ _ _ _ M (Z.to_nat (to_Z s)) HB V3 Hs Hneg Hle). }
  destruct (phase2_opt mn en t0 A0n (ttab m E0 p1st) d (bb p1st) (ovec carr) (ttab m E0 st3) (oo st3)
              (bb st3) (fun j => al.[of_Z (Z.of_nat j)])
              st1_valid d_N d_nonneg V3 Hd3) as (F & Eo & Lo).
  - intros j Hj Ha. rewrite Hal in Ha by exact Hj. apply andb_false_iff in Ha. destruct Ha as [Ha|Ha].
    + left. rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec in Ha.
      rewrite to_Z_of_Z_small in Ha by (rewrite wB_val; lia). lia.
    + right. apply qzerob_R_false in Ha. pose proof (d_nonneg j Hj).
      unfold d, oo, ovec in *. lra.
  - exact Hopt.
  - assert (EV : Q2R (Qopp (sO st3).[E0 + m]) = (- oo st3 (en + mn))%R).
    { rewrite Q2R_opp. unfold oo, ovec. f_equal. f_equal. f_equal. apply to_Z_inj.
      rewrite to_Z_of_Z_small by (rewrite wB_val; lia). lia. }
    rewrite EV. split.
    + exists (xb mn en (ttab m E0 st3) (bb st3)). split; [exact F | exact Eo].
    + exact Lo.
Qed.

End Correct.
End P_SV.

(* ================================================================== *)
Section P_RP.
Open Scope uint63_scope.

(* ------------------------------------------------------------------ *)
(* Roads, Floyd-Warshall, routes                                       *)
(* ------------------------------------------------------------------ *)

(* the n x n matrix, one flat row-major table *)
Definition fill2 (n : int) (g : int -> int -> int) (A : array int) : array int :=
  forl 0 n (fun i A => forl 0 n (fun j A => A.[i * n + j <- g i j]) A) A.

Definition flatten (n : int) (x : array (array int)) : array int :=
  fill2 n (fun i j => (x.[i]).[j]) (PArray.make (n * n) 0).

(* a road: a positive length *)
Definition isroad (e : int) : bool := Sint63.ltb 0 e.

Definition INF : int := 1073741824.

Definition fw_cell (n k i j : int) (st : array int * array int) : array int * array int :=
  let D := fst st in let X := snd st in
  let a := D.[i * n + k] + D.[k * n + j] in
  if a <? D.[i * n + j] then (D.[i * n + j <- a], X.[i * n + j <- X.[i * n + k]]) else st.

Definition fw_iter (n k : int) (st : array int * array int) : array int * array int :=
  forl 0 n (fun i st => forl 0 n (fun j st => fw_cell n k i j st) st) st.

(* distances D and successors X: X.[i*n+j] is the city after i on the route to j *)
Definition fw (n : int) (W : array int) : array int * array int :=
  let D0 := fill2 n (fun i j => if i =? j then 0 else if isroad W.[i * n + j] then W.[i * n + j] else INF)
              (PArray.make (n * n) 0) in
  let X0 := fill2 n (fun i j => j) (PArray.make (n * n) 0) in
  forl 0 n (fun k st => fw_iter n k st) (D0, X0).

(* road indices: I.[p] is the index of the road at position p = i*n+j, P.[e] the
   position of road e, and the number of roads *)
Definition scan_roads (n : int) (W : array int) : array int * array int * int :=
  forl 0 (n * n) (fun p st =>
     let I := fst (fst st) in let P := snd (fst st) in let e := snd st in
     if isroad W.[p] then (I.[p <- e], P.[e <- p], e + 1) else st)
    (PArray.make (n * n) 0, PArray.make (n * n) 0, 0).

Lemma walk_dec : forall a b : int, (a <? b) = true -> Zwf 0 (to_Z a) (to_Z b).
Proof.
  intros a b H. apply Uint63.ltb_spec in H. pose proof (to_Z_bounded a). unfold Zwf. lia.
Qed.

(* follow the successors from cur to d, counting the roads used *)
Fixpoint walk (n d E : int) (D X I : array int) (cur : int) (cnt : array int)
    (H : Acc (Zwf 0) (to_Z D.[cur * n + d])) {struct H} : array int :=
  if cur =? d then cnt else
  let v := X.[cur * n + d] in
  match bdec (D.[v * n + d] <? D.[cur * n + d]) with
  | left Hlt =>
      let e := I.[cur * n + v] in
      walk n d E D X I v (if e <? E then cnt.[e <- cnt.[e] + 1] else cnt)
        (Acc_inv H (walk_dec _ _ Hlt))
  | right _ => cnt
  end.

Definition route_cnt (n E : int) (D X I : array int) (s d : int) : array int :=
  walk n d E D X I s (PArray.make E 0) (Zwf_well_founded 0 _).

(* ------------------------------------------------------------------ *)
(* The linear program                                                  *)
(* ------------------------------------------------------------------ *)

(* columns: x_e = (time on road e) - (its length), e < E; the slack y_e of
   x_e <= length, E + e; the artificial variable of delivery k, 2E + k.
   rows: x_e + y_e = length_e (e < E); for delivery k (row E + k)
   sum_e cnt_k(e) x_e + a_k = t_k - D_k, the row negated (but a_k) when the
   right-hand side is negative. *)
Definition bound_rows (E w N : int) (W P : array int) (T : array Q) : array Q :=
  forl 0 E (fun e T =>
     let u := W.[P.[e]] in
     let T := T.[e * w + e <- 1%Q] in
     let T := T.[e * w + (E + e) <- 1%Q] in
     T.[e * w + N <- if isroad u then inject_Z (zofs u) else 0%Q]) T.

Definition deliv_row (n E w N : int) (D X I : array int) (rs rd rt : array int) (k : int)
    (T : array Q) : array Q :=
  let s := rs.[k] in let d := rd.[k] in
  let cnt := route_cnt n E D X I s d in
  let b := (zofi rt.[k] - zofi D.[s * n + d])%Z in
  let i := E + k in
  let T := forl 0 E (fun e T =>
     T.[i * w + e <- inject_Z (if Z.ltb b 0 then (- zofi cnt.[e])%Z else zofi cnt.[e])]) T in
  let T := T.[i * w + (E + E + k) <- 1%Q] in
  T.[i * w + N <- inject_Z (Z.abs b)].

Definition build_T (n E R : int) (W D X I P : array int) (rs rd rt : array int) : array Q :=
  let m := E + R in let w := E + m + 1 in let N := E + m in
  let T := bound_rows E w N W P (PArray.make (m * w) 0%Q) in
  forl 0 R (fun k T => deliv_row n E w N D X I rs rd rt k T) T.

Definition guard (E R : int) : bool :=
  (1 <=? E + R) && (E <=? 2048) && (R <=? 2048) && ((E + R) * (E + (E + R) + 1) <=? 4194303).

(* the cost of a query route: cnt(e) on x_e, nothing elsewhere *)
Definition qcost (E w : int) (cnt : array int) (neg : bool) : array Q :=
  forl 0 E (fun e c => c.[e <- inject_Z (if neg then (- zofi cnt.[e])%Z else zofi cnt.[e])])
    (PArray.make w 0%Q).

(* a non-negative rational below 2^16 as a float within 2^-35 *)
Definition two36 : int := 68719476736.
Definition q2f (q : Q) : float :=
  let mz := ((Qnum q * 68719476736) / Zpos (Qden q))%Z in
  (of_uint63 (iofz mz) / of_uint63 two36)%float.
End P_RP.

(* ================================================================== *)
Section P_BLD.
Open Scope uint63_scope.

Section Build.
Variables (n E RR : int) (W D X I P : array int) (rs rd rt : array int).
Hypothesis Hg : guard E RR = true.

Local Notation m := (E + RR).
Local Notation w := (E + (E + RR) + 1).
Local Notation N := (E + (E + RR)).

Lemma guard_facts : (1 <= to_Z E + to_Z RR /\ to_Z E <= 2048 /\ to_Z RR <= 2048)%Z.
Proof.
  unfold guard in Hg. apply andb_true_iff in Hg as [H1 _]. apply andb_true_iff in H1 as [H1 H3].
  apply andb_true_iff in H1 as [H1 H2].
  rewrite Uint63.leb_spec in H1, H2, H3. change (to_Z 2048) with 2048%Z in *.
  change (to_Z 1) with 1%Z in H1. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR).
  assert (to_Z (E + RR) = to_Z E + to_Z RR)%Z by sia. lia.
Qed.

Lemma m_val : to_Z m = (to_Z E + to_Z RR)%Z.
Proof. pose proof guard_facts. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). sia. Qed.

Lemma w_val' : to_Z w = (2 * to_Z E + to_Z RR + 1)%Z.
Proof. pose proof guard_facts. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). sia. Qed.

Lemma N_val' : to_Z N = (2 * to_Z E + to_Z RR)%Z.
Proof. pose proof guard_facts. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). sia. Qed.

Lemma sz_facts : (to_Z m * to_Z w <= 4194303)%Z.
Proof.
  pose proof Hg as Hg'. unfold guard in Hg'. apply andb_true_iff in Hg' as [_ H]. rewrite Uint63.leb_spec in H.
  change (to_Z 4194303) with 4194303%Z in H. pose proof guard_facts as G.
  pose proof m_val as Em. pose proof w_val' as Ew.
  assert (B : (0 <= (to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1) <= 4096 * 6145)%Z).
  { pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR).
    split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia. }
  assert (E2 : to_Z ((E + RR) * (E + (E + RR) + 1)) = ((to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1))%Z).
  { rewrite mul_spec, Em, Ew. apply Z.mod_small. rewrite wB_val. lia. }
  rewrite Em, Ew. lia.
Qed.

Definition ue (e : Z) : Z := let u := W.[P.[of_Z e]] in if isroad u then zofs u else 0%Z.

Definition boundf (r j : Z) : R :=
  if Z.eqb j r then 1%R else if Z.eqb j (to_Z E + r) then 1%R
  else if Z.eqb j (to_Z N) then IZR (ue r) else 0%R.

Lemma bound_rows_spec :
  let T := bound_rows E w N W P (PArray.make (m * w) 0%Q) in
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z /\
  forall r j, IR w m r j -> cellZ T w r j = if Z.ltb r (to_Z E) then boundf r j else 0%R.
Proof.
  cbv zeta. unfold bound_rows. pose proof guard_facts as G. pose proof sz_facts as S.
  pose proof m_val as Em. pose proof w_val' as Ew. pose proof N_val' as EN.
  pose (Iv := fun ez (T : array Q) => to_Z (PArray.length T) = (to_Z m * to_Z w)%Z /\
     forall r j, IR w m r j -> cellZ T w r j = if Z.ltb r ez then boundf r j else 0%R).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl; exact Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split.
    + rewrite lmakeQ; [lia|]. pose proof (to_Z_bounded (m * w)).
      assert (to_Z (m * w) = to_Z m * to_Z w)%Z by (rewrite mul_spec; apply Z.mod_small; lia). lia.
    + intros r j [Hr Hj]. unfold cellZ. rewrite gmakeQ, Q2R_0. change (to_Z 0) with 0%Z.
      destruct (Z.ltb_spec r 0); [lia | reflexivity].
  - intros e T He [HL Pv]. change (to_Z 0) with 0%Z in He.
    assert (Hm0 : (to_Z 0 < to_Z m)%Z) by (change (to_Z 0) with 0%Z; lia).
    assert (IRe : forall j0 : int, (to_Z j0 < to_Z w)%Z -> IR w m (to_Z e) (to_Z j0)).
    { intros j0 Hj0. pose proof (to_Z_bounded j0). unfold IR. lia. }
    assert (EEe : to_Z (E + e) = (to_Z E + to_Z e)%Z) by (clear -G He; pose proof (to_Z_bounded e); pose proof (to_Z_bounded E); sia).
    cbv zeta.
    split; [rewrite !lsetQ; exact HL|].
    intros r j Hrj.
    rewrite (cellZ_set_IR w m 0 S Hm0); [| rewrite !lsetQ; exact HL | exact Hrj | apply IRe; lia].
    rewrite (cellZ_set_IR w m 0 S Hm0); [| rewrite !lsetQ; exact HL | exact Hrj | apply IRe; lia].
    rewrite (cellZ_set_IR w m 0 S Hm0); [| exact HL | exact Hrj | apply IRe; lia].
    rewrite Pv by exact Hrj. rewrite EEe.
    unfold boundf.
    destruct (Z.eqb_spec r (to_Z e)) as [Er|Er].
    + subst r. destruct (Z.ltb_spec (to_Z e) (to_Z e)); [lia|].
      destruct (Z.ltb_spec (to_Z e) (to_Z e + 1)); [|lia].
      destruct (Z.eqb_spec j (to_Z N)); destruct (Z.eqb_spec j (to_Z E + to_Z e));
        destruct (Z.eqb_spec j (to_Z e)); simpl; try reflexivity; try lia;
        try (rewrite Q2R_1; reflexivity);
        unfold ue; rewrite of_Z_to_Z; destruct (isroad _); [apply Q2R_inject | rewrite Q2R_0; reflexivity].
    + simpl. destruct (Z.ltb_spec r (to_Z e)); destruct (Z.ltb_spec r (to_Z e + 1)); try reflexivity; lia.
Qed.

Definition cntk (k : Z) : array int := route_cnt n E D X I rs.[of_Z k] rd.[of_Z k].
Definition bk (k : Z) : Z := (zofi rt.[of_Z k] - zofi D.[rs.[of_Z k] * n + rd.[of_Z k]])%Z.
Definition delivf (k j : Z) : R :=
  if Z.ltb j (to_Z E) then
    IZR (if Z.ltb (bk k) 0 then (- zofi (cntk k).[of_Z j])%Z else zofi (cntk k).[of_Z j])
  else if Z.eqb j (to_Z E + to_Z E + k) then 1%R
  else if Z.eqb j (to_Z N) then IZR (Z.abs (bk k)) else 0%R.

Definition T0f (r j : Z) : R :=
  if Z.ltb r (to_Z E) then boundf r j else delivf (r - to_Z E) j.

Lemma build_spec :
  let T := build_T n E RR W D X I P rs rd rt in
  to_Z (PArray.length T) = (to_Z m * to_Z w)%Z /\
  forall r j, IR w m r j -> cellZ T w r j = T0f r j.
Proof.
  cbv zeta. unfold build_T. cbv zeta.
  pose proof guard_facts as G. pose proof sz_facts as S.
  pose proof m_val as Em. pose proof w_val' as Ew. pose proof N_val' as EN.
  destruct bound_rows_spec as [HL0 P0].
  set (zm := to_Z (E + RR)) in *. set (zw := to_Z (E + (E + RR) + 1)) in *.
  set (zN := to_Z (E + (E + RR))) in *.
  pose (Iv := fun kz (T : array Q) => to_Z (PArray.length T) = (to_Z m * to_Z w)%Z /\
     forall r j, IR w m r j -> cellZ T w r j =
       if Z.ltb r (to_Z E + kz) then T0f r j else 0%R).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL0|]. intros r j Hrj. rewrite P0 by exact Hrj. change (to_Z 0) with 0%Z.
    rewrite Z.add_0_r. unfold T0f. destruct (Z.ltb r (to_Z E)); reflexivity.
  - intros k T Hk [HL Pv]. change (to_Z 0) with 0%Z in Hk.
    assert (Hm0 : (to_Z 0 < to_Z m)%Z) by (change (to_Z 0) with 0%Z; lia).
    assert (Eik : to_Z (E + k) = (to_Z E + to_Z k)%Z) by (clear -G Hk Em; pose proof (to_Z_bounded k); pose proof (to_Z_bounded E); sia).
    assert (IRi : forall j0 : int, (to_Z j0 < zw)%Z -> IR w m (to_Z (E + k)) (to_Z j0)).
    { intros j0 Hj0. pose proof (to_Z_bounded j0). unfold IR. fold zm zw. rewrite Eik. lia. }
    unfold deliv_row. cbv zeta.
    set (cnt := route_cnt n E D X I rs.[k] rd.[k]).
    set (b := (zofi rt.[k] - zofi D.[rs.[k] * n + rd.[k]])%Z).
    (* the inner loop over the x columns *)
    pose (Jv := fun ez (T' : array Q) => to_Z (PArray.length T') = (to_Z m * to_Z w)%Z /\
       forall r j, IR w m r j -> cellZ T' w r j =
         if (Z.eqb r (to_Z E + to_Z k) && Z.ltb j ez)%bool
         then IZR (if Z.ltb b 0 then (- zofi cnt.[of_Z j])%Z else zofi cnt.[of_Z j])
         else cellZ T w r j).
    match goal with |- context [forl ?lo ?hi ?f ?s0] =>
      assert (Gj : Jv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Jv); unfold Jv | unfold Jv in Gj] end.
    + change (to_Z 0) with 0%Z. lia.
    + split; [exact HL|]. intros r j Hrj. change (to_Z 0) with 0%Z.
      destruct (Z.ltb_spec j 0); [destruct Hrj; lia|]. rewrite andb_false_r. reflexivity.
    + intros e T' He [HL' Pj]. change (to_Z 0) with 0%Z in He. split; [rewrite lsetQ; exact HL'|].
      intros r j Hrj. rewrite (cellZ_set_IR w m 0 S Hm0); [| exact HL' | exact Hrj | apply IRi; clear -He Ew G; lia].
      rewrite Pj by exact Hrj. rewrite Eik.
      destruct (Z.eqb_spec r (to_Z E + to_Z k)); destruct (Z.eqb_spec j (to_Z e)); simpl.
      * subst. rewrite Q2R_inject, of_Z_to_Z. destruct (Z.ltb_spec (to_Z e) (to_Z e + 1)); [reflexivity|lia].
      * destruct (Z.ltb_spec j (to_Z e)); destruct (Z.ltb_spec j (to_Z e + 1)); try reflexivity; lia.
      * reflexivity.
      * reflexivity.
    + destruct Gj as [HLj Pj]. cbv zeta. split; [rewrite !lsetQ; exact HLj|].
      assert (EEk : to_Z (E + E + k) = (to_Z E + to_Z E + to_Z k)%Z) by (clear -G Hk Em; pose proof (to_Z_bounded k); pose proof (to_Z_bounded E); sia).
      intros r j Hrj.
      rewrite (cellZ_set_IR w m 0 S Hm0); [| rewrite lsetQ; exact HLj | exact Hrj | apply IRi; rewrite N_val'; clear -Ew G; lia].
      rewrite (cellZ_set_IR w m 0 S Hm0); [| exact HLj | exact Hrj | apply IRi; rewrite EEk; clear -Ew G Hk Em; lia].
      rewrite Pj by exact Hrj. rewrite Pv by exact Hrj. rewrite Eik, EEk.
      unfold T0f, delivf, bk, cntk.
      destruct (Z.eqb_spec r (to_Z E + to_Z k)) as [Er|Er].
      * subst r. replace (to_Z E + to_Z k - to_Z E)%Z with (to_Z k) by lia. rewrite of_Z_to_Z.
        fold cnt. fold b.
        destruct (Z.ltb_spec (to_Z E + to_Z k) (to_Z E)); [lia|].
        destruct (Z.ltb_spec (to_Z E + to_Z k) (to_Z E + (to_Z k + 1))); [|lia].
        destruct Hrj as [_ Hj]. fold zN. fold zw in Hj. clear Pj Pv P0 HLj HL HL0 IRi.
        destruct (Z.eqb_spec j zN); destruct (Z.eqb_spec j (to_Z E + to_Z E + to_Z k));
          destruct (Z.ltb_spec j zw); destruct (Z.ltb_spec j (to_Z E)); simpl; try lia.
        -- rewrite Q2R_inject. reflexivity.
        -- rewrite Q2R_1. reflexivity.
        -- reflexivity.
        -- destruct (Z.ltb (to_Z E + to_Z k) (to_Z E + to_Z k)); reflexivity.
      * simpl. destruct (Z.ltb_spec r (to_Z E + to_Z k)); destruct (Z.ltb_spec r (to_Z E + (to_Z k + 1)));
          try reflexivity; lia.
  - destruct Gl as [HL P']. split; [exact HL|]. intros r j Hrj. rewrite P' by exact Hrj.
    destruct Hrj as [Hr _]. destruct (Z.ltb_spec r (to_Z E + to_Z RR)); [reflexivity|lia].
Qed.


Lemma binit_spec : forall mm E0 : int, (to_Z mm <= 4194303)%Z -> (to_Z E0 + to_Z mm < wB)%Z ->
  to_Z (PArray.length (binit mm E0)) = to_Z mm /\
  forall k, (0 <= k < to_Z mm)%Z -> to_Z (binit mm E0).[of_Z k] = (to_Z E0 + k)%Z.
Proof.
  intros mm E0 Hm Hw. unfold binit.
  pose (Iv := fun kz (B : array int) => to_Z (PArray.length B) = to_Z mm /\
     forall k, (0 <= k < kz)%Z -> to_Z B.[of_Z k] = (to_Z E0 + k)%Z).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl; exact Gl] end.
  - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded mm). lia.
  - rewrite lmakeI by exact Hm. split; [reflexivity|]. intros k Hk. change (to_Z 0) with 0%Z in Hk. lia.
  - intros k B Hk [HL Pk]. change (to_Z 0) with 0%Z in Hk. split; [rewrite lsetI; exact HL|].
    intros k' Hk'. destruct (Z.eq_dec k' (to_Z k)) as [Ek|Ek].
    + subst k'. rewrite of_Z_to_Z, gssI by lia. rewrite add_spec. apply Z.mod_small.
      pose proof (to_Z_bounded E0). lia.
    + rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val in *; lia); lia). apply Pk. lia.
Qed.

Lemma build_ok : P1ok (build_T n E RR W D X I P rs rd rt) (E + RR) E (E + E).
Proof.
  pose proof guard_facts as G. pose proof sz_facts as S.
  pose proof m_val as Em. pose proof w_val' as Ew. pose proof N_val' as EN.
  destruct build_spec as [HL PT].
  set (T := build_T n E RR W D X I P rs rd rt) in *.
  assert (Hunit : unit0 (Z.to_nat (to_Z (E + RR))) (Z.to_nat (to_Z E)) (cell T (E + (E + RR) + 1))).
  { intros r i Hr Hi. unfold cell. rewrite PT by (unfold IR; lia).
    unfold T0f, boundf, delivf, delta. rewrite Nat2Z.inj_add, !Z2Nat.id by (pose proof (to_Z_bounded E); lia).
    destruct (Z.ltb_spec (Z.of_nat r) (to_Z E)).
    - destruct (Z.eqb_spec (to_Z E + Z.of_nat i) (Z.of_nat r)); [lia|].
      destruct (Z.eqb_spec (to_Z E + Z.of_nat i) (to_Z E + Z.of_nat r));
        destruct (Nat.eqb_spec r i); try lia; [reflexivity|].
      destruct (Z.eqb_spec (to_Z E + Z.of_nat i) (to_Z (E + (E + RR)))); [lia | reflexivity].
    - destruct (Z.ltb_spec (to_Z E + Z.of_nat i) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (to_Z E + Z.of_nat i) (to_Z E + to_Z E + (Z.of_nat r - to_Z E)));
        destruct (Nat.eqb_spec r i); try lia; [reflexivity|].
      destruct (Z.eqb_spec (to_Z E + Z.of_nat i) (to_Z (E + (E + RR)))); [lia | reflexivity]. }
  assert (Hrhs : forall k, (k < Z.to_nat (to_Z (E + RR)))%nat ->
            (0 <= cell T (E + (E + RR) + 1) k (Z.to_nat (to_Z E) + Z.to_nat (to_Z (E + RR))))%R).
  { intros k Hk. unfold cell. rewrite PT by (unfold IR; lia).
    rewrite Nat2Z.inj_add, !Z2Nat.id by (pose proof (to_Z_bounded E); pose proof (to_Z_bounded (E + RR)); lia).
    unfold T0f, boundf, delivf.
    destruct (Z.ltb_spec (Z.of_nat k) (to_Z E)).
    - destruct (Z.eqb_spec (to_Z E + to_Z (E + RR)) (Z.of_nat k)); [lia|].
      destruct (Z.eqb_spec (to_Z E + to_Z (E + RR)) (to_Z E + Z.of_nat k)); [lia|].
      destruct (Z.eqb_spec (to_Z E + to_Z (E + RR)) (to_Z (E + (E + RR)))); [|lia].
      apply IZR_le. unfold ue. destruct (isroad _) eqn:Er; [|lia].
      unfold isroad in Er. apply Sint63.ltb_spec in Er. rewrite zofs_spec.
      change (Sint63.to_Z 0) with 0%Z in Er. apply Z.compare_lt_iff in Er. exact (Z.lt_le_incl _ _ Er).
    - destruct (Z.ltb_spec (to_Z E + to_Z (E + RR)) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (to_Z E + to_Z (E + RR)) (to_Z E + to_Z E + (Z.of_nat k - to_Z E))); [lia|].
      destruct (Z.eqb_spec (to_Z E + to_Z (E + RR)) (to_Z (E + (E + RR)))); [|lia].
      apply IZR_le. lia. }
  assert (HA : (to_Z (E + E) <= to_Z (E + (E + RR)))%Z).
  { assert (to_Z (E + E) = 2 * to_Z E)%Z by (pose proof (to_Z_bounded E); clear - G; sia). lia. }
  destruct (cart_spec (E + (E + RR) + 1) (E + E) (E + (E + RR)) HA ltac:(lia) ltac:(lia)) as [Hc Pc].
  destruct (binit_spec (E + RR) E ltac:(lia) ltac:(rewrite wB_val; lia)) as [HB PB].
  assert (S2 : (to_Z (E + RR) * (to_Z E + to_Z (E + RR) + 1) <= 4194303)%Z).
  { replace (to_Z E + to_Z (E + RR) + 1)%Z with (to_Z (E + (E + RR) + 1)) by lia. exact S. }
  constructor.
  - lia.
  - lia.
  - exact S2.
  - exact Hunit.
  - unfold st0. apply init_VS.
    + lia.
    + lia.
    + exact S2.
    + exact HL.
    + exact HB.
    + intros k Hk. apply PB. lia.
    + exact Hunit.
    + exact Hrhs.
    + exact Hc.
    + pose proof (Pc (to_Z (E + (E + RR))) ltac:(lia)) as Pn. rewrite of_Z_to_Z in Pn. rewrite Pn.
      destruct (Z.ltb_spec (to_Z (E + (E + RR))) (to_Z (E + (E + RR)))); [lia|].
      rewrite andb_false_r. reflexivity.
Qed.

End Build.
End P_BLD.

(* ================================================================== *)
Section P_G.
Import ListNotations.
Open Scope N_scope.

Section G.
Variable dist : list (list Z).

Lemma distance_cons2 : forall a b l, distance dist (a :: b :: l) = (entry dist a b + distance dist (b :: l))%Z.
Proof. reflexivity. Qed.

Lemma route_head : forall s d p, route dist s d p -> exists tl, p = s :: tl.
Proof. intros s d p H. destruct H; eexists; reflexivity. Qed.

Lemma route_cities : forall s d p, route dist s d p -> forall x, In x p -> x < len dist.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; intros x Hx.
  - destruct Hx as [<-|[]]. exact Hs.
  - destruct Hx as [<-|Hx]; [apply Hr | apply IH; exact Hx].
Qed.

Lemma route_ends : forall s d p, route dist s d p -> s < len dist /\ d < len dist.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; [auto|].
  split; [apply Hr | apply IH].
Qed.

Lemma route_join : forall s m p1, route dist s m p1 -> forall d p2, route dist m d p2 ->
  route dist s d (p1 ++ tl p2) /\
  distance dist (p1 ++ tl p2) = (distance dist p1 + distance dist p2)%Z.
Proof.
  intros s m p1 H. induction H as [s Hs | s m' m p Hr Hp IH]; intros d p2 H2.
  - destruct (route_head _ _ _ H2) as [tl E]. subst p2. simpl. split; [exact H2|]. lia.
  - destruct (IH d p2 H2) as [R E]. split.
    + simpl. apply route_step with m'; assumption.
    + destruct (route_head _ _ _ Hp) as [tl Et]. subst p. simpl app.
      rewrite !distance_cons2. simpl app in E. rewrite E. lia.
Qed.

Lemma route_split : forall l1 s d v l2, route dist s d (l1 ++ v :: l2) ->
  route dist s v (l1 ++ [v]) /\ route dist v d (v :: l2) /\
  distance dist (l1 ++ v :: l2) = (distance dist (l1 ++ [v]) + distance dist (v :: l2))%Z.
Proof.
  induction l1 as [|x l1 IH]; intros s d v l2 H.
  - simpl in *. destruct (route_head _ _ _ H) as [tl E]. inversion E. subst.
    split; [apply route_here; apply (route_ends _ _ _ H)|]. split; [exact H|]. simpl. lia.
  - simpl in H. inversion H as [s' Hs' Es | s' m d' p Hr Hp Es Ed Ep]; subst.
    + destruct l1; discriminate.
    + destruct (IH m d v l2 Hp) as (R1 & R2 & E). split; [|split; [exact R2|]].
      * simpl. apply route_step with m; assumption.
      * destruct (route_head _ _ _ Hp) as [tl Et]. simpl app. rewrite Et.
        destruct (route_head _ _ _ R1) as [tl' Et']. rewrite Et'.
        rewrite !distance_cons2. rewrite <- Et, <- Et'. rewrite E. lia.
Qed.

Lemma distance_nonneg : forall s d p, route dist s d p -> (0 <= distance dist p)%Z.
Proof.
  intros s d p H. induction H as [s Hs | s m d p Hr Hp IH]; [simpl; lia|].
  destruct (route_head _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
  destruct Hr as (_ & _ & Hr). lia.
Qed.

Lemma distance_pos : forall s d x l, route dist s d (s :: x :: l) -> (0 < distance dist (s :: x :: l))%Z.
Proof.
  intros s d x l H. inversion H; subst. rewrite distance_cons2.
  destruct (route_head _ _ _ H4) as [tl Et]. inversion Et; subst.
  pose proof (distance_nonneg _ _ _ H4). destruct H1 as (_ & _ & H1). lia.
Qed.

Lemma shortest_nodup : forall s d p, shortest_route dist s d p -> NoDup p.
Proof.
  intros s d p [Hr Hmin].
  assert (Dec : decidable_eq N) by (intros x y; unfold decidable; destruct (N.eq_dec x y); tauto).
  destruct (NoDup_decidable Dec p) as [ND|ND]; [exact ND|]. exfalso.
  destruct (not_NoDup Dec ND) as (v & l1 & l2 & l3 & ->).
  destruct (route_split l1 s d v (l2 ++ v :: l3) Hr) as (R1 & R2 & E1).
  destruct (route_split (v :: l2) v d v l3 R2) as (R3 & R4 & E2).
  destruct (route_join s v (l1 ++ [v]) R1 d (v :: l3) R4) as [R5 E3].
  simpl tl in R5, E3.
  assert (Ej : (l1 ++ [v]) ++ l3 = l1 ++ v :: l3) by (rewrite <- app_assoc; reflexivity).
  rewrite Ej in R5, E3.
  pose proof (Hmin _ R5) as L.
  assert (P : (0 < distance dist (v :: l2 ++ [v]))%Z).
  { destruct (l2 ++ [v]) as [|x l] eqn:El; [destruct l2; discriminate|].
    apply (distance_pos v v x l). simpl in R3. rewrite El in R3. exact R3. }
  simpl app in E2. rewrite E1, E2 in L. rewrite E3 in L. lia.
Qed.

Lemma nodup_length : forall (p : list N) n, NoDup p -> (forall x, In x p -> x < n) ->
  (List.length p <= N.to_nat n)%nat.
Proof using.
  intros p n ND H.
  rewrite <- (length_seq (N.to_nat n) 0), <- (length_map N.of_nat (seq 0 (N.to_nat n))).
  apply NoDup_incl_length; [exact ND|]. intros x Hx. apply in_map_iff.
  exists (N.to_nat x). split; [apply N2Nat.id|]. apply in_seq. pose proof (H x Hx). lia.
Qed.

Lemma distance_bound : forall B s d p, (forall i j, road dist i j -> (entry dist i j <= B)%Z) ->
  (0 <= B)%Z -> route dist s d p -> (distance dist p <= B * (Z.of_nat (List.length p) - 1))%Z.
Proof.
  intros B s d p HB HB0 H. induction H as [s Hs | s m d p Hr Hp IH]; [simpl; lia|].
  destruct (route_head _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
  pose proof (HB _ _ Hr). simpl length in *. lia.
Qed.

End G.
End P_G.

(* ================================================================== *)
Section P_FWM.
Import ListNotations.
Open Scope N_scope.

(* Floyd-Warshall on functions: the k-th relaxation and its invariant *)

Section FWM.
Variable dist : list (list Z).
Local Notation nn := (len dist).
Variable INF : Z.

Definition FD (D : N -> N -> Z) (k a b : N) : Z :=
  if (D a k + D k b <? D a b)%Z then (D a k + D k b)%Z else D a b.
Definition FX (D : N -> N -> Z) (X : N -> N -> N) (k a b : N) : N :=
  if (D a k + D k b <? D a b)%Z then X a k else X a b.

Record Inv (k : N) (D : N -> N -> Z) (X : N -> N -> N) : Prop := {
  i_bnd : forall a b, a < nn -> b < nn -> (0 <= D a b <= INF)%Z;
  i_diag : forall a, a < nn -> D a a = 0%Z;
  i_road : forall a b, road dist a b -> (D a b <= entry dist a b)%Z;
  i_succ : forall a b, a < nn -> b < nn -> a <> b -> (D a b < INF)%Z ->
     road dist a (X a b) /\ (entry dist a (X a b) + D (X a b) b <= D a b)%Z;
  i_tri : forall c a b, c < k -> a < nn -> b < nn -> (D a b <= D a c + D c b)%Z
}.

Lemma FD_kk : forall D k a, (0 <= D k k)%Z -> D k k = 0%Z -> FD D k a k = D a k.
Proof using. intros D k a H0 H. unfold FD. rewrite H. destruct (Z.ltb_spec (D a k + 0) (D a k)); lia. Qed.

Lemma FD_kb : forall D k b, D k k = 0%Z -> FD D k k b = D k b.
Proof using. intros D k b H. unfold FD. rewrite H. destruct (Z.ltb_spec (0 + D k b) (D k b)); lia. Qed.

Lemma FD_le : forall D k a b, (FD D k a b <= D a b)%Z.
Proof using. intros. unfold FD. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia. Qed.

Lemma FD_le2 : forall D k a b, (FD D k a b <= D a k + D k b)%Z.
Proof using. intros. unfold FD. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia. Qed.

Lemma inv_step : forall k D X, k < nn -> Inv k D X -> Inv (k + 1) (FD D k) (FX D X k).
Proof.
  intros k D X Hk [Hb Hd Hr Hs Ht].
  assert (Hkk : D k k = 0%Z) by (apply Hd; exact Hk).
  constructor.
  - intros a b Ha Hb'. pose proof (FD_le D k a b). pose proof (Hb a b Ha Hb').
    pose proof (Hb a k Ha Hk). pose proof (Hb k b Hk Hb').
    unfold FD in *. destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia.
  - intros a Ha. pose proof (Hb a k Ha Hk). pose proof (Hb k a Hk Ha).
    unfold FD. rewrite (Hd a Ha). destruct (Z.ltb_spec (D a k + D k a) 0); lia.
  - intros a b R. pose proof (FD_le D k a b). pose proof (Hr a b R). lia.
  - intros a b Ha Hb' Nab Hlt. unfold FX.
    destruct (Z.ltb_spec (D a k + D k b) (D a b)) as [L|L].
    + assert (Nak : a <> k) by (intros ->; lia).
      pose proof (Hb k b Hk Hb').
      assert (FDe : FD D k a b = (D a k + D k b)%Z) by (unfold FD; destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia).
      destruct (Hs a k Ha Hk Nak ltac:(lia)) as [R E].
      split; [exact R|]. rewrite FDe. pose proof (FD_le2 D k (X a k) b). lia.
    + assert (FDe : FD D k a b = D a b) by (unfold FD; destruct (Z.ltb_spec (D a k + D k b) (D a b)); lia).
      rewrite FDe in Hlt. destruct (Hs a b Ha Hb' Nab Hlt) as [R E].
      split; [exact R|]. rewrite FDe. pose proof (FD_le D k (X a b) b). lia.
  - intros c a b Hc Ha Hb'.
    assert (Hc' : c < nn) by lia.
    destruct (N.eq_dec c k) as [->|Nck].
    + rewrite FD_kk by (try apply Hb; auto; lia). rewrite FD_kb by exact Hkk. apply FD_le2.
    + assert (Hc2 : c < k) by lia.
      pose proof (Ht c a b Hc2 Ha Hb'). pose proof (Ht c k b Hc2 Hk Hb'). pose proof (Ht c a k Hc2 Ha Hk).
      pose proof (Hb a c Ha Hc'). pose proof (Hb c b Hc' Hb'). pose proof (Hb a k Ha Hk).
      pose proof (Hb k b Hk Hb'). pose proof (Hb k c Hk Hc'). pose proof (Hb c k Hc' Hk).
      pose proof (FD_le D k a b). pose proof (FD_le2 D k a b).
      unfold FD at 2 3.
      destruct (Z.ltb_spec (D a k + D k c) (D a c)); destruct (Z.ltb_spec (D c k + D k b) (D c b)); lia.
Qed.

Lemma inv_route : forall D X, Inv nn D X -> forall s d p, route dist s d p -> (D s d <= distance dist p)%Z.
Proof.
  intros D X I s d p H. induction H as [s Hs | s m d p R Hp IH].
  - rewrite (i_diag _ _ _ I s Hs). simpl. lia.
  - destruct (route_head dist _ _ _ Hp) as [tl Et]. subst p. rewrite distance_cons2.
    pose proof (i_road _ _ _ I s m R). destruct R as (Hs & Hm & _).
    pose proof (route_ends dist _ _ _ Hp) as [_ Hd].
    pose proof (i_tri _ _ _ I m s d Hm Hs Hd). lia.
Qed.

End FWM.
End P_FWM.

(* ================================================================== *)
Section P_FWP.
Open Scope uint63_scope.

Section FWP.
Variable n : int.
Hypothesis Hn : (to_Z n <= 2000)%Z.

Definition dN (A : array int) (a b : N) : Z := to_Z A.[of_Z (Z.of_N a * to_Z n + Z.of_N b)].
Definition xN (A : array int) (a b : N) : N := Z.to_N (dN A a b).
Definition toN (i : int) : N := Z.to_N (to_Z i).

Lemma nn_bound : (to_Z n * to_Z n <= 4000000)%Z.
Proof. pose proof (to_Z_bounded n). nia. Qed.

Lemma idx_val : forall a b : int, (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  to_Z (a * n + b) = (to_Z a * to_Z n + to_Z b)%Z.
Proof.
  intros a b Ha Hb. pose proof nn_bound. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b).
  pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite add_spec, mul_spec. rewrite (Z.mod_small (to_Z a * to_Z n)) by (rewrite wB_val; lia).
  apply Z.mod_small. rewrite wB_val. nia.
Qed.

Lemma get_idx : forall (A : array int) (a b : int), (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z ->
  A.[a * n + b] = A.[of_Z (Z.of_N (toN a) * to_Z n + Z.of_N (toN b))].
Proof.
  intros A a b Ha Hb. f_equal. apply to_Z_inj. rewrite idx_val by assumption.
  unfold toN. rewrite !Z2N.id by (pose proof (to_Z_bounded a); pose proof (to_Z_bounded b); lia).
  rewrite to_Z_of_Z_small; [reflexivity|]. pose proof nn_bound. pose proof (to_Z_bounded a).
  pose proof (to_Z_bounded b). pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
  rewrite wB_val. lia.
Qed.

Lemma ofZN : forall a : N, (Z.of_N a < to_Z n)%Z -> toN (of_Z (Z.of_N a)) = a.
Proof.
  intros a Ha. unfold toN. rewrite to_Z_of_Z_small by (pose proof (to_Z_bounded n); lia). lia.
Qed.

Lemma dN_set : forall (A : array int) (a b : int) v (a' b' : N),
  to_Z (PArray.length A) = (to_Z n * to_Z n)%Z ->
  (to_Z a < to_Z n)%Z -> (to_Z b < to_Z n)%Z -> (Z.of_N a' < to_Z n)%Z -> (Z.of_N b' < to_Z n)%Z ->
  dN (A.[a * n + b <- v]) a' b' = if (N.eqb a' (toN a) && N.eqb b' (toN b))%bool then to_Z v else dN A a' b'.
Proof.
  intros A a b v a' b' HL Ha Hb Ha' Hb'. unfold dN.
  pose proof nn_bound. pose proof (to_Z_bounded a). pose proof (to_Z_bounded b). pose proof (to_Z_bounded n).
  assert (to_Z a * to_Z n <= to_Z n * to_Z n - to_Z n)%Z by nia.
  assert (Z.of_N a' * to_Z n <= to_Z n * to_Z n - to_Z n)%Z by nia.
  destruct (N.eqb_spec a' (toN a)); destruct (N.eqb_spec b' (toN b)); simpl.
  - subst. rewrite <- get_idx by assumption. rewrite gssI; [reflexivity|]. rewrite idx_val by assumption. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
  - rewrite gsoZI; [reflexivity|]. rewrite idx_val, to_Z_of_Z_small by (try assumption; rewrite wB_val; lia).
    intros E. apply idx_inj in E; [|lia|lia]. unfold toN in *. lia.
Qed.

Lemma fill2_spec : forall g (A : array int), to_Z (PArray.length A) = (to_Z n * to_Z n)%Z ->
  to_Z (PArray.length (fill2 n g A)) = (to_Z n * to_Z n)%Z /\
  forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
    dN (fill2 n g A) a b = to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))).
Proof.
  intros g A HL. unfold fill2. pose proof (to_Z_bounded n).
  pose (Iv := fun iz (A' : array int) => to_Z (PArray.length A') = (to_Z n * to_Z n)%Z /\
     forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
       dN A' a b = if Z.ltb (Z.of_N a) iz then to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))) else dN A a b).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HL|]. intros a b Ha Hb. change (to_Z 0) with 0%Z. destruct (Z.ltb_spec (Z.of_N a) 0); [lia|reflexivity].
  - intros i A1 Hi [HL1 P1]. change (to_Z 0) with 0%Z in Hi.
    pose (Jv := fun jz (A' : array int) => to_Z (PArray.length A') = (to_Z n * to_Z n)%Z /\
       forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
         dN A' a b = if (Z.ltb (Z.of_N a) (to_Z i) || (Z.eqb (Z.of_N a) (to_Z i) && Z.ltb (Z.of_N b) jz))%bool
                     then to_Z (g (of_Z (Z.of_N a)) (of_Z (Z.of_N b))) else dN A a b).
    match goal with |- context [forl ?lo ?hi ?f ?s0] =>
      assert (Gj : Jv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Jv); unfold Jv | unfold Jv in Gj] end.
    + change (to_Z 0) with 0%Z. lia.
    + split; [exact HL1|]. intros a b Ha Hb. rewrite P1 by assumption. change (to_Z 0) with 0%Z.
      destruct (Z.ltb_spec (Z.of_N b) 0); [lia|]. rewrite andb_false_r, orb_false_r. reflexivity.
    + intros j A2 Hj [HL2 P2]. change (to_Z 0) with 0%Z in Hj. split; [rewrite lsetI; exact HL2|].
      intros a b Ha Hb. rewrite dN_set by (try assumption; lia). rewrite P2 by assumption.
      unfold toN.
      destruct (N.eqb_spec a (Z.to_N (to_Z i))); destruct (N.eqb_spec b (Z.to_N (to_Z j))); simpl.
      * subst. rewrite !Z2N.id by lia. rewrite !of_Z_to_Z.
        destruct (Z.ltb_spec (to_Z i) (to_Z i)); [lia|]. rewrite Z.eqb_refl.
        destruct (Z.ltb_spec (to_Z j) (to_Z j + 1)); [reflexivity|lia].
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [|reflexivity]. simpl.
        destruct (Z.ltb_spec (Z.of_N b) (to_Z j)); destruct (Z.ltb_spec (Z.of_N b) (to_Z j + 1)); try reflexivity; lia.
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [lia|reflexivity].
      * destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); [reflexivity|]. simpl.
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); [lia|reflexivity].
    + destruct Gj as [HL2 P2]. split; [exact HL2|]. intros a b Ha Hb. rewrite P2 by assumption.
      destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N a) (to_Z i + 1)); simpl;
        try lia; try reflexivity;
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); simpl; try lia;
        destruct (Z.ltb_spec (Z.of_N b) (to_Z n)); try reflexivity; lia.
  - destruct Gl as [HL1 P1]. split; [exact HL1|]. intros a b Ha Hb. rewrite P1 by assumption.
    destruct (Z.ltb_spec (Z.of_N a) (to_Z n)); [reflexivity|lia].
Qed.


Lemma INF_val : to_Z INF = 1073741824%Z.
Proof. reflexivity. Qed.

Definition LenOK (A : array int) : Prop := to_Z (PArray.length A) = (to_Z n * to_Z n)%Z.

Section Iter.
Variables (k : int) (D X : array int).
Hypothesis Hk : (to_Z k < to_Z n)%Z.
Hypothesis HD : LenOK D.
Hypothesis HX : LenOK X.
Hypothesis Hb : forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
  (0 <= dN D a b <= to_Z INF)%Z.
Hypothesis Hkk : dN D (toN k) (toN k) = 0%Z.

Local Notation kN := (toN k).
Local Notation FDk := (FD (dN D) kN).
Local Notation FXk := (FX (dN D) (xN X) kN).

Definition Ist (P : N -> N -> bool) (st : array int * array int) : Prop :=
  LenOK (fst st) /\ LenOK (snd st) /\
  forall a b : N, (Z.of_N a < to_Z n)%Z -> (Z.of_N b < to_Z n)%Z ->
    dN (fst st) a b = (if P a b then FDk a b else dN D a b) /\
    xN (snd st) a b = (if P a b then FXk a b else xN X a b).

Lemma kN_lt : (Z.of_N kN < to_Z n)%Z.
Proof. unfold toN. pose proof (to_Z_bounded k). lia. Qed.

Lemma FD_ik : forall a, (Z.of_N a < to_Z n)%Z -> FDk a kN = dN D a kN.
Proof. intros a Ha. apply FD_kk; [rewrite Hkk; lia | exact Hkk]. Qed.

Lemma FX_ik : forall a, (Z.of_N a < to_Z n)%Z -> FXk a kN = xN X a kN.
Proof.
  intros a Ha. unfold FX. rewrite Hkk.
  destruct (Z.ltb_spec (dN D a kN + 0) (dN D a kN)); [lia | reflexivity].
Qed.

Lemma FD_kj : forall b, FDk kN b = dN D kN b.
Proof. intros b. apply FD_kb. exact Hkk. Qed.

Lemma fw_cell_spec : forall (i j : int) st (P : N -> N -> bool),
  (to_Z i < to_Z n)%Z -> (to_Z j < to_Z n)%Z ->
  Ist P st -> P (toN i) (toN j) = false ->
  Ist (fun a b => P a b || (N.eqb a (toN i) && N.eqb b (toN j)))%bool (fw_cell n k i j st).
Proof.
  intros i j [D' X'] P Hi Hj (HD' & HX' & HP) Pij. simpl in HD', HX', HP.
  pose proof kN_lt as HkN.
  assert (HiN : (Z.of_N (toN i) < to_Z n)%Z) by (unfold toN; pose proof (to_Z_bounded i); lia).
  assert (HjN : (Z.of_N (toN j) < to_Z n)%Z) by (unfold toN; pose proof (to_Z_bounded j); lia).
  assert (Eik : to_Z D'.[i * n + k] = dN D (toN i) kN).
  { rewrite get_idx by assumption. fold (dN D' (toN i) kN). destruct (HP _ _ HiN HkN) as [E1 _].
    rewrite E1. destruct (P (toN i) kN); [apply FD_ik; exact HiN | reflexivity]. }
  assert (Ekj : to_Z D'.[k * n + j] = dN D kN (toN j)).
  { rewrite get_idx by assumption. fold (dN D' kN (toN j)). destruct (HP _ _ HkN HjN) as [E1 _].
    rewrite E1. destruct (P kN (toN j)); [apply FD_kj | reflexivity]. }
  assert (Eij : to_Z D'.[i * n + j] = dN D (toN i) (toN j)).
  { rewrite get_idx by assumption. fold (dN D' (toN i) (toN j)). destruct (HP _ _ HiN HjN) as [E1 _].
    rewrite E1, Pij. reflexivity. }
  assert (Xik : Z.to_N (to_Z X'.[i * n + k]) = xN X (toN i) kN).
  { rewrite get_idx by assumption. fold (dN X' (toN i) kN). fold (xN X' (toN i) kN).
    destruct (HP _ _ HiN HkN) as [_ E1]. rewrite E1. destruct (P (toN i) kN); [apply FX_ik; exact HiN | reflexivity]. }
  pose proof (Hb _ _ HiN HkN). pose proof (Hb _ _ HkN HjN). rewrite INF_val in *.
  assert (Esum : to_Z (D'.[i * n + k] + D'.[k * n + j]) = (dN D (toN i) kN + dN D kN (toN j))%Z).
  { rewrite add_spec, Eik, Ekj. apply Z.mod_small. rewrite wB_val. lia. }
  unfold fw_cell, Ist. simpl fst. simpl snd.
  destruct (D'.[i * n + k] + D'.[k * n + j] <? D'.[i * n + j]) eqn:L.
  - apply Uint63.ltb_spec in L. rewrite Esum, Eij in L. cbn [fst snd].
    split; [unfold LenOK; rewrite lsetI; exact HD'|]. split; [unfold LenOK; rewrite lsetI; exact HX'|].
    intros a b Ha Hb'. simpl. unfold xN. rewrite !dN_set by (try assumption; try lia).
    destruct (HP a b Ha Hb') as [E1 E2]. unfold xN in E2.
    destruct (N.eqb_spec a (toN i)); destruct (N.eqb_spec b (toN j)); simpl; rewrite ?orb_true_r, ?orb_false_r.
    + subst. unfold FD, FX. destruct (Z.ltb_spec (dN D (toN i) kN + dN D kN (toN j)) (dN D (toN i) (toN j))); [|lia].
      split; [exact Esum | exact Xik].
    + exact (conj E1 E2).
    + exact (conj E1 E2).
    + exact (conj E1 E2).
  - apply Bool.not_true_iff_false in L. rewrite Uint63.ltb_spec, Esum, Eij in L. cbn [fst snd].
    split; [exact HD'|]. split; [exact HX'|].
    intros a b Ha Hb'. destruct (HP a b Ha Hb') as [E1 E2]. simpl.
    destruct (N.eqb_spec a (toN i)); destruct (N.eqb_spec b (toN j)); simpl; rewrite ?orb_true_r, ?orb_false_r;
      try exact (conj E1 E2).
    subst. rewrite Pij in E1, E2. unfold FD, FX.
    destruct (Z.ltb_spec (dN D (toN i) kN + dN D kN (toN j)) (dN D (toN i) (toN j))); [lia|].
    exact (conj E1 E2).
Qed.

Lemma fw_iter_spec :
  Ist (fun _ _ => true) (fw_iter n k (D, X)).
Proof.
  unfold fw_iter. pose proof (to_Z_bounded n).
  pose (Iv := fun iz st => Ist (fun a _ => Z.ltb (Z.of_N a) iz) st).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HD|]. split; [exact HX|]. intros a b _ _. change (to_Z 0) with 0%Z.
    destruct (Z.ltb_spec (Z.of_N a) 0); [lia|]. split; reflexivity.
  - intros i st Hi Pi. change (to_Z 0) with 0%Z in Hi.
    pose (Jv := fun jz st => Ist (fun a b => Z.ltb (Z.of_N a) (to_Z i) ||
                  (Z.eqb (Z.of_N a) (to_Z i) && Z.ltb (Z.of_N b) jz))%bool st).
    match goal with |- context [forl ?lo ?hi ?f ?s0] =>
      assert (Gj : Jv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Jv); unfold Jv | unfold Jv in Gj] end.
    + change (to_Z 0) with 0%Z. lia.
    + destruct Pi as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
      intros a b Ha Hb'. change (to_Z 0) with 0%Z. destruct (Z.ltb_spec (Z.of_N b) 0); [lia|].
      rewrite andb_false_r, orb_false_r. apply P3; assumption.
    + intros j st' Hj Pj. change (to_Z 0) with 0%Z in Hj.
      assert (Q := fw_cell_spec i j st' _ ltac:(lia) ltac:(lia) Pj).
      destruct Q as (Q1 & Q2 & Q3).
      * unfold toN. rewrite !Z2N.id by lia. destruct (Z.ltb_spec (to_Z i) (to_Z i)); [lia|].
        rewrite Z.eqb_refl. destruct (Z.ltb_spec (to_Z j) (to_Z j)); [lia|]. reflexivity.
      * split; [exact Q1|]. split; [exact Q2|]. intros a b Ha Hb'. rewrite (proj1 (Q3 a b Ha Hb')), (proj2 (Q3 a b Ha Hb')).
        unfold toN. replace (
          ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z j))) ||
          (N.eqb a (Z.to_N (to_Z i))) && (N.eqb b (Z.to_N (to_Z j))))%bool with
          ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z j + 1)))%bool;
          [split; reflexivity|].
        destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); simpl; [reflexivity|].
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); simpl.
        -- destruct (N.eqb_spec a (Z.to_N (to_Z i))); [|lia]. simpl.
           destruct (Z.ltb_spec (Z.of_N b) (to_Z j)); destruct (Z.ltb_spec (Z.of_N b) (to_Z j + 1));
             destruct (N.eqb_spec b (Z.to_N (to_Z j))); simpl; try reflexivity; lia.
        -- destruct (N.eqb_spec a (Z.to_N (to_Z i))); [lia|]. reflexivity.
    + destruct Gj as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
      intros a b Ha Hb'. rewrite (proj1 (P3 a b Ha Hb')), (proj2 (P3 a b Ha Hb')).
      replace ((Z.ltb (Z.of_N a) (to_Z i)) || (Z.eqb (Z.of_N a) (to_Z i)) && (Z.ltb (Z.of_N b) (to_Z n)))%bool
        with (Z.ltb (Z.of_N a) (to_Z i + 1)); [split; reflexivity|].
      destruct (Z.ltb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N a) (to_Z i + 1));
        destruct (Z.eqb_spec (Z.of_N a) (to_Z i)); destruct (Z.ltb_spec (Z.of_N b) (to_Z n)); simpl;
        try reflexivity; lia.
  - destruct Gl as (P1 & P2 & P3). split; [exact P1|]. split; [exact P2|].
    intros a b Ha Hb'. rewrite (proj1 (P3 a b Ha Hb')), (proj2 (P3 a b Ha Hb')).
    destruct (Z.ltb_spec (Z.of_N a) (to_Z n)); [split; reflexivity | lia].
Qed.

End Iter.

End FWP.
End P_FWP.

(* ================================================================== *)
Section P_FWQ.
Open Scope uint63_scope.

Lemma Inv_ext : forall dist INF k D X D' X', (k <= len dist)%N ->
  (forall a b, a < len dist -> b < len dist -> D' a b = D a b /\ X' a b = X a b)%N ->
  Inv dist INF k D X -> Inv dist INF k D' X'.
Proof.
  intros dist INF k D X D' X' Hk E [Hb Hd Hr Hs Ht]. constructor.
  - intros a b Ha Hb'. rewrite (proj1 (E a b Ha Hb')). apply Hb; assumption.
  - intros a Ha. rewrite (proj1 (E a a Ha Ha)). apply Hd; assumption.
  - intros a b R. pose proof R as (Ha & Hb' & _). rewrite (proj1 (E a b Ha Hb')). apply Hr; assumption.
  - intros a b Ha Hb' Nab Hlt. rewrite (proj1 (E a b Ha Hb')) in *. rewrite (proj2 (E a b Ha Hb')).
    destruct (Hs a b Ha Hb' Nab Hlt) as [R L]. split; [exact R|].
    pose proof R as (_ & Hx & _). rewrite (proj1 (E _ b Hx Hb')). exact L.
  - intros c a b Hc Ha Hb'. assert (Hc' : (c < len dist)%N) by lia.
    rewrite (proj1 (E a b Ha Hb')), (proj1 (E a c Ha Hc')), (proj1 (E c b Hc' Hb')). apply Ht; assumption.
Qed.

Section FWQ.
Variable dist : list (list Z).
Variables (n : int) (W : array int).
Hypothesis Hn : to_Z n = Z.of_N (len dist).
Hypothesis Hn2 : (to_Z n <= 2000)%Z.
Hypothesis HWl : LenOK n W.
Hypothesis HW : forall a b, (a < len dist)%N -> (b < len dist)%N ->
  Sint63.to_Z W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = entry dist a b.
Hypothesis Hdiag : forall a, (a < len dist)%N -> entry dist a a = 0%Z.
Hypothesis Hrange : forall a b, (a < len dist)%N -> (b < len dist)%N -> a <> b ->
  entry dist a b = (-1)%Z \/ (1 <= entry dist a b <= 1000)%Z.

Lemma ltn : forall a, (a < len dist)%N -> (Z.of_N a < to_Z n)%Z.
Proof. intros a Ha. rewrite Hn. lia. Qed.

Lemma sint_pos : forall x : int, (0 < Sint63.to_Z x)%Z -> to_Z x = Sint63.to_Z x.
Proof.
  intros x H. rewrite <- zofs_spec in *. unfold zofs in *. rewrite zofi_spec in *.
  destruct (x <? 4611686018427387904) eqn:E; [reflexivity|].
  pose proof (to_Z_bounded x). lia.
Qed.

Lemma isroad_iff : forall a b, (a < len dist)%N -> (b < len dist)%N ->
  isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = true <-> road dist a b.
Proof.
  intros a b Ha Hb. unfold isroad, road. rewrite Sint63.ltb_spec, HW by assumption.
  change (Sint63.to_Z 0) with 0%Z. split; [intros H; auto | intros (_ & _ & H); exact H].
Qed.

Lemma fw_spec : LenOK n (fst (fw n W)) /\ LenOK n (snd (fw n W)) /\
  Inv dist (to_Z INF) (len dist) (dN n (fst (fw n W))) (xN n (snd (fw n W))).
Proof.
  unfold fw. cbv zeta. pose proof (to_Z_bounded n).
  assert (Hmk : LenOK n (PArray.make (n * n) 0)).
  { unfold LenOK. pose proof (nn_bound n Hn2). rewrite lmakeI.
    - rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    - rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia. }
  set (g0 := fun i j => if i =? j then 0 else if isroad W.[i * n + j] then W.[i * n + j] else INF).
  destruct (fill2_spec n Hn2 g0 _ Hmk) as [HD0 PD0].
  destruct (fill2_spec n Hn2 (fun i j => j) _ Hmk) as [HX0 PX0].
  set (D0 := fill2 n g0 (PArray.make (n * n) 0)) in *.
  set (X0 := fill2 n (fun i j => j) (PArray.make (n * n) 0)) in *.
  assert (Hg0 : forall a b, (a < len dist)%N -> (b < len dist)%N ->
     dN n D0 a b = if N.eqb a b then 0%Z else if Z.ltb 0 (entry dist a b) then entry dist a b else to_Z INF).
  { intros a b Ha Hb. rewrite PD0 by (apply ltn; assumption). unfold g0.
    pose proof (ltn a Ha). pose proof (ltn b Hb). clear PD0 PX0 HD0 HX0.
    assert (Ea : to_Z (of_Z (Z.of_N a)) = Z.of_N a) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    assert (Eb : to_Z (of_Z (Z.of_N b)) = Z.of_N b) by (apply to_Z_of_Z_small; rewrite wB_val; lia).
    destruct (N.eqb_spec a b).
    - subst. rewrite Uint63.eqb_refl. reflexivity.
    - replace (of_Z (Z.of_N a) =? of_Z (Z.of_N b)) with false.
      2:{ symmetry. apply Uint63.eqb_false_spec. intros E. apply (f_equal to_Z) in E. rewrite Ea, Eb in E. lia. }
      rewrite get_idx by (rewrite ?Ea, ?Eb; lia). rewrite (ofZN n) by lia. rewrite (ofZN n) by lia.
      destruct (Z.ltb_spec 0 (entry dist a b)) as [P|P].
      + assert (Hr : isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = true)
          by (apply isroad_iff; auto; repeat split; assumption).
        rewrite Hr. rewrite sint_pos; [apply HW; assumption|]. rewrite HW by assumption. exact P.
      + destruct (isroad W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)]) eqn:Hr; [|reflexivity].
        apply isroad_iff in Hr; auto. destruct Hr as (_ & _ & Hr). lia. }
  assert (I0 : Inv dist (to_Z INF) 0 (dN n D0) (xN n X0)).
  { constructor.
    - intros a b Ha Hb. rewrite Hg0 by assumption. rewrite INF_val. clear - Hrange Ha Hb.
      destruct (N.eqb_spec a b) as [Eab|Nab]; [lia|]. destruct (Z.ltb_spec 0 (entry dist a b)); [|lia].
      destruct (Hrange a b Ha Hb Nab); lia.
    - intros a Ha. rewrite Hg0 by assumption. rewrite N.eqb_refl. reflexivity.
    - intros a b (Ha & Hb & Hp). rewrite Hg0 by assumption. clear Hg0 PD0 PX0. destruct (N.eqb_spec a b).
      + subst. rewrite Hdiag in Hp by assumption. exfalso. clear - Hp. lia.
      + clear - Hp. destruct (Z.ltb_spec 0 (entry dist a b)); lia.
    - intros a b Ha Hb Nab Hlt. pose proof (ltn a Ha) as La. pose proof (ltn b Hb) as Lb.
      rewrite Hg0 in Hlt by assumption. rewrite (Hg0 a b Ha Hb).
      destruct (N.eqb_spec a b); [contradiction|].
      assert (Ex : xN n X0 a b = b).
      { unfold xN. rewrite PX0 by assumption. rewrite to_Z_of_Z_small by (rewrite wB_val; clear - Lb Hn2; lia).
        clear; lia. }
      rewrite Ex. destruct (Z.ltb_spec 0 (entry dist a b)) as [P|P]; [|exfalso; clear - Hlt; lia].
      split; [repeat split; assumption|]. rewrite Hg0 by assumption. rewrite N.eqb_refl. clear; lia.
    - intros c a b Hc. exfalso. clear - Hc. lia. }
  clearbody D0 X0. clear Hg0 PD0 PX0 Hmk. clearbody g0.
  pose (Iv := fun kz (st : array int * array int) => LenOK n (fst st) /\ LenOK n (snd st) /\
              Inv dist (to_Z INF) (Z.to_N kz) (dN n (fst st)) (xN n (snd st))).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - split; [exact HD0|]. split; [exact HX0|]. exact I0.
  - intros k [D X] Hk (HD & HX & Ik). change (to_Z 0) with 0%Z in Hk. simpl fst in *; simpl snd in *.
    assert (HkN : (toN k < len dist)%N) by (unfold toN; lia).
    destruct (fw_iter_spec n Hn2 k D X ltac:(lia) HD HX) as (Q1 & Q2 & Q3).
    + intros a b Ha Hb. apply (i_bnd _ _ _ _ _ Ik); lia.
    + apply (i_diag _ _ _ _ _ Ik). exact HkN.
    + split; [exact Q1|]. split; [exact Q2|].
      replace (Z.to_N (to_Z k + 1)) with (toN k + 1)%N by (unfold toN; lia).
      apply (Inv_ext _ _ _ (FD (dN n D) (toN k)) (FX (dN n D) (xN n X) (toN k))); [lia| |].
      * intros a b Ha Hb. destruct (Q3 a b ltac:(lia) ltac:(lia)) as [E1 E2]. split; assumption.
      * apply inv_step; assumption.
  - destruct Gl as (G1 & G2 & G3). split; [exact G1|]. split; [exact G2|].
    replace (len dist) with (Z.to_N (to_Z n)) by lia. exact G3.
Qed.

End FWQ.
End P_FWQ.

(* ================================================================== *)
Section P_WK.
Open Scope uint63_scope.

Lemma scan_spec : forall (n : int) (W : array int), (to_Z n <= 2000)%Z -> LenOK n W ->
  let I := fst (fst (scan_roads n W)) in let P := snd (fst (scan_roads n W)) in
  let E := snd (scan_roads n W) in
  LenOK n I /\ LenOK n P /\ (to_Z E <= to_Z n * to_Z n)%Z /\
  (forall p, (0 <= p < to_Z n * to_Z n)%Z -> isroad W.[of_Z p] = true ->
     (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
  (forall e, (0 <= e < to_Z E)%Z ->
     (0 <= to_Z P.[of_Z e] < to_Z n * to_Z n)%Z /\ isroad W.[P.[of_Z e]] = true /\
     to_Z I.[P.[of_Z e]] = e).
Proof.
  intros n W Hn HW. cbv zeta. unfold scan_roads. pose proof (to_Z_bounded n).
  pose proof (nn_bound n Hn) as Hnn.
  assert (Enn : to_Z (n * n) = (to_Z n * to_Z n)%Z) by (rewrite mul_spec; apply Z.mod_small; rewrite wB_val; lia).
  assert (Hmk : LenOK n (PArray.make (n * n) 0)) by (unfold LenOK; rewrite lmakeI; lia).
  pose (Iv := fun pz (st : array int * array int * int) =>
     let I := fst (fst st) in let P := snd (fst st) in let E := snd st in
     LenOK n I /\ LenOK n P /\ (to_Z E <= pz)%Z /\
     (forall p, (0 <= p < pz)%Z -> isroad W.[of_Z p] = true ->
        (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
     (forall e, (0 <= e < to_Z E)%Z ->
        (0 <= to_Z P.[of_Z e] < pz)%Z /\ isroad W.[P.[of_Z e]] = true /\ to_Z I.[P.[of_Z e]] = e)).
  match goal with |- context [forl ?lo ?hi ?f ?s0] =>
    assert (Gl : Iv (to_Z hi) (forl lo hi f s0)); [apply (for_invZ Iv); unfold Iv | unfold Iv in Gl] end.
  - change (to_Z 0) with 0%Z. lia.
  - simpl. split; [exact Hmk|]. split; [exact Hmk|]. change (to_Z 0) with 0%Z.
    split; [lia|]. split; intros; lia.
  - intros p [[I P] e] Hp (HI & HP & He & R1 & R2). simpl in *. change (to_Z 0) with 0%Z in Hp.
    rewrite Enn in Hp. unfold LenOK in HI, HP.
    destruct (isroad W.[p]) eqn:Rp; simpl.
    + assert (Ee : to_Z (e + 1) = (to_Z e + 1)%Z) by (pose proof (to_Z_bounded e); clear - He Hp Hnn; sia).
      split; [unfold LenOK; rewrite lsetI; exact HI|]. split; [unfold LenOK; rewrite lsetI; exact HP|].
      split; [lia|]. split.
      * intros p' Hp' Rp'. destruct (Z.eq_dec p' (to_Z p)) as [Eq|Nq].
        -- subst p'. rewrite of_Z_to_Z. rewrite gssI by lia. rewrite gssI by (pose proof (to_Z_bounded e); lia).
           split; lia.
        -- rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
           destruct (R1 p' ltac:(lia) Rp') as [L1 L2].
           rewrite gsoZI by lia. split; [lia | exact L2].
      * intros e' He'. rewrite Ee in He'. destruct (Z.eq_dec e' (to_Z e)) as [Eq|Nq].
        -- subst e'. rewrite of_Z_to_Z. rewrite gssI by (pose proof (to_Z_bounded e); lia).
           split; [pose proof (to_Z_bounded p); lia|]. split; [exact Rp|]. rewrite gssI by lia. reflexivity.
        -- rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
           destruct (R2 e' ltac:(lia)) as (L1 & L2 & L3). split; [lia|]. split; [exact L2|].
           rewrite gsoZI by lia. exact L3.
    + split; [exact HI|]. split; [exact HP|]. split; [lia|]. split.
      * intros p' Hp' Rp'. destruct (Z.eq_dec p' (to_Z p)) as [Eq|Nq].
        -- subst p'. rewrite of_Z_to_Z in Rp'. congruence.
        -- apply R1; [lia | exact Rp'].
      * intros e' He'. destruct (R2 e' He') as (L1 & L2 & L3). split; [lia|]. auto.
  - rewrite Enn in Gl. exact Gl.
Qed.

Fixpoint psumR (f : N -> N -> R) (p : list N) : R :=
  match p with
  | a :: ((b :: _) as tl) => (f a b + psumR f tl)%R
  | _ => 0%R
  end.

Definition cntsum (E : int) (cnt : array int) (z : nat -> R) : R :=
  sumR (Z.to_nat (to_Z E)) (fun e => (IZR (to_Z cnt.[of_Z (Z.of_nat e)]) * z e)%R).

Lemma cntsum_incr : forall E cnt (e : int) z,
  to_Z (PArray.length cnt) = to_Z E ->
  (to_Z e < to_Z E)%Z -> (to_Z cnt.[e] + 1 < wB)%Z ->
  cntsum E (cnt.[e <- cnt.[e] + 1]) z = (cntsum E cnt z + z (Z.to_nat (to_Z e)))%R.
Proof.
  intros E cnt e z HL He Hb. unfold cntsum.
  rewrite (sumR_ext _ _ (fun e' => (IZR (to_Z cnt.[of_Z (Z.of_nat e')]) * z e' +
              (if Nat.eqb e' (Z.to_nat (to_Z e)) then z e' else 0))%R)).
  - rewrite sumR_plus, sumR_delta. destruct (Nat.ltb_spec (Z.to_nat (to_Z e)) (Z.to_nat (to_Z E))); [reflexivity|].
    pose proof (to_Z_bounded e). lia.
  - intros e' He'. destruct (Nat.eqb_spec e' (Z.to_nat (to_Z e))) as [Eq|Nq].
    + subst e'. rewrite Z2Nat.id by (pose proof (to_Z_bounded e); lia). rewrite of_Z_to_Z.
      rewrite gssI by lia. rewrite add_spec, Z.mod_small by (pose proof (to_Z_bounded cnt.[e]); lia).
      change (to_Z 1) with 1%Z. rewrite plus_IZR. ring.
    + rewrite gsoZI. 2:{ rewrite to_Z_of_Z_small by (rewrite wB_val; pose proof (to_Z_bounded E); lia). lia. }
      ring.
Qed.

Lemma walk_eq : forall n d E D X I cur cnt H,
  walk n d E D X I cur cnt H =
  if cur =? d then cnt else
  let v := X.[cur * n + d] in
  match bdec (D.[v * n + d] <? D.[cur * n + d]) with
  | left Hlt =>
      let e := I.[cur * n + v] in
      walk n d E D X I v (if e <? E then cnt.[e <- cnt.[e] + 1] else cnt)
        (Acc_inv H (walk_dec _ _ Hlt))
  | right _ => cnt
  end.
Proof. intros. destruct H. reflexivity. Qed.

Section Walk.
Variable dist : list (list Z).
Variables (n E : int) (D X I : array int).
Hypothesis Hn : to_Z n = Z.of_N (len dist).
Hypothesis Hn2 : (to_Z n <= 2000)%Z.
Hypothesis HI : Inv dist (to_Z INF) (len dist) (dN n D) (xN n X).
Hypothesis HIr : forall a b, road dist a b -> (to_Z I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] < to_Z E)%Z.

Lemma toN_lt : forall c : int, (to_Z c < to_Z n)%Z -> (toN c < len dist)%N.
Proof. intros c H. unfold toN. pose proof (to_Z_bounded c). lia. Qed.

Lemma walk_spec : forall (d : int), (to_Z d < to_Z n)%Z -> forall B, (B <= to_Z INF)%Z ->
  forall mz cur cnt H, to_Z D.[cur * n + d] = mz ->
  (to_Z cur < to_Z n)%Z -> (dN n D (toN cur) (toN d) < to_Z INF)%Z ->
  to_Z (PArray.length cnt) = to_Z E ->
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e] <= B - dN n D (toN cur) (toN d))%Z) ->
  exists p, route dist (toN cur) (toN d) p /\
    (distance dist p <= dN n D (toN cur) (toN d))%Z /\
    to_Z (PArray.length (walk n d E D X I cur cnt H)) = to_Z E /\
    (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (walk n d E D X I cur cnt H).[of_Z e] <= B)%Z) /\
    forall z, cntsum E (walk n d E D X I cur cnt H) z =
      (cntsum E cnt z + psumR (fun a b => z (Z.to_nat (dN n I a b))) p)%R.
Proof.
  intros d Hd B HB mz. induction mz as [mz IH] using (well_founded_induction (Zwf_well_founded 0)).
  intros cur cnt H Emz Hc Hlt HL Hcnt.
  pose proof (toN_lt cur Hc) as HcN. pose proof (toN_lt d Hd) as HdN.
  pose proof (i_bnd _ _ _ _ _ HI _ _ HcN HdN) as Bcd.
  rewrite walk_eq.
  destruct (cur =? d) eqn:Ecd.
  - apply Uint63.eqb_spec in Ecd. subst cur. exists (toN d :: nil). split; [apply route_here; exact HdN|].
    split; [simpl; lia|]. split; [exact HL|]. split.
    + intros e He. pose proof (Hcnt e He). lia.
    + intros z. simpl. ring.
  - apply Uint63.eqb_false_spec in Ecd.
    assert (Ncd : toN cur <> toN d).
    { intros E'. apply Ecd. apply to_Z_inj. unfold toN in E'. pose proof (to_Z_bounded cur).
      pose proof (to_Z_bounded d). lia. }
    destruct (i_succ _ _ _ _ _ HI _ _ HcN HdN Ncd Hlt) as [R Le].
    cbv zeta.
    set (v := X.[cur * n + d]).
    assert (Ev : xN n X (toN cur) (toN d) = toN v).
    { unfold xN, dN, v, toN. rewrite get_idx by assumption. reflexivity. }
    rewrite Ev in R, Le.
    assert (Hv : (to_Z v < to_Z n)%Z) by (destruct R as (_ & Hv & _); unfold toN in Hv; pose proof (to_Z_bounded v); lia).
    pose proof (toN_lt v Hv) as HvN.
    assert (Edv : to_Z D.[v * n + d] = dN n D (toN v) (toN d)) by (unfold dN; rewrite get_idx by assumption; reflexivity).
    assert (Edc : to_Z D.[cur * n + d] = dN n D (toN cur) (toN d)) by (unfold dN; rewrite get_idx by assumption; reflexivity).
    pose proof R as (_ & _ & Rp).
    destruct (bdec (D.[v * n + d] <? D.[cur * n + d])) as [Hlt'|Hlt'].
    2:{ exfalso. rewrite <- Bool.not_true_iff_false, Uint63.ltb_spec, Edv, Edc in Hlt'. lia. }
    cbv zeta. set (e := I.[cur * n + v]).
    assert (He : (to_Z e < to_Z E)%Z).
    { unfold e. rewrite get_idx by assumption. apply HIr. exact R. }
    replace (e <? E) with true by (symmetry; apply Uint63.ltb_spec; exact He).
    pose proof (to_Z_bounded e) as Be.
    assert (Bce : (0 <= to_Z cnt.[e] <= B - dN n D (toN cur) (toN d))%Z).
    { rewrite <- (of_Z_to_Z e). apply Hcnt. lia. }
    assert (Ece : to_Z (cnt.[e] + 1) = (to_Z cnt.[e] + 1)%Z).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_val. rewrite INF_val in *. lia. }
    pose proof (i_bnd _ _ _ _ _ HI _ _ HvN HdN) as Bvd.
    destruct (IH (to_Z D.[v * n + d])) with (cur := v) (cnt := cnt.[e <- cnt.[e] + 1])
       (H := Acc_inv H (walk_dec D.[v * n + d] D.[cur * n + d] Hlt')) as (p' & R' & L' & HL' & Hc' & Hs').
    + rewrite <- Emz, Edv, Edc. unfold Zwf. lia.
    + reflexivity.
    + exact Hv.
    + lia.
    + rewrite lsetI. exact HL.
    + intros e' He'. destruct (Z.eq_dec e' (to_Z e)) as [Eq|Nq].
      * subst e'. rewrite of_Z_to_Z, gssI by lia. lia.
      * rewrite gsoZI by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia).
        pose proof (Hcnt e' He'). lia.
    + exists (toN cur :: p'). split; [apply route_step with (toN v); assumption|].
      destruct (route_head dist _ _ _ R') as [tl Et].
      split; [rewrite Et in *; rewrite distance_cons2; lia|].
      split; [exact HL'|]. split; [exact Hc'|].
      intros z. rewrite Hs'. rewrite cntsum_incr by (try exact HL; try lia).
      rewrite Et. simpl psumR.
      assert (Ei : dN n I (toN cur) (toN v) = to_Z e) by (unfold dN, e; rewrite get_idx by assumption; reflexivity).
      rewrite Ei. ring.
Qed.

End Walk.
End P_WK.

(* ================================================================== *)
Section P_MS1.
Open Scope uint63_scope.

Section MS1.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.

Local Notation n := (PArray.length xdist).
Local Notation nn := (len dist).
Local Notation W := (flatten (PArray.length xdist) xdist).

Lemma n_val : to_Z n = Z.of_N nn.
Proof. destruct Rd as [L _]. unfold len. rewrite nat_N_Z. symmetry. exact L. Qed.

Lemma n_bounds : (1 <= to_Z n <= 30)%Z.
Proof. rewrite n_val. destruct (vi_n _ _ _ _ _ _ Hv). lia. Qed.

Lemma n_le : (to_Z n <= 2000)%Z.
Proof. pose proof n_bounds. lia. Qed.

Lemma entry_repr : forall a b, (a < nn)%N -> (b < nn)%N ->
  Sint63.to_Z ((xdist.[of_Z (Z.of_N a)]).[of_Z (Z.of_N b)] : sint) = entry dist a b.
Proof.
  intros a b Ha Hb. destruct Rd as [L Hc].
  unfold len in Ha, Hb.
  destruct (Hc (N.to_nat a) ltac:(lia)) as (row & Er & Rr).
  pose proof (vi_rows _ _ _ _ _ _ Hv) as Rows. rewrite Forall_forall in Rows.
  assert (Hrow : len row = nn) by (apply Rows; apply nth_error_In with (N.to_nat a); exact Er).
  destruct Rr as [Lr Hcr].
  unfold len in Hrow.
  destruct (Hcr (N.to_nat b) ltac:(lia)) as (e & Ee & Re).
  unfold repr, repr_sint in Re.
  rewrite N_nat_Z in Re. rewrite N_nat_Z in Re.
  unfold entry. rewrite (nth_error_nth _ _ _ Er). rewrite (nth_error_nth _ _ _ Ee). exact Re.
Qed.

Lemma W_len : LenOK n W.
Proof.
  unfold flatten. destruct (fill2_spec n n_le (fun i j => (xdist.[i]).[j]) (PArray.make (n * n) 0)) as [L _].
  - pose proof n_bounds. pose proof (nn_bound n n_le). unfold LenOK. rewrite lmakeI.
    + rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    + rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia.
  - exact L.
Qed.

Lemma W_spec : forall a b, (a < nn)%N -> (b < nn)%N ->
  Sint63.to_Z W.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] = entry dist a b.
Proof.
  intros a b Ha Hb. unfold flatten.
  match goal with |- context [fill2 ?n0 ?g ?A] =>
    destruct (fill2_spec n0 n_le g A) as [_ P] end.
  - pose proof n_bounds. pose proof (nn_bound n n_le). unfold LenOK. rewrite lmakeI.
    + rewrite mul_spec. apply Z.mod_small. rewrite wB_val. lia.
    + rewrite mul_spec, Z.mod_small by (rewrite wB_val; lia). lia.
  - pose proof n_val. specialize (P a b ltac:(lia) ltac:(lia)). unfold dN in P.
    apply to_Z_inj in P. rewrite P. exact (entry_repr a b Ha Hb).
Qed.


Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).

Lemma Hdiag : forall a, (a < nn)%N -> entry dist a a = 0%Z.
Proof. intros a Ha. apply (vi_diag _ _ _ _ _ _ Hv). exact Ha. Qed.

Lemma Hrange : forall a b, (a < nn)%N -> (b < nn)%N -> a <> b ->
  entry dist a b = (-1)%Z \/ (1 <= entry dist a b <= 1000)%Z.
Proof. intros a b Ha Hb Nab. apply (vi_dist _ _ _ _ _ _ Hv); assumption. Qed.

Lemma FWinv : Inv dist (to_Z INF) nn (dN n D) (xN n X).
Proof. apply (fw_spec dist n W n_val n_le W_spec Hdiag Hrange). Qed.

Lemma road_le : forall a b, road dist a b -> (1 <= entry dist a b <= 1000)%Z.
Proof.
  intros a b (Ha & Hb & Hp). destruct (N.eq_dec a b) as [->|Nab].
  - rewrite Hdiag in Hp by exact Ha. lia.
  - destruct (Hrange a b Ha Hb Nab); lia.
Qed.

Lemma scan_facts :
  LenOK n I /\ LenOK n P /\ (to_Z E <= to_Z n * to_Z n)%Z /\
  (forall p, (0 <= p < to_Z n * to_Z n)%Z -> isroad W.[of_Z p] = true ->
     (to_Z I.[of_Z p] < to_Z E)%Z /\ to_Z P.[I.[of_Z p]] = p) /\
  (forall e, (0 <= e < to_Z E)%Z ->
     (0 <= to_Z P.[of_Z e] < to_Z n * to_Z n)%Z /\ isroad W.[P.[of_Z e]] = true /\
     to_Z I.[P.[of_Z e]] = e).
Proof. apply (scan_spec n W n_le W_len). Qed.

Lemma E_le : (to_Z E <= 900)%Z.
Proof. destruct scan_facts as (_ & _ & H & _). pose proof n_bounds. nia. Qed.

Lemma pos_lt : forall a b, (a < nn)%N -> (b < nn)%N ->
  (0 <= Z.of_N a * to_Z n + Z.of_N b < to_Z n * to_Z n)%Z.
Proof. intros a b Ha Hb. pose proof n_val. nia. Qed.

Lemma HIr : forall a b, road dist a b -> (to_Z I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)] < to_Z E)%Z.
Proof.
  intros a b R. pose proof R as (Ha & Hb & _). destruct scan_facts as (_ & _ & _ & S1 & _).
  apply S1; [apply pos_lt; assumption|]. apply (isroad_iff dist n W W_spec); assumption.
Qed.

Lemma shortest_bound : forall s d p, shortest_route dist s d p ->
  (distance dist p <= 1000 * (Z.of_N nn - 1))%Z.
Proof.
  intros s d p Sh. pose proof (shortest_nodup dist s d p Sh) as ND.
  destruct Sh as [R _].
  pose proof (nodup_length p nn ND (route_cities dist _ _ _ R)) as L.
  pose proof (distance_bound dist 1000 s d p (fun i j H => proj2 (road_le i j H)) ltac:(lia) R) as B.
  destruct (route_head dist _ _ _ R) as [tl ->]. simpl length in *. nia.
Qed.

Lemma route_cnt_spec : forall s d : int, (toN s < nn)%N -> (toN d < nn)%N ->
  unique_shortest_route dist (toN s) (toN d) ->
  let cnt := route_cnt n E D X I s d in
  to_Z (PArray.length cnt) = to_Z E /\
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e] <= to_Z INF)%Z) /\
  exists p, shortest_route dist (toN s) (toN d) p /\ distance dist p = dN n D (toN s) (toN d) /\
    (forall p', shortest_route dist (toN s) (toN d) p' -> p' = p) /\
    forall z, cntsum E cnt z = psumR (fun a b => z (Z.to_nat (dN n I a b))) p.
Proof.
  intros s d Hs Hd (p0 & Sh0 & Un0). cbv zeta.
  pose proof FWinv as FI. pose proof n_val as En. pose proof E_le as HE.
  assert (Hs' : (to_Z s < to_Z n)%Z) by (unfold toN in Hs; pose proof (to_Z_bounded s); lia).
  assert (Hd' : (to_Z d < to_Z n)%Z) by (unfold toN in Hd; pose proof (to_Z_bounded d); lia).
  assert (Dle : (dN n D (toN s) (toN d) <= distance dist p0)%Z) by (apply (inv_route dist _ _ _ FI); apply Sh0).
  pose proof (shortest_bound _ _ _ Sh0) as Bp0.
  assert (Dlt : (dN n D (toN s) (toN d) < to_Z INF)%Z).
  { rewrite INF_val. destruct (vi_n _ _ _ _ _ _ Hv). lia. }
  assert (HLm : to_Z (PArray.length (PArray.make E 0)) = to_Z E) by (rewrite lmakeI; [reflexivity | lia]).
  unfold route_cnt.
  destruct (walk_spec dist n E D X I n_val n_le FI HIr d Hd' (to_Z INF) ltac:(lia)
              (to_Z D.[s * n + d]) s (PArray.make E 0) (Zwf_well_founded 0 _) eq_refl Hs' Dlt HLm)
    as (p & R & Ld & HL & Hc & Hsum).
  - intros e He. rewrite gmakeI. change (to_Z 0) with 0%Z. pose proof (i_bnd _ _ _ _ _ FI _ _ Hs Hd). lia.
  - split; [exact HL|]. split; [exact Hc|].
    assert (Shp : shortest_route dist (toN s) (toN d) p).
    { split; [exact R|]. intros p' R'. pose proof (inv_route dist _ _ _ FI _ _ _ R'). lia. }
    exists p. split; [exact Shp|]. split.
    + pose proof (inv_route dist _ _ _ FI _ _ _ R). lia.
    + split.
      * intros p' Sh'. rewrite (Un0 p' Sh'), (Un0 p Shp). reflexivity.
      * intros z. rewrite Hsum. unfold cntsum. rewrite sumR_zero; [ring|].
        intros e He. rewrite gmakeI. change (to_Z 0) with 0%Z. simpl. ring.
Qed.

End MS1.
End P_MS1.

(* ================================================================== *)
Section P_MS2.
Open Scope uint63_scope.

(* the rows of the initial tableau, read as linear forms *)
Section Rows.
Variables (n E RR : int) (W D X I P rs rd rt : array int).
Hypothesis Hg : guard E RR = true.
Local Notation Et := (Z.to_nat (to_Z E)).
Local Notation Rt := (Z.to_nat (to_Z RR)).
Local Notation w := (E + (E + RR) + 1).
Local Notation T0 := (build_T n E RR W D X I P rs rd rt).
Local Notation t0 := (cell (build_T n E RR W D X I P rs rd rt) (E + (E + RR) + 1)).

Lemma mn_val : Z.to_nat (to_Z (E + RR)) = (Et + Rt)%nat.
Proof. rewrite (m_val E RR Hg). pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia. Qed.

Lemma Nn_val : Z.of_nat (Et + (Et + Rt)) = to_Z (E + (E + RR)).
Proof. rewrite (N_val' E RR Hg). pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia. Qed.

Lemma t0_eq : forall r j, (r < Et + Rt)%nat -> (j <= Et + (Et + Rt))%nat ->
  t0 r j = T0f n E RR W D X I P rs rd rt (Z.of_nat r) (Z.of_nat j).
Proof.
  intros r j Hr Hj. unfold cell. destruct (build_spec n E RR W D X I P rs rd rt Hg) as [_ PT].
  apply PT. unfold IR. rewrite (m_val E RR Hg), (w_val' E RR Hg).
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). lia.
Qed.

Definition cnt_k (k : nat) : array int := cntk n E D X I rs rd (Z.of_nat k).
Definition b_k (k : nat) : Z := bk n D rs rd rt (Z.of_nat k).
Definition sg (b : Z) : R := if Z.ltb b 0 then (-1)%R else 1%R.

Lemma lin_bound : forall e z, (e < Et)%nat ->
  lin (Et + Rt) Et (t0 e) z = (z e + z (Et + e)%nat)%R.
Proof.
  intros e z He. unfold lin. replace (Et + (Et + Rt))%nat with (Et + (Et + Rt))%nat by lia.
  rewrite (sumR_ext _ _ (fun j => (if Nat.eqb j e then z j else 0) + (if Nat.eqb j (Et + e) then z j else 0))%R).
  - rewrite sumR_plus, !sumR_delta.
    destruct (Nat.ltb_spec e (Et + (Et + Rt))); [|lia]. destruct (Nat.ltb_spec (Et + e) (Et + (Et + Rt))); [|lia].
    reflexivity.
  - intros j Hj. rewrite t0_eq by lia. unfold T0f, boundf.
    pose proof (to_Z_bounded E). pose proof Nn_val.
    destruct (Z.ltb_spec (Z.of_nat e) (to_Z E)); [|lia].
    destruct (Nat.eqb_spec j e); destruct (Nat.eqb_spec j (Et + e)); try lia.
    + subst. rewrite Z.eqb_refl. ring.
    + destruct (Z.eqb_spec (Z.of_nat j) (Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + Z.of_nat e)); [|lia]. ring.
    + destruct (Z.eqb_spec (Z.of_nat j) (Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + Z.of_nat e)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z (E + (E + RR)))); [lia|]. ring.
Qed.

Lemma rhs_bound : forall e, (e < Et)%nat -> t0 e (Et + (Et + Rt)) = IZR (ue W P (Z.of_nat e)).
Proof.
  intros e He. rewrite t0_eq by lia. unfold T0f, boundf. rewrite Nn_val.
  pose proof (to_Z_bounded E). pose proof (N_val' E RR Hg).
  destruct (Z.ltb_spec (Z.of_nat e) (to_Z E)); [|lia].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (Z.of_nat e)); [lia|].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (to_Z E + Z.of_nat e)); [lia|].
  rewrite Z.eqb_refl. reflexivity.
Qed.

Lemma lin_deliv : forall k z, (k < Rt)%nat ->
  lin (Et + Rt) Et (t0 (Et + k)) z =
  (sg (b_k k) * cntsum E (cnt_k k) z + z (Et + Et + k)%nat)%R.
Proof.
  intros k z Hk. unfold lin. pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). pose proof Nn_val.
  rewrite (sumR_ext _ _ (fun j => (if Nat.ltb j Et then sg (b_k k) * (IZR (to_Z (cnt_k k).[of_Z (Z.of_nat j)]) * z j) else 0) +
                                   (if Nat.eqb j (Et + Et + k) then z j else 0))%R).
  - rewrite sumR_plus, sumR_delta. destruct (Nat.ltb_spec (Et + Et + k) (Et + (Et + Rt))); [|lia].
    f_equal. unfold cntsum. rewrite <- sumR_scal.
    replace (Et + (Et + Rt))%nat with (Et + (Et + Rt))%nat by reflexivity.
    rewrite sumR_split. rewrite (sumR_zero (Et + Rt)) by (intros i Hi; destruct (Nat.ltb_spec (Et + i) Et); [lia|reflexivity]).
    rewrite Rplus_0_r. apply sumR_ext. intros j Hj. destruct (Nat.ltb_spec j Et); [reflexivity|lia].
  - intros j Hj. rewrite t0_eq by lia. unfold T0f, delivf.
    destruct (Z.ltb_spec (Z.of_nat (Et + k)) (to_Z E)); [lia|].
    replace (Z.of_nat (Et + k) - to_Z E)%Z with (Z.of_nat k) by lia.
    fold (cnt_k k). unfold cntk. fold (b_k k).
    destruct (Nat.ltb_spec j Et); destruct (Nat.eqb_spec j (Et + Et + k)); try lia.
    + destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [|lia]. unfold sg, b_k. rewrite zofi_spec.
      destruct (Z.ltb (bk n D rs rd rt (Z.of_nat k)) 0); rewrite ?opp_IZR; ring.
    + subst j. destruct (Z.ltb_spec (Z.of_nat (Et + Et + k)) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat (Et + Et + k)) (to_Z E + to_Z E + Z.of_nat k)); [|lia]. ring.
    + destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z E + to_Z E + Z.of_nat k)); [lia|].
      destruct (Z.eqb_spec (Z.of_nat j) (to_Z (E + (E + RR)))); [lia|]. ring.
Qed.

Lemma rhs_deliv : forall k, (k < Rt)%nat -> t0 (Et + k) (Et + (Et + Rt)) = IZR (Z.abs (b_k k)).
Proof.
  intros k Hk. rewrite t0_eq by lia. unfold T0f, delivf. rewrite Nn_val.
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR). pose proof (N_val' E RR Hg).
  destruct (Z.ltb_spec (Z.of_nat (Et + k)) (to_Z E)); [lia|].
  destruct (Z.ltb_spec (to_Z (E + (E + RR))) (to_Z E)); [lia|].
  destruct (Z.eqb_spec (to_Z (E + (E + RR))) (to_Z E + to_Z E + (Z.of_nat (Et + k) - to_Z E))); [lia|].
  rewrite Z.eqb_refl. unfold b_k. f_equal. f_equal. f_equal. lia.
Qed.

End Rows.

Lemma duration_cons2 : forall dist v a b l,
  duration dist v (a :: b :: l) = (60 * IZR (entry dist a b) / v a b + duration dist v (b :: l))%R.
Proof. reflexivity. Qed.

Lemma dur_gen : forall dist (v : N -> N -> R) (f : N -> N -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + f a b)%R) ->
  forall s d p, route dist s d p -> duration dist v p = (IZR (distance dist p) + psumR f p)%R.
Proof.
  intros dist v f Hf s d p R. induction R as [s Hs | s m d p Rr Rp IH].
  - simpl. ring.
  - destruct (route_head dist _ _ _ Rp) as [tl ->]. rewrite duration_cons2, distance_cons2.
    simpl psumR. rewrite Hf by exact Rr. rewrite IH, plus_IZR. simpl psumR. ring.
Qed.

Lemma repr_uint_nth : forall (x : array uint) (l : list N), repr x l ->
  forall k : nat, (k < List.length l)%nat ->
  Z.to_N (to_Z x.[of_Z (Z.of_nat k)]) = get_list_N l (N.of_nat k).
Proof.
  intros x l [L H] k Hk. destruct (H k Hk) as (v & Ev & Rv). unfold repr, repr_uint in Rv.
  unfold get_list_N. rewrite Nat2N.id. rewrite (nth_error_nth _ _ _ Ev). exact Rv.
Qed.

Lemma repr_uint_len : forall (x : array uint) (l : list N), repr x l ->
  to_Z (PArray.length x) = Z.of_N (len l).
Proof. intros x l [L _]. unfold len. rewrite nat_N_Z. symmetry. exact L. Qed.
End P_MS2.

(* ================================================================== *)
Section P_FL.
Import Flocq.Core.Raux Flocq.Core.Zaux.
Local Open Scope R_scope.

Lemma two36_R : IZR (to_Z two36) = 68719476736.
Proof. reflexivity. Qed.

Lemma q2f_spec : forall q, 0 <= Q2R q <= 60000 ->
  exists r, repr (q2f q) r /\ Rabs (r - Q2R q) <= / 1000000.
Proof.
  intros [num den] Hq. unfold q2f. simpl Qnum. simpl Qden.
  set (mz := ((num * 68719476736) / Zpos den)%Z).
  assert (Hd : (0 < Zpos den)%Z) by lia.
  assert (Lo : (mz * Zpos den <= num * 68719476736)%Z) by (unfold mz; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
  assert (Hi : (num * 68719476736 < (mz + 1) * Zpos den)%Z).
  { unfold mz. rewrite Z.mul_comm. pose proof (Z.mul_succ_div_gt (num * 68719476736) (Zpos den) Hd). lia. }
  unfold Q2R in Hq. simpl in Hq.
  assert (Dp : 0 < IZR (Zpos den)) by (apply IZR_lt; lia).
  set (y := IZR num * / IZR (Zpos den)) in *.
  assert (Ylo : IZR mz <= y * 68719476736).
  { apply (Rmult_le_reg_r (IZR (Zpos den))); [exact Dp|]. unfold y.
    replace (IZR num * / IZR (Z.pos den) * 68719476736 * IZR (Z.pos den)) with (IZR (num * 68719476736))
      by (rewrite mult_IZR; field; lra).
    rewrite <- mult_IZR. apply IZR_le. exact Lo. }
  assert (Yhi : y * 68719476736 < IZR mz + 1).
  { apply (Rmult_lt_reg_r (IZR (Zpos den))); [exact Dp|]. unfold y.
    replace (IZR num * / IZR (Z.pos den) * 68719476736 * IZR (Z.pos den)) with (IZR (num * 68719476736))
      by (rewrite mult_IZR; field; lra).
    replace ((IZR mz + 1) * IZR (Z.pos den)) with (IZR ((mz + 1) * Z.pos den)) by (rewrite mult_IZR, plus_IZR; ring).
    apply IZR_lt. exact Hi. }
  assert (Mb : (0 <= mz < 4503599627370496)%Z).
  { split.
    - destruct (Z_lt_le_dec mz 0) as [L|L]; [|exact L]. exfalso.
      assert (IZR mz <= -1) by (apply IZR_le; lia). lra.
    - apply lt_IZR. assert (y * 68719476736 <= 60000 * 68719476736) by lra. lra. }
  assert (Ei : to_Z (iofz mz) = mz) by (apply iofz_spec; rewrite wB_val; lia).
  assert (Ra : repr (of_uint63 (iofz mz)) (IZR mz)).
  { pose proof (repr_of_uint63_exact (iofz mz) ltac:(rewrite Ei; lia)) as R0. rewrite Ei in R0. exact R0. }
  assert (Rb : repr (of_uint63 two36) 68719476736).
  { rewrite <- two36_R. apply repr_of_uint63_exact. reflexivity. }
  set (t := IZR mz / 68719476736).
  assert (Tb : 0 <= t <= 60000).
  { unfold t. split.
    - apply Rmult_le_pos; [apply IZR_le; lia | lra].
    - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra. }
  exists (rnd t). split.
  - apply repr_div; [exact Ra | exact Rb | lra |].
    assert (Tb' : 0 <= IZR mz / 68719476736 <= 60000) by exact Tb.
    apply rnd_no_overflow_small. rewrite Rabs_right by lra.
    pose proof (bpow_le radix2 20 1000 ltac:(lia)) as H1. change (bpow radix2 20) with 1048576 in H1. lra.
  - change (Q2R (num # den)) with y. destruct (rnd_model t) as (eps & eta & Heps & Heta & _ & ->).
    pose proof eta_max_le_u. rewrite u_val in *.
    assert (Ht : Rabs (t - y) <= / 68719476736).
    { unfold t. apply Rabs_le. split.
      - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra.
      - apply (Rmult_le_reg_r 68719476736); [lra|]. field_simplify. lra. }
    replace (t * (1 + eps) + eta - y) with ((t - y) + t * eps + eta) by ring.
    eapply Rle_trans; [apply Rabs_triang|]. eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang|].
    rewrite Rabs_mult. rewrite (Rabs_right t) by lra.
    assert (t * Rabs eps <= 60000 * (/ 4503599627370496 / 2)).
    { apply Rmult_le_compat; try lra. apply Rabs_pos. }
    lra.
Qed.
End P_FL.

(* ================================================================== *)
Section P_MD.
Open Scope uint63_scope.

(* a plain read, a constant of its own so that proofs refer to the very
   same term *)
Definition aget (t : array int) (i : int) : int := t.[i].

Section Answers.
Variables (n E RR : int) (D X I : array int) (T0 : array Q).
Local Notation w := (E + (E + RR) + 1).
Local Notation NN := (E + (E + RR)).
Variable Hp : P1ok T0 (E + RR) E (E + E).

(* the route length of the trip s -> d *)
Definition dq (s d : int) : Q := inject_Z (zofi D.[s * n + d]).

(* the least (neg = false) or minus the greatest (neg = true) extra time of
   the trip s -> d, from the phase-1 tableau st1 *)
Definition vq (st1 : SState)
    (Hv1 : VS (E + RR) E (cell T0 w) (ovec (cart w (E + E) NN)) st1)
    (al : array bool) (s d : int) (neg : bool) : Q :=
  phase2 T0 (E + RR) E (E + E) Hp st1 Hv1 al (qcost E w (route_cnt n E D X I s d) neg).

Definition qans (st1 : SState)
    (Hv1 : VS (E + RR) E (cell T0 w) (ovec (cart w (E + E) NN)) st1)
    (al : array bool) (s d : int) : float * float :=
  (q2f (Qplus (dq s d) (vq st1 Hv1 al s d false)),
   q2f (Qminus (dq s d) (vq st1 Hv1 al s d true))).

Definition answers (xqs xqd : array int) : array (float * float) :=
  let st1 := phase1 T0 (E + RR) E (E + E) Hp in
  let al := al2 (sO st1) (E + E) NN in
  forl 0 (PArray.length xqs)
    (fun j out => out.[j <- qans st1 (phase1_VS T0 (E + RR) E (E + E) Hp) al (aget xqs j) (aget xqd j)])
    (PArray.make (PArray.length xqs) (PrimFloat.zero, PrimFloat.zero)).
End Answers.

Definition roadtimes_impl (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint)
    : array (float * float) :=
  let n := PArray.length xdist in
  let W := flatten n xdist in
  let FW := fw n W in
  let D := fst FW in let X := snd FW in
  let SR := scan_roads n W in
  let I := fst (fst SR) in let P := snd (fst SR) in let E := snd SR in
  let RR := PArray.length xrs in
  match bdec (guard E RR) with
  | left Hg =>
      let T0 := build_T n E RR W D X I P xrs xrd xrt in
      answers n E RR D X I T0 (build_ok n E RR W D X I P xrs xrd xrt Hg) xqs xqd
  | right _ => PArray.make (PArray.length xqs) (PrimFloat.zero, PrimFloat.zero)
  end.
End P_MD.

(* ================================================================== *)
Section P_MS3.
Open Scope uint63_scope.

Lemma guard_true : forall E RR : int, (1 <= to_Z E + to_Z RR)%Z -> (to_Z E <= 2048)%Z -> (to_Z RR <= 2048)%Z ->
  ((to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1) <= 4194303)%Z -> guard E RR = true.
Proof.
  intros E RR H1 H2 H3 H4. unfold guard.
  pose proof (to_Z_bounded E). pose proof (to_Z_bounded RR).
  assert (A : to_Z (E + RR) = (to_Z E + to_Z RR)%Z) by (rewrite add_spec; apply Z.mod_small; rewrite wB_val; lia).
  assert (B2 : to_Z (E + (E + RR) + 1) = (2 * to_Z E + to_Z RR + 1)%Z).
  { rewrite add_spec, add_spec, A. change (to_Z 1) with 1%Z.
    rewrite (Z.mod_small (to_Z E + (to_Z E + to_Z RR))) by (rewrite wB_val; lia).
    rewrite Z.mod_small; [lia | rewrite wB_val; lia]. }
  assert (C : to_Z ((E + RR) * (E + (E + RR) + 1)) = ((to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1))%Z).
  { rewrite mul_spec, A, B2. apply Z.mod_small. split; [apply Z.mul_nonneg_nonneg; lia|]. rewrite wB_val. lia. }
  repeat (apply andb_true_iff; split); apply Uint63.leb_spec;
    rewrite ?A, ?C; change (to_Z 1) with 1%Z; change (to_Z 2048) with 2048%Z;
    change (to_Z 4194303) with 4194303%Z; lia.
Qed.


Lemma qcost_spec : forall E w cnt neg, (to_Z E < to_Z w)%Z -> (to_Z w <= 4194303)%Z ->
  to_Z (PArray.length (qcost E w cnt neg)) = to_Z w /\
  forall j, (0 <= j < to_Z w)%Z -> Q2R (qcost E w cnt neg).[of_Z j] =
    if Z.ltb j (to_Z E) then (if neg then (- IZR (to_Z cnt.[of_Z j]))%R else IZR (to_Z cnt.[of_Z j])) else 0%R.
Proof.
  intros E w cnt neg HE Hw. unfold qcost. pose proof (to_Z_bounded E).
  pose (Iv := fun ez (c : array Q) => to_Z (PArray.length c) = to_Z w /\
     forall j, (0 <= j < to_Z w)%Z -> Q2R c.[of_Z j] =
       if Z.ltb j ez then (if neg then (- IZR (to_Z cnt.[of_Z j]))%R else IZR (to_Z cnt.[of_Z j])) else 0%R).
  assert (G : Iv (to_Z E) (forl 0 E (fun e c => c.[e <- inject_Z (if neg then (- zofi cnt.[e])%Z else zofi cnt.[e])])
                 (PArray.make w 0%Q))).
  { apply (for_invZ Iv); unfold Iv.
    - change (to_Z 0) with 0%Z. lia.
    - rewrite lmakeQ by exact Hw. split; [reflexivity|]. intros j Hj. rewrite gmakeQ, Q2R_0.
      change (to_Z 0) with 0%Z. destruct (Z.ltb_spec j 0); [lia | reflexivity].
    - intros e c He [Hc P]. change (to_Z 0) with 0%Z in He. split; [rewrite lsetQ; exact Hc|].
      intros j Hj. destruct (Z.eq_dec j (to_Z e)) as [Eq|Nq].
      + subst j. rewrite of_Z_to_Z, gssQ by lia. rewrite Q2R_inject, zofi_spec.
        destruct (Z.ltb_spec (to_Z e) (to_Z e + 1)); [|lia]. destruct neg; [apply opp_IZR | reflexivity].
      + rewrite gsoZQ by (rewrite to_Z_of_Z_small by (rewrite wB_val; lia); lia). rewrite P by exact Hj.
        destruct (Z.ltb_spec j (to_Z e)); destruct (Z.ltb_spec j (to_Z e + 1)); try reflexivity; lia. }
  exact G.
Qed.

Section Sem.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.
Hypothesis Rrs : repr xrs rs.
Hypothesis Rrd : repr xrd rd.
Hypothesis Rrt : repr xrt rt.
Hypothesis Rqs : repr xqs qs.
Hypothesis Rqd : repr xqd qd.

Local Notation n := (PArray.length xdist).
Local Notation nn := (len dist).
Local Notation W := (flatten (PArray.length xdist) xdist).
Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).
Local Notation RR := (PArray.length xrs).
Local Notation Et := (Z.to_nat (to_Z E)).
Local Notation Rt := (Z.to_nat (to_Z RR)).

Lemma RR_val : to_Z RR = Z.of_N (len rs).
Proof. exact (repr_uint_len xrs rs Rrs). Qed.

Lemma Rt_val : Rt = List.length rs.
Proof. rewrite RR_val. unfold len. lia. Qed.

Lemma Hg : guard E RR = true.
Proof.
  pose proof (E_le dist rs rd rt qs qd xdist Hv Rd) as HE. pose proof RR_val as HR.
  destruct (vi_r _ _ _ _ _ _ Hv) as [R1 R2].
  pose proof (to_Z_bounded E).
  apply guard_true; try lia.
  assert (0 <= (to_Z E + to_Z RR) * (2 * to_Z E + to_Z RR + 1) <= 1000 * 1901)%Z
    by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg]; lia).
  lia.
Qed.

Definition pe (e : nat) : Z := to_Z P.[of_Z (Z.of_nat e)].
Definition rA (e : nat) : N := Z.to_N (pe e / to_Z n).
Definition rB (e : nat) : N := Z.to_N (pe e mod to_Z n).
Definition idx (a b : N) : nat := Z.to_nat (dN n I a b).
Definition uR (e : nat) : R := IZR (ue W P (Z.of_nat e)).

Lemma road_e : forall e, (e < Et)%nat ->
  road dist (rA e) (rB e) /\ ue W P (Z.of_nat e) = entry dist (rA e) (rB e) /\ idx (rA e) (rB e) = e.
Proof.
  intros e He. pose proof (n_val dist xdist Rd) as En. pose proof (n_bounds dist rs rd rt qs qd xdist Hv Rd) as Bn.
  destruct (scan_facts dist rs rd rt qs qd xdist Hv Rd) as (_ & _ & _ & _ & S2).
  destruct (S2 (Z.of_nat e) ltac:(lia)) as (B1 & B2 & B3). fold (pe e) in B1.
  assert (Ep : pe e = (Z.of_N (rA e) * to_Z n + Z.of_N (rB e))%Z).
  { unfold rA, rB. pose proof (Z.div_mod (pe e) (to_Z n) ltac:(lia)).
    pose proof (Z.mod_pos_bound (pe e) (to_Z n) ltac:(lia)). pose proof (Z.div_pos (pe e) (to_Z n) ltac:(lia) ltac:(lia)).
    rewrite !Z2N.id by lia. lia. }
  assert (HaN : (rA e < nn)%N).
  { unfold rA. assert (pe e / to_Z n < to_Z n)%Z by (apply Z.div_lt_upper_bound; lia).
    pose proof (Z.div_pos (pe e) (to_Z n) ltac:(lia) ltac:(lia)). lia. }
  assert (HbN : (rB e < nn)%N).
  { unfold rB. pose proof (Z.mod_pos_bound (pe e) (to_Z n) ltac:(lia)). lia. }
  assert (EP : P.[of_Z (Z.of_nat e)] = of_Z (Z.of_N (rA e) * to_Z n + Z.of_N (rB e))).
  { rewrite <- Ep. unfold pe. rewrite of_Z_to_Z. reflexivity. }
  rewrite EP in B2, B3.
  split; [apply (isroad_iff dist n W (W_spec dist rs rd rt qs qd xdist Hv Rd)); assumption|].
  split.
  - unfold ue. rewrite EP, B2. rewrite zofs_spec. apply (W_spec dist rs rd rt qs qd xdist Hv Rd); assumption.
  - unfold idx, dN. rewrite B3. lia.
Qed.

Lemma idx_road : forall a b, road dist a b ->
  (idx a b < Et)%nat /\ rA (idx a b) = a /\ rB (idx a b) = b.
Proof.
  intros a b R. pose proof R as (Ha & Hb & _).
  pose proof (n_val dist xdist Rd) as En. pose proof (n_bounds dist rs rd rt qs qd xdist Hv Rd) as Bn.
  destruct (scan_facts dist rs rd rt qs qd xdist Hv Rd) as (_ & _ & _ & S1 & _).
  pose proof (pos_lt dist xdist Rd a b Ha Hb) as Hp.
  destruct (S1 _ Hp) as [L1 L2].
  { apply (isroad_iff dist n W (W_spec dist rs rd rt qs qd xdist Hv Rd)); assumption. }
  assert (Ei : of_Z (Z.of_nat (idx a b)) = I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)]).
  { unfold idx, dN. rewrite Z2Nat.id by (apply to_Z_bounded). apply of_Z_to_Z. }
  assert (Epe : pe (idx a b) = (Z.of_N a * to_Z n + Z.of_N b)%Z) by (unfold pe; rewrite Ei; exact L2).
  split; [unfold idx, dN; pose proof (to_Z_bounded (I.[of_Z (Z.of_N a * to_Z n + Z.of_N b)])); clear - L1 H; lia|].
  unfold rA, rB. rewrite Epe. assert (Ha' : (Z.of_N a < to_Z n)%Z) by (clear - Ha En; lia). assert (Hb' : (Z.of_N b < to_Z n)%Z) by (clear - Hb En; lia).
  clear - Ha' Hb' Bn. split.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma uR_pos : forall e, (e < Et)%nat -> (1 <= uR e <= 1000)%R.
Proof.
  intros e He. destruct (road_e e He) as (R & Eu & _). unfold uR. rewrite Eu.
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R). split; apply IZR_le; lia.
Qed.


Local Notation T0 := (build_T n E RR W D X I P xrs xrd xrt).
Local Notation t0 := (cell (build_T n E RR W D X I P xrs xrd xrt) (E + (E + RR) + 1)).
Local Notation mn := (Z.to_nat (to_Z (E + RR))).
Local Notation A0n := (Z.to_nat (to_Z (E + E))).
Local Notation Ck := (cnt_k n E D X I xrs xrd).
Local Notation bK := (b_k n D xrs xrd xrt).

Lemma A0n_val : A0n = (Et + Et)%nat.
Proof.
  pose proof (E_le dist rs rd rt qs qd xdist Hv Rd) as HE. pose proof (to_Z_bounded E).
  assert (to_Z (E + E) = to_Z E + to_Z E)%Z by (rewrite add_spec; apply Z.mod_small; rewrite wB_val; lia).
  lia.
Qed.

Lemma mn_eq : mn = (Et + Rt)%nat.
Proof. apply (mn_val E RR Hg). Qed.

Lemma cntsum_nonneg : forall cnt z, (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e])%Z) ->
  (forall e, (e < Et)%nat -> (0 <= z e)%R) -> (0 <= cntsum E cnt z)%R.
Proof.
  intros cnt z Hc Hz. unfold cntsum. apply sumR_nonneg. intros e He. apply Rmult_le_pos; [|apply Hz; exact He].
  apply IZR_le. apply Hc. clear - He. lia.
Qed.

Lemma cntsum_le : forall cnt z z', (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z cnt.[of_Z e])%Z) ->
  (forall e, (e < Et)%nat -> (z e <= z' e)%R) -> (cntsum E cnt z <= cntsum E cnt z')%R.
Proof.
  intros cnt z z' Hc Hz. unfold cntsum. apply sumR_le. intros e He. apply Rmult_le_compat_l; [|apply Hz; exact He].
  apply IZR_le. apply Hc. clear - He. lia.
Qed.

Lemma cntsum_ext : forall cnt z z', (forall e, (e < Et)%nat -> z e = z' e) -> cntsum E cnt z = cntsum E cnt z'.
Proof. intros cnt z z' H. unfold cntsum. apply sumR_ext. intros e He. rewrite H by exact He. reflexivity. Qed.

Lemma sumR_term : forall n0 f k, (forall j, (j < n0)%nat -> (0 <= f j)%R) -> (k < n0)%nat -> (f k <= sumR n0 f)%R.
Proof.
  induction n0; intros f k Hf Hk; [lia|]. simpl. destruct (Nat.eq_dec k n0) as [->|Nk].
  - pose proof (sumR_nonneg n0 f ltac:(intros; apply Hf; lia)). lra.
  - pose proof (IHn0 f k ltac:(intros; apply Hf; lia) ltac:(lia)). pose proof (Hf n0 ltac:(lia)). lra.
Qed.

(* a trip of the input: two cities with a unique shortest route *)
Definition TripOK (s d : int) : Prop :=
  (toN s < nn)%N /\ (toN d < nn)%N /\ unique_shortest_route dist (toN s) (toN d).

Lemma TripOK_intro : forall s d a b, toN s = a -> toN d = b -> (a < nn)%N -> (b < nn)%N ->
  unique_shortest_route dist a b -> TripOK s d.
Proof. intros s d a b Ea Eb Ha Hb U. subst a b. split; [exact Ha|]. split; [exact Hb | exact U]. Qed.

Lemma deliv_ok : forall k, (k < Rt)%nat ->
  TripOK xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)] /\
  toN xrs.[of_Z (Z.of_nat k)] = get_list_N rs (N.of_nat k) /\
  toN xrd.[of_Z (Z.of_nat k)] = get_list_N rd (N.of_nat k) /\
  Z.to_N (to_Z xrt.[of_Z (Z.of_nat k)]) = get_list_N rt (N.of_nat k).
Proof.
  intros k Hk. rewrite Rt_val in Hk.
  pose proof (vi_rd _ _ _ _ _ _ Hv) as Ld. pose proof (vi_rt _ _ _ _ _ _ Hv) as Lt. unfold len in Ld, Lt.
  assert (Es : toN xrs.[of_Z (Z.of_nat k)] = get_list_N rs (N.of_nat k)) by (apply repr_uint_nth; assumption).
  assert (Ed : toN xrd.[of_Z (Z.of_nat k)] = get_list_N rd (N.of_nat k)) by (apply repr_uint_nth; [assumption | lia]).
  assert (Et' : Z.to_N (to_Z xrt.[of_Z (Z.of_nat k)]) = get_list_N rt (N.of_nat k)) by (apply repr_uint_nth; [assumption | lia]).
  split; [|auto].
  destruct (vi_r_cities _ _ _ _ _ _ Hv (N.of_nat k) ltac:(unfold len; lia)) as [C1 C2].
  pose proof (vi_r_unique _ _ _ _ _ _ Hv (N.of_nat k) ltac:(unfold len; lia)) as U.
  eapply TripOK_intro; [exact Es | exact Ed | exact C1 | exact C2 | exact U].
Qed.

Lemma query_ok : forall j, (j < List.length qs)%nat ->
  TripOK xqs.[of_Z (Z.of_nat j)] xqd.[of_Z (Z.of_nat j)] /\
  toN xqs.[of_Z (Z.of_nat j)] = get_list_N qs (N.of_nat j) /\
  toN xqd.[of_Z (Z.of_nat j)] = get_list_N qd (N.of_nat j).
Proof.
  intros j Hj.
  pose proof (vi_qd _ _ _ _ _ _ Hv) as Ld. unfold len in Ld.
  assert (Es : toN xqs.[of_Z (Z.of_nat j)] = get_list_N qs (N.of_nat j)) by (apply repr_uint_nth; assumption).
  assert (Ed : toN xqd.[of_Z (Z.of_nat j)] = get_list_N qd (N.of_nat j)) by (apply repr_uint_nth; [assumption | lia]).
  split; [|auto].
  destruct (vi_q_cities _ _ _ _ _ _ Hv (N.of_nat j) ltac:(unfold len; lia)) as [C1 C2].
  pose proof (vi_q_unique _ _ _ _ _ _ Hv (N.of_nat j) ltac:(unfold len; lia)) as U.
  eapply TripOK_intro; [exact Es | exact Ed | exact C1 | exact C2 | exact U].
Qed.

Definition RC (s d : int) := route_cnt n E D X I s d.
Definition Dsd (s d : int) : Z := dN n D (toN s) (toN d).

Lemma trip_facts : forall s d, TripOK s d ->
  to_Z (PArray.length (RC s d)) = to_Z E /\
  (forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (RC s d).[of_Z e] <= to_Z INF)%Z) /\
  exists p, shortest_route dist (toN s) (toN d) p /\ distance dist p = Dsd s d /\
    (forall p', shortest_route dist (toN s) (toN d) p' -> p' = p) /\
    forall z, cntsum E (RC s d) z = psumR (fun a b => z (idx a b)) p.
Proof.
  intros s d (Hs & Hd & U). apply (route_cnt_spec dist rs rd rt qs qd xdist Hv Rd s d Hs Hd U).
Qed.

Lemma Dsd_get : forall s d, TripOK s d -> to_Z D.[s * n + d] = Dsd s d.
Proof.
  intros s d (Hs & Hd & _). unfold Dsd, dN. pose proof (n_val dist xdist Rd) as En.
  pose proof (n_le dist rs rd rt qs qd xdist Hv Rd) as Hn.
  rewrite (get_idx n Hn); [reflexivity | |]; unfold toN in *; pose proof (to_Z_bounded s); pose proof (to_Z_bounded d);
    clear - Hs Hd En H H0; lia.
Qed.

Lemma bK_val : forall k, (k < Rt)%nat ->
  bK k = (Z.of_N (get_list_N rt (N.of_nat k)) - Dsd xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)])%Z.
Proof.
  intros k Hk. destruct (deliv_ok k Hk) as (T & _ & _ & Et').
  unfold b_k, bk. rewrite !zofi_spec. rewrite Dsd_get by exact T. rewrite <- Et'.
  rewrite Z2N.id; [reflexivity | apply to_Z_bounded].
Qed.

Lemma Ck_eq : forall k, Ck k = RC xrs.[of_Z (Z.of_nat k)] xrd.[of_Z (Z.of_nat k)].
Proof. reflexivity. Qed.


Lemma Ck_facts : forall k, (k < Rt)%nat ->
  forall e, (0 <= e < to_Z E)%Z -> (0 <= to_Z (Ck k).[of_Z e])%Z.
Proof.
  intros k Hk e He. rewrite Ck_eq. destruct (deliv_ok k Hk) as (T & _).
  destruct (trip_facts _ _ T) as (_ & B & _). apply B. exact He.
Qed.

Lemma uR_nonneg : forall e, (e < Et)%nat -> (0 <= uR e)%R.
Proof. intros e He. pose proof (uR_pos e He). lra. Qed.

Definition zext (x : nat -> R) (j : nat) : R :=
  if Nat.ltb j Et then x j else if Nat.ltb j (Et + Et) then (uR (j - Et)%nat - x (j - Et)%nat)%R else 0%R.

Lemma sg_abs : forall b c, (sg b * c = IZR (Z.abs b))%R <-> c = IZR b.
Proof.
  intros b c. unfold sg. destruct (Z.ltb_spec b 0).
  - rewrite Z.abs_neq by lia. rewrite opp_IZR. split; intros; lra.
  - rewrite Z.abs_eq by lia. split; intros; lra.
Qed.

Lemma feas_x : forall z, Feas mn Et t0 A0n z ->
  (forall e, (e < Et)%nat -> (0 <= z e <= uR e)%R) /\
  (forall k, (k < Rt)%nat -> cntsum E (Ck k) z = IZR (bK k)) /\
  (forall j, (j < Et + (Et + Rt))%nat -> (0 <= z j)%R).
Proof.
  intros z (S & Pz & Az). unfold Sol in S. rewrite mn_eq in S, Pz, Az. rewrite A0n_val in Az.
  split; [|split; [|exact Pz]].
  - intros e He. pose proof (S e ltac:(lia)) as Se.
    rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg e z He), (rhs_bound n E RR W D X I P xrs xrd xrt Hg e He) in Se.
    pose proof (Pz e ltac:(lia)). pose proof (Pz (Et + e)%nat ltac:(lia)). unfold uR. lra.
  - intros k Hk. pose proof (S (Et + k)%nat ltac:(lia)) as Sk.
    rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg k z Hk), (rhs_deliv n E RR W D X I P xrs xrd xrt Hg k Hk) in Sk.
    rewrite (Az (Et + Et + k)%nat ltac:(lia) ltac:(lia)) in Sk. rewrite Rplus_0_r in Sk.
    apply sg_abs. exact Sk.
Qed.

Lemma cntsum_zext : forall cnt x, cntsum E cnt (zext x) = cntsum E cnt x.
Proof.
  intros cnt x. apply cntsum_ext. intros e He. unfold zext. destruct (Nat.ltb_spec e Et); [reflexivity | lia].
Qed.

Lemma x_feas : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) ->
  (forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k)) ->
  Feas mn Et t0 A0n (zext x).
Proof.
  intros x Hx Hd. unfold Feas, Sol. rewrite mn_eq, A0n_val. split; [|split].
  - intros r Hr. destruct (Nat.ltb_spec r Et).
    + rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg r _ H), (rhs_bound n E RR W D X I P xrs xrd xrt Hg r H).
      unfold zext. destruct (Nat.ltb_spec r Et); [|lia]. destruct (Nat.ltb_spec (Et + r) Et); [lia|].
      destruct (Nat.ltb_spec (Et + r) (Et + Et)); [|lia]. replace (Et + r - Et)%nat with r by lia.
      unfold uR. ring.
    + replace r with (Et + (r - Et))%nat by lia.
      rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg (r - Et) _ ltac:(lia)),
              (rhs_deliv n E RR W D X I P xrs xrd xrt Hg (r - Et) ltac:(lia)).
      rewrite cntsum_zext. rewrite Hd by lia.
      unfold zext. destruct (Nat.ltb_spec (Et + Et + (r - Et)) Et); [lia|].
      destruct (Nat.ltb_spec (Et + Et + (r - Et)) (Et + Et)); [lia|].
      rewrite Rplus_0_r. apply sg_abs. reflexivity.
  - intros j Hj. unfold zext. destruct (Nat.ltb_spec j Et); [apply Hx; exact H|].
    destruct (Nat.ltb_spec j (Et + Et)); [|lra]. pose proof (Hx (j - Et)%nat ltac:(lia)). lra.
  - intros j Hj1 Hj2. unfold zext. destruct (Nat.ltb_spec j Et); [lia|].
    destruct (Nat.ltb_spec j (Et + Et)); [lia | reflexivity].
Qed.

Definition Mb : R :=
  (sumR Et uR + sumR Rt (fun k => IZR (Z.abs (bK k)) + cntsum E (Ck k) uR))%R.

Lemma bounded : Bounded mn Et t0 Mb.
Proof.
  intros z S Pz j Hj. rewrite mn_eq in Hj, Pz. unfold Sol in S. rewrite mn_eq in S.
  assert (Bu : forall e, (e < Et)%nat -> (z e <= uR e)%R).
  { intros e He. pose proof (S e ltac:(lia)) as Se.
    rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg e z He), (rhs_bound n E RR W D X I P xrs xrd xrt Hg e He) in Se.
    pose proof (Pz (Et + e)%nat ltac:(lia)). unfold uR. lra. }
  assert (Pk : forall k, (k < Rt)%nat -> (0 <= IZR (Z.abs (bK k)) + cntsum E (Ck k) uR)%R).
  { intros k Hk. pose proof (IZR_le 0 _ (Z.abs_nonneg (bK k))).
    pose proof (cntsum_nonneg (Ck k) uR (Ck_facts k Hk) uR_nonneg). lra. }
  assert (S1 : (0 <= sumR Et uR)%R) by (apply sumR_nonneg; exact uR_nonneg).
  assert (S2 : (0 <= sumR Rt (fun k => IZR (Z.abs (bK k)) + cntsum E (Ck k) uR))%R) by (apply sumR_nonneg; exact Pk).
  unfold Mb.
  destruct (Nat.ltb_spec j Et).
  - pose proof (Bu j H). pose proof (sumR_term Et uR j uR_nonneg H). lra.
  - destruct (Nat.ltb_spec j (Et + Et)).
    + pose proof (S (j - Et)%nat ltac:(lia)) as Se.
      rewrite (lin_bound n E RR W D X I P xrs xrd xrt Hg (j - Et) z ltac:(lia)),
              (rhs_bound n E RR W D X I P xrs xrd xrt Hg (j - Et) ltac:(lia)) in Se.
      replace (Et + (j - Et))%nat with j in Se by lia.
      pose proof (Pz (j - Et)%nat ltac:(lia)). pose proof (sumR_term Et uR (j - Et) uR_nonneg ltac:(lia)).
      unfold uR in *. lra.
    + set (k := (j - Et - Et)%nat). assert (Hk : (k < Rt)%nat) by (unfold k; lia).
      pose proof (S (Et + k)%nat ltac:(lia)) as Sk.
      rewrite (lin_deliv n E RR W D X I P xrs xrd xrt Hg k z Hk), (rhs_deliv n E RR W D X I P xrs xrd xrt Hg k Hk) in Sk.
      replace (Et + Et + k)%nat with j in Sk by (unfold k; lia).
      pose proof (cntsum_nonneg (Ck k) z (Ck_facts k Hk) (fun e He => Pz e ltac:(lia))) as C0.
      pose proof (cntsum_le (Ck k) z uR (Ck_facts k Hk) Bu) as C1.
      pose proof (sumR_term Rt _ k Pk Hk) as T. cbv beta in T.
      assert (Hs : (- cntsum E (Ck k) z <= sg (bK k) * cntsum E (Ck k) z)%R).
      { unfold sg. destruct (Z.ltb (bK k) 0); lra. }
      lra.
Qed.

Definition xv (v : N -> N -> R) (e : nat) : R := (60 * uR e / v (rA e) (rB e) - uR e)%R.
Definition vx (x : nat -> R) (a b : N) : R :=
  (60 * IZR (entry dist a b) / (IZR (entry dist a b) + x (idx a b)))%R.

Lemma xv_rel : forall v, forall a b, road dist a b ->
  (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + xv v (idx a b))%R.
Proof.
  intros v a b R. destruct (idx_road a b R) as (Hi & Ea & Eb). destruct (road_e _ Hi) as (_ & Eu & _).
  unfold xv, uR. rewrite Eu, Ea, Eb. ring.
Qed.

Lemma xv_bounds : forall v, speeds_ok dist v -> forall e, (e < Et)%nat -> (0 <= xv v e <= uR e)%R.
Proof.
  intros v Hs e He. destruct (road_e e He) as (R & _ & _). pose proof (Hs _ _ R) as Hv'.
  pose proof (uR_pos e He). unfold xv. set (u := uR e) in *. set (vv := v (rA e) (rB e)) in *.
  assert (A : (60 * u / vv = u * (60 / vv))%R) by (field; lra). rewrite A.
  assert (B1 : (1 <= 60 / vv)%R) by (apply (Rmult_le_reg_r vv); [lra|]; field_simplify; lra).
  assert (B2 : (60 / vv <= 2)%R) by (apply (Rmult_le_reg_r vv); [lra|]; field_simplify; lra).
  split; nra.
Qed.

Lemma vx_rel : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) ->
  forall a b, road dist a b ->
  (60 * IZR (entry dist a b) / vx x a b = IZR (entry dist a b) + x (idx a b))%R.
Proof.
  intros x Hx a b R. destruct (idx_road a b R) as (Hi & _ & _). pose proof (Hx _ Hi).
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R) as Re. pose proof (IZR_le 1 _ (proj1 Re)).
  unfold vx. field. lra.
Qed.

Lemma vx_speeds : forall x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) -> speeds_ok dist (vx x).
Proof.
  intros x Hx a b R. destruct (idx_road a b R) as (Hi & Ea & Eb). pose proof (Hx _ Hi) as Bx.
  destruct (road_e _ Hi) as (_ & Eu & _). unfold uR in Bx. rewrite Eu, Ea, Eb in Bx.
  pose proof (road_le dist rs rd rt qs qd Hv _ _ R) as Re. pose proof (IZR_le 1 _ (proj1 Re)).
  unfold vx. set (e := IZR (entry dist a b)) in *. set (y := x (idx a b)) in *.
  split.
  - apply (Rmult_le_reg_r (e + y)); [lra|]. field_simplify; lra.
  - apply (Rmult_le_reg_r (e + y)); [lra|]. field_simplify; lra.
Qed.

Lemma trip_dur : forall s d, TripOK s d -> forall (v : N -> N -> R) (x : nat -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + x (idx a b))%R) ->
  forall t, trip_takes dist v (toN s) (toN d) t <-> t = (IZR (Dsd s d) + cntsum E (RC s d) x)%R.
Proof.
  intros s d T v x Hr t. destruct (trip_facts s d T) as (_ & _ & p & Sh & Dp & Un & Cs).
  pose proof (dur_gen dist v (fun a b => x (idx a b)) Hr _ _ _ (proj1 Sh)) as Du.
  rewrite Cs, <- Dp. split.
  - intros H. rewrite <- (H p Sh). exact Du.
  - intros -> p' Sh'. rewrite (Un p' Sh'). exact Du.
Qed.

Lemma deliv_iff : forall (v : N -> N -> R) (x : nat -> R),
  (forall a b, road dist a b -> (60 * IZR (entry dist a b) / v a b = IZR (entry dist a b) + x (idx a b))%R) ->
  matches_deliveries dist rs rd rt v <-> forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k).
Proof.
  intros v x Hr. unfold matches_deliveries. split.
  - intros H k Hk. destruct (deliv_ok k Hk) as (T & Es & Ed & Et').
    pose proof (H (N.of_nat k) ltac:(rewrite Rt_val in Hk; unfold len; lia)) as Hk'.
    rewrite <- Es, <- Ed in Hk'. apply (trip_dur _ _ T v x Hr) in Hk'.
    rewrite Ck_eq, bK_val by exact Hk. rewrite minus_IZR. lra.
  - intros H k Hk. set (kn := N.to_nat k). assert (Ek : k = N.of_nat kn) by (unfold kn; lia).
    assert (Hkn : (kn < Rt)%nat) by (rewrite Rt_val; unfold len in Hk; lia).
    destruct (deliv_ok kn Hkn) as (T & Es & Ed & Et'). rewrite Ek, <- Es, <- Ed.
    apply (trip_dur _ _ T v x Hr). pose proof (H kn Hkn) as Hc. rewrite Ck_eq, bK_val in Hc by exact Hkn.
    rewrite minus_IZR in Hc. lra.
Qed.

Lemma possible_iff : forall s d, TripOK s d -> forall t,
  possible dist rs rd rt (toN s) (toN d) t <->
  exists x, (forall e, (e < Et)%nat -> (0 <= x e <= uR e)%R) /\
    (forall k, (k < Rt)%nat -> cntsum E (Ck k) x = IZR (bK k)) /\
    t = (IZR (Dsd s d) + cntsum E (RC s d) x)%R.
Proof.
  intros s d T t. split.
  - intros (v & Hs & Hm & Ht). exists (xv v). split; [apply xv_bounds; exact Hs|].
    split; [apply (deliv_iff v (xv v) (xv_rel v)); exact Hm|].
    apply (trip_dur _ _ T v (xv v) (xv_rel v)). exact Ht.
  - intros (x & Hb & Hd & Ht). exists (vx x). split; [apply vx_speeds; exact Hb|].
    split; [apply (deliv_iff (vx x) x (vx_rel x Hb)); exact Hd|].
    apply (trip_dur _ _ T (vx x) x (vx_rel x Hb)). exact Ht.
Qed.

Lemma feas_exists : exists x0, Feas mn Et t0 A0n x0.
Proof.
  destruct (vi_consistent _ _ _ _ _ _ Hv) as (v & Hs & Hm).
  exists (zext (xv v)). apply x_feas; [apply xv_bounds; exact Hs|].
  apply (deliv_iff v (xv v) (xv_rel v)). exact Hm.
Qed.


Local Notation w := (E + (E + RR) + 1).
Local Notation NN := (E + (E + RR)).

Lemma w_facts : (to_Z E < to_Z w)%Z /\ (to_Z w <= 4194303)%Z /\ to_Z w = (2 * to_Z E + to_Z RR + 1)%Z.
Proof.
  pose proof (w_val' E RR Hg) as Ew. pose proof (E_le dist rs rd rt qs qd xdist Hv Rd).
  pose proof RR_val. destruct (vi_r _ _ _ _ _ _ Hv). pose proof (to_Z_bounded RR). lia.
Qed.

Lemma cost_eq : forall cnt neg z,
  sumR (Et + mn) (fun j => (ovec (qcost E w cnt neg) j * z j)%R) =
  (if neg then - cntsum E cnt z else cntsum E cnt z)%R.
Proof.
  intros cnt neg z. destruct w_facts as (W1 & W2 & W3).
  destruct (qcost_spec E w cnt neg W1 W2) as [_ Pc].
  rewrite mn_eq. rewrite sumR_split.
  rewrite (sumR_zero (Et + Rt)).
  2:{ intros i Hi. unfold ovec. rewrite Pc by (pose proof (to_Z_bounded E); pose proof RR_val; clear - Hi W3 H H0; lia).
      destruct (Z.ltb_spec (Z.of_nat (Et + i)) (to_Z E)); [lia | ring]. }
  rewrite Rplus_0_r. unfold cntsum.
  assert (Ex : forall j, (j < Et)%nat -> (ovec (qcost E w cnt neg) j * z j =
      (if neg then -1 else 1) * (IZR (to_Z cnt.[of_Z (Z.of_nat j)]) * z j))%R).
  { intros j Hj. unfold ovec. rewrite Pc by (pose proof (to_Z_bounded E); clear - Hj W1; lia).
    destruct (Z.ltb_spec (Z.of_nat j) (to_Z E)); [|lia]. destruct neg; ring. }
  rewrite (sumR_ext _ _ _ Ex), sumR_scal. destruct neg; ring.
Qed.

Lemma carr_N : forall cnt neg, Q2R (qcost E w cnt neg).[NN] = 0%R.
Proof.
  intros cnt neg. destruct w_facts as (W1 & W2 & W3). destruct (qcost_spec E w cnt neg W1 W2) as [_ Pc].
  pose proof (N_val' E RR Hg) as EN.
  pose proof (Pc (to_Z NN) ltac:(pose proof (to_Z_bounded NN); lia)) as H. rewrite of_Z_to_Z in H. rewrite H.
  destruct (Z.ltb_spec (to_Z NN) (to_Z E)); [|reflexivity].
  pose proof (to_Z_bounded RR). lia.
Qed.

Lemma carr_len : forall cnt neg, to_Z (PArray.length (qcost E w cnt neg)) = to_Z w.
Proof. intros cnt neg. destruct w_facts as (W1 & W2 & _). apply (qcost_spec E w cnt neg W1 W2). Qed.

Lemma psum_u : forall s d p, route dist s d p ->
  psumR (fun a b => uR (idx a b)) p = IZR (distance dist p).
Proof.
  intros s d p R. induction R as [s Hs | s m d p Rr Rp IH].
  - simpl. reflexivity.
  - destruct (route_head dist _ _ _ Rp) as [tl ->]. rewrite distance_cons2. simpl psumR.
    simpl psumR in IH. rewrite IH. destruct (idx_road _ _ Rr) as (Hi & Ea & Eb).
    destruct (road_e _ Hi) as (_ & Eu & _). unfold uR. rewrite Eu, Ea, Eb. rewrite plus_IZR. reflexivity.
Qed.

Section Q.
Variable Hp : P1ok T0 (E + RR) E (E + E).

Local Notation st1 := (phase1 T0 (E + RR) E (E + E) Hp).
Local Notation Hv1 := (phase1_VS T0 (E + RR) E (E + E) Hp).
Local Notation al := (al2 (sO (phase1 T0 (E + RR) E (E + E) Hp)) (E + E) NN).
Local Notation VQ := (vq n E RR D X I T0 Hp st1 Hv1 al).

Lemma vq_spec : forall (s d : int) (neg : bool),
  (exists z, Feas mn Et t0 A0n z /\
     (if neg then - cntsum E (RC s d) z else cntsum E (RC s d) z)%R = Q2R (VQ s d neg)) /\
  (forall z, Feas mn Et t0 A0n z ->
     (Q2R (VQ s d neg) <= if neg then - cntsum E (RC s d) z else cntsum E (RC s d) z)%R).
Proof.
  intros s d neg.
  assert (HA0 : (to_Z (E + E) <= to_Z E + to_Z (E + RR))%Z).
  { pose proof A0n_val. pose proof mn_eq. pose proof (to_Z_bounded (E + E)). pose proof (to_Z_bounded (E + RR)). lia. }
  pose proof (phase2_min T0 (E + RR) E (E + E) Hp HA0 Mb bounded feas_exists
                (qcost E w (route_cnt n E D X I s d) neg) (carr_len _ _) (carr_N _ _)) as G.
  cbv zeta in G. unfold p1st in G.
  destruct G as [[z [Fz Cz]] Lz]. split.
  - exists z. split; [exact Fz|]. rewrite <- cost_eq. exact Cz.
  - intros z' Fz'. rewrite <- cost_eq. exact (Lz z' Fz').
Qed.

Lemma query_sem : forall s d, TripOK s d ->
  least_possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) + Q2R (VQ s d false))%R /\
  greatest_possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) - Q2R (VQ s d true))%R /\
  (0 <= IZR (Dsd s d) + Q2R (VQ s d false))%R /\
  (IZR (Dsd s d) - Q2R (VQ s d true) <= 60000)%R /\
  (IZR (Dsd s d) + Q2R (VQ s d false) <= IZR (Dsd s d) - Q2R (VQ s d true))%R.
Proof.
  intros s d T.
  destruct (trip_facts s d T) as (_ & Cb & p & Sh & Dp & _ & Cs).
  destruct (vq_spec s d false) as [[z1 [F1 C1]] L1]. destruct (vq_spec s d true) as [[z2 [F2 C2]] L2].
  destruct (feas_x z1 F1) as (B1 & D1 & P1). destruct (feas_x z2 F2) as (B2 & D2 & P2).
  assert (Cn : forall z, (forall e, (e < Et)%nat -> (0 <= z e)%R) -> (0 <= cntsum E (RC s d) z)%R).
  { intros z Hz. apply cntsum_nonneg; [|exact Hz]. intros e He. apply Cb. exact He. }
  assert (Cu : forall z, (forall e, (e < Et)%nat -> (0 <= z e <= uR e)%R) ->
            (cntsum E (RC s d) z <= IZR (Dsd s d))%R).
  { intros z Hz. rewrite <- Dp. rewrite <- (psum_u _ _ _ (proj1 Sh)). rewrite <- Cs.
    apply cntsum_le; [intros e He; apply Cb; exact He|]. intros e He. apply Hz. exact He. }
  assert (Dn : (0 <= IZR (Dsd s d))%R).
  { rewrite <- Dp. apply IZR_le. apply (distance_nonneg dist _ _ _ (proj1 Sh)). }
  assert (Db : (IZR (Dsd s d) <= 29000)%R).
  { rewrite <- Dp. apply IZR_le. pose proof (shortest_bound dist rs rd rt qs qd Hv _ _ _ Sh).
    destruct (vi_n _ _ _ _ _ _ Hv). lia. }
  assert (Ex1 : possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) + Q2R (VQ s d false))%R).
  { apply (possible_iff s d T). exists z1. split; [exact B1|]. split; [exact D1|]. rewrite <- C1. reflexivity. }
  assert (Ex2 : possible dist rs rd rt (toN s) (toN d) (IZR (Dsd s d) - Q2R (VQ s d true))%R).
  { apply (possible_iff s d T). exists z2. split; [exact B2|]. split; [exact D2|]. rewrite <- C2. ring. }
  split.
  { split; [exact Ex1|]. intros t' Ht'. apply (possible_iff s d T) in Ht'. destruct Ht' as (x & Bx & Dx & ->).
    pose proof (L1 (zext x) (x_feas x Bx Dx)) as L. rewrite cntsum_zext in L. lra. }
  split.
  { split; [exact Ex2|]. intros t' Ht'. apply (possible_iff s d T) in Ht'. destruct Ht' as (x & Bx & Dx & ->).
    pose proof (L2 (zext x) (x_feas x Bx Dx)) as L. rewrite cntsum_zext in L. lra. }
  pose proof (Cn z1 (fun e He => proj1 (B1 e He))). pose proof (Cu z2 B2). pose proof (L1 z2 F2).
  rewrite <- C1, <- C2. split; [lra|]. split; lra.
Qed.

Lemma dq_R : forall s d, TripOK s d -> Q2R (dq n D s d) = IZR (Dsd s d).
Proof.
  intros s d T. unfold dq. rewrite Q2R_inject, zofi_spec. exact (f_equal IZR (Dsd_get s d T)).
Qed.

Local Notation QA := (qans n E RR D X I T0 Hp st1 Hv1 al).

Lemma qans_spec : forall s d, TripOK s d ->
  exists lo hi, least_possible dist rs rd rt (toN s) (toN d) lo /\
    greatest_possible dist rs rd rt (toN s) (toN d) hi /\
    repr (fst (QA s d)) (fval (fst (QA s d))) /\ repr (snd (QA s d)) (fval (snd (QA s d))) /\
    close (fval (fst (QA s d))) lo /\ close (fval (snd (QA s d))) hi.
Proof.
  intros s d T. destruct (query_sem s d T) as (Hl & Hh & B1 & B2 & B3).
  exists (IZR (Dsd s d) + Q2R (VQ s d false))%R, (IZR (Dsd s d) - Q2R (VQ s d true))%R.
  split; [exact Hl|]. split; [exact Hh|].
  assert (E1 : Q2R (Qplus (dq n D s d) (VQ s d false)) = (IZR (Dsd s d) + Q2R (VQ s d false))%R)
    by (rewrite Q2R_plus, dq_R by exact T; reflexivity).
  assert (E2 : Q2R (Qminus (dq n D s d) (VQ s d true)) = (IZR (Dsd s d) - Q2R (VQ s d true))%R)
    by (rewrite Q2R_minus, dq_R by exact T; reflexivity).
  destruct (q2f_spec (Qplus (dq n D s d) (VQ s d false)) ltac:(rewrite E1; lra)) as (r1 & R1 & L1).
  destruct (q2f_spec (Qminus (dq n D s d) (VQ s d true)) ltac:(rewrite E2; lra)) as (r2 & R2 & L2).
  unfold qans. simpl fst. simpl snd.
  assert (F1 : fval (q2f (Qplus (dq n D s d) (VQ s d false))) = r1) by (destruct R1; assumption).
  assert (F2 : fval (q2f (Qminus (dq n D s d) (VQ s d true))) = r2) by (destruct R2; assumption).
  rewrite F1, F2. split; [exact R1|]. split; [exact R2|].
  rewrite E1 in L1. rewrite E2 in L2. split; left; assumption.
Qed.

End Q.

End Sem.
End P_MS3.

(* ================================================================== *)
Section P_MF.
Open Scope uint63_scope.

Lemma lboundP : forall (t : array (float * float)), (to_Z (PArray.length t) <= 4194303)%Z.
Proof. intros t. pose proof (leb_length (float * float) t) as H. rewrite Uint63.leb_spec in H. exact H. Qed.

Lemma fill1P : forall (nq : int) (f : int -> array (float * float) -> array (float * float))
    (F : int -> float * float) (z0 : float * float),
  (forall j out, f j out = out.[j <- F j]) -> (to_Z nq <= 4194303)%Z ->
  PArray.length (forl 0 nq f (PArray.make nq z0)) = nq /\
  forall j, (to_Z j < to_Z nq)%Z -> (forl 0 nq f (PArray.make nq z0)).[j] = F j.
Proof.
  intros nq f F z0 Hf Hn.
  pose (Iv := fun kz (out : array (float * float)) => PArray.length out = nq /\
     forall j, (to_Z j < kz)%Z -> out.[j] = F j).
  assert (G : Iv (to_Z nq) (forl 0 nq f (PArray.make nq z0))).
  { apply (for_invZ Iv); unfold Iv.
    - change (to_Z 0) with 0%Z. pose proof (to_Z_bounded nq). lia.
    - split.
      + etransitivity; [exact (length_make _ nq z0)|]. replace (nq <=? max_length) with true; [reflexivity|].
        symmetry. rewrite Uint63.leb_spec. exact Hn.
      + intros j Hj. change (to_Z 0) with 0%Z in Hj. pose proof (to_Z_bounded j). lia.
    - intros j out Hj [HL P]. change (to_Z 0) with 0%Z in Hj. rewrite Hf. split.
      + etransitivity; [exact (length_set _ out j (F j)) | exact HL].
      + intros j' Hj'. destruct (Z.eq_dec (to_Z j') (to_Z j)) as [E|E].
        * apply to_Z_inj in E. subst j'. assert (Hlt : (j <? PArray.length out) = true) by (rewrite Uint63.ltb_spec, HL; lia).
          exact (get_set_same _ out j (F j) Hlt).
        * assert (Nj : j <> j') by (intros F'; apply E; rewrite F'; reflexivity).
          etransitivity; [exact (get_set_other _ out j j' (F j) Nj) | apply P; lia]. }
  exact G.
Qed.

Section Main.
Variables (dist : list (list Z)) (rs rd rt qs qd : list N).
Variables (xdist : array (array sint)) (xrs xrd xrt xqs xqd : array uint).
Hypothesis Hv : valid_input dist rs rd rt qs qd.
Hypothesis Rd : repr xdist dist.
Hypothesis Rrs : repr xrs rs.
Hypothesis Rrd : repr xrd rd.
Hypothesis Rrt : repr xrt rt.
Hypothesis Rqs : repr xqs qs.
Hypothesis Rqd : repr xqd qd.

Local Notation n := (PArray.length xdist).
Local Notation W := (flatten (PArray.length xdist) xdist).
Local Notation D := (fst (fw (PArray.length xdist) W)).
Local Notation X := (snd (fw (PArray.length xdist) W)).
Local Notation I := (fst (fst (scan_roads (PArray.length xdist) W))).
Local Notation P := (snd (fst (scan_roads (PArray.length xdist) W))).
Local Notation E := (snd (scan_roads (PArray.length xdist) W)).
Local Notation RR := (PArray.length xrs).
Local Notation T0 := (build_T n E RR W D X I P xrs xrd xrt).
Local Notation NN := (E + (E + RR)).

Lemma nq_val : to_Z (PArray.length xqs) = Z.of_nat (List.length qs).
Proof. pose proof (repr_uint_len xqs qs Rqs) as H. unfold len in H. etransitivity; [exact H | lia]. Qed.

Theorem main_correct : exists o : list (R * R),
  repr (roadtimes_impl xdist xrs xrd xrt xqs xqd) o /\ roadtimes_spec dist rs rd rt qs qd o.
Proof.
  unfold roadtimes_impl. cbv zeta.
  destruct (bdec (guard E RR)) as [Hg'|Hg'].
  2:{ exfalso. rewrite (Hg dist rs rd rt qs qd xdist xrs Hv Rd Rrs) in Hg'. discriminate. }
  unfold answers. cbv zeta.
  pose (Hp := build_ok n E RR W D X I P xrs xrd xrt Hg').
  pose (F := fun j => qans n E RR D X I T0 Hp (phase1 T0 (E + RR) E (E + E) Hp)
                       (phase1_VS T0 (E + RR) E (E + E) Hp) (al2 (sO (phase1 T0 (E + RR) E (E + E) Hp)) (E + E) NN)
                       (aget xqs j) (aget xqd j)).
  match goal with |- context [forl 0 ?nq ?f (PArray.make ?nq ?z0)] => set (ff := f) end.
  assert (Hf : forall j out, ff j out = out.[j <- F j]) by (intros j out; exact_no_check (eq_refl (ff j out))).
  destruct (fill1P (PArray.length xqs) ff F (PrimFloat.zero, PrimFloat.zero) Hf (lboundI xqs)) as [HL' HC'].
  set (out := forl 0 (PArray.length xqs) ff (PArray.make (PArray.length xqs) (PrimFloat.zero, PrimFloat.zero))) in *.
  pose (o := map (fun k => (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k))))))
                 (seq 0 (List.length qs))).
  assert (Lo : List.length o = List.length qs) by (unfold o; rewrite length_map, length_seq; reflexivity).
  assert (No : forall k, (k < List.length qs)%nat ->
            nth_error o k = Some (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))).
  { intros k Hk. unfold o. rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec k (List.length qs)); [reflexivity|lia]. }
  assert (Qk : forall k, (k < List.length qs)%nat ->
     exists lo hi, least_possible dist rs rd rt (get_list_N qs (N.of_nat k)) (get_list_N qd (N.of_nat k)) lo /\
       greatest_possible dist rs rd rt (get_list_N qs (N.of_nat k)) (get_list_N qd (N.of_nat k)) hi /\
       repr (fst (F (of_Z (Z.of_nat k)))) (fval (fst (F (of_Z (Z.of_nat k))))) /\
       repr (snd (F (of_Z (Z.of_nat k)))) (fval (snd (F (of_Z (Z.of_nat k))))) /\
       close (fval (fst (F (of_Z (Z.of_nat k))))) lo /\ close (fval (snd (F (of_Z (Z.of_nat k))))) hi).
  { intros k Hk. destruct (query_ok dist rs rd rt qs qd xqs xqd Hv Rqs Rqd k Hk) as (T & Es & Ed).
    assert (T' : TripOK dist (aget xqs (of_Z (Z.of_nat k))) (aget xqd (of_Z (Z.of_nat k)))) by exact T.
    assert (Es' : toN (aget xqs (of_Z (Z.of_nat k))) = get_list_N qs (N.of_nat k)) by exact Es.
    assert (Ed' : toN (aget xqd (of_Z (Z.of_nat k))) = get_list_N qd (N.of_nat k)) by exact Ed.
    destruct (qans_spec dist rs rd rt qs qd xdist xrs xrd xrt Hv Rd Rrs Rrd Rrt Hp _ _ T')
      as (lo & hi & H1 & H2 & H3 & H4 & H5 & H6).
    rewrite Es', Ed' in H1, H2.
    exists lo, hi. exact_no_check (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 H6))))). }
  exists o. split.
  - split.
    + rewrite Lo. rewrite <- nq_val. exact_no_check (f_equal to_Z (eq_sym HL')).
    + intros k Hk. rewrite Lo in Hk. eexists. split; [apply No; exact Hk|].
      destruct (Qk k Hk) as (lo & hi & _ & _ & R1 & R2 & _).
      assert (Hk' : (to_Z (of_Z (Z.of_nat k)) < to_Z (PArray.length xqs))%Z).
      { pose proof nq_val. rewrite to_Z_of_Z_small by (rewrite wB_val; pose proof (lboundI xqs); lia). lia. }
      pose proof (HC' _ Hk') as Ek.
      assert (Rp : repr (F (of_Z (Z.of_nat k)))
                        (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))) by (split; assumption).
      exact_no_check (eq_ind_r (fun c => repr c (fval (fst (F (of_Z (Z.of_nat k)))), fval (snd (F (of_Z (Z.of_nat k)))))) Rp Ek).
  - split.
    + unfold len. rewrite Lo. reflexivity.
    + intros j Hj. unfold len in Hj. set (k := N.to_nat j).
      assert (Hk : (k < List.length qs)%nat) by (unfold k; lia).
      destruct (Qk k Hk) as (lo & hi & H1 & H2 & _ & _ & H5 & H6).
      replace (N.of_nat k) with j in H1, H2 by (unfold k; lia).
      exists lo, hi. split; [exact H1|]. split; [exact H2|].
      rewrite (nth_error_nth o k (0%R, 0%R) (No k Hk)). simpl fst; simpl snd. split; assumption.
Qed.

End Main.
End P_MF.

(* ================================================================== *)
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition roadtimes : array (array sint) -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array (float * float) := roadtimes_impl.

Definition roadtimes_correct :
  forall (dist : list (list Z)) (rs rd rt qs qd : list N)
         (xdist : array (array sint))
         (xrs xrd xrt xqs xqd : array uint),
    valid_input dist rs rd rt qs qd ->
    repr xdist dist -> repr xrs rs -> repr xrd rd -> repr xrt rt ->
    repr xqs qs -> repr xqd qd ->
    exists o : list (R * R),
      repr (roadtimes xdist xrs xrd xrt xqs xqd) o /\
      roadtimes_spec dist rs rd rt qs qd o
  := main_correct.
