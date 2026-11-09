(* Executable implementation and its required termination dependencies.
   Correctness proofs are in roadtimes_proofs.v. *)
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
From Roadtimes.spec Require Import Prelude.
From Stdlib Require Import Uint63 PArray ZifyUint63 Arith ZArith NArith List Bool Lia Zwf.
From Stdlib Require Import Reals Lra QArith Qreals PrimFloat ListDec Decidable.
From Stdlib Require Sint63.
From StdGalilei Require Import repr.
From StdGalilei Require Import bigint repr_float.
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
(* The spec's items, at top level                                      *)
(* ================================================================== *)

Definition roadtimes : array (array sint) -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array (float * float) := roadtimes_impl.
