(* Executable implementation and its required termination dependencies.
   Correctness proofs are in unionfind_proofs.v. *)
(* Implementation of unionfind (unionfind.spec): disjoint-set union with
   union by rank and full path compression, over one left-to-right scan of
   the operations.

   Code.  [run_ops n is_union a b] builds the parent array [par] (cell i
   holds i) and a rank array [rk] (all 0), both flat arrays of n cells, and
   an answer array of Q cells (all false).  Operation k finds the roots ra
   of a[k] and rb of b[k] (each [find] compresses the path it walks: every
   node on it is re-pointed at the root); a union links the root of lower
   rank under the other one (ties: ra under rb, rank of rb + 1), a query
   writes [ra =? rb] into answer cell k.  All three arrays are threaded
   linearly; [find] is recursive (depth = length of the path, O(log n)
   under union by rank) and returns the root with the new parent array.

   Termination.  [init_loop] and [scan] recurse on an erased
   [Acc (Zwf 0) (gap m i)] as in template/polymul1.  [find] recurses on an
   erased [Acc (R par) x], where [R par y x] says y is the parent of the
   non-root x: the scan carries, as an erased argument, the proof
   [wf_par par] that every element is accessible (no parent cycle), and
   re-establishes it after every find and every link from Prop lemmas
   ([find_wf], [link_wf]).  No runtime guard, no fuel, no nat.

   Proof.  A root path [path par x r] (follow parents from x until the
   fixpoint r); [sameroot par x y] when x and y reach the same root.  The
   scan invariant [Inv k par] says: par has n cells all pointing into
   [0, n); every union among the first k operations joined its two
   elements (they have the same root); two elements with the same root are
   connected by the first k operations.  The converse direction of the
   query answer is an induction on [connected]. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Import Relations Transitive_Closure.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

Lemma aget_set_same : forall (t : array int) (i : int) (b : int),
  (i <? PArray.length t) = true -> t.[i <- b].[i] = b.
Proof. intros t i b H. exact (get_set_same int t i b H). Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (b : int),
  i <> j -> t.[i <- b].[j] = t.[j].
Proof. intros t i j b H. exact (get_set_other int t i j b H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (b : int),
  PArray.length t.[i <- b] = PArray.length t.
Proof. intros t i b. exact (length_set int t i b). Qed.

Lemma aget_make : forall (n i b : int), (PArray.make n b).[i] = b.
Proof. intros n i b. exact (get_make int b n i). Qed.

Lemma get_set_cases : forall (t : array int) (i j : int) (v : int),
  (i = j /\ t.[i <- v].[j] = v) \/ t.[i <- v].[j] = t.[j].
Proof.
  intros t i j v.
  destruct (i =? j) eqn:E.
  - apply eqb_spec in E. subst j.
    destruct (i <? PArray.length t) eqn:L.
    + left. split; [reflexivity|]. apply aget_set_same. exact L.
    + right.
      assert (L' : (i <? PArray.length t.[i <- v]) = false)
        by (rewrite alength_set; exact L).
      transitivity (default t.[i <- v]); [exact (get_out_of_bounds int t.[i <- v] i L')|].
      transitivity (default t); [exact (default_set int t i v)|].
      symmetry. exact (get_out_of_bounds int t i L).
  - apply eqb_false_spec in E. right. apply aget_set_other. exact E.
Qed.

(* ------------------------------------------------------------------ *)
(* The termination devices                                             *)
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

(* y is the parent of the non-root x. *)
Definition R (par : array int) (y x : int) : Prop := par.[x] = y /\ y <> x.

(* No parent cycle: every element is accessible. *)
Definition wf_par (par : array int) : Prop := forall x, Acc (R par) x.

Lemma find_step : forall par x, (par.[x] =? x) = false -> R par par.[x] x.
Proof. intros par x H. split; [reflexivity|]. apply eqb_false_spec. exact H. Qed.

(* ------------------------------------------------------------------ *)
(* The program, part 1: find with path compression                     *)
(* ------------------------------------------------------------------ *)

(* The root of x, and par with every node of the path re-pointed at it. *)
Fixpoint find (par : array int) (x : int) (H : Acc (R par) x) {struct H}
    : int * array int :=
  let p := par.[x] in
  match bdec (p =? x) with
  | left _ => (x, par)
  | right Hne =>
      let rp := find par p (Acc_inv H (find_step par x Hne)) in
      (fst rp, (snd rp).[x <- fst rp])
  end.

Lemma find_eq : forall par x H,
  find par x H =
  match bdec (par.[x] =? x) with
  | left _ => (x, par)
  | right Hne =>
      let rp := find par par.[x] (Acc_inv H (find_step par x Hne)) in
      (fst rp, (snd rp).[x <- fst rp])
  end.
Proof. intros. destruct H. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Root paths                                                          *)
(* ------------------------------------------------------------------ *)

Inductive path (p : array int) : int -> int -> Prop :=
| path_root : forall x, p.[x] = x -> path p x x
| path_step : forall x r, p.[x] <> x -> path p p.[x] r -> path p x r.

Lemma path_fix : forall p x r, path p x r -> p.[r] = r.
Proof. intros p x r H. induction H; auto. Qed.

Lemma path_of_root : forall p x r, p.[x] = x -> path p x r -> r = x.
Proof.
  intros p x r Hx H. inversion H as [x' Hx' | x' r' Hne Hr]; subst; auto.
  contradiction.
Qed.

Lemma path_tc : forall p y z, path p y z -> z <> y -> clos_trans _ (R p) z y.
Proof.
  intros p y z H. induction H as [x Hx | x r Hne H IH]; intros Hzy.
  - contradiction.
  - destruct (r =? p.[x]) eqn:E.
    + apply eqb_spec in E. subst r. apply t_step. split; [reflexivity|].
      exact Hne.
    + apply eqb_false_spec in E.
      apply (t_trans _ _ r p.[x] x); [apply IH; exact E|].
      apply t_step. split; [reflexivity|]. exact Hne.
Qed.

(* ------------------------------------------------------------------ *)
(* Well-foundedness transfer                                           *)
(* ------------------------------------------------------------------ *)

(* Every new parent edge is an old path, or leads to a new root. *)
Lemma wf_transfer : forall p p', wf_par p ->
  (forall x y, R p' y x -> clos_trans _ (R p) y x \/ p'.[y] = y) ->
  wf_par p'.
Proof.
  intros p p' W Hs x.
  pose proof (wf_clos_trans _ (R p) W) as Wt.
  induction (Wt x) as [x _ IH].
  constructor. intros y Hy.
  destruct (Hs x y Hy) as [T | Rt].
  - apply IH. exact T.
  - constructor. intros z [Hz Hne]. rewrite Rt in Hz. contradiction Hne.
    symmetry. exact Hz.
Qed.

(* p' agrees with p, except for cells re-pointed at their root. *)
Definition compat (p p' : array int) : Prop :=
  forall y, p'.[y] = p.[y] \/ path p y p'.[y].

Lemma compat_root : forall p p' z, compat p p' -> p.[z] = z -> p'.[z] = z.
Proof.
  intros p p' z C Hz. destruct (C z) as [E | P].
  - rewrite E. exact Hz.
  - exact (path_of_root p z _ Hz P).
Qed.

Lemma compat_wf : forall p p', wf_par p -> compat p p' -> wf_par p'.
Proof.
  intros p p' W C. apply (wf_transfer p p' W).
  intros x y [Hy Hne]. left. destruct (C x) as [E | P].
  - apply t_step. split; [rewrite <- E; exact Hy | exact Hne].
  - rewrite Hy in P. apply path_tc; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* What find computes                                                  *)
(* ------------------------------------------------------------------ *)

Lemma find_spec_aux : forall p x, Acc (R p) x -> forall H : Acc (R p) x,
  path p x (fst (find p x H)) /\ compat p (snd (find p x H)) /\
  PArray.length (snd (find p x H)) = PArray.length p.
Proof.
  intros p x A. induction A as [x _ IH]. intros H.
  rewrite find_eq. destruct (bdec (p.[x] =? x)) as [E | E].
  - cbn [fst snd]. split; [apply path_root; apply eqb_spec; exact E|].
    split; [intros y; left; reflexivity | reflexivity].
  - cbv zeta.
    destruct (IH p.[x] (find_step p x E) (Acc_inv H (find_step p x E)))
      as (P1 & C1 & L1).
    set (rp := find p p.[x] (Acc_inv H (find_step p x E))) in *.
    cbn [fst snd].
    assert (Px : path p x (fst rp))
      by (apply path_step; [apply eqb_false_spec; exact E | exact P1]).
    split; [exact Px|]. split.
    + intros y. destruct (get_set_cases (snd rp) x y (fst rp)) as [[Exy G] | G].
      * subst y. rewrite G. right. exact Px.
      * rewrite G. exact (C1 y).
    + rewrite alength_set. exact L1.
Qed.

Lemma find_spec : forall p x H,
  path p x (fst (find p x H)) /\ compat p (snd (find p x H)) /\
  PArray.length (snd (find p x H)) = PArray.length p.
Proof. intros p x H. exact (find_spec_aux p x H H). Qed.

Lemma find_wf : forall p x H, wf_par p -> wf_par (snd (find p x H)).
Proof.
  intros p x H W. destruct (find_spec p x H) as (_ & C & _).
  exact (compat_wf p _ W C).
Qed.

Lemma find_root : forall p x H,
  (snd (find p x H)).[fst (find p x H)] = fst (find p x H).
Proof.
  intros p x H. destruct (find_spec p x H) as (P & C & _).
  exact (compat_root p _ _ C (path_fix p x _ P)).
Qed.

Lemma find_keeps_root : forall p x H z, p.[z] = z -> (snd (find p x H)).[z] = z.
Proof.
  intros p x H z Hz. destruct (find_spec p x H) as (_ & C & _).
  exact (compat_root p _ z C Hz).
Qed.

(* ------------------------------------------------------------------ *)
(* The program, part 2: link by rank                                   *)
(* ------------------------------------------------------------------ *)

(* Union by rank of the two roots ra and rb. *)
Definition link (par rk : array int) (ra rb : int) : array int * array int :=
  if ra =? rb then (par, rk)
  else
    let ka := rk.[ra] in
    let kb := rk.[rb] in
    if ka <? kb then (par.[ra <- rb], rk)
    else if kb <? ka then (par.[rb <- ra], rk)
    else (par.[ra <- rb], rk.[rb <- kb + 1]).

Lemma set_root_wf : forall p u v, wf_par p -> p.[v] = v -> wf_par p.[u <- v].
Proof.
  intros p u v W Hv. apply (wf_transfer p _ W).
  intros x y [Hy Hne]. destruct (get_set_cases p u x v) as [[Eux G] | G].
  - right. subst x. rewrite G in Hy. subst y.
    destruct (get_set_cases p u v v) as [[E G'] | G']; [symmetry in E; contradiction|].
    rewrite G'. exact Hv.
  - left. apply t_step. split; [rewrite <- G; exact Hy | exact Hne].
Qed.

Lemma link_cases : forall p rk ra rb,
  (ra = rb /\ fst (link p rk ra rb) = p) \/
  (ra <> rb /\ (fst (link p rk ra rb) = p.[ra <- rb] \/
                fst (link p rk ra rb) = p.[rb <- ra])).
Proof.
  intros p rk ra rb. unfold link.
  destruct (ra =? rb) eqn:E.
  - left. split; [apply eqb_spec; exact E | reflexivity].
  - right. split; [apply eqb_false_spec; exact E|].
    cbv zeta. destruct (rk.[ra] <? rk.[rb]); [left; reflexivity|].
    destruct (rk.[rb] <? rk.[ra]); [right | left]; reflexivity.
Qed.

Lemma link_wf : forall p rk ra rb, wf_par p -> p.[ra] = ra -> p.[rb] = rb ->
  wf_par (fst (link p rk ra rb)).
Proof.
  intros p rk ra rb W Ha Hb.
  destruct (link_cases p rk ra rb) as [[_ ->] | [_ [-> | ->]]];
    [exact W | apply set_root_wf; auto | apply set_root_wf; auto].
Qed.

(* ------------------------------------------------------------------ *)
(* The program, part 3: initialisation and the scan                    *)
(* ------------------------------------------------------------------ *)

(* Cells i, i+1, ..., n-1 of p point at themselves. *)
Fixpoint init_loop (n i : int) (p : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => init_loop n (i + 1) p.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => p
  end.

Lemma init_loop_eq : forall n i p H,
  init_loop n i p H =
  match bdec (i <? n) with
  | left Hi => init_loop n (i + 1) p.[i <- i] (Acc_inv H (dec_step n i Hi))
  | right _ => p
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma make_wf : forall n, wf_par (PArray.make n 0).
Proof.
  intros n x. constructor. intros y [Hy _]. rewrite aget_make in Hy. subst y.
  constructor. intros z [Hz Hne]. rewrite aget_make in Hz. subst z.
  contradiction Hne. reflexivity.
Qed.

Lemma set_self_wf : forall p i, wf_par p -> wf_par p.[i <- i].
Proof.
  intros p i W. apply (wf_transfer p _ W).
  intros x y [Hy Hne]. left. destruct (get_set_cases p i x i) as [[Eix G] | G].
  - subst x. rewrite G in Hy. subst y. contradiction Hne. reflexivity.
  - apply t_step. split; [rewrite <- G; exact Hy | exact Hne].
Qed.

Lemma init_loop_wf_aux : forall n z i p H, gap n i = z ->
  wf_par p -> wf_par (init_loop n i p H).
Proof.
  intros n z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros i p H Hz W. rewrite init_loop_eq.
  destruct (bdec (i <? n)) as [Hi | Hi].
  - eapply IH; [ | reflexivity | apply set_self_wf; exact W ].
    rewrite <- Hz. apply dec_step. exact Hi.
  - exact W.
Qed.

Lemma init_loop_wf : forall n i p H, wf_par p -> wf_par (init_loop n i p H).
Proof. intros n i p H. exact (init_loop_wf_aux n _ i p H eq_refl). Qed.

Definition init_par (n : int) : array int :=
  init_loop n 0 (PArray.make n 0) (Zwf_well_founded 0 (gap n 0)).

Lemma init_wf : forall n, wf_par (init_par n).
Proof. intros n. apply init_loop_wf. apply make_wf. Qed.

(* Operations k, k+1, ..., q-1, on the parent array par (no cycle: W),
   the rank array rk and the answer array out. *)
Fixpoint scan (xu : array bool) (xa xb : array int) (q k : int)
    (par rk : array int) (out : array bool) (W : wf_par par)
    (H : Acc (Zwf 0) (gap q k)) {struct H} : array bool :=
  match bdec (k <? q) with
  | left Hk =>
      let a := xa.[k] in
      let b := xb.[k] in
      let fa := find par a (W a) in
      let Wa := find_wf par a (W a) W in
      let fb := find (snd fa) b (Wa b) in
      let Wb := find_wf (snd fa) b (Wa b) Wa in
      if xu.[k] then
        let l := link (snd fb) rk (fst fa) (fst fb) in
        scan xu xa xb q (k + 1) (fst l) (snd l) out
          (link_wf (snd fb) rk (fst fa) (fst fb) Wb
             (find_keeps_root (snd fa) b (Wa b) (fst fa) (find_root par a (W a)))
             (find_root (snd fa) b (Wa b)))
          (Acc_inv H (dec_step q k Hk))
      else
        scan xu xa xb q (k + 1) (snd fb) rk out.[k <- fst fa =? fst fb] Wb
          (Acc_inv H (dec_step q k Hk))
  | right _ => out
  end.

Definition run_ops_impl (xn : uint) (xu : array bool) (xa xb : array uint)
    : array bool :=
  let q := PArray.length xu in
  scan xu xa xb q 0 (init_par xn) (PArray.make xn 0) (PArray.make q false)
    (init_wf xn) (Zwf_well_founded 0 (gap q 0)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition run_ops : uint -> array bool -> array uint -> array uint ->
                     array bool := run_ops_impl.
