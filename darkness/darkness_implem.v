(* Implementation of darkness (darkness.spec). *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf
  QArith Relations Bool.
Import ListNotations.

Open Scope uint63_scope.
Open Scope array_scope.

Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* two distinct primitive literals *)
Ltac dd := let E := fresh in intro E; apply (f_equal to_Z) in E; cbv in E; discriminate E.

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

Lemma half_dec : forall x : int, (x =? 0) = false -> Zwf 0 (φ (x / 2)) (φ x).
Proof.
  intros x H. rewrite eqb_false_spec in H.
  assert ((φ x) <> 0%Z) by (intro E; apply H; apply to_Z_inj; exact E).
  unfold Zwf. rewrite div_spec. change (φ 2) with 2%Z.
  pose proof (to_Z_bounded x). split; [lia|].
  apply Z.div_lt; lia.
Qed.

Lemma dist_dec : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a).
  unfold Zwf. lia.
Qed.

Lemma flow_dec : forall B F F' : int,
  ((F <? F') && (F' <=? B)) = true -> Zwf 0 (gap B F') (gap B F).
Proof.
  intros B F F' H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite ltb_spec in H1. rewrite leb_spec in H2. unfold Zwf, gap.
  pose proof (to_Z_bounded F). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The grid in row-major order: f u i j for every cell u = i*C + j < n. *)
Fixpoint gloop {A : Type} (C n : int) (f : int -> int -> int -> A -> A)
    (u i j : int) (a : A) (H : Acc (Zwf 0) (gap n u)) {struct H} : A :=
  match bdec (u <? n) with
  | left Hu =>
      let a' := f u i j a in
      let j1 := j + 1 in
      let e := j1 =? C in
      gloop C n f (u + 1) (if e then i + 1 else i) (if e then 0 else j1) a'
        (Acc_inv H (dec_step n u Hu))
  | right _ => a
  end.

Definition grid_fold {A : Type} (C n : int) (f : int -> int -> int -> A -> A)
    (a : A) : A :=
  gloop C n f 0 0 0 a (Zwf_well_founded 0 (gap n 0)).

(* Light levels. *)
Definition M48 : int := 281474976710656.

Definition absdiff (a b : int) : int := if a <? b then b - a else a - b.

Definition denom (hh i j i' j' : int) : int :=
  let di := absdiff i i' in let dj := absdiff j j' in di * di + dj * dj + hh.

(* sum of floor (M48 * s / d) over all bulbs *)
Definition lo_sum (s : array int) (C n hh i j : int) : int :=
  grid_fold C n (fun u i' j' acc => acc + (M48 * s.[u]) / denom hh i j i' j') 0.

Fixpoint zofint_aux (x : int) (H : Acc (Zwf 0) (φ x)) {struct H} : Z :=
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      let r := zofint_aux (x / 2) (Acc_inv H (half_dec x Hx)) in
      if x mod 2 =? 0 then (2 * r)%Z else (2 * r + 1)%Z
  end.

Definition zofint (x : int) : Z := zofint_aux x (Zwf_well_founded 0 (φ x)).

(* the exact light level, as the fraction p / q *)
Definition exact_sum (s : array int) (C n hh i j : int) : Z * Z :=
  grid_fold C n (fun u i' j' (pq : Z * Z) =>
    let d := zofint (denom hh i j i' j') in
    let sv := zofint s.[u] in
    ((fst pq * d + sv * snd pq)%Z, (snd pq * d)%Z)) (0%Z, 1%Z).

Definition lit_cell (s : array int) (C n b hh i j : int) : bool :=
  let lo := lo_sum s C n hh i j in
  let mb := M48 * b in
  if mb <=? lo then true
  else if lo + n <? mb then false
  else let pq := exact_sum s C n hh i j in
       Z.leb (zofint b * snd pq) (fst pq).

Definition lit_arr (s : array int) (C n b hh : int) : array bool :=
  grid_fold C n (fun u i j a => a.[u <- lit_cell s C n b hh i j])
    (PArray.make n false).

Definition flat (xg : array (array int)) (C n : int) : array int :=
  grid_fold C n (fun u i j a => a.[u <- xg.[i].[j]]) (PArray.make n 0).

(* Capacities and residuals.  res.[2u] is the residual capacity from u to
   its right neighbour, res.[2u+1] from u to its lower neighbour; the
   residual in the opposite direction is twice the capacity minus it.
   Directions: 0 right, 1 left, 2 down, 3 up. *)
Definition capf (x y : bool) : int := if x && y then 43 else 11.

Definition init_res (lt : array bool) (C n : int) : array int :=
  grid_fold C n (fun u i j r =>
    let c1 := capf lt.[u] lt.[u + 1] in
    let c2 := capf lt.[u] lt.[u + C] in
    r.[2 * u <- c1].[2 * u + 1 <- c2]) (PArray.make (2 * n) 0).

Definition nbr (C p d : int) : int :=
  if d =? 0 then p + 1 else if d =? 1 then p - 1
  else if d =? 2 then p + C else p - C.

Definition opp (d : int) : int :=
  if d =? 0 then 1 else if d =? 1 then 0 else if d =? 2 then 3 else 2.

Definition slot (C p d : int) : int :=
  if d =? 0 then 2 * p else if d =? 1 then 2 * (p - 1)
  else if d =? 2 then 2 * p + 1 else 2 * (p - C) + 1.

Definition fwd (d : int) : bool := (d =? 0) || (d =? 2).

Definition resid (lt : array bool) (res : array int) (C p d : int) : int :=
  let k := slot C p d in
  if fwd d then res.[k] else 2 * capf lt.[p] lt.[nbr C p d] - res.[k].

Definition aug (res : array int) (C p d dl : int) : array int :=
  let k := slot C p d in
  if fwd d then res.[k <- res.[k] - dl] else res.[k <- res.[k] + dl].

(* Breadth-first search from all the dark cells at once (the implicit
   source) in the residual graph. *)
Record bst := { bd : array int; bp : array int; bq : array int; bt : int }.

Definition visit (lt : array bool) (res : array int) (C : int) (st : bst)
    (v dv d : int) (ok : bool) : bst :=
  if ok then
    let w := nbr C v d in
    if 0 <? resid lt res C v d then
      if (bd st).[w] =? 0 then
        {| bd := (bd st).[w <- dv + 1]; bp := (bp st).[w <- d];
           bq := (bq st).[bt st <- w]; bt := bt st + 1 |}
      else st
    else st
  else st.

Fixpoint bfs_loop (lt : array bool) (res : array int) (C n head : int)
    (st : bst) (H : Acc (Zwf 0) (gap n head)) {struct H} : bst :=
  match bdec (head <? n) with
  | left Hh =>
      if head <? bt st then
        let v := (bq st).[head] in
        let dv := (bd st).[v] in
        let j := v mod C in
        let st1 := visit lt res C st v dv 0 (j + 1 <? C) in
        let st2 := visit lt res C st1 v dv 1 (0 <? j) in
        let st3 := visit lt res C st2 v dv 2 (v + C <? n) in
        let st4 := visit lt res C st3 v dv 3 (C <=? v) in
        bfs_loop lt res C n (head + 1) st4 (Acc_inv H (dec_step n head Hh))
      else st
  | right _ => st
  end.

Definition root_step (lt : array bool) (u i j : int) (st : bst) : bst :=
  if lt.[u] then st
  else {| bd := (bd st).[u <- 1]; bp := (bp st).[u <- 4];
          bq := (bq st).[bt st <- u]; bt := bt st + 1 |}.

Definition roots (lt : array bool) (C n : int) : bst :=
  grid_fold C n (root_step lt)
    {| bd := PArray.make n 0; bp := PArray.make n 0;
       bq := PArray.make n 0; bt := 0 |}.

Definition bfs (lt : array bool) (res : array int) (C n : int) : bst :=
  bfs_loop lt res C n 0 (roots lt C n) (Zwf_well_founded 0 (gap n 0)).

Definition is_border (R C i j : int) : bool :=
  (i =? 0) || (i =? R - 1) || (j =? 0) || (j =? C - 1).

(* a reached border cell of least distance, n when there is none *)
Definition fb_step (dist : array int) (R C n u i j acc : int) : int :=
  if is_border R C i j && negb (dist.[u] =? 0)
     && ((acc =? n) || (dist.[u] <? dist.[acc]))
  then u else acc.

Definition find_border (dist : array int) (R C n : int) : int :=
  grid_fold C n (fb_step dist R C n) n.

(* The augmenting path, followed back from a border cell. *)
Fixpoint tmin (lt : array bool) (res : array int) (C : int) (par dist : array int)
    (v dl : int) (H : Acc (Zwf 0) (φ (dist.[v]))) {struct H} : int :=
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlt =>
        let r := resid lt res C p d in
        tmin lt res C par dist p (if r <? dl then r else dl)
          (Acc_inv H (dist_dec _ _ Hlt))
    | right _ => dl
    end
  else dl.

Fixpoint tapp (C : int) (par dist : array int) (dl v : int) (res : array int)
    (H : Acc (Zwf 0) (φ (dist.[v]))) {struct H} : array int :=
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlt =>
        tapp C par dist dl p (aug res C p d dl) (Acc_inv H (dist_dec _ _ Hlt))
    | right _ => res
    end
  else res.

Fixpoint flow_loop (lt : array bool) (R C n B : int) (res : array int) (F : int)
    (H : Acc (Zwf 0) (gap B F)) {struct H} : int :=
  let st := bfs lt res C n in
  let w := find_border (bd st) R C n in
  if w =? n then F
  else
    let dl := tmin lt res C (bp st) (bd st) w 1000
                (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let res' := tapp C (bp st) (bd st) dl w res
                  (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let F' := F + dl in
    match bdec ((F <? F') && (F' <=? B)) with
    | left Hg => flow_loop lt R C n B res' F' (Acc_inv H (flow_dec B F F' Hg))
    | right _ => F
    end.

Definition darkness_impl (xb xh : uint) (xg : array (array uint)) : uint :=
  let R := PArray.length xg in
  let C := PArray.length xg.[0] in
  let n := R * C in
  let s := flat xg C n in
  let lt := lit_arr s C n xb (xh * xh) in
  let res := init_res lt C n in
  let B := 86 * n in
  flow_loop lt R C n B res 0 (Zwf_well_founded 0 (gap B 0)).

(* ------------------------------------------------------------------ *)
(* Plumbing                                                            *)
(* ------------------------------------------------------------------ *)

Lemma wB_val : wB = 9223372036854775808%Z.
Proof. reflexivity. Qed.

Lemma aget_set_other : forall (t : array int) (i j : int) (v : int),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (PArray.get_set_other int t i j v H). Qed.

Lemma aget_set_same : forall (t : array int) (i : int) (v : int),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (PArray.get_set_same int t i v H). Qed.

Lemma alength_set : forall (t : array int) (i : int) (v : int),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (PArray.length_set int t i v). Qed.

Lemma max_length_val : (φ PArray.max_length) = 4194303%Z.
Proof. reflexivity. Qed.

Lemma divmod_succ : forall C u : Z, (0 < C)%Z -> (0 <= u)%Z ->
  ((u + 1) / C = if (u mod C + 1 =? C)%Z then u / C + 1 else u / C)%Z /\
  ((u + 1) mod C = if (u mod C + 1 =? C)%Z then 0 else u mod C + 1)%Z.
Proof.
  intros C u HC Hu.
  pose proof (Z.div_mod u C ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound u C HC) as B.
  destruct (Z.eqb_spec (u mod C + 1) C) as [Q | Q].
  - split.
    + symmetry. apply (Z.div_unique_pos _ _ _ 0); lia.
    + symmetry. apply (Z.mod_unique_pos _ _ (u / C + 1)); lia.
  - split.
    + symmetry. apply (Z.div_unique_pos _ _ _ (u mod C + 1)); lia.
    + symmetry. apply (Z.mod_unique_pos _ _ (u / C)); lia.
Qed.

Lemma gloop_eq : forall {A} C n f u i j (a : A) H,
  @gloop A C n f u i j a H =
  match bdec (u <? n) with
  | left Hu =>
      let a' := f u i j a in
      let j1 := j + 1 in
      let e := j1 =? C in
      gloop C n f (u + 1) (if e then i + 1 else i) (if e then 0 else j1) a'
        (Acc_inv H (dec_step n u Hu))
  | right _ => a
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma gloop_spec : forall {A} (C n : int) (f : int -> int -> int -> A -> A)
    (P : Z -> A -> Prop),
  (0 < (φ C))%Z ->
  (forall u i j a, ((φ u) < (φ n))%Z -> (φ i) = ((φ u) / (φ C))%Z ->
     (φ j) = ((φ u) mod (φ C))%Z -> P (φ u) a -> P ((φ u) + 1)%Z (f u i j a)) ->
  forall z u i j a H, gap n u = z -> ((φ u) <= (φ n))%Z ->
  (φ i) = ((φ u) / (φ C))%Z -> (φ j) = ((φ u) mod (φ C))%Z -> P (φ u) a ->
  P (φ n) (gloop C n f u i j a H).
Proof.
  intros A C n f P HC Hf z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros u i j a H Hz Hun Hi Hj Ha.
  rewrite gloop_eq. destruct (bdec (u <? n)) as [Hu | Hu].
  - pose proof Hu as Hu'. rewrite ltb_spec in Hu'.
    pose proof (to_Z_bounded u) as Bu. pose proof (to_Z_bounded n) as Bn.
    pose proof (to_Z_bounded C) as BC.
    assert (Hu1 : (φ (u + 1)) = ((φ u) + 1)%Z) by sia.
    destruct (divmod_succ (φ C) (φ u) HC ltac:(lia)) as [Dq Dr].
    pose proof (Z.mod_pos_bound (φ u) (φ C) HC) as Br.
    assert (Bq : (0 <= (φ u) / (φ C) <= (φ u))%Z).
    { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; nia]. }
    assert (Hj1 : (φ (j + 1)) = ((φ j) + 1)%Z) by sia.
    assert (He : ((j + 1) =? C) = ((φ u) mod (φ C) + 1 =? (φ C))%Z).
    { apply Bool.eq_iff_eq_true. rewrite Uint63.eqb_spec, Z.eqb_eq. split; intro E.
      - rewrite <- Hj, <- Hj1, E. reflexivity.
      - apply to_Z_inj. lia. }
    cbv zeta. rewrite He.
    eapply IH; [ | reflexivity | | | | ].
    + rewrite <- Hz. apply dec_step. exact Hu.
    + lia.
    + rewrite Hu1, Dq. destruct ((φ u) mod (φ C) + 1 =? (φ C))%Z; [|exact Hi]. sia.
    + rewrite Hu1, Dr. destruct ((φ u) mod (φ C) + 1 =? (φ C))%Z; [reflexivity|]. lia.
    + rewrite Hu1. apply Hf; assumption.
  - rewrite <- Bool.not_true_iff_false, ltb_spec in Hu.
    replace (φ n) with (φ u) by lia. exact Ha.
Qed.

Lemma grid_fold_spec : forall {A} (C n : int) (f : int -> int -> int -> A -> A)
    (P : Z -> A -> Prop) (a : A),
  (0 < (φ C))%Z ->
  (forall u i j a, ((φ u) < (φ n))%Z -> (φ i) = ((φ u) / (φ C))%Z ->
     (φ j) = ((φ u) mod (φ C))%Z -> P (φ u) a -> P ((φ u) + 1)%Z (f u i j a)) ->
  P 0%Z a -> P (φ n) (grid_fold C n f a).
Proof.
  intros A C n f P a HC Hf H0. unfold grid_fold.
  pose proof (to_Z_bounded n).
  eapply gloop_spec; try eassumption; try reflexivity;
    change (φ 0) with 0%Z; try lia;
    try (rewrite Z.div_0_l; lia); try (rewrite Z.mod_0_l; lia).
Qed.

Lemma of_Z_to_nat : forall i : int, of_Z (Z.of_nat (Z.to_nat (φ i))) = i.
Proof.
  intros i. pose proof (to_Z_bounded i). rewrite Z2Nat.id by lia. apply of_to_Z.
Qed.

(* ------------------------------------------------------------------ *)
(* Reading the input                                                   *)
(* ------------------------------------------------------------------ *)

Lemma repr_grid : forall b h g (xg : array (array uint)),
  valid_input b h g -> repr xg g ->
  (φ (PArray.length xg)) = Z.of_N (rows g) /\
  (φ (PArray.length xg.[0])) = Z.of_N (cols g) /\
  forall i j : int, ((φ i) < Z.of_N (rows g))%Z -> ((φ j) < Z.of_N (cols g))%Z ->
    (φ (xg.[i].[j])) = Z.of_N (strength g (Z.to_N (φ i)) (Z.to_N (φ j))).
Proof.
  intros b h g xg Hv [Hl Hc].
  destruct Hv as [_ _ [Hr0 _] [Hc0 _] Hrows _ _].
  unfold rows, cols, len in *.
  assert (Hrow : forall i : int, ((φ i) < Z.of_N (rows g))%Z ->
    exists row, nth (Z.to_nat (φ i)) g [] = row /\
      N.of_nat (List.length row) = cols g /\ repr (xg.[i]) row).
  { intros i Hi. unfold rows, len in Hi.
    destruct (Hc (Z.to_nat (φ i)) ltac:(lia)) as (row & Hn & Hr).
    exists row. split; [apply nth_error_nth; exact Hn|]. split.
    - rewrite Forall_forall in Hrows. apply Hrows.
      eapply nth_error_In. exact Hn.
    - rewrite of_Z_to_nat in Hr. exact Hr. }
  split; [lia|]. split.
  - destruct (Hrow 0 ltac:(change (φ 0) with 0%Z; unfold rows, len; lia))
      as (row & Hn & Hlr & [Hl' _]).
    destruct g as [|r0 g']; [simpl in Hr0; lia|].
    simpl in Hn. subst row. simpl. unfold cols, len in Hlr. simpl in Hlr.
    etransitivity; [symmetry; exact Hl'|lia].
  - intros i j Hi Hj.
    destruct (Hrow i Hi) as (row & Hn & Hlr & [Hl' Hc']).
    unfold cols, len in Hj, Hlr.
    destruct (Hc' (Z.to_nat (φ j)) ltac:(lia)) as (m & Hm & Hrm).
    unfold repr, repr_uint in Hrm. rewrite of_Z_to_nat in Hrm.
    unfold strength. rewrite Z_N_nat, Z_N_nat, Hn.
    erewrite nth_error_nth; [|exact Hm].
    subst m. rewrite Z2N.id; [reflexivity|]. apply to_Z_bounded.
Qed.

(* ------------------------------------------------------------------ *)
(* Exact arithmetic helpers                                            *)
(* ------------------------------------------------------------------ *)

Lemma zofint_aux_eq : forall x H, zofint_aux x H =
  match bdec (x =? 0) with
  | left _ => 0%Z
  | right Hx =>
      let r := zofint_aux (x / 2) (Acc_inv H (half_dec x Hx)) in
      if x mod 2 =? 0 then (2 * r)%Z else (2 * r + 1)%Z
  end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma zofint_spec : forall x, zofint x = (φ x).
Proof.
  assert (G : forall z x H, (φ x) = z -> zofint_aux x H = (φ x)).
  2: { intros x. apply (G (φ x)). reflexivity. }
  intros z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros x H Hz. rewrite zofint_aux_eq.
  destruct (bdec (x =? 0)) as [E | E].
  - rewrite Uint63.eqb_spec in E. subst x. reflexivity.
  - cbv zeta. rewrite (IH (φ (x / 2)) ltac:(subst z; apply half_dec; exact E) (x / 2) _ eq_refl).
    rewrite div_spec. change (φ 2) with 2%Z.
    destruct (x mod 2 =? 0) eqn:P.
    + rewrite Uint63.eqb_spec in P. apply (f_equal to_Z) in P.
      rewrite mod_spec in P. change (φ 2) with 2%Z in P. change (φ 0) with 0%Z in P.
      pose proof (Z.div_mod (φ x) 2 ltac:(lia)). lia.
    + rewrite eqb_false_spec in P.
      assert (P' : ((φ x) mod 2 <> 0)%Z).
      { intro F. apply P. apply to_Z_inj. rewrite mod_spec. exact F. }
      pose proof (Z.div_mod (φ x) 2 ltac:(lia)).
      pose proof (Z.mod_pos_bound (φ x) 2 ltac:(lia)). lia.
Qed.

Lemma floor_le : forall a d : Z, (0 <= a)%Z -> (0 < d)%Z ->
  inject_Z (a / d) <= inject_Z a / inject_Z d.
Proof.
  intros a d Ha Hd. apply Qle_shift_div_l.
  - rewrite <- (Zlt_Qlt 0). exact Hd.
  - rewrite <- inject_Z_mult, <- Zle_Qle.
    pose proof (Z.div_mod a d ltac:(lia)).
    pose proof (Z.mod_pos_bound a d Hd). lia.
Qed.

Lemma floor_ge : forall a d : Z, (0 <= a)%Z -> (0 < d)%Z ->
  inject_Z a / inject_Z d <= inject_Z (a / d) + 1.
Proof.
  intros a d Ha Hd. apply Qle_shift_div_r.
  - rewrite <- (Zlt_Qlt 0). exact Hd.
  - replace ((inject_Z (a / d) + 1) * inject_Z d)%Q with (inject_Z ((a / d + 1) * d)%Z)
      by (rewrite inject_Z_mult, inject_Z_plus; reflexivity).
    rewrite <- Zle_Qle.
    pose proof (Z.div_mod a d ltac:(lia)).
    pose proof (Z.mod_pos_bound a d Hd). lia.
Qed.

Lemma frac_step : forall p q s d : Z, (0 < q)%Z -> (0 < d)%Z ->
  inject_Z (p * d + s * q) / inject_Z (q * d)
  == inject_Z p / inject_Z q + inject_Z s / inject_Z d.
Proof.
  intros p q s d Hq Hd.
  assert (Q1 : ~ inject_Z q == 0).
  { intro E. unfold Qeq in E. simpl in E. lia. }
  assert (Q2 : ~ inject_Z d == 0).
  { intro E. unfold Qeq in E. simpl in E. lia. }
  rewrite inject_Z_plus, !inject_Z_mult. field. split; assumption.
Qed.

(* Row-major partial sums over the grid. *)
Definition qrows (f : N -> N -> Q) (C : Z) (k : nat) : Q :=
  qsum (fun i' => qsum (f i') (Z.to_nat C)) k.

Definition qpart (f : N -> N -> Q) (C u : Z) : Q :=
  qrows f C (Z.to_nat (u / C)) + qsum (f (Z.to_N (u / C))) (Z.to_nat (u mod C)).

Lemma qpart_S : forall f C u, (0 < C)%Z -> (0 <= u)%Z ->
  qpart f C (u + 1) == qpart f C u + f (Z.to_N (u / C)) (Z.to_N (u mod C)).
Proof.
  intros f C u HC Hu. unfold qpart.
  destruct (divmod_succ C u HC Hu) as [Dq Dr]. rewrite Dq, Dr.
  pose proof (Z.mod_pos_bound u C HC) as Br.
  assert (Bq : (0 <= u / C)%Z) by (apply Z.div_pos; lia).
  destruct (Z.eqb_spec (u mod C + 1) C) as [E | E].
  - replace (Z.to_nat (u / C + 1)) with (S (Z.to_nat (u / C))) by lia.
    unfold qrows. simpl qsum. rewrite Z_nat_N.
    replace (Z.to_nat C) with (S (Z.to_nat (u mod C))) by lia.
    simpl qsum. rewrite Z_nat_N. ring.
  - replace (Z.to_nat (u mod C + 1)) with (S (Z.to_nat (u mod C))) by lia.
    simpl qsum. rewrite Z_nat_N. ring.
Qed.

Lemma qpart_full : forall f C R, (0 < C)%Z -> (0 <= R)%Z ->
  qpart f C (R * C) == qrows f C (Z.to_nat R).
Proof.
  intros f C R HC HR. unfold qpart.
  rewrite Z.div_mul by lia. rewrite Z.mod_mul by lia. simpl. ring.
Qed.

Lemma qpart_0 : forall f C, (0 < C)%Z -> qpart f C 0 == 0.
Proof.
  intros f C HC. unfold qpart. rewrite Z.div_0_l, Z.mod_0_l by lia.
  reflexivity.
Qed.

Lemma absdiff_spec : forall a b, (φ (absdiff a b)) = Z.abs ((φ a) - (φ b)).
Proof.
  intros a b. unfold absdiff. destruct (a <? b) eqn:E;
    [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E];
    rewrite sub_spec; rewrite Z.mod_small; pose proof (to_Z_bounded a);
    pose proof (to_Z_bounded b); lia.
Qed.

Lemma denom_spec : forall hh i j i' j',
  ((φ i) < 64)%Z -> ((φ j) < 64)%Z -> ((φ i') < 64)%Z -> ((φ j') < 64)%Z -> ((φ hh) < 64)%Z ->
  (φ (denom hh i j i' j')) = (((φ i) - (φ i')) ^ 2 + ((φ j) - (φ j')) ^ 2 + (φ hh))%Z.
Proof.
  intros hh i j i' j' Hi Hj Hi' Hj' Hh. unfold denom.
  pose proof (absdiff_spec i i') as A1. pose proof (absdiff_spec j j') as A2.
  set (x := absdiff i i') in *. set (y := absdiff j j') in *.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  pose proof (to_Z_bounded i'). pose proof (to_Z_bounded j').
  pose proof (to_Z_bounded hh).
  assert (Ex : ((φ x) * (φ x) = ((φ i) - (φ i')) ^ 2)%Z).
  { rewrite A1, Z.pow_2_r. destruct (Z.abs_spec ((φ i) - (φ i'))) as [[_ ->] | [_ ->]]; ring. }
  assert (Ey : ((φ y) * (φ y) = ((φ j) - (φ j')) ^ 2)%Z).
  { rewrite A2, Z.pow_2_r. destruct (Z.abs_spec ((φ j) - (φ j'))) as [[_ ->] | [_ ->]]; ring. }
  assert (Bx : (0 <= (φ x) < 64)%Z) by lia. assert (By : (0 <= (φ y) < 64)%Z) by lia.
  assert (Px : (0 <= (φ x) * (φ x) <= 4096)%Z) by (clear -Bx; nia).
  assert (Py : (0 <= (φ y) * (φ y) <= 4096)%Z) by (clear -By; nia).
  rewrite !add_spec, !mul_spec.
  rewrite (Z.mod_small ((φ x) * (φ x))) by (rewrite wB_val; lia).
  rewrite (Z.mod_small ((φ y) * (φ y))) by (rewrite wB_val; lia).
  rewrite (Z.mod_small ((φ x) * (φ x) + (φ y) * (φ y))) by (rewrite wB_val; lia).
  rewrite Z.mod_small by (rewrite wB_val; lia). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The light levels                                                    *)
(* ------------------------------------------------------------------ *)

Section Light.

Variables (b h : N) (g : list (list N)).
Hypothesis Hv : valid_input b h g.

Local Notation Rz := (Z.of_N (rows g)).
Local Notation Cz := (Z.of_N (cols g)).

Lemma vi_facts : (1 <= Rz <= 30)%Z /\ (1 <= Cz <= 30)%Z /\
  (1 <= Z.of_N b <= 9)%Z /\ (1 <= Z.of_N h <= 5)%Z.
Proof. destruct Hv as [[Hb1 Hb2] [Hh1 Hh2] [Hr1 Hr2] [Hc1 Hc2] _ _ _]. lia. Qed.

Lemma strength_le9 : forall i' j', (strength g i' j' <= 9)%N.
Proof.
  intros i' j'. destruct Hv as [_ _ _ _ _ Hd _]. unfold strength.
  destruct (nth_in_or_default (N.to_nat i') g []) as [Hin | Hdf].
  - rewrite Forall_forall in Hd. pose proof (Hd _ Hin) as Hr.
    rewrite Forall_forall in Hr.
    destruct (nth_in_or_default (N.to_nat j') (nth (N.to_nat i') g []) 0%N)
      as [Hin' | Hdf'].
    + apply Hr. exact Hin'.
    + rewrite Hdf'. lia.
  - rewrite Hdf. destruct (N.to_nat j'); simpl; lia.
Qed.

(* the contribution of bulb (i', j') at cell (ci, cj) *)
Definition Tm (ci cj : N) (i' j' : N) : Q :=
  (inject_Z (Z.of_N (strength g i' j')) /
   inject_Z ((Z.of_N ci - Z.of_N i') ^ 2 + (Z.of_N cj - Z.of_N j') ^ 2
             + Z.of_N h ^ 2))%Q.

Lemma light_eq : forall ci cj,
  light h g ci cj = qrows (Tm ci cj) Cz (Z.to_nat Rz).
Proof.
  intros ci cj. unfold light, qrows, Tm.
  replace (Z.to_nat Cz) with (N.to_nat (cols g)) by lia.
  replace (Z.to_nat Rz) with (N.to_nat (rows g)) by lia. reflexivity.
Qed.

Definition Mq : Q := inject_Z 281474976710656.

Section Cell.

Variables (s : array int) (C n hh i j : int).
Hypothesis Hs : forall u, ((φ u) < (φ n))%Z ->
  (φ (s.[u])) = Z.of_N (strength g (Z.to_N ((φ u) / Cz)) (Z.to_N ((φ u) mod Cz))).
Hypothesis HC : (φ C) = Cz.
Hypothesis Hn : (φ n) = (Rz * Cz)%Z.
Hypothesis Hhh : (φ hh) = (Z.of_N h ^ 2)%Z.
Hypothesis Hi : ((φ i) < Rz)%Z.
Hypothesis Hj : ((φ j) < Cz)%Z.

(* what a step of the two sums reads at cell u = (i', j') *)
Lemma term_facts : forall u i' j', ((φ u) < (φ n))%Z ->
  (φ i') = ((φ u) / (φ C))%Z -> (φ j') = ((φ u) mod (φ C))%Z ->
  let sv := (φ (s.[u])) in let D := (φ (denom hh i j i' j')) in
  (0 <= sv <= 9)%Z /\ (1 <= D)%Z /\
  (Mq * Tm (Z.to_N (φ i)) (Z.to_N (φ j)) (Z.to_N ((φ u) / Cz)) (Z.to_N ((φ u) mod Cz))
   == inject_Z (281474976710656 * sv) / inject_Z D)%Q /\
  (Tm (Z.to_N (φ i)) (Z.to_N (φ j)) (Z.to_N ((φ u) / Cz)) (Z.to_N ((φ u) mod Cz))
   == inject_Z sv / inject_Z D)%Q.
Proof.
  intros u i' j' Hu Hi' Hj' sv D.
  destruct vi_facts as (HR & HCb & Hb & Hh).
  rewrite HC in Hi', Hj'.
  pose proof (to_Z_bounded u). pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  assert (Bi' : (0 <= (φ u) / Cz < Rz)%Z).
  { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia. }
  assert (Bj' : (0 <= (φ u) mod Cz < Cz)%Z) by (apply Z.mod_pos_bound; lia).
  assert (Hsv : sv = Z.of_N (strength g (Z.to_N ((φ u) / Cz)) (Z.to_N ((φ u) mod Cz))))
    by (apply Hs; exact Hu).
  pose proof (strength_le9 (Z.to_N ((φ u) / Cz)) (Z.to_N ((φ u) mod Cz))) as Hs9.
  assert (Hh2 : (1 <= Z.of_N h ^ 2 <= 25)%Z) by (clear -Hh; rewrite Z.pow_2_r; nia).
  assert (HD : D = (((φ i) - (φ i')) ^ 2 + ((φ j) - (φ j')) ^ 2 + (φ hh))%Z).
  { apply denom_spec; lia. }
  assert (HD1 : (1 <= D)%Z).
  { rewrite HD, Hhh.
    assert (0 <= ((φ i) - (φ i')) ^ 2)%Z by (rewrite Z.pow_2_r; apply Z.square_nonneg).
    assert (0 <= ((φ j) - (φ j')) ^ 2)%Z by (rewrite Z.pow_2_r; apply Z.square_nonneg).
    lia. }
  assert (HDz : D = ((Z.of_N (Z.to_N (φ i)) - Z.of_N (Z.to_N ((φ u) / Cz))) ^ 2
           + (Z.of_N (Z.to_N (φ j)) - Z.of_N (Z.to_N ((φ u) mod Cz))) ^ 2
           + Z.of_N h ^ 2)%Z).
  { rewrite HD, Hhh, !Z2N.id by lia. rewrite Hi', Hj'. reflexivity. }
  assert (DQ : ~ (inject_Z D == 0)%Q) by (intro E; unfold Qeq in E; simpl in E; lia).
  split; [rewrite Hsv; clear -Hs9; lia|]. split; [exact HD1|]. split.
  - unfold Tm, Mq. rewrite <- HDz, <- Hsv, inject_Z_mult. field. exact DQ.
  - unfold Tm. rewrite <- HDz, <- Hsv. reflexivity.
Qed.

Lemma lo_sum_spec :
  let lo := lo_sum s C n hh i j in
  (inject_Z (φ lo) <= Mq * light h g (Z.to_N (φ i)) (Z.to_N (φ j)))%Q /\
  (Mq * light h g (Z.to_N (φ i)) (Z.to_N (φ j)) <= inject_Z (φ lo) + inject_Z (Rz * Cz))%Q.
Proof.
  destruct vi_facts as (HR & HCb & Hb & Hh).
  set (f := Tm (Z.to_N (φ i)) (Z.to_N (φ j))).
  assert (G : forall lo : int,
    ((φ lo) <= (φ n) * (9 * 281474976710656))%Z /\
    (inject_Z (φ lo) <= Mq * qpart f Cz (φ n))%Q /\
    (Mq * qpart f Cz (φ n) <= inject_Z (φ lo) + inject_Z (φ n))%Q ->
    (inject_Z (φ lo) <= Mq * light h g (Z.to_N (φ i)) (Z.to_N (φ j)))%Q /\
    (Mq * light h g (Z.to_N (φ i)) (Z.to_N (φ j)) <= inject_Z (φ lo) + inject_Z (Rz * Cz))%Q).
  { intros lo (_ & H1 & H2). rewrite light_eq. rewrite Hn in H1, H2.
    rewrite qpart_full in H1, H2 by lia. split; assumption. }
  apply G. unfold lo_sum.
  apply (grid_fold_spec C n _ (fun u lo =>
    ((φ lo) <= u * (9 * 281474976710656))%Z /\
    (inject_Z (φ lo) <= Mq * qpart f Cz u)%Q /\
    (Mq * qpart f Cz u <= inject_Z (φ lo) + inject_Z u)%Q)).
  - lia.
  - intros u i' j' lo Hu Hi' Hj' (IH0 & IH1 & IH2).
    destruct (term_facts u i' j' Hu Hi' Hj') as (Hsv & HD & EM & _).
    set (sv := (φ (s.[u]))) in *. set (D := (φ (denom hh i j i' j'))) in *.
    pose proof (to_Z_bounded u) as Bu.
    assert (Hn' : ((φ n) <= 900)%Z) by (rewrite Hn; clear -HR HCb; nia).
    assert (Hm : (φ (M48 * s.[u])) = (281474976710656 * sv)%Z).
    { rewrite mul_spec. change (φ M48) with 281474976710656%Z.
      apply Z.mod_small. rewrite wB_val. lia. }
    assert (Ht : (φ ((M48 * s.[u]) / denom hh i j i' j'))
                 = ((281474976710656 * sv) / D)%Z).
    { rewrite div_spec, Hm. reflexivity. }
    assert (Bt : (0 <= (281474976710656 * sv) / D <= 9 * 281474976710656)%Z).
    { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. clear -Hsv HD; nia. }
    assert (Hadd : (φ (lo + (M48 * s.[u]) / denom hh i j i' j'))
                   = ((φ lo) + (281474976710656 * sv) / D)%Z).
    { rewrite add_spec, Ht. apply Z.mod_small. rewrite wB_val.
      pose proof (to_Z_bounded lo). clear -IH0 Bt Hu Hn' Bu H. lia. }
    assert (EQ : (Mq * qpart f Cz ((φ u) + 1)
                  == Mq * qpart f Cz (φ u) + inject_Z (281474976710656 * sv) / inject_Z D)%Q).
    { rewrite qpart_S by lia. rewrite <- EM. unfold f. ring. }
    rewrite Hadd. split; [clear -IH0 Bt; lia|]. split.
    + rewrite EQ, inject_Z_plus. apply Qplus_le_compat; [exact IH1|].
      apply floor_le; lia.
    + rewrite EQ, !inject_Z_plus.
      apply Qle_trans with ((inject_Z (φ lo) + inject_Z (φ u))
                            + (inject_Z ((281474976710656 * sv) / D) + 1))%Q.
      * apply Qplus_le_compat; [exact IH2|]. apply floor_ge; lia.
      * apply Qle_lteq. right. ring.
  - split; [change (φ 0) with 0%Z; lia|]. rewrite qpart_0 by lia.
    change (φ 0) with 0%Z. split; [apply Qle_lteq; right; reflexivity|].
    apply Qle_lteq; right; reflexivity.
Qed.

Lemma exact_sum_spec :
  let pq := exact_sum s C n hh i j in
  (0 < snd pq)%Z /\
  (inject_Z (fst pq) / inject_Z (snd pq) == light h g (Z.to_N (φ i)) (Z.to_N (φ j)))%Q.
Proof.
  destruct vi_facts as (HR & HCb & Hb & Hh).
  set (f := Tm (Z.to_N (φ i)) (Z.to_N (φ j))).
  enough (G : (0 < snd (exact_sum s C n hh i j))%Z /\
    (inject_Z (fst (exact_sum s C n hh i j)) / inject_Z (snd (exact_sum s C n hh i j))
     == qpart f Cz (φ n))%Q).
  { destruct G as [G1 G2]. split; [exact G1|]. rewrite G2, light_eq, Hn.
    apply qpart_full; lia. }
  unfold exact_sum.
  apply (grid_fold_spec C n _ (fun u (pq : Z * Z) =>
    (0 < snd pq)%Z /\
    (inject_Z (fst pq) / inject_Z (snd pq) == qpart f Cz u)%Q)).
  - lia.
  - intros u i' j' [p q] Hu Hi' Hj' [Hq IH]. simpl in Hq, IH |- *.
    destruct (term_facts u i' j' Hu Hi' Hj') as (Hsv & HD & _ & ET).
    rewrite !zofint_spec. split; [apply Z.mul_pos_pos; lia|].
    rewrite frac_step by lia. rewrite qpart_S by (pose proof (to_Z_bounded u); lia).
    rewrite IH. unfold f. rewrite ET. reflexivity.
  - simpl. split; [lia|]. rewrite qpart_0 by lia. reflexivity.
Qed.

Lemma lit_cell_spec : forall xb : int, (φ xb) = Z.of_N b ->
  lit_cell s C n xb hh i j = lit b h g (Z.to_N (φ i)) (Z.to_N (φ j)).
Proof.
  intros xb Hxb.
  destruct vi_facts as (HR & HCb & Hb & Hh).
  unfold lit_cell, lit.
  destruct lo_sum_spec as [L1 L2].
  set (lo := lo_sum s C n hh i j) in *.
  set (L := light h g (Z.to_N (φ i)) (Z.to_N (φ j))) in *.
  assert (HMb : (φ (M48 * xb)) = (281474976710656 * Z.of_N b)%Z).
  { rewrite mul_spec, Hxb. change (φ M48) with 281474976710656%Z.
    apply Z.mod_small. rewrite wB_val. lia. }
  assert (MP : (0 < Mq)%Q) by (unfold Mq; reflexivity).
  assert (EMb : (inject_Z (281474976710656 * Z.of_N b) == Mq * inject_Z (Z.of_N b))%Q).
  { unfold Mq. rewrite inject_Z_mult. reflexivity. }
  destruct (M48 * xb <=? lo) eqn:E1.
  - rewrite leb_spec, HMb in E1. symmetry. apply Qle_bool_iff.
    apply (Qmult_le_l _ _ Mq MP). rewrite <- EMb.
    apply Qle_trans with (inject_Z (φ lo)); [rewrite <- Zle_Qle; exact E1|exact L1].
  - destruct (lo + n <? M48 * xb) eqn:E2.
    + rewrite ltb_spec, HMb in E2. rewrite add_spec, Hn in E2.
      rewrite Z.mod_small in E2 by (rewrite <- leb_spec in E1 || idtac;
        pose proof (to_Z_bounded lo); rewrite wB_val;
        rewrite <- Bool.not_true_iff_false, leb_spec, HMb in E1; nia).
      symmetry. apply Bool.not_true_iff_false. rewrite Qle_bool_iff. intro F.
      apply (Qmult_le_l _ _ Mq MP) in F. rewrite <- EMb in F.
      apply (Qlt_not_le _ _ (Qle_lt_trans _ _ _ L2 ltac:(rewrite <- inject_Z_plus, <- Zlt_Qlt; exact E2))).
      exact F.
    + destruct exact_sum_spec as [Hq EQ].
      set (pq := exact_sum s C n hh i j) in *.
      rewrite zofint_spec, Hxb.
      apply Bool.eq_iff_eq_true. rewrite Z.leb_le, Qle_bool_iff.
      fold L in EQ. rewrite <- EQ.
      assert (QP : (0 < inject_Z (snd pq))%Q) by (rewrite <- (Zlt_Qlt 0); exact Hq).
      split; intro F.
      * apply Qle_shift_div_l; [exact QP|]. rewrite <- inject_Z_mult, <- Zle_Qle. exact F.
      * rewrite Zle_Qle, inject_Z_mult.
        apply Qle_trans with (inject_Z (fst pq) / inject_Z (snd pq) * inject_Z (snd pq))%Q.
        -- apply Qmult_le_compat_r; [exact F | apply Qlt_le_weak; exact QP].
        -- apply Qle_lteq. right. field. intro Z0. rewrite Z0 in QP. discriminate.
Qed.

End Cell.

End Light.

(* ------------------------------------------------------------------ *)
(* Sums over Z                                                         *)
(* ------------------------------------------------------------------ *)

Fixpoint zsum (f : N -> Z) (n : nat) : Z :=
  match n with O => 0%Z | S m => (zsum f m + f (N.of_nat m))%Z end.

Lemma zsum_ext : forall f g n,
  (forall k, (k < n)%nat -> f (N.of_nat k) = g (N.of_nat k)) -> zsum f n = zsum g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; simpl; [reflexivity|].
  rewrite IH by (intros k Hk; apply H; lia). rewrite H by lia. reflexivity.
Qed.

Lemma zsum_le : forall f g n,
  (forall k, (k < n)%nat -> (f (N.of_nat k) <= g (N.of_nat k))%Z) ->
  (zsum f n <= zsum g n)%Z.
Proof.
  intros f g n. induction n as [|n IH]; intros H; simpl; [lia|].
  pose proof (IH ltac:(intros k Hk; apply H; lia)). pose proof (H n ltac:(lia)). lia.
Qed.

Lemma zsum_le_eq : forall f g n,
  (forall k, (k < n)%nat -> (f (N.of_nat k) <= g (N.of_nat k))%Z) ->
  zsum f n = zsum g n ->
  forall k, (k < n)%nat -> f (N.of_nat k) = g (N.of_nat k).
Proof.
  intros f g n. induction n as [|n IH]; intros H E k Hk; [lia|].
  simpl in E.
  pose proof (zsum_le f g n ltac:(intros k' Hk'; apply H; lia)) as L.
  pose proof (H n ltac:(lia)) as Ln.
  assert (En : f (N.of_nat n) = g (N.of_nat n)) by lia.
  destruct (Nat.eq_dec k n) as [-> | Hne]; [exact En|].
  apply IH; [intros k' Hk'; apply H; lia | lia | lia].
Qed.

Lemma zsum_const_le : forall f n c,
  (forall k, (k < n)%nat -> (f (N.of_nat k) <= c)%Z) ->
  (zsum f n <= Z.of_nat n * c)%Z.
Proof.
  intros f n c. induction n as [|n IH]; intros H; cbn [zsum]; [lia|].
  pose proof (IH ltac:(intros k Hk; apply H; lia)). pose proof (H n ltac:(lia)).
  rewrite Nat2Z.inj_succ, Z.mul_succ_l. lia.
Qed.

Lemma zsum_nonneg : forall f n,
  (forall k, (k < n)%nat -> (0 <= f (N.of_nat k))%Z) -> (0 <= zsum f n)%Z.
Proof.
  intros f n H. pose proof (zsum_le (fun _ => 0%Z) f n H) as L.
  assert (zsum (fun _ => 0%Z) n = 0%Z) as Z0.
  { clear. induction n; simpl; [reflexivity | rewrite IHn; reflexivity]. }
  lia.
Qed.

Lemma zsum_upd : forall f g n k0 D, (k0 < n)%nat ->
  (forall k, (k < n)%nat -> k <> k0 -> g (N.of_nat k) = f (N.of_nat k)) ->
  g (N.of_nat k0) = (f (N.of_nat k0) + D)%Z ->
  zsum g n = (zsum f n + D)%Z.
Proof.
  intros f g n. induction n as [|n IH]; intros k0 D Hk0 Ho Hs; [lia|].
  simpl. destruct (Nat.eq_dec k0 n) as [-> | Hne].
  - rewrite (zsum_ext g f n) by (intros k Hk; apply Ho; lia). rewrite Hs. lia.
  - rewrite (IH k0 D) by (try lia; intros k Hk Hk'; apply Ho; lia).
    rewrite (Ho n) by lia. lia.
Qed.

Lemma zsum_nsum : forall f n,
  Z.of_N (nsum f n) = zsum (fun k => Z.of_N (f k)) n.
Proof.
  intros f n. induction n as [|n IH]; simpl; [reflexivity|]. rewrite <- IH. lia.
Qed.

Definition b2z (x : bool) : Z := if x then 1%Z else 0%Z.

Lemma cell_inj : forall C i j i' j' : Z, (0 <= j < C)%Z -> (0 <= j' < C)%Z ->
  (0 <= i)%Z -> (0 <= i')%Z ->
  (i * C + j = i' * C + j')%Z -> i = i' /\ j = j'.
Proof.
  intros C i j i' j' Hj Hj' Hi Hi' E.
  assert (Q1 : i = ((i * C + j) / C)%Z) by (apply (Z.div_unique_pos _ _ _ j); lia).
  assert (Q2 : i' = ((i' * C + j') / C)%Z) by (apply (Z.div_unique_pos _ _ _ j'); lia).
  assert (i = i') by (rewrite Q1, Q2, E; reflexivity). subst i'. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The flow, on the math side                                          *)
(* ------------------------------------------------------------------ *)

Section Flow.

Variables (b h : N) (g : list (list N)).
Hypothesis Hv : valid_input b h g.

Local Notation Rz := (Z.of_N (rows g)).
Local Notation Cz := (Z.of_N (cols g)).

Lemma vi_rc : (1 <= Rz <= 30)%Z /\ (1 <= Cz <= 30)%Z.
Proof. destruct (vi_facts b h g Hv) as (A & B & _). lia. Qed.

(* prices of the horizontal section right of (i, j) and the vertical one
   below it, and the two slots of res that hold their residuals *)
Definition pH (i j : N) : Z := Z.of_N (price b h g i j i (j + 1)).
Definition pV (i j : N) : Z := Z.of_N (price b h g i j (i + 1) j).
Definition sH (i j : N) : int := of_Z (2 * (Z.of_N i * Cz + Z.of_N j)).
Definition sV (i j : N) : int := of_Z (2 * (Z.of_N i * Cz + Z.of_N j) + 1).

(* the flow through a section, from (i, j) to its right / lower neighbour *)
Definition fH (res : array int) (i j : N) : Z := (pH i j - (φ (res.[sH i j])))%Z.
Definition fV (res : array int) (i j : N) : Z := (pV i j - (φ (res.[sV i j])))%Z.

(* the net flow out of the set X of cells *)
Definition phiH (X : N -> N -> bool) (res : array int) : Z :=
  zsum (fun i => zsum (fun j => (b2z (X i j) - b2z (X i (j + 1)%N)) * fH res i j)%Z
                      (N.to_nat (cols g - 1))) (N.to_nat (rows g)).
Definition phiV (X : N -> N -> bool) (res : array int) : Z :=
  zsum (fun i => zsum (fun j => (b2z (X i j) - b2z (X (i + 1)%N j)) * fV res i j)%Z
                      (N.to_nat (cols g))) (N.to_nat (rows g - 1)).
Definition phi X res : Z := (phiH X res + phiV X res)%Z.

Definition bnd (res : array int) : Prop :=
  (forall i j, (i < rows g)%N -> (j + 1 < cols g)%N -> ((φ (res.[sH i j])) <= 2 * pH i j)%Z) /\
  (forall i j, (i + 1 < rows g)%N -> (j < cols g)%N -> ((φ (res.[sV i j])) <= 2 * pV i j)%Z).

Definition goodX (X : N -> N -> bool) : Prop :=
  (forall i j, in_grid g i j -> lit b h g i j = false -> X i j = true) /\
  (forall i j, on_border g i j -> X i j = false).

Lemma price_bounds : forall i j i' j',
  (11 <= Z.of_N (price b h g i j i' j') <= 43)%Z.
Proof. intros. unfold price. destruct (_ && _); lia. Qed.

Lemma phi_sH : forall i j, (i < rows g)%N -> (j < cols g)%N ->
  (φ (sH i j)) = (2 * (Z.of_N i * Cz + Z.of_N j))%Z.
Proof.
  intros i j Hi Hj. destruct vi_rc as [HR HC]. unfold sH.
  rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
  assert (Z.of_N i * Cz <= 30 * 30)%Z by (clear -HR HC Hi; nia). lia.
Qed.

Lemma phi_sV : forall i j, (i < rows g)%N -> (j < cols g)%N ->
  (φ (sV i j)) = (2 * (Z.of_N i * Cz + Z.of_N j) + 1)%Z.
Proof.
  intros i j Hi Hj. destruct vi_rc as [HR HC]. unfold sV.
  rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
  assert (Z.of_N i * Cz <= 30 * 30)%Z by (clear -HR HC Hi; nia). lia.
Qed.

Lemma sH_inj : forall i j i' j', (i < rows g)%N -> (j < cols g)%N ->
  (i' < rows g)%N -> (j' < cols g)%N -> sH i j = sH i' j' -> i = i' /\ j = j'.
Proof.
  intros i j i' j' Hi Hj Hi' Hj' E. apply (f_equal to_Z) in E.
  rewrite !phi_sH in E by assumption.
  destruct (cell_inj Cz (Z.of_N i) (Z.of_N j) (Z.of_N i') (Z.of_N j')) as [E1 E2];
    try lia.
Qed.

Lemma sV_inj : forall i j i' j', (i < rows g)%N -> (j < cols g)%N ->
  (i' < rows g)%N -> (j' < cols g)%N -> sV i j = sV i' j' -> i = i' /\ j = j'.
Proof.
  intros i j i' j' Hi Hj Hi' Hj' E. apply (f_equal to_Z) in E.
  rewrite !phi_sV in E by assumption.
  destruct (cell_inj Cz (Z.of_N i) (Z.of_N j) (Z.of_N i') (Z.of_N j')) as [E1 E2];
    try lia.
Qed.

Lemma sH_sV : forall i j i' j', (i < rows g)%N -> (j < cols g)%N ->
  (i' < rows g)%N -> (j' < cols g)%N -> sH i j <> sV i' j'.
Proof.
  intros i j i' j' Hi Hj Hi' Hj' E. apply (f_equal to_Z) in E.
  rewrite phi_sH, phi_sV in E by assumption. lia.
Qed.

Lemma phi_updH : forall X res res' i0 j0 D,
  (i0 < rows g)%N -> (j0 + 1 < cols g)%N ->
  (forall x, x <> sH i0 j0 -> res'.[x] = res.[x]) ->
  (φ (res'.[sH i0 j0])) = ((φ (res.[sH i0 j0])) + D)%Z ->
  phi X res' = (phi X res - D * (b2z (X i0 j0) - b2z (X i0 (j0 + 1)%N)))%Z.
Proof.
  intros X res res' i0 j0 D Hi0 Hj0 Ho Hs. unfold phi.
  assert (EV : phiV X res' = phiV X res).
  { unfold phiV. apply zsum_ext. intros k Hk. apply zsum_ext. intros l Hl.
    unfold fV. rewrite Ho; [reflexivity|].
    intro E. symmetry in E. revert E. apply sH_sV; lia. }
  rewrite EV.
  enough (phiH X res' = phiH X res - D * (b2z (X i0 j0) - b2z (X i0 (j0 + 1)%N)))%Z by lia.
  unfold phiH.
  apply (zsum_upd _ _ _ (N.to_nat i0)); [lia | |].
  - intros k Hk Hne. apply zsum_ext. intros l Hl. unfold fH. rewrite Ho; [reflexivity|].
    intro E. apply sH_inj in E; lia.
  - rewrite N2Nat.id.
    apply (zsum_upd _ _ _ (N.to_nat j0)); [lia | |].
    + intros l Hl Hne. unfold fH. rewrite Ho; [reflexivity|].
      intro E. apply sH_inj in E; lia.
    + rewrite N2Nat.id. unfold fH. rewrite Hs. ring.
Qed.

Lemma phi_updV : forall X res res' i0 j0 D,
  (i0 + 1 < rows g)%N -> (j0 < cols g)%N ->
  (forall x, x <> sV i0 j0 -> res'.[x] = res.[x]) ->
  (φ (res'.[sV i0 j0])) = ((φ (res.[sV i0 j0])) + D)%Z ->
  phi X res' = (phi X res - D * (b2z (X i0 j0) - b2z (X (i0 + 1)%N j0)))%Z.
Proof.
  intros X res res' i0 j0 D Hi0 Hj0 Ho Hs. unfold phi.
  assert (EH : phiH X res' = phiH X res).
  { unfold phiH. apply zsum_ext. intros k Hk. apply zsum_ext. intros l Hl.
    unfold fH. rewrite Ho; [reflexivity|].
    apply sH_sV; lia. }
  rewrite EH.
  enough (phiV X res' = phiV X res - D * (b2z (X i0 j0) - b2z (X (i0 + 1)%N j0)))%Z by lia.
  unfold phiV.
  apply (zsum_upd _ _ _ (N.to_nat i0)); [lia | |].
  - intros k Hk Hne. apply zsum_ext. intros l Hl. unfold fV. rewrite Ho; [reflexivity|].
    intro E. apply sV_inj in E; lia.
  - rewrite N2Nat.id.
    apply (zsum_upd _ _ _ (N.to_nat j0)); [lia | |].
    + intros l Hl Hne. unfold fV. rewrite Ho; [reflexivity|].
      intro E. apply sV_inj in E; lia.
    + rewrite N2Nat.id. unfold fV. rewrite Hs. ring.
Qed.

Lemma term_le : forall (x y hf : bool) (P : N) (r : Z),
  (0 <= r <= 2 * Z.of_N P)%Z -> (x <> y -> hf = true) ->
  ((b2z x - b2z y) * (Z.of_N P - r) <= Z.of_N (if hf then P else 0%N))%Z.
Proof.
  intros x y hf P r Hr Hf. unfold b2z.
  destruct x, y, hf; cbv beta iota; try lia;
    specialize (Hf ltac:(discriminate)); discriminate.
Qed.

Lemma term_eq : forall (x y : bool) (P : N) (r : Z),
  (x = true -> y = false -> r = 0%Z) -> (x = false -> y = true -> r = 2 * Z.of_N P)%Z ->
  ((b2z x - b2z y) * (Z.of_N P - r) = Z.of_N (if xorb x y then P else 0%N))%Z.
Proof.
  intros x y P r H1 H2. unfold b2z. destruct x, y; cbv beta iota delta [xorb]; try lia;
    first [rewrite H1 by reflexivity | rewrite H2 by reflexivity]; lia.
Qed.

Lemma term_43 : forall (x y : bool) (P : N) (r : Z),
  (0 <= r <= 2 * Z.of_N P)%Z -> (Z.of_N P <= 43)%Z ->
  ((b2z x - b2z y) * (Z.of_N P - r) <= 43)%Z.
Proof. intros x y P r Hr HP. unfold b2z. destruct x, y; cbv beta iota; lia. Qed.

Lemma cost_split : forall hf vf,
  Z.of_N (cost b h g hf vf) =
  (zsum (fun i => zsum (fun j => Z.of_N (if hf i j then price b h g i j i (j + 1) else 0%N))
                       (N.to_nat (cols g - 1))) (N.to_nat (rows g)) +
   zsum (fun i => zsum (fun j => Z.of_N (if vf i j then price b h g i j (i + 1) j else 0%N))
                       (N.to_nat (cols g))) (N.to_nat (rows g - 1)))%Z.
Proof.
  intros hf vf. unfold cost. rewrite N2Z.inj_add, !zsum_nsum.
  f_equal; apply zsum_ext; intros k Hk; apply zsum_nsum.
Qed.

Lemma phi_le_cost : forall X res hf vf, bnd res ->
  (forall i j, (i < rows g)%N -> (j + 1 < cols g)%N -> X i j <> X i (j + 1)%N -> hf i j = true) ->
  (forall i j, (i + 1 < rows g)%N -> (j < cols g)%N -> X i j <> X (i + 1)%N j -> vf i j = true) ->
  (phi X res <= Z.of_N (cost b h g hf vf))%Z.
Proof.
  intros X res hf vf [BH BV] HH HV. rewrite cost_split. unfold phi, phiH, phiV.
  apply Z.add_le_mono.
  - apply zsum_le. intros k Hk. apply zsum_le. intros l Hl.
    apply term_le.
    + pose proof (to_Z_bounded (res.[sH (N.of_nat k) (N.of_nat l)])).
      pose proof (BH (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)). unfold pH in *. lia.
    + apply HH; lia.
  - apply zsum_le. intros k Hk. apply zsum_le. intros l Hl.
    apply term_le.
    + pose proof (to_Z_bounded (res.[sV (N.of_nat k) (N.of_nat l)])).
      pose proof (BV (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)). unfold pV in *. lia.
    + apply HV; lia.
Qed.

Definition cutH (X : N -> N -> bool) i j := xorb (X i j) (X i (j + 1)%N).
Definition cutV (X : N -> N -> bool) i j := xorb (X i j) (X (i + 1)%N j).

Lemma phi_cut : forall X res,
  (forall i j, (i < rows g)%N -> (j + 1 < cols g)%N ->
     (X i j = true -> X i (j + 1)%N = false -> (φ (res.[sH i j])) = 0%Z) /\
     (X i j = false -> X i (j + 1)%N = true -> (φ (res.[sH i j])) = 2 * pH i j)%Z) ->
  (forall i j, (i + 1 < rows g)%N -> (j < cols g)%N ->
     (X i j = true -> X (i + 1)%N j = false -> (φ (res.[sV i j])) = 0%Z) /\
     (X i j = false -> X (i + 1)%N j = true -> (φ (res.[sV i j])) = 2 * pV i j)%Z) ->
  phi X res = Z.of_N (cost b h g (cutH X) (cutV X)).
Proof.
  intros X res HH HV. rewrite cost_split. unfold phi, phiH, phiV.
  f_equal.
  - apply zsum_ext. intros k Hk. apply zsum_ext. intros l Hl.
    destruct (HH (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)) as [A B].
    apply term_eq; assumption.
  - apply zsum_ext. intros k Hk. apply zsum_ext. intros l Hl.
    destruct (HV (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)) as [A B].
    apply term_eq; assumption.
Qed.

Lemma phi_le_bound : forall X res, bnd res -> (phi X res <= 86 * (Rz * Cz))%Z.
Proof.
  intros X res [BH BV]. destruct vi_rc as [HR HC]. unfold phi, phiH, phiV.
  assert (A : (zsum (fun i => zsum (fun j => (b2z (X i j) - b2z (X i (j + 1)%N)) * fH res i j)%Z
                      (N.to_nat (cols g - 1))) (N.to_nat (rows g))
              <= Z.of_nat (N.to_nat (rows g)) * (Z.of_nat (N.to_nat (cols g - 1)) * 43))%Z).
  { apply zsum_const_le. intros k Hk. apply zsum_const_le. intros l Hl.
    unfold fH, pH. apply term_43.
    + pose proof (to_Z_bounded (res.[sH (N.of_nat k) (N.of_nat l)])).
      pose proof (BH (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)). unfold pH in *. lia.
    + apply price_bounds. }
  assert (B : (zsum (fun i => zsum (fun j => (b2z (X i j) - b2z (X (i + 1)%N j)) * fV res i j)%Z
                      (N.to_nat (cols g))) (N.to_nat (rows g - 1))
              <= Z.of_nat (N.to_nat (rows g - 1)) * (Z.of_nat (N.to_nat (cols g)) * 43))%Z).
  { apply zsum_const_le. intros k Hk. apply zsum_const_le. intros l Hl.
    unfold fV, pV. apply term_43.
    + pose proof (to_Z_bounded (res.[sV (N.of_nat k) (N.of_nat l)])).
      pose proof (BV (N.of_nat k) (N.of_nat l) ltac:(lia) ltac:(lia)). unfold pV in *. lia.
    + apply price_bounds. }
  replace (Z.of_nat (N.to_nat (rows g))) with Rz in A by lia.
  replace (Z.of_nat (N.to_nat (rows g - 1))) with (Rz - 1)%Z in B by lia.
  replace (Z.of_nat (N.to_nat (cols g))) with Cz in B by lia.
  replace (Z.of_nat (N.to_nat (cols g - 1))) with (Cz - 1)%Z in A by lia.
  clear -A B HR HC. nia.
Qed.

(* ------------------------------------------------------------------ *)
(* Cells and directions, on the machine side                           *)
(* ------------------------------------------------------------------ *)

Variables (Rm Cm nm : int) (lt : array bool).
Hypothesis HRm : (φ Rm) = Rz.
Hypothesis HCm : (φ Cm) = Cz.
Hypothesis Hnm : (φ nm) = (Rz * Cz)%Z.

Definition ci (u : int) : N := Z.to_N ((φ u) / Cz).
Definition cj (u : int) : N := Z.to_N ((φ u) mod Cz).
Definition litm (u : int) : bool := lit b h g (ci u) (cj u).
Definition cell (i j : N) : int := of_Z (Z.of_N i * Cz + Z.of_N j).

Hypothesis Hlt : forall u, ((φ u) < (φ nm))%Z -> lt.[u] = litm u.

Lemma coord_unique : forall C x q r : Z, (0 <= r < C)%Z -> x = (q * C + r)%Z ->
  (x / C = q /\ x mod C = r)%Z.
Proof.
  intros C x q r Hr Ex. split.
  - symmetry. apply (Z.div_unique_pos _ _ _ r); lia.
  - symmetry. apply (Z.mod_unique_pos _ _ q); lia.
Qed.

Lemma cell_facts : forall u, ((φ u) < Rz * Cz)%Z ->
  (ci u < rows g)%N /\ (cj u < cols g)%N /\
  (φ u) = (Z.of_N (ci u) * Cz + Z.of_N (cj u))%Z.
Proof.
  intros u Hu. destruct vi_rc as [HR HC]. pose proof (to_Z_bounded u).
  unfold ci, cj.
  pose proof (Z.div_mod (φ u) Cz ltac:(lia)).
  pose proof (Z.mod_pos_bound (φ u) Cz ltac:(lia)).
  assert (0 <= (φ u) / Cz)%Z by (apply Z.div_pos; lia).
  assert ((φ u) / Cz < Rz)%Z by (apply Z.div_lt_upper_bound; lia).
  rewrite !Z2N.id by lia. lia.
Qed.

Lemma cell_coords : forall i j, (i < rows g)%N -> (j < cols g)%N ->
  (φ (cell i j)) = (Z.of_N i * Cz + Z.of_N j)%Z /\ ci (cell i j) = i /\ cj (cell i j) = j.
Proof.
  intros i j Hi Hj. destruct vi_rc as [HR HC].
  assert (E : (φ (cell i j)) = (Z.of_N i * Cz + Z.of_N j)%Z).
  { unfold cell. rewrite of_Z_spec. apply Z.mod_small. rewrite wB_val.
    assert (Z.of_N i * Cz <= 30 * 30)%Z by (clear -HR HC Hi; nia). lia. }
  destruct (coord_unique Cz (φ (cell i j)) (Z.of_N i) (Z.of_N j)) as [E1 E2]; [lia|exact E|].
  unfold ci, cj. rewrite E1, E2. split; [exact E|]. split; apply N2Z.id.
Qed.

Lemma cell_of : forall u, ((φ u) < Rz * Cz)%Z -> cell (ci u) (cj u) = u.
Proof.
  intros u Hu. destruct (cell_facts u Hu) as (A & B & E).
  apply to_Z_inj. rewrite (proj1 (cell_coords _ _ A B)). lia.
Qed.

Lemma sH_cell : forall u, ((φ u) < Rz * Cz)%Z -> (φ (sH (ci u) (cj u))) = (2 * (φ u))%Z.
Proof.
  intros u Hu. destruct (cell_facts u Hu) as (A & B & E). rewrite phi_sH by assumption. lia.
Qed.

Lemma sV_cell : forall u, ((φ u) < Rz * Cz)%Z -> (φ (sV (ci u) (cj u))) = (2 * (φ u) + 1)%Z.
Proof.
  intros u Hu. destruct (cell_facts u Hu) as (A & B & E). rewrite phi_sV by assumption. lia.
Qed.

Definition hd (p d : int) : Prop :=
  ((φ p) < Rz * Cz)%Z /\
  ((d = 0%uint63 /\ (φ p) mod Cz + 1 < Cz) \/ (d = 1%uint63 /\ 0 < (φ p) mod Cz) \/
   (d = 2%uint63 /\ (φ p) + Cz < Rz * Cz) \/ (d = 3%uint63 /\ Cz <= (φ p)))%Z.

Lemma nbr0 : forall C p, nbr C p 0 = p + 1. Proof. reflexivity. Qed.
Lemma nbr1 : forall C p, nbr C p 1 = p - 1. Proof. reflexivity. Qed.
Lemma nbr2 : forall C p, nbr C p 2 = p + C. Proof. reflexivity. Qed.
Lemma nbr3 : forall C p, nbr C p 3 = p - C. Proof. reflexivity. Qed.
Lemma slot0 : forall C p, slot C p 0 = 2 * p. Proof. reflexivity. Qed.
Lemma slot1 : forall C p, slot C p 1 = 2 * (p - 1). Proof. reflexivity. Qed.
Lemma slot2 : forall C p, slot C p 2 = 2 * p + 1. Proof. reflexivity. Qed.
Lemma slot3 : forall C p, slot C p 3 = 2 * (p - C) + 1. Proof. reflexivity. Qed.

(* the neighbour across a direction: its index and coordinates *)
Lemma nbr_facts : forall p d, hd p d ->
  let w := nbr Cm p d in
  ((φ w) < Rz * Cz)%Z /\
  (d = 0%uint63 -> (φ w) = (φ p) + 1 /\ ci w = ci p /\ cj w = (cj p + 1)%N
            /\ (φ (slot Cm p d)) = 2 * (φ p))%Z /\
  (d = 1%uint63 -> (φ p) = (φ w) + 1 /\ ci w = ci p /\ (cj w + 1)%N = cj p
            /\ (φ (slot Cm p d)) = 2 * (φ w))%Z /\
  (d = 2%uint63 -> (φ w) = (φ p) + Cz /\ ci w = (ci p + 1)%N /\ cj w = cj p
            /\ (φ (slot Cm p d)) = 2 * (φ p) + 1)%Z /\
  (d = 3%uint63 -> (φ p) = (φ w) + Cz /\ (ci w + 1)%N = ci p /\ cj w = cj p
            /\ (φ (slot Cm p d)) = 2 * (φ w) + 1)%Z.
Proof.
  intros p d [Hp Hd]. destruct vi_rc as [HR HC]. pose proof (to_Z_bounded p).
  pose proof (Z.div_mod (φ p) Cz ltac:(lia)) as DM.
  pose proof (Z.mod_pos_bound (φ p) Cz ltac:(lia)) as MB.
  assert (Hq : (0 <= (φ p) / Cz)%Z) by (apply Z.div_pos; lia).
  assert (Hn900 : (Rz * Cz <= 900)%Z) by (clear -HR HC; nia).
  assert (Hqr : ((φ p) / Cz < Rz)%Z) by (apply Z.div_lt_upper_bound; lia).
  assert (Hqc : (Cz * ((φ p) / Cz) + Cz <= Rz * Cz)%Z) by (clear -Hqr HC; nia).
  unfold ci, cj.
  destruct Hd as [[-> Hm] | [[-> Hm] | [[-> Hm] | [-> Hm]]]]; cbv zeta.
  - rewrite nbr0, slot0.
    assert (Ew : (φ (p + 1)) = ((φ p) + 1)%Z) by sia.
    destruct (coord_unique Cz (φ (p + 1)) ((φ p) / Cz) ((φ p) mod Cz + 1)) as [E1 E2]; [lia|lia|].
    split; [lia|]. split; [intros _|split; [dd|split; dd]].
    rewrite E1, E2. split; [exact Ew|]. split; [reflexivity|]. split; [lia|].
    rewrite mul_spec. change (φ 2) with 2%Z. apply Z.mod_small. rewrite wB_val. lia.
  - rewrite nbr1, slot1.
    assert (Ew : (φ (p - 1)) = ((φ p) - 1)%Z) by sia.
    destruct (coord_unique Cz (φ (p - 1)) ((φ p) / Cz) ((φ p) mod Cz - 1)) as [E1 E2]; [lia|lia|].
    split; [lia|]. split; [dd|]. split; [intros _|split; dd].
    rewrite E1, E2. split; [lia|]. split; [reflexivity|]. split; [lia|].
    rewrite mul_spec, Ew. change (φ 2) with 2%Z. apply Z.mod_small. rewrite wB_val. lia.
  - rewrite nbr2, slot2.
    assert (Ew : (φ (p + Cm)) = ((φ p) + Cz)%Z) by sia.
    destruct (coord_unique Cz (φ (p + Cm)) ((φ p) / Cz + 1) ((φ p) mod Cz)) as [E1 E2]; [lia|lia|].
    split; [lia|]. split; [dd|]. split; [dd|]. split; [intros _|dd].
    rewrite E1, E2. split; [exact Ew|]. split; [lia|]. split; [reflexivity|].
    rewrite add_spec, mul_spec. change (φ 2) with 2%Z. change (φ 1) with 1%Z.
    rewrite (Z.mod_small (2 * (φ p))) by (rewrite wB_val; lia).
    apply Z.mod_small. rewrite wB_val. lia.
  - rewrite nbr3, slot3.
    assert (Ew : (φ (p - Cm)) = ((φ p) - Cz)%Z) by sia.
    assert (Hq1 : (1 <= (φ p) / Cz)%Z) by (apply Z.div_le_lower_bound; lia).
    destruct (coord_unique Cz (φ (p - Cm)) ((φ p) / Cz - 1) ((φ p) mod Cz)) as [E1 E2]; [lia|lia|].
    split; [lia|]. split; [dd|]. split; [dd|]. split; [dd|].
    intros _. rewrite E1, E2. split; [lia|]. split; [lia|]. split; [reflexivity|].
    rewrite add_spec, mul_spec, Ew. change (φ 2) with 2%Z. change (φ 1) with 1%Z.
    rewrite (Z.mod_small (2 * ((φ p) - Cz))) by (rewrite wB_val; lia).
    apply Z.mod_small. rewrite wB_val. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Residuals and augmentation along one edge                           *)
(* ------------------------------------------------------------------ *)

Lemma resid0 : forall lt res C p, resid lt res C p 0 = res.[slot C p 0].
Proof. reflexivity. Qed.
Lemma resid1 : forall lt res C p,
  resid lt res C p 1 = 2 * capf lt.[p] lt.[nbr C p 1] - res.[slot C p 1].
Proof. reflexivity. Qed.
Lemma resid2 : forall lt res C p, resid lt res C p 2 = res.[slot C p 2].
Proof. reflexivity. Qed.
Lemma resid3 : forall lt res C p,
  resid lt res C p 3 = 2 * capf lt.[p] lt.[nbr C p 3] - res.[slot C p 3].
Proof. reflexivity. Qed.
Lemma aug0 : forall res C p dl,
  aug res C p 0 dl = res.[slot C p 0 <- res.[slot C p 0] - dl].
Proof. reflexivity. Qed.
Lemma aug1 : forall res C p dl,
  aug res C p 1 dl = res.[slot C p 1 <- res.[slot C p 1] + dl].
Proof. reflexivity. Qed.
Lemma aug2 : forall res C p dl,
  aug res C p 2 dl = res.[slot C p 2 <- res.[slot C p 2] - dl].
Proof. reflexivity. Qed.
Lemma aug3 : forall res C p dl,
  aug res C p 3 dl = res.[slot C p 3 <- res.[slot C p 3] + dl].
Proof. reflexivity. Qed.

Lemma capf_price : forall i j i' j' p q,
  litm p = lit b h g i' j' -> litm q = lit b h g i j ->
  (φ (capf (litm p) (litm q))) = Z.of_N (price b h g i j i' j').
Proof.
  intros i j i' j' p q Ep Eq. unfold price. rewrite Ep, Eq.
  destruct (lit b h g i j), (lit b h g i' j'); reflexivity.
Qed.

Lemma bnd_updH : forall res res' i0 j0, bnd res ->
  (i0 < rows g)%N -> (j0 + 1 < cols g)%N ->
  (forall x, x <> sH i0 j0 -> res'.[x] = res.[x]) ->
  ((φ (res'.[sH i0 j0])) <= 2 * pH i0 j0)%Z -> bnd res'.
Proof.
  intros res res' i0 j0 [BH BV] Hi0 Hj0 Ho Hk. split.
  - intros i j Hi Hj. destruct (N.eq_dec i i0) as [-> | Ni];
      [destruct (N.eq_dec j j0) as [-> | Nj]; [exact Hk|] |];
      rewrite Ho; [apply BH; assumption | | apply BH; assumption |];
      intro E; apply sH_inj in E; lia.
  - intros i j Hi Hj. rewrite Ho; [apply BV; assumption|].
    intro E. symmetry in E. revert E. apply sH_sV; lia.
Qed.

Lemma bnd_updV : forall res res' i0 j0, bnd res ->
  (i0 + 1 < rows g)%N -> (j0 < cols g)%N ->
  (forall x, x <> sV i0 j0 -> res'.[x] = res.[x]) ->
  ((φ (res'.[sV i0 j0])) <= 2 * pV i0 j0)%Z -> bnd res'.
Proof.
  intros res res' i0 j0 [BH BV] Hi0 Hj0 Ho Hk. split.
  - intros i j Hi Hj. rewrite Ho; [apply BH; assumption|].
    apply sH_sV; lia.
  - intros i j Hi Hj. destruct (N.eq_dec i i0) as [-> | Ni];
      [destruct (N.eq_dec j j0) as [-> | Nj]; [exact Hk|] |];
      rewrite Ho; [apply BV; assumption | | apply BV; assumption |];
      intro E; apply sV_inj in E; lia.
Qed.

Lemma lit_of : forall p, ((φ p) < Rz * Cz)%Z -> lt.[p] = lit b h g (ci p) (cj p).
Proof. intros p Hp. rewrite Hlt by lia. reflexivity. Qed.

Lemma hd_dir : forall p d, hd p d ->
  ((φ p) < Rz * Cz)%Z /\
  (d = 0%uint63 -> (φ p) mod Cz + 1 < Cz)%Z /\ (d = 1%uint63 -> 0 < (φ p) mod Cz)%Z /\
  (d = 2%uint63 -> (φ p) + Cz < Rz * Cz)%Z /\ (d = 3%uint63 -> Cz <= (φ p))%Z.
Proof.
  intros p d [Hp Hd]. split; [exact Hp|].
  destruct Hd as [[-> Hm] | [[-> Hm] | [[-> Hm] | [-> Hm]]]];
    repeat split; intros E; try exact Hm; revert E; dd.
Qed.

(* the residual of an edge, and augmenting it, direction by direction *)
Section Edge.
Variables (res : array int) (p : int) (dl : int).
Hypothesis Bres : bnd res.
Hypothesis Lres : (φ (PArray.length res)) = (2 * (Rz * Cz))%Z.

Lemma len_slot : forall k, ((φ k) < 2 * (Rz * Cz))%Z -> (k <? PArray.length res) = true.
Proof. intros k Hk. rewrite ltb_spec, Lres. exact Hk. Qed.

Lemma small_sub : forall x y : int, ((φ y) <= (φ x))%Z -> (φ (x - y)) = ((φ x) - (φ y))%Z.
Proof. intros x y H. rewrite sub_spec. apply Z.mod_small. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.

Lemma small_add : forall x y : int, ((φ x) <= 1000)%Z -> ((φ y) <= 1000)%Z -> (φ (x + y)) = ((φ x) + (φ y))%Z.
Proof. intros x y H1 H2. rewrite add_spec. apply Z.mod_small. rewrite wB_val. pose proof (to_Z_bounded x). pose proof (to_Z_bounded y). lia. Qed.

Lemma two_cap : forall x y : bool, (φ (2 * capf x y)) = (2 * (φ (capf x y)))%Z /\ ((φ (capf x y)) <= 43)%Z.
Proof. intros x y. unfold capf. destruct (x && y); split; reflexivity || (cbv; discriminate). Qed.

Lemma edge0 : hd p 0 ->
  let w := nbr Cm p 0 in
  (φ (resid lt res Cm p 0)) = (φ (res.[sH (ci p) (cj p)])) /\  ((1 <= (φ dl) <= (φ (resid lt res Cm p 0)))%Z ->
   let res' := aug res Cm p 0 dl in
   (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\   (forall x, x <> slot Cm p 0 -> res'.[x] = res.[x]) /\   forall X, phi X res' = (phi X res + (φ dl) * (b2z (X (ci p) (cj p)) - b2z (X (ci w) (cj w))))%Z).
Proof.
  intros Hhd w.
  pose proof (nbr_facts p 0 Hhd) as (Hw & F & _). specialize (F eq_refl).
  destruct F as (Ew & Ci & Cj & Es). fold w in Ew, Ci, Cj.
  destruct (hd_dir p 0 Hhd) as (Hp & Hm & _). specialize (Hm eq_refl).
  destruct (cell_facts p Hp) as (Pi & Pj & Pe).
  assert (Ek : slot Cm p 0 = sH (ci p) (cj p)) by (apply to_Z_inj; rewrite Es, sH_cell; lia).
  assert (Hr : (φ (resid lt res Cm p 0)) = (φ (res.[sH (ci p) (cj p)]))) by (rewrite resid0, Ek; reflexivity).
  split; [exact Hr|]. intros Hdl res'.
  assert (Ho : forall x, x <> sH (ci p) (cj p) -> res'.[x] = res.[x]).
  { intros x Hx. unfold res'. rewrite aug0, Ek. apply aget_set_other. congruence. }
  assert (Hn : (φ (res'.[sH (ci p) (cj p)])) = ((φ (res.[sH (ci p) (cj p)])) + - (φ dl))%Z).
  { unfold res'. rewrite aug0, Ek, aget_set_same.
    - rewrite small_sub by lia. lia.
    - apply len_slot. rewrite <- Ek, Es. lia. }
  assert (Hj1 : (cj p + 1 < cols g)%N) by (unfold cj; lia).
  split; [unfold res'; rewrite aug0, alength_set; exact Lres|].
  split; [apply (bnd_updH res res' (ci p) (cj p) Bres Pi Hj1 Ho); rewrite Hn;
          destruct Bres as [BH _]; pose proof (BH _ _ Pi Hj1); lia|].
  split; [intros x Hx; apply Ho; rewrite <- Ek; exact Hx|].
  intros X. rewrite (phi_updH X res res' (ci p) (cj p) (- (φ dl)) Pi Hj1 Ho Hn).
  rewrite Ci, Cj. ring.
Qed.

Lemma edge1 : hd p 1 ->
  let w := nbr Cm p 1 in
  (φ (resid lt res Cm p 1)) = (2 * pH (ci w) (cj w) - (φ (res.[sH (ci w) (cj w)])))%Z /\  ((1 <= (φ dl) <= (φ (resid lt res Cm p 1)))%Z ->
   let res' := aug res Cm p 1 dl in
   (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\   (forall x, x <> slot Cm p 1 -> res'.[x] = res.[x]) /\   forall X, phi X res' = (phi X res + (φ dl) * (b2z (X (ci p) (cj p)) - b2z (X (ci w) (cj w))))%Z).
Proof.
  intros Hhd w.
  pose proof (nbr_facts p 1 Hhd) as (Hw & _ & F & _). specialize (F eq_refl).
  destruct F as (Ew & Ci & Cj & Es). fold w in Hw, Ew, Ci, Cj.
  destruct (hd_dir p 1 Hhd) as (Hp & _ & Hm & _). specialize (Hm eq_refl).
  destruct (cell_facts w Hw) as (Wi & Wj & We).
  assert (Hj1 : (cj w + 1 < cols g)%N) by (rewrite Cj; destruct (cell_facts p Hp) as (_ & A & _); exact A).
  assert (Ek : slot Cm p 1 = sH (ci w) (cj w)) by (apply to_Z_inj; rewrite Es, sH_cell; lia).
  destruct Bres as [BH BV].
  pose proof (BH _ _ Wi Hj1) as Bw.
  assert (Hc : (φ (capf lt.[p] lt.[w])) = pH (ci w) (cj w)).
  { rewrite (lit_of p Hp), (lit_of w Hw). unfold pH, price.
    rewrite <- Ci, <- Cj. rewrite andb_comm. unfold capf. destruct (_ && _); reflexivity. }
  assert (Hr : (φ (resid lt res Cm p 1)) = (2 * pH (ci w) (cj w) - (φ (res.[sH (ci w) (cj w)])))%Z).
  { rewrite resid1, Ek. fold w. destruct (two_cap lt.[p] lt.[w]) as [T1 T2].
    rewrite small_sub; rewrite T1, Hc; [reflexivity|]. exact Bw. }
  split; [exact Hr|]. intros Hdl res'.
  assert (Ho : forall x, x <> sH (ci w) (cj w) -> res'.[x] = res.[x]).
  { intros x Hx. unfold res'. rewrite aug1, Ek. apply aget_set_other. congruence. }
  pose proof (price_bounds (ci w) (cj w) (ci w) (cj w + 1)) as PB. fold (pH (ci w) (cj w)) in PB.
  assert (Hn : (φ (res'.[sH (ci w) (cj w)])) = ((φ (res.[sH (ci w) (cj w)])) + (φ dl))%Z).
  { unfold res'. rewrite aug1, Ek, aget_set_same.
    - apply small_add; lia.
    - apply len_slot. rewrite <- Ek, Es. lia. }
  split; [unfold res'; rewrite aug1, alength_set; exact Lres|].
  split; [apply (bnd_updH res res' (ci w) (cj w) (conj BH BV) Wi Hj1 Ho); rewrite Hn; lia|].
  split; [intros x Hx; apply Ho; rewrite <- Ek; exact Hx|].
  intros X. rewrite (phi_updH X res res' (ci w) (cj w) (φ dl) Wi Hj1 Ho Hn).
  rewrite Ci, Cj. ring.
Qed.

Lemma edge2 : hd p 2 ->
  let w := nbr Cm p 2 in
  (φ (resid lt res Cm p 2)) = (φ (res.[sV (ci p) (cj p)])) /\  ((1 <= (φ dl) <= (φ (resid lt res Cm p 2)))%Z ->
   let res' := aug res Cm p 2 dl in
   (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\   (forall x, x <> slot Cm p 2 -> res'.[x] = res.[x]) /\   forall X, phi X res' = (phi X res + (φ dl) * (b2z (X (ci p) (cj p)) - b2z (X (ci w) (cj w))))%Z).
Proof.
  intros Hhd w.
  pose proof (nbr_facts p 2 Hhd) as (Hw & _ & _ & F & _). specialize (F eq_refl).
  destruct F as (Ew & Ci & Cj & Es). fold w in Hw, Ew, Ci, Cj.
  destruct (hd_dir p 2 Hhd) as (Hp & _ & _ & Hm & _). specialize (Hm eq_refl).
  destruct (cell_facts p Hp) as (Pi & Pj & Pe).
  destruct (cell_facts w Hw) as (Wi & Wj & We).
  assert (Ek : slot Cm p 2 = sV (ci p) (cj p)) by (apply to_Z_inj; rewrite Es, sV_cell; lia).
  assert (Hr : (φ (resid lt res Cm p 2)) = (φ (res.[sV (ci p) (cj p)]))) by (rewrite resid2, Ek; reflexivity).
  split; [exact Hr|]. intros Hdl res'.
  assert (Ho : forall x, x <> sV (ci p) (cj p) -> res'.[x] = res.[x]).
  { intros x Hx. unfold res'. rewrite aug2, Ek. apply aget_set_other. congruence. }
  assert (Hn : (φ (res'.[sV (ci p) (cj p)])) = ((φ (res.[sV (ci p) (cj p)])) + - (φ dl))%Z).
  { unfold res'. rewrite aug2, Ek, aget_set_same.
    - rewrite small_sub by lia. lia.
    - apply len_slot. rewrite <- Ek, Es. lia. }
  assert (Hi1 : (ci p + 1 < rows g)%N) by (rewrite <- Ci; exact Wi).
  split; [unfold res'; rewrite aug2, alength_set; exact Lres|].
  split; [apply (bnd_updV res res' (ci p) (cj p) Bres Hi1 Pj Ho); rewrite Hn;
          destruct Bres as [_ BV]; pose proof (BV _ _ Hi1 Pj); lia|].
  split; [intros x Hx; apply Ho; rewrite <- Ek; exact Hx|].
  intros X. rewrite (phi_updV X res res' (ci p) (cj p) (- (φ dl)) Hi1 Pj Ho Hn).
  rewrite Ci, Cj. ring.
Qed.

Lemma edge3 : hd p 3 ->
  let w := nbr Cm p 3 in
  (φ (resid lt res Cm p 3)) = (2 * pV (ci w) (cj w) - (φ (res.[sV (ci w) (cj w)])))%Z /\  ((1 <= (φ dl) <= (φ (resid lt res Cm p 3)))%Z ->
   let res' := aug res Cm p 3 dl in
   (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\   (forall x, x <> slot Cm p 3 -> res'.[x] = res.[x]) /\   forall X, phi X res' = (phi X res + (φ dl) * (b2z (X (ci p) (cj p)) - b2z (X (ci w) (cj w))))%Z).
Proof.
  intros Hhd w.
  pose proof (nbr_facts p 3 Hhd) as (Hw & _ & _ & _ & F). specialize (F eq_refl).
  destruct F as (Ew & Ci & Cj & Es). fold w in Hw, Ew, Ci, Cj.
  destruct (hd_dir p 3 Hhd) as (Hp & _ & _ & _ & Hm). specialize (Hm eq_refl).
  destruct (cell_facts w Hw) as (Wi & Wj & We).
  assert (Hi1 : (ci w + 1 < rows g)%N) by (rewrite Ci; destruct (cell_facts p Hp) as (A & _ & _); exact A).
  assert (Ek : slot Cm p 3 = sV (ci w) (cj w)) by (apply to_Z_inj; rewrite Es, sV_cell; lia).
  destruct Bres as [BH BV].
  pose proof (BV _ _ Hi1 Wj) as Bw.
  assert (Hc : (φ (capf lt.[p] lt.[w])) = pV (ci w) (cj w)).
  { rewrite (lit_of p Hp), (lit_of w Hw). unfold pV, price.
    rewrite <- Ci, <- Cj. rewrite andb_comm. unfold capf. destruct (_ && _); reflexivity. }
  assert (Hr : (φ (resid lt res Cm p 3)) = (2 * pV (ci w) (cj w) - (φ (res.[sV (ci w) (cj w)])))%Z).
  { rewrite resid3, Ek. fold w. destruct (two_cap lt.[p] lt.[w]) as [T1 T2].
    rewrite small_sub; rewrite T1, Hc; [reflexivity|]. exact Bw. }
  split; [exact Hr|]. intros Hdl res'.
  assert (Ho : forall x, x <> sV (ci w) (cj w) -> res'.[x] = res.[x]).
  { intros x Hx. unfold res'. rewrite aug3, Ek. apply aget_set_other. congruence. }
  pose proof (price_bounds (ci w) (cj w) (ci w + 1) (cj w)) as PB. fold (pV (ci w) (cj w)) in PB.
  assert (Hn : (φ (res'.[sV (ci w) (cj w)])) = ((φ (res.[sV (ci w) (cj w)])) + (φ dl))%Z).
  { unfold res'. rewrite aug3, Ek, aget_set_same.
    - apply small_add; lia.
    - apply len_slot. rewrite <- Ek, Es. lia. }
  split; [unfold res'; rewrite aug3, alength_set; exact Lres|].
  split; [apply (bnd_updV res res' (ci w) (cj w) (conj BH BV) Hi1 Wj Ho); rewrite Hn; lia|].
  split; [intros x Hx; apply Ho; rewrite <- Ek; exact Hx|].
  intros X. rewrite (phi_updV X res res' (ci w) (cj w) (φ dl) Hi1 Wj Ho Hn).
  rewrite Ci, Cj. ring.
Qed.

End Edge.

Lemma dir_cases : forall p d, hd p d ->
  d = 0%uint63 \/ d = 1%uint63 \/ d = 2%uint63 \/ d = 3%uint63.
Proof. intros p d [_ Hd]. destruct Hd as [[-> _]|[[-> _]|[[-> _]|[-> _]]]]; auto. Qed.

Lemma edge_aug : forall res p d dl, hd p d -> bnd res ->
  (φ (PArray.length res)) = (2 * (Rz * Cz))%Z ->
  (1 <= (φ dl) <= (φ (resid lt res Cm p d)))%Z ->
  let w := nbr Cm p d in
  let res' := aug res Cm p d dl in
  (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\
  (forall x, x <> slot Cm p d -> res'.[x] = res.[x]) /\
  forall X, phi X res' = (phi X res + (φ dl) * (b2z (X (ci p) (cj p)) - b2z (X (ci w) (cj w))))%Z.
Proof.
  intros res p d dl Hhd B L Hdl.
  destruct (dir_cases p d Hhd) as [-> | [-> | [-> | ->]]].
  - exact (proj2 (edge0 res p dl B L Hhd) Hdl).
  - exact (proj2 (edge1 res p dl B L Hhd) Hdl).
  - exact (proj2 (edge2 res p dl B L Hhd) Hdl).
  - exact (proj2 (edge3 res p dl B L Hhd) Hdl).
Qed.

Lemma slot_shape : forall p d, hd p d ->
  let w := nbr Cm p d in
  exists m o : Z, (o = 0 \/ o = 1)%Z /\ (φ (slot Cm p d)) = (2 * m + o)%Z /\
    (((φ p) = m /\ (φ w) = m + 1 + o * (Cz - 1)) \/ ((φ w) = m /\ (φ p) = m + 1 + o * (Cz - 1)))%Z.
Proof.
  intros p d Hhd w.
  pose proof (nbr_facts p d Hhd) as (Hw & F0 & F1 & F2 & F3). fold w in Hw, F0, F1, F2, F3.
  destruct (dir_cases p d Hhd) as [-> | [-> | [-> | ->]]].
  - destruct (F0 eq_refl) as (E & _ & _ & S). exists (φ p), 0%Z. lia.
  - destruct (F1 eq_refl) as (E & _ & _ & S). exists (φ w), 0%Z. lia.
  - destruct (F2 eq_refl) as (E & _ & _ & S). exists (φ p), 1%Z. lia.
  - destruct (F3 eq_refl) as (E & _ & _ & S). exists (φ w), 1%Z. lia.
Qed.

Lemma slot_eq : forall a e p d, hd a e -> hd p d -> slot Cm a e = slot Cm p d ->
  (a = p /\ nbr Cm a e = nbr Cm p d) \/ (a = nbr Cm p d /\ nbr Cm a e = p).
Proof.
  intros a e p d Ha Hp E.
  destruct (slot_shape a e Ha) as (m & o & Ho & Sa & Ca).
  destruct (slot_shape p d Hp) as (m' & o' & Ho' & Sp & Cp).
  apply (f_equal to_Z) in E. rewrite Sa, Sp in E.
  destruct vi_rc as [HR HC].
  assert (m = m' /\ o = o') as [<- <-] by lia.
  assert (1 <= 1 + o * (Cz - 1))%Z by (destruct Ho as [-> | ->]; lia).
  destruct Ca as [[A1 A2] | [A1 A2]]; destruct Cp as [[P1 P2] | [P1 P2]].
  - left. split; apply to_Z_inj; lia.
  - right. split; apply to_Z_inj; lia.
  - right. split; apply to_Z_inj; lia.
  - left. split; apply to_Z_inj; lia.
Qed.

Lemma resid_frame : forall res res' k a e,
  (forall x, x <> k -> res'.[x] = res.[x]) -> slot Cm a e <> k ->
  resid lt res' Cm a e = resid lt res Cm a e.
Proof.
  intros res res' k a e Ho Hk. unfold resid. cbv zeta.
  rewrite (Ho (slot Cm a e) Hk). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Augmenting paths                                                    *)
(* ------------------------------------------------------------------ *)

Inductive path (par dist res : array int) (dl : Z) : int -> Prop :=
| path_root : forall v, ((φ v) < Rz * Cz)%Z -> (par.[v] <? 4) = false ->
    litm v = false -> path par dist res dl v
| path_step : forall v, ((φ v) < Rz * Cz)%Z -> (par.[v] <? 4) = true ->
    hd (nbr Cm v (opp par.[v])) par.[v] ->
    nbr Cm (nbr Cm v (opp par.[v])) par.[v] = v ->
    (dist.[nbr Cm v (opp par.[v])] <? dist.[v]) = true ->
    (dl <= (φ (resid lt res Cm (nbr Cm v (opp par.[v])) par.[v])))%Z ->
    path par dist res dl (nbr Cm v (opp par.[v])) -> path par dist res dl v.

Lemma path_frame : forall par dist res dl v, path par dist res dl v ->
  forall res',
  (forall a e, hd a e -> ((φ (dist.[a])) < (φ (dist.[nbr Cm a e])))%Z ->
     ((φ (dist.[nbr Cm a e])) <= (φ (dist.[v])))%Z ->
     resid lt res' Cm a e = resid lt res Cm a e) ->
  path par dist res' dl v.
Proof.
  intros par dist res dl v Hp. induction Hp as [v Hvv Hpar Hl | v Hvv Hpar Hhd Hn Hd Hr Hp IH];
    intros res' Hf.
  - apply path_root; assumption.
  - pose proof Hd as Hd'. rewrite ltb_spec in Hd'.
    refine (path_step _ _ _ _ v Hvv Hpar Hhd Hn Hd _ _).
    + rewrite Hf; [exact Hr | exact Hhd | rewrite Hn; exact Hd' | rewrite Hn; lia].
    + apply IH. intros a e Ha H1 H2. apply Hf; [exact Ha | exact H1 | lia].
Qed.

Lemma tmin_eq : forall lt res C par dist v dl H,
  tmin lt res C par dist v dl H =
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlq =>
        let r := resid lt res C p d in
        tmin lt res C par dist p (if r <? dl then r else dl)
          (Acc_inv H (dist_dec _ _ Hlq))
    | right _ => dl
    end
  else dl.
Proof. intros. destruct H. reflexivity. Qed.

Lemma tapp_eq : forall C par dist dl v res H,
  tapp C par dist dl v res H =
  let d := par.[v] in
  if d <? 4 then
    let p := nbr C v (opp d) in
    match bdec (dist.[p] <? dist.[v]) with
    | left Hlq =>
        tapp C par dist dl p (aug res C p d dl) (Acc_inv H (dist_dec _ _ Hlq))
    | right _ => res
    end
  else res.
Proof. intros. destruct H. reflexivity. Qed.

Lemma tmin_spec : forall par dist res v, path par dist res 1 v ->
  forall dl H, (1 <= (φ dl) <= 1000)%Z ->
  let m := tmin lt res Cm par dist v dl H in
  (1 <= (φ m) <= (φ dl))%Z /\ path par dist res (φ m) v.
Proof.
  intros par dist res v Hp. induction Hp as [v Hvv Hpar Hl | v Hvv Hpar Hhd Hn Hd Hr Hp IH];
    intros dl H Hdl m; subst m; rewrite tmin_eq; cbv zeta.
  - rewrite Hpar. split; [lia|]. apply path_root; assumption.
  - rewrite Hpar.
    destruct (bdec (dist.[nbr Cm v (opp par.[v])] <? dist.[v])) as [Hlq | Hlq];
      [| rewrite Hd in Hlq; discriminate].
    set (r := resid lt res Cm (nbr Cm v (opp par.[v])) par.[v]) in *.
    set (dl1 := if r <? dl then r else dl).
    assert (D1 : (1 <= (φ dl1) <= 1000 /\ (φ dl1) <= (φ dl) /\ (φ dl1) <= (φ r))%Z).
    { unfold dl1. destruct (r <? dl) eqn:E;
        [rewrite ltb_spec in E | rewrite <- Bool.not_true_iff_false, ltb_spec in E]; lia. }
    destruct (IH dl1 (Acc_inv H (dist_dec _ _ Hlq)) ltac:(lia)) as [M Pm].
    split; [lia|].
    refine (path_step _ _ _ _ v Hvv Hpar Hhd Hn Hd _ Pm). lia.
Qed.

Lemma tapp_spec : forall par dist dlm, (1 <= (φ dlm))%Z ->
  forall z v res H, (φ (dist.[v])) = z ->
  path par dist res (φ dlm) v -> bnd res ->
  (φ (PArray.length res)) = (2 * (Rz * Cz))%Z ->
  let res' := tapp Cm par dist dlm v res H in
  (φ (PArray.length res')) = (2 * (Rz * Cz))%Z /\ bnd res' /\
  forall X, (forall u, ((φ u) < Rz * Cz)%Z -> litm u = false -> X (ci u) (cj u) = true) ->
    phi X res' = (phi X res + (φ dlm) * (1 - b2z (X (ci v) (cj v))))%Z.
Proof.
  intros par dist dlm Hdl z.
  induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v res H Hz Hp B L res'. subst res'. rewrite tapp_eq. cbv zeta.
  inversion Hp as [v' Hvv Hpar Hl | v' Hvv Hpar Hhd Hn Hd Hr Hp']; subst v'.
  - rewrite Hpar. split; [exact L|]. split; [exact B|].
    intros X HX. rewrite (HX v Hvv Hl). simpl. lia.
  - rewrite Hpar.
    destruct (bdec (dist.[nbr Cm v (opp par.[v])] <? dist.[v])) as [Hlq | Hlq];
      [| rewrite Hd in Hlq; discriminate].
    set (p := nbr Cm v (opp par.[v])) in *.
    set (d := par.[v]) in *.
    destruct (edge_aug res p d dlm Hhd B L ltac:(lia)) as (L1 & B1 & O1 & P1).
    set (res1 := aug res Cm p d dlm) in *.
    assert (Hp1 : path par dist res1 (φ dlm) p).
    { apply (path_frame _ _ _ _ _ Hp'). intros a e Ha H1 H2.
      apply (resid_frame res res1 (slot Cm p d)); [exact O1|].
      intro E. pose proof Hlq as Hlq'. rewrite ltb_spec in Hlq'.
      destruct (slot_eq a e p d Ha Hhd E) as [[-> E2] | [E1 E2]].
      - lia.
      - rewrite Hn in E1. subst a. rewrite E2 in H1, H2. lia. }
    assert (Zp : Zwf 0 (φ (dist.[p])) z).
    { rewrite <- Hz. apply dist_dec. exact Hlq. }
    destruct (IH _ Zp p res1 (Acc_inv H (dist_dec _ _ Hlq)) eq_refl Hp1 B1 L1)
      as (L2 & B2 & P2).
    split; [exact L2|]. split; [exact B2|].
    intros X HX. rewrite (P2 X HX), (P1 X). fold p d. rewrite Hn. ring.
Qed.

(* ------------------------------------------------------------------ *)
(* Breadth-first search                                                *)
(* ------------------------------------------------------------------ *)

Fixpoint cnt0 (a : array int) (k : nat) : Z :=
  match k with
  | O => 0%Z
  | S k' => (cnt0 a k' + (if Uint63.eqb a.[of_Z (Z.of_nat k')] 0 then 1 else 0))%Z
  end.

Lemma cnt0_nonneg : forall a k, (0 <= cnt0 a k)%Z.
Proof. intros a k. induction k; simpl; [lia|]. destruct (_ =? 0); lia. Qed.

Lemma of_Z_nat_phi : forall k : nat, (Z.of_nat k < wB)%Z -> (φ (of_Z (Z.of_nat k))) = Z.of_nat k.
Proof. intros k Hk. rewrite of_Z_spec. apply Z.mod_small. lia. Qed.

Lemma cnt0_upd : forall a w x k, (Z.of_nat k <= 4194304)%Z ->
  (x =? 0) = false -> a.[w] = 0 -> (w <? PArray.length a) = true ->
  cnt0 (a.[w <- x]) k = (cnt0 a k - (if ((φ w) <? Z.of_nat k)%Z then 1 else 0))%Z.
Proof.
  intros a w x k. induction k as [|k IH]; intros Hk Hx Hw Hl; [simpl; destruct ((φ w) <? 0)%Z eqn:E; [rewrite Z.ltb_lt in E; pose proof (to_Z_bounded w); lia | lia]|].
  cbn [cnt0]. rewrite IH by lia.
  assert (Pk : (φ (of_Z (Z.of_nat k))) = Z.of_nat k) by (apply of_Z_nat_phi; rewrite wB_val; lia).
  destruct (Z.eq_dec (φ w) (Z.of_nat k)) as [E | E].
  - assert (Ew : of_Z (Z.of_nat k) = w) by (apply to_Z_inj; lia). rewrite Ew.
    rewrite aget_set_same by exact Hl. rewrite Hx, Hw.
    destruct ((φ w) <? Z.of_nat k)%Z eqn:E1; [rewrite Z.ltb_lt in E1; lia|].
    destruct ((φ w) <? Z.of_nat (S k))%Z eqn:E2; [|rewrite Z.ltb_ge in E2; lia].
    simpl. lia.
  - rewrite aget_set_other by (intro F; apply E; rewrite F, Pk; reflexivity).
    destruct ((φ w) <? Z.of_nat k)%Z eqn:E1; destruct ((φ w) <? Z.of_nat (S k))%Z eqn:E2;
      try (rewrite Z.ltb_lt in *; rewrite ?Z.ltb_ge in *; lia);
      try (rewrite Z.ltb_ge in *; rewrite ?Z.ltb_lt in *; lia).
Qed.

Lemma cnt0_pos : forall a w k, a.[w] = 0 -> ((φ w) < Z.of_nat k)%Z ->
  (Z.of_nat k <= 4194304)%Z -> (1 <= cnt0 a k)%Z.
Proof.
  intros a w k. induction k as [|k IH]; intros Hw Hk Hb; [lia|].
  cbn [cnt0]. pose proof (cnt0_nonneg a k).
  destruct (Z.eq_dec (φ w) (Z.of_nat k)) as [E | E].
  - assert (Ew : of_Z (Z.of_nat k) = w).
    { apply to_Z_inj. rewrite of_Z_nat_phi by (rewrite wB_val; lia). lia. }
    rewrite Ew, Hw. simpl. lia.
  - pose proof (IH Hw ltac:(lia) ltac:(lia)). destruct (_ =? 0); lia.
Qed.

Definition NN : Z := (Rz * Cz)%Z.

Lemma NN_bounds : (1 <= NN <= 900)%Z.
Proof. destruct vi_rc as [HR HC]. unfold NN. clear -HR HC. nia. Qed.

Definition visited (a : array int) (v : int) : Prop := a.[v] <> 0.

(* what BFS maintains *)
Record bcore (res : array int) (st : bst) : Prop := {
  bc_len : (φ (PArray.length (bd st))) = NN /\ (φ (PArray.length (bp st))) = NN /\
           (φ (PArray.length (bq st))) = NN;
  bc_cnt : ((φ (bt st)) + cnt0 (bd st) (Z.to_nat NN))%Z = NN;
  bc_q : forall k, ((φ k) < (φ (bt st)))%Z ->
           ((φ ((bq st).[k])) < NN)%Z /\ visited (bd st) ((bq st).[k]);
  bc_v : forall v, ((φ v) < NN)%Z -> visited (bd st) v ->
           exists k, ((φ k) < (φ (bt st)))%Z /\ (bq st).[k] = v;
  bc_p : forall v, ((φ v) < NN)%Z -> visited (bd st) v ->
           ((bp st).[v] <? 4) = false /\ litm v = false \/
           ((bp st).[v] <? 4) = true /\
           hd (nbr Cm v (opp (bp st).[v])) (bp st).[v] /\
           nbr Cm (nbr Cm v (opp (bp st).[v])) (bp st).[v] = v /\
           visited (bd st) (nbr Cm v (opp (bp st).[v])) /\
           ((bd st).[nbr Cm v (opp (bp st).[v])] <? (bd st).[v]) = true /\
           (0 < (φ (resid lt res Cm (nbr Cm v (opp (bp st).[v])) (bp st).[v])))%Z;
  bc_d : forall v, ((φ v) < NN)%Z -> visited (bd st) v -> ((φ ((bd st).[v])) <= (φ (bt st)))%Z
}.

(* head is the number of cells already expanded *)
Definition binv (res : array int) (st : bst) (head : Z) : Prop :=
  bcore res st /\
  (forall k, ((φ k) < head)%Z -> forall d, hd ((bq st).[k]) d ->
     (0 < (φ (resid lt res Cm ((bq st).[k]) d)))%Z ->
     visited (bd st) (nbr Cm ((bq st).[k]) d)) /\
  (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st) v).

Lemma bt_le : forall res st, bcore res st -> ((φ (bt st)) <= NN)%Z.
Proof. intros res st B. pose proof (bc_cnt _ _ B). pose proof (cnt0_nonneg (bd st) (Z.to_nat NN)). lia. Qed.

Lemma nbr_opp : forall v d, hd v d -> nbr Cm (nbr Cm v d) (opp d) = v /\ hd (nbr Cm v d) (opp d) = hd (nbr Cm v d) (opp d).
Proof.
  intros v d Hhd. split; [|reflexivity].
  destruct (dir_cases v d Hhd) as [-> | [-> | [-> | ->]]]; cbv [opp];
    rewrite ?nbr0, ?nbr1, ?nbr2, ?nbr3; apply to_Z_inj; pose proof (to_Z_bounded v); sia.
Qed.

Definition addc (st : bst) (w x d : int) : bst :=
  {| bd := (bd st).[w <- x]; bp := (bp st).[w <- d];
     bq := (bq st).[bt st <- w]; bt := bt st + 1 |}.

Lemma add_cell : forall res st w x d, bcore res st ->
  ((φ w) < NN)%Z -> (bd st).[w] = 0 -> (1 <= (φ x) <= (φ (bt st)) + 1)%Z ->
  ((d <? 4) = false /\ litm w = false \/
   (d <? 4) = true /\ hd (nbr Cm w (opp d)) d /\ nbr Cm (nbr Cm w (opp d)) d = w /\
   visited (bd st) (nbr Cm w (opp d)) /\ ((φ ((bd st).[nbr Cm w (opp d)])) < (φ x))%Z /\
   (0 < (φ (resid lt res Cm (nbr Cm w (opp d)) d)))%Z) ->
  let st' := addc st w x d in
  bcore res st' /\
  (forall v, v <> w -> (bd st').[v] = (bd st).[v]) /\
  (forall k, ((φ k) < (φ (bt st)))%Z -> (bq st').[k] = (bq st).[k]) /\
  visited (bd st') w /\ (φ (bt st')) = ((φ (bt st)) + 1)%Z.
Proof.
  intros res st w x d B Hw Hw0 Hx Hpw st'.
  destruct B as [[L1 [L2 L3]] Bc Bq Bv Bp Bd].
  pose proof NN_bounds as NB.
  assert (Cpos : (1 <= cnt0 (bd st) (Z.to_nat NN))%Z)
    by (apply (cnt0_pos _ w); [exact Hw0 | lia | lia]).
  assert (Hbt : ((φ (bt st)) < NN)%Z) by lia.
  assert (Hbt1 : (φ (bt st + 1)) = ((φ (bt st)) + 1)%Z) by sia.
  assert (Ox : forall v, v <> w -> (bd st').[v] = (bd st).[v])
    by (intros v Hvv; unfold st', addc; simpl; apply aget_set_other; congruence).
  assert (Sx : (bd st').[w] = x)
    by (unfold st', addc; simpl; apply aget_set_same; rewrite ltb_spec; lia).
  assert (Op : forall v, v <> w -> (bp st').[v] = (bp st).[v])
    by (intros v Hvv; unfold st', addc; simpl; apply aget_set_other; congruence).
  assert (Sp : (bp st').[w] = d)
    by (unfold st', addc; simpl; apply aget_set_same; rewrite ltb_spec; lia).
  assert (Oq : forall k, ((φ k) < (φ (bt st)))%Z -> (bq st').[k] = (bq st).[k]).
  { intros k Hk. unfold st', addc; simpl. apply aget_set_other.
    intro E. rewrite E in Hk. lia. }
  assert (Sq : (bq st').[bt st] = w)
    by (unfold st', addc; simpl; apply aget_set_same; rewrite ltb_spec; lia).
  assert (Bt' : (φ (bt st')) = ((φ (bt st)) + 1)%Z) by exact Hbt1.
  assert (Vw : visited (bd st') w) by (unfold visited; rewrite Sx; intro E; rewrite E in Hx; change (φ 0) with 0%Z in Hx; lia).
  assert (Vne : forall v, visited (bd st) v -> v <> w)
    by (intros v Hvv E; subst v; exact (Hvv Hw0)).
  assert (Vmono : forall v, visited (bd st) v -> visited (bd st') v)
    by (intros v Hvv; unfold visited; rewrite Ox by (apply Vne; exact Hvv); exact Hvv).
  assert (Vback : forall v, visited (bd st') v -> v <> w -> visited (bd st) v)
    by (intros v Hvv Hne; unfold visited in *; rewrite Ox in Hvv by exact Hne; exact Hvv).
  split; [|split; [exact Ox|split; [exact Oq|split; [exact Vw|exact Bt']]]].
  constructor.
  - unfold st', addc; simpl. rewrite !alength_set. auto.
  - rewrite Bt'. unfold st', addc; simpl.
    rewrite cnt0_upd; [| lia | | exact Hw0 | rewrite ltb_spec; lia].
    + destruct ((φ w) <? Z.of_nat (Z.to_nat NN))%Z eqn:E; [lia|]. rewrite Z.ltb_ge in E. lia.
    + rewrite eqb_false_spec. intro E. rewrite E in Hx. change (φ 0) with 0%Z in Hx. lia.
  - intros k Hk. rewrite Bt' in Hk.
    destruct (Z.eq_dec (φ k) (φ (bt st))) as [E | E].
    + assert (k = bt st) by (apply to_Z_inj; exact E). subst k. rewrite Sq. split; [exact Hw|exact Vw].
    + rewrite Oq by lia. destruct (Bq k ltac:(lia)) as [Q1 Q2]. split; [exact Q1|]. apply Vmono. exact Q2.
  - intros v Hvv Vv. rewrite Bt'.
    destruct (Z.eq_dec (φ v) (φ w)) as [E | E].
    + assert (v = w) by (apply to_Z_inj; exact E). subst v. exists (bt st). split; [lia|exact Sq].
    + assert (v <> w) by (intro F; apply E; rewrite F; reflexivity).
      destruct (Bv v Hvv (Vback v Vv ltac:(assumption))) as (k & Hk & Ek).
      exists k. split; [lia|]. rewrite Oq by lia. exact Ek.
  - intros v Hvv Vv. destruct (Z.eq_dec (φ v) (φ w)) as [E | E].
    + assert (v = w) by (apply to_Z_inj; exact E). subst v. rewrite Sp.
      destruct Hpw as [Hpw | (Hd4 & Hh & Hn & Vp & Lp & Rp)]; [left; exact Hpw|].
      right. assert (Pne : nbr Cm w (opp d) <> w) by (apply Vne; exact Vp).
      split; [exact Hd4|]. split; [exact Hh|]. split; [exact Hn|].
      split; [apply Vmono; exact Vp|]. split; [|exact Rp].
      rewrite Ox by exact Pne. rewrite Sx. rewrite ltb_spec. exact Lp.
    + assert (Hne : v <> w) by (intro F; apply E; rewrite F; reflexivity).
      pose proof (Vback v Vv Hne) as Vv0.
      rewrite Op by exact Hne.
      destruct (Bp v Hvv Vv0) as [Hr | (Hd4 & Hh & Hn & Vp & Lp & Rp)]; [left; exact Hr|].
      right. split; [exact Hd4|]. split; [exact Hh|]. split; [exact Hn|].
      split; [apply Vmono; exact Vp|]. split; [|exact Rp].
      rewrite (Ox v Hne). rewrite Ox by (apply Vne; exact Vp). exact Lp.
  - intros v Hvv Vv. rewrite Bt'. destruct (Z.eq_dec (φ v) (φ w)) as [E | E].
    + assert (v = w) by (apply to_Z_inj; exact E). subst v. rewrite Sx. lia.
    + assert (Hne : v <> w) by (intro F; apply E; rewrite F; reflexivity).
      rewrite (Ox v Hne). pose proof (Bd v Hvv (Vback v Vv Hne)). lia.
Qed.

Lemma alength_make : forall (n : int) (v : int),
  PArray.length (PArray.make n v) = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n v. exact (PArray.length_make int n v). Qed.

Lemma aget_make : forall (n : int) (v i : int), (PArray.make n v).[i] = v.
Proof. intros n v i. exact (PArray.get_make int v n i). Qed.

Lemma len_make_nm : (φ (PArray.length (PArray.make nm 0))) = NN.
Proof.
  rewrite alength_make. pose proof NN_bounds.
  replace (nm <=? PArray.max_length) with true; [unfold NN; lia|].
  symmetry. rewrite leb_spec, max_length_val. unfold NN in *. lia.
Qed.

Lemma cnt0_make : forall n k, cnt0 (PArray.make n 0) k = Z.of_nat k.
Proof. intros n k. induction k as [|k IH]; [reflexivity|]. cbn [cnt0]. rewrite IH, aget_make. simpl. lia. Qed.

Lemma root_step_eq : forall u i j st,
  root_step lt u i j st = if lt.[u] then st else addc st u 1 4.
Proof. reflexivity. Qed.

Lemma roots_spec : forall res,
  let st := roots lt Cm nm in
  bcore res st /\ (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st) v).
Proof.
  intros res st. pose proof NN_bounds as NB. destruct vi_rc as [HR HC].
  assert (G : bcore res st /\
    (forall v, ((φ nm) <= (φ v))%Z -> ((φ v) < NN)%Z -> (bd st).[v] = 0) /\
    (forall v, ((φ v) < (φ nm))%Z -> litm v = false -> visited (bd st) v)).
  { unfold st, roots.
    apply (grid_fold_spec Cm nm _ (fun u st => bcore res st /\
      (forall v, (u <= (φ v))%Z -> ((φ v) < NN)%Z -> (bd st).[v] = 0) /\
      (forall v, ((φ v) < u)%Z -> litm v = false -> visited (bd st) v))).
    - lia.
    - intros u i j s Hu Hi Hj (B & Z0 & D0). rewrite root_step_eq.
      rewrite (Hlt u Hu).
      assert (Hu' : ((φ u) < NN)%Z) by (unfold NN; lia).
      destruct (litm u) eqn:Lu.
      + split; [exact B|]. split; [intros v Hv1 Hv2; apply Z0; lia|].
        intros v Hv1 Hv2. destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
        * assert (v = u) by (apply to_Z_inj; exact E). subst v. congruence.
        * apply D0; [lia | exact Hv2].
      + destruct (add_cell res s u 1 4 B Hu' (Z0 u ltac:(lia) Hu')
                   ltac:(pose proof (to_Z_bounded (bt s)); change (φ 1) with 1%Z; lia)
                   (or_introl (conj eq_refl Lu)))
          as (B' & Ox & _ & Vu & _).
        split; [exact B'|]. split.
        * intros v Hv1 Hv2. rewrite Ox by (intro F; subst v; lia). apply Z0; lia.
        * intros v Hv1 Hv2. destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
          -- assert (v = u) by (apply to_Z_inj; exact E). subst v. exact Vu.
          -- unfold visited. rewrite Ox by (intro F; apply E; rewrite F; reflexivity).
             apply D0; [lia | exact Hv2].
    - split; [|split].
      + constructor; simpl.
        * rewrite !len_make_nm. auto.
        * rewrite cnt0_make. change (φ 0) with 0%Z. lia.
        * intros k Hk. change (φ 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
        * intros v _ Vv. exfalso. apply Vv. apply aget_make.
        * intros v _ Vv. exfalso. apply Vv. apply aget_make.
        * intros v _ Vv. exfalso. apply Vv. apply aget_make.
      + intros v _ _. apply aget_make.
      + intros v Hvx. pose proof (to_Z_bounded v). lia. }
  destruct G as (B & _ & D). split; [exact B|].
  intros v Hvx Lv. apply D; [unfold NN in Hvx; lia | exact Lv].
Qed.

Lemma visit_eq : forall res C st v dv d ok,
  visit lt res C st v dv d ok =
  if ok then
    if 0 <? resid lt res C v d then
      if (bd st).[nbr C v d] =? 0 then addc st (nbr C v d) (dv + 1) d else st
    else st
  else st.
Proof. reflexivity. Qed.

Lemma d_lt4 : forall p d, hd p d -> (d <? 4) = true.
Proof. intros p d H. destruct (dir_cases p d H) as [-> | [-> | [-> | ->]]]; reflexivity. Qed.

Lemma visit_spec : forall res st head v dv d ok, binv res st head ->
  ((φ (bt st)) <= NN)%Z -> v = (bq st).[of_Z head] -> (0 <= head < (φ (bt st)))%Z ->
  (ok = true <-> hd v d) -> dv = (bd st).[v] ->
  let st' := visit lt res Cm st v dv d ok in
  binv res st' head /\
  (forall x, visited (bd st) x -> (bd st').[x] = (bd st).[x]) /\
  (forall x, visited (bd st) x -> visited (bd st') x) /\
  (forall k, ((φ k) < (φ (bt st)))%Z -> (bq st').[k] = (bq st).[k]) /\
  ((φ (bt st)) <= (φ (bt st')))%Z /\
  (hd v d -> (0 < (φ (resid lt res Cm v d)))%Z -> visited (bd st') (nbr Cm v d)).
Proof.
  intros res st head v dv d ok [B [E R]] Hbt Ev Hh Hok Hdv0 st'. subst dv.
  assert (Hk : ((φ (of_Z head)) < (φ (bt st)))%Z) by (rewrite of_Z_spec, Z.mod_small; [lia | rewrite wB_val; lia]).
  destruct (bc_q _ _ B (of_Z head) Hk) as [Hv0 Vv]. rewrite <- Ev in Hv0, Vv.
  pose proof (bc_d _ _ B v Hv0 Vv) as Dv.
  assert (Same : binv res st head /\
     (forall x, visited (bd st) x -> (bd st).[x] = (bd st).[x]) /\
     (forall x, visited (bd st) x -> visited (bd st) x) /\
     (forall k, ((φ k) < (φ (bt st)))%Z -> (bq st).[k] = (bq st).[k]) /\
     ((φ (bt st)) <= (φ (bt st)))%Z).
  { split; [split; [exact B | split; assumption] |]. split; [auto|]. split; [auto|]. split; [auto|]. lia. }
  unfold st'. rewrite visit_eq.
  destruct ok.
  2: { destruct Same as (S1 & S0 & S2 & S3 & S4). split; [exact S1|]. split; [exact S0|]. split; [exact S2|].
       split; [exact S3|]. split; [exact S4|]. intros Hhd. apply Hok in Hhd. discriminate. }
  pose proof (proj1 Hok eq_refl) as Hhd.
  destruct (0 <? resid lt res Cm v d) eqn:Er.
  2: { destruct Same as (S1 & S0 & S2 & S3 & S4). split; [exact S1|]. split; [exact S0|]. split; [exact S2|].
       split; [exact S3|]. split; [exact S4|]. intros _ Hr.
       rewrite <- Bool.not_true_iff_false, ltb_spec in Er. change (φ 0) with 0%Z in Er. lia. }
  set (w := nbr Cm v d).
  destruct ((bd st).[w] =? 0) eqn:Ew.
  2: { destruct Same as (S1 & S0 & S2 & S3 & S4). split; [exact S1|]. split; [exact S0|]. split; [exact S2|].
       split; [exact S3|]. split; [exact S4|]. intros _ _.
       rewrite eqb_false_spec in Ew. exact Ew. }
  rewrite Uint63.eqb_spec in Ew.
  pose proof (nbr_facts v d Hhd) as (Hw & _). fold w in Hw.
  assert (Hdv : (φ ((bd st).[v] + 1)) = ((φ ((bd st).[v])) + 1)%Z).
  { pose proof NN_bounds. rewrite add_spec. change (φ 1) with 1%Z. apply Z.mod_small.
    rewrite wB_val. pose proof (to_Z_bounded ((bd st).[v])). lia. }
  assert (Dv1 : (1 <= (φ ((bd st).[v])))%Z).
  { pose proof (to_Z_bounded ((bd st).[v])). destruct (Z.eq_dec (φ ((bd st).[v])) 0) as [Z0|Z0]; [|lia].
    exfalso. apply Vv. apply to_Z_inj. exact Z0. }
  destruct (nbr_opp v d Hhd) as [Eo _].
  destruct (add_cell res st w ((bd st).[v] + 1) d B Hw Ew ltac:(rewrite Hdv; lia))
    as (B' & Ox & Oq & Vw & Bt').
  { right. fold w in Eo. rewrite Eo. split; [apply (d_lt4 v d Hhd)|].
    split; [exact Hhd|]. split; [reflexivity|]. split; [exact Vv|]. split; [rewrite Hdv; lia|].
    rewrite ltb_spec in Er. exact Er. }
  assert (Vs : forall x, visited (bd st) x -> (bd (addc st w ((bd st).[v] + 1) d)).[x] = (bd st).[x]).
  { intros x Vx. rewrite Ox; [reflexivity|]. intro F. subst x. exact (Vx Ew). }
  assert (Vm : forall x, visited (bd st) x -> visited (bd (addc st w ((bd st).[v] + 1) d)) x).
  { intros x Vx. unfold visited. rewrite Vs by exact Vx. exact Vx. }
  split; [|split; [exact Vs|split; [exact Vm|split; [exact Oq|split; [lia|intros _ _; exact Vw]]]]].
  split; [exact B'|]. split.
  - intros k Hk' d' Hh' Hr'. rewrite Oq by lia. apply Vm. apply E; [exact Hk'|rewrite <- (Oq k) by lia; exact Hh'|].
    rewrite <- (Oq k) by lia. exact Hr'.
  - intros x Hx Lx. apply Vm. apply R; assumption.
Qed.

Lemma flag_iff : forall v, ((φ v) < NN)%Z ->
  ((v mod Cm + 1 <? Cm) = true <-> hd v 0) /\
  ((0 <? v mod Cm) = true <-> hd v 1) /\
  ((v + Cm <? nm) = true <-> hd v 2) /\
  ((Cm <=? v) = true <-> hd v 3).
Proof.
  intros v Hv0. destruct vi_rc as [HR HC]. pose proof NN_bounds as NB. unfold NN in *.
  pose proof (to_Z_bounded v).
  assert (Mv : (φ (v mod Cm)) = ((φ v) mod Cz)%Z) by (rewrite mod_spec, HCm; reflexivity).
  pose proof (Z.mod_pos_bound (φ v) Cz ltac:(lia)).
  assert (Hj1 : (φ (v mod Cm + 1)) = ((φ v) mod Cz + 1)%Z).
  { rewrite add_spec, Mv. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val. lia. }
  assert (Hv2 : (φ (v + Cm)) = ((φ v) + Cz)%Z).
  { rewrite add_spec, HCm. apply Z.mod_small. rewrite wB_val. lia. }
  split; [|split; [|split]]; split; intros F.
  - rewrite ltb_spec, Hj1, HCm in F. split; [exact Hv0|]. left. split; [reflexivity|exact F].
  - destruct (hd_dir v 0 F) as (_ & A & _). specialize (A eq_refl).
    rewrite ltb_spec, Hj1, HCm. exact A.
  - rewrite ltb_spec, Mv in F. change (φ 0) with 0%Z in F. split; [exact Hv0|].
    right; left. split; [reflexivity|exact F].
  - destruct (hd_dir v 1 F) as (_ & _ & A & _). specialize (A eq_refl).
    rewrite ltb_spec, Mv. exact A.
  - rewrite ltb_spec, Hv2, Hnm in F. split; [exact Hv0|].
    right; right; left. split; [reflexivity|exact F].
  - destruct (hd_dir v 2 F) as (_ & _ & _ & A & _). specialize (A eq_refl).
    rewrite ltb_spec, Hv2, Hnm. exact A.
  - rewrite leb_spec, HCm in F. split; [exact Hv0|].
    right; right; right. split; [reflexivity|exact F].
  - destruct (hd_dir v 3 F) as (_ & _ & _ & _ & A). specialize (A eq_refl).
    rewrite leb_spec, HCm. exact A.
Qed.

Lemma bfs_loop_eq : forall lt res C n head st H,
  bfs_loop lt res C n head st H =
  match bdec (head <? n) with
  | left Hh =>
      if head <? bt st then
        let v := (bq st).[head] in
        let dv := (bd st).[v] in
        let j := v mod C in
        let st1 := visit lt res C st v dv 0 (j + 1 <? C) in
        let st2 := visit lt res C st1 v dv 1 (0 <? j) in
        let st3 := visit lt res C st2 v dv 2 (v + C <? n) in
        let st4 := visit lt res C st3 v dv 3 (C <=? v) in
        bfs_loop lt res C n (head + 1) st4 (Acc_inv H (dec_step n head Hh))
      else st
  | right _ => st
  end.
Proof. intros. destruct H. reflexivity. Qed.

Definition closed (res : array int) (st : bst) : Prop :=
  forall v, ((φ v) < NN)%Z -> visited (bd st) v -> forall d, hd v d ->
    (0 < (φ (resid lt res Cm v d)))%Z -> visited (bd st) (nbr Cm v d).

Lemma bfs_loop_spec : forall res z head st H, gap nm head = z ->
  binv res st (φ head) -> ((φ head) <= (φ (bt st)))%Z ->
  let st' := bfs_loop lt res Cm nm head st H in
  bcore res st' /\ (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st') v) /\
  closed res st'.
Proof.
  intros res z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros head st H Hz Bi Hhb st'. subst st'. rewrite bfs_loop_eq.
  pose proof NN_bounds as NB.
  destruct Bi as [B [E R]].
  pose proof (bt_le res st B) as Btn.
  assert (Exit : ((φ (bt st)) <= (φ head))%Z ->
     bcore res st /\ (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st) v) /\ closed res st).
  { intros Hx. split; [exact B|]. split; [exact R|].
    intros v Hv0 Vv d Hd Hr. destruct (bc_v _ _ B v Hv0 Vv) as (k & Hk & Ek).
    subst v. apply E; [lia | exact Hd | exact Hr]. }
  destruct (bdec (head <? nm)) as [Hh | Hh].
  2: { apply Exit. rewrite <- Bool.not_true_iff_false, ltb_spec, Hnm in Hh. unfold NN in Btn. lia. }
  destruct (head <? bt st) eqn:Hhb'.
  2: { apply Exit. rewrite <- Bool.not_true_iff_false, ltb_spec in Hhb'. lia. }
  rewrite ltb_spec in Hhb'. cbv zeta.
  set (v := (bq st).[head]).
  set (dv := (bd st).[v]).
  pose proof (to_Z_bounded head) as Bh.
  assert (Hoh : of_Z (φ head) = head) by apply of_to_Z.
  destruct (bc_q _ _ B head Hhb') as [Hv0 Vv]. fold v in Hv0, Vv.
  destruct (flag_iff v Hv0) as (F0 & F1 & F2 & F3).
  destruct (visit_spec res st (φ head) v dv 0 _ (conj B (conj E R)) Btn
              ltac:(rewrite Hoh; reflexivity) ltac:(lia) F0 eq_refl)
    as (B1 & S1 & M1 & Q1 & T1 & N1).
  set (st1 := visit lt res Cm st v dv 0 (v mod Cm + 1 <? Cm)) in *.
  assert (Bt1 : ((φ (bt st1)) <= NN)%Z) by exact (bt_le res st1 (proj1 B1)).
  assert (Dv1 : dv = (bd st1).[v]) by (rewrite S1 by exact Vv; reflexivity).
  assert (Qv1 : v = (bq st1).[of_Z (φ head)]) by (rewrite Hoh, Q1 by lia; reflexivity).
  destruct (visit_spec res st1 (φ head) v dv 1 _ B1 Bt1 Qv1 ltac:(lia) F1 Dv1)
    as (B2 & S2 & M2 & Q2 & T2 & N2).
  set (st2 := visit lt res Cm st1 v dv 1 (0 <? v mod Cm)) in *.
  assert (Bt2 : ((φ (bt st2)) <= NN)%Z) by exact (bt_le res st2 (proj1 B2)).
  assert (Dv2 : dv = (bd st2).[v]) by (rewrite S2 by (apply M1; exact Vv); exact Dv1).
  assert (Qv2 : v = (bq st2).[of_Z (φ head)]) by (rewrite Hoh, Q2 by lia; rewrite Hoh in Qv1; exact Qv1).
  destruct (visit_spec res st2 (φ head) v dv 2 _ B2 Bt2 Qv2 ltac:(lia) F2 Dv2)
    as (B3 & S3 & M3 & Q3 & T3 & N3).
  set (st3 := visit lt res Cm st2 v dv 2 (v + Cm <? nm)) in *.
  assert (Bt3 : ((φ (bt st3)) <= NN)%Z) by exact (bt_le res st3 (proj1 B3)).
  assert (Dv3 : dv = (bd st3).[v]) by (rewrite S3 by (apply M2, M1; exact Vv); exact Dv2).
  assert (Qv3 : v = (bq st3).[of_Z (φ head)]) by (rewrite Hoh, Q3 by lia; rewrite Hoh in Qv2; exact Qv2).
  destruct (visit_spec res st3 (φ head) v dv 3 _ B3 Bt3 Qv3 ltac:(lia) F3 Dv3)
    as (B4 & S4 & M4 & Q4 & T4 & N4).
  set (st4 := visit lt res Cm st3 v dv 3 (Cm <=? v)) in *.
  assert (Hh1 : (φ (head + 1)) = ((φ head) + 1)%Z) by (rewrite Hnm in *; rewrite ltb_spec in Hh; sia).
  eapply IH; [ | reflexivity | | ].
  - rewrite <- Hz. apply dec_step. exact Hh.
  - destruct B4 as [B4c [E4 R4]]. split; [exact B4c|]. split; [|exact R4].
    intros k Hk d Hd Hr. rewrite Hh1 in Hk.
    destruct (Z.eq_dec (φ k) (φ head)) as [Ek | Ek].
    + assert (k = head) by (apply to_Z_inj; exact Ek). subst k.
      assert (Ev4 : (bq st4).[head] = v).
      { rewrite Hoh in Qv3. rewrite Q4 by lia. symmetry. exact Qv3. }
      rewrite Ev4 in Hd, Hr |- *.
      destruct (dir_cases v d Hd) as [-> | [-> | [-> | ->]]].
      * apply M4, M3, M2. exact (N1 Hd Hr).
      * apply M4, M3. exact (N2 Hd Hr).
      * apply M4. exact (N3 Hd Hr).
      * exact (N4 Hd Hr).
    + apply E4; [lia | exact Hd | exact Hr].
  - lia.
Qed.

Lemma bfs_spec : forall res,
  let st := bfs lt res Cm nm in
  bcore res st /\ (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st) v) /\
  closed res st.
Proof.
  intros res st. unfold st, bfs.
  destruct (roots_spec res) as [B R].
  apply (bfs_loop_spec res _ 0 _ _ eq_refl).
  - split; [exact B|]. split; [|exact R].
    intros k Hk. change (φ 0) with 0%Z in Hk. pose proof (to_Z_bounded k). lia.
  - change (φ 0) with 0%Z. pose proof (to_Z_bounded (bt (roots lt Cm nm))). lia.
Qed.

Lemma visited_path : forall res st, bcore res st ->
  forall z v, (φ ((bd st).[v])) = z -> ((φ v) < NN)%Z -> visited (bd st) v ->
  path (bp st) (bd st) res 1 v.
Proof.
  intros res st B z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros v Hz Hv0 Vv.
  destruct (bc_p _ _ B v Hv0 Vv) as [[P4 Lv] | (P4 & Hh & Hn & Vp & Lp & Rp)].
  - apply path_root; [exact Hv0 | exact P4 | exact Lv].
  - destruct (hd_dir _ _ Hh) as (Hp0 & _).
    apply (path_step _ _ _ _ v Hv0 P4 Hh Hn Lp); [lia|].
    eapply IH; [ | reflexivity | exact Hp0 | exact Vp].
    rewrite <- Hz. apply dist_dec. exact Lp.
Qed.

(* ------------------------------------------------------------------ *)
(* Any fencing that fences out the dark cells cuts some closed set     *)
(* ------------------------------------------------------------------ *)

Section Closure.
Variables hf vf : N -> N -> bool.
Hypothesis Hfence : fences_out_dark b h g hf vf.

Definition ing (i j : N) : bool := (i <? rows g)%N && (j <? cols g)%N.

Definition X0 (i j : N) : bool := ing i j && negb (lit b h g i j).

Definition nxt (X : N -> N -> bool) (i j : N) : bool :=
  ing i j &&
  (X i j
   || ((0 <? j)%N && X i (j - 1)%N && negb (hf i (j - 1)%N))
   || ((j + 1 <? cols g)%N && X i (j + 1)%N && negb (hf i j))
   || ((0 <? i)%N && X (i - 1)%N j && negb (vf (i - 1)%N j))
   || ((i + 1 <? rows g)%N && X (i + 1)%N j && negb (vf i j))).

Fixpoint iter (k : nat) : N -> N -> bool :=
  match k with O => X0 | S k' => nxt (iter k') end.

Definition cntX (X : N -> N -> bool) : Z :=
  zsum (fun i => zsum (fun j => b2z (X i j)) (N.to_nat (cols g))) (N.to_nat (rows g)).

Lemma ing_true : forall i j, ing i j = true <-> in_grid g i j.
Proof.
  intros i j. unfold ing, in_grid. rewrite andb_true_iff, !N.ltb_lt. tauto.
Qed.

Lemma iter_ing : forall k i j, iter k i j = true -> ing i j = true.
Proof.
  intros k i j. destruct k; simpl; [unfold X0|unfold nxt]; rewrite andb_true_iff; tauto.
Qed.

Lemma iter_mono : forall k i j, iter k i j = true -> iter (S k) i j = true.
Proof.
  intros k i j H. simpl. unfold nxt. rewrite (iter_ing k i j H), H. reflexivity.
Qed.

Lemma iter_mono_le : forall k k' i j, (k <= k')%nat -> iter k i j = true -> iter k' i j = true.
Proof.
  intros k k' i j Hk. induction Hk; [auto|]. intros H. apply iter_mono. auto.
Qed.

Lemma b2z_bounds : forall x, (0 <= b2z x <= 1)%Z.
Proof. intros []; simpl; lia. Qed.

Lemma cntX_bounds : forall X, (0 <= cntX X <= Rz * Cz)%Z.
Proof.
  intros X. unfold cntX. split.
  - apply zsum_nonneg. intros k _. apply zsum_nonneg. intros l _. apply b2z_bounds.
  - eapply Z.le_trans.
    + apply zsum_const_le with (c := Cz). intros k _.
      eapply Z.le_trans; [apply zsum_const_le with (c := 1%Z); intros l _; apply b2z_bounds|]. lia.
    + lia.
Qed.

Lemma b2z_iter : forall k i j, (b2z (iter k i j) <= b2z (iter (S k) i j))%Z.
Proof.
  intros k i j. destruct (iter k i j) eqn:E.
  - rewrite (iter_mono _ _ _ E). simpl. lia.
  - destruct (iter (S k) i j); simpl; lia.
Qed.

Lemma cnt_mono : forall k, (cntX (iter k) <= cntX (iter (S k)))%Z.
Proof.
  intros k. unfold cntX. apply zsum_le. intros i _. apply zsum_le. intros j _.
  apply b2z_iter.
Qed.

Lemma cnt_stable : forall k, cntX (iter (S k)) = cntX (iter k) ->
  forall i j, (i < rows g)%N -> (j < cols g)%N -> iter (S k) i j = iter k i j.
Proof.
  intros k E i j Hi Hj. unfold cntX in E.
  assert (Row : forall i0, (i0 < N.to_nat (rows g))%nat ->
    zsum (fun j => b2z (iter k (N.of_nat i0) j)) (N.to_nat (cols g)) =
    zsum (fun j => b2z (iter (S k) (N.of_nat i0) j)) (N.to_nat (cols g))).
  { apply (zsum_le_eq (fun i => zsum (fun j => b2z (iter k i j)) (N.to_nat (cols g)))
                      (fun i => zsum (fun j => b2z (iter (S k) i j)) (N.to_nat (cols g)))).
    - intros i0 _. apply zsum_le. intros j0 _. apply b2z_iter.
    - symmetry. exact E. }
  pose proof (Row (N.to_nat i) ltac:(lia)) as Ri. rewrite N2Nat.id in Ri.
  pose proof (zsum_le_eq (fun j => b2z (iter k i j)) (fun j => b2z (iter (S k) i j))
                (N.to_nat (cols g))) as Z.
  assert (Ez : b2z (iter k i j) = b2z (iter (S k) i j)).
  { pose proof (Z ltac:(intros j0 _; apply b2z_iter)
                 Ri (N.to_nat j) ltac:(lia)) as R.
    rewrite N2Nat.id in R. exact R. }
  destruct (iter k i j), (iter (S k) i j); simpl in Ez; congruence.
Qed.

Lemma exists_stable : forall m,
  (exists k, (k <= m)%nat /\ cntX (iter (S k)) = cntX (iter k)) \/
  (Z.of_nat m <= cntX (iter m))%Z.
Proof.
  intros m. induction m as [|m IH].
  - right. pose proof (cntX_bounds (iter 0)). lia.
  - destruct IH as [(k & Hk & Ek) | Hm].
    + left. exists k. split; [lia|exact Ek].
    + destruct (Z.eq_dec (cntX (iter (S m))) (cntX (iter m))) as [E | E].
      * left. exists m. split; [lia|exact E].
      * right. pose proof (cnt_mono m). lia.
Qed.

Lemma iter_sound : forall k i j, iter k i j = true ->
  in_grid g i j /\ exists a c, in_grid g a c /\ lit b h g a c = false /\
    clos_refl_trans _ (step hf vf g) (a, c) (i, j).
Proof.
  induction k as [|k IH]; intros i j H.
  - unfold iter, X0 in H. rewrite andb_true_iff, negb_true_iff, ing_true in H.
    destruct H as [Hg Hl]. split; [exact Hg|]. exists i, j. split; [exact Hg|].
    split; [exact Hl|]. apply rt_refl.
  - simpl in H. unfold nxt in H. rewrite andb_true_iff, ing_true in H.
    destruct H as [Hg H]. split; [exact Hg|].
    assert (Ext : forall i' j', iter k i' j' = true -> step hf vf g (i', j') (i, j) ->
      exists a c, in_grid g a c /\ lit b h g a c = false /\
        clos_refl_trans _ (step hf vf g) (a, c) (i, j)).
    { intros i' j' H' S. destruct (IH i' j' H') as (_ & a & c & A1 & A2 & A3).
      exists a, c. split; [exact A1|]. split; [exact A2|].
      eapply rt_trans; [exact A3|]. apply rt_step. exact S. }
    destruct Hg as [Hi Hj].
    repeat rewrite orb_true_iff in H. repeat rewrite andb_true_iff in H.
    repeat rewrite negb_true_iff in H. rewrite ?N.ltb_lt in H.
    destruct H as [[[[H | H] | H] | H] | H];
      [| destruct H as [[H1 H2] H3] | destruct H as [[H1 H2] H3]
       | destruct H as [[H1 H2] H3] | destruct H as [[H1 H2] H3]].
    + destruct (IH i j H) as (_ & R). exact R.
    + apply (Ext i (j - 1)%N H2). unfold step, in_grid. lia.
    + apply (Ext i (j + 1)%N H2). unfold step, in_grid. lia.
    + apply (Ext (i - 1)%N j H2). unfold step, in_grid. lia.
    + apply (Ext (i + 1)%N j H2). unfold step, in_grid. lia.
Qed.

Lemma nxt_fromleft : forall X i j, ing i (j + 1)%N = true -> X i j = true -> hf i j = false ->
  nxt X i (j + 1)%N = true.
Proof.
  intros X i j G H1 H2. unfold nxt. rewrite G. simpl andb.
  replace (j + 1 - 1)%N with j by lia. rewrite H1, H2.
  replace (0 <? j + 1)%N with true by (symmetry; apply N.ltb_lt; lia).
  cbn [andb negb]. rewrite ?orb_true_r, ?orb_true_l. reflexivity.
Qed.

Lemma nxt_fromright : forall X i j, ing i j = true -> (j + 1 < cols g)%N ->
  X i (j + 1)%N = true -> hf i j = false -> nxt X i j = true.
Proof.
  intros X i j G Hj H1 H2. unfold nxt. rewrite G. simpl andb. rewrite H1, H2.
  replace (j + 1 <? cols g)%N with true by (symmetry; apply N.ltb_lt; lia).
  cbn [andb negb]. rewrite ?orb_true_r, ?orb_true_l. reflexivity.
Qed.

Lemma nxt_fromup : forall X i j, ing (i + 1)%N j = true -> X i j = true -> vf i j = false ->
  nxt X (i + 1)%N j = true.
Proof.
  intros X i j G H1 H2. unfold nxt. rewrite G. simpl andb.
  replace (i + 1 - 1)%N with i by lia. rewrite H1, H2.
  replace (0 <? i + 1)%N with true by (symmetry; apply N.ltb_lt; lia).
  cbn [andb negb]. rewrite ?orb_true_r, ?orb_true_l. reflexivity.
Qed.

Lemma nxt_fromdown : forall X i j, ing i j = true -> (i + 1 < rows g)%N ->
  X (i + 1)%N j = true -> vf i j = false -> nxt X i j = true.
Proof.
  intros X i j G Hi H1 H2. unfold nxt. rewrite G. simpl andb. rewrite H1, H2.
  replace (i + 1 <? rows g)%N with true by (symmetry; apply N.ltb_lt; lia).
  cbn [andb negb]. rewrite ?orb_true_r, ?orb_true_l. reflexivity.
Qed.

Lemma fence_closure : exists Y, goodX Y /\
  (forall i j, (i < rows g)%N -> (j + 1 < cols g)%N -> Y i j <> Y i (j + 1)%N -> hf i j = true) /\
  (forall i j, (i + 1 < rows g)%N -> (j < cols g)%N -> Y i j <> Y (i + 1)%N j -> vf i j = true).
Proof.
  destruct vi_rc as [HR HC].
  assert (Hm : (Rz * Cz <= 900)%Z) by (clear -HR HC; nia).
  destruct (exists_stable (Z.to_nat (Rz * Cz) + 1)) as [(K & _ & EK) | Hbig].
  2: { pose proof (cntX_bounds (iter (Z.to_nat (Rz * Cz) + 1))). lia. }
  pose proof (cnt_stable K EK) as St.
  exists (iter K). split; [split|split].
  - intros i j Hg Hl. apply (iter_mono_le 0); [lia|]. unfold iter, X0.
    rewrite (proj2 (ing_true i j) Hg), Hl. reflexivity.
  - intros i j [Hg Hb]. destruct (iter K i j) eqn:E; [|reflexivity].
    destruct (iter_sound K i j E) as (_ & a & c & A1 & A2 & A3).
    exfalso. exact (Hfence a c i j A1 A2 (conj Hg Hb) A3).
  - intros i j Hi Hj Hne. destruct (hf i j) eqn:Ehf; [reflexivity|]. exfalso.
    assert (Hg1 : ing i j = true) by (apply ing_true; unfold in_grid; lia).
    assert (Hg2 : ing i (j + 1)%N = true) by (apply ing_true; unfold in_grid; lia).
    destruct (iter K i j) eqn:E1, (iter K i (j + 1)%N) eqn:E2; try congruence.
    + rewrite <- (St i (j + 1)%N) in E2 by lia. cbn [iter] in E2.
      rewrite (nxt_fromleft _ i j Hg2 E1 Ehf) in E2. discriminate.
    + rewrite <- (St i j) in E1 by lia. cbn [iter] in E1.
      rewrite (nxt_fromright _ i j Hg1 Hj E2 Ehf) in E1. discriminate.
  - intros i j Hi Hj Hne. destruct (vf i j) eqn:Evf; [reflexivity|]. exfalso.
    assert (Hg1 : ing i j = true) by (apply ing_true; unfold in_grid; lia).
    assert (Hg2 : ing (i + 1)%N j = true) by (apply ing_true; unfold in_grid; lia).
    destruct (iter K i j) eqn:E1, (iter K (i + 1)%N j) eqn:E2; try congruence.
    + rewrite <- (St (i + 1)%N j) in E2 by lia. cbn [iter] in E2.
      rewrite (nxt_fromup _ i j Hg2 E1 Evf) in E2. discriminate.
    + rewrite <- (St i j) in E1 by lia. cbn [iter] in E1.
      rewrite (nxt_fromdown _ i j Hg1 Hi E2 Evf) in E1. discriminate.
Qed.

End Closure.

(* ------------------------------------------------------------------ *)
(* Finding a reached border cell                                       *)
(* ------------------------------------------------------------------ *)

Lemma eqb_phi : forall x y : int, (x =? y) = true <-> (φ x) = (φ y).
Proof. intros x y. rewrite Uint63.eqb_spec. split; [intros ->; reflexivity | apply to_Z_inj]. Qed.

Lemma is_border_iff : forall u i j, ((φ u) < NN)%Z -> (φ i) = ((φ u) / Cz)%Z -> (φ j) = ((φ u) mod Cz)%Z ->
  is_border Rm Cm i j = true <-> on_border g (ci u) (cj u).
Proof.
  intros u i j Hu Hi Hj. destruct vi_rc as [HR HC].
  destruct (cell_facts u Hu) as (A & B & _).
  assert (E1 : (φ (Rm - 1)) = (Rz - 1)%Z) by (rewrite sub_spec, HRm; apply Z.mod_small; rewrite wB_val; lia).
  assert (E2 : (φ (Cm - 1)) = (Cz - 1)%Z) by (rewrite sub_spec, HCm; apply Z.mod_small; rewrite wB_val; lia).
  unfold is_border. rewrite !orb_true_iff, !eqb_phi, E1, E2. change (φ 0) with 0%Z.
  unfold on_border, in_grid, ci, cj in *. rewrite <- Hi, <- Hj in *.
  pose proof (to_Z_bounded i). pose proof (to_Z_bounded j).
  split.
  - intros Hq. split; [split; assumption|].
    destruct Hq as [[[Hq|Hq]|Hq]|Hq]; [left|right;left|right;right;left|right;right;right]; lia.
  - intros [_ Hq]. destruct Hq as [Hq|[Hq|[Hq|Hq]]]; [left;left;left|left;left;right|left;right|right]; lia.
Qed.

Lemma fb_step_eq : forall dist R C n u i j acc,
  fb_step dist R C n u i j acc =
  if is_border R C i j && negb (dist.[u] =? 0) && ((acc =? n) || (dist.[u] <? dist.[acc]))
  then u else acc.
Proof. reflexivity. Qed.

Lemma find_border_spec : forall dist,
  let w := find_border dist Rm Cm nm in
  (w = nm /\ forall v, ((φ v) < NN)%Z -> on_border g (ci v) (cj v) -> dist.[v] = 0) \/
  (((φ w) < NN)%Z /\ on_border g (ci w) (cj w) /\ visited dist w).
Proof.
  intros dist w. destruct vi_rc as [HR HC].
  assert (G : (w = nm /\ forall v, ((φ v) < (φ nm))%Z -> on_border g (ci v) (cj v) -> dist.[v] = 0) \/
              (((φ w) < NN)%Z /\ on_border g (ci w) (cj w) /\ visited dist w)).
  { unfold w, find_border.
    apply (grid_fold_spec Cm nm _ (fun u acc =>
      (acc = nm /\ forall v, ((φ v) < u)%Z -> on_border g (ci v) (cj v) -> dist.[v] = 0) \/
      (((φ acc) < NN)%Z /\ on_border g (ci acc) (cj acc) /\ visited dist acc))).
    - lia.
    - intros u i j acc Hu Hi Hj IH. rewrite fb_step_eq.
      rewrite HCm in Hi, Hj.
      assert (Hu' : ((φ u) < NN)%Z) by (unfold NN; lia).
      pose proof (is_border_iff u i j Hu' Hi Hj) as Bi.
      destruct (is_border Rm Cm i j && negb (dist.[u] =? 0) && ((acc =? nm) || (dist.[u] <? dist.[acc]))) eqn:Ec.
      + right. rewrite !andb_true_iff, negb_true_iff in Ec. destruct Ec as [[E1 E2] _].
        split; [exact Hu'|]. split; [apply Bi; exact E1|]. rewrite eqb_false_spec in E2. exact E2.
      + destruct IH as [[Ea IH] | IH]; [left | right; exact IH].
        split; [exact Ea|]. intros v Hvv Hb.
        destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
        * assert (v = u) by (apply to_Z_inj; exact E). subst v.
          destruct (dist.[u] =? 0) eqn:Ed; [apply Uint63.eqb_spec; exact Ed|].
          exfalso. subst acc. rewrite (proj2 Bi Hb), Uint63.eqb_refl in Ec. simpl in Ec. discriminate.
        * apply IH; [lia | exact Hb].
    - left. split; [reflexivity|]. intros v Hvv. pose proof (to_Z_bounded v). lia. }
  destruct G as [[Ea G] | G]; [left | right; exact G].
  split; [exact Ea|]. intros v Hvv. apply G. unfold NN in Hvv. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* No augmenting path left: the reached set is a minimum cut           *)
(* ------------------------------------------------------------------ *)

Definition Xs (a : array int) (i j : N) : bool := ing i j && negb (a.[cell i j] =? 0).

Lemma cell_lt : forall i j, (i < rows g)%N -> (j < cols g)%N -> ((φ (cell i j)) < NN)%Z.
Proof.
  intros i j Hi Hj. destruct (cell_coords i j Hi Hj) as (E & _ & _). rewrite E. unfold NN.
  assert (Z.of_N i + 1 <= Rz)%Z by lia.
  assert ((Z.of_N i + 1) * Cz <= Rz * Cz)%Z by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

Lemma Xs_cell : forall a u, ((φ u) < NN)%Z -> Xs a (ci u) (cj u) = negb (a.[u] =? 0).
Proof.
  intros a u Hu. destruct (cell_facts u Hu) as (A & B & _). unfold Xs.
  replace (ing (ci u) (cj u)) with true by (symmetry; apply ing_true; split; assumption).
  rewrite cell_of by exact Hu. reflexivity.
Qed.

Lemma Xs_at : forall a i j, (i < rows g)%N -> (j < cols g)%N ->
  Xs a i j = negb (a.[cell i j] =? 0).
Proof.
  intros a i j Hi Hj. destruct (cell_coords i j Hi Hj) as (_ & Ci & Cj).
  rewrite <- (Xs_cell a (cell i j) (cell_lt i j Hi Hj)), Ci, Cj. reflexivity.
Qed.

Lemma xorb_false_eq : forall x y, xorb x y = false -> x = y.
Proof. intros [] []; simpl; congruence. Qed.

Lemma cut_step : forall X p q, step (cutH X) (cutV X) g p q ->
  X (fst p) (snd p) = X (fst q) (snd q).
Proof.
  intros X [i j] [i' j'] (_ & _ & D). simpl.
  destruct D as [(-> & -> & E) | [(-> & -> & E) | [(-> & -> & E) | (-> & -> & E)]]];
    apply xorb_false_eq in E; congruence.
Qed.

Lemma cut_crt : forall X p q, clos_refl_trans _ (step (cutH X) (cutV X) g) p q ->
  X (fst p) (snd p) = X (fst q) (snd q).
Proof.
  intros X p q H. induction H as [p q H | p | p q r _ IH1 _ IH2].
  - apply cut_step. exact H.
  - reflexivity.
  - congruence.
Qed.

Lemma final_spec : forall res F st,
  (φ (PArray.length res)) = (2 * (Rz * Cz))%Z -> bnd res ->
  (forall X, goodX X -> phi X res = (φ F)) ->
  (forall v, ((φ v) < NN)%Z -> litm v = false -> visited (bd st) v) ->
  closed res st ->
  (forall v, ((φ v) < NN)%Z -> on_border g (ci v) (cj v) -> (bd st).[v] = 0) ->
  darkness_spec b h g (Z.to_N (φ F)).
Proof.
  intros res F st Lres Bres Hphi Hdark Hcl Hbord.
  set (a := bd st) in *.
  destruct vi_rc as [HR HC].
  assert (Good : goodX (Xs a)).
  { split.
    - intros i j [Hi Hj] Hl. rewrite Xs_at by assumption.
      destruct (cell_coords i j Hi Hj) as (_ & Ci & Cj).
      assert (Vu : visited a (cell i j)).
      { apply Hdark; [apply cell_lt; assumption|]. unfold litm. rewrite Ci, Cj. exact Hl. }
      destruct (a.[cell i j] =? 0) eqn:E; [|reflexivity].
      rewrite Uint63.eqb_spec in E. exfalso. exact (Vu E).
    - intros i j [[Hi Hj] Hb]. rewrite Xs_at by assumption.
      destruct (cell_coords i j Hi Hj) as (_ & Ci & Cj).
      rewrite Hbord; [reflexivity | apply cell_lt; assumption |].
      rewrite Ci, Cj. split; [split; assumption | exact Hb]. }
  assert (Cut : phi (Xs a) res = Z.of_N (cost b h g (cutH (Xs a)) (cutV (Xs a)))).
  { apply phi_cut.
    - intros i j Hi Hj.
      assert (Hj' : (j < cols g)%N) by lia.
      set (p := cell i j). set (q := cell i (j + 1)).
      destruct (cell_coords i j Hi Hj') as (Ep & Cip & Cjp). fold p in Ep, Cip, Cjp.
      destruct (cell_coords i (j + 1) Hi Hj) as (Eq & Ciq & Cjq). fold q in Eq, Ciq, Cjq.
      pose proof (cell_lt i j Hi Hj') as Hp. pose proof (cell_lt i (j + 1) Hi Hj) as Hq. fold p in Hp. fold q in Hq.
      assert (Mp : ((φ p) mod Cz = Z.of_N j)%Z).
      { rewrite <- Cjp. unfold cj. rewrite Z2N.id; [reflexivity|]. apply Z.mod_pos_bound. lia. }
      assert (Mq : ((φ q) mod Cz = Z.of_N j + 1)%Z).
      { assert (Z.of_N (cj q) = Z.of_N j + 1)%Z by (rewrite Cjq; lia).
        unfold cj in H. rewrite Z2N.id in H; [exact H|]. apply Z.mod_pos_bound. lia. }
      assert (H0 : hd p 0) by (split; [exact Hp|]; left; split; [reflexivity|lia]).
      assert (H1 : hd q 1) by (split; [exact Hq|]; right; left; split; [reflexivity|lia]).
      assert (N0 : nbr Cm p 0 = q).
      { apply to_Z_inj. destruct (nbr_facts p 0 H0) as (_ & F0 & _). destruct (F0 eq_refl) as (E & _). lia. }
      assert (N1 : nbr Cm q 1 = p).
      { apply to_Z_inj. destruct (nbr_facts q 1 H1) as (_ & _ & F1 & _). destruct (F1 eq_refl) as (E & _). lia. }
      rewrite !Xs_at by lia. fold p q.
      pose proof (proj1 (edge0 res p 1 Bres Lres H0)) as R0.
      pose proof (proj1 (edge1 res q 1 Bres Lres H1)) as R1. cbv zeta in R1. rewrite N1 in R1.
      rewrite Cip, Cjp in R0, R1.
      pose proof (to_Z_bounded (res.[sH i j])).
      destruct Bres as [BH _]. pose proof (BH i j Hi Hj) as Bij.
      split; intros X1 X2; rewrite negb_true_iff, negb_false_iff in *.
      + rewrite Uint63.eqb_spec in X2. rewrite eqb_false_spec in X1.
        destruct (Z_lt_le_dec 0 (φ (resid lt res Cm p 0))) as [Pos | Neg].
        * exfalso. apply (Hcl p Hp X1 0 H0) in Pos. rewrite N0 in Pos. exact (Pos X2).
        * lia.
      + rewrite Uint63.eqb_spec in X1. rewrite eqb_false_spec in X2.
        destruct (Z_lt_le_dec 0 (φ (resid lt res Cm q 1))) as [Pos | Neg].
        * exfalso. apply (Hcl q Hq X2 1 H1) in Pos. rewrite N1 in Pos. exact (Pos X1).
        * lia.
    - intros i j Hi Hj.
      assert (Hi' : (i < rows g)%N) by lia.
      set (p := cell i j). set (q := cell (i + 1) j).
      destruct (cell_coords i j Hi' Hj) as (Ep & Cip & Cjp). fold p in Ep, Cip, Cjp.
      destruct (cell_coords (i + 1) j Hi Hj) as (Eq & Ciq & Cjq). fold q in Eq, Ciq, Cjq.
      pose proof (cell_lt i j Hi' Hj) as Hp. pose proof (cell_lt (i + 1) j Hi Hj) as Hq. fold p in Hp. fold q in Hq.
      assert (H2 : hd p 2) by (split; [exact Hp|]; right; right; left; split; [reflexivity|unfold NN in Hq; lia]).
      assert (H3 : hd q 3) by (split; [exact Hq|]; right; right; right; split; [reflexivity|lia]).
      assert (N2 : nbr Cm p 2 = q).
      { apply to_Z_inj. destruct (nbr_facts p 2 H2) as (_ & _ & _ & F2 & _). destruct (F2 eq_refl) as (E & _). lia. }
      assert (N3 : nbr Cm q 3 = p).
      { apply to_Z_inj. destruct (nbr_facts q 3 H3) as (_ & _ & _ & _ & F3). destruct (F3 eq_refl) as (E & _). lia. }
      rewrite !Xs_at by lia. fold p q.
      pose proof (proj1 (edge2 res p 1 Bres Lres H2)) as R2.
      pose proof (proj1 (edge3 res q 1 Bres Lres H3)) as R3. cbv zeta in R3. rewrite N3 in R3.
      rewrite Cip, Cjp in R2, R3.
      pose proof (to_Z_bounded (res.[sV i j])).
      destruct Bres as [_ BV]. pose proof (BV i j Hi Hj) as Bij.
      split; intros X1 X2; rewrite negb_true_iff, negb_false_iff in *.
      + rewrite Uint63.eqb_spec in X2. rewrite eqb_false_spec in X1.
        destruct (Z_lt_le_dec 0 (φ (resid lt res Cm p 2))) as [Pos | Neg].
        * exfalso. apply (Hcl p Hp X1 2 H2) in Pos. rewrite N2 in Pos. exact (Pos X2).
        * lia.
      + rewrite Uint63.eqb_spec in X1. rewrite eqb_false_spec in X2.
        destruct (Z_lt_le_dec 0 (φ (resid lt res Cm q 3))) as [Pos | Neg].
        * exfalso. apply (Hcl q Hq X2 3 H3) in Pos. rewrite N3 in Pos. exact (Pos X1).
        * lia. }
  rewrite (Hphi _ Good) in Cut.
  split.
  - exists (cutH (Xs a)), (cutV (Xs a)). split.
    + intros i j i' j' Hg Hl Hb Hc.
      pose proof (cut_crt (Xs a) _ _ Hc) as E. simpl in E.
      rewrite (proj1 Good i j Hg Hl), (proj2 Good i' j' Hb) in E. discriminate.
    + pose proof (to_Z_bounded F). lia.
  - intros hf vf Hf.
    destruct (fence_closure hf vf Hf) as (Y & GY & HY & VY).
    pose proof (phi_le_cost Y res hf vf Bres HY VY) as L.
    rewrite (Hphi Y GY) in L. pose proof (to_Z_bounded F). lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The main loop                                                       *)
(* ------------------------------------------------------------------ *)

Definition borderb (i j : N) : bool :=
  ing i j && ((i =? 0) || (i =? rows g - 1) || (j =? 0) || (j =? cols g - 1))%N.

Definition Xg (i j : N) : bool := negb (borderb i j).

Lemma borderb_iff : forall i j, borderb i j = true <-> on_border g i j.
Proof.
  intros i j. unfold borderb, on_border. rewrite andb_true_iff, ing_true, !orb_true_iff, !N.eqb_eq.
  tauto.
Qed.

Lemma Xg_good : goodX Xg.
Proof.
  split.
  - intros i j Hg Hl. unfold Xg. destruct (borderb i j) eqn:E; [|reflexivity].
    apply borderb_iff in E. destruct Hv as [_ _ _ _ _ _ Hb]. rewrite (Hb i j E) in Hl. discriminate.
  - intros i j Hb. unfold Xg. apply borderb_iff in Hb. rewrite Hb. reflexivity.
Qed.

Lemma good_cells : forall X, goodX X ->
  forall u, ((φ u) < Rz * Cz)%Z -> litm u = false -> X (ci u) (cj u) = true.
Proof.
  intros X [G _] u Hu Hl. destruct (cell_facts u Hu) as (A & B & _).
  apply G; [split; assumption | exact Hl].
Qed.

Lemma flow_loop_eq : forall lt R C n B res F H,
  flow_loop lt R C n B res F H =
  let st := bfs lt res C n in
  let w := find_border (bd st) R C n in
  if w =? n then F
  else
    let dl := tmin lt res C (bp st) (bd st) w 1000
                (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let res' := tapp C (bp st) (bd st) dl w res
                  (Zwf_well_founded 0 (φ ((bd st).[w]))) in
    let F' := F + dl in
    match bdec ((F <? F') && (F' <=? B)) with
    | left Hg => flow_loop lt R C n B res' F' (Acc_inv H (flow_dec B F F' Hg))
    | right _ => F
    end.
Proof. intros. destruct H. reflexivity. Qed.

Lemma flow_spec : forall Bm, (φ Bm) = (86 * NN)%Z ->
  forall z F res H, gap Bm F = z ->
  (φ (PArray.length res)) = (2 * (Rz * Cz))%Z -> bnd res ->
  (forall X, goodX X -> phi X res = (φ F)) ->
  darkness_spec b h g (Z.to_N (φ (flow_loop lt Rm Cm nm Bm res F H))).
Proof.
  intros Bm HB z. induction z as [z IH] using (well_founded_ind (Zwf_well_founded 0)).
  intros F res H Hz L Bd Hphi.
  rewrite flow_loop_eq. cbv zeta.
  destruct (bfs_spec res) as (B & R & Cl).
  set (st := bfs lt res Cm nm) in *.
  destruct (find_border_spec (bd st)) as [[Ew Hb] | (Hw & Hb & Vw)].
  - rewrite Ew, Uint63.eqb_refl. exact (final_spec res F st L Bd Hphi R Cl Hb).
  - set (w := find_border (bd st) Rm Cm nm) in *.
    assert (Ewn : (w =? nm) = false) by (rewrite eqb_false_spec; intro E; rewrite E, Hnm in Hw; unfold NN in Hw; lia).
    rewrite Ewn.
    pose proof (visited_path res st B _ w eq_refl Hw Vw) as P1.
    destruct (tmin_spec (bp st) (bd st) res w P1 1000 (Zwf_well_founded 0 (φ ((bd st).[w])))
                ltac:(change (φ 1000) with 1000%Z; lia)) as [Dl Pd].
    set (dl := tmin lt res Cm (bp st) (bd st) w 1000 (Zwf_well_founded 0 (φ ((bd st).[w])))) in *.
    change (φ 1000) with 1000%Z in Dl.
    destruct (tapp_spec (bp st) (bd st) dl ltac:(lia) _ w res
                (Zwf_well_founded 0 (φ ((bd st).[w]))) eq_refl Pd Bd L) as (L' & B' & P').
    set (res' := tapp Cm (bp st) (bd st) dl w res (Zwf_well_founded 0 (φ ((bd st).[w])))) in *.
    pose proof NN_bounds as NB.
    assert (FB : ((φ F) <= 86 * NN)%Z) by (rewrite <- (Hphi Xg Xg_good); apply phi_le_bound; exact Bd).
    assert (EF : (φ (F + dl)) = ((φ F) + (φ dl))%Z).
    { rewrite add_spec. apply Z.mod_small. rewrite wB_val. pose proof (to_Z_bounded F). lia. }
    assert (Hphi' : forall X, goodX X -> phi X res' = (φ (F + dl))).
    { intros X GX. rewrite (P' X (good_cells X GX)), (Hphi X GX), EF.
      rewrite (proj2 GX (ci w) (cj w) Hb). simpl. ring. }
    assert (FB' : ((φ (F + dl)) <= 86 * NN)%Z)
      by (rewrite <- (Hphi' Xg Xg_good); apply phi_le_bound; exact B').
    destruct (bdec ((F <? F + dl) && (F + dl <=? Bm))) as [Hg | Hg].
    + eapply IH; [ | reflexivity | exact L' | exact B' | exact Hphi'].
      rewrite <- Hz. apply flow_dec. exact Hg.
    + exfalso. rewrite andb_false_iff in Hg.
      destruct Hg as [Hg | Hg]; rewrite <- Bool.not_true_iff_false in Hg; apply Hg.
      * rewrite ltb_spec. lia.
      * rewrite leb_spec. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The initial residuals: the zero flow                                *)
(* ------------------------------------------------------------------ *)

Lemma zsum_zero : forall f n, (forall k, (k < n)%nat -> f (N.of_nat k) = 0%Z) -> zsum f n = 0%Z.
Proof.
  intros f n H. rewrite (zsum_ext f (fun _ => 0%Z)) by exact H.
  clear. induction n; simpl; [reflexivity | rewrite IHn; reflexivity].
Qed.

Lemma len_make_2nm : (φ (PArray.length (PArray.make (2 * nm) 0))) = (2 * NN)%Z.
Proof.
  rewrite alength_make. pose proof NN_bounds. unfold NN in *.
  assert (E : (φ (2 * nm)) = (2 * (Rz * Cz))%Z).
  { rewrite mul_spec, Hnm. change (φ 2) with 2%Z. apply Z.mod_small. rewrite wB_val. lia. }
  replace (2 * nm <=? PArray.max_length) with true; [exact E|].
  symmetry. rewrite leb_spec, max_length_val, E. lia.
Qed.

Lemma init_res_spec :
  let res := init_res lt Cm nm in
  (φ (PArray.length res)) = (2 * (Rz * Cz))%Z /\ bnd res /\ forall X, phi X res = 0%Z.
Proof.
  intros res. pose proof NN_bounds as NB. destruct vi_rc as [HR HC].
  assert (D2 : forall v, ((φ v) < NN)%Z -> (φ (2 * v)) = (2 * (φ v))%Z /\ (φ (2 * v + 1)) = (2 * (φ v) + 1)%Z).
  { intros v Hv0. pose proof (to_Z_bounded v).
    assert (E : (φ (2 * v)) = (2 * (φ v))%Z) by (rewrite mul_spec; change (φ 2) with 2%Z; apply Z.mod_small; rewrite wB_val; lia).
    split; [exact E|]. rewrite add_spec, E. change (φ 1) with 1%Z. apply Z.mod_small. rewrite wB_val. lia. }
  assert (G : (φ (PArray.length res)) = (2 * NN)%Z /\
    forall v, ((φ v) < (φ nm))%Z ->
      res.[2 * v] = capf lt.[v] lt.[v + 1] /\ res.[2 * v + 1] = capf lt.[v] lt.[v + Cm]).
  { unfold res, init_res.
    apply (grid_fold_spec Cm nm _ (fun u r => (φ (PArray.length r)) = (2 * NN)%Z /\
      forall v, ((φ v) < u)%Z ->
        r.[2 * v] = capf lt.[v] lt.[v + 1] /\ r.[2 * v + 1] = capf lt.[v] lt.[v + Cm])).
    - lia.
    - intros u i j r Hu _ _ [Lr IH]. cbv zeta.
      assert (Hu' : ((φ u) < NN)%Z) by (unfold NN; lia).
      destruct (D2 u Hu') as [U1 U2].
      assert (I1 : (2 * u <? PArray.length r) = true) by (rewrite ltb_spec, Lr, U1; lia).
      assert (I2 : (2 * u + 1 <? PArray.length (r.[2 * u <- capf lt.[u] lt.[u + 1]])) = true)
        by (rewrite alength_set, ltb_spec, Lr, U2; lia).
      assert (N12 : 2 * u <> 2 * u + 1) by (intro E; apply (f_equal to_Z) in E; lia).
      split; [rewrite !alength_set; exact Lr|].
      intros v Hv0. destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
      + assert (v = u) by (apply to_Z_inj; exact E). subst v.
        rewrite aget_set_other by (intro F; apply N12; symmetry; exact F).
        rewrite aget_set_same by exact I1. rewrite aget_set_same by exact I2. split; reflexivity.
      + assert (Hv' : ((φ v) < NN)%Z) by lia. destruct (D2 v Hv') as [V1 V2].
        rewrite !aget_set_other by (intro F; apply (f_equal to_Z) in F; rewrite ?U1, ?U2, ?V1, ?V2 in F; lia).
        apply IH. lia.
    - split; [exact len_make_2nm|]. intros v Hv0. pose proof (to_Z_bounded v). change (φ 0) with 0%Z in Hv0. lia. }
  destruct G as [L G].
  assert (EH : forall i j, (i < rows g)%N -> (j + 1 < cols g)%N -> (φ (res.[sH i j])) = pH i j).
  { intros i j Hi Hj.
    set (p := cell i j). destruct (cell_coords i j Hi ltac:(lia)) as (Ep & Cip & Cjp). fold p in Ep, Cip, Cjp.
    destruct (cell_coords i (j + 1) Hi Hj) as (Eq & Ciq & Cjq).
    pose proof (cell_lt i j Hi ltac:(lia)) as Hp. fold p in Hp.
    assert (Hq : cell i (j + 1) = p + 1) by (apply to_Z_inj; rewrite Eq, add_spec, Ep; change (φ 1) with 1%Z; rewrite Z.mod_small; [lia | rewrite wB_val; unfold NN in Hp; lia]).
    assert (Es : sH i j = 2 * p) by (apply to_Z_inj; rewrite phi_sH by lia; rewrite (proj1 (D2 p Hp)); lia).
    rewrite Es, (proj1 (G p ltac:(unfold NN in Hp; lia))).
    rewrite (lit_of p ltac:(exact Hp)), <- Hq, (lit_of (cell i (j + 1)) ltac:(apply cell_lt; lia)).
    rewrite Cip, Cjp, Ciq, Cjq. unfold pH, price, capf.
    destruct (lit b h g i j), (lit b h g i (j + 1)); reflexivity. }
  assert (EV : forall i j, (i + 1 < rows g)%N -> (j < cols g)%N -> (φ (res.[sV i j])) = pV i j).
  { intros i j Hi Hj.
    set (p := cell i j). destruct (cell_coords i j ltac:(lia) Hj) as (Ep & Cip & Cjp). fold p in Ep, Cip, Cjp.
    destruct (cell_coords (i + 1) j Hi Hj) as (Eq & Ciq & Cjq).
    pose proof (cell_lt i j ltac:(lia) Hj) as Hp. fold p in Hp.
    pose proof (cell_lt (i + 1) j Hi Hj) as Hq0.
    assert (Hq : cell (i + 1) j = p + Cm) by (apply to_Z_inj; rewrite Eq, add_spec, Ep, HCm; rewrite Z.mod_small; [lia | rewrite wB_val; unfold NN in Hp; lia]).
    assert (Es : sV i j = 2 * p + 1) by (apply to_Z_inj; rewrite phi_sV by lia; rewrite (proj2 (D2 p Hp)); lia).
    rewrite Es, (proj2 (G p ltac:(unfold NN in Hp; lia))).
    rewrite (lit_of p ltac:(exact Hp)), <- Hq, (lit_of (cell (i + 1) j) ltac:(exact Hq0)).
    rewrite Cip, Cjp, Ciq, Cjq. unfold pV, price, capf.
    destruct (lit b h g i j), (lit b h g (i + 1) j); reflexivity. }
  split; [exact L|]. split.
  - split.
    + intros i j Hi Hj. rewrite EH by assumption. unfold pH. lia.
    + intros i j Hi Hj. rewrite EV by assumption. unfold pV. lia.
  - intros X. unfold phi, phiH, phiV.
    rewrite (zsum_zero _ (N.to_nat (rows g))), (zsum_zero _ (N.to_nat (rows g - 1))); [reflexivity| |].
    + intros k Hk. apply zsum_zero. intros l Hl. unfold fV. rewrite EV by lia. ring.
    + intros k Hk. apply zsum_zero. intros l Hl. unfold fH. rewrite EH by lia. ring.
Qed.

End Flow.

(* ------------------------------------------------------------------ *)
(* The whole program                                                   *)
(* ------------------------------------------------------------------ *)

Lemma bget_set_other : forall (t : array bool) (i j : int) (v : bool),
  i <> j -> t.[i <- v].[j] = t.[j].
Proof. intros t i j v H. exact (PArray.get_set_other bool t i j v H). Qed.

Lemma bget_set_same : forall (t : array bool) (i : int) (v : bool),
  (i <? PArray.length t) = true -> t.[i <- v].[i] = v.
Proof. intros t i v H. exact (PArray.get_set_same bool t i v H). Qed.

Lemma blength_set : forall (t : array bool) (i : int) (v : bool),
  PArray.length t.[i <- v] = PArray.length t.
Proof. intros t i v. exact (PArray.length_set bool t i v). Qed.

Lemma blength_make : forall (n : int) (v : bool),
  PArray.length (PArray.make n v) = if n <=? PArray.max_length then n else PArray.max_length.
Proof. intros n v. exact (PArray.length_make bool n v). Qed.

Lemma darkness_impl_correct :
  forall (b h : N) (g : list (list N)) (xb xh : uint) (xg : array (array uint)),
  valid_input b h g -> repr xb b -> repr xh h -> repr xg g ->
  exists o : N, repr (darkness_impl xb xh xg) o /\ darkness_spec b h g o.
Proof.
  intros b h g xb xh xg Hv Hb Hh Hg.
  destruct (repr_grid b h g xg Hv Hg) as (LR & LC & Gc).
  destruct (vi_facts b h g Hv) as (HR & HC & Bb & Bh).
  unfold repr, repr_uint in Hb, Hh.
  assert (Hxb : (φ xb) = Z.of_N b) by (rewrite <- Hb, Z2N.id; [reflexivity | apply to_Z_bounded]).
  assert (Hxh : (φ xh) = Z.of_N h) by (rewrite <- Hh, Z2N.id; [reflexivity | apply to_Z_bounded]).
  unfold darkness_impl.
  set (R := PArray.length xg) in *. set (C := PArray.length xg.[0]) in *.
  set (n := R * C).
  assert (NB : (Z.of_N (rows g) * Z.of_N (cols g) <= 900)%Z) by (clear -HR HC; nia).
  assert (Hn : (φ n) = (Z.of_N (rows g) * Z.of_N (cols g))%Z).
  { unfold n. rewrite mul_spec, LR, LC. apply Z.mod_small. rewrite wB_val. lia. }
  assert (Hhh : (φ (xh * xh)) = (Z.of_N h ^ 2)%Z).
  { rewrite mul_spec, Hxh, Z.pow_2_r. apply Z.mod_small. rewrite wB_val. clear -Bh; nia. }
  (* the flat strengths *)
  set (s := flat xg C n).
  assert (Hs : forall u, ((φ u) < (φ n))%Z -> (φ (s.[u])) =
             Z.of_N (strength g (Z.to_N ((φ u) / Z.of_N (cols g))) (Z.to_N ((φ u) mod Z.of_N (cols g))))).
  { assert (G : (φ (PArray.length s)) = (φ n) /\ forall u, ((φ u) < (φ n))%Z -> (φ (s.[u])) =
             Z.of_N (strength g (Z.to_N ((φ u) / Z.of_N (cols g))) (Z.to_N ((φ u) mod Z.of_N (cols g))))).
    { unfold s, flat.
      apply (grid_fold_spec C n _ (fun k a => (φ (PArray.length a)) = (φ n) /\ forall u, ((φ u) < k)%Z ->
        (φ (a.[u])) = Z.of_N (strength g (Z.to_N ((φ u) / Z.of_N (cols g))) (Z.to_N ((φ u) mod Z.of_N (cols g)))))).
      - lia.
      - intros u i j a Hu Hi Hj [La IH]. rewrite LC in Hi, Hj.
        split; [rewrite alength_set; exact La|].
        intros v Hv0. destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
        + assert (v = u) by (apply to_Z_inj; exact E). subst v.
          rewrite aget_set_same by (rewrite ltb_spec, La; exact Hu).
          assert (Bi : ((φ u) / Z.of_N (cols g) < Z.of_N (rows g))%Z)
            by (apply Z.div_lt_upper_bound; lia).
          assert (Bj : ((φ u) mod Z.of_N (cols g) < Z.of_N (cols g))%Z) by (apply Z.mod_pos_bound; lia).
          transitivity (Z.of_N (strength g (Z.to_N (φ i)) (Z.to_N (φ j))));
            [exact (Gc i j ltac:(lia) ltac:(lia)) | rewrite Hi, Hj; reflexivity].
        + rewrite aget_set_other by (intro F; apply E; rewrite F; reflexivity). apply IH. lia.
      - split.
        + rewrite alength_make. replace (n <=? PArray.max_length) with true; [reflexivity|].
          symmetry. rewrite leb_spec, max_length_val. lia.
        + intros u Hu. pose proof (to_Z_bounded u). change (φ 0) with 0%Z in Hu. lia. }
    exact (proj2 G). }
  (* the lit cells *)
  set (lt := lit_arr s C n xb (xh * xh)).
  assert (Hlt : forall u, ((φ u) < (φ n))%Z -> lt.[u] = litm b h g u).
  { assert (G : (φ (PArray.length lt)) = (φ n) /\ forall u, ((φ u) < (φ n))%Z -> lt.[u] = litm b h g u).
    { unfold lt, lit_arr.
      apply (grid_fold_spec C n _ (fun k a => (φ (PArray.length a)) = (φ n) /\
        forall u, ((φ u) < k)%Z -> a.[u] = litm b h g u)).
      - lia.
      - intros u i j a Hu Hi Hj [La IH]. rewrite LC in Hi, Hj.
        split; [rewrite blength_set; exact La|].
        intros v Hv0. destruct (Z.eq_dec (φ v) (φ u)) as [E | E].
        + assert (v = u) by (apply to_Z_inj; exact E). subst v.
          rewrite bget_set_same by (rewrite ltb_spec, La; exact Hu).
          assert (Bi : ((φ u) / Z.of_N (cols g) < Z.of_N (rows g))%Z)
            by (apply Z.div_lt_upper_bound; lia).
          assert (Bj : ((φ u) mod Z.of_N (cols g) < Z.of_N (cols g))%Z) by (apply Z.mod_pos_bound; lia).
          rewrite (lit_cell_spec b h g Hv s C n (xh * xh) i j Hs LC Hn Hhh ltac:(lia) ltac:(lia) xb Hxb).
          unfold litm, ci, cj. rewrite Hi, Hj. reflexivity.
        + rewrite bget_set_other by (intro F; apply E; rewrite F; reflexivity). apply IH. lia.
      - split.
        + rewrite blength_make. replace (n <=? PArray.max_length) with true; [reflexivity|].
          symmetry. rewrite leb_spec, max_length_val. lia.
        + intros u Hu. pose proof (to_Z_bounded u). change (φ 0) with 0%Z in Hu. lia. }
    exact (proj2 G). }
  destruct (init_res_spec b h g Hv R C n lt LC Hn Hlt) as (L0 & B0 & P0).
  set (res := init_res lt C n) in *.
  assert (HB : (φ (86 * n)) = (86 * NN g)%Z).
  { unfold NN. rewrite mul_spec, Hn. change (φ 86) with 86%Z. apply Z.mod_small. rewrite wB_val. lia. }
  eexists. split; [reflexivity|].
  apply (flow_spec b h g Hv R C n lt LR LC Hn Hlt (86 * n) HB _ 0 res _ eq_refl L0 B0).
  intros X _. rewrite P0. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition darkness : uint -> uint -> array (array uint) -> uint := darkness_impl.

Definition darkness_correct :
  forall (b h : N) (g : list (list N)) (xb xh : uint) (xg : array (array uint)),
  valid_input b h g -> repr xb b -> repr xh h -> repr xg g ->
  exists o : N, repr (darkness xb xh xg) o /\ darkness_spec b h g o
  := darkness_impl_correct.
