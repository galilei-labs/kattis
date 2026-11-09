(* Executable implementation and its required termination dependencies.
   Correctness proofs are in largesttriangle_proofs.v. *)
From Largesttriangle.spec Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
From Flocq Require Core.Core.
Import ListNotations.

Unset Lia Cache.

(* ================================================================== *)
(* Geometry over Z                                                     *)
(* ================================================================== *)

Local Open Scope Z_scope.
Definition vsub (a b : Z * Z) : Z * Z := (fst a - fst b, snd a - snd b).

Definition E (Q : Z -> Z * Z) (l : Z -> Z) (t : Z) : Z * Z := vsub (Q (l (t + 1))) (Q (l t)).

Local Close Scope Z_scope.

(* ================================================================== *)
(* The program                                                         *)
(* ================================================================== *)

Local Open Scope bool_scope.
Local Open Scope uint63_scope.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

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

Lemma dec_r : forall r : int, (1 <? r) = true -> Zwf 0 (to_Z (r - 1)) (to_Z r).
Proof.
  intros r H. rewrite Uint63.ltb_spec in H. change (to_Z 1) with 1%Z in H.
  assert (to_Z (r - 1) = (to_Z r - 1)%Z) by sia. unfold Zwf. lia.
Qed.

Lemma ms_dec1 : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo)) = true ->
  Zwf 0 (gap (lo + (hi - lo) / 2) lo) (gap hi lo).
Proof.
  intros lo hi H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (to_Z 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  assert (E2 : to_Z ((hi - lo) / 2) = ((to_Z hi - to_Z lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : to_Z (lo + (hi - lo) / 2) = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((to_Z hi - to_Z lo) / 2 <= to_Z hi - to_Z lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold Zwf, gap. rewrite E3. split; [lia |].
  assert ((to_Z hi - to_Z lo) / 2 < to_Z hi - to_Z lo)%Z by (apply Z.div_lt; lia). lia.
Qed.

Lemma ms_dec2 : forall lo hi : int, ((lo <? hi) && (1 <? hi - lo)) = true ->
  Zwf 0 (gap hi (lo + (hi - lo) / 2)) (gap hi lo).
Proof.
  intros lo hi H. apply andb_prop in H as [H1 H2]. rewrite Uint63.ltb_spec in H1, H2.
  change (to_Z 1) with 1%Z in H2. pose proof (to_Z_bounded hi). pose proof (to_Z_bounded lo).
  assert (E : to_Z (hi - lo) = (to_Z hi - to_Z lo)%Z) by sia.
  assert (E2 : to_Z ((hi - lo) / 2) = ((to_Z hi - to_Z lo) / 2)%Z) by (rewrite Uint63.div_spec, E; reflexivity).
  assert (E3 : to_Z (lo + (hi - lo) / 2) = (to_Z lo + (to_Z hi - to_Z lo) / 2)%Z).
  { rewrite Uint63.add_spec, E2. apply Z.mod_small. split; [apply Z.add_nonneg_nonneg; [lia | apply Z.div_pos; lia] |].
    assert ((to_Z hi - to_Z lo) / 2 <= to_Z hi - to_Z lo)%Z by (apply Z.div_le_upper_bound; lia). lia. }
  unfold Zwf, gap. rewrite E3. split; [lia |].
  assert (1 <= (to_Z hi - to_Z lo) / 2)%Z by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(* The one generic loop: for i = lo, lo+1, ... while i < hi and [cont i s], s := f i s. *)
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

End Loop.

(* -- Cross products, exact in 63 bits ------------------------------- *)

Definition SH : int := 67108864.               (* 2^26 > 4 * 10^7 *)
Definition OFF : int := 1152921504606846976.   (* 2^60 *)

(* the cross product (B - A) x (C - A), plus OFF so that it is non-negative *)
Definition crs (ax ay bx by_ cx cy : int) : int :=
  (bx - ax) * (cy - ay) - (cx - ax) * (by_ - ay) + OFF.

(* -- The sort: top-down merge sort of the keys ----------------------- *)

Definition merge_step (A : array int) (mid hi : int) (k : int) (st : array int * int * int)
    : array int * int * int :=
  let '(T, i, j) := st in
  if (i <? mid) && ((hi <=? j) || (A.[i] <=? A.[j])) then (T.[k <- A.[i]], i + 1, j)
  else (T.[k <- A.[j]], i, j + 1).

Definition merge (A T : array int) (lo mid hi : int) : array int :=
  let '(T', _, _) := loop hi (fun _ _ => true) (merge_step A mid hi) lo (T, lo, mid) in T'.

Definition copy_step (T : array int) (k : int) (A : array int) : array int := A.[k <- T.[k]].

Fixpoint msort (A T : array int) (lo hi : int) (H : Acc (Zwf 0) (gap hi lo)) {struct H}
    : array int * array int :=
  match bdec ((lo <? hi) && (1 <? hi - lo)) with
  | left Hlt =>
      let mid := lo + (hi - lo) / 2 in
      let '(A1, T1) := msort A T lo mid (Acc_inv H (ms_dec1 lo hi Hlt)) in
      let '(A2, T2) := msort A1 T1 mid hi (Acc_inv H (ms_dec2 lo hi Hlt)) in
      let T3 := merge A2 T2 lo mid hi in
      (loop hi (fun _ _ => true) (copy_step T3) lo A2, T3)
  | right _ => (A, T)
  end.

Definition sort (K : array int) (n : int) : array int :=
  fst (msort K (PArray.make n 0) 0 n (Zwf_well_founded 0 (gap n 0))).

(* -- Distinct points ------------------------------------------------- *)

Definition dedup_step (S : array int) (t : int) (st : array int * int) : array int * int :=
  let '(D, m) := st in
  if (m =? 0) || (D.[m - 1] <? S.[t]) then (D.[m <- S.[t]], m + 1) else (D, m).

Definition decode_step (D : array int) (u : int) (st : array int * array int) : array int * array int :=
  let '(PX, PY) := st in let d := D.[u] in (PX.[u <- d / SH], PY.[u <- d mod SH]).

(* -- One chain of Andrew's monotone chain ---------------------------- *)

Fixpoint popl (X Y ST : array int) (s r : int) (H : Acc (Zwf 0) (to_Z r)) {struct H} : int :=
  match bdec (1 <? r) with
  | left Hr =>
      let i1 := ST.[r - 2] in let i2 := ST.[r - 1] in
      if crs X.[i1] Y.[i1] X.[i2] Y.[i2] X.[s] Y.[s] <=? OFF
      then popl X Y ST s (r - 1) (Acc_inv H (dec_r r Hr))
      else r
  | right _ => r
  end.

Definition pass_step (X Y : array int) (s : int) (st : array int * int) : array int * int :=
  let '(ST, r) := st in
  let r' := popl X Y ST s r (Zwf_well_founded 0 (to_Z r)) in
  (ST.[r' <- s], r' + 1).

Definition pass (X Y : array int) (m : int) : array int * int :=
  loop m (fun _ _ => true) (pass_step X Y) 1 (PArray.make m 0, 1).

Definition rev_step (X : array int) (m : int) (s : int) (R : array int) : array int :=
  R.[s <- X.[m - 1 - s]].

Definition low_step (PX PY LS : array int) (t : int) (st : array int * array int) : array int * array int :=
  let '(HX, HY) := st in let v := LS.[t] in (HX.[t <- PX.[v]], HY.[t <- PY.[v]]).

Definition up_step (RX RY US : array int) (a : int) (t : int) (st : array int * array int)
    : array int * array int :=
  let '(HX, HY) := st in let v := US.[t - a + 1] in (HX.[t <- RX.[v]], HY.[t <- RY.[v]]).

(* -- The rotating sweep ---------------------------------------------- *)

(* the third corner k climbs while the area does not decrease *)
Fixpoint climb (HX HY : array int) (hm xi yi xj yj k gk : int)
    (H : Acc (Zwf 0) (gap hm k)) {struct H} : int :=
  match bdec (k <? hm) with
  | left Hk =>
      let k1 := k + 1 in
      let g1 := crs xi yi xj yj HX.[k1] HY.[k1] in
      if gk <=? g1 then climb HX HY hm xi yi xj yj k1 g1 (Acc_inv H (dec_step hm k Hk)) else k
  | right _ => k
  end.

(* the second corner j = j, j+1, ..., hm - 1 ; the best area found so far *)
Fixpoint jloop (HX HY : array int) (hm xi yi j k best : int)
    (H : Acc (Zwf 0) (gap hm j)) {struct H} : int :=
  match bdec (j <? hm) with
  | left Hj =>
      let xj := HX.[j] in let yj := HY.[j] in
      let k1 := if j <? k then k else j + 1 in
      let k2 := climb HX HY hm xi yi xj yj k1 (crs xi yi xj yj HX.[k1] HY.[k1])
                  (Zwf_well_founded 0 (gap hm k1)) in
      let g := crs xi yi xj yj HX.[k2] HY.[k2] in
      jloop HX HY hm xi yi (j + 1) k2 (if best <? g then g else best) (Acc_inv H (dec_step hm j Hj))
  | right _ => best
  end.

Definition sweep_step (HX HY : array int) (h : int) (i best : int) : int :=
  jloop HX HY (h - 1) HX.[i] HY.[i] (i + 1) (i + 2) best (Zwf_well_founded 0 (gap (h - 1) (i + 1))).

Definition sweep (HX HY : array int) (h : int) : int :=
  loop (h - 2) (fun _ _ => true) (sweep_step HX HY h) 0 OFF.

(* -- The whole ------------------------------------------------------- *)

Definition fzero : float := of_uint63 0.

Definition largest_triangle_impl (x y : array uint) : float :=
  let n := PArray.length x in
  let K := loop n (fun _ _ => true) (fun i K => K.[i <- x.[i] * SH + y.[i]]) 0 (PArray.make n 0) in
  let S := sort K n in
  let '(D, m) := loop n (fun _ _ => true) (dedup_step S) 0 (PArray.make n 0, 0) in
  if m <? 3 then fzero else
  let '(PX, PY) := loop m (fun _ _ => true) (decode_step D) 0 (PArray.make m 0, PArray.make m 0) in
  let '(LS, a) := pass PX PY m in
  let RX := loop m (fun _ _ => true) (rev_step PX m) 0 (PArray.make m 0) in
  let RY := loop m (fun _ _ => true) (rev_step PY m) 0 (PArray.make m 0) in
  let '(US, b) := pass RX RY m in
  let h := a + b - 2 in
  if h <? 3 then fzero else
  let '(HX1, HY1) := loop a (fun _ _ => true) (low_step PX PY LS) 0 (PArray.make h 0, PArray.make h 0) in
  let '(HX, HY) := loop h (fun _ _ => true) (up_step RX RY US a) a (HX1, HY1) in
  let best := sweep HX HY h in
  (of_uint63 (best - OFF) / of_uint63 2)%float.

Definition largest_triangle : array uint -> array uint -> float := largest_triangle_impl.
