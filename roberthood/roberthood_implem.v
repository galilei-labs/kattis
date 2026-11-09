(* Executable implementation and its required termination dependencies.
   Correctness proofs are in roberthood_proofs.v. *)
(* Implementation of roberthood.spec: the diameter of a point set by
   convex hull (Andrew's monotone chain) and rotating calipers, exactly in
   63-bit integers, one float square root at the end. *)

From Speck Require Import Prelude.
From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals Lra Lia ZifyUint63 Zwf.
From Stdlib Require Sint63.
From StdGalilei Require Import repr.
From StdGalilei Require Import repr_float.
Import ListNotations.
From Stdlib Require Import Bool.

Open Scope uint63_scope.
Open Scope bool_scope.
Unset Lia Cache.

Ltac sia := zify; Z.to_euclidean_division_equations; lia.

(* ------------------------------------------------------------------ *)
(* The termination devices                                             *)
(* ------------------------------------------------------------------ *)

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

End Loop.

Lemma dec_double : forall n w : int, ((w <? n) && (w <? w + w)) = true ->
  Zwf 0 (gap n (w + w)) (gap n w).
Proof.
  intros n w H. apply andb_prop in H. destruct H as [H1 H2].
  rewrite Uint63.ltb_spec in H1, H2. pose proof (to_Z_bounded n).
  pose proof (to_Z_bounded (w + w)). unfold Zwf, gap. lia.
Qed.

Lemma dec_pred : forall (t : int) (b : bool), ((1 <? t) && b) = true ->
  Zwf 0 (to_Z (t - 1)) (to_Z t).
Proof.
  intros t b H. apply andb_prop in H. destruct H as [H _].
  rewrite Uint63.ltb_spec in H. unfold Zwf. change (to_Z 1) with 1%Z in H. sia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* A point (x, y), |x|, |y| <= 1000, is the key (x + 1000) * 2048 + (y + 1000):
   key order is lexicographic order, and Kneg - key is the key of (-x, -y). *)
Definition encode (x y : int) : int := (x + 1000) * 2048 + (y + 1000).
Definition Kneg : int := 4098000.

Definition cx (k : int) : int := k / 2048 - 1000.
Definition cy (k : int) : int := k mod 2048 - 1000.

(* (a2 - a1) x (b2 - b1), read signed *)
Definition mcross (a1 a2 b1 b2 : int) : int :=
  (cx a2 - cx a1) * (cy b2 - cy b1) - (cy a2 - cy a1) * (cx b2 - cx b1).

(* the squared distance between the point of key a and the opposite of the
   point of key b *)
Definition msq (a b : int) : int :=
  let dx := cx a + cx b in let dy := cy a + cy b in dx * dx + dy * dy.

(* -- the keys -- *)
Definition key_step (x y : array int) (i : int) (A : array int) : array int :=
  A.[i <- encode x.[i] y.[i]].

(* -- bottom-up merge sort -- *)
Definition merge_step (src : array int) (mid hi : int) (k : int)
    (st : int * int * array int) : int * int * array int :=
  let '(i, j, D) := st in
  if (i <? mid) && ((hi <=? j) || (src.[i] <=? src.[j]))
  then (i + 1, j, D.[k <- src.[i]])
  else (i, j + 1, D.[k <- src.[j]]).

Definition merge (src : array int) (lo mid hi : int) (D : array int) : array int :=
  let '(_, _, D) := loop hi (fun _ _ => true) (merge_step src mid hi) lo (lo, mid, D) in D.

Definition pass_step (src : array int) (n w : int) (c : int) (D : array int) : array int :=
  let lo := c * (w + w) in
  let mid := if lo + w <? n then lo + w else n in
  let hi := if lo + (w + w) <? n then lo + (w + w) else n in
  merge src lo mid hi D.

Definition merge_pass (src D : array int) (n w : int) : array int :=
  loop ((n + (w + w) - 1) / (w + w)) (fun _ _ => true) (pass_step src n w) 0 D.

Fixpoint msort_rec (n w : int) (A B : array int) (H : Acc (Zwf 0) (gap n w)) {struct H}
    : array int :=
  match bdec ((w <? n) && (w <? w + w)) with
  | left Hw => msort_rec n (w + w) (merge_pass A B n w) A (Acc_inv H (dec_double n w Hw))
  | right _ => A
  end.

Definition msort (A : array int) (n : int) : array int :=
  msort_rec n 1 A (PArray.make n 0) (Zwf_well_founded 0 (gap n 1)).

(* -- removal of duplicates: Q[0 .. m) -- *)
Definition dedup_step (A : array int) (i : int) (st : array int * int) : array int * int :=
  let '(Q, m) := st in
  let a := A.[i] in
  if a =? Q.[m - 1] then (Q, m) else (Q.[m <- a], m + 1).

(* -- the negated points, in increasing key order -- *)
Definition neg_step (Q : array int) (m : int) (i : int) (B : array int) : array int :=
  B.[i <- Kneg - Q.[m - 1 - i]].

(* -- the lower chain of Q[0 .. m) (monotone chain) -- *)
Fixpoint pops (St : array int) (c : int) (t : int) (H : Acc (Zwf 0) (to_Z t)) {struct H} : int :=
  match bdec ((1 <? t) && negb (Sint63.ltb 0 (mcross St.[t - 2] St.[t - 1] St.[t - 2] c))) with
  | left Hc => pops St c (t - 1) (Acc_inv H (dec_pred t _ Hc))
  | right _ => t
  end.

Definition chain_step (Q : array int) (i : int) (st : array int * int) : array int * int :=
  let '(St, t) := st in
  let c := Q.[i] in
  let t := pops St c t (Zwf_well_founded 0 (to_Z t)) in
  (St.[t <- c], t + 1).

Definition chain (Q : array int) (m : int) : array int * int :=
  loop m (fun _ _ => true) (chain_step Q) 1 (PArray.make m Q.[0], 1).

(* -- rotating calipers between the lower chain L and the lower chain N of
      the negated points (the upper chain, from right to left) -- *)
Definition cal_step (L N : array int) (lL lN : int) (s : int) (st : int * int * int)
    : int * int * int :=
  let '(j, k, best) := st in
  let d := msq L.[j] N.[k] in
  let best := if best <? d then d else best in
  if (j <? lL) && ((k =? lN) || Sint63.ltb 0 (mcross L.[j] L.[j + 1] N.[k] N.[k + 1]))
  then (j + 1, k, best) else (j, k + 1, best).

Definition calipers (L N : array int) (lL lN : int) : int :=
  let '(j, k, best) := loop (lL + lN) (fun _ _ => true) (cal_step L N lL lN) 0 (0, 0, 0) in
  let d := msq L.[j] N.[k] in
  if best <? d then d else best.

Definition diam2 (x y : array int) : int :=
  let n := PArray.length x in
  let A := loop n (fun _ _ => true) (key_step x y) 0 (PArray.make n 0) in
  let A := msort A n in
  let '(Q, m) := loop n (fun _ _ => true) (dedup_step A) 1 (PArray.make n A.[0], 1) in
  if m <? 2 then 0
  else
    let Q2 := loop m (fun _ _ => true) (neg_step Q m) 0%uint63 (PArray.make m 0%uint63) in
    let '(L, tL) := chain Q m in
    let '(N, tN) := chain Q2 m in
    calipers L N (tL - 1) (tN - 1).

Definition roberthood (x y : array sint) : float :=
  PrimFloat.sqrt (PrimFloat.of_uint63 (diam2 x y)).

(* ------------------------------------------------------------------ *)
(* Small signed arithmetic is exact                                    *)
(* ------------------------------------------------------------------ *)

Notation sv := Sint63.to_Z.

(* ------------------------------------------------------------------ *)
(* Plane geometry over Z                                               *)
(* ------------------------------------------------------------------ *)

Local Open Scope Z_scope.
