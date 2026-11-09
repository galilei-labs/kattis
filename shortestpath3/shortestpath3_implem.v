(* Executable implementation and its required termination dependencies.
   Correctness proofs are in shortestpath3_proofs.v. *)
From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
From Stdlib Require Sint63 ListDec.
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

Lemma dec_lt : forall a b : int, (a <? b) = true -> Zwf 0 (φ a) (φ b).
Proof.
  intros a b H. rewrite ltb_spec in H. pose proof (to_Z_bounded a).
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* The "unreached" state of the distance table: the largest signed word. *)
Definition INF : int := 4611686018427387903.

(* Relaxation of edge j on the table d; ch records a change. *)
Definition relax (us vs ws : array int) (j : int) (d : array int) (ch : bool)
  : array int * bool :=
  let du := d.[us.[j]] in
  if du =? INF then (d, ch) else
  let v := vs.[j] in
  let nd := du + ws.[j] in
  if ltsb nd d.[v] then (d.[v <- nd], true) else (d, ch).

(* One round: edges j, j+1, ..., m-1 relaxed in order. *)
Fixpoint edges_loop (us vs ws : array int) (m j : int) (d : array int) (ch : bool)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * bool :=
  match bdec (j <? m) with
  | left Hj =>
      let (d', ch') := relax us vs ws j d ch in
      edges_loop us vs ws m (j + 1) d' ch' (Acc_inv H (dec_step m j Hj))
  | right _ => (d, ch)
  end.

(* Rounds k, k+1, ..., R-1, stopping after a round that changed nothing. *)
Fixpoint rounds_loop (us vs ws : array int) (m R k : int) (d : array int)
    (H : Acc (Zwf 0) (gap R k)) {struct H} : array int :=
  match bdec (k <? R) with
  | left Hk =>
      let (d', ch) := edges_loop us vs ws m 0 d false
                        (Zwf_well_founded 0 (gap m 0)) in
      if ch then rounds_loop us vs ws m R (k + 1) d' (Acc_inv H (dec_step R k Hk))
      else d'
  | right _ => d
  end.

(* The check round: the target of every edge that still relaxes is marked
   and enqueued (once). *)
Fixpoint seed_loop (us vs ws d : array int) (m j : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * array int * int :=
  match bdec (j <? m) with
  | left Hj =>
      let du := d.[us.[j]] in
      let v := vs.[j] in
      if (negb (du =? INF) && ltsb (du + ws.[j]) d.[v] && (mk.[v] =? 0))%bool then
        seed_loop us vs ws d m (j + 1) mk.[v <- 1] q.[tl <- v] (tl + 1)
          (Acc_inv H (dec_step m j Hj))
      else seed_loop us vs ws d m (j + 1) mk q tl (Acc_inv H (dec_step m j Hj))
  | right _ => (mk, q, tl)
  end.

(* The adjacency, a forward star: hd.[u] is 1 + the last edge out of u (0:
   none), nx.[j] is 1 + the previous edge with the same source as j. *)
Fixpoint build_loop (us : array int) (m j : int) (hd nx : array int)
    (H : Acc (Zwf 0) (gap m j)) {struct H} : array int * array int :=
  match bdec (j <? m) with
  | left Hj =>
      let u := us.[j] in
      let h := hd.[u] in
      build_loop us m (j + 1) hd.[u <- j + 1] nx.[j <- h]
        (Acc_inv H (dec_step m j Hj))
  | right _ => (hd, nx)
  end.

(* The out-edges of one node, from the chain cell e on: their unmarked
   targets are marked and enqueued. *)
Fixpoint adj_loop (vs nx : array int) (e : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (φ e)) {struct H} : array int * array int * int :=
  match bdec (0 <? e) with
  | left _ =>
      let j := e - 1 in
      let v := vs.[j] in
      let e' := nx.[j] in
      match bdec (e' <? e) with
      | left Hd =>
          if mk.[v] =? 0 then
            adj_loop vs nx e' mk.[v <- 1] q.[tl <- v] (tl + 1)
              (Acc_inv H (dec_lt e' e Hd))
          else adj_loop vs nx e' mk q tl (Acc_inv H (dec_lt e' e Hd))
      | right _ => (mk, q, tl)
      end
  | right _ => (mk, q, tl)
  end.

(* The breadth-first search: queue cells h, h+1, ... are processed. *)
Fixpoint bfs_loop (vs hd nx : array int) (n h : int) (mk q : array int) (tl : int)
    (H : Acc (Zwf 0) (gap n h)) {struct H} : array int :=
  match bdec (h <? tl) with
  | left _ =>
      match bdec (h <? n) with
      | left Hh =>
          let x := q.[h] in
          let '(mk', q', tl') :=
            adj_loop vs nx hd.[x] mk q tl (Zwf_well_founded 0 (φ (hd.[x]))) in
          bfs_loop vs hd nx n (h + 1) mk' q' tl' (Acc_inv H (dec_step n h Hh))
      | right _ => mk
      end
  | right _ => mk
  end.

(* The answer of one query node t. *)
Definition answer_of (d mk : array int) (t : int) : answer int :=
  let x := d.[t] in
  if x =? INF then Impossible
  else if mk.[t] =? 0 then Dist x else MinusInfinity.

Fixpoint ans_loop (d mk qs : array int) (Q i : int) (out : array (answer int))
    (H : Acc (Zwf 0) (gap Q i)) {struct H} : array (answer int) :=
  match bdec (i <? Q) with
  | left Hi =>
      let a := answer_of d mk qs.[i] in
      ans_loop d mk qs Q (i + 1) out.[i <- a] (Acc_inv H (dec_step Q i Hi))
  | right _ => out
  end.

Definition shortestpath3_impl (n s : int) (us vs ws qs : array int)
  : array (answer int) :=
  let m := PArray.length us in
  let d0 := (PArray.make n INF).[s <- 0] in
  let d := rounds_loop us vs ws m (n - 1) 0 d0 (Zwf_well_founded 0 (gap (n - 1) 0)) in
  let '(mk, q, tl) := seed_loop us vs ws d m 0 (PArray.make n 0) (PArray.make n 0) 0
                        (Zwf_well_founded 0 (gap m 0)) in
  let '(hd, nx) := build_loop us m 0 (PArray.make n 0) (PArray.make m 0)
                     (Zwf_well_founded 0 (gap m 0)) in
  let mk' := bfs_loop vs hd nx n 0 mk q tl (Zwf_well_founded 0 (gap n 0)) in
  let Q := PArray.length qs in
  ans_loop d mk' qs Q 0 (PArray.make Q Impossible) (Zwf_well_founded 0 (gap Q 0)).

(* ------------------------------------------------------------------ *)
(* Graph theory on the math side: explicit paths, the reduction of a  *)
(* walk to a short one or a negative cycle, and the classification of  *)
(* a node from a distance view D and a mark view Mk.                   *)
(* ------------------------------------------------------------------ *)

(* The list accessor of the spec (PArray.get shadows the name). *)
Notation lget := Prelude.get.

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition shortestpath3 :
  uint -> uint -> array uint -> array uint -> array sint -> array uint ->
  array (answer sint) := shortestpath3_impl.
