(* Executable implementation and its required termination dependencies.
   Correctness proofs are in water_proofs.v. *)
(* Implementation of water (water.spec): incremental Edmonds-Karp. *)

From Speck Require Import Prelude.
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
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition water : uint -> array uint -> array uint -> array uint ->
  array uint -> array uint -> array uint -> array uint := water_impl.
