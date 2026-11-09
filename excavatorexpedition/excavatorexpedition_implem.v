(* Executable implementation and its required termination dependencies.
   Correctness proofs are in excavatorexpedition_proofs.v. *)
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

From Speck Require Import Prelude.
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
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition excavator : PrimString.string -> array uint -> array uint -> sint :=
  excavator_impl.
