(* Executable implementation and its required termination dependencies.
   Correctness proofs are in slowleak_proofs.v. *)
(* Implementation of slowleak (slowleak.spec): Floyd-Warshall on the
   road graph, then an O(V^2) array Dijkstra on the refill points.

   Code.  One flat n*n [array int] T, cell a*n+b for intersections a+1,
   b+1: INF = 2^61 everywhere, 0 on the diagonal ([diag_loop]), then
   T[u][v] := min(T[u][v], k) in both directions for every road
   ([edge_loop]), then Floyd-Warshall in place, pivot k outermost
   ([fw_k] / [fw_i] / [fw_j], T[i][k] read once per row).  Entries never
   exceed INF, so a sum of two entries (< 2^62) never wraps.  Dijkstra
   ([dij_loop]) runs on M = t+2 nodes: node 0 is the school, node a (1 <=
   a <= t) the station xs[a-1], node t+1 home; V (built by [vx_loop]) maps
   a node to its 0-based intersection.  The edge a -> b weighs
   T[V[a]][V[b]] when that is <= d.  Each round selects the unvisited node
   of least finite distance ([sel_loop]); home selected: Some dist; none
   left: None ("stuck"); otherwise it is marked and its edges relaxed
   ([rel_loop]); home is never expanded.  A counter r (M at start) bounds
   the rounds.  No Z, no nat, no list in the code; every array is used
   linearly.

   Termination: every loop recurses on an erased [Acc (Zwf 0) _] proof
   (gap hi i, or phi r for [dij_loop]), as in the template.

   Proof.  [fwinv K T]: entries <= INF, zero diagonal, every entry < INF
   is the length of a walk, every road bounds its cell, and the triangle
   inequality through every pivot < K.  [stepped] describes the table in
   the middle of a pivot step (cells before the flat position q updated);
   row and column k are unchanged during step k because T[k][k] = 0.  With
   K = n, [fw_lower]: no walk is shorter than its cell.  Dijkstra is
   proven on an abstract weight w: [dp a L] (a path from node 0 to a of
   length L, never leaving home), invariant [dji] (sound distances,
   visited distances optimal, relaxed edges), and the cut lemma [cut]:
   every path to an unvisited node passes an unvisited node of distance
   <= its length; [ucnt] counts the unvisited nodes for the r = 0 branch.
   [sound] / [complete] relate dp on the node graph to the spec's [trip]
   (through [fw_lower] and the walks of the table).  The None case uses
   the spec's vi_answer: if some trip existed, a shortest one would
   (double negation, [dn_min]) and be < 2^31 < INF, so Dijkstra would
   have reached home. *)

From Speck Require Import Prelude.
From Respeced Require Import Repr.
From Stdlib Require Import ZArith NArith List Uint63 PArray ZifyUint63 Lia Zwf.
Import ListNotations.

Open Scope uint63_scope.

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

Lemma dec_down : forall r : int,
  (0 <? r) = true -> Zwf 0 (φ (r - 1)) (φ r).
Proof.
  intros r H. rewrite ltb_spec in H. change (φ 0) with 0%Z in H.
  assert (H1 : (φ (r - 1)) = ((φ r) - 1)%Z) by sia.
  unfold Zwf. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The program                                                         *)
(* ------------------------------------------------------------------ *)

(* "infinity": 2^61, above every distance, and twice it still fits. *)
Definition INF : int := 2305843009213693952.

(* T.[p] := min(T.[p], s) *)
Definition setmin (T : array int) (p s : int) : array int :=
  if s <? T.[p] then T.[p <- s] else T.

(* the diagonal cells i*n+i, i < n, set to 0 *)
Fixpoint diag_loop (n i : int) (T : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi => diag_loop n (i + 1) T.[i * n + i <- 0] (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

(* the roads e .. m-1, in both directions *)
Fixpoint edge_loop (n : int) (xi xj xk : array int) (m e : int) (T : array int)
    (H : Acc (Zwf 0) (gap m e)) {struct H} : array int :=
  match bdec (e <? m) with
  | left He =>
      let u := xi.[e] - 1 in
      let v := xj.[e] - 1 in
      let k := xk.[e] in
      edge_loop n xi xj xk m (e + 1) (setmin (setmin T (u * n + v) k) (v * n + u) k)
        (Acc_inv H (dec_step m e He))
  | right _ => T
  end.

(* Floyd-Warshall, pivot k, row i (rowi = i*n), columns j .. n-1;
   aik = T[i][k], rowk = k*n. *)
Fixpoint fw_j (n rowi rowk aik j : int) (T : array int)
    (H : Acc (Zwf 0) (gap n j)) {struct H} : array int :=
  match bdec (j <? n) with
  | left Hj =>
      fw_j n rowi rowk aik (j + 1) (setmin T (rowi + j) (aik + T.[rowk + j]))
        (Acc_inv H (dec_step n j Hj))
  | right _ => T
  end.

Fixpoint fw_i (n k rowk i : int) (T : array int)
    (H : Acc (Zwf 0) (gap n i)) {struct H} : array int :=
  match bdec (i <? n) with
  | left Hi =>
      let rowi := i * n in
      fw_i n k rowk (i + 1)
        (fw_j n rowi rowk T.[rowi + k] 0 T (Zwf_well_founded 0 (gap n 0)))
        (Acc_inv H (dec_step n i Hi))
  | right _ => T
  end.

Fixpoint fw_k (n k : int) (T : array int)
    (H : Acc (Zwf 0) (gap n k)) {struct H} : array int :=
  match bdec (k <? n) with
  | left Hk =>
      fw_k n (k + 1) (fw_i n k (k * n) 0 T (Zwf_well_founded 0 (gap n 0)))
        (Acc_inv H (dec_step n k Hk))
  | right _ => T
  end.

(* V.[i+1] := xs.[i] - 1 for i = i .. t-1: the 0-based intersection of
   every repair station. *)
Fixpoint vx_loop (xs : array int) (t i : int) (V : array int)
    (H : Acc (Zwf 0) (gap t i)) {struct H} : array int :=
  match bdec (i <? t) with
  | left Hi => vx_loop xs t (i + 1) V.[i + 1 <- xs.[i] - 1] (Acc_inv H (dec_step t i Hi))
  | right _ => V
  end.

(* Dijkstra: the unvisited node of least finite distance among i .. M-1,
   b/bv the best so far (b = M: none). *)
Fixpoint sel_loop (M : int) (vis : array bool) (dist : array int) (i b bv : int)
    (H : Acc (Zwf 0) (gap M i)) {struct H} : int :=
  match bdec (i <? M) with
  | left Hi =>
      if vis.[i] then sel_loop M vis dist (i + 1) b bv (Acc_inv H (dec_step M i Hi))
      else
        let di := dist.[i] in
        if di <? bv then sel_loop M vis dist (i + 1) i di (Acc_inv H (dec_step M i Hi))
        else sel_loop M vis dist (i + 1) b bv (Acc_inv H (dec_step M i Hi))
  | right _ => b
  end.

(* Dijkstra: relax the edges u -> b, b = b .. M-1 unvisited, of weight
   T[V[u]][V[b]] <= d; ru = V[u]*n, du = dist[u]. *)
Fixpoint rel_loop (M : int) (V T : array int) (vis : array bool) (d ru du b : int)
    (dist : array int) (H : Acc (Zwf 0) (gap M b)) {struct H} : array int :=
  match bdec (b <? M) with
  | left Hb =>
      let dist' :=
        if vis.[b] then dist
        else
          let w := T.[ru + V.[b]] in
          if w <=? d then setmin dist b (du + w) else dist in
      rel_loop M V T vis d ru du (b + 1) dist' (Acc_inv H (dec_step M b Hb))
  | right _ => dist
  end.

(* Dijkstra: at most r more nodes to visit; tgt is home. *)
Fixpoint dij_loop (n M tgt : int) (V T : array int) (d r : int) (vis : array bool)
    (dist : array int) (H : Acc (Zwf 0) (φ r)) {struct H} : option int :=
  match bdec (0 <? r) with
  | left Hr =>
      let u := sel_loop M vis dist 0 M INF (Zwf_well_founded 0 (gap M 0)) in
      if u =? M then None
      else if u =? tgt then Some dist.[u]
      else
        let vis' := vis.[u <- true] in
        let dist' := rel_loop M V T vis' d (V.[u] * n) dist.[u] 0 dist
                       (Zwf_well_founded 0 (gap M 0)) in
        dij_loop n M tgt V T d (r - 1) vis' dist' (Acc_inv H (dec_down r Hr))
  | right _ => None
  end.

Definition slowleak_impl (x y : uint) (xs xi xj xk : array uint) : option uint :=
  let n := x in
  let T0 := diag_loop n 0 (PArray.make (n * n) INF) (Zwf_well_founded 0 (gap n 0)) in
  let m := PArray.length xi in
  let T1 := edge_loop n xi xj xk m 0 T0 (Zwf_well_founded 0 (gap m 0)) in
  let T := fw_k n 0 T1 (Zwf_well_founded 0 (gap n 0)) in
  let t := PArray.length xs in
  let M := t + 2 in
  let V := vx_loop xs t 0 (PArray.make M 0).[t + 1 <- n - 1]
             (Zwf_well_founded 0 (gap t 0)) in
  dij_loop n M (t + 1) V T y M (PArray.make M false) (PArray.make M INF).[0 <- 0]
    (Zwf_well_founded 0 (φ M)).

(* ------------------------------------------------------------------ *)
(* The spec's items, at top level                                      *)
(* ------------------------------------------------------------------ *)

Definition slowleak :
  uint -> uint -> array uint -> array uint -> array uint -> array uint ->
  option uint := slowleak_impl.
