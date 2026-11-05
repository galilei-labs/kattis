(* @function        shortestpath3
   @signature       uint -> uint -> array uint -> array uint -> array sint ->
                    array uint -> array (answer sint)
   @math_signature  N -> N -> list N -> list N -> list Z -> list N ->
                    list (answer Z)
   @summary         [shortestpath3 n s us vs ws qs] takes one test case: a
                    directed graph on nodes 0..n-1 whose j-th edge goes from
                    us_j to vs_j with weight ws_j, a start node s and the
                    query nodes qs.  Answer i is Impossible when no path leads
                    from s to qs_i, MinusInfinity when there are arbitrarily
                    short paths from s to it, and Dist d when d is the minimum
                    distance from s to it.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* One output line per query, the same inductive on both sides: the machine
   answer carries a sint, the math answer a Z. *)
Inductive answer (D : Type) : Type :=
| Dist (d : D)
| Impossible
| MinusInfinity.
Arguments Dist {D} d.
Arguments Impossible {D}.
Arguments MinusInfinity {D}.

Instance repr_answer A M `{Repr A M} : Repr (answer A) (answer M) :=
  fun x i => match x, i with
             | Dist a, Dist d => repr a d
             | Impossible, Impossible => True
             | MinusInfinity, MinusInfinity => True
             | _, _ => False
             end.

(* Math side.  The edge list is three parallel lists, one per column of the
   input lines "u v w". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The j-th element of l (d past the end). *)
Definition get {A} (l : list A) (d : A) (j : N) : A := nth (N.to_nat j) l d.

(* [walk us vs ws x t c]: following edges of the graph from node x, one
   reaches node t with total weight c (a path in the statement's sense:
   edges and nodes may repeat; the empty path goes from x to x, weight 0). *)
Inductive walk (us vs : list N) (ws : list Z) : N -> N -> Z -> Prop :=
| walk_nil : forall x, walk us vs ws x x 0
| walk_cons : forall j t c,
    (j < len us)%N ->
    walk us vs ws (get vs 0%N j) t c ->
    walk us vs ws (get us 0%N j) t (get ws 0 j + c).

(* There is a path from s to t. *)
Definition reachable us vs ws (s t : N) : Prop :=
  exists c, walk us vs ws s t c.

(* There are arbitrarily short paths from s to t. *)
Definition arbitrarily_short us vs ws (s t : N) : Prop :=
  forall b : Z, exists c, walk us vs ws s t c /\ c < b.

(* d is the minimum distance from s to t: some path has weight d, none less. *)
Definition min_distance us vs ws (s t : N) (d : Z) : Prop :=
  walk us vs ws s t d /\ forall c, walk us vs ws s t c -> d <= c.

(* The statement's guarantees on one test case. *)
Record valid_input (n s : N) (us vs : list N) (ws : list Z) (qs : list N)
  : Prop := {
  (* 1 <= n <= 1000 *)
  vi_n : (1 <= n <= 1000)%N;
  (* 0 <= m <= 5000, m lines "u v w" *)
  vi_m : (len us <= 5000)%N;
  vi_vs : len vs = len us;
  vi_ws : len ws = len us;
  (* 1 <= q <= 100 *)
  vi_q : (1 <= len qs <= 100)%N;
  (* 0 <= s < n *)
  vi_s : (s < n)%N;
  (* Nodes are numbered from 0 to n-1: the ends of every edge ... *)
  vi_us : Forall (fun u => (u < n)%N) us;
  vi_vs_range : Forall (fun v => (v < n)%N) vs;
  (* ... and the node number given on each query line *)
  vi_qs : Forall (fun t => (t < n)%N) qs;
  (* -2000 <= w <= 2000 *)
  vi_w : Forall (fun w => -2000 <= w <= 2000) ws;
}.

(* One answer per query, in order; each answer is the case that holds. *)
Definition shortestpath3_spec (n s : N) (us vs : list N) (ws : list Z)
    (qs : list N) (o : list (answer Z)) : Prop :=
  len o = len qs /\
  forall i, (i < len qs)%N ->
    let t := get qs 0%N i in
    (get o Impossible i = Impossible <-> ~ reachable us vs ws s t) /\
    (get o Impossible i = MinusInfinity <-> arbitrarily_short us vs ws s t) /\
    (forall d, get o Impossible i = Dist d <-> min_distance us vs ws s t d).

Program shortestpath3 :
  uint -> uint -> array uint -> array uint -> array sint -> array uint ->
  array (answer sint).

Specification shortestpath3_correct :
  forall (n s : N) (us vs : list N) (ws : list Z) (qs : list N)
         (xn xs : uint) (xus xvs : array uint) (xws : array sint)
         (xqs : array uint),
  valid_input n s us vs ws qs ->
  repr xn n -> repr xs s -> repr xus us -> repr xvs vs -> repr xws ws ->
  repr xqs qs ->
  exists o : list (answer Z),
    repr (shortestpath3 xn xs xus xvs xws xqs) o /\
    shortestpath3_spec n s us vs ws qs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
