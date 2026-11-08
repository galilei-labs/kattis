(** * Single source shortest path, negative weights *)

(** ** Description *)

(** Answer shortest-path queries from one source in a directed weighted
    graph, distinguishing unreachable vertices and costs unbounded below by
    negative cycles.

    [@kattis shortestpath3]
    - Difficulty: 2.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 1,000 vertices; 0 to 5,000 edges; 1 to 100 queries.
    - Edge weights from -2,000 to 2,000. *)

(** ** Examples *)

(** - Input convention: Per case: vertex, edge and query counts and source; weighted edges and query vertices; four zeros end input.
    - Output convention: One shortest distance, Impossible or -Infinity per query. *)
(* Input:
5 4 3 0
0 1 999
1 2 -2
2 1 1
0 3 2
1
3
4
2 1 1 0
0 1 -100
1
0 0 0 0
Output:
-Infinity
2
Impossible

-100
*)

(** ** [@hide] Environment *)

(* @function        shortestpath3
   @signature       uint -> uint -> array uint -> array uint -> array sint ->
                    array uint -> array (answer sint)
   @math_signature  N -> N -> list N -> list N -> list Z -> list N ->
                    list (answer Z)
   @summary         [shortestpath3 node_count source edge_sources edge_targets
                    edge_weights queries] takes one test case: a directed
                    graph on nodes 0..node_count-1 whose j-th edge goes from
                    edge_sources_j to edge_targets_j with weight
                    edge_weights_j, a start node source and the query nodes
                    queries.  Answer i is Impossible when no path leads from
                    source to queries_i, MinusInfinity when there are
                    arbitrarily short paths from source to it, and Dist
                    distance when distance is the minimum distance from
                    source to it.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** One [output] line per query, the same inductive on
    both sides: the machine [answer] carries a sint, the
    math [answer] a Z. *)
Inductive answer (D : Type) : Type :=
| Dist (distance : D)
| Impossible
| MinusInfinity.
Arguments Dist {D} distance.
Arguments Impossible {D}.
Arguments MinusInfinity {D}.

Instance repr_answer A M `{Repr A M} : Repr (answer A)
  (answer M) :=
  fun machine math => match machine, math with
             | Dist distance, Dist distance' => repr
            distance distance'
             | Impossible, Impossible => True
             | MinusInfinity, MinusInfinity => True
             | _, _ => False
             end.

(* Math side. The edge list is three parallel lists, one
   per column of the input lines "u v w". *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The j-th element of l (fallback past the end). *)
Definition get {A} (l : list A) (fallback : A) (j : N) : A
  :=
  nth (N.to_nat j) l fallback.

(** A walk from start to target with the given total edge weight. Vertices and edges may repeat; an empty walk has weight zero. *)
Inductive walk (edge_sources edge_targets : list N)
  (edge_weights : list Z)
    : N -> N -> Z -> Prop :=
| walk_nil : forall node,
    walk edge_sources edge_targets edge_weights node node 0
| walk_cons : forall j target cost,
    (j < len edge_sources)%N ->
    walk edge_sources edge_targets edge_weights
      (get edge_targets 0%N j)
      target cost ->
    walk edge_sources edge_targets edge_weights
      (get edge_sources 0%N j)
      target (get edge_weights 0 j + cost).

(** There is a path from [source] to target. *)
Definition reachable edge_sources edge_targets edge_weights
    (source target : N) : Prop :=
  exists cost, walk edge_sources edge_targets edge_weights
    source target cost.

(** There are arbitrarily short paths from [source] to
    target. *)
Definition arbitrarily_short edge_sources edge_targets
  edge_weights
    (source target : N) : Prop :=
  forall bound : Z, exists cost,
    walk edge_sources edge_targets edge_weights source
      target cost /\
    cost < bound.

(** distance is the minimum distance from [source] to
    target: some path has weight distance, none less. *)
Definition min_distance edge_sources edge_targets
  edge_weights
    (source target : N) (distance : Z) : Prop :=
  walk edge_sources edge_targets edge_weights source target
    distance /\
  forall cost, walk edge_sources edge_targets edge_weights
    source target cost ->
    distance <= cost.

(** [@inside shortestpath3_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (node_count source : N)
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) (queries : list N) : Prop := {
  (* 1 <= n <= 1000 *)
  vi_n : (1 <= node_count <= 1000)%N;
  (* 0 <= m <= 5000, m lines "u v w" *)
  vi_m : (len edge_sources <= 5000)%N;
  vi_vs : len edge_targets = len edge_sources;
  vi_ws : len edge_weights = len edge_sources;
  (* 1 <= q <= 100 *)
  vi_q : (1 <= len queries <= 100)%N;
  (* 0 <= s < n *)
  vi_s : (source < node_count)%N;
  (* Nodes are numbered from 0 to n-1: the ends of every
     edge ... *)
  vi_us : Forall (fun node => (node < node_count)%N)
    edge_sources;
  vi_vs_range : Forall (fun node => (node < node_count)%N)
    edge_targets;
  (* ... and the node number given on each query line *)
  vi_qs : Forall (fun target => (target < node_count)%N)
    queries;
  (* -2000 <= w <= 2000 *)
  vi_w : Forall (fun weight => -2000 <= weight <= 2000)
    edge_weights;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry gives the shortest distance to the queried vertex, or classifies
    it as unreachable or unbounded below. *)
Definition shortestpath3_spec
  (node_count source : N)
  (edge_sources edge_targets : list N )
  (edge_weights : list Z )
  (queries : list N)
  (output : list (answer Z))
  : Prop :=
  len output = len queries /\
  forall i, (i < len queries)%N ->
    let target := get queries 0%N i in
    (get output Impossible i = Impossible <->
       ~ reachable edge_sources edge_targets edge_weights
         source target) /\
    (get output Impossible i = MinusInfinity <->
       arbitrarily_short edge_sources edge_targets
         edge_weights source
         target) /\
    (forall distance, get output Impossible i = Dist
      distance <->
       min_distance edge_sources edge_targets edge_weights
         source target
         distance).

(** ** Interface *)

(** Answer shortest-path queries from one source in a directed weighted graph,
    distinguishing unreachable vertices and costs unbounded below by negative cycles.
    - Input [node_count]:
    - Input [source]:
    - Input [edge_sources]:
    - Input [edge_targets]:
    - Input [edge_weights]:
    - Input [queries]:
    - Output [output]: *)
Program shortestpath3 :
  uint -> uint -> array uint -> array uint -> array sint ->
    array uint ->
  array (answer sint).

(** ** Bridge *)

(** [@requirement shortestpath3_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [shortestpath3_spec]. *)
Specification shortestpath3_correct :
  forall (node_count source : N) (edge_sources edge_targets
    : list N )
         (edge_weights : list Z) (queries : list N)
         (node_count_int source_int : uint)
         (edge_sources_arr edge_targets_arr : array uint)
         (edge_weights_arr : array sint ) (queries_arr :
           array uint ),
  valid_input node_count source edge_sources edge_targets
    edge_weights
    queries ->
  repr node_count_int node_count -> repr source_int source
    ->
  repr edge_sources_arr edge_sources -> repr
    edge_targets_arr edge_targets ->
  repr edge_weights_arr edge_weights -> repr queries_arr
    queries ->
  exists output : list (answer Z),
    repr (shortestpath3 node_count_int source_int
      edge_sources_arr
            edge_targets_arr edge_weights_arr queries_arr)
            output /\
    shortestpath3_spec node_count source edge_sources
      edge_targets
      edge_weights queries output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
