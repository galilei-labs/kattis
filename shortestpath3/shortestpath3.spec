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
    - Vertex count: $1 \le n \le 10^{3}$; Edge count: $0 \le m \le 5 \times 10^{3}$; Query count: $1 \le q \le 100$.
    - Edge weights: $-2 \times 10^{3} \le w_i \le 2 \times 10^{3}$. *)

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
                    It runs in at most c1 * ((n + 1) * (m + 1) + q) + c2
                    steps of the cost model on a valid input, n the number
                    of nodes, m of edges and q of queries (Bellman-Ford,
                    then one breadth-first search, then the queries), for
                    two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** A query result: [Dist distance] gives a finite shortest distance, [Impossible]
    denotes an unreachable vertex, and [MinusInfinity] denotes costs unbounded
    below. Distances use [sint] in machine results and [Z] in mathematical results. *)
Inductive answer (D : Type) : Type :=
| Dist (distance : D)
| Impossible
| MinusInfinity.

(** [@hide] Constructor argument declarations and the representation relation
    between machine and mathematical answers. *)
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

(** [@hide] The cost translation of [answer], for the bound below. *)
Elpi complexity answer.

(* Math side. The edge list is three parallel lists, one
   per column of the input lines "u v w". *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [j] in [l], or [fallback] beyond the end. *)
Definition get {A} (l : list A) (fallback : A) (j : N) : A
  :=
  nth (N.to_nat j) l fallback.

(** [walk edge_sources edge_targets edge_weights source target cost] means that
    a directed walk from [source] to [target] has total weight [cost], using the
    graph given by the parallel edge lists. Vertices and edges may repeat; an
    empty walk has weight zero. *)
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

(** Some walk leads from [source] to [target]. *)
Definition reachable edge_sources edge_targets edge_weights
    (source target : N) : Prop :=
  exists cost, walk edge_sources edge_targets edge_weights
    source target cost.

(** For every integer bound, some walk from [source] to [target] has weight below
    that bound. *)
Definition arbitrarily_short edge_sources edge_targets
  edge_weights
    (source target : N) : Prop :=
  forall bound : Z, exists cost,
    walk edge_sources edge_targets edge_weights source
      target cost /\
    cost < bound.

(** A walk from [source] to [target] attains [distance], and no such walk has
    smaller weight. *)
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
  (* 1 <= n <= 10^3 *)
  vi_n : (1 <= node_count <= 1000)%N;
  (* 0 <= m <= 5 * 10^3, m lines "u v w" *)
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
  (* -2 * 10^3 <= w <= 2 * 10^3 *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((V+1)(E+1)+q)$ steps, where $V$ is the node count, $E$ the edge count, and $q$ the number of queries. *)
Definition shortestpath3_time_spec (c1 c2 n_node_count n_edge_sources n_queries steps : nat) : Prop :=
  (steps <= c1 * ((n_node_count + 1) * (n_edge_sources + 1) + n_queries) + c2)%nat.

(** ** Interface *)

(** Answer shortest-path queries from one source in a directed weighted graph,
    distinguishing unreachable vertices and costs unbounded below by negative cycles.
    - Input [node_count]: Number of graph vertices.
    - Input [source]: Vertex from which distances are measured.
    - Input [edge_sources]: Source vertex of each directed edge.
    - Input [edge_targets]: Destination vertex of each directed edge.
    - Input [edge_weights]: Signed weight of each corresponding edge.
    - Input [queries]: Vertices whose shortest distances are requested.
    - Output [output]: Each output entry gives the shortest distance to the queried vertex, or classifies it as unreachable or unbounded below. *)
Program shortestpath3 :
  uint -> uint -> array uint -> array uint -> array sint ->
    array uint ->
  array (answer sint).

(** [@example shortestpath3]
    - Sample: 1
    - Case: 1
    - Input [node_count]: 5
    - Input [source]: 0
    - Input [edge_sources]: [0; 1; 2; 0]
    - Input [edge_targets]: [1; 2; 1; 3]
    - Input [edge_weights]: [999; -2; 1; 2]%Z
    - Input [queries]: [1; 3; 4]
    - Output [output]: [MinusInfinity; Dist 2; Impossible]%Z
*)

(** [@example shortestpath3]
    - Sample: 1
    - Case: 2
    - Input [node_count]: 2
    - Input [source]: 0
    - Input [edge_sources]: [0]
    - Input [edge_targets]: [1]
    - Input [edge_weights]: [-100]%Z
    - Input [queries]: [1]
    - Output [output]: [Dist (-100)]%Z
*)

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

(** ** Complexity *)

(** [@hide] [shortestpath3_cost] is the cost translation of [shortestpath3] (the judge
    recomputes it and compares) ... *)
Complexity shortestpath3_cost for shortestpath3.

(** [@fold complexity bound] ... and runs in at most c1 * ((n + 1) * (m + 1) + q) + c2 steps of the cost model on a valid input, n the number of nodes, m of edges and q of queries (Bellman-Ford, then one breadth-first search, then the queries), for two constants
    quantified before the inputs, on every valid input. [@requirement shortestpath3_time_spec] *)
Specification shortestpath3_time : exists c1 c2 : nat,
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
  shortestpath3_time_spec c1 c2 (size node_count_int) (size edge_sources_arr) (size queries_arr) (cost6 shortestpath3_cost node_count_int source_int edge_sources_arr edge_targets_arr edge_weights_arr queries_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
