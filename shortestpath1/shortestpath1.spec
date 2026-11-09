(** * Single source shortest path, non-negative weights *)

(** ** Description *)

(** Find the shortest distance from a source to every vertex of a directed
    graph with nonnegative edge weights, identifying unreachable vertices.

    [@kattis shortestpath1]
    - Difficulty: 2.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 10{,}000$; Edge count: $0 \le m \le 30{,}000$.
    - Edge weights in $[0, 1{,}000]$. *)

(** ** Examples *)

(** - Input convention: Per case: vertex, edge and query counts and source; weighted edges and query vertices; four zeros end input.
    - Output convention: One shortest distance or Impossible per query. *)
(* Input:
4 3 4 0
0 1 2
1 2 2
3 0 2
0
1
2
3
2 1 1 0
0 1 100
1
0 0 0 0
Output:
0
2
4
Impossible

100
*)

(** ** [@hide] Environment *)

(* @function        dijkstra
   @signature       uint -> array uint -> array uint -> array uint -> uint
                    -> array (option uint)
   @math_signature  N -> list N -> list N -> list N -> N -> list (option N)
   @summary         [dijkstra node_count edge_sources edge_targets
                    edge_weights source] returns, for every node of the
                    directed graph on the nodes 0 .. node_count - 1 with the
                    edges edge_sources[k] -> edge_targets[k] of weight
                    edge_weights[k], Some the least cost of a path from
                    source to that node, or None when there is no such path
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < [len] l (0, or None,
    outside : never relied on). *)
Definition get_list_N (l : list N ) (k : N) : N := nth
  (N.to_nat k) l 0.
(** Get list option. *)
Definition get_list_option (l : list (option N)) (k : N) :
  option N :=
  nth (N.to_nat k) l None.

(** node is in [0, node_count - 1]. *)
Definition vertex (node_count node : N) : Prop :=
  node < node_count.

(** k is in [0, m - 1]. *)
Definition edge_index (edge_sources : list N) (k : N) : Prop
  :=
  k < len edge_sources.

(** There is an [edge] from from_node to to_node of
    weight weight. *)
Definition edge
  (edge_sources edge_targets edge_weights : list N)
    (from_node to_node weight : N) : Prop :=
  exists k, edge_index edge_sources k /\
    get_list_N edge_sources k = from_node /\
    get_list_N edge_targets k = to_node /\
    get_list_N edge_weights k = weight.

(** [path] [source] node cost : there is a [path] from
    [source] to node of total weight cost. *)
Inductive path (edge_sources edge_targets edge_weights :
  list N )
    (source : N) : N -> N -> Prop :=
  | path_refl :
      path edge_sources edge_targets edge_weights source
        source 0
  | path_step : forall from_node to_node weight cost,
      path edge_sources edge_targets edge_weights source
        from_node cost ->
      edge edge_sources edge_targets edge_weights from_node
        to_node weight ->
      path edge_sources edge_targets edge_weights source
        to_node
        (cost + weight).

(** Reachable. *)
Definition reachable (edge_sources edge_targets edge_weights
  : list N )
    (source node : N) : Prop :=
  exists cost, path edge_sources edge_targets edge_weights
    source node cost.

(** cost is the cost of a [path] from [source] to node
    and no [path] from [source] to node costs less. *)
Definition shortest_distance
  (edge_sources edge_targets edge_weights : list N)
    (source node cost : N) : Prop :=
  path edge_sources edge_targets edge_weights source node
    cost /\
  forall cost', path edge_sources edge_targets edge_weights
    source node cost' ->
    cost <= cost'.

(** [@inside dijkstra_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (node_count : N)
    (edge_sources edge_targets edge_weights : list N)
      (source : N) : Prop := {
  (* 1 <= n <= 10000 *)
  vi_n : 1 <= node_count <= 10 ^ 4;
  (* 0 <= m <= 30000 *)
  vi_m : len edge_sources <= 3 * 10 ^ 4;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len edge_targets = len edge_sources;
  vi_ws_length : len edge_weights = len edge_sources;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index edge_sources k ->
    vertex node_count (get_list_N edge_sources k) /\
    vertex node_count (get_list_N edge_targets k);
  (* 0 <= w <= 1000 *)
  vi_weights : Forall (fun weight => weight <= 1000)
    edge_weights;
  (* 0 <= s < n *)
  vi_source : vertex node_count source;
}.

(** The entry for node : Some the shortest distance from
    [source] when a [path] reaches node, None otherwise. *)
Definition distance_of
  (edge_sources edge_targets edge_weights : list N)
    (source node : N) (entry : option N) : Prop :=
  match entry with
  | Some cost =>
      shortest_distance edge_sources edge_targets
        edge_weights source node cost
  | None => ~ reachable edge_sources edge_targets
    edge_weights source node
  end.

(** ** Correctness *)

(** [@requirement]
    Each output entry gives the shortest distance from the source to its vertex, or None
    if that vertex is unreachable. *)
Definition dijkstra_spec
  (node_count : N)
  (edge_sources edge_targets edge_weights : list N)
  (source : N)
  (output : list (option N))
  : Prop :=
  len output = node_count /\
  forall node, vertex node_count node ->
    distance_of edge_sources edge_targets edge_weights
      source node
      (get_list_option output node).

(** ** Interface *)

(** Find the shortest distance from a source to every vertex of a directed graph with
    nonnegative edge weights, identifying unreachable vertices.
    - Input [node_count]: Number of graph vertices.
    - Input [edge_sources]: Source vertex of each directed edge.
    - Input [edge_targets]: Destination vertex of each directed edge.
    - Input [edge_weights]: Nonnegative weight of each edge.
    - Input [source]: Vertex from which distances are measured.
    - Output [output]: Each output entry gives the shortest distance from the source to its vertex, or None if that vertex is unreachable. *)
Program dijkstra : uint -> array uint -> array uint -> array
  uint ->
                     uint -> array (option uint).

(** ** Bridge *)

(** [@requirement dijkstra_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [dijkstra_spec]. *)
Specification dijkstra_correct :
  forall (node_count : N)
    (edge_sources edge_targets edge_weights : list N)
         (source : N) (node_count_int : uint)
         (edge_sources_arr edge_targets_arr edge_weights_arr
           : array uint)
         (source_int : uint),
  valid_input node_count edge_sources edge_targets
    edge_weights source ->
  repr node_count_int node_count -> repr edge_sources_arr
    edge_sources ->
  repr edge_targets_arr edge_targets -> repr
    edge_weights_arr edge_weights ->
  repr source_int source ->
  exists output : list (option N),
    repr (dijkstra node_count_int edge_sources_arr
      edge_targets_arr
                   edge_weights_arr source_int) output /\
    dijkstra_spec node_count edge_sources edge_targets
      edge_weights source
      output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
