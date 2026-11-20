(** * Single source shortest path, non-negative weights *)

(** ** Description *)

(** Find the shortest distance from a source to every vertex of a directed
    graph with nonnegative edge weights, identifying unreachable vertices.

    [@kattis shortestpath1]
    - Difficulty: 2.0
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 10^{4}$; Edge count: $0 \le m \le 3 \times 10^{4}$.
    - Edge weights: $0 \le w_i \le 10^{3}$. *)

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
                    It runs in at most c1 * (n + m + 1) * (log2 (n + m) + 1)
                    + c2 steps of the cost model on a valid input, n the
                    number of nodes and m of edges (Dijkstra with a binary
                    heap), for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N ) (k : N) : N := nth
  (N.to_nat k) l 0.
(** The optional distance at zero-based index [k] in [l], or [None] beyond the end. *)
Definition get_list_option (l : list (option N)) (k : N) :
  option N :=
  nth (N.to_nat k) l None.

(** [node] is a valid zero-based vertex index below [node_count]. *)
Definition vertex (node_count node : N) : Prop :=
  node < node_count.

(** [k] is a valid zero-based index into the edge lists. *)
Definition edge_index (edge_sources : list N) (k : N) : Prop
  :=
  k < len edge_sources.

(** An input edge leads from [from_node] to [to_node] with weight [weight]. *)
Definition edge
  (edge_sources edge_targets edge_weights : list N)
    (from_node to_node weight : N) : Prop :=
  exists k, edge_index edge_sources k /\
    get_list_N edge_sources k = from_node /\
    get_list_N edge_targets k = to_node /\
    get_list_N edge_weights k = weight.

(** [path edge_sources edge_targets edge_weights source node cost] means that a
    directed walk from [source] to [node] has total weight [cost], using the graph
    given by the parallel edge lists. Vertices and edges may repeat. *)
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

(** Some path from [source] reaches [node]. *)
Definition reachable (edge_sources edge_targets edge_weights
  : list N )
    (source node : N) : Prop :=
  exists cost, path edge_sources edge_targets edge_weights
    source node cost.

(** A path from [source] to [node] attains [cost], and no such path has smaller
    weight. *)
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
  (* 1 <= n <= 10^4 *)
  vi_n : 1 <= node_count <= 10 ^ 4;
  (* 0 <= m <= 3 * 10^4 *)
  vi_m : len edge_sources <= 3 * 10 ^ 4;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len edge_targets = len edge_sources;
  vi_ws_length : len edge_weights = len edge_sources;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index edge_sources k ->
    vertex node_count (get_list_N edge_sources k) /\
    vertex node_count (get_list_N edge_targets k);
  (* 0 <= w <= 10^3 *)
  vi_weights : Forall (fun weight => weight <= 1000)
    edge_weights;
  (* 0 <= s < n *)
  vi_source : vertex node_count source;
}.

(** The vertex result is [Some] of the shortest distance from [source], or [None]
    exactly when the vertex is unreachable. *)
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
    The output has one entry per vertex in zero-based vertex order. Each entry
    gives the shortest distance from [source], or [None] if unreachable. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((V+E+1)\log(V+E+2))$ steps, where $V$ is the node count and $E$ the edge count. *)
Definition dijkstra_time_spec (c1 c2 n_node_count n_edge_sources steps : nat) : Prop :=
  (steps <= c1 * ((n_node_count + n_edge_sources + 1) * (Nat.log2 (n_node_count + n_edge_sources) + 1)) + c2)%nat.

(** ** Interface *)

(** Find the shortest distance from a source to every vertex of a directed graph with
    nonnegative edge weights, identifying unreachable vertices. The Kattis text
    interface prints only the requested vertices from this complete result.
    - Input [node_count]: Number of graph vertices.
    - Input [edge_sources]: Source vertex of each directed edge.
    - Input [edge_targets]: Destination vertex of each directed edge.
    - Input [edge_weights]: Nonnegative weight of each edge.
    - Input [source]: Zero-based vertex from which distances are measured.
    - Output [output]: One entry per vertex, in zero-based vertex order: [Some distance] for its shortest distance or [None] if unreachable. *)
Program dijkstra : uint -> array uint -> array uint -> array
  uint ->
                     uint -> array (option uint).

(** [@example dijkstra]
    - Sample: 1
    - Case: 1
    - Input [node_count]: 4
    - Input [edge_sources]: [0; 1; 3]
    - Input [edge_targets]: [1; 2; 0]
    - Input [edge_weights]: [2; 2; 2]
    - Input [source]: 0
    - Output [output]: [Some 0; Some 2; Some 4; None]
*)

(** [@example dijkstra]
    - Sample: 1
    - Case: 2
    - Input [node_count]: 2
    - Input [edge_sources]: [0]
    - Input [edge_targets]: [1]
    - Input [edge_weights]: [100]
    - Input [source]: 0
    - Output [output]: [Some 0; Some 100]
*)

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

(** ** Complexity *)

(** [@hide] [dijkstra_cost] is the cost translation of [dijkstra] (the judge
    recomputes it and compares) ... *)
Complexity dijkstra_cost for dijkstra.

(** [@fold complexity bound] ... and runs in at most c1 * (n + m + 1) * (log2 (n + m) + 1) + c2 steps of the cost model on a valid input, n the number of nodes and m of edges (Dijkstra with a binary heap), for two constants
    quantified before the inputs, on every valid input. [@requirement dijkstra_time_spec] *)
Specification dijkstra_time : exists c1 c2 : nat,
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
  dijkstra_time_spec c1 c2 (size node_count_int) (size edge_sources_arr) (cost5 dijkstra_cost node_count_int edge_sources_arr edge_targets_arr edge_weights_arr source_int).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
