(** * Minimum Spanning Tree *)

(** ** Description *)

(** Find a minimum spanning tree of an undirected weighted graph. Return its
    total weight and edge indices, or report that the graph is disconnected.

    [@kattis minspantree]
    - Difficulty: 2.5
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 2 \times 10^{4}$; Edge count: $0 \le m \le 3 \times 10^{4}$.
    - Edge weights: $-2 \times 10^{4} \le w_i \le 2 \times 10^{4}$. *)

(** ** Examples *)

(** - Input convention: Per case: vertex and edge counts, followed by weighted edges; 0 0 ends input.
    - Output convention: Minimum tree cost and lexicographically sorted endpoint pairs, or Impossible if disconnected. *)
(* Input:
4 4
0 1 1
1 2 2
1 3 3
2 3 0
2 1
0 1 100
3 0
0 0
Output:
3
0 1
1 2
2 3
100
0 1
Impossible
*)

(** ** [@hide] Environment *)
(* @function        mst
   @signature       uint -> array uint -> array uint -> array sint
                    -> option (sint * array uint)
   @math_signature  N -> list N -> list N -> list Z -> option (Z * list N)
   @summary         [mst vertex_count edge_sources edge_targets edge_weights]
                    returns a minimum spanning tree of the undirected graph
                    on the vertices 0 .. vertex_count - 1 with the edges
                    (edge_sources[k], edge_targets[k]) of weight
                    edge_weights[k], as its total weight and the indices of
                    its edges, or None when the graph is not connected ; any
                    minimum spanning tree when several exist
                    It runs in at most c1 * ((m + 1) * (log2 m + log2 n + 1)
                    + n) + c2 steps of the cost model on a valid input, n
                    the number of vertices and m of edges (the sort of the
                    edges, then m union-find operations each within log2 n
                    by union by rank), for two constants c1, c2.
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
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.
(** The integer at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0%Z.

(** [candidate] is a valid zero-based vertex index below [vertex_count]. *)
Definition vertex (vertex_count candidate : N) : Prop :=
  candidate < vertex_count.

(** [k] is a valid zero-based index into the edge lists. *)
Definition edge_index (edge_sources : list N)
  (k : N) : Prop :=
  k < len edge_sources.

(** The undirected edge at index [k] joins [endpoint] and [endpoint']. *)
Definition joins (edge_sources edge_targets : list N)
    (k endpoint endpoint' : N) : Prop :=
  (get_list_N edge_sources k = endpoint /\
   get_list_N edge_targets k = endpoint') \/
  (get_list_N edge_sources k = endpoint' /\
   get_list_N edge_targets k = endpoint).

(** [linked edge_sources edge_targets selected origin destination] means that
    [origin] and [destination] are connected by a walk in the graph given by the
    endpoint lists, using only edge indices that satisfy [selected]. *)
Inductive linked (edge_sources edge_targets : list N)
  (selected : N -> Prop)
    (origin : N) : N -> Prop :=
  | linked_here : linked edge_sources edge_targets selected
    origin origin
  | linked_hop : forall middle k reached,
      linked edge_sources edge_targets selected origin
        middle ->
      edge_index edge_sources k -> selected k ->
      joins edge_sources edge_targets k middle reached ->
      linked edge_sources edge_targets selected origin
        reached.

(** Allow every edge when testing connectivity. *)
Definition every_edge : N -> Prop := fun _ => True.

(** Every pair of valid vertices is connected using the input edges. *)
Definition graph_connected (vertex_count : N)
    (edge_sources edge_targets : list N) : Prop :=
  forall node other, vertex vertex_count node ->
    vertex vertex_count other ->
    linked edge_sources edge_targets every_edge node other.

(** Every index in [tree] names an input edge. *)
Definition tree_edges (edge_sources : list N)
  (tree : list N) : Prop :=
  Forall (edge_index edge_sources) tree.

(** [tree] contains no repeated edge index. *)
Definition tree_distinct (tree : list N) : Prop :=
  NoDup tree.

(** [tree] contains exactly [vertex_count - 1] edges. *)
Definition tree_size (vertex_count : N)
  (tree : list N) : Prop :=
  len tree = vertex_count - 1.

(** The edges selected by [tree] connect every pair of valid vertices. *)
Definition tree_spans (vertex_count : N)
    (edge_sources edge_targets : list N) (tree : list N) :
      Prop :=
  forall node other, vertex vertex_count node ->
    vertex vertex_count other ->
    linked edge_sources edge_targets (fun k => In k tree)
      node other.

(** [tree] contains [vertex_count - 1] distinct input edges connecting all vertices. *)
Record spanning_tree (vertex_count : N)
  (edge_sources edge_targets : list N)
    (tree : list N) : Prop := {
  st_edges : tree_edges edge_sources tree;
  st_distinct : tree_distinct tree;
  st_size : tree_size vertex_count tree;
  st_spans : tree_spans vertex_count edge_sources
    edge_targets tree;
}.

(** The sum of the weights of the edges selected by [tree]. *)
Fixpoint total_weight (edge_weights : list Z)
  (tree : list N) : Z :=
  match tree with
  | [] => 0%Z
  | k :: rest => (get_list_Z edge_weights k + total_weight
    edge_weights rest)%Z
  end.

(** [@inside mst_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (vertex_count : N)
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) : Prop := {
  (* 1 <= n <= 2 * 10^4 *)
  vi_n : 1 <= vertex_count <= 20000;
  (* 0 <= m <= 3 * 10^4 *)
  vi_m : len edge_sources <= 30000;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len edge_targets = len edge_sources;
  vi_ws_length : len edge_weights = len edge_sources;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index edge_sources k ->
    vertex vertex_count (get_list_N edge_sources k) /\
    vertex vertex_count (get_list_N edge_targets k);
  (* -2 * 10^4 <= w <= 2 * 10^4 *)
  vi_weights : Forall (fun weight => (- 20000 <= weight <=
    20000)%Z)
                 edge_weights;
}.

(** [tree] is a spanning tree with total weight [tree_weight], and no spanning tree
    has smaller total weight. *)
Definition minimum_spanning_tree (vertex_count : N)
    (edge_sources edge_targets : list N) (edge_weights :
      list Z)
    (tree_weight : Z) (tree : list N) : Prop :=
  spanning_tree vertex_count edge_sources edge_targets tree
    /\
  tree_weight = total_weight edge_weights tree /\
  forall tree', spanning_tree vertex_count edge_sources
    edge_targets tree' ->
    (total_weight edge_weights tree <= total_weight
      edge_weights tree')%Z.

(** ** Correctness *)

(** [@requirement]
    The output gives a minimum spanning tree and its total weight, or None exactly when
    the graph is disconnected. *)
Definition mst_spec (vertex_count : N)
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) (output : option (Z * list N)) :
      Prop :=
  match output with
  | None => ~ graph_connected vertex_count edge_sources
    edge_targets
  | Some (tree_weight, tree) =>
      minimum_spanning_tree vertex_count edge_sources
        edge_targets
        edge_weights tree_weight tree
  end.

(** ** Complexity *)

(** [@requirement] Runs in $O((E+1)(\log(E+2)+\log(V+2))+V)$ steps, where $V$ is the vertex count and $E$ the edge count. *)
Definition mst_time_spec (c1 c2 n_edge_sources n_vertex_count steps : nat) : Prop :=
  (steps <= c1 * ((n_edge_sources + 1) * (Nat.log2 (n_edge_sources) + Nat.log2 (n_vertex_count) + 1) + n_vertex_count) + c2)%nat.

(** ** Interface *)

(** Find a minimum spanning tree of an undirected weighted graph. Return its total weight
    and edge indices, or report that the graph is disconnected.
    - Input [vertex_count]: Number of graph vertices.
    - Input [edge_sources]: First endpoint of each undirected edge.
    - Input [edge_targets]: Second endpoint of each undirected edge.
    - Input [edge_weights]: Weight of each corresponding edge.
    - Output [output]: The output gives a minimum spanning tree and its total weight, or None exactly when the graph is disconnected. *)
Program mst : uint -> array uint -> array uint -> array sint
  ->
                option (sint * array uint).

(** [@example mst]
    - Sample: 1
    - Case: 1
    - Input [vertex_count]: 4
    - Input [edge_sources]: [0; 1; 1; 2]
    - Input [edge_targets]: [1; 2; 3; 3]
    - Input [edge_weights]: [1; 2; 3; 0]%Z
    - Output [output]: Some (3%Z, [0; 1; 3])
*)

(** [@example mst]
    - Sample: 1
    - Case: 2
    - Input [vertex_count]: 2
    - Input [edge_sources]: [0]
    - Input [edge_targets]: [1]
    - Input [edge_weights]: [100]%Z
    - Output [output]: Some (100%Z, [0])
*)

(** [@example mst]
    - Sample: 1
    - Case: 3
    - Input [vertex_count]: 3
    - Input [edge_sources]: []
    - Input [edge_targets]: []
    - Input [edge_weights]: []
    - Output [output]: None
*)

(** ** Bridge *)

(** [@requirement mst_spec] [@fold full correctness statement] On valid
    represented inputs, [mst] returns a represented output
    satisfying [mst_spec]. *)
Specification mst_correct :
  forall (vertex_count : N) (edge_sources edge_targets :
    list N)
         (edge_weights : list Z) (vertex_count_int : uint)
         (edge_sources_arr edge_targets_arr : array uint)
         (edge_weights_arr : array sint),
  valid_input vertex_count edge_sources edge_targets
    edge_weights ->
  repr vertex_count_int vertex_count ->
    repr edge_sources_arr edge_sources ->
  repr edge_targets_arr edge_targets ->
    repr edge_weights_arr edge_weights ->
  exists output : option (Z * list N),
    repr (mst vertex_count_int edge_sources_arr
      edge_targets_arr
            edge_weights_arr) output /\
    mst_spec vertex_count edge_sources edge_targets
      edge_weights output.

(** ** Complexity *)

(** [@hide] [mst_cost] is the cost translation of [mst] (the judge
    recomputes it and compares) ... *)
Complexity mst_cost for mst.

(** [@fold complexity bound] ... and runs in at most c1 * ((m + 1) * (log2 m + log2 n + 1) + n) + c2 steps of the cost model on a valid input, n the number of vertices and m of edges (the sort of the edges, then m union-find operations each within log2 n by union by rank), for two constants
    quantified before the inputs, on every valid input. [@requirement mst_time_spec] *)
Specification mst_time : exists c1 c2 : nat,
  forall (vertex_count : N) (edge_sources edge_targets :
  list N)
  (edge_weights : list Z) (vertex_count_int : uint)
  (edge_sources_arr edge_targets_arr : array uint)
  (edge_weights_arr : array sint),
  valid_input vertex_count edge_sources edge_targets
  edge_weights ->
  repr vertex_count_int vertex_count ->
  repr edge_sources_arr edge_sources ->
  repr edge_targets_arr edge_targets ->
  repr edge_weights_arr edge_weights ->
  mst_time_spec c1 c2 (size edge_sources_arr) (size vertex_count_int) (cost4 mst_cost vertex_count_int edge_sources_arr edge_targets_arr edge_weights_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
