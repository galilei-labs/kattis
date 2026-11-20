(** * All Pairs Shortest Path *)

(** ** Description *)

(** Find the minimum walk cost between every pair of vertices in a directed
    weighted graph, distinguishing unreachable pairs and costs unbounded
    below by negative cycles.

    [@kattis allpairspath]
    - Difficulty: 2.7
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 150$; Edge count: $0 \le m \le 5 \times 10^{3}$.
    - Edge weights: $-10^{3} \le w_i \le 10^{3}$. *)

(** ** Examples *)

(** - Input convention: Per case: vertex, edge and query counts; weighted directed edges; vertex-pair queries; 0 0 0 ends input.
    - Output convention: One minimum distance, Impossible or -Infinity per query; a blank line separates cases. *)
(* Input:
4 3 4
0 1 2
1 2 2
3 3 1
0 2
1 2
3 0
3 3
2 1 2
0 1 100
0 1
1 0
0 0 0
Output:
4
2
Impossible
0

100
Impossible
*)

(** ** [@hide] Environment *)

(* @function        allpairspath
   @signature       uint -> array uint -> array uint -> array sint
                    -> array (array (answer sint))
   @math_signature  N -> list N -> list N -> list Z -> list (list (answer Z))
   @summary         [allpairspath node_count edge_sources edge_targets
                    edge_weights] returns, for every pair of nodes
                    (source, target) of the directed graph on the nodes
                    0 .. node_count - 1 with the edges edge_sources[k] ->
                    edge_targets[k] of weight edge_weights[k], the answer
                    at row source, column target : Distance the least cost
                    of a walk from source to target when it exists,
                    Impossible when no walk reaches target from source,
                    NegInfinity when walks from source to target have
                    arbitrarily low costs
                    It runs in at most c1 * (n + 1) * (n + m + 1) * (log2 (n
                    + m) + 1) + c2 steps of the cost model on a valid input,
                    n the number of nodes and m of edges (Johnson's
                    algorithm: one Bellman-Ford pass in n * m, then n runs
                    of Dijkstra with a binary heap), for two constants c1,
                    c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** A shortest-path result: a finite distance, an unreachable destination, or costs
    unbounded below. Distances use [sint] on the machine side and [Z] on the
    mathematical side. *)
Inductive answer (A : Type) : Type :=
  | Impossible : answer A
  | NegInfinity : answer A
  | Distance : A -> answer A.

(** [@hide] Constructor argument declarations. *)
Arguments Impossible {A}.
Arguments NegInfinity {A}.
Arguments Distance {A} _.

(** [@hide] A machine answer represents a math answer :
    the same case, and a represented distance. *)
Instance repr_answer A M `{Repr A M} : Repr (answer A)
  (answer M) :=
  fun machine math =>
    match machine, math with
    | Impossible, Impossible => True
    | NegInfinity, NegInfinity => True
    | Distance machine_distance, Distance math_distance =>
        repr machine_distance math_distance
    | _, _ => False
    end.

(** [@hide] The cost translation of [answer], for the bound below. *)
Elpi complexity answer.

(* Math side *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0%N.
(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.
(** The entry at zero-based index [k] in [l], or [Impossible] beyond the end. *)
Definition get_list_answer (l : list (answer Z))
  (k : N) : answer Z :=
  nth (N.to_nat k) l Impossible.
(** The row at the given position, or an empty list
    beyond the matrix. *)
Definition get_list_row (rows : list (list (answer Z)))
  (node : N)
    : list (answer Z) :=
  nth (N.to_nat node) rows [].

(** [node] is a valid zero-based vertex index below [node_count]. *)
Definition vertex (node_count node : N) : Prop :=
  (node < node_count)%N.

(** [k] is a valid zero-based index into the edge lists. *)
Definition edge_index (edge_sources : list N)
  (k : N) : Prop :=
  (k < len edge_sources)%N.

(** The input contains a directed edge from [source] to [target] with weight
    [weight]. *)
Definition edge (edge_sources edge_targets : list N)
  (edge_weights : list Z)
    (source target : N) (weight : Z) : Prop :=
  exists k, edge_index edge_sources k /\
    get_list_N edge_sources k = source /\
    get_list_N edge_targets k = target /\
    get_list_Z edge_weights k = weight.

(** [walk edge_sources edge_targets edge_weights source target cost] means that
    a directed walk from [source] to [target] has total weight [cost], using the
    graph given by the parallel edge lists. Vertices and edges may repeat; an
    empty walk has weight zero. *)
Inductive walk (edge_sources edge_targets : list N)
  (edge_weights : list Z)
    (source : N) : N -> Z -> Prop :=
  | walk_refl :
      walk edge_sources edge_targets edge_weights source
        source 0
  | walk_step : forall node next weight cost,
      walk edge_sources edge_targets edge_weights source
        node cost ->
      edge edge_sources edge_targets edge_weights node next
        weight ->
      walk edge_sources edge_targets edge_weights source
        next (cost + weight).

(** Some walk leads from [source] to [target]. *)
Definition reachable (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N) : Prop :=
  exists cost, walk edge_sources edge_targets edge_weights
    source target cost.

(** [distance] is attained by a walk from [source] to [target], and no such walk has
    smaller weight. *)
Definition shortest_distance
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N)
      (distance : Z) : Prop :=
  walk edge_sources edge_targets edge_weights source target
    distance /\
  forall cost, walk edge_sources edge_targets edge_weights
    source target cost ->
    distance <= cost.

(** For every integer bound, some walk from [source] to [target] has weight below
    that bound. *)
Definition arbitrarily_short
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N) : Prop :=
  forall bound, exists cost,
    walk edge_sources edge_targets edge_weights source
      target cost /\
    cost < bound.

(** [@inside allpairspath_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (node_count : N)
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) : Prop := {
  (* 1 <= n <= 150, n the number of nodes *)
  vi_n : (1 <= node_count <= 150)%N;
  (* 0 <= m <= 5 * 10^3, m the number of edges *)
  vi_m : (len edge_sources <= 5000)%N;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len edge_targets = len edge_sources;
  vi_ws_length : len edge_weights = len edge_sources;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index edge_sources k ->
    vertex node_count (get_list_N edge_sources k) /\
    vertex node_count (get_list_N edge_targets k);
  (* -10^3 <= w <= 10^3 *)
  vi_weights : Forall
    (fun weight => - 1000 <= weight <= 1000) edge_weights;
}.

(** Classify walks from [source] to [target] by their minimum distance, absence, or
    weights unbounded below. *)
Definition answer_of (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N)
      (pair_answer : answer Z)
    : Prop :=
  match pair_answer with
  | Impossible =>
      ~ reachable edge_sources edge_targets edge_weights
        source target
  | NegInfinity =>
      arbitrarily_short edge_sources edge_targets
        edge_weights source target
  | Distance distance =>
      shortest_distance edge_sources edge_targets
        edge_weights source target
        distance
  end.

(** ** Correctness *)

(** [@requirement]
    The output is a square matrix indexed by source row and destination column,
    both zero-based. Each entry gives the minimum walk cost, or identifies an
    unreachable pair or a cost unbounded below. *)
Definition allpairspath_spec (node_count : N)
    (edge_sources edge_targets : list N)
      (edge_weights : list Z)
    (output : list (list (answer Z))) : Prop :=
  len output = node_count /\
  forall source, vertex node_count source ->
    len (get_list_row output source) = node_count /\
    forall target, vertex node_count target ->
      answer_of edge_sources edge_targets edge_weights
        source target
        (get_list_answer
          (get_list_row output source) target).

(** ** Complexity *)

(** [@requirement] Runs in $O((V+1)(V+E+1)\log(V+E+2))$ steps, where $V$ is the number of nodes and $E$ the number of edges. *)
Definition allpairspath_time_spec (c1 c2 n_node_count n_edge_sources steps : nat) : Prop :=
  (steps <= c1 * ((n_node_count + 1) * (n_node_count + n_edge_sources + 1) * (Nat.log2 (n_node_count + n_edge_sources) + 1)) + c2)%nat.

(** ** Interface *)

(** Find the minimum walk cost between every pair of vertices in a directed weighted graph,
    distinguishing unreachable pairs and costs unbounded below by negative cycles.
    The function returns all vertex pairs; the Kattis text interface selects
    the requested entries from this matrix.
    - Input [node_count]: Number of graph vertices.
    - Input [edge_sources]: Source vertex of each directed edge.
    - Input [edge_targets]: Destination vertex of each directed edge.
    - Input [edge_weights]: Cost of each edge, in matching order.
    - Output [output]: A [node_count] by [node_count] matrix with zero-based source rows and destination columns. [Distance distance] gives the minimum cost, [Impossible] denotes no walk, and [NegInfinity] denotes costs unbounded below. *)
Program allpairspath : uint -> array uint -> array uint
  -> array sint ->
                           array (array (answer sint)).

(** [@example allpairspath]
    - Sample: 1
    - Case: 1
    - Input [node_count]: 4
    - Input [edge_sources]: [0; 1; 3]
    - Input [edge_targets]: [1; 2; 3]
    - Input [edge_weights]: [2; 2; 1]%Z
    - Output [output]: [[Distance 0; Distance 2; Distance 4; Impossible]; [Impossible; Distance 0; Distance 2; Impossible]; [Impossible; Impossible; Distance 0; Impossible]; [Impossible; Impossible; Impossible; Distance 0]]%Z
*)

(** [@example allpairspath]
    - Sample: 1
    - Case: 2
    - Input [node_count]: 2
    - Input [edge_sources]: [0]
    - Input [edge_targets]: [1]
    - Input [edge_weights]: [100]%Z
    - Output [output]: [[Distance 0; Distance 100]; [Impossible; Distance 0]]%Z
*)

(** ** Bridge *)

(** [@requirement allpairspath_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [allpairspath_spec]. *)
Specification allpairspath_correct :
  forall (node_count : N)
    (edge_sources edge_targets : list N)
         (edge_weights : list Z)
         (node_count_int : uint)
         (edge_sources_arr edge_targets_arr : array uint)
         (edge_weights_arr : array sint),
  valid_input node_count edge_sources edge_targets
    edge_weights ->
  repr node_count_int node_count ->
  repr edge_sources_arr edge_sources
    -> repr edge_targets_arr edge_targets ->
  repr edge_weights_arr edge_weights ->
  exists output : list (list (answer Z)),
    repr (allpairspath node_count_int edge_sources_arr
      edge_targets_arr
            edge_weights_arr) output /\
    allpairspath_spec node_count edge_sources edge_targets
      edge_weights
      output.

(** ** Complexity *)

(** [@hide] [allpairspath_cost] is the cost translation of [allpairspath] (the judge
    recomputes it and compares) ... *)
Complexity allpairspath_cost for allpairspath.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) * (n + m + 1) * (log2 (n + m) + 1) + c2 steps of the cost model on a valid input, n the number of nodes and m of edges (Johnson's algorithm: one Bellman-Ford pass in n * m, then n runs of Dijkstra with a binary heap), for two constants
    quantified before the inputs, on every valid input. [@requirement allpairspath_time_spec] *)
Specification allpairspath_time : exists c1 c2 : nat,
  forall (node_count : N)
  (edge_sources edge_targets : list N)
  (edge_weights : list Z)
  (node_count_int : uint)
  (edge_sources_arr edge_targets_arr : array uint)
  (edge_weights_arr : array sint),
  valid_input node_count edge_sources edge_targets
  edge_weights ->
  repr node_count_int node_count ->
  repr edge_sources_arr edge_sources
  -> repr edge_targets_arr edge_targets ->
  repr edge_weights_arr edge_weights ->
  allpairspath_time_spec c1 c2 (size node_count_int) (size edge_sources_arr) (cost4 allpairspath_cost node_count_int edge_sources_arr edge_targets_arr edge_weights_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
