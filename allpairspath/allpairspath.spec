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
    - Vertex count: $1 \le n \le 150$; Edge count: $0 \le m \le 5{,}000$.
    - Edge weights in $[-1{,}000, 1{,}000]$. *)

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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** A distance classification, parameterized by the numeric type: sint for machine values and Z for mathematical values. *)
Inductive answer (A : Type) : Type :=
  | Impossible : answer A
  | NegInfinity : answer A
  | Distance : A -> answer A.
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

(* Math side *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < len l (0, Impossible,
    or [] outside : never relied on). *)
Definition get_list_N (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0%N.
(** The integer at the given position, or zero beyond
    the list. *)
Definition get_list_Z (l : list Z) (k : N) : Z :=
  nth (N.to_nat k) l 0.
(** The answer at the given position, or [Unreachable]
    beyond the list. *)
Definition get_list_answer (l : list (answer Z))
  (k : N) : answer Z :=
  nth (N.to_nat k) l Impossible.
(** The row at the given position, or an empty list
    beyond the matrix. *)
Definition get_list_row (rows : list (list (answer Z)))
  (node : N)
    : list (answer Z) :=
  nth (N.to_nat node) rows [].

(** node is in [0, node_count - 1]. *)
Definition vertex (node_count node : N) : Prop :=
  (node < node_count)%N.

(** k is in [0, m - 1], m the number of edges. *)
Definition edge_index (edge_sources : list N)
  (k : N) : Prop :=
  (k < len edge_sources)%N.

(** There is an edge from source to target of weight
    weight. *)
Definition edge (edge_sources edge_targets : list N)
  (edge_weights : list Z)
    (source target : N) (weight : Z) : Prop :=
  exists k, edge_index edge_sources k /\
    get_list_N edge_sources k = source /\
    get_list_N edge_targets k = target /\
    get_list_Z edge_weights k = weight.

(** walk source target cost : there is a walk from
    source to target of total cost cost (vertices and
    edges may repeat). *)
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

(** There is a path from the source to the target. *)
Definition reachable (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N) : Prop :=
  exists cost, walk edge_sources edge_targets edge_weights
    source target cost.

(** distance is the cost of a walk from source to target
    and no walk from source to target costs less. *)
Definition shortest_distance
  (edge_sources edge_targets : list N)
    (edge_weights : list Z) (source target : N)
      (distance : Z) : Prop :=
  walk edge_sources edge_targets edge_weights source target
    distance /\
  forall cost, walk edge_sources edge_targets edge_weights
    source target cost ->
    distance <= cost.

(** Walks from source to target cost less than any
    bound. *)
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
  (* 0 <= m <= 5000, m the number of edges *)
  vi_m : (len edge_sources <= 5000)%N;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len edge_targets = len edge_sources;
  vi_ws_length : len edge_weights = len edge_sources;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index edge_sources k ->
    vertex node_count (get_list_N edge_sources k) /\
    vertex node_count (get_list_N edge_targets k);
  (* -1000 <= w <= 1000 *)
  vi_weights : Forall
    (fun weight => - 1000 <= weight <= 1000) edge_weights;
}.

(** The classification of walks from source to target: minimum distance, unreachable destination or cost unbounded below. *)
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
    Each output entry gives the minimum walk cost for its vertex pair, or identifies an
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

(** ** Interface *)

(** Find the minimum walk cost between every pair of vertices in a directed weighted graph,
    distinguishing unreachable pairs and costs unbounded below by negative cycles.
    - Input [node_count]: Number of graph vertices.
    - Input [edge_sources]: Source vertex of each directed edge.
    - Input [edge_targets]: Destination vertex of each directed edge.
    - Input [edge_weights]: Cost of each edge, in matching order.
    - Output [output]: Each output entry gives the minimum walk cost for its vertex pair, or identifies an unreachable pair or a cost unbounded below. *)
Program allpairspath : uint -> array uint -> array uint
  -> array sint ->
                           array (array (answer sint)).

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

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
