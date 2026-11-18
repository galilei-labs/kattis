(** * YATP *)

(** ** Description *)

(** For each vertex $u$ of a weighted tree, minimize
    $\operatorname{distance}(u, v) + \operatorname{penalty}(u) \cdot \operatorname{penalty}(v)$
    over all vertices $v$, then sum these minimum
    costs.

    [@kattis yatp]
    - Difficulty: 4.3
    - CPU time limit: 5 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 2 \times 10^{5}$ forming a tree.
    - Vertex penalties and edge weights: $1 \le p_i, w_i \le 10^{6}$. *)

(** ** Examples *)

(** - Input convention: Vertex count, vertex penalties, then weighted tree edges with 1-based endpoints.
    - Output convention: The sum of the minimum path costs over all starting vertices. *)
(* Input:
5
9 7 1 1 9
3 2 8
5 2 10
4 3 10
2 1 2
Output:
63
*)

(** ** [@hide] Environment *)

(* @function        yatp
   @signature       array uint -> array uint -> array uint -> array uint -> uint
   @math_signature  list N -> list N -> list N -> list N -> N
   @summary         [yatp penalties edge_sources edge_targets edge_weights]
                    takes a tree on the nodes 1..n (n the length of
                    penalties, node v of penalty the v-th entry of
                    penalties) whose k-th edge joins edge_sources_k and
                    edge_targets_k with weight edge_weights_k.  The cost of
                    a simple path is the sum of its edge weights plus the
                    product of the penalties of its two endpoints (the
                    square of the penalty for the path of 0 edges); the
                    result is the sum, over every node, of the smallest
                    cost of a simple path starting at that node.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* The edge list of the input, n - 1 lines "i
   j w" , is given as three parallel lists, one per
   column; nodes are numbered 1..n as in the statement. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get (l : list N) (k : N) : N :=
  nth (N.to_nat k) l 0.

(** The penalty assigned to the one-based vertex [node]. *)
Definition penalty (penalties : list N) (node : N) : N :=
  get penalties (node - 1).

(** The input edge at index [k] joins [node] and [other], in either direction. *)
Definition joins (edge_sources edge_targets : list N)
  (k node other : N)
    : Prop :=
  k < len edge_sources /\
  ((get edge_sources k = node /\ get edge_targets k = other)
    \/
   (get edge_sources k = other /\ get edge_targets k = node)
     ).

(** [walk edge_sources edge_targets nodes edges] means that [nodes] lists the
    vertices visited in order, with consecutive vertices joined by the
    corresponding edge indices in [edges]. The endpoint lists describe the graph. *)
Inductive walk (edge_sources edge_targets : list N)
    : list N -> list N -> Prop :=
| walk_one : forall node, walk edge_sources edge_targets
  [node] []
| walk_step : forall node next k nodes edges,
    joins edge_sources edge_targets k node next ->
    walk edge_sources edge_targets (next :: nodes) edges ->
    walk edge_sources edge_targets (node :: next :: nodes)
      (k :: edges).

(** A walk from [start] to [finish] with no repeated vertex. *)
Definition simple_path (edge_sources edge_targets : list N)
    (start finish : N) (nodes edges : list N) : Prop :=
  walk edge_sources edge_targets nodes edges /\
  hd_error nodes = Some start /\ last nodes start = finish
    /\ NoDup nodes.

(** The sum of the weights of the listed path edges. *)
Fixpoint path_weight (edge_weights edges : list N) : N :=
  match edges with
  | [] => 0
  | edge :: rest => get edge_weights edge + path_weight edge_weights rest
  end.

(** The sum of path edge weights plus the product of the penalties at [start] and
    [finish]. *)
Definition cost (penalties edge_weights : list N)
  (start finish : N)
    (edges : list N) : N :=
  path_weight edge_weights edges
  + penalty penalties start * penalty penalties finish.

(** [best] is the minimum cost of any simple path beginning at [start]. *)
Definition min_cost (penalties edge_sources edge_targets
  edge_weights : list N)
    (start best : N) : Prop :=
  (exists finish nodes edges,
     simple_path edge_sources edge_targets start finish
       nodes edges /\
     cost penalties edge_weights start finish edges = best)
       /\
  (forall finish nodes edges,
     simple_path edge_sources edge_targets start finish
       nodes edges ->
     best <= cost penalties edge_weights start finish
       edges).

(** The sum of [term] over one-based vertex indices from one through [count]. *)
Fixpoint sum_nodes (term : N -> N) (count : nat) : N :=
  match count with
  | O => 0
  | S count' => sum_nodes term count' + term (N.of_nat
    count)
  end.

(** [@inside yatp_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (penalties edge_sources edge_targets
  edge_weights : list N )
    : Prop := {
  (* 1 <= n <= 2 * 10^5, the number of nodes; n penalties *)
  vi_n : 1 <= len penalties <= 200000;
  (* 1 <= p <= 10^6, the penalty of each node *)
  vi_p : Forall (fun value => 1 <= value <= 1000000)
    penalties;
  (* n - 1 lines, each "i j w" *)
  vi_m : len edge_sources = len penalties - 1;
  vi_ev : len edge_targets = len edge_sources;
  vi_ew : len edge_weights = len edge_sources;
  (* 1 <= i <= n, 1 <= j <= n *)
  vi_i : Forall (fun node => 1 <= node <= len penalties)
    edge_sources;
  vi_j : Forall (fun node => 1 <= node <= len penalties)
    edge_targets;
  (* i <> j *)
  vi_ij : forall k, k < len edge_sources ->
    get edge_sources k <> get edge_targets k;
  (* 1 <= w <= 10^6 *)
  vi_w : Forall (fun weight => 1 <= weight <= 1000000)
    edge_weights;
  (* "You are given a tree" : n - 1 edges joining every
     two nodes *)
  vi_tree : forall node other,
    1 <= node <= len penalties -> 1 <= other <= len
      penalties ->
    exists nodes edges, walk edge_sources edge_targets nodes
      edges /\
      hd_error nodes = Some node /\ last nodes node = other;
}.

(** ** Correctness *)

(** [@requirement]
    The output sums, over all starting vertices, the minimum of path distance plus the
    product of endpoint penalties. *)
Definition yatp_spec
  (penalties edge_sources edge_targets edge_weights : list N
    )
  (output : N)
  : Prop :=
  exists best_cost : N -> N,
    (forall node, 1 <= node <= len penalties ->
       min_cost penalties edge_sources edge_targets
         edge_weights node
         (best_cost node)) /\
    output = sum_nodes best_cost (List.length penalties).

(** ** Interface *)

(** For each vertex u of a weighted tree, minimize distance(u, v) + penalty(u) * penalty(v)
    over all vertices v, then sum these minimum costs.
    - Input [penalties]: Penalty assigned to each vertex.
    - Input [edge_sources]: First endpoint of each tree edge.
    - Input [edge_targets]: Second endpoint of each tree edge.
    - Input [edge_weights]: Length of each corresponding edge.
    - Output [output]: The output sums, over all starting vertices, the minimum of path distance plus the product of endpoint penalties. *)
Program yatp : array uint -> array uint -> array uint ->
  array uint -> uint.

(** [@example yatp]
    - Sample: 1
    - Input [penalties]: [9; 7; 1; 1; 9]
    - Input [edge_sources]: [3; 5; 4; 2]
    - Input [edge_targets]: [2; 2; 3; 1]
    - Input [edge_weights]: [8; 10; 10; 2]
    - Output [output]: 63
*)

(** ** Bridge *)

(** [@requirement yatp_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [yatp_spec]. *)
Specification yatp_correct :
  forall (penalties edge_sources edge_targets edge_weights :
    list N )
         (penalties_arr edge_sources_arr : array uint)
         (edge_targets_arr edge_weights_arr : array uint),
  valid_input penalties edge_sources edge_targets
    edge_weights ->
  repr penalties_arr penalties -> repr edge_sources_arr
    edge_sources ->
  repr edge_targets_arr edge_targets -> repr
    edge_weights_arr edge_weights ->
  exists output : N,
    repr (yatp penalties_arr edge_sources_arr
      edge_targets_arr
            edge_weights_arr) output /\
    yatp_spec penalties edge_sources edge_targets
      edge_weights output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
