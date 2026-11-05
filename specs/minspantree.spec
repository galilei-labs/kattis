(* @function        mst
   @signature       uint -> array uint -> array uint -> array sint
                    -> option (sint * array uint)
   @math_signature  N -> list N -> list N -> list Z -> option (Z * list N)
   @summary         [mst n us vs ws] returns a minimum spanning tree of the
                    undirected graph on the vertices 0 .. n - 1 with the
                    edges (us[k], vs[k]) of weight ws[k], as its total
                    weight and the indices of its edges, or None when the
                    graph is not connected ; any minimum spanning tree when
                    several exist
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.
Definition get_list_Z (l : list Z) (k : N) : Z := nth (N.to_nat k) l 0%Z.

(* v is in [0, n - 1]. *)
Definition vertex (n v : N) : Prop := v < n.

(* k is in [0, m - 1]. *)
Definition edge_index (us : list N) (k : N) : Prop := k < len us.

(* Edge k joins a and b. *)
Definition joins (us vs : list N) (k a b : N) : Prop :=
  (get_list_N us k = a /\ get_list_N vs k = b) \/
  (get_list_N us k = b /\ get_list_N vs k = a).

(* linked sel a b : a and b are connected by edges satisfying sel. *)
Inductive linked (us vs : list N) (sel : N -> Prop) (a : N) : N -> Prop :=
  | linked_here : linked us vs sel a a
  | linked_hop : forall b k c,
      linked us vs sel a b ->
      edge_index us k -> sel k -> joins us vs k b c ->
      linked us vs sel a c.

Definition every_edge : N -> Prop := fun _ => True.

Definition graph_connected (n : N) (us vs : list N) : Prop :=
  forall u v, vertex n u -> vertex n v -> linked us vs every_edge u v.

(* t lists edge indices. *)
Definition tree_edges (us : list N) (t : list N) : Prop :=
  Forall (edge_index us) t.

Definition tree_distinct (t : list N) : Prop := NoDup t.

Definition tree_size (n : N) (t : list N) : Prop := len t = n - 1.

(* The edges of t connect all the vertices. *)
Definition tree_spans (n : N) (us vs : list N) (t : list N) : Prop :=
  forall u v, vertex n u -> vertex n v -> linked us vs (fun k => In k t) u v.

(* t is a spanning tree : n - 1 distinct edges connecting all vertices. *)
Record spanning_tree (n : N) (us vs : list N) (t : list N) : Prop := {
  st_edges : tree_edges us t;
  st_distinct : tree_distinct t;
  st_size : tree_size n t;
  st_spans : tree_spans n us vs t;
}.

(* The sum of the weights of the edges of t. *)
Fixpoint total_weight (ws : list Z) (t : list N) : Z :=
  match t with
  | [] => 0%Z
  | k :: t' => (get_list_Z ws k + total_weight ws t')%Z
  end.

(* The statement's bounds, for one test case. *)
Record valid_input (n : N) (us vs : list N) (ws : list Z) : Prop := {
  (* 1 <= n <= 20000 *)
  vi_n : 1 <= n <= 20000;
  (* 0 <= m <= 30000 *)
  vi_m : len us <= 30000;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len vs = len us;
  vi_ws_length : len ws = len us;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index us k ->
    vertex n (get_list_N us k) /\ vertex n (get_list_N vs k);
  (* -20000 <= w <= 20000 *)
  vi_weights : Forall (fun w => (- 20000 <= w <= 20000)%Z) ws;
}.

(* t is a spanning tree of total weight c and no spanning tree weighs
   less. *)
Definition minimum_spanning_tree (n : N) (us vs : list N) (ws : list Z)
                                 (c : Z) (t : list N) : Prop :=
  spanning_tree n us vs t /\
  c = total_weight ws t /\
  forall t', spanning_tree n us vs t' ->
    (total_weight ws t <= total_weight ws t')%Z.

(* The result is None exactly when the graph is not connected, and
   otherwise a minimum spanning tree with its weight. *)
Definition mst_spec (n : N) (us vs : list N) (ws : list Z)
                    (r : option (Z * list N)) : Prop :=
  match r with
  | None => ~ graph_connected n us vs
  | Some (c, t) => minimum_spanning_tree n us vs ws c t
  end.

(* machine side : the only thing that gets extracted *)
Program mst : uint -> array uint -> array uint -> array sint ->
                option (sint * array uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification mst_correct :
  forall (n : N) (us vs : list N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists r : option (Z * list N),
    repr (mst xn xu xv xw) r /\ mst_spec n us vs ws r.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
