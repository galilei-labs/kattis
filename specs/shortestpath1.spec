(* @function        dijkstra
   @signature       uint -> array uint -> array uint -> array uint -> uint
                    -> array (option uint)
   @math_signature  N -> list N -> list N -> list N -> N -> list (option N)
   @summary         [dijkstra n us vs ws s] returns, for every vertex v of
                    the directed graph on the vertices 0 .. n - 1 with the
                    edges us[k] -> vs[k] of weight ws[k], Some the least
                    cost of a path from s to v, or None when there is no
                    such path
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0, or None, outside : never
   relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.
Definition get_list_option (l : list (option N)) (k : N) : option N :=
  nth (N.to_nat k) l None.

(* v is in [0, n - 1]. *)
Definition vertex (n v : N) : Prop := v < n.

(* k is in [0, m - 1]. *)
Definition edge_index (us : list N) (k : N) : Prop := k < len us.

(* There is an edge from u to v of weight w. *)
Definition edge (us vs ws : list N) (u v w : N) : Prop :=
  exists k, edge_index us k /\
    get_list_N us k = u /\ get_list_N vs k = v /\ get_list_N ws k = w.

(* path s v c : there is a path from s to v of total weight c. *)
Inductive path (us vs ws : list N) (s : N) : N -> N -> Prop :=
  | path_refl :
      path us vs ws s s 0
  | path_step : forall u v w c,
      path us vs ws s u c ->
      edge us vs ws u v w ->
      path us vs ws s v (c + w).

Definition reachable (us vs ws : list N) (s v : N) : Prop :=
  exists c, path us vs ws s v c.

(* c is the cost of a path from s to v and no path from s to v costs
   less. *)
Definition shortest_distance (us vs ws : list N) (s v c : N) : Prop :=
  path us vs ws s v c /\
  forall c', path us vs ws s v c' -> c <= c'.

(* The statement's bounds, for one test case. *)
Record valid_input (n : N) (us vs ws : list N) (s : N) : Prop := {
  (* 1 <= n <= 10000 *)
  vi_n : 1 <= n <= 10 ^ 4;
  (* 0 <= m <= 30000 *)
  vi_m : len us <= 3 * 10 ^ 4;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len vs = len us;
  vi_ws_length : len ws = len us;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index us k ->
    vertex n (get_list_N us k) /\ vertex n (get_list_N vs k);
  (* 0 <= w <= 1000 *)
  vi_weights : Forall (fun w => w <= 1000) ws;
  (* 0 <= s < n *)
  vi_source : vertex n s;
}.

(* The entry for v : Some the shortest distance from s when a path
   reaches v, None otherwise. *)
Definition distance_of (us vs ws : list N) (s v : N) (o : option N) : Prop :=
  match o with
  | Some c => shortest_distance us vs ws s v c
  | None => ~ reachable us vs ws s v
  end.

(* The result has one entry per vertex. *)
Definition dijkstra_spec (n : N) (us vs ws : list N) (s : N)
                         (d : list (option N)) : Prop :=
  len d = n /\
  forall v, vertex n v -> distance_of us vs ws s v (get_list_option d v).

(* machine side : the only thing that gets extracted *)
Program dijkstra : uint -> array uint -> array uint -> array uint ->
                     uint -> array (option uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification dijkstra_correct :
  forall (n : N) (us vs ws : list N) (s : N)
         (xn : uint) (xu xv xw : array uint) (xs : uint),
  valid_input n us vs ws s ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws -> repr xs s ->
  exists d : list (option N),
    repr (dijkstra xn xu xv xw xs) d /\ dijkstra_spec n us vs ws s d.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
