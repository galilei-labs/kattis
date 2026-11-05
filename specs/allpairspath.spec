(* @function        allpairspath
   @signature       uint -> array uint -> array uint -> array sint
                    -> array (array (answer sint))
   @math_signature  N -> list N -> list N -> list Z -> list (list (answer Z))
   @summary         [allpairspath n us vs ws] returns, for every pair of
                    vertices (u, v) of the directed graph on the vertices
                    0 .. n - 1 with the edges us[k] -> vs[k] of weight
                    ws[k], the answer at row u, column v : Distance the
                    least cost of a walk from u to v when it exists,
                    Impossible when no walk reaches v from u, NegInfinity
                    when walks from u to v have arbitrarily low costs
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* The answer for one pair of vertices, on both sides : A is sint on the
   machine side, Z on the math side. *)
Inductive answer (A : Type) : Type :=
  | Impossible : answer A
  | NegInfinity : answer A
  | Distance : A -> answer A.
Arguments Impossible {A}.
Arguments NegInfinity {A}.
Arguments Distance {A} _.

(* A machine answer represents a math answer : the same case, and a
   represented distance. *)
Instance repr_answer A M `{Repr A M} : Repr (answer A) (answer M) :=
  fun x i => match x, i with
             | Impossible, Impossible => True
             | NegInfinity, NegInfinity => True
             | Distance a, Distance m => repr a m
             | _, _ => False
             end.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0, Impossible, or [] outside :
   never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0%N.
Definition get_list_Z (l : list Z) (k : N) : Z := nth (N.to_nat k) l 0.
Definition get_list_answer (l : list (answer Z)) (k : N) : answer Z :=
  nth (N.to_nat k) l Impossible.
Definition get_list_row (m : list (list (answer Z))) (u : N) : list (answer Z) :=
  nth (N.to_nat u) m [].

(* v is in [0, n - 1]. *)
Definition vertex (n v : N) : Prop := (v < n)%N.

(* k is in [0, m - 1]. *)
Definition edge_index (us : list N) (k : N) : Prop := (k < len us)%N.

(* There is an edge from u to v of weight w. *)
Definition edge (us vs : list N) (ws : list Z) (u v : N) (w : Z) : Prop :=
  exists k, edge_index us k /\
    get_list_N us k = u /\ get_list_N vs k = v /\ get_list_Z ws k = w.

(* walk u v c : there is a walk from u to v of total cost c (vertices and
   edges may repeat). *)
Inductive walk (us vs : list N) (ws : list Z) (u : N) : N -> Z -> Prop :=
  | walk_refl :
      walk us vs ws u u 0
  | walk_step : forall v v' w c,
      walk us vs ws u v c ->
      edge us vs ws v v' w ->
      walk us vs ws u v' (c + w).

Definition reachable (us vs : list N) (ws : list Z) (u v : N) : Prop :=
  exists c, walk us vs ws u v c.

(* d is the cost of a walk from u to v and no walk from u to v costs
   less. *)
Definition shortest_distance (us vs : list N) (ws : list Z) (u v : N) (d : Z)
  : Prop :=
  walk us vs ws u v d /\
  forall c, walk us vs ws u v c -> d <= c.

(* Walks from u to v cost less than any bound. *)
Definition arbitrarily_short (us vs : list N) (ws : list Z) (u v : N) : Prop :=
  forall lo, exists c, walk us vs ws u v c /\ c < lo.

(* The statement's bounds, for one test case. *)
Record valid_input (n : N) (us vs : list N) (ws : list Z) : Prop := {
  (* 1 <= n <= 150 *)
  vi_n : (1 <= n <= 150)%N;
  (* 0 <= m <= 5000 *)
  vi_m : (len us <= 5000)%N;
  (* one pair of endpoints and one weight per edge *)
  vi_vs_length : len vs = len us;
  vi_ws_length : len ws = len us;
  (* endpoints are vertices *)
  vi_endpoints : forall k, edge_index us k ->
    vertex n (get_list_N us k) /\ vertex n (get_list_N vs k);
  (* -1000 <= w <= 1000 *)
  vi_weights : Forall (fun w => - 1000 <= w <= 1000) ws;
}.

(* The answer for the pair (u, v) : the shortest distance when there is
   one, Impossible when v is not reachable from u, NegInfinity when the
   walks from u to v have arbitrarily low costs.  Exactly one case holds. *)
Definition answer_of (us vs : list N) (ws : list Z) (u v : N) (a : answer Z)
  : Prop :=
  match a with
  | Impossible => ~ reachable us vs ws u v
  | NegInfinity => arbitrarily_short us vs ws u v
  | Distance d => shortest_distance us vs ws u v d
  end.

(* n rows of n answers, the one at row u, column v being for the pair
   (u, v). *)
Definition allpairspath_spec (n : N) (us vs : list N) (ws : list Z)
                               (m : list (list (answer Z))) : Prop :=
  len m = n /\
  forall u, vertex n u ->
    len (get_list_row m u) = n /\
    forall v, vertex n v ->
      answer_of us vs ws u v (get_list_answer (get_list_row m u) v).

(* machine side : the only thing that gets extracted *)
Program allpairspath : uint -> array uint -> array uint -> array sint ->
                           array (array (answer sint)).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification allpairspath_correct :
  forall (n : N) (us vs : list N) (ws : list Z)
         (xn : uint) (xu xv : array uint) (xw : array sint),
  valid_input n us vs ws ->
  repr xn n -> repr xu us -> repr xv vs -> repr xw ws ->
  exists m : list (list (answer Z)),
    repr (allpairspath xn xu xv xw) m /\ allpairspath_spec n us vs ws m.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
