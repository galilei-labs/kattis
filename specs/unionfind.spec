(* @function        run_ops
   @signature       uint -> array bool -> array uint -> array uint
                    -> array bool
   @math_signature  N -> list bool -> list N -> list N -> list bool
   @summary         [run_ops n is_union elt_a elt_b] returns one boolean
                    per operation k on the elements 0 .. n - 1, initially
                    each in its own set : when is_union[k] is true the sets
                    of elt_a[k] and elt_b[k] are joined and the boolean is
                    unspecified, when it is false the boolean says whether
                    elt_a[k] and elt_b[k] are in the same set at that point
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Operation k is is_union[k] (true : union, false : query)
   on the elements elt_a[k] and elt_b[k]. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0, or false, outside : never
   relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.
Definition get_list_bool (l : list bool) (k : N) : bool :=
  nth (N.to_nat k) l false.

(* Operation k is a union. *)
Definition union_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = true.

(* Operation k is a query. *)
Definition query_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = false.

(* a and b are in the same set after the unions among the first k
   operations. *)
Inductive connected (is_union : list bool) (elt_a elt_b : list N) (k : N)
  : N -> N -> Prop :=
  | conn_refl : forall a,
      connected is_union elt_a elt_b k a a
  | conn_union : forall m,
      m < k ->
      union_op is_union m ->
      connected is_union elt_a elt_b k (get_list_N elt_a m) (get_list_N elt_b m)
  | conn_sym : forall a b,
      connected is_union elt_a elt_b k a b ->
      connected is_union elt_a elt_b k b a
  | conn_trans : forall a b c,
      connected is_union elt_a elt_b k a b ->
      connected is_union elt_a elt_b k b c ->
      connected is_union elt_a elt_b k a c.

(* The statement's bounds. *)
Record valid_input (n : N) (is_union : list bool) (elt_a elt_b : list N)
  : Prop := {
  (* 1 <= N <= 10^6 *)
  vi_n : 1 <= n <= 10 ^ 6;
  (* 0 <= Q <= 10^6 *)
  vi_q : len is_union <= 10 ^ 6;
  (* one pair of elements per operation *)
  vi_a_length : len elt_a = len is_union;
  vi_b_length : len elt_b = len is_union;
  (* a and b are integers between 0 and N - 1.  The statement says
     "distinct", but its second sample asks "? 0 0" : a = b is a valid
     input and is not assumed away (a query on a = b answers true by
     conn_refl, a union on a = b changes nothing). *)
  vi_a_range : forall k, k < len is_union -> get_list_N elt_a k < n;
  vi_b_range : forall k, k < len is_union -> get_list_N elt_b k < n;
}.

(* At query k, the answer is true exactly when the earlier unions connect
   its two elements. *)
Definition answers_query (is_union : list bool) (elt_a elt_b : list N)
                         (out : list bool) (k : N) : Prop :=
  get_list_bool out k = true
  <-> connected is_union elt_a elt_b k (get_list_N elt_a k) (get_list_N elt_b k).

(* One answer per operation ; only the answers at queries are specified. *)
Definition run_ops_spec (n : N) (is_union : list bool) (elt_a elt_b : list N)
                        (out : list bool) : Prop :=
  len out = len is_union /\
  forall k, k < len is_union -> query_op is_union k ->
    answers_query is_union elt_a elt_b out k.

(* machine side : the only thing that gets extracted *)
Program run_ops : uint -> array bool -> array uint -> array uint ->
                    array bool.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification run_ops_correct :
  forall (n : N) (is_union : list bool) (elt_a elt_b : list N)
         (xn : uint) (xu : array bool) (xa xb : array uint),
  valid_input n is_union elt_a elt_b ->
  repr xn n -> repr xu is_union -> repr xa elt_a -> repr xb elt_b ->
  exists out : list bool,
    repr (run_ops xn xu xa xb) out /\ run_ops_spec n is_union elt_a elt_b out.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
