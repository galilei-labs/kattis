(** * Union-Find *)

(** ** Description *)

(** Maintain disjoint sets under union operations and answer whether two
    elements belong to the same set.

    [@kattis unionfind]
    - Difficulty: 2.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 1,000,000 elements and 0 to 1,000,000 operations.
    - Element indices from 0 to N - 1. *)

(** ** Examples *)

(** - Input convention: Element and operation counts, followed by = a b unions and ? a b connectivity queries.
    - Output convention: yes or no for each connectivity query, one result per line. *)
(* Input:
10 4
? 1 3
= 1 8
= 3 8
? 1 3
Output:
no
yes
*)

(** ** [@hide] Environment *)

(* @function        run_ops
   @signature       uint -> array bool -> array uint -> array uint
                    -> array bool
   @math_signature  N -> list bool -> list N -> list N -> list bool
   @summary         [run_ops element_count is_union first_elements
                    second_elements] returns one boolean per operation k on
                    the elements 0 .. element_count - 1, initially each in
                    its own set : when is_union[k] is true the sets of
                    first_elements[k] and second_elements[k] are joined and
                    the boolean is unspecified, when it is false the boolean
                    says whether first_elements[k] and second_elements[k]
                    are in the same set at that point
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. Operation k is is_union[k] (true : union,
   false : query) on the elements first_elements[k] and
   second_elements[k]. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The k-th element of l, for k < [len] l (0, or false,
    outside : never relied on). *)
Definition get_list_N (l : list N ) (k : N) : N := nth
  (N.to_nat k) l 0.
(** Get list bool. *)
Definition get_list_bool (l : list bool) (k : N) : bool :=
  nth (N.to_nat k) l false.

(** Operation k is a union. *)
Definition union_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = true.

(** Operation k is a query. *)
Definition query_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = false.

(** Two elements are in the same set after the unions
    among the first k operations. *)
Inductive connected (is_union : list bool)
  (first_elements second_elements : list N) (k : N) : N -> N
    -> Prop :=
  | conn_refl : forall element,
      connected is_union first_elements second_elements k
        element element
  | conn_union : forall m,
      m < k ->
      union_op is_union m ->
      connected is_union first_elements second_elements k
        (get_list_N first_elements m)
          (get_list_N second_elements m)
  | conn_sym : forall element other,
      connected is_union first_elements second_elements k
        element other ->
      connected is_union first_elements second_elements k
        other element
  | conn_trans : forall element middle other,
      connected is_union first_elements second_elements k
        element middle ->
      connected is_union first_elements second_elements k
        middle other ->
      connected is_union first_elements second_elements k
        element other.

(** [@inside run_ops_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (element_count : N)
  (is_union : list bool)
  (first_elements second_elements : list N) : Prop := {
  (* 1 <= N <= 10^6 *)
  vi_n : 1 <= element_count <= 10 ^ 6;
  (* 0 <= Q <= 10^6 *)
  vi_q : len is_union <= 10 ^ 6;
  (* one pair of elements per operation *)
  vi_a_length : len first_elements = len is_union;
  vi_b_length : len second_elements = len is_union;
  (* a and b are integers between 0 and N - 1. The
     statement says "distinct" , but its second sample
     asks "? 0 0" : a = b is a valid input and is not
     assumed away (a query on a = b answers true by
     conn_refl, a union on a = b changes nothing). *)
  vi_a_range : forall k, k < len is_union ->
    get_list_N first_elements k < element_count;
  vi_b_range : forall k, k < len is_union ->
    get_list_N second_elements k < element_count;
}.

(** At query k, the answer is true exactly when the
    earlier unions connect its two elements. *)
Definition answers_query (is_union : list bool)
  (first_elements second_elements : list N)
    (answers : list bool) (k : N)
  : Prop :=
  get_list_bool answers k = true
  <-> connected is_union first_elements second_elements k
        (get_list_N first_elements k)
          (get_list_N second_elements k).

(** ** Correctness *)

(** [@requirement]
    The output has one entry per operation; entries corresponding to queries indicate
    whether the queried elements are connected after the preceding unions. *)
Definition run_ops_spec
  (element_count : N)
  (is_union : list bool)
  (first_elements second_elements : list N)
  (output : list bool)
  : Prop :=
  len output = len is_union /\
  forall k, k < len is_union -> query_op is_union k ->
    answers_query is_union first_elements second_elements
      output k.

(** ** Interface *)

(** Maintain disjoint sets under union operations and answer whether two elements belong to
    the same set.
    - Input [element_count]:
    - Input [is_union]:
    - Input [first_elements]:
    - Input [second_elements]:
    - Output [output]: *)
Program run_ops : uint -> array bool -> array uint -> array
  uint ->
                    array bool.

(** ** Bridge *)

(** [@requirement run_ops_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [run_ops_spec]. *)
Specification run_ops_correct :
  forall (element_count : N) (is_union : list bool)
         (first_elements second_elements : list N)
         (element_count_int : uint)
           (is_union_arr : array bool)
         (first_elements_arr second_elements_arr : array
        uint)
           ,
  valid_input element_count is_union first_elements
    second_elements ->
  repr element_count_int element_count -> repr is_union_arr
    is_union ->
  repr first_elements_arr first_elements ->
  repr second_elements_arr second_elements ->
  exists output : list bool,
    repr (run_ops element_count_int is_union_arr
      first_elements_arr
            second_elements_arr) output /\
    run_ops_spec element_count is_union first_elements
      second_elements
      output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
