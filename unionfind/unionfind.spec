(** * Union-Find *)

(** ** Description *)

(** Maintain disjoint sets under union operations and answer whether two
    elements belong to the same set.

    [@kattis unionfind]
    - Difficulty: 2.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Element count: $1 \le N \le 10^{6}$; operation count: $0 \le Q \le 10^{6}$.
    - Element indices: $0 \le i < N$. *)

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
                     second_elements] processes operations on the elements
                     0 .. element_count - 1, initially each in its own set.
                     When is_union[k] is true the sets of first_elements[k]
                     and second_elements[k] are joined, producing no answer.
                     When it is false, append a boolean saying whether those
                     elements are in the same set at that point. Returns one
                     boolean per query, in query order.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Operation k is is_union[k] (true : union,
   false : query) on the elements first_elements[k] and
   second_elements[k]. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [k] in [l], or zero beyond the end. *)
Definition get_list_N (l : list N ) (k : N) : N := nth
  (N.to_nat k) l 0.
(** The Boolean at zero-based index [k] in [l], or [false] beyond the end. *)
Definition get_list_bool (l : list bool) (k : N) : bool :=
  nth (N.to_nat k) l false.

(** The operation at zero-based index [k] is a union. *)
Definition union_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = true.

(** The operation at zero-based index [k] is a query. *)
Definition query_op (is_union : list bool) (k : N) : Prop :=
  get_list_bool is_union k = false.

(** [connected is_union first_elements second_elements k element other] means
    that [element] and [other] are in the same set after the unions among the first
    [k] operations. The three parallel lists give the operation kinds and their
    two element arguments. *)
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

(** Number of query operations in [ops]; [false] denotes a query. *)
Definition query_count (ops : list bool) : N :=
  len (filter negb ops).

(** Output position of a query at operation index [k]: the number of preceding
    queries. *)
Definition query_index (is_union : list bool) (k : N) : N :=
  query_count (firstn (N.to_nat k) is_union).

(** At operation index [k], the corresponding query answer is true exactly when
    earlier unions connect its two elements. *)
Definition answers_query (is_union : list bool)
  (first_elements second_elements : list N)
    (answers : list bool) (k : N)
  : Prop :=
  get_list_bool answers (query_index is_union k) = true
  <-> connected is_union first_elements second_elements k
        (get_list_N first_elements k)
          (get_list_N second_elements k).

(** ** Correctness *)

(** [@requirement]
    The output contains one Boolean per query, in query order. Each answer is true
    exactly when preceding unions connect the queried elements. *)
Definition run_ops_spec
  (element_count : N)
  (is_union : list bool)
  (first_elements second_elements : list N)
  (output : list bool)
  : Prop :=
  len output = query_count is_union /\
  forall k, k < len is_union -> query_op is_union k ->
    answers_query is_union first_elements second_elements
      output k.

(** ** Interface *)

(** Maintain disjoint sets under union operations and answer whether two elements belong to
    the same set. Return answers only for connectivity queries, in query order.
    - Input [element_count]: Number of elements, initially in separate sets.
    - Input [is_union]: Whether each operation joins sets rather than querying connectivity.
    - Input [first_elements]: First element of each operation.
    - Input [second_elements]: Second element of each operation.
    - Output [output]: One Boolean per connectivity query, in query order, reporting whether preceding unions connect its two elements. Union operations produce no output entry. *)
Program run_ops : uint -> array bool -> array uint -> array
  uint ->
                    array bool.

(** [@example run_ops]
    - Sample: 1
    - Input [element_count]: 10
    - Input [is_union]: [false; true; true; false]
    - Input [first_elements]: [1; 1; 3; 1]
    - Input [second_elements]: [3; 8; 8; 3]
    - Output [output]: [false; true]
*)

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
