(** * Binary search tree *)

(** ** Description *)

(** Insert a permutation into an initially empty binary search tree. After
    each insertion, return the sum of all inserted nodes' depths, with root
    depth zero.

    [@kattis bst]
    - Difficulty: 3.4

    **Kattis Bounds**
    - 1 to 300000 entries, forming a permutation of 1 through N. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
4
1
2
3
4
Output:
0
1
3
6
*)

(** ** [@hide] Environment *)

(* @function        bst
   @signature       array uint -> array uint
   @math_signature  list N -> list N
   @summary         The numbers of sequence, a permutation of 1..N, are
                    inserted in order into an initially empty (unbalanced)
                    binary search tree, the first one becoming the root, at
                    depth 0.  [bst sequence] has length N and its cell k is
                    the counter C after the (k+1)-th insertion: the sum of
                    the depths at which sequence_0, ..., sequence_k were
                    placed.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The j-th element of numbers (0-based); 0 beyond the
    end. *)
Definition get (numbers : list N) (j : N) : N :=
  nth (N.to_nat j) numbers 0.

(** A binary tree with a number written inside each
    node. *)
Inductive tree : Type :=
| Leaf : tree
| Node : tree -> N -> tree -> tree.

(** Inserting number: traverse the tree as if searching
    for number, and put number as a new leaf, left of
    key if number < key, right of key if key < number,
    where the search cannot continue. *)
Fixpoint insert (number : N) (subtree : tree) : tree :=
  match subtree with
  | Leaf => Node Leaf number Leaf
  | Node left_tree key right_tree =>
      if number <? key then Node
        (insert number left_tree) key right_tree
      else if key <? number then Node left_tree key
        (insert number right_tree)
      else subtree
  end.

(** The depth of the node holding number: the number of
    edges from the root down to it along the search path
    of number. *)
Fixpoint depth (number : N) (subtree : tree) : N :=
  match subtree with
  | Leaf => 0
  | Node left_tree key right_tree =>
      if number <? key then N.succ (depth number left_tree)
      else if key <? number then N.succ
        (depth number right_tree)
      else 0
  end.

(** The tree built from sequence: the first number at
    the root, every other number inserted in order. *)
Definition tree_of (sequence : list N) : tree :=
  fold_left
    (fun built number => insert number built) sequence Leaf.

(** The depth of sequence_j in the tree right after its
    insertion. *)
Definition placed_depth (sequence : list N) (j : N) : N :=
  depth (get sequence j) (tree_of (firstn
    (N.to_nat j + 1) sequence)).

(** The counter C after the first insertion_count
    insertions: the sum of the depths of sequence_0,
    ..., sequence_(insertion_count-1); C is 0 before any
    insertion. *)
Fixpoint counter (sequence : list N)
  (insertion_count : nat) : N :=
  match insertion_count with
  | O => 0
  | S j => counter sequence j + placed_depth sequence
    (N.of_nat j)
  end.

(** [@inside bst_correct] The statement's bounds. *)
Record valid_input (sequence : list N) : Prop := {
  (* 1 <= N <= 300 000, N the length of the sequence *)
  vi_n : 1 <= len sequence <= 300000;
  (* the numbers of the sequence are integers in the
    interval [1, N] *)
  vi_range : Forall
    (fun number => 1 <= number <= len sequence) sequence;
  (* the numbers will be distinct *)
  vi_distinct : NoDup sequence;
}.

(** ** Correctness *)

(** [@requirement] [@short must return the cumulative
    insertion depths.] One counter per insertion: cell k
    is C after sequence_k has been inserted. *)
Definition bst_spec (sequence : list N)
  (output : list N) : Prop :=
  len output = len sequence /\
  forall k, k < len output ->
    get output k = counter sequence (N.to_nat k + 1).

(** ** Interface *)

(** The machine-level interface.
    - Input [sequence]:
    - Output [output]: *)
Program bst : array uint -> array uint.

(** ** Bridge *)

(** [@requirement bst_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying [bst_spec]. *)
Specification bst_correct :
  forall (sequence : list N) (sequence_arr : array uint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : list N,
    repr (bst sequence_arr) output
      /\ bst_spec sequence output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
