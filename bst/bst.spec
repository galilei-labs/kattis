(** * Binary search tree *)

(** ** Description *)

(** Insert a permutation into an initially empty binary search tree. After
    each insertion, return the sum of all inserted nodes' depths, with root
    depth zero.

    [@kattis bst]
    - Difficulty: 3.4
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Entry count: $1 \le n \le 3 \times 10^{5}$, forming a permutation of the integers $1 \le x \le n$. *)

(** ** Examples *)

(** - Input convention: Sequence length, followed by distinct insertion values, one per line.
    - Output convention: One cumulative node-depth sum after each insertion. *)
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
                    It runs in at most c1 * (N + 1) * (log2 N + 1) + c2
                    steps of the cost model on a valid input, N the number
                    of keys (one red-black insertion and one predecessor and
                    successor search per key, each within the tree's depth,
                    logarithmic by the red-black invariant), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [j] in [numbers], or zero beyond the end. *)
Definition get (numbers : list N) (j : N) : N :=
  nth (N.to_nat j) numbers 0.

(** A binary tree with a number written inside each
    node. *)
Inductive tree : Type :=
| Leaf : tree
| Node : tree -> N -> tree -> tree.

(** Insert [number] as a leaf at the end of its binary-search path: smaller keys go
    left and larger keys go right. An existing equal key is unchanged. *)
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

(** The number of edges from the root to [number] along its binary-search path. *)
Fixpoint depth (number : N) (subtree : tree) : N :=
  match subtree with
  | Leaf => 0
  | Node left_tree key right_tree =>
      if number <? key then N.succ (depth number left_tree)
      else if key <? number then N.succ
        (depth number right_tree)
      else 0
  end.

(** Insert the remaining numbers into [built], in input order. *)
Fixpoint tree_from (sequence : list N) (built : tree) : tree :=
  match sequence with
  | [] => built
  | number :: rest => tree_from rest (insert number built)
  end.

(** The tree built from sequence: the first number at
    the root, every other number inserted in order. *)
Definition tree_of (sequence : list N) : tree :=
  tree_from sequence Leaf.

(** The depth of the entry at index [j], immediately after that entry is inserted. *)
Definition placed_depth (sequence : list N) (j : N) : N :=
  depth (get sequence j) (tree_of (firstn
    (N.to_nat j + 1) sequence)).

(** The sum of insertion depths for the first [insertion_count] entries, with value
    zero before any insertion. *)
Fixpoint counter (sequence : list N)
  (insertion_count : nat) : N :=
  match insertion_count with
  | O => 0
  | S j => counter sequence j + placed_depth sequence
    (N.of_nat j)
  end.

(** [@inside bst_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sequence : list N) : Prop := {
  (* 1 <= N <= 3 * 10^5, N the length of the sequence *)
  vi_n : 1 <= len sequence <= 300000;
  (* the numbers of the sequence are integers in the
    interval [1, N] *)
  vi_range : Forall
    (fun number => 1 <= number <= len sequence) sequence;
  (* the numbers will be distinct *)
  vi_distinct : NoDup sequence;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry is the sum of node depths after the corresponding insertion into
    an initially empty binary search tree; the root has depth zero. *)
Definition bst_spec (sequence : list N)
  (output : list N) : Prop :=
  len output = len sequence /\
  forall k, k < len output ->
    get output k = counter sequence (N.to_nat k + 1).

(** ** Complexity *)

(** [@requirement] Runs in $O(n \log(n+1))$ steps, where $n$ is the sequence length. *)
Definition bst_time_spec (c1 c2 n_sequence steps : nat) : Prop :=
  (steps <= c1 * ((n_sequence + 1) * (Nat.log2 (n_sequence) + 1)) + c2)%nat.

(** ** Interface *)

(** Insert a permutation into an initially empty binary search tree. After each insertion,
    return the sum of all inserted nodes' depths, with root depth zero.
    - Input [sequence]: Distinct values in binary-search-tree insertion order.
    - Output [output]: Each output entry is the sum of node depths after the corresponding insertion into an initially empty binary search tree; the root has depth zero. *)
Program bst : array uint -> array uint.

(** [@example bst]
    - Sample: 1
    - Input [sequence]: [1; 2; 3; 4]
    - Output [output]: [0; 1; 3; 6]
*)

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

(** ** Complexity *)

(** [@hide] [bst_cost] is the cost translation of [bst] (the judge
    recomputes it and compares) ... *)
Complexity bst_cost for bst.

(** [@fold complexity bound] ... and runs in at most c1 * (N + 1) * (log2 N + 1) + c2 steps of the cost model on a valid input, N the number of keys (one red-black insertion and one predecessor and successor search per key, each within the tree's depth, logarithmic by the red-black invariant), for two constants
    quantified before the inputs, on every valid input. [@requirement bst_time_spec] *)
Specification bst_time : exists c1 c2 : nat,
  forall (sequence : list N) (sequence_arr : array uint),
  valid_input sequence -> repr sequence_arr sequence ->
  bst_time_spec c1 c2 (size sequence_arr) (cost1 bst_cost sequence_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
