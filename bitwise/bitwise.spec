(** * Bitwise *)

(** ** Description *)

(** Partition a circular sequence into a specified number of nonempty
    contiguous sections. Maximize the bitwise AND of the sections' bitwise
    ORs.

    [@kattis bitwise]
    - Difficulty: 6.2
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Section count $k$ and sequence length $n$: $1 \le k \le n \le 5 \times 10^{5}$.
    - Entries: $0 \le a_i \le 10^{9}$. *)

(** ** Examples *)

(** - Input convention: Sequence length and partition count, followed by the circular sequence values.
    - Output convention: A single integer giving the maximum AND of the section ORs. *)
(* Input:
4 2
2 3 4 1
Output:
3
*)

(** ** [@hide] Environment *)

(* @function        best_and
   @signature       uint -> array uint -> uint
   @math_signature  N -> list N -> N
   @summary         [best_and section_count integers] returns the greatest
                    bitwise AND of the bitwise ORs of the sections, over the
                    divisions of the circle integers into section_count
                    contiguous non-empty sections
                    It runs in at most c1 * (n + 1) + c2 steps of the cost
                    model on a valid input, n the number of integers (a
                    fixed number of candidate bits, each tested by a
                    constant number of passes over the unrolled circle), for
                    two constants c1, c2.
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

(** Read the circular list [integers] beginning at the zero-based index [start],
    wrapping at the end. *)
Definition rotate (start : nat)
  (integers : list N) : list N :=
  skipn start integers ++ firstn start integers.

(** Extend [accumulated] by taking the bitwise OR with each remaining integer. *)
Fixpoint power_from (section : list N) (accumulated : N) : N :=
  match section with
  | [] => accumulated
  | integer :: rest => power_from rest (N.lor accumulated integer)
  end.

(** The bitwise OR of the integers in [section]. *)
Definition power (section : list N) : N :=
  power_from section 0.

(** Extend [accumulated] by taking the bitwise AND with each remaining section's power. *)
Fixpoint and_powers_from (sections : list (list N)) (accumulated : N) : N :=
  match sections with
  | [] => accumulated
  | section :: rest => and_powers_from rest (N.land accumulated (power section))
  end.

(** The bitwise AND of the section powers. The empty list yields zero; valid
    divisions always contain at least one section. *)
Definition and_powers (sections : list (list N)) : N :=
  match sections with
  | [] => 0
  | first :: rest =>
      and_powers_from rest (power first)
  end.

(** [sections] partitions the circular list [integers] into [section_count] nonempty
    contiguous sections, beginning at some position on the circle. *)
Definition division (integers : list N) (section_count : N)
  (sections : list (list N)) : Prop :=
  len sections = section_count /\
  Forall (fun section => section <> []) sections /\
  exists start, (start < List.length integers)%nat /\
    concat sections = rotate start integers.

(** [@inside best_and_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (section_count : N)
  (integers : list N) : Prop := {
  (* 1 <= K <= N <= 5 * 10^5 *)
  vi_k : 1 <= section_count <= len integers;
  vi_n : len integers <= 5 * 10 ^ 5;
  (* 0 <= A_i <= 10^9 *)
  vi_values : Forall
    (fun integer => integer <= 10 ^ 9) integers;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the maximum bitwise AND of section ORs over all partitions into the
    requested number of nonempty circular sections. *)
Definition best_and_spec (section_count : N)
  (integers : list N)
  (output : N) : Prop :=
  (exists sections, division integers section_count sections
    /\
     and_powers sections = output) /\
  forall sections, division integers section_count sections
    ->
    and_powers sections <= output.

(** ** Complexity *)

(** [@requirement] Runs in $O(n)$ steps, where $n$ is the number of input integers. *)
Definition best_and_time_spec (c1 c2 n_integers steps : nat) : Prop :=
  (steps <= c1 * (n_integers + 1) + c2)%nat.

(** ** Interface *)

(** Partition a circular sequence into a specified number of nonempty contiguous sections.
    Maximize the bitwise AND of the sections' bitwise ORs.
    - Input [section_count]: Required number of nonempty circular sections.
    - Input [integers]: Values around the circle, in order.
    - Output [output]: The output is the maximum bitwise AND of section ORs over all partitions into the requested number of nonempty circular sections. *)
Program best_and : uint -> array uint -> uint.

(** [@example best_and]
    - Sample: 1
    - Input [section_count]: 2
    - Input [integers]: [2; 3; 4; 1]
    - Output [output]: 3
*)

(** ** Bridge *)

(** [@requirement best_and_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [best_and_spec]. *)
Specification best_and_correct :
  forall (section_count : N) (integers : list N)
         (section_count_int : uint)
           (integers_arr : array uint),
  valid_input section_count integers ->
  repr section_count_int section_count
    -> repr integers_arr integers ->
  exists output : N,
    repr (best_and section_count_int integers_arr) output /\
    best_and_spec section_count integers output.

(** ** Complexity *)

(** [@hide] [best_and_cost] is the cost translation of [best_and] (the judge
    recomputes it and compares) ... *)
Complexity best_and_cost for best_and.

(** [@fold complexity bound] ... and runs in at most c1 * (n + 1) + c2 steps of the cost model on a valid input, n the number of integers (a fixed number of candidate bits, each tested by a constant number of passes over the unrolled circle), for two constants
    quantified before the inputs, on every valid input. [@requirement best_and_time_spec] *)
Specification best_and_time : exists c1 c2 : nat,
  forall (section_count : N) (integers : list N)
  (section_count_int : uint)
  (integers_arr : array uint),
  valid_input section_count integers ->
  repr section_count_int section_count
  -> repr integers_arr integers ->
  best_and_time_spec c1 c2 (size integers_arr) (cost2 best_and_cost section_count_int integers_arr).

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
