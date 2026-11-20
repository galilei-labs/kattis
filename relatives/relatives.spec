(** * Relatives *)

(** ** Description *)

(** Count the positive integers smaller than $n$ that are relatively prime to
    $n$.

    [@kattis relatives]
    - Difficulty: 2.7
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le n \le 10^{9}$. *)

(** ** Examples *)

(** - Input convention: One positive integer per case; a zero ends input.
    - Output convention: One count of smaller positive coprime integers per case. *)
(* Input:
7
12
0
Output:
6
4
*)

(** ** [@hide] Environment *)

(* @function        relatives
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [relatives number] is the number of integers
                    candidate, 1 <= candidate < number, that are relatively
                    prime to number, in the statement's sense: no integer
                    common_factor >= 2 divides both. One test case per
                    call; number = 1 gives 0.
                    It runs in at most c1 * (sqrt n + log2 n + 1) + c2 steps
                    of the cost model, for two constants c1, c2.
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

(** The two integers have no common integer divisor greater than one. *)
Definition relatively_prime (first second : N) : Prop :=
  ~ exists common_factor first_cofactor second_cofactor,
      2 <= common_factor /\ 1 <= first_cofactor /\ 1 <=
        second_cofactor /\
      first = common_factor * first_cofactor /\
      second = common_factor * second_cofactor.

(** [candidate] is a positive integer smaller than [number] and relatively prime
    to [number]. *)
Definition relative (number candidate : N) : Prop :=
  1 <= candidate < number /\ relatively_prime candidate
    number.

(** Exactly [count] distinct natural numbers satisfy [property]. *)
Definition count_of (property : N -> Prop) (count : N) :
  Prop :=
  exists members : list N,
    NoDup members /\
    (forall candidate, In candidate members <-> property
      candidate) /\
    len members = count.

(** [@inside relatives_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (number : N) : Prop := {
  (* a line with 1 <= n <= 10^9 *)
  vi_n : 1 <= number <= 10^9;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts positive integers smaller than the input that are coprime to it. *)
Definition relatives_spec
  (number : N)
  (output : N)
  : Prop :=
  count_of (relative number) output.

(** ** Complexity *)

(** [@requirement] Runs in $O(\sqrt{N}+\log(N+2))$ steps, where $N$ is the input number. *)
Definition relatives_time_spec (c1 c2 n_number steps : nat) : Prop :=
  (steps <= c1 * (Nat.sqrt (n_number) + Nat.log2 (n_number) + 1) + c2)%nat.

(** ** Interface *)

(** Count the positive integers smaller than [number] that are relatively prime
    to [number]. The count is zero when [number] is one.
    - Input [number]: Positive integer against which coprimality is tested.
    - Output [output]: The output counts positive integers smaller than the input that are coprime to it. *)
Program relatives : uint -> uint.

(** [@example relatives]
    - Sample: 1
    - Case: 1
    - Input [number]: 7
    - Output [output]: 6
*)

(** [@example relatives]
    - Sample: 1
    - Case: 2
    - Input [number]: 12
    - Output [output]: 4
*)

(** ** Bridge *)

(** [@requirement relatives_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [relatives_spec]. *)
Specification relatives_correct : forall (number : N)
  (number_int : uint),
  valid_input number -> repr number_int number ->
  exists output : N,
    repr (relatives number_int) output /\
    relatives_spec number output.

(** ** Complexity *)

(** [@hide] [relatives_cost] is the cost translation of [relatives] (the judge
    recomputes it and compares) ... *)
Complexity relatives_cost for relatives.

(** [@fold complexity bound] ... and runs in at most c1 * (sqrt n + log2 n + 1) + c2 steps of the cost model, for two constants
    quantified before the input. [@requirement relatives_time_spec] *)
Specification relatives_time : exists c1 c2 : nat, forall number_int : uint,
  relatives_time_spec c1 c2 (size number_int) (cost1 relatives_cost number_int).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
