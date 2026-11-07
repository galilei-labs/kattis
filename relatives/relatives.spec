(* @function        relatives
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [relatives number] is the number of integers
                    candidate, 1 <= candidate < number, that are relatively
                    prime to number, in the statement's sense: no integer
                    common_factor >= 2 divides both. One test case per
                    call; number = 1 gives 0.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The statement's definition: first and second are relatively prime when
   there are no integers common_factor >= 2, first_cofactor >= 1,
   second_cofactor >= 1 such that first = common_factor * first_cofactor
   and second = common_factor * second_cofactor (all three are positive,
   so they range over N). *)
Definition relatively_prime (first second : N) : Prop :=
  ~ exists common_factor first_cofactor second_cofactor,
      2 <= common_factor /\ 1 <= first_cofactor /\ 1 <= second_cofactor /\
      first = common_factor * first_cofactor /\
      second = common_factor * second_cofactor.

(* candidate is counted for number: a positive integer less than number,
   relatively prime to number. *)
Definition relative (number candidate : N) : Prop :=
  1 <= candidate < number /\ relatively_prime candidate number.

(* count is the number of naturals satisfying property: property holds of
   exactly the members of a duplicate-free list of length count. *)
Definition count_of (property : N -> Prop) (count : N) : Prop :=
  exists members : list N,
    NoDup members /\
    (forall candidate, In candidate members <-> property candidate) /\
    len members = count.

(* The statement's bounds, for one test case. *)
Record valid_input (number : N) : Prop := {
  (* a line with 1 <= n <= 1 000 000 000 *)
  vi_n : 1 <= number <= 10^9;
}.

(* The answer: how many positive integers less than number are relatively
   prime to number. *)
Definition relatives_spec (number : N) (output : N) : Prop :=
  count_of (relative number) output.

Program relatives : uint -> uint.

Specification relatives_correct : forall (number : N) (number_int : uint),
  valid_input number -> repr number_int number ->
  exists output : N,
    repr (relatives number_int) output /\
    relatives_spec number output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
