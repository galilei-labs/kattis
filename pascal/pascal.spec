(** * Pascal *)

(** ** Description *)

(** Starting at n - 1 and counting downward, stop at the first divisor of n.
    Return the number of candidate integers examined.

    [@kattis pascal]
    - Difficulty: 3.5
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - $1 \le n \le 10^9$. *)

(** ** Examples *)

(** - Input convention: A single positive integer n.
    - Output convention: The number of descending divisor candidates examined. *)
(* Input:
1
Output:
0
*)

(** ** [@hide] Environment *)
(* @function        pascal
   @signature       uint -> uint
   @math_signature  N -> N
   @summary         [pascal number] is what Frane's Pascal program prints on
                    input number: the counter after the loop "for i :=
                    number-1 downto 1, add one to the counter, stop as soon
                    as number mod i = 0".
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. Frane's program, line by line: readln(N); counter := 0;
    for i := N - 1 downto 1 do begin counter := counter + 1; if N
    mod i = 0 then break; end; writeln(counter); [frane_loop number
    divisor counter]: the loop run from the current value [divisor]
    of the loop variable i down to 1, the counter being [counter] on
    entry; it returns the counter on exit (after the break, or after
    i = 1). *)
Fixpoint frane_loop (number : N) (divisor : nat)
  (counter : N) : N :=
  match divisor with
  | O => counter
  | S smaller =>
      let counter' := counter + 1 in
      if number mod N.of_nat divisor =? 0 then counter'
      else frane_loop number smaller counter'
  end.

(** readln(N); counter := 0; the loop from N - 1; writeln(counter). *)
Definition frane_output (number : N) : N :=
  frane_loop number (N.to_nat (number - 1)) 0.

(** [@inside pascal_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (number : N) : Prop := {
  (* The first and only line of input contains the
     integer 1 <= N <= 10^9. *)
  vi_n : 1 <= number <= 10 ^ 9;
}.

(** ** Correctness *)

(** [@requirement]
    The output counts descending candidate divisors from n - 1 through the first divisor
    of n; for n = 1, it is zero. *)
Definition pascal_spec (number : N) (output : N) : Prop :=
  output = frane_output number.

(** ** Interface *)

(** Starting at n - 1 and counting downward, stop at the first divisor of n. Return the
    number of candidate integers examined.
    - Input [number]: Positive integer whose descending divisor search is counted.
    - Output [output]: The output counts descending candidate divisors from n - 1 through the first divisor of n; for n = 1, it is zero. *)
Program pascal : uint -> uint.

(** ** Bridge *)

(** [@requirement pascal_spec] [@fold full correctness statement] On
    valid represented inputs, [pascal] returns a represented output
    satisfying [pascal_spec]. *)
Specification pascal_correct : forall (number : N)
  (number_int : uint),
  valid_input number -> repr number_int number ->
  exists output : N,
    repr (pascal number_int) output /\ pascal_spec number
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
