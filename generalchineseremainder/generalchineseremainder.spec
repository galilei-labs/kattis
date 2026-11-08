(** * Chinese Remainder Theorem (non-relatively prime moduli) *)

(** ** Description *)

(** Solve two modular congruences whose moduli need not be coprime. Return
    the least nonnegative solution and its period, or report that the
    congruences are inconsistent.

    [@kattis generalchineseremainder]
    - Difficulty: 2.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Both moduli are from 1 to $10^{9}$.
    - Each residue is nonnegative and smaller than its modulus. *)

(** ** Examples *)

(** - Input convention: Case count, followed by remainder-modulus pairs a n b m for each case.
    - Output convention: Least nonnegative solution and combined modulus, or no solution if inconsistent. *)
(* Input:
3
10000 23000 9000 23000
10000 23000 10000 23000
1234 2000 746 2002
Output:
no solution
10000 23000
489234 2002000
*)

(** ** [@hide] Environment *)
(* @function        crt
   @signature       uint -> uint -> uint -> uint -> option (uint * uint)
   @math_signature  N -> N -> N -> N -> option (N * N)
   @summary         [crt residue1 modulus1 residue2 modulus2] solves the
                    system x = residue1 (mod modulus1), x = residue2 (mod
                    modulus2) for moduli that need not be coprime.  It
                    returns Some (value, period) with period =
                    lcm(modulus1, modulus2) and value the solution in
                    [0, period), or None ("no solution") when no integer
                    satisfies both congruences.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. One call is one test case, one line "a n b m" (residue1
    modulus1 residue2 modulus2). The integer candidate satisfies
    both congruences candidate = residue1 (mod modulus1), candidate
    = residue2 (mod modulus2). *)
Definition solves
  (residue1 modulus1 residue2 modulus2 : N) (candidate : Z)
    : Prop :=
  (candidate mod Z.of_N modulus1 = Z.of_N residue1)%Z /\
  (candidate mod Z.of_N modulus2 = Z.of_N residue2)%Z.

(** [@inside crt_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (residue1 modulus1 residue2 modulus2 : N) : Prop := {
  (* 1 <= n, m <= 10^9 *)
  vi_n : 1 <= modulus1 <= 10 ^ 9;
  vi_m : 1 <= modulus2 <= 10 ^ 9;
  (* 0 <= a < n, 0 <= b < m *)
  vi_a : residue1 < modulus1;
  vi_b : residue2 < modulus2;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the least nonnegative simultaneous solution and the least common
    multiple of the moduli, or None exactly when the congruences are inconsistent. *)
Definition crt_spec
  (residue1 modulus1 residue2 modulus2 : N)
    (output : option (N * N)) : Prop :=
  match output with
  | Some (value, period) =>
      period = N.lcm modulus1 modulus2 /\ value < period /\
      solves residue1 modulus1 residue2 modulus2 (Z.of_N
        value)
  | None =>
      ~ exists candidate : Z,
          solves residue1 modulus1 residue2 modulus2
            candidate
  end.

(** ** Interface *)

(** Solve two modular congruences whose moduli need not be coprime. Return the least
    nonnegative solution and its period, or report that the congruences are
    inconsistent.
    - Input [residue1]:
    - Input [modulus1]:
    - Input [residue2]:
    - Input [modulus2]:
    - Output [output]: *)
Program crt : uint -> uint -> uint -> uint -> option
  (uint * uint).

(** ** Bridge *)

(** [@requirement crt_spec] [@fold full correctness statement] On valid
    represented inputs, [crt] returns a represented output
    satisfying [crt_spec]. *)
Specification crt_correct :
  forall (residue1 modulus1 residue2 modulus2 : N)
         (residue1_int modulus1_int residue2_int
           modulus2_int : uint),
  valid_input residue1 modulus1 residue2 modulus2 ->
  repr residue1_int residue1 ->
    repr modulus1_int modulus1 ->
  repr residue2_int residue2 ->
    repr modulus2_int modulus2 ->
  exists output : option (N * N),
    repr (crt residue1_int modulus1_int residue2_int
      modulus2_int)
      output /\
    crt_spec residue1 modulus1 residue2 modulus2 output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
