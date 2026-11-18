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
    - Moduli: $1 \le n, m \le 10^{9}$.
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
                    It runs in at most c1 * (log2 m1 + log2 m2 + 1) + c2
                    steps of the cost model on a valid input (the extended
                    Euclidean algorithm on the two moduli), for two
                    constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** [candidate] satisfies both congruences: residue [residue1] modulo [modulus1],
    and residue [residue2] modulo [modulus2]. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O(\log(m_1+2)+\log(m_2+2))$ steps, where $m_1$ and $m_2$ are the two moduli. *)
Definition crt_time_spec (c1 c2 n_modulus1 n_modulus2 steps : nat) : Prop :=
  (steps <= c1 * (Nat.log2 (n_modulus1) + Nat.log2 (n_modulus2) + 1) + c2)%nat.

(** ** Interface *)

(** Solve two modular congruences whose moduli need not be coprime. Return the least
    nonnegative solution and its period, or report that the congruences are
    inconsistent.
    - Input [residue1]: Required remainder for the first congruence.
    - Input [modulus1]: Modulus of the first congruence.
    - Input [residue2]: Required remainder for the second congruence.
    - Input [modulus2]: Modulus of the second congruence.
    - Output [output]: The output gives the least nonnegative simultaneous solution and the least common multiple of the moduli, or None exactly when the congruences are inconsistent. *)
Program crt : uint -> uint -> uint -> uint -> option
  (uint * uint).

(** [@example crt]
    - Sample: 1
    - Case: 1
    - Input [residue1]: 10000
    - Input [modulus1]: 23000
    - Input [residue2]: 9000
    - Input [modulus2]: 23000
    - Output [output]: None
*)

(** [@example crt]
    - Sample: 1
    - Case: 2
    - Input [residue1]: 10000
    - Input [modulus1]: 23000
    - Input [residue2]: 10000
    - Input [modulus2]: 23000
    - Output [output]: Some (10000, 23000)
*)

(** [@example crt]
    - Sample: 1
    - Case: 3
    - Input [residue1]: 1234
    - Input [modulus1]: 2000
    - Input [residue2]: 746
    - Input [modulus2]: 2002
    - Output [output]: Some (489234, 2002000)
*)

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

(** ** Complexity *)

(** [@hide] [crt_cost] is the cost translation of [crt] (the judge
    recomputes it and compares) ... *)
Complexity crt_cost for crt.

(** [@fold complexity bound] ... and runs in at most c1 * (log2 m1 + log2 m2 + 1) + c2 steps of the cost model on a valid input (the extended Euclidean algorithm on the two moduli), for two constants
    quantified before the inputs, on every valid input. [@requirement crt_time_spec] *)
Specification crt_time : exists c1 c2 : nat,
  forall (residue1 modulus1 residue2 modulus2 : N)
  (residue1_int modulus1_int residue2_int
  modulus2_int : uint),
  valid_input residue1 modulus1 residue2 modulus2 ->
  repr residue1_int residue1 ->
  repr modulus1_int modulus1 ->
  repr residue2_int residue2 ->
  repr modulus2_int modulus2 ->
  crt_time_spec c1 c2 (size modulus1_int) (size modulus2_int) (cost4 crt_cost residue1_int modulus1_int residue2_int modulus2_int).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
