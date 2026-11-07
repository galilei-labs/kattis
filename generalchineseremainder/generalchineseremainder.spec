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

(* Math side.  One call is one test case, one line "a n b m"
   (residue1 modulus1 residue2 modulus2). *)

(* The integer candidate satisfies both congruences
   candidate = residue1 (mod modulus1),
   candidate = residue2 (mod modulus2). *)
Definition solves (residue1 modulus1 residue2 modulus2 : N) (candidate : Z)
    : Prop :=
  (candidate mod Z.of_N modulus1 = Z.of_N residue1)%Z /\
  (candidate mod Z.of_N modulus2 = Z.of_N residue2)%Z.

(* The statement's bounds, for one test case. *)
Record valid_input (residue1 modulus1 residue2 modulus2 : N) : Prop := {
  (* 1 <= n, m <= 10^9 *)
  vi_n : 1 <= modulus1 <= 10 ^ 9;
  vi_m : 1 <= modulus2 <= 10 ^ 9;
  (* 0 <= a < n, 0 <= b < m *)
  vi_a : residue1 < modulus1;
  vi_b : residue2 < modulus2;
}.

(* Some (value, period): period = lcm(modulus1, modulus2) and value is the
   solution in [0, period).
   None: no integer solves the system ("no solution"). *)
Definition crt_spec (residue1 modulus1 residue2 modulus2 : N)
    (output : option (N * N)) : Prop :=
  match output with
  | Some (value, period) =>
      period = N.lcm modulus1 modulus2 /\ value < period /\
      solves residue1 modulus1 residue2 modulus2 (Z.of_N value)
  | None =>
      ~ exists candidate : Z,
          solves residue1 modulus1 residue2 modulus2 candidate
  end.

(* machine side : the only thing that gets extracted *)
Program crt : uint -> uint -> uint -> uint -> option (uint * uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification crt_correct :
  forall (residue1 modulus1 residue2 modulus2 : N)
         (residue1_int modulus1_int residue2_int modulus2_int : uint),
  valid_input residue1 modulus1 residue2 modulus2 ->
  repr residue1_int residue1 -> repr modulus1_int modulus1 ->
  repr residue2_int residue2 -> repr modulus2_int modulus2 ->
  exists output : option (N * N),
    repr (crt residue1_int modulus1_int residue2_int modulus2_int)
      output /\
    crt_spec residue1 modulus1 residue2 modulus2 output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
