(* @function        crt
   @signature       uint -> uint -> uint -> uint -> option (uint * uint)
   @math_signature  N -> N -> N -> N -> option (N * N)
   @summary         [crt a n b m] solves the system x = a (mod n),
                    x = b (mod m) for moduli that need not be coprime.  It
                    returns Some (x, K) with K = lcm(n, m) and x the solution
                    in [0, K), or None ("no solution") when no integer
                    satisfies both congruences.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  One call is one test case, one line "a n b m". *)

(* The integer x satisfies both congruences x = a (mod n), x = b (mod m). *)
Definition solves (a n b m : N) (x : Z) : Prop :=
  (x mod Z.of_N n = Z.of_N a)%Z /\ (x mod Z.of_N m = Z.of_N b)%Z.

(* The statement's bounds, for one test case. *)
Record valid_input (a n b m : N) : Prop := {
  (* 1 <= n, m <= 10^9 *)
  vi_n : 1 <= n <= 10 ^ 9;
  vi_m : 1 <= m <= 10 ^ 9;
  (* 0 <= a < n, 0 <= b < m *)
  vi_a : a < n;
  vi_b : b < m;
}.

(* Some (x, K): K = lcm(n, m) and x is the solution in [0, K).
   None: no integer solves the system ("no solution"). *)
Definition crt_spec (a n b m : N) (o : option (N * N)) : Prop :=
  match o with
  | Some (x, k) => k = N.lcm n m /\ x < k /\ solves a n b m (Z.of_N x)
  | None => ~ exists x : Z, solves a n b m x
  end.

(* machine side : the only thing that gets extracted *)
Program crt : uint -> uint -> uint -> uint -> option (uint * uint).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification crt_correct :
  forall (a n b m : N) (xa xn xb xm : uint),
  valid_input a n b m ->
  repr xa a -> repr xn n -> repr xb b -> repr xm m ->
  exists o : option (N * N), repr (crt xa xn xb xm) o /\ crt_spec a n b m o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
