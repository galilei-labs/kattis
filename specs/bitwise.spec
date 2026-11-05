(* @function        best_and
   @signature       uint -> array uint -> uint
   @math_signature  N -> list N -> N
   @summary         [best_and k a] returns the greatest bitwise AND of the
                    bitwise ORs of the sections, over the divisions of the
                    circle a into k contiguous non-empty sections
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The circle a read from position r : a[r], ..., a[n-1], a[0], ...,
   a[r-1]. *)
Definition rotate (r : nat) (a : list N) : list N :=
  skipn r a ++ firstn r a.

(* The power of a section : the bitwise OR of its integers. *)
Definition power (s : list N) : N := fold_left N.lor s 0.

(* The bitwise AND of the powers of the sections (0 for no section, never
   relied on : there is at least one). *)
Definition and_powers (secs : list (list N)) : N :=
  match secs with
  | [] => 0
  | s :: rest => fold_left (fun acc t => N.land acc (power t)) rest (power s)
  end.

(* secs divides the circle a into k contiguous non-empty sections : laid
   end to end, they read the circle from some position. *)
Definition division (a : list N) (k : N) (secs : list (list N)) : Prop :=
  len secs = k /\
  Forall (fun s => s <> []) secs /\
  exists r, (r < List.length a)%nat /\ concat secs = rotate r a.

(* The statement's bounds, for one test case. *)
Record valid_input (k : N) (a : list N) : Prop := {
  (* 1 <= K <= N <= 5 * 10^5 *)
  vi_k : 1 <= k <= len a;
  vi_n : len a <= 5 * 10 ^ 5;
  (* 0 <= A_i <= 10^9 *)
  vi_values : Forall (fun v => v <= 10 ^ 9) a;
}.

(* The answer : the value of some division, that no division exceeds. *)
Definition best_and_spec (k : N) (a : list N) (v : N) : Prop :=
  (exists secs, division a k secs /\ and_powers secs = v) /\
  forall secs, division a k secs -> and_powers secs <= v.

(* machine side : the only thing that gets extracted *)
Program best_and : uint -> array uint -> uint.

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification best_and_correct : forall (k : N) (a : list N) (xk : uint) (xa : array uint),
  valid_input k a -> repr xk k -> repr xa a ->
  exists v : N, repr (best_and xk xa) v /\ best_and_spec k a v.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
