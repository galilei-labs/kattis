(* @function        solve
   @signature       uint -> array (array float) -> array float
                    -> outcome (array float)
   @math_signature  N -> list (list R) -> list R -> outcome (list R)
   @summary         [solve n a b] decides the linear system a x = b over the
                    reals, a being n rows of n coefficients and b the n
                    right-hand sides, the system being the exact one the
                    input floats denote : Unique xs when it has exactly one
                    solution, xs holding n floats each within 10^-3 of the
                    corresponding component of that solution (wherever a
                    float lies within 10^-3 of it) ; Multiple when it has
                    several ; Inconsistent when it has none.  The harness
                    prints xs, "multiple" or "inconsistent"
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The answer, on both sides : V is array float on the machine side,
   list R on the math side. *)
Inductive outcome (V : Type) : Type :=
  | Unique : V -> outcome V
  | Multiple : outcome V
  | Inconsistent : outcome V.
Arguments Unique {V} _.
Arguments Multiple {V}.
Arguments Inconsistent {V}.

(* A machine outcome represents a math outcome : the same case, and a
   represented vector. *)
Instance repr_outcome V M `{Repr V M} : Repr (outcome V) (outcome M) :=
  fun x i => match x, i with
             | Unique v, Unique m => repr v m
             | Multiple, Multiple => True
             | Inconsistent, Inconsistent => True
             | _, _ => False
             end.

(* Math side.  A float input is read as the real it denotes (repr_float) ;
   the system is the one those reals form, and it is solved exactly in R. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The sum of the products of the entries of row and x, term by term (the
   shorter list ends the sum : never relied on, both have n entries
   wherever it matters). *)
Fixpoint dot (row x : list R) : R :=
  match row, x with
  | r :: row', v :: x' => (r * v + dot row' x')%R
  | _, _ => 0%R
  end.

(* x solves a x = b : n components, and row by row the sum of the
   coefficients times the components is the right-hand side. *)
Definition solves (n : N) (a : list (list R)) (b x : list R) : Prop :=
  len x = n /\ Forall2 (fun row bi => dot row x = bi) a b.

(* Some float lies within 10^-3 of r.  The tolerance is absolute and the
   doubles thin out as they grow : above 2^44 two consecutive ones are more
   than 2 * 10^-3 apart, so a component of the solution that large may have
   no float within 10^-3 of it, and one beyond 2^1024 has none.  The
   contract asks for the tolerance exactly where a float can meet it. *)
Definition attainable (r : R) : Prop :=
  exists f : R, representable (A := float) f /\ (Rabs (f - r) <= 1 / 1000)%R.

(* Component by component, u is within 10^-3 of x wherever some float is :
   "the entries of x are allowed to have an error of at most 10^-3". *)
Definition approximates (u x : list R) : Prop :=
  Forall2 (fun uj xj => attainable xj -> (Rabs (uj - xj) <= 1 / 1000)%R) u x.

(* The statement's bounds on one test case. *)
Record valid_input (n : N) (a : list (list R)) (b : list R) : Prop := {
  (* 1 <= n <= 100 *)
  vi_n : 1 <= n <= 100;
  (* n rows of n coefficients *)
  vi_rows : len a = n;
  vi_row : Forall (fun row => len row = n) a;
  (* n right-hand sides *)
  vi_b : len b = n;
  (* "floating point numbers" : the statement bounds neither their
     magnitude nor their digits ; each is a finite binary64 (repr_float),
     nothing more. *)
}.

(* The answer : Unique u when exactly one vector solves the system and u
   approximates it, Multiple when two distinct vectors solve it,
   Inconsistent when none does.  Exactly one case holds. *)
Definition solve_spec (n : N) (a : list (list R)) (b : list R)
                      (o : outcome (list R)) : Prop :=
  match o with
  | Unique u => exists x, solves n a b x /\ (forall y, solves n a b y -> y = x)
                          /\ approximates u x
  | Multiple => exists x y, solves n a b x /\ solves n a b y /\ x <> y
  | Inconsistent => forall x, ~ solves n a b x
  end.

(* machine side : the only thing that gets extracted *)
Program solve : uint -> array (array float) -> array float ->
                  outcome (array float).

(* the one line : repr on the inputs (universal), repr on the output
   (existential) *)
Specification solve_correct :
  forall (n : N) (a : list (list R)) (b : list R)
         (xn : uint) (xa : array (array float)) (xb : array float),
  valid_input n a b -> repr xn n -> repr xa a -> repr xb b ->
  exists o : outcome (list R), repr (solve xn xa xb) o /\ solve_spec n a b o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
