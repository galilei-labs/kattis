(* @function        committees
   @signature       uint -> array PrimString.string -> array PrimString.string -> uint
   @math_signature  N -> list String.string -> list String.string -> N
   @summary         One department: [committees n a b] gets the number n of
                    department members and the m pairs of members who do
                    not get along, pair i naming a.[i] and b.[i].  It
                    returns the minimum number of committees such that
                    everyone sits on exactly one committee and no two
                    members of a pair sit on the same one.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray PrimString.
From Stdlib Require String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m pairs come as two parallel lists, one per name column
   of the m lines; a member is known by its name. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* A letter a-z or A-Z, read through its byte code. *)
Definition is_letter (ch : Ascii.ascii) : Prop :=
  let k := Ascii.N_of_ascii ch in (65 <= k <= 90) \/ (97 <= k <= 122).

(* A name: a sequence of up to 20 lowercase and/or uppercase letters. *)
Definition name (s : String.string) : Prop :=
  N.of_nat (String.length s) <= 20 /\
  Forall is_letter (String.list_ascii_of_string s).

(* [x] is the name of a member listed in some pair. *)
Definition listed (a b : list String.string) (x : String.string) : Prop :=
  In x a \/ In x b.

(* [c] puts everyone on one of k committees, numbered 0 .. k-1.  The
   department has at least one member, so k >= 1; members listed in no
   pair can sit on any committee, so only the listed ones are constrained. *)
Definition assignment (a b : list String.string) (k : N)
    (c : String.string -> N) : Prop :=
  0 < k /\ forall x, listed a b x -> c x < k.

(* No pair sits on the same committee. *)
Definition separates (a b : list String.string) (c : String.string -> N)
  : Prop :=
  Forall2 (fun x y => c x <> c y) a b.

(* k committees suffice. *)
Definition feasible (a b : list String.string) (k : N) : Prop :=
  exists c, assignment a b k c /\ separates a b c.

(* The statement's guarantees on one department. *)
Record valid_input (n : N) (a b : list String.string) : Prop := {
  (* a positive integer n <= 15 *)
  vi_n : 1 <= n <= 15;
  (* a non-negative integer m <= n(n-1)/2 *)
  vi_m : len a <= n * (n - 1) / 2;
  (* m lines, each listing the names of two department members *)
  vi_pairs : len b = len a;
  (* ... two different department members *)
  vi_different : Forall2 (fun x y => x <> y) a b;
  (* a name is a sequence of up to 20 lowercase and/or uppercase letters *)
  vi_names_a : Forall name a;
  vi_names_b : Forall name b;
  (* n people in the department, each with a unique name, and every name
     listed is one of theirs *)
  vi_members : exists members : list String.string,
    len members = n /\ NoDup members /\
    forall x, listed a b x -> In x members;
}.

(* The minimum number of committees. *)
Definition committees_spec (n : N) (a b : list String.string) (k : N)
  : Prop :=
  feasible a b k /\ forall k', feasible a b k' -> k <= k'.

Program committees :
  uint -> array PrimString.string -> array PrimString.string -> uint.

Specification committees_correct :
  forall (n : N) (a b : list String.string)
         (x : uint) (y z : array PrimString.string),
  valid_input n a b -> repr x n -> repr y a -> repr z b ->
  exists k : N, repr (committees x y z) k /\ committees_spec n a b k.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
