(** * Committee Assignment *)

(** ** Description *)

(** Partition a graph's vertices into as few groups as possible, with no
    adjacent vertices in the same group.

    [@kattis committeeassignment]
    - Difficulty: 7.0
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $1 \le n \le 15$; at most $n(n-1)/2$ incompatible pairs.
    - Names contain at most $20$ uppercase or lowercase letters. *)

(** ** Examples *)

(** - Input convention: Per case: vertex and edge counts, followed by pairs of names; 0 0 ends input.
    - Output convention: One minimum number of independent groups per case. *)
(* Input:
5 0
5 2
wally alice
wally dilbert
5 3
greg don
greg bill
don bill
0 0
Output:
1
2
3
*)

(** ** [@hide] Environment *)

(* @function        committees
   @signature       uint -> array PrimString.string -> array PrimString.string -> uint
   @math_signature  N -> list String.string -> list String.string -> N
   @summary         One department: [committees member_count first_names
                    second_names] gets the number member_count of department
                    members and the m pairs of members who do not get along,
                    pair i naming first_names.[i] and second_names.[i].  It
                    returns the minimum number of committees such that
                    everyone sits on exactly one committee and no two
                    members of a pair sit on the same one.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  PrimString.
From Stdlib Require String Ascii.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The m pairs come as two parallel lists, one
  per name column
   of the m lines; a member is known by its name. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A letter a-z or A-Z, read through its byte code. *)
Definition is_letter (character : Ascii.ascii) : Prop :=
  let code := Ascii.N_of_ascii character in
  (65 <= code <= 90) \/ (97 <= code <= 122).

(** A name: a sequence of up to 20 lowercase and/or
    uppercase letters. *)
Definition name (candidate : String.string) : Prop :=
  N.of_nat (String.length candidate) <= 20 /\
  Forall is_letter (String.list_ascii_of_string candidate).

(** [member] is the name of a member listed in some
    pair. *)
Definition listed
  (first_names second_names : list String.string)
    (member : String.string) : Prop :=
  In member first_names \/ In member second_names.

(** [committee_of] puts everyone on one of
    committee_count committees, numbered 0 ..
    committee_count-1. The department has at least one
    member, so committee_count >= 1; members listed in
    no pair can sit on any committee, so only the listed
    ones are constrained. *)
Definition assignment
  (first_names second_names : list String.string)
    (committee_count : N) (committee_of : String.string
      -> N) : Prop :=
  0 < committee_count /\
  forall member, listed first_names second_names member ->
    committee_of member < committee_count.

(** No pair sits on the same committee. *)
Definition separates
  (first_names second_names : list String.string)
    (committee_of : String.string -> N) : Prop :=
  Forall2 (fun member member' => committee_of member <>
    committee_of member')
    first_names second_names.

(** committee_count committees suffice. *)
Definition feasible
  (first_names second_names : list String.string)
    (committee_count : N) : Prop :=
  exists committee_of,
    assignment first_names second_names committee_count
      committee_of /\
    separates first_names second_names committee_of.

(** [@inside committees_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (member_count : N)
    (first_names second_names : list String.string) : Prop
      := {
  (* a positive integer n <= 15 *)
  vi_n : 1 <= member_count <= 15;
  (* a non-negative integer m <= n(n-1)/2 *)
  vi_m : len first_names <= member_count *
    (member_count - 1) / 2;
  (* m lines, each listing the names of two department
    members *)
  vi_pairs : len second_names = len first_names;
  (* ... two different department members *)
  vi_different : Forall2
    (fun member member' => member <> member')
                   first_names second_names;
  (* a name is a sequence of up to 20 lowercase and/or
    uppercase letters *)
  vi_names_a : Forall name first_names;
  vi_names_b : Forall name second_names;
  (* n people in the department, each with a unique name,
    and every name
     listed is one of theirs *)
  vi_members : exists members : list String.string,
    len members = member_count /\ NoDup members /\
    forall member, listed first_names second_names member
      -> In member members;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the minimum number of groups in a partition of the vertices with no
    adjacent vertices in the same group. *)
Definition committees_spec (member_count : N)
    (first_names second_names : list String.string)
      (output : N)
  : Prop :=
  feasible first_names second_names output /\
  forall output', feasible first_names second_names output'
    ->
    output <= output'.

(** ** Interface *)

(** Partition a graph's vertices into as few groups as possible, with no adjacent vertices
    in the same group.
    - Input [member_count]: Total number of vertices to partition.
    - Input [first_names]: First endpoint name of each incompatible pair.
    - Input [second_names]: Second endpoint name of each incompatible pair.
    - Output [output]: The output is the minimum number of groups in a partition of the vertices with no adjacent vertices in the same group. *)
Program committees :
  uint -> array PrimString.string
    -> array PrimString.string -> uint.

(** ** Bridge *)

(** [@requirement committees_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [committees_spec]. *)
Specification committees_correct :
  forall (member_count : N)
    (first_names second_names : list String.string)
         (member_count_int : uint)
         (first_names_arr second_names_arr : array
           PrimString.string),
  valid_input member_count first_names second_names ->
  repr member_count_int member_count
    -> repr first_names_arr first_names ->
  repr second_names_arr second_names ->
  exists output : N,
    repr (committees member_count_int first_names_arr
      second_names_arr)
      output /\
    committees_spec member_count first_names second_names
      output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
