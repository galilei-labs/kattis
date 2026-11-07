(** * Bilateral Projects *)

(** ** Description *)

(** Find a smallest vertex cover of a bipartite graph: a set containing at
    least one endpoint of every edge. Prefer a minimum cover containing
    vertex 1009 whenever one exists.

    [@kattis bilateral]
    - Difficulty: 5.6

    **Kattis Bounds**
    - 1 to 10000 distinct edges.
    - The two vertex sets use IDs 1000 to 1999 and 2000 to 2999. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
2
1009 2011
1017 2011
Output:
1
2011
*)

(** ** [@hide] Environment *)

(* @function        bilateral
   @signature       array uint -> array uint -> array uint
   @math_signature  list N -> list N -> list N
   @summary         [bilateral stockholm_members london_members] takes the
                    m two-person teams, team k being the Stockholm employee
                    stockholm_members_k and the London employee
                    london_members_k, and returns the IDs of a smallest set of
                    employees containing at least one member of every team.
                    Among the smallest such sets it returns one containing
                    the friend, employee 1009, whenever one exists.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  Employees are their IDs; the teams are two
  parallel lists,
   one per column of the input. *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Your friend has ID 1009. *)
Definition friend : N := 1009.

(** The teams, as (Stockholm member, London member)
    pairs. *)
Definition teams (stockholm_members london_members : list N)
  : list (N * N) :=
  combine stockholm_members london_members.

(** invitees lists distinct employees and includes at
    least one person from each project. *)
Definition invitation
  (stockholm_members london_members invitees : list N)
  : Prop :=
  NoDup invitees /\
  Forall (fun team => In (fst team) invitees \/ In
    (snd team) invitees)
    (teams stockholm_members london_members).

(** invitees is an invitation with the smallest number
    of employees. *)
Definition smallest
  (stockholm_members london_members invitees : list N)
  : Prop :=
  invitation stockholm_members london_members invitees /\
  forall invitees',
    invitation stockholm_members london_members invitees' ->
    len invitees <= len invitees'.

(** [@inside bilateral_correct] The statement's bounds. *)
Record valid_input
  (stockholm_members london_members : list N) : Prop := {
  (* 1 <= m <= 10 000, the number of teams *)
  vi_m : 1 <= len stockholm_members <= 10000;
  (* the following m lines each contain two integers i, j *)
  vi_pairs : len london_members = len stockholm_members;
  (* Stockholm employees have IDs in the range 1000 to 1999
    *)
  vi_st : Forall (fun employee => 1000 <= employee <= 1999)
            stockholm_members;
  (* London employees have IDs in the range 2000 to 2999 *)
  vi_lo : Forall
    (fun employee => 2000 <= employee <= 2999)
    london_members;
  (* there cannot be several teams consisting of the same
    pair of
     employees *)
  vi_distinct : NoDup
    (teams stockholm_members london_members);
}.

(** ** Correctness *)

(** [@requirement] [@short must return a smallest valid
    invitation list.] The invitees: a smallest
    invitation, which contains the friend whenever some
    smallest invitation does. Any such list, in any
    order. *)
Definition bilateral_spec
  (stockholm_members london_members : list N)
    (output : list N) : Prop :=
  smallest stockholm_members london_members output /\
  ((exists invitees',
      smallest stockholm_members london_members invitees' /\
      In friend invitees') ->
   In friend output).

(** ** Interface *)

(** The machine-level interface.
    - Input [stockholm_members]:
    - Input [london_members]:
    - Output [output]: *)
Program bilateral : array uint -> array uint -> array uint.

(** ** Bridge *)

(** [@requirement bilateral_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented output satisfying
    [bilateral_spec]. *)
Specification bilateral_correct :
  forall (stockholm_members london_members : list N)
         (stockholm_members_arr london_members_arr : array
           uint),
  valid_input stockholm_members london_members ->
  repr stockholm_members_arr stockholm_members ->
  repr london_members_arr london_members ->
  exists output : list N,
    repr (bilateral stockholm_members_arr
      london_members_arr) output /\
    bilateral_spec stockholm_members london_members output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
