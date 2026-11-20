(** * Bilateral Projects *)

(** ** Description *)

(** Each project pairs an employee in Stockholm with one in London. Invite
    the fewest employees so every project has at least one member invited.
    Among minimum-size invitations, prefer one including employee 1009
    whenever possible. In graph terms, this is a minimum vertex cover of
    the bipartite graph of employees and projects.

    [@kattis bilateral]
    - Difficulty: 5.6
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Distinct project count: $1 \le m \le 10^{4}$.
    - Stockholm employee IDs: $10^{3} \le s_i \le 2 \times 10^{3} - 1$; London employee IDs: $2 \times 10^{3} \le l_i \le 3 \times 10^{3} - 1$. *)

(** ** Examples *)

(** - Input convention: Project count, followed by the Stockholm and London employee IDs for each project.
    - Output convention: Minimum invitation size, followed by one invited employee ID per line. *)
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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(* Employees are their IDs; the teams are two
  parallel lists,
   one per column of the input. *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The employee to include in a minimum-size invitation whenever possible: 1009. *)
Definition friend : N := 1009.

(** The project teams as pairs of Stockholm and London employees, combining
    corresponding entries of [stockholm_members] and [london_members]. *)
Definition teams (stockholm_members london_members : list N)
  : list (N * N) :=
  combine stockholm_members london_members.

(** [invitees] lists distinct employees and includes at
    least one person from each project. *)
Definition invitation
  (stockholm_members london_members invitees : list N)
  : Prop :=
  NoDup invitees /\
  Forall (fun team => In (fst team) invitees \/ In
    (snd team) invitees)
    (teams stockholm_members london_members).

(** [invitees] is a valid [invitation] with minimum cardinality. *)
Definition smallest
  (stockholm_members london_members invitees : list N)
  : Prop :=
  invitation stockholm_members london_members invitees /\
  forall invitees',
    invitation stockholm_members london_members invitees' ->
    len invitees <= len invitees'.

(** [@inside bilateral_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (stockholm_members london_members : list N) : Prop := {
  (* 1 <= m <= 10^4, the number of teams *)
  vi_m : 1 <= len stockholm_members <= 10000;
  (* the following m lines each contain two integers i, j *)
  vi_pairs : len london_members = len stockholm_members;
  (* Stockholm employees have IDs satisfying 10^3 <= s_i <= 2 * 10^3 - 1
    *)
  vi_st : Forall (fun employee => 1000 <= employee <= 1999)
            stockholm_members;
  (* London employees have IDs satisfying 2 * 10^3 <= l_i <= 3 * 10^3 - 1 *)
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

(** [@requirement]
    The output invites the fewest employees while representing every project.
    It includes employee 1009 whenever a minimum-size invitation can do so. *)
Definition bilateral_spec
  (stockholm_members london_members : list N)
    (output : list N) : Prop :=
  smallest stockholm_members london_members output /\
  ((exists invitees',
      smallest stockholm_members london_members invitees' /\
      In friend invitees') ->
   In friend output).

(** ** Interface *)

(** Invite the fewest employees so each project has an invited team member,
    preferring a minimum-size invitation that includes employee 1009.
    - Input [stockholm_members]: Stockholm employee assigned to each project.
    - Input [london_members]: London employee assigned to each corresponding project.
    - Output [output]: Distinct invited employee IDs, covering every project with the fewest invitees and including employee 1009 whenever possible at that size. *)
Program bilateral : array uint -> array uint -> array uint.

(** [@example bilateral]
    - Sample: 1
    - Input [stockholm_members]: [1009; 1017]
    - Input [london_members]: [2011; 2011]
    - Output [output]: [2011]
*)

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
