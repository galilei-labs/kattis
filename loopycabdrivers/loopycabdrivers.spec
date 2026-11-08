(** * Loopy Cab Drivers *)

(** ** Description *)

(** Find the strongly connected components of a directed graph that contain
    at least two vertices. Sort the names within each component and the
    components lexicographically, and list the remaining vertices
    separately.

    [@kattis loopycabdrivers]
    - Difficulty: 5.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 0 to 10,000 directed edges, with no repeated edge or self-loop.
    - Vertex names contain 1 to 20 uppercase or lowercase letters. *)

(** ** Examples *)

(** - Input convention: Directed edge count, followed by source-destination name pairs.
    - Output convention: Sorted multi-vertex components prefixed by okay; remaining names on a final avoid line. *)
(* Input:
6
Starbucks HEB
BahamaBucks CVS
CVS HEB
CVS BahamaBucks
HEB Starbucks
BahamaBucks OfficeDepot
Output:
okay BahamaBucks CVS
okay HEB Starbucks
avoid OfficeDepot
*)

(** ** [@hide] Environment *)
(* @function        loopy_regions
   @signature       array PrimString.string -> array PrimString.string ->
                    array (array PrimString.string) * array PrimString.string
   @math_signature  list String.string -> list String.string ->
                    list (list String.string) * list String.string
   @summary         Given the one-way streets of a city as two parallel
                    lists of store names (street k goes from origins_k to
                    destinations_k), [loopy_regions origins destinations]
                    returns the groups of two or more stores that can be
                    visited together indefinitely (each reaches every other
                    one and back), each group in lexicographic order and the
                    groups in lexicographic order, and, in lexicographic
                    order, the stores in no group.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii Relations Sorting.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The input lines are two parallel lists, one per column
    (line k is "origins_k destinations_k"). The number of elements
    of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters of name. *)
Definition slen (name : string) : N :=
  N.of_nat (String.length name).

(** Every character of name is a letter, a-z or A-Z. *)
Definition letters (name : string) : Prop :=
  forall k letter, String.get k name = Some letter ->
    (65 <= N_of_ascii letter <= 90) \/ (97 <= N_of_ascii
      letter <= 122).

(** Lexicographic order: character codes, a proper prefix first ('Z' <
    'a'). *)
Definition str_lt (name name' : string) : Prop :=
  String.compare name name' = Lt.

(** Lexicographic order on lists of names, element by element, a proper
    prefix first. *)
Fixpoint lex_lt (names names' : list string) : Prop :=
  match names, names' with
  | _, [] => False
  | [], _ :: _ => True
  | name :: rest, name' :: rest' =>
      str_lt name name' \/ (name = name' /\ lex_lt rest
        rest')
  end.

(** One can drive from name to name' along one street. *)
Definition street (origins destinations : list string)
  (name name' : string)
    : Prop :=
  In (name, name') (combine origins destinations).

(** name is a store of the city: it is named on some input line. *)
Definition store (origins destinations : list string)
  (name : string)
    : Prop :=
  In name origins \/ In name destinations.

(** One can drive from name to name' along zero or more streets. *)
Definition reaches (origins destinations : list string)
    : string -> string -> Prop :=
  clos_refl_trans string (street origins destinations).

(** name and name' can be visited together indefinitely. *)
Definition together (origins destinations : list string)
    (name name' : string) : Prop :=
  reaches origins destinations name name' /\
  reaches origins destinations name' name.

(** name can be visited indefinitely in conjunction with at least one
    other store. *)
Definition loopy (origins destinations : list string)
  (name : string)
    : Prop :=
  exists other, other <> name /\ together origins
    destinations name other.

(** members is a group: two or more stores, exactly those that can be
    visited together with one of them. *)
Definition group (origins destinations : list string)
  (members : list string)
    : Prop :=
  2 <= len members /\
  exists name, forall other,
    In other members <-> together origins destinations name
      other.

(** [@inside loopy_regions_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input
  (origins destinations : list string) : Prop := {
  (* a line containing an integer 0 <= n <= 10 000 *)
  vi_n : len origins <= 10000;
  (* following this are n lines, each containing a pair
     of store names *)
  vi_lines : len origins = len destinations;
  (* every name is a sequence of between 1 and 20 letters
     (a-z, A-Z) *)
  vi_src_names :
    Forall (fun name => 1 <= slen name <= 20 /\ letters
      name) origins;
  vi_dst_names :
    Forall (fun name => 1 <= slen name <= 20 /\ letters
      name) destinations;
  (* A <> B *)
  vi_distinct : Forall2 (fun name name' => name <> name')
    origins destinations;
  (* no pair of stores is listed more than once *)
  vi_no_repeat : NoDup (combine origins destinations);
}.

(** ** Correctness *)

(** [@requirement]
    The output lists strongly connected components of size at least two with names and
    groups sorted lexicographically, followed separately by the remaining names in
    sorted order. *)
Definition loopy_regions_spec
  (origins destinations : list string)
    (output : list (list string) * list string) : Prop :=
  match output with
  | (groups, avoid) =>
      (forall members, In members groups ->
         group origins destinations members /\
         StronglySorted str_lt members) /\
      (forall name, loopy origins destinations name ->
         exists members, In members groups /\ In name
           members) /\
      StronglySorted lex_lt groups /\
      StronglySorted str_lt avoid /\
      (forall name, In name avoid <->
         store origins destinations name /\ ~ loopy origins
           destinations name)
  end.

(** ** Interface *)

(** Find the strongly connected components of a directed graph that contain at least two
    vertices. Sort the names within each component and the components lexicographically,
    and list the remaining vertices separately.
    - Input [origins]:
    - Input [destinations]:
    - Output [output]: *)
Program loopy_regions :
  array PrimString.string -> array PrimString.string ->
  array (array PrimString.string) * array PrimString.string.

(** ** Bridge *)

(** [@requirement loopy_regions_spec] [@fold full correctness statement]
    On valid represented inputs, [loopy_regions] returns a
    represented output satisfying [loopy_regions_spec]. *)
Specification loopy_regions_correct :
  forall (origins destinations : list string)
         (origins_arr destinations_arr : array
           PrimString.string),
  valid_input origins destinations ->
  repr origins_arr origins ->
    repr destinations_arr destinations ->
  exists output : list (list string) * list string,
    repr (loopy_regions origins_arr destinations_arr) output
      /\
    loopy_regions_spec origins destinations output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
