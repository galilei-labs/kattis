(** * Loopy Cab Drivers *)

(** ** Description *)

(** A cab driver waiting outside a store must drive around and return to
    pick up the passenger. The streets are one-way, so returning is not
    always possible. Find the maximal groups of at least two stores in which
    every store can be reached from every other by following the streets.
    These are the regions in which the driver can circulate and return.
    Sort store names within each group and the groups lexicographically;
    list all stores outside these groups separately in sorted order.

    [@kattis loopycabdrivers]
    - Difficulty: 5.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Directed edge count: $0 \le m \le 10^{4}$, with no repeated edge or self-loop.
    - Vertex name length: $1 \le \ell \le 20$ uppercase or lowercase letters. *)

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
From StdGalilei Require Import repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The number of characters in [name]. *)
Definition slen (name : string) : N :=
  N.of_nat (String.length name).

(** Every character of [name] is an uppercase or lowercase English letter. *)
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

(** A directed input street leads from [name] to [name']. *)
Definition street (origins destinations : list string)
  (name name' : string)
    : Prop :=
  In (name, name') (combine origins destinations).

(** [name] appears as an endpoint of some input street. *)
Definition store (origins destinations : list string)
  (name : string)
    : Prop :=
  In name origins \/ In name destinations.

(** A walk of zero or more streets leads from [name] to [name']. *)
Definition reaches (origins destinations : list string)
    : string -> string -> Prop :=
  clos_refl_trans string (street origins destinations).

(** [name] and [name'] are mutually reachable by directed streets. *)
Definition together (origins destinations : list string)
    (name name' : string) : Prop :=
  reaches origins destinations name name' /\
  reaches origins destinations name' name.

(** [name] belongs to a mutually reachable group containing at least one other
    store. *)
Definition loopy (origins destinations : list string)
  (name : string)
    : Prop :=
  exists other, other <> name /\ together origins
    destinations name other.

(** [members] lists a maximal mutually reachable group of at least two stores. *)
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
  (* a line containing an integer 0 <= n <= 10^4 *)
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
    The output lists maximal mutually reachable groups of at least two stores,
    with names and groups sorted lexicographically, and separately lists all
    remaining store names in sorted order. *)
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

(** Find maximal mutually reachable groups of at least two stores connected
    by one-way streets, and separately list stores outside these groups.
    - Input [origins]: Starting store of each one-way street.
    - Input [destinations]: Destination store of each corresponding street.
    - Output [output]: Groups with names and groups sorted lexicographically, paired with the sorted list of remaining stores. *)
Program loopy_regions :
  array PrimString.string -> array PrimString.string ->
  array (array PrimString.string) * array PrimString.string.

(** [@example loopy_regions]
    - Sample: 1
    - Input [origins]: ["Starbucks"; "BahamaBucks"; "CVS"; "CVS"; "HEB"; "BahamaBucks"]%string
    - Input [destinations]: ["HEB"; "CVS"; "HEB"; "BahamaBucks"; "Starbucks"; "OfficeDepot"]%string
    - Output [output]: ([["BahamaBucks"; "CVS"]; ["HEB"; "Starbucks"]], ["OfficeDepot"])%string
*)

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
