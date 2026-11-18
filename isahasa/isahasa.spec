(** * Is-A? Has-A? Who Knowz-A? *)

(** ** Description *)

(** Given facts about classes, determine which inheritance and containment
    relationships follow. A class A is-a B when A is a subclass of B; A has-a
    B when it has a field of type B. These relationships also propagate:
    subclasses inherit fields, and a contained object may itself contain
    other objects or belong to a subclass.

    An is-a query follows a chain of zero or more is-a relationships. A has-a
    query follows a chain of either kind containing at least one has-a step.
    For example, if A has-a B and B is-a C, then A has-a C.

    [@kattis isahasa]
    - Difficulty: 6.4
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Relationship count: $1 \le n \le 10^{4}$ and Query count: $1 \le q \le 10^{4}$.
    - At most $500$ distinct class names; query names occur in the given
      relationships.
    - No nontrivial is-a cycles. *)

(** ** Examples *)

(** - Input convention: Fact and query counts, followed by name is-a name or name has-a name relations.
    - Output convention: One Query number: true/false result per query, numbered from 1. *)
(* Input:
5 5
Day is-a Time
Appointment is-a Datebook
Appointment is-a Reminder
Appointment has-a Day
Datebook has-a Year
Day is-a Time
Time is-a Day
Appointment has-a Time
Appointment has-a Year
Day is-a Day
Output:
Query 1: true
Query 2: false
Query 3: true
Query 4: true
Query 5: true
*)

(** ** [@hide] Environment *)
(* @function        isahasa
   @signature       array PrimString.string -> array relkind ->
                    array PrimString.string -> array PrimString.string ->
                    array relkind -> array PrimString.string -> array bool
   @math_signature  list String.string -> list relkind -> list String.string ->
                    list String.string -> list relkind -> list String.string ->
                    list bool
   @summary         Given relationship i reads "given_sources_i
                    given_kinds_i given_targets_i" and query j reads
                    "query_sources_j query_kinds_j query_targets_j", the
                    kind being is-a or has-a.  Answer j is true exactly
                    when query j follows from the given relationships: x
                    is-a y iff a chain of zero or more given is-a steps
                    leads from x to y; x has-a y iff a chain of given
                    steps of either kind, at least one of them has-a,
                    does.
                    It runs in at most c1 * ((n + m + 1) * (n + 1)^2 + L) +
                    c2 steps of the cost model on a valid input, n the
                    number of given lines, m of queries and L the total
                    length of the names ([sizes]): the worst case of the
                    chained name table (a chain may hold every name) and the
                    bit-packed transitive closure over the k <= 2n names,
                    k^3 / 63 word operations; the expected time of the
                    hashing is not stated, for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Relations String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The relationship kind, is-a or has-a, shared by the machine and mathematical
    interfaces. *)
Inductive relkind := IsA | HasA.

(** [@hide] Machine and mathematical relationship kinds represent themselves. *)
Instance repr_relkind : Repr relkind relkind :=
  fun kind kind' => kind = kind'.

(** [@hide] The cost translation of [relkind] and the witness of a machine
    relationship kind, for the bound below. *)
Elpi complexity relkind.
Instance witness_relkind : Witness relkind (fun CM r => relkind_cost CM r) :=
  fun r => match r with IsA => IsA_cost stepsCM | HasA => HasA_cost stepsCM end.
Instance witness_array_relkind :
  Witness (array relkind) (fun CM t => array_cost CM relkind (relkind_cost CM) t) :=
  @witness_array relkind (fun CM => relkind_cost CM) witness_relkind.

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A single-word class name: not empty, and no space, tab, newline,
    carriage return, vertical tab or form feed. *)
Definition single_word (name : string) : Prop :=
  name <> EmptyString /\
  forall k character, String.get k name = Some character ->
    ~ (N_of_ascii character = 32 \/ (9 <= N_of_ascii
      character <= 13)).

(** An input line states the relationship of kind [kind] from [from_class] to
    [to_class]. *)
Definition given (given_sources : list string)
  (given_kinds : list relkind)
    (given_targets : list string) (kind : relkind)
    (from_class to_class : string) : Prop :=
  exists i, nth_error given_sources i = Some from_class /\
            nth_error given_kinds i = Some kind /\
            nth_error given_targets i = Some to_class.

(** An input relationship of either kind goes from [from_class] to [to_class]. *)
Definition any_given given_sources given_kinds given_targets
    (from_class to_class : string) : Prop :=
  given given_sources given_kinds given_targets IsA
    from_class to_class \/
  given given_sources given_kinds given_targets HasA
    from_class to_class.

(** A chain of zero or more given is-a relationships leads from [from_class] to
    [to_class]. *)
Definition is_a given_sources given_kinds given_targets :
  relation string :=
  clos_refl_trans string (given given_sources given_kinds
    given_targets IsA).

(** A chain of given relationships leads from [from_class] to [to_class] and
    contains at least one has-a step. *)
Definition has_a given_sources given_kinds given_targets
    (from_class to_class : string) : Prop :=
  exists has_owner has_part,
    clos_refl_trans string
      (any_given given_sources given_kinds given_targets)
      from_class has_owner /\
    given given_sources given_kinds given_targets HasA
      has_owner has_part /\
    clos_refl_trans string
      (any_given given_sources given_kinds given_targets)
      has_part to_class.

(** The relationship of kind [kind] from [from_class] to [to_class] follows from the
    given relationships. *)
Definition follows given_sources given_kinds given_targets
  (kind : relkind)
    (from_class to_class : string) : Prop :=
  match kind with
  | IsA => is_a given_sources given_kinds given_targets
    from_class to_class
  | HasA => has_a given_sources given_kinds given_targets
    from_class to_class
  end.

(** [@inside isahasa_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (given_sources : list string)
    (given_kinds : list relkind) (given_targets : list
      string)
    (query_sources : list string) (query_kinds : list
      relkind)
    (query_targets : list string) : Prop := {
  (* 1 <= n <= 10^4, n the number of given
     relationships, one per line "c1 r c2" *)
  vi_n : 1 <= len given_sources <= 10000;
  vi_rs_len : len given_kinds = len given_sources;
  vi_dst_len : len given_targets = len given_sources;
  (* 1 <= m <= 10^4, m the number of queries, one per
     line, same format *)
  vi_m : 1 <= len query_sources <= 10000;
  vi_qrs_len : len query_kinds = len query_sources;
  vi_qdst_len : len query_targets = len query_sources;
  (* c1 and c2 are single-word class names *)
  vi_words : Forall single_word
    (given_sources ++ given_targets ++ query_sources ++
      query_targets);
  (* there will be at most 500 distinct class names in
     the n + m lines *)
  vi_distinct : exists names : list string, len names <= 500
    /\
    forall name,
      In name (given_sources ++ given_targets ++
        query_sources ++
               query_targets) ->
      In name names;
  (* all class names in the last m lines will appear at
     least once in the initial n lines *)
  vi_query_names : forall name,
    In name (query_sources ++ query_targets) ->
    In name (given_sources ++ given_targets);
  (* is-a relationships can not be circular (apart from
     the trivial identity "x is-a x") *)
  vi_acyclic : forall from_class to_class,
    is_a given_sources given_kinds given_targets from_class
      to_class ->
    is_a given_sources given_kinds given_targets to_class
      from_class ->
    from_class = to_class;
}.

(** ** Correctness *)

(** [@requirement]
    Each output entry is true exactly when the corresponding relationship follows from
    the given is-a and has-a facts. *)
Definition isahasa_spec (given_sources : list string)
    (given_kinds : list relkind) (given_targets : list
      string)
    (query_sources : list string) (query_kinds : list
      relkind)
    (query_targets : list string) (output : list bool) :
      Prop :=
  len output = len query_sources /\
  forall j : nat, (j < List.length query_sources)%nat ->
    (nth j output false = true <->
     follows given_sources given_kinds given_targets (nth j
       query_kinds IsA)
             (nth j query_sources EmptyString)
             (nth j query_targets EmptyString)).

(** ** Complexity *)

(** [@requirement] Runs in $O((g+q+1)(g+1)^2+L)$ steps, where $g$ is the number of given relations, $q$ the number of queries, and $L$ the total length of their source and target names. *)
Definition isahasa_time_spec (c1 c2 n_given_sources n_query_sources total_given_sources total_given_targets total_query_sources total_query_targets steps : nat) : Prop :=
  (steps <= c1 * ((n_given_sources + n_query_sources + 1) * (n_given_sources + 1) * (n_given_sources + 1) + total_given_sources + total_given_targets + total_query_sources + total_query_targets + 1) + c2)%nat.

(** ** Interface *)

(** Decide which subclass (is-a) and field-containment (has-a) relationships
    follow from the given class facts. An is-a relationship follows along
    zero or more is-a links; a has-a relationship follows along a chain of
    either kind containing at least one has-a link.
    - Input [given_sources]: Source class of each given relationship.
    - Input [given_kinds]: Kind of each given relationship: is-a or has-a.
    - Input [given_targets]: Target class of each given relationship.
    - Input [query_sources]: Source class of each query.
    - Input [query_kinds]: Relationship kind asked about in each query.
    - Input [query_targets]: Target class of each query.
    - Output [output]: Each output entry is true exactly when the corresponding relationship follows from the given is-a and has-a facts. *)
Program isahasa :
  array PrimString.string -> array relkind ->
    array PrimString.string ->
  array PrimString.string -> array relkind ->
    array PrimString.string ->
  array bool.

(** [@example isahasa]
    - Sample: 1
    - Input [given_sources]: ["Day"; "Appointment"; "Appointment"; "Appointment"; "Datebook"]%string
    - Input [given_kinds]: [IsA; IsA; IsA; HasA; HasA]
    - Input [given_targets]: ["Time"; "Datebook"; "Reminder"; "Day"; "Year"]%string
    - Input [query_sources]: ["Day"; "Time"; "Appointment"; "Appointment"; "Day"]%string
    - Input [query_kinds]: [IsA; IsA; HasA; HasA; IsA]
    - Input [query_targets]: ["Time"; "Day"; "Time"; "Year"; "Day"]%string
    - Output [output]: [true; false; true; true; true]
*)

(** ** Bridge *)

(** [@requirement isahasa_spec] [@fold full correctness statement] On
    valid represented inputs, [isahasa] returns a represented output
    satisfying [isahasa_spec]. *)
Specification isahasa_correct :
  forall (given_sources : list string) (given_kinds : list
    relkind)
         (given_targets : list string) (query_sources : list
           string)
         (query_kinds : list relkind) (query_targets : list
           string)
         (given_sources_arr : array PrimString.string)
         (given_kinds_arr : array relkind)
         (given_targets_arr : array PrimString.string)
         (query_sources_arr : array PrimString.string)
         (query_kinds_arr : array relkind)
         (query_targets_arr : array PrimString.string),
  valid_input given_sources given_kinds given_targets
    query_sources
    query_kinds query_targets ->
  repr given_sources_arr given_sources ->
    repr given_kinds_arr given_kinds ->
  repr given_targets_arr given_targets ->
  repr query_sources_arr query_sources ->
    repr query_kinds_arr query_kinds ->
  repr query_targets_arr query_targets ->
  exists output : list bool,
    repr (isahasa given_sources_arr given_kinds_arr
      given_targets_arr
            query_sources_arr query_kinds_arr
              query_targets_arr) output /\
    isahasa_spec given_sources given_kinds given_targets
      query_sources
      query_kinds query_targets output.

(** ** Complexity *)

(** [@hide] [isahasa_cost] is the cost translation of [isahasa] (the judge
    recomputes it and compares) ... *)
Complexity isahasa_cost for isahasa.

(** [@fold complexity bound] ... and runs in at most c1 * ((n + m + 1) * (n + 1)^2 + L) + c2 steps of the cost model on a valid input, n the number of given lines, m of queries and L the total length of the names ([sizes]): the worst case of the chained name table (a chain may hold every name) and the bit-packed transitive closure over the k <= 2n names, k^3 / 63 word operations; the expected time of the hashing is not stated, for two constants
    quantified before the inputs, on every valid input. [@requirement isahasa_time_spec] *)
Specification isahasa_time : exists c1 c2 : nat,
  forall (given_sources : list string) (given_kinds : list
  relkind)
  (given_targets : list string) (query_sources : list
  string)
  (query_kinds : list relkind) (query_targets : list
  string)
  (given_sources_arr : array PrimString.string)
  (given_kinds_arr : array relkind)
  (given_targets_arr : array PrimString.string)
  (query_sources_arr : array PrimString.string)
  (query_kinds_arr : array relkind)
  (query_targets_arr : array PrimString.string),
  valid_input given_sources given_kinds given_targets
  query_sources
  query_kinds query_targets ->
  repr given_sources_arr given_sources ->
  repr given_kinds_arr given_kinds ->
  repr given_targets_arr given_targets ->
  repr query_sources_arr query_sources ->
  repr query_kinds_arr query_kinds ->
  repr query_targets_arr query_targets ->
  isahasa_time_spec c1 c2 (size given_sources_arr) (size query_sources_arr) (sizes given_sources_arr) (sizes given_targets_arr) (sizes query_sources_arr) (sizes query_targets_arr) (cost6 isahasa_cost given_sources_arr given_kinds_arr given_targets_arr query_sources_arr query_kinds_arr query_targets_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
