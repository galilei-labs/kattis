(** * Is-A? Has-A? Who Knowz-A? *)

(** ** Description *)

(** Answer reachability queries on is-a and has-a relationships. An is-a
    query requires only is-a edges; a has-a query allows both edge types but
    requires at least one has-a edge.

    [@kattis isahasa]
    - Difficulty: 6.4
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - 1 to 10000 given relationships and 1 to 10000 queries.
    - At most 500 distinct class names; query names occur in the given
      relationships.
    - No nontrivial is-a cycles. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Relations String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The word r of a relationship line, "is-a" or "has-a"; the same type
    on both sides. *)
Inductive relkind := IsA | HasA.
Instance repr_relkind : Repr relkind relkind :=
  fun kind kind' => kind = kind'.

(** Math side. The relationships are three parallel lists, one per
    column of the lines "c1 r c2" (given_sources, given_kinds,
    given_targets). The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** A single-word class name: not empty, and no space, tab, newline,
    carriage return, vertical tab or form feed. *)
Definition single_word (name : string) : Prop :=
  name <> EmptyString /\
  forall k character, String.get k name = Some character ->
    ~ (N_of_ascii character = 32 \/ (9 <= N_of_ascii
      character <= 13)).

(** Some given line reads "from_class kind to_class". *)
Definition given (given_sources : list string)
  (given_kinds : list relkind)
    (given_targets : list string) (kind : relkind)
    (from_class to_class : string) : Prop :=
  exists i, nth_error given_sources i = Some from_class /\
            nth_error given_kinds i = Some kind /\
            nth_error given_targets i = Some to_class.

(** Some given line of either kind goes from from_class to to_class. *)
Definition any_given given_sources given_kinds given_targets
    (from_class to_class : string) : Prop :=
  given given_sources given_kinds given_targets IsA
    from_class to_class \/
  given given_sources given_kinds given_targets HasA
    from_class to_class.

(** from_class is-a to_class: a chain of zero or more given is-a steps
    from from_class to to_class. *)
Definition is_a given_sources given_kinds given_targets :
  relation string :=
  clos_refl_trans string (given given_sources given_kinds
    given_targets IsA).

(** from_class has-a to_class: a chain of given steps from from_class to
    to_class, at least one a has-a (from has_owner to has_part). *)
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

(** "from_class kind to_class" follows from the given lines. *)
Definition follows given_sources given_kinds given_targets
  (kind : relkind)
    (from_class to_class : string) : Prop :=
  match kind with
  | IsA => is_a given_sources given_kinds given_targets
    from_class to_class
  | HasA => has_a given_sources given_kinds given_targets
    from_class to_class
  end.

(** [@inside isahasa_correct] The statement's guarantees, for one test
    case. *)
Record valid_input (given_sources : list string)
    (given_kinds : list relkind) (given_targets : list
      string)
    (query_sources : list string) (query_kinds : list
      relkind)
    (query_targets : list string) : Prop := {
  (* 1 <= n <= 10 000, n the number of given
     relationships, one per line "c1 r c2" *)
  vi_n : 1 <= len given_sources <= 10000;
  vi_rs_len : len given_kinds = len given_sources;
  vi_dst_len : len given_targets = len given_sources;
  (* 1 <= m <= 10 000, m the number of queries, one per
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

(** [@requirement] [@short One answer per query, answer j true exactly
    when query j follows (all    relationships are deduced from the
    n given ones).] One answer per query, answer j true exactly when
    query j follows (all relationships are deduced from the n given
    ones). *)
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

(** ** Interface *)

(** The [isahasa] program on machine values.
    - Output [output]: *)
Program isahasa :
  array PrimString.string -> array relkind ->
    array PrimString.string ->
  array PrimString.string -> array relkind ->
    array PrimString.string ->
  array bool.

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

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
