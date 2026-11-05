(* @function        isahasa
   @signature       array PrimString.string -> array relkind ->
                    array PrimString.string -> array PrimString.string ->
                    array relkind -> array PrimString.string -> array bool
   @math_signature  list String.string -> list relkind -> list String.string ->
                    list String.string -> list relkind -> list String.string ->
                    list bool
   @summary         Given relationship i reads "src_i r_i dst_i" and query j
                    reads "qsrc_j qr_j qdst_j", r being is-a or has-a.
                    Answer j is true exactly when query j follows from the
                    given relationships: x is-a y iff a chain of zero or more
                    given is-a steps leads from x to y; x has-a y iff a chain
                    of given steps of either kind, at least one of them has-a,
                    does.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import Relations String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* The word r of a relationship line, "is-a" or "has-a"; the same type on
   both sides. *)
Inductive relkind := IsA | HasA.
Instance repr_relkind : Repr relkind relkind := fun x i => x = i.

(* Math side.  The relationships are three parallel lists, one per column
   of the lines "c1 r c2". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* A single-word class name: not empty, and no space, tab, newline,
   carriage return, vertical tab or form feed. *)
Definition single_word (s : string) : Prop :=
  s <> EmptyString /\
  forall k c, String.get k s = Some c ->
    ~ (N_of_ascii c = 32 \/ (9 <= N_of_ascii c <= 13)).

(* Some given line reads "x r y". *)
Definition given (src : list string) (rs : list relkind) (dst : list string)
    (r : relkind) (x y : string) : Prop :=
  exists i, nth_error src i = Some x /\ nth_error rs i = Some r /\
            nth_error dst i = Some y.

(* Some given line of either kind goes from x to y. *)
Definition any_given src rs dst (x y : string) : Prop :=
  given src rs dst IsA x y \/ given src rs dst HasA x y.

(* x is-a y: a chain of zero or more given is-a steps from x to y. *)
Definition is_a src rs dst : relation string :=
  clos_refl_trans string (given src rs dst IsA).

(* x has-a z: a chain of given steps from x to z, at least one a has-a. *)
Definition has_a src rs dst (x z : string) : Prop :=
  exists y y',
    clos_refl_trans string (any_given src rs dst) x y /\
    given src rs dst HasA y y' /\
    clos_refl_trans string (any_given src rs dst) y' z.

(* "x r y" follows from the given lines. *)
Definition follows src rs dst (r : relkind) (x y : string) : Prop :=
  match r with
  | IsA => is_a src rs dst x y
  | HasA => has_a src rs dst x y
  end.

(* The statement's guarantees, for one test case. *)
Record valid_input (src : list string) (rs : list relkind) (dst : list string)
    (qsrc : list string) (qrs : list relkind) (qdst : list string) : Prop := {
  (* 1 <= n <= 10 000, n the number of given relationships, one per line
     "c1 r c2" *)
  vi_n : 1 <= len src <= 10000;
  vi_rs_len : len rs = len src;
  vi_dst_len : len dst = len src;
  (* 1 <= m <= 10 000, m the number of queries, one per line, same format *)
  vi_m : 1 <= len qsrc <= 10000;
  vi_qrs_len : len qrs = len qsrc;
  vi_qdst_len : len qdst = len qsrc;
  (* c1 and c2 are single-word class names *)
  vi_words : Forall single_word (src ++ dst ++ qsrc ++ qdst);
  (* there will be at most 500 distinct class names in the n + m lines *)
  vi_distinct : exists names : list string, len names <= 500 /\
    forall s, In s (src ++ dst ++ qsrc ++ qdst) -> In s names;
  (* all class names in the last m lines will appear at least once in the
     initial n lines *)
  vi_query_names : forall s, In s (qsrc ++ qdst) -> In s (src ++ dst);
  (* is-a relationships can not be circular (apart from the trivial
     identity "x is-a x") *)
  vi_acyclic : forall x y,
    is_a src rs dst x y -> is_a src rs dst y x -> x = y;
}.

(* One answer per query, answer j true exactly when query j follows (all
   relationships are deduced from the n given ones). *)
Definition isahasa_spec (src : list string) (rs : list relkind)
    (dst : list string) (qsrc : list string) (qrs : list relkind)
    (qdst : list string) (o : list bool) : Prop :=
  len o = len qsrc /\
  forall j : nat, (j < List.length qsrc)%nat ->
    (nth j o false = true <->
     follows src rs dst (nth j qrs IsA) (nth j qsrc EmptyString)
             (nth j qdst EmptyString)).

Program isahasa :
  array PrimString.string -> array relkind -> array PrimString.string ->
  array PrimString.string -> array relkind -> array PrimString.string ->
  array bool.

Specification isahasa_correct :
  forall (src : list string) (rs : list relkind) (dst : list string)
         (qsrc : list string) (qrs : list relkind) (qdst : list string)
         (xsrc : array PrimString.string) (xrs : array relkind)
         (xdst : array PrimString.string) (xqsrc : array PrimString.string)
         (xqrs : array relkind) (xqdst : array PrimString.string),
  valid_input src rs dst qsrc qrs qdst ->
  repr xsrc src -> repr xrs rs -> repr xdst dst ->
  repr xqsrc qsrc -> repr xqrs qrs -> repr xqdst qdst ->
  exists o : list bool,
    repr (isahasa xsrc xrs xdst xqsrc xqrs xqdst) o /\
    isahasa_spec src rs dst qsrc qrs qdst o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
