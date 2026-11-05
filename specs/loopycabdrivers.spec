(* @function        loopy_regions
   @signature       array PrimString.string -> array PrimString.string ->
                    array (array PrimString.string) * array PrimString.string
   @math_signature  list String.string -> list String.string ->
                    list (list String.string) * list String.string
   @summary         Given the one-way streets of a city as two parallel lists
                    of store names (street k goes from src_k to dst_k),
                    [loopy_regions src dst] returns the groups of two or more
                    stores that can be visited together indefinitely (each
                    reaches every other one and back), each group in
                    lexicographic order and the groups in lexicographic order,
                    and, in lexicographic order, the stores in no group.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii Relations Sorting.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The input lines are two parallel lists, one per column
   (line k is "src_k dst_k"). *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of characters of s. *)
Definition slen (s : string) : N := N.of_nat (String.length s).

(* Every character of s is a letter, a-z or A-Z. *)
Definition letters (s : string) : Prop :=
  forall k c, String.get k s = Some c ->
    (65 <= N_of_ascii c <= 90) \/ (97 <= N_of_ascii c <= 122).

(* Lexicographic order: character codes, a proper prefix first ('Z' < 'a'). *)
Definition str_lt (a b : string) : Prop := String.compare a b = Lt.

(* Lexicographic order on lists of names, element by element, a proper
   prefix first. *)
Fixpoint lex_lt (u v : list string) : Prop :=
  match u, v with
  | _, [] => False
  | [], _ :: _ => True
  | x :: u', y :: v' => str_lt x y \/ (x = y /\ lex_lt u' v')
  end.

(* One can drive from a to b along one street. *)
Definition street (src dst : list string) (a b : string) : Prop :=
  In (a, b) (combine src dst).

(* a is a store of the city: it is named on some input line. *)
Definition store (src dst : list string) (a : string) : Prop :=
  In a src \/ In a dst.

(* One can drive from a to b along zero or more streets. *)
Definition reaches (src dst : list string) : string -> string -> Prop :=
  clos_refl_trans string (street src dst).

(* a and b can be visited together indefinitely. *)
Definition together (src dst : list string) (a b : string) : Prop :=
  reaches src dst a b /\ reaches src dst b a.

(* a can be visited indefinitely in conjunction with at least one other
   store. *)
Definition loopy (src dst : list string) (a : string) : Prop :=
  exists b, b <> a /\ together src dst a b.

(* g is a group: two or more stores, exactly those that can be visited
   together with one of them. *)
Definition group (src dst : list string) (g : list string) : Prop :=
  2 <= len g /\ exists a, forall b, In b g <-> together src dst a b.

Record valid_input (src dst : list string) : Prop := {
  (* a line containing an integer 0 <= n <= 10 000 *)
  vi_n : len src <= 10000;
  (* following this are n lines, each containing a pair of store names *)
  vi_lines : len src = len dst;
  (* every name is a sequence of between 1 and 20 letters (a-z, A-Z) *)
  vi_src_names : Forall (fun s => 1 <= slen s <= 20 /\ letters s) src;
  vi_dst_names : Forall (fun s => 1 <= slen s <= 20 /\ letters s) dst;
  (* A <> B *)
  vi_distinct : Forall2 (fun a b => a <> b) src dst;
  (* no pair of stores is listed more than once *)
  vi_no_repeat : NoDup (combine src dst);
}.

(* The "okay" lines are the groups, each in lexicographic order, the groups
   in lexicographic order, every store that belongs to a group listed in
   one; the "avoid" line is, in lexicographic order, every store in no
   group. *)
Definition loopy_regions_spec (src dst : list string)
    (o : list (list string) * list string) : Prop :=
  let (groups, avoid) := o in
  (forall g, In g groups -> group src dst g /\ StronglySorted str_lt g) /\
  (forall a, loopy src dst a -> exists g, In g groups /\ In a g) /\
  StronglySorted lex_lt groups /\
  StronglySorted str_lt avoid /\
  (forall a, In a avoid <-> store src dst a /\ ~ loopy src dst a).

Program loopy_regions :
  array PrimString.string -> array PrimString.string ->
  array (array PrimString.string) * array PrimString.string.

Specification loopy_regions_correct :
  forall (src dst : list string) (x y : array PrimString.string),
  valid_input src dst -> repr x src -> repr y dst ->
  exists o : list (list string) * list string,
    repr (loopy_regions x y) o /\ loopy_regions_spec src dst o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
