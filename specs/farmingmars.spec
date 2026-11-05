(* @function        farmingmars
   @signature       array float -> array uint -> array uint -> array bool
   @math_signature  list R -> list N -> list N -> list bool
   @summary         [farmingmars ph ls rs] answers the m queries
                    [ls_j, rs_j] (acres numbered from 1, both ends
                    included) on the strip whose acre i has pH ph_i: answer
                    j is true ("usable") exactly when some pH value is
                    shared by a strict majority, floor((r-l+1)/2) + 1, of
                    the acres l..r, and false ("unusable") otherwise. pH
                    values are compared exactly, as the reals they denote.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  The pH of an acre is the real its float denotes; the
   queries are two parallel lists, one per column of the lines "l r". *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The k-th element of l, for k < len l (0 outside, never relied on). *)
Definition get_list_N (l : list N) (k : N) : N := nth (N.to_nat k) l 0.

(* The acres l..r of the strip, acres numbered from 1. *)
Definition acres (ph : list R) (l r : N) : list R :=
  firstn (N.to_nat (r - l + 1)) (skipn (N.to_nat (l - 1)) ph).

(* The number of acres of the list whose pH is exactly v. *)
Definition count_ph (v : R) (xs : list R) : N :=
  len (filter (fun x => if Req_EM_T x v then true else false) xs).

(* Some pH value is shared by a strict majority floor((r-l+1)/2) + 1 of
   the acres l..r. *)
Definition usable (ph : list R) (l r : N) : Prop :=
  exists v : R, (r - l + 1) / 2 + 1 <= count_ph v (acres ph l r).

(* The statement's bounds.  "Exactly six decimal digits" is a property of
   the input text, gone once parsed: the contract is exact on the reals
   the parsed floats denote. *)
Record valid_input (ph : list R) (ls rs : list N) : Prop := {
  (* 1 <= n <= 10 000: the size of the strip of land *)
  vi_n : 1 <= len ph <= 10000;
  (* 1 <= m <= 10 000: the number of queries *)
  vi_m : 1 <= len ls <= 10000;
  (* m lines containing two space-separated integers each *)
  vi_rs : len rs = len ls;
  (* Each pH value lies between 0.000000 and 14.000000, inclusive *)
  vi_ph : Forall (fun p => (0 <= p <= 14)%R) ph;
  (* 1 <= l_j <= r_j <= n *)
  vi_lr : forall j, j < len ls ->
    1 <= get_list_N ls j <= get_list_N rs j /\ get_list_N rs j <= len ph;
}.

(* One answer per query, in query order: true iff the interval is usable. *)
Definition farmingmars_spec (ph : list R) (ls rs : list N) (o : list bool)
  : Prop :=
  len o = len ls /\
  forall j, j < len ls ->
    (nth (N.to_nat j) o false = true <->
     usable ph (get_list_N ls j) (get_list_N rs j)).

Program farmingmars : array float -> array uint -> array uint -> array bool.

Specification farmingmars_correct :
  forall (ph : list R) (ls rs : list N) (p : array float) (x y : array uint),
    valid_input ph ls rs -> repr p ph -> repr x ls -> repr y rs ->
    exists o : list bool, repr (farmingmars p x y) o /\
                          farmingmars_spec ph ls rs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
