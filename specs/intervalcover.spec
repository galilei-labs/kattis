(* @function        cover
   @signature       float -> float -> array float -> array float
                    -> option (array uint)
   @math_signature  R -> R -> list R -> list R -> option (list N)
   @summary         [cover a b ls rs] returns the indices of a smallest
                    selection of the intervals [ls_i, rs_i] whose union
                    contains [a, b], any one of them when several exist,
                    or None when no selection does ; the harness prints
                    the count then the indices, or "impossible"
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray Floats Reals.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side.  A float input is read as the real it denotes (repr_float),
   and the reals are compared exactly : this problem does no arithmetic
   on them, so there is no rounding and no tolerance. *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The i-th endpoint, for i < len l (0 outside, never relied on). *)
Definition get_list_R (l : list R) (i : N) : R := nth (N.to_nat i) l 0%R.

(* The k-th index listed in t, for k < len t (0 outside, never relied
   on). *)
Definition get_list_N (t : list N) (k : N) : N := nth (N.to_nat k) t 0.

(* Every listed index is the index of an interval. *)
Definition indices_valid (ls : list R) (t : list N) : Prop :=
  forall k, k < len t -> get_list_N t k < len ls.

(* x lies in the closed interval [lo, hi]. *)
Definition inside (lo hi x : R) : Prop := (lo <= x <= hi)%R.

(* Every point of [a, b] lies in one of the listed intervals. *)
Definition covers (a b : R) (ls rs : list R) (t : list N) : Prop :=
  forall x : R, inside a b x ->
    exists k, k < len t /\
      inside (get_list_R ls (get_list_N t k)) (get_list_R rs (get_list_N t k)) x.

(* t is a selection of intervals covering [a, b]. *)
Definition covering (a b : R) (ls rs : list R) (t : list N) : Prop :=
  indices_valid ls t /\ covers a b ls rs t.

(* The statement's bounds on one test case. *)
Record valid_input (a b : R) (ls rs : list R) : Prop := {
  (* A <= B *)
  vi_target : (a <= b)%R;
  (* 1 <= n <= 20 000 *)
  vi_length : 1 <= len ls <= 2 * 10 ^ 4;
  (* one right endpoint per left endpoint *)
  vi_lengths : len rs = len ls;
  (* a_i <= b_i *)
  vi_intervals : forall i, i < len ls -> (get_list_R ls i <= get_list_R rs i)%R;
  (* "at most 6 digits after the decimal point" : a property of the input
     text, gone once the harness parses it into binary64 (0.1 has no
     exact float), so it has no counterpart here.  Nothing depends on
     it : the contract only compares the values, and parsing is monotone. *)
}.

(* The answer : None when no selection covers [a, b], otherwise a
   covering selection that none is shorter than. *)
Definition cover_spec (a b : R) (ls rs : list R) (o : option (list N)) : Prop :=
  match o with
  | None => forall t, ~ covering a b ls rs t
  | Some t => covering a b ls rs t /\
              forall t', covering a b ls rs t' -> len t <= len t'
  end.

(* machine side : gets extracted *)
Program cover : float -> float -> array float -> array float -> option (array uint).

(* Glue between machine and math worlds *)
Specification cover_correct :
  forall (a b : R) (ls rs : list R) (x y : float) (xs ys : array float),
    valid_input a b ls rs -> repr x a -> repr y b -> repr xs ls -> repr ys rs ->
    exists o : option (list N), repr (cover x y xs ys) o /\ cover_spec a b ls rs o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.

(* The four classical axioms Stdlib's reals rest on: the math side is over R. *)
Allowed Axioms ClassicalDedekindReals.sig_forall_dec ClassicalDedekindReals.sig_not_dec Classical_Prop.classic FunctionalExtensionality.functional_extensionality_dep.
