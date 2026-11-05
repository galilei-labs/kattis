(* @function        joinstrings
   @signature       array PrimString.string -> array uint -> array uint ->
                    PrimString.string
   @math_signature  list String.string -> list N -> list N -> String.string
   @summary         [joinstrings s a b] executes, in order, the N-1
                    operations of the statement on the N strings
                    S_1..S_N = s: the i-th operation (1-based indices a_i,
                    b_i) sets S_(a_i) := S_(a_i) ++ S_(b_i), then
                    S_(b_i) := "". It returns the one string that remains
                    at the end, the S_r whose index r is no b_i.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Stdlib Require Import String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Types: the N-1 operation lines "a b" are two parallel arrays, a_i and
   b_i, kept 1-based as in the statement. *)

(* Math side.  The strings S_1..S_N are a list, S_k at position k - 1. *)

Definition len {A} (l : list A) : N := N.of_nat (List.length l).
Definition slen (t : string) : N := N.of_nat (String.length t).

(* S_k, 1-based. *)
Definition str (st : list string) (k : N) : string :=
  nth (N.to_nat (k - 1)) st ""%string.

(* st with S_k (1-based) replaced by t. *)
Definition set_str (st : list string) (k : N) (t : string) : list string :=
  firstn (N.to_nat (k - 1)) st ++ t :: skipn (N.to_nat k) st.

(* One operation "x y": S_x := S_x + S_y, then S_y := "". *)
Definition join (st : list string) (x y : N) : list string :=
  set_str (set_str st x (str st x ++ str st y)) y ""%string.

(* The strings after all the operations, executed in the order given. *)
Definition run (s : list string) (a b : list N) : list string :=
  fold_left (fun st op => join st (fst op) (snd op)) (combine a b) s.

(* Every character of t is a lowercase letter 'a'..'z'. *)
Definition lowercase (t : string) : Prop :=
  forall k c, String.get k t = Some c -> 97 <= N_of_ascii c <= 122.

(* The total number of characters over all the strings. *)
Definition total (s : list string) : N := fold_right N.add 0 (map slen s).

Record valid_input (s : list string) (a b : list N) : Prop := {
  (* 1 <= N <= 10^5 *)
  vi_n : 1 <= len s <= 10 ^ 5;
  (* N non-empty strings *)
  vi_nonempty : Forall (fun t => 1 <= slen t) s;
  (* all the characters are lowercase alphabets from 'a' to 'z' *)
  vi_lower : Forall lowercase s;
  (* the total number of characters over all the strings is at most 10^6 *)
  vi_total : total s <= 10 ^ 6;
  (* N - 1 operations *)
  vi_len_a : len a = len s - 1;
  vi_len_b : len b = len s - 1;
  (* 1 <= a, b <= N *)
  vi_a : Forall (fun x => 1 <= x <= len s) a;
  vi_b : Forall (fun y => 1 <= y <= len s) b;
  (* a <> b *)
  vi_neq : forall i, (i < List.length a)%nat -> nth i a 0 <> nth i b 0;
  (* after the i-th operation, no future operation accesses S_b *)
  vi_future : forall i j, (i < j)%nat -> (j < List.length a)%nat ->
    nth j a 0 <> nth i b 0 /\ nth j b 0 <> nth i b 0;
}.

(* The answer: S_r after all the operations, r being the index that no
   operation empties. *)
Definition joinstrings_spec (s : list string) (a b : list N) (o : string)
    : Prop :=
  exists r, 1 <= r <= len s /\ ~ In r b /\ o = str (run s a b) r.

Program joinstrings :
  array PrimString.string -> array uint -> array uint -> PrimString.string.

Specification joinstrings_correct :
  forall (s : list string) (a b : list N)
         (xs : array PrimString.string) (xa xb : array uint),
  valid_input s a b -> repr xs s -> repr xa a -> repr xb b ->
  exists o : string, repr (joinstrings xs xa xb) o /\
                     joinstrings_spec s a b o.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
