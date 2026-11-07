(* @function        inversions
   @signature       array uint -> uint
   @math_signature  list N -> N
   @summary         [inversions sequence] returns the number of pairs of
                    positions i < j of sequence such that
                    sequence[j] < sequence[i]
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(* The number of elements of l. *)
Definition len {A} (l : list A) : N := N.of_nat (List.length l).

(* The number of elements of values smaller than pivot. *)
Definition count_lt (pivot : N) (values : list N) : nat :=
  List.length (filter (fun value => value <? pivot) values).

(* The number of pairs of positions i < j whose values are in decreasing
   order. *)
Fixpoint inv_list (values : list N) : nat :=
  match values with
  | [] => 0%nat
  | first :: rest => (count_lt first rest + inv_list rest)%nat
  end.

(* The statement's bounds. *)
Record valid_input (sequence : list N) : Prop := {
  (* 1 <= n <= 500000 *)
  vi_length : 1 <= len sequence <= 5 * 10 ^ 5;
  (* 0 <= a[i] <= 999999999 *)
  vi_values : Forall (fun element => element <= 10 ^ 9 - 1) sequence;
  (* the integers are distinct *)
  vi_distinct : NoDup sequence;
}.

(* The result is the number of inversions. *)
Definition inversions_spec (sequence : list N) (output : N) : Prop :=
  output = N.of_nat (inv_list sequence).

(* machine side : the only thing that gets extracted *)
Program inversions : array uint -> uint.

(* the one line : repr on the input (universal), repr on the output
   (existential) *)
Specification inversions_correct :
  forall (sequence : list N) (sequence_arr : array uint),
  valid_input sequence -> repr sequence_arr sequence ->
  exists output : N,
    repr (inversions sequence_arr) output /\
    inversions_spec sequence output.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
