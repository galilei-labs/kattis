(** * Bitwise *)

(** ** Description *)

(** Partition a circular sequence into a specified number of nonempty
    contiguous sections. Maximize the bitwise AND of the sections' bitwise
    ORs.

    [@kattis bitwise]
    - Difficulty: 6.2

    **Kattis Bounds**
    - 1 $\le$ section count $\le$ sequence length $\le$ 500,000.
    - Entries from 0 to $10^{9}$. *)

(** ** Examples *)

(** Kattis text input and output. *)
(* Input:
4 2
2 3 4 1
Output:
3
*)

(** ** [@hide] Environment *)

(* @function        best_and
   @signature       uint -> array uint -> uint
   @math_signature  N -> list N -> N
   @summary         [best_and section_count integers] returns the greatest
                    bitwise AND of the bitwise ORs of the sections, over the
                    divisions of the circle integers into section_count
                    contiguous non-empty sections
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The circle integers read from position start :
    integers[start], ..., integers[n-1], integers[0],
    ..., integers[start-1]. *)
Definition rotate (start : nat)
  (integers : list N) : list N :=
  skipn start integers ++ firstn start integers.

(** The power of a section : the bitwise OR of its
    integers. *)
Definition power (section : list N) : N :=
  fold_left N.lor section 0.

(** The bitwise AND of the powers of the sections (0 for
    no section, never relied on : there is at least
    one). *)
Definition and_powers (sections : list (list N)) : N :=
  match sections with
  | [] => 0
  | first :: rest =>
      fold_left
        (fun accumulated section => N.land accumulated
        (power section))
        rest (power first)
  end.

(** sections divides the circle integers into
    section_count contiguous non-empty sections : laid
    end to end, they read the circle from some position. *)
Definition division (integers : list N) (section_count : N)
  (sections : list (list N)) : Prop :=
  len sections = section_count /\
  Forall (fun section => section <> []) sections /\
  exists start, (start < List.length integers)%nat /\
    concat sections = rotate start integers.

(** [@inside best_and_correct] The statement's bounds,
    for one test case. *)
Record valid_input (section_count : N)
  (integers : list N) : Prop := {
  (* 1 <= K <= N <= 5 * 10^5 *)
  vi_k : 1 <= section_count <= len integers;
  vi_n : len integers <= 5 * 10 ^ 5;
  (* 0 <= A_i <= 10^9 *)
  vi_values : Forall
    (fun integer => integer <= 10 ^ 9) integers;
}.

(** ** Correctness *)

(** [@requirement] [@short must maximise the bitwise AND
    of the section ORs.] The answer : the value of some
    division, that no division exceeds. *)
Definition best_and_spec (section_count : N)
  (integers : list N)
  (output : N) : Prop :=
  (exists sections, division integers section_count sections
    /\
     and_powers sections = output) /\
  forall sections, division integers section_count sections
    ->
    and_powers sections <= output.

(** ** Interface *)

(** The machine-level interface.
    - Input [section_count]:
    - Input [integers]:
    - Output [output]: *)
Program best_and : uint -> array uint -> uint.

(** ** Bridge *)

(** [@requirement best_and_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented output satisfying
    [best_and_spec]. *)
Specification best_and_correct :
  forall (section_count : N) (integers : list N)
         (section_count_int : uint)
           (integers_arr : array uint),
  valid_input section_count integers ->
  repr section_count_int section_count
    -> repr integers_arr integers ->
  exists output : N,
    repr (best_and section_count_int integers_arr) output /\
    best_and_spec section_count integers output.

(** [@hide] The kernel primitives (int, array, float,
    string) and their axioms. *)
Allowed Primitive Axioms.
