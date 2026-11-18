(** * Remainder Reminder *)

(** ** Description *)

(** Fold open boxes from a rectangular sheet of width $a$ and length $b$
    by cutting a square of integer side $x$ from each corner. The box volume
    is $x(a-2x)(b-2x)$, with $x > 0$, $2x < a$, and $2x < b$. Use the three
    largest distinct possible volumes as moduli. Find the unique integer in
    the given interval with the specified remainders modulo those volumes.

    [@kattis remainderreminder]
    - Difficulty: 5.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Sheet dimensions: $7 \le a \le b \le 100$.
    - Each remainder satisfies $1 \le r \le 10^{9}$.
    - Search interval endpoints satisfy $1 \le \text{lower} < \text{upper} \le 10^{9}$;
      exactly one answer exists. *)

(** ** Examples *)

(** - Input convention: Sheet dimensions, three remainders in descending box-volume order, then lower and upper bounds.
    - Output convention: The unique integer satisfying the interval and congruence constraints. *)
(* Input:
16 21 407 409 17 20000 30000
Output:
22457
*)

(** ** [@hide] Environment *)

(* @function        remainderreminder
   @signature       uint -> uint -> uint -> uint -> uint -> uint -> uint -> uint
   @math_signature  N -> N -> N -> N -> N -> N -> N -> N
   @summary         [remainderreminder sheet_width sheet_length
                    left_largest left_second left_third min_books
                    max_books] is the number of books,
                    min_books <= books <= max_books, that leaves
                    left_largest, left_second and left_third books over
                    when packed in boxes of the largest, second largest
                    and third largest of the distinct volumes of the open
                    boxes foldable from a sheet_width-by-sheet_length sheet
                    by cutting equal integer squares at the four corners.
                    The input guarantees that exactly one such number of
                    books exists.
                    It runs in at most c1 * (a + log2 b + 1) + c2 steps of
                    the cost model on a valid input, a and b the sheet
                    dimensions (one pass over the corner cuts, then the
                    extended Euclidean algorithm on the volumes), for two
                    constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* A book is a 1-inch cube, so a box holds as
   many books as its volume in cubic inches. *)

(** ** Definitions *)

(** Removing squares of side [cut] from each corner leaves a box whose three integer
    dimensions are positive. *)
Definition cut_ok (sheet_width sheet_length cut : N) : Prop
  :=
  1 <= cut /\ 2 * cut < sheet_width /\ 2 * cut <
    sheet_length.

(** [volume] is the volume of some box foldable from the
    sheet. *)
Definition box_size (sheet_width sheet_length volume : N) :
  Prop :=
  exists cut, cut_ok sheet_width sheet_length cut /\
    volume = cut * (sheet_width - 2 * cut) *
      (sheet_length - 2 * cut).

(** [largest_volume], [second_volume], and [third_volume] are the three largest
    distinct box volumes, in decreasing order. *)
Definition three_largest (sheet_width sheet_length : N)
    (largest_volume second_volume third_volume : N) : Prop
      :=
  box_size sheet_width sheet_length largest_volume /\
  box_size sheet_width sheet_length second_volume /\
  box_size sheet_width sheet_length third_volume /\
  third_volume < second_volume < largest_volume /\
  forall volume, box_size sheet_width sheet_length volume ->
    volume = largest_volume \/ volume = second_volume \/
    volume = third_volume \/ volume < third_volume.

(** [books] lies between [min_books] and [max_books], inclusive, and has the
    specified remainders modulo the three largest distinct box volumes. *)
Definition consistent (sheet_width sheet_length : N)
    (left_largest left_second left_third min_books max_books
      books : N)
    : Prop :=
  min_books <= books <= max_books /\
  exists largest_volume second_volume third_volume,
    three_largest sheet_width sheet_length
      largest_volume second_volume third_volume /\
    books mod largest_volume = left_largest /\
    books mod second_volume = left_second /\
    books mod third_volume = left_third.

(** [@inside remainderreminder_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (sheet_width sheet_length : N)
    (left_largest left_second left_third min_books max_books
      : N) : Prop := {
  (* a <= b, 7 <= a, b <= 100 *)
  vi_ab : sheet_width <= sheet_length;
  vi_a : 7 <= sheet_width <= 100;
  vi_b : 7 <= sheet_length <= 100;
  (* 1 <= c, d, e <= 10^9 *)
  vi_c : 1 <= left_largest <= 10 ^ 9;
  vi_d : 1 <= left_second <= 10 ^ 9;
  vi_e : 1 <= left_third <= 10 ^ 9;
  (* 1 <= f < g <= 10^9 *)
  vi_fg : 1 <= min_books < max_books;
  vi_g : max_books <= 10 ^ 9;
  (* Each problem is guaranteed to have a unique answer. *)
  vi_unique : exists! books,
    consistent sheet_width sheet_length
      left_largest left_second left_third min_books
        max_books books;
}.

(** ** Correctness *)

(** [@requirement]
    The output is the unique integer within the given bounds satisfying the three
    congruences defined by the largest distinct box volumes. *)
Definition remainderreminder_spec
  (sheet_width sheet_length : N)
  (left_largest left_second left_third min_books max_books :
    N)
  (output : N)
  : Prop :=
  forall books,
    consistent sheet_width sheet_length
      left_largest left_second left_third min_books
        max_books books <->
    books = output.

(** ** Complexity *)

(** [@requirement] Runs in $O(W+\log(L+2))$ steps, where $W$ and $L$ are the sheet width and length. *)
Definition remainderreminder_time_spec (c1 c2 n_sheet_width n_sheet_length steps : nat) : Prop :=
  (steps <= c1 * (n_sheet_width + Nat.log2 (n_sheet_length) + 1) + c2)%nat.

(** ** Interface *)

(** Find the three largest distinct volumes of boxes foldable from the sheet
    by removing equal integer-sized corner squares. Return the unique integer
    within the supplied bounds having the given remainder modulo each volume.
    - Input [sheet_width]: Shorter side of the rectangular sheet.
    - Input [sheet_length]: Longer side of the rectangular sheet.
    - Input [left_largest]: Remainder modulo the largest available box volume.
    - Input [left_second]: Remainder modulo the second-largest distinct box volume.
    - Input [left_third]: Remainder modulo the third-largest distinct box volume.
    - Input [min_books]: Inclusive lower bound for the unknown integer.
    - Input [max_books]: Inclusive upper bound for the unknown integer.
    - Output [output]: The output is the unique integer within the given bounds satisfying the three congruences defined by the largest distinct box volumes. *)
Program remainderreminder :
  uint -> uint -> uint -> uint -> uint -> uint -> uint ->
    uint.

(** [@example remainderreminder]
    - Sample: 1
    - Input [sheet_width]: 16
    - Input [sheet_length]: 21
    - Input [left_largest]: 407
    - Input [left_second]: 409
    - Input [left_third]: 17
    - Input [min_books]: 20000
    - Input [max_books]: 30000
    - Output [output]: 22457
*)

(** ** Bridge *)

(** [@requirement remainderreminder_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [remainderreminder_spec]. *)
Specification remainderreminder_correct :
  forall (sheet_width sheet_length : N)
         (left_largest left_second left_third min_books
           max_books : N)
         (sheet_width_int sheet_length_int : uint)
         (left_largest_int left_second_int left_third_int :
           uint)
         (min_books_int max_books_int : uint),
  valid_input sheet_width sheet_length
    left_largest left_second left_third min_books max_books
      ->
  repr sheet_width_int sheet_width -> repr sheet_length_int
    sheet_length ->
  repr left_largest_int left_largest -> repr left_second_int
    left_second ->
  repr left_third_int left_third ->
  repr min_books_int min_books -> repr max_books_int
    max_books ->
  exists output : N,
    repr (remainderreminder sheet_width_int sheet_length_int
            left_largest_int left_second_int left_third_int
            min_books_int max_books_int) output /\
    remainderreminder_spec sheet_width sheet_length
      left_largest left_second left_third min_books
        max_books output.

(** ** Complexity *)

(** [@hide] [remainderreminder_cost] is the cost translation of [remainderreminder] (the judge
    recomputes it and compares) ... *)
Complexity remainderreminder_cost for remainderreminder.

(** [@fold complexity bound] ... and runs in at most c1 * (a + log2 b + 1) + c2 steps of the cost model on a valid input, a and b the sheet dimensions (one pass over the corner cuts, then the extended Euclidean algorithm on the volumes), for two constants
    quantified before the inputs, on every valid input. [@requirement remainderreminder_time_spec] *)
Specification remainderreminder_time : exists c1 c2 : nat,
  forall (sheet_width sheet_length : N)
  (left_largest left_second left_third min_books
  max_books : N)
  (sheet_width_int sheet_length_int : uint)
  (left_largest_int left_second_int left_third_int :
  uint)
  (min_books_int max_books_int : uint),
  valid_input sheet_width sheet_length
  left_largest left_second left_third min_books max_books
  ->
  repr sheet_width_int sheet_width -> repr sheet_length_int
  sheet_length ->
  repr left_largest_int left_largest -> repr left_second_int
  left_second ->
  repr left_third_int left_third ->
  repr min_books_int min_books -> repr max_books_int
  max_books ->
  remainderreminder_time_spec c1 c2 (size sheet_width_int) (size sheet_length_int) (cost7 remainderreminder_cost sheet_width_int sheet_length_int left_largest_int left_second_int left_third_int min_books_int max_books_int).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
