(** * Remainder Reminder *)

(** ** Description *)

(** Recover the unique number of books from the
    remainders left when packing them into the three
    largest distinct boxes foldable from a rectangular
    sheet.

    [@kattis remainderreminder]
    - Difficulty: 5.1
    - CPU time limit: 1 second
    - Memory limit: 1024 MB *)

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
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. A book is a 1-inch cube, so a box holds as
   many books as its volume in cubic inches. *)

(** ** Definitions *)

(** Cutting cut-by-cut squares at the corners of a
    [sheet_width]-by-[sheet_length] sheet folds a box of
    integer dimensions cut, [sheet_width] - 2 cut,
    [sheet_length] - 2 cut, all at least 1. *)
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

(** largest_volume > second_volume > third_volume are the
    three largest distinct box sizes. *)
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

(** [books] books fit everything Bill remembers: books
    lies in [min_books, max_books] and leaves
    [left_largest], [left_second], [left_third] books
    over with the largest, second and third largest box
    size. *)
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

(** [@inside remainderreminder_correct] The statement's
    bounds. *)
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

(** [@requirement] [@short Recover the unique number of
    books from the remainders left when packing them into
    the three largest distinct boxes foldable from a
    rectangular sheet.] The answer is the one
    [consistent] number of books. *)
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

(** ** Interface *)

(** Recover the unique number of books from the
    remainders left when packing them into the three
    largest distinct boxes foldable from a rectangular
    sheet.
    - Input [sheet_width]:
    - Input [sheet_length]:
    - Input [left_largest]:
    - Input [left_second]:
    - Input [left_third]:
    - Input [min_books]:
    - Input [max_books]:
    - Output [output]: *)
Program remainderreminder :
  uint -> uint -> uint -> uint -> uint -> uint -> uint ->
    uint.

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

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
