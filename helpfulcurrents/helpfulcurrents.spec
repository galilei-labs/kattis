(** * Helpful Currents *)

(** ** Description *)

(** [helpfulcurrents row_count column_count start_column ocean_map]
    counts the distinct routes of the ship from column start_column
    of the bottom row of the map to the castle '@', a route being a
    sequence of moves, each either north onto a cell that is not '#'
    or along the current ('>' east, '<' west) of the cell the ship
    is on. It returns [Some (count mod 1000003)] when at least one
    route exists and [None] ("begin repairs") when none does. *)

(** [@kattis helpfulcurrents]
    - Difficulty: 6.9
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB *)

(** ** Examples *)

(** Kattis sample: text input and output. *)
(* 2 2 0
>@
>~ = 2 *)

(** Kattis sample: text input and output. *)
(* 3 5 1
>>@<<
>~#~<
>>>>~ = 4 *)

(** ** [@hide] Environment *)
(* @function        helpfulcurrents
   @signature       uint -> uint -> uint -> array PrimString.string -> option uint
   @math_signature  N -> N -> N -> list String.string -> option N
   @summary         [helpfulcurrents row_count column_count start_column
                    ocean_map] counts the distinct routes of the ship from
                    column start_column of the bottom row of the map to
                    the castle '@', a route being a sequence of moves, each
                    either north onto a cell that is not '#' or along the
                    current ('>' east, '<' west) of the cell the ship is on.
                    It returns [Some (count mod 1000003)] when at least one
                    route exists and [None] ("begin repairs") when none does.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** Math side. The map is the list of its row_count rows, row 0 the
    northernmost (the first line of the input), the ship starting on
    row row_count - 1. The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The character in column column of row row ('#' outside the map). *)
Definition cell (ocean_map : list string)
  (row column : N) : ascii :=
  match String.get (N.to_nat column)
          (nth (N.to_nat row) ocean_map EmptyString) with
  | Some character => character
  | None => "#"%char
  end.

(** The [in_map] definition. *)
Definition in_map
  (row_count column_count row column : N) : Prop :=
  row < row_count /\ column < column_count.

(** The two moves of the statement: north (lowering the sails), or along
    the current of the cell the ship is on (retracting them). *)
Inductive move := North | Current.

(** One move from (row, column): none from the castle, where the route
    ends; north onto row row - 1 unless the ship is on row 0 or that
    cell is '#'; along the current, east on '>' and west on '<',
    none on any other cell. *)
Definition step (ocean_map : list string) (position : N * N)
    (direction : move) : option (N * N) :=
  let '(row, column) := position in
  let character := cell ocean_map row column in
  if Ascii.eqb character "@"%char then None
  else match direction with
  | North =>
      if orb (row =? 0) (Ascii.eqb (cell ocean_map (row - 1)
        column) "#"%char)
      then None
      else Some (row - 1, column)
  | Current =>
      if Ascii.eqb character ">"%char then Some (row, column
        + 1)
      else if Ascii.eqb character "<"%char then Some (row,
        column - 1)
      else None
  end.

(** The cell reached from position by the moves of moves, if every move
    is possible. *)
Fixpoint run (ocean_map : list string) (position : N * N)
    (moves : list move) : option (N * N) :=
  match moves with
  | [] => Some position
  | direction :: moves' =>
      match step ocean_map position direction with
      | None => None
      | Some next => run ocean_map next moves'
      end
  end.

(** moves takes the ship from column start_column of the bottom row to
    the castle. *)
Definition is_route (row_count start_column : N)
  (ocean_map : list string)
    (moves : list move) : Prop :=
  exists arrival, run ocean_map (row_count - 1,
    start_column) moves =
            Some arrival /\
            cell ocean_map (fst arrival) (snd arrival) =
              "@"%char.

(** There are exactly total routes. *)
Definition route_count (row_count start_column : N)
    (ocean_map : list string) (total : N) : Prop :=
  exists routes, NoDup routes /\ len routes = total /\
    forall moves, In moves routes <->
                  is_route row_count start_column ocean_map
            moves.

(** [@inside helpfulcurrents_correct] The statement's bounds and
    guarantees. *)
Record valid_input (row_count column_count start_column : N)
    (ocean_map : list string) : Prop := {
  (* 0 < Y <= 300 (row_count) *)
  vi_Y : 0 < row_count <= 300;
  (* 0 <= x_init < X <= 50 000 (start_column,
     column_count) *)
  vi_X : start_column < column_count <= 50000;
  (* Then follow Y rows, each with X characters each *)
  vi_rows : len ocean_map = row_count;
  vi_cols : Forall (fun line => N.of_nat (String.length
    line) = column_count)
              ocean_map;
  (* All characters C_{x,y} is one of '~', '#', '@', '>'
     and '<' *)
  vi_chars : forall row column,
    in_map row_count column_count row column ->
    In (cell ocean_map row column)
       ["~"%char; "#"%char; "@"%char; ">"%char; "<"%char];
  (* If C_{x,y} = '>', then x+1 < X and C_{x+1,y} is not
     '<' nor '#' *)
  vi_east : forall row column,
    in_map row_count column_count row column ->
    cell ocean_map row column = ">"%char ->
    column + 1 < column_count /\
    cell ocean_map row (column + 1) <> "<"%char /\
    cell ocean_map row (column + 1) <> "#"%char;
  (* If C_{x,y} = '<', then 0 <= x-1 and C_{x-1,y} is not
     '>' nor '#' *)
  vi_west : forall row column,
    in_map row_count column_count row column ->
    cell ocean_map row column = "<"%char ->
    1 <= column /\
    cell ocean_map row (column - 1) <> ">"%char /\
    cell ocean_map row (column - 1) <> "#"%char;
  (* There is exactly one '@' tile on the map *)
  vi_castle : exists castle_row castle_column,
    in_map row_count column_count castle_row castle_column
      /\
    cell ocean_map castle_row castle_column = "@"%char /\
    forall row column, in_map row_count column_count row
      column ->
      cell ocean_map row column = "@"%char ->
      row = castle_row /\ column = castle_column;
  (* The boat will not start on a '#' tile *)
  vi_start : cell ocean_map (row_count - 1) start_column <>
    "#"%char;
}.

(** ** Correctness *)

(** [@requirement] [@short None is "begin repairs": there is no route.
    Some total_mod: there are    total > 0 routes, and total_mod is
    total modulo 1 000 003.] None is "begin repairs": there is no
    route. Some total_mod: there are total > 0 routes, and total_mod
    is total modulo 1 000 003. *)
Definition helpfulcurrents_spec
  (row_count column_count start_column : N)
    (ocean_map : list string) (output : option N) : Prop :=
  match output with
  | None => forall moves, ~ is_route row_count start_column
    ocean_map moves
  | Some total_mod =>
      exists total, 0 < total /\
        route_count row_count start_column ocean_map total
          /\
        total_mod = total mod 1000003
  end.

(** ** Interface *)

(** The [helpfulcurrents] program on machine values.
    - Input [row_count]:
    - Input [column_count]:
    - Input [start_column]:
    - Input [ocean_map]:
    - Output [output]: *)
Program helpfulcurrents :
  uint -> uint -> uint -> array PrimString.string ->
    option uint.

(** ** Bridge *)

(** [@requirement helpfulcurrents_spec] [@fold full correctness
    statement] On valid represented inputs, [helpfulcurrents]
    returns a represented output satisfying [helpfulcurrents_spec]. *)
Specification helpfulcurrents_correct :
  forall (row_count column_count start_column : N)
    (ocean_map : list string)
         (row_count_int column_count_int start_column_int :
           uint)
         (ocean_map_arr : array PrimString.string),
  valid_input row_count column_count start_column ocean_map
    ->
  repr row_count_int row_count ->
    repr column_count_int column_count ->
  repr start_column_int start_column ->
    repr ocean_map_arr ocean_map ->
  exists output : option N,
    repr (helpfulcurrents row_count_int column_count_int
      start_column_int
            ocean_map_arr) output /\
    helpfulcurrents_spec row_count column_count start_column
      ocean_map
      output.

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
