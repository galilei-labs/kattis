(** * Helpful Currents *)

(** ** Description *)

(** Count paths through a grid from a given bottom-row cell to a
    castle. Each move goes north or follows the current cell's
    horizontal arrow, avoiding obstacles. Return the count modulo $10^{6} + 3$,
    distinguishing an unreachable castle. The map uses ~ for open water,
    # for obstacles, @ for the castle, and > or < for horizontal currents.

    [@kattis helpfulcurrents]
    - Difficulty: 6.9
    - CPU time limit: 3 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Row count: $1 \le Y \le 300$; column count: $1 \le X \le 5 \times 10^{4}$.
    - Exactly one castle; the start is not an obstacle.
    - Arrows stay within the grid and point to neither an obstacle nor an
      opposing arrow. *)

(** ** Examples *)

(** - Input convention: Grid dimensions and starting column, followed by rows using ~, #, @, > and <.
    - Output convention: Path count modulo $10^{6} + 3$, or begin repairs if the castle is unreachable. *)
(* Input:
2 2 0
>@
>~
Output:
2
*)

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
                    It runs in at most c1 * (Y + 1) * (X + 1) + c2 steps of
                    the cost model on a valid input, Y and X the dimensions
                    of the map (one row of counts at a time, the chains
                    propagated in two passes), for two constants c1, c2.
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray
  String Ascii.
From Stdlib Require PrimString.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The character at zero-based position [(row, column)] in [ocean_map], or the wall
    marker outside the map. *)
Definition cell (ocean_map : list string)
  (row column : N) : ascii :=
  match String.get (N.to_nat column)
          (nth (N.to_nat row) ocean_map EmptyString) with
  | Some character => character
  | None => "#"%char
  end.

(** The zero-based coordinates [row] and [column] are within the map dimensions. *)
Definition in_map
  (row_count column_count row column : N) : Prop :=
  row < row_count /\ column < column_count.

(** A permitted step moves north or follows the current cell's horizontal arrow. *)
Inductive move := North | Current.

(** Apply one move from [(row, column)]. No move leaves the castle. North is allowed
    only within the map and into a non-wall cell; horizontal movement follows the
    current cell's arrow. *)
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

(** Follow [moves] from [position], returning the final cell if every move is
    permitted. *)
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

(** [moves] leads from [start_column] of the bottom row to the castle. *)
Definition is_route (row_count start_column : N)
  (ocean_map : list string)
    (moves : list move) : Prop :=
  exists arrival, run ocean_map (row_count - 1,
    start_column) moves =
            Some arrival /\
            cell ocean_map (fst arrival) (snd arrival) =
              "@"%char.

(** Exactly [total] distinct move sequences are valid routes to the castle. *)
Definition route_count (row_count start_column : N)
    (ocean_map : list string) (total : N) : Prop :=
  exists routes, NoDup routes /\ len routes = total /\
    forall moves, In moves routes <->
                  is_route row_count start_column ocean_map
            moves.

(** [@inside helpfulcurrents_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (row_count column_count start_column : N)
    (ocean_map : list string) : Prop := {
  (* 0 < Y <= 300 (row_count) *)
  vi_Y : 0 < row_count <= 300;
  (* 0 <= x_init < X <= 5 * 10^4 (start_column,
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

(** [@requirement]
    The output is the number of permitted paths to the castle modulo $10^{6} + 3$,
    or [None] exactly when no path exists. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((r+1)(c+1))$ steps, where $r$ and $c$ are the map's row and column counts. *)
Definition helpfulcurrents_time_spec (c1 c2 n_row_count n_column_count steps : nat) : Prop :=
  (steps <= c1 * ((n_row_count + 1) * (n_column_count + 1)) + c2)%nat.

(** ** Interface *)

(** Count paths through a grid from a given bottom-row cell to the castle. Each move goes
    north or follows the current cell's horizontal arrow, avoiding obstacles. Return the
    count modulo $10^{6} + 3$, distinguishing an unreachable castle.
    - Input [row_count]: Number of grid rows.
    - Input [column_count]: Number of grid columns.
    - Input [start_column]: Zero-based starting column on the bottom row.
    - Input [ocean_map]: Rows from north to south; ~ is open water, # an obstacle, @ the castle, and > or < a horizontal current.
    - Output [output]: Path count to the castle modulo $10^{6} + 3$, or [None] exactly when unreachable. *)
Program helpfulcurrents :
  uint -> uint -> uint -> array PrimString.string ->
    option uint.

(** [@example helpfulcurrents]
    - Sample: 1
    - Input [row_count]: 2
    - Input [column_count]: 2
    - Input [start_column]: 0
    - Input [ocean_map]: [">@"; ">~"]%string
    - Output [output]: Some 2
*)

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

(** ** Complexity *)

(** [@hide] [helpfulcurrents_cost] is the cost translation of [helpfulcurrents] (the judge
    recomputes it and compares) ... *)
Complexity helpfulcurrents_cost for helpfulcurrents.

(** [@fold complexity bound] ... and runs in at most c1 * (Y + 1) * (X + 1) + c2 steps of the cost model on a valid input, Y and X the dimensions of the map (one row of counts at a time, the chains propagated in two passes), for two constants
    quantified before the inputs, on every valid input. [@requirement helpfulcurrents_time_spec] *)
Specification helpfulcurrents_time : exists c1 c2 : nat,
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
  helpfulcurrents_time_spec c1 c2 (size row_count_int) (size column_count_int) (cost4 helpfulcurrents_cost row_count_int column_count_int start_column_int ocean_map_arr).

(** [@hide] The kernel primitives (int, array, float, string) and their
    axioms. *)
Allowed Primitive Axioms.
