(** * Self Balancing Binary Search Tree *)

(** ** Description *)

(** Maintain several initially empty ordered maps of integer key-value pairs.
    Each map has its own cursor, which selects an entry or is unset. Keys are
    unique within a map, and their increasing order determines cursor movement
    and zero-based ranks.

    Process commands that insert or erase entries, copy a map's contents,
    find keys, move the cursor, or read and change the selected value.
    Insertion selects the inserted or existing key; an existing key keeps its
    old value. Copying and erasing unset the destination cursor. A selection
    with no matching entry also unsets the cursor.

    Only rank, value, and size queries emit answers. Rank and value queries
    emit [None] when the cursor is unset. The mathematical commands are named
    constructors of [operation], with their behavior specified by [action]
    and [step], not by a particular map representation or search algorithm.

    [@kattis selfbalancingbst]
    - Difficulty: 5.3
    - CPU time limit: 3 seconds
    - Memory limit: 192 MB

    **Kattis Bounds**
    - Map instance IDs: $1 \le i \le 10^{3}$.
    - Keys and values are signed integers satisfying $-2^{31} \le x \le 2^{31} - 1$. *)

(** ** Examples *)

(** - Input convention: Command count, followed by instance identifiers, operation characters and any arguments.
    - Output convention: One result per rank, get or size query, in command order; - denotes an unset cursor for rank or get. *)
(* Input:
14
1 i -8 -2
1 i 4 5
1 >
1 i 2 3
1 e
1 f
1 i -7 0
1 ? 10
1 s 2
1 z
1 i 4 5
1 i -3 4
1 g
1 <
Output:
3
4
*)

(** ** [@hide] Environment *)

(* @function        run_commands
   @signature       array machine_command -> array (option sint)
   @math_signature  list command -> list (option Z)
   @summary         The mathematical input is a list of named commands, each
                    addressed to a map instance. Starting with empty maps and
                    unset cursors, execution emits one answer per rank, value,
                    or size query. None denotes the printed "-".
                    Runtime commands have the same structure, with machine
                    integers representing mathematical identifiers and arguments.
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** A mathematical operation carries exactly its required arguments.
    The corresponding Kattis characters are [a], [?], [l], [u], [i], [e],
    [f], [b], [>], [<], [k], [r], [g], [s], and [z], respectively.
    Copying copies bindings, not the source cursor. *)
Inductive operation (U S : Type) :=
| CopyFrom (source : U)
| FindKey (key : S)
| LowerBound (key : S)
| UpperBound (key : S)
| Insert (key value : S)
| Erase
| First
| Last
| NextKey
| PreviousKey
| SelectRank (index : S)
| GetRank
| GetValue
| SetValue (value : S)
| GetSize.

(** [@hide] Implicit type parameters for the operation constructors. *)
Arguments CopyFrom {U S} source.
Arguments FindKey {U S} key.
Arguments LowerBound {U S} key.
Arguments UpperBound {U S} key.
Arguments Insert {U S} key value.
Arguments Erase {U S}.
Arguments First {U S}.
Arguments Last {U S}.
Arguments NextKey {U S}.
Arguments PreviousKey {U S}.
Arguments SelectRank {U S} index.
Arguments GetRank {U S}.
Arguments GetValue {U S}.
Arguments SetValue {U S} value.
Arguments GetSize {U S}.

(** A destination instance identifier together with a named operation. *)
Definition command := (N * operation N Z)%type.

(** The same command structure at runtime, with machine-sized identifiers,
    keys, and values. The input wrapper constructs these named operations
    directly from the command characters and their arguments. *)
Definition machine_command := (uint * operation uint sint)%type.

(** An abstract map associates each key with a value or with absence.
    No ordering of stored entries or tree structure is prescribed. *)
Definition key_map := Z -> option Z.

(** The key is present in the map. *)
Definition present (contents : key_map) (key : Z) : Prop :=
  exists value, contents key = Some value.

(** The finite set of keys satisfying [predicate] has [count] elements.
    The witnessing enumeration has no prescribed order. *)
Definition cardinality (contents : key_map) (predicate : Z -> Prop)
    (count : Z) : Prop :=
  exists keys : list Z,
    NoDup keys /\
    (forall key, In key keys <-> present contents key /\ predicate key) /\
    count = Z.of_nat (List.length keys).

(** An abstract map and its optional selected key. *)
Record instance := MapInstance {
  bindings : key_map;
  cursor : option Z;
}.

(** Each map instance has finitely many keys and an unset or existing cursor.
    These are the states described by the command semantics. *)
Definition instance_valid (current : instance) : Prop :=
  (exists count, cardinality (bindings current) (fun _ => True) count) /\
  match cursor current with
  | None => True
  | Some key => present (bindings current) key
  end.

(** The instance associated with each identifier. *)
Definition state := N -> instance.

(** Initially every map is empty and every cursor is unset. *)
Definition init : state := fun _ => MapInstance (fun _ => None) None.

(** Replace one instance, leaving every other instance unchanged. *)
Definition replace_instance (instances : state) (id : N)
    (current : instance) : state :=
  fun other => if N.eqb other id then current else instances other.

(** [selected] is the least eligible existing key, or is unset exactly when
    there is no eligible key. This specifies a minimum, not a search procedure. *)
Definition least_key (contents : key_map) (eligible : Z -> Prop)
    (selected : option Z) : Prop :=
  match selected with
  | Some key => present contents key /\ eligible key /\
      forall other, present contents other -> eligible other -> key <= other
  | None => forall key, present contents key -> ~ eligible key
  end.

(** The greatest eligible existing key, or an unset result if none exists. *)
Definition greatest_key (contents : key_map) (eligible : Z -> Prop)
    (selected : option Z) : Prop :=
  match selected with
  | Some key => present contents key /\ eligible key /\
      forall other, present contents other -> eligible other -> other <= key
  | None => forall key, present contents key -> ~ eligible key
  end.

(** Cursor selections. Rank is zero-based: selecting rank [index] means
    selecting a key with exactly [index] smaller keys. An invalid rank selects
    nothing. Moving an unset cursor leaves it unset. *)
Inductive selects : operation N Z -> key_map -> option Z -> option Z -> Prop :=
| SelectFind : forall contents old key selected,
    least_key contents (fun candidate => candidate = key) selected ->
    selects (FindKey key) contents old selected
| SelectLower : forall contents old key selected,
    least_key contents (fun candidate => key <= candidate) selected ->
    selects (LowerBound key) contents old selected
| SelectUpper : forall contents old key selected,
    least_key contents (fun candidate => key < candidate) selected ->
    selects (UpperBound key) contents old selected
| SelectFirst : forall contents old selected,
    least_key contents (fun _ => True) selected ->
    selects First contents old selected
| SelectLast : forall contents old selected,
    greatest_key contents (fun _ => True) selected ->
    selects Last contents old selected
| SelectNext : forall contents key selected,
    least_key contents (fun candidate => key < candidate) selected ->
    selects NextKey contents (Some key) selected
| SelectNextUnset : forall contents,
    selects NextKey contents None None
| SelectPrevious : forall contents key selected,
    greatest_key contents (fun candidate => candidate < key) selected ->
    selects PreviousKey contents (Some key) selected
| SelectPreviousUnset : forall contents,
    selects PreviousKey contents None None
| SelectIndex : forall contents old index selected,
    least_key contents
      (fun key => cardinality contents (fun other => other < key) index)
      selected ->
    selects (SelectRank index) contents old selected.

(** Changing or removing one binding preserves all other bindings. *)
Definition changes_only (before after : key_map) (key : Z) : Prop :=
  forall other, other <> key -> after other = before other.

(** One operation on a single map. The emitted list is empty for a mutation
    or selection, and a singleton for a query. In particular, emitting [None]
    is different from emitting no answer. Copying is handled by [step]. *)
Inductive action : operation N Z -> instance -> instance -> list (option Z) -> Prop :=
| ActSelect : forall op contents old selected,
    selects op contents old selected ->
    action op (MapInstance contents old) (MapInstance contents selected) []
| ActInsertNew : forall contents old key value after,
    contents key = None -> after key = Some value ->
    changes_only contents after key ->
    action (Insert key value) (MapInstance contents old)
      (MapInstance after (Some key)) []
| ActInsertExisting : forall contents old key value existing,
    contents key = Some existing ->
    action (Insert key value) (MapInstance contents old)
      (MapInstance contents (Some key)) []
| ActErase : forall contents key after,
    after key = None -> changes_only contents after key ->
    action Erase (MapInstance contents (Some key)) (MapInstance after None) []
| ActEraseUnset : forall contents,
    action Erase (MapInstance contents None) (MapInstance contents None) []
| ActSet : forall contents key value after,
    after key = Some value -> changes_only contents after key ->
    action (SetValue value) (MapInstance contents (Some key))
      (MapInstance after (Some key)) []
| ActSetUnset : forall contents value,
    action (SetValue value) (MapInstance contents None) (MapInstance contents None) []
| ActRank : forall contents key rank,
    cardinality contents (fun other => other < key) rank ->
    action GetRank (MapInstance contents (Some key))
      (MapInstance contents (Some key)) [Some rank]
| ActRankUnset : forall contents,
    action GetRank (MapInstance contents None) (MapInstance contents None) [None]
| ActGet : forall contents key value,
    contents key = Some value ->
    action GetValue (MapInstance contents (Some key))
      (MapInstance contents (Some key)) [Some value]
| ActGetUnset : forall contents,
    action GetValue (MapInstance contents None) (MapInstance contents None) [None]
| ActSize : forall contents selected count,
    cardinality contents (fun _ => True) count ->
    action GetSize (MapInstance contents selected)
      (MapInstance contents selected) [Some count].

(** A command changes only its destination instance. Copying takes a snapshot
    of the source bindings and unsets the destination cursor, including when
    source and destination are the same instance. *)
Inductive step : state -> command -> state -> list (option Z) -> Prop :=
| StepAction : forall instances id op current output,
    instance_valid (instances id) ->
    action op (instances id) current output ->
    instance_valid current ->
    step instances (id, op) (replace_instance instances id current) output
| StepCopy : forall instances id source,
    instance_valid (instances source) ->
    step instances (id, CopyFrom source)
      (replace_instance instances id (MapInstance (bindings (instances source)) None)) [].

(** Execution composes command transitions and concatenates their emitted
    answers in order. There is no prescribed map implementation. *)
Inductive executes : state -> list command -> state -> list (option Z) -> Prop :=
| ExecuteNil : forall instances, executes instances [] instances []
| ExecuteCons : forall before middle after line rest emitted output,
    step before line middle emitted ->
    executes middle rest after output ->
    executes before (line :: rest) after (emitted ++ output).

(** Signed 32-bit keys and values. *)
Definition int32 (value : Z) : Prop := -2^31 <= value < 2^31.

(** The arguments carried by a mathematical operation satisfy the statement's
    bounds. Negative or out-of-range selection ranks are allowed: they simply
    unset the cursor. *)
Definition operation_valid (op : operation N Z) : Prop :=
  match op with
  | CopyFrom source => (1 <= source <= 1000)%N
  | FindKey key | LowerBound key | UpperBound key => int32 key
  | Insert key value => int32 key /\ int32 value
  | SelectRank index => int32 index
  | SetValue value => int32 value
  | _ => True
  end.

(** [@inside run_commands_correct] Mathematical commands address instances
    1 through 1000 and carry valid arguments. No padding arguments occur here. *)
Definition valid_input (commands : list command) : Prop :=
  Forall (fun line => (1 <= fst line <= 1000)%N /\ operation_valid (snd line)) commands.

(** ** Correctness *)

(** [@requirement] Starting with empty maps and unset cursors, the commands
    admit an execution whose query answers are exactly [output], in order.
    Only [GetRank], [GetValue], and [GetSize] emit answers. *)
Definition run_commands_spec (commands : list command)
    (output : list (option Z)) : Prop :=
  exists final, executes init commands final output.

(** ** Complexity *)

(** [@requirement] Runs in $O(q \log(q+1))$ steps, where $q$ is the number of commands. *)
Definition run_commands_time_spec (c1 c2 n_operations steps : nat) : Prop :=
  (steps <= c1 * ((n_operations + 1) * (Nat.log2 (n_operations) + 1)) + c2)%nat.

(** ** Runtime representation *)

(** [@hide] Corresponding operations have the same constructor, with each
    machine integer representing its mathematical argument. Products and
    arrays lift this relation to whole command streams. *)
Global Instance repr_operation : Repr (operation uint sint) (operation N Z) :=
  fun machine mathematical =>
    match machine, mathematical with
    | CopyFrom source_int, CopyFrom source => repr source_int source
    | FindKey key_int, FindKey key
    | LowerBound key_int, LowerBound key
    | UpperBound key_int, UpperBound key => repr key_int key
    | Insert key_int value_int, Insert key value =>
        repr key_int key /\ repr value_int value
    | SelectRank index_int, SelectRank index => repr index_int index
    | SetValue value_int, SetValue value => repr value_int value
    | Erase, Erase | First, First | Last, Last
    | NextKey, NextKey | PreviousKey, PreviousKey
    | GetRank, GetRank | GetValue, GetValue | GetSize, GetSize => True
    | _, _ => False
    end.

(** [@hide] Cost translations and structural witnesses for the typed runtime
    input. These describe its representation, not command behavior. *)
Elpi complexity operation.
Elpi complexity machine_command.

Global Instance witness_operation : Witness (operation uint sint)
    (fun CM => operation_cost CM uint (int_cost CM) sint (int_cost CM)) :=
  fun op => match op with
  | CopyFrom source => @CopyFrom_cost stepsCM _ _ _ _ source (witness source)
  | FindKey key => @FindKey_cost stepsCM _ _ _ _ key (witness key)
  | LowerBound key => @LowerBound_cost stepsCM _ _ _ _ key (witness key)
  | UpperBound key => @UpperBound_cost stepsCM _ _ _ _ key (witness key)
  | Insert key value => @Insert_cost stepsCM _ _ _ _ key (witness key) value (witness value)
  | Erase => @Erase_cost stepsCM _ _ _ _
  | First => @First_cost stepsCM _ _ _ _
  | Last => @Last_cost stepsCM _ _ _ _
  | NextKey => @NextKey_cost stepsCM _ _ _ _
  | PreviousKey => @PreviousKey_cost stepsCM _ _ _ _
  | SelectRank index => @SelectRank_cost stepsCM _ _ _ _ index (witness index)
  | GetRank => @GetRank_cost stepsCM _ _ _ _
  | GetValue => @GetValue_cost stepsCM _ _ _ _
  | SetValue value => @SetValue_cost stepsCM _ _ _ _ value (witness value)
  | GetSize => @GetSize_cost stepsCM _ _ _ _
  end.

Global Instance witness_machine_command : Witness machine_command machine_command_cost :=
  fun line => match line with
  | (id, op) => @pair_cost stepsCM _ _ _ _ id (witness id) op (witness op)
  end.

Global Instance witness_array_machine_command : Witness (array machine_command)
    (fun CM commands => array_cost CM machine_command (machine_command_cost CM) commands) :=
  @witness_array machine_command machine_command_cost witness_machine_command.

(** ** Interface *)

(** Execute named mathematical commands on initially empty ordered maps with
    independent, initially unset cursors. The runtime array and mathematical
    list contain corresponding named commands; only their integer types differ.
    - Input [commands]: Destination instance identifiers paired with named operations and their arguments.
    - Output [output]: One result per rank, value, or size query, in command order. [None] denotes the printed - for an unset cursor. *)
Program run_commands :
  array machine_command -> array (option sint).

(** [@example run_commands]
    - Sample: 1
    - Input [commands]: [(1%N, Insert (-8) (-2)); (1%N, Insert 4 5); (1%N, NextKey); (1%N, Insert 2 3); (1%N, Erase); (1%N, First); (1%N, Insert (-7) 0); (1%N, FindKey 10); (1%N, SetValue 2); (1%N, GetSize); (1%N, Insert 4 5); (1%N, Insert (-3) 4); (1%N, GetValue); (1%N, PreviousKey)]%Z
    - Output [output]: [Some 3; Some 4]%Z
*)

(** ** Bridge *)

(** [@requirement run_commands_spec] [@fold full correctness statement]
    A runtime array representing valid mathematical commands returns represented
    query answers satisfying the abstract execution relation. *)
Specification run_commands_correct :
  forall (commands : list command) (commands_arr : array machine_command),
  valid_input commands ->
  repr commands_arr commands ->
  exists output : list (option Z),
    repr (run_commands commands_arr) output /\
    run_commands_spec commands output.

(** ** Complexity *)

(** [@hide] The cost translation of [run_commands]. *)
Complexity run_commands_cost for run_commands.

(** [@fold complexity bound] On valid represented commands, the program
    satisfies [run_commands_time_spec], with constants independent of the
    commands. [@requirement run_commands_time_spec] *)
Specification run_commands_time : exists c1 c2 : nat,
  forall (commands : list command) (commands_arr : array machine_command),
  valid_input commands ->
  repr commands_arr commands ->
  run_commands_time_spec c1 c2 (size commands_arr)
    (cost1 run_commands_cost commands_arr).

(** [@hide] The permitted kernel primitives and their axioms. *)
Allowed Primitive Axioms.
