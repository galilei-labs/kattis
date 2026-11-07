(** * Self Balancing Binary Search Tree *)

(** ** Description *)

(** Execute operations on ordered integer key-value maps with a cursor per
    map, including insertion, deletion, lookup, copying, cursor movement and
    rank queries. Return the requested query results.

    [@kattis selfbalancingbst]
    - Difficulty: 5.3
    - CPU time limit: 3 seconds
    - Memory limit: 192 MB

    **Kattis Bounds**
    - Map instance IDs from 1 to 1000.
    - Keys and values are signed 32-bit integers. *)

(** ** Examples *)

(** Kattis text input and output. *)
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
   @signature       array uint -> array uint -> array sint -> array sint -> array (option sint)
   @math_signature  list N -> list N -> list Z -> list Z -> list (option Z)
   @summary         [run_commands instance_ids operations first_args
                    second_args] replays the statement's command stream on
                    the instances 1..1000 of an ordered key -> value map, all
                    initially empty, each with a cursor that is unset or on a
                    key; line j is "instance_ids[j] operations[j]
                    first_args[j] second_args[j]", the operation as its
                    character code, an absent argument as 0.  The outputs
                    hold one cell per rank, get and size command, in order:
                    the number printed, or None where Kattis prints "-" (the
                    cursor is unset).
*)
From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(** ** Definitions *)

(** Math side. The contents of an instance: its (key,
    value) pairs in the tree's left-to-right order, i.e.
    by strictly increasing key. *)
Definition entries := list (Z * Z).

(** An instance: its contents and its cursor (the key of
    a node, or unset). *)
Definition inst := (entries * option Z)%type.

(** The first key of contents, in left-to-right order,
    that satisfies predicate. *)
Fixpoint first_key (predicate : Z -> bool)
  (contents : entries) : option Z :=
  match contents with
  | [] => None
  | (key, _) :: rest =>
      if predicate key then Some key else first_key
        predicate rest
  end.

(** Adds (key, value) in key order; contents is unchanged
    if it already holds key. *)
Fixpoint insert (key value : Z) (contents : entries) :
  entries :=
  match contents with
  | [] => [(key, value)]
  | (key', value') :: rest =>
      if key <? key' then (key, value) :: contents
      else if key =? key' then contents
      else (key', value') :: insert key value rest
  end.

(** Erase. *)
Definition erase (cursor_key : Z) (contents : entries) :
  entries :=
  filter (fun entry => negb (fst entry =? cursor_key))
    contents.

(** Set value. *)
Definition set_value (cursor_key value : Z) (contents :
  entries) : entries :=
  map (fun entry => if fst entry =? cursor_key then
    (cursor_key, value)
                    else entry) contents.

(** Lookup. *)
Definition lookup (cursor_key : Z) (contents : entries) :
  option Z :=
  option_map snd (find (fun entry => fst entry =?
    cursor_key) contents).

(** The number of keys of contents smaller than
    cursor_key. *)
Definition rank (cursor_key : Z) (contents : entries) : Z :=
  Z.of_nat (List.length (filter (fun entry => fst entry <?
    cursor_key)
                                contents)).

(** The key at 0-based position index in left-to-right
    order. *)
Definition kth (index : Z) (contents : entries) : option Z
  :=
  if 0 <=? index then option_map fst (nth_error contents
    (Z.to_nat index))
  else None.

(** On cursor. *)
Definition on_cursor (cursor : option Z ) (action : Z ->
  option Z )
    : option Z :=
  match cursor with None => None | Some cursor_key => action
    cursor_key end.

(** The instances, by id; all empty with the cursor unset
    at the start. *)
Definition state := N -> inst.
(** Init. *)
Definition init : state := fun _ => ([], None).

(** One input line: instance id, operation code, first
    and second argument. *)
Definition command := (N * N * Z * Z)%type.

(** One [command]: the new [state] and the line it prints
    (none or one). Every operation that returns a node
    (find, lower/upper bound, [insert], front, back,
    successor, predecessor, k-th) sets the cursor to it,
    unset when it is the sentinel; [erase] and assignment
    unset it; assignment makes the instance a copy of
    instance first_arg. *)
Definition step (instances : state) (line : command)
    : state * list (option Z) :=
  let '(instance_id, operation, first_arg, second_arg) :=
    line in
  let '(contents, cursor) := instances instance_id in
  let update (instance : inst) : state :=
    fun other_id =>
      if N.eqb other_id instance_id then instance else
        instances other_id in
  let move (cursor' : option Z) :=
    (update (contents, cursor'), @nil (option Z)) in
  let say (output : option Z) := (instances, [output]) in
  match operation with
  | 97%N  (* a *) => (update (fst (instances (Z.to_N
    first_arg)), None), [])
  | 63%N  (* ? *) => move (first_key (fun key => key =?
    first_arg) contents)
  | 108%N (* l *) => move (first_key (fun key => first_arg
    <=? key) contents)
  | 117%N (* u *) => move (first_key (fun key => first_arg
    <? key) contents)
  | 105%N (* i *) =>
      (update (insert first_arg second_arg contents, Some
        first_arg), [])
  | 101%N (* e *) =>
      (update (match cursor with
               | None => contents
               | Some cursor_key => erase cursor_key
            contents
               end, None), [])
  | 102%N (* f *) => move (first_key (fun _ => true)
    contents)
  | 98%N  (* b *) => move (first_key (fun _ => true) (rev
    contents))
  | 62%N  (* > *) =>
      move (on_cursor cursor (fun cursor_key =>
              first_key (fun key => cursor_key <? key)
            contents))
  | 60%N  (* < *) =>
      move (on_cursor cursor (fun cursor_key =>
              first_key (fun key => key <? cursor_key)
            (rev contents) ))
  | 107%N (* k *) => move (kth first_arg contents)
  | 114%N (* r *) =>
      say (option_map (fun cursor_key => rank cursor_key
        contents) cursor)
  | 103%N (* g *) =>
      say (on_cursor cursor (fun cursor_key => lookup
        cursor_key contents))
  | 115%N (* s *) =>
      (update (match cursor with
               | None => contents
               | Some cursor_key => set_value cursor_key
            first_arg contents
               end, cursor), [])
  | 122%N (* z *) => say (Some (Z.of_nat (List.length
    contents)))
  | _ => (instances, [])
  end.

(** Replay. *)
Fixpoint replay (instances : state) (lines : list command)
    : list (option Z) :=
  match lines with
  | [] => []
  | line :: rest =>
      let '(instances', output) := step instances line in
      output ++ replay instances' rest
  end.

(** The [command] lines, from the four columns. *)
Definition commands (instance_ids operations : list N)
    (first_args second_args : list Z) : list command :=
  map (fun j => (nth j instance_ids 0%N, nth j operations
    0%N,
                 nth j first_args 0, nth j second_args 0))
      (seq 0 (List.length instance_ids)).

(** A 32-bit signed integer. *)
Definition int32 (value : Z) : Prop :=
  - 2 ^ 31 <= value < 2 ^ 31.

(** The arguments a line of operation operation carries;
    an absent one is 0. *)
Definition args_ok (operation : N)
  (first_arg second_arg : Z) : Prop :=
  match operation with
  | 63%N | 108%N | 117%N =>
      int32 first_arg /\ second_arg = 0     (* ? l u : the
        key searched *)
  | 105%N =>
      int32 first_arg /\ int32 second_arg   (* i : the key
        and the value *)
  | 115%N =>
      int32 first_arg /\ second_arg = 0     (* s : the value
        written *)
  | 107%N =>
      int32 first_arg /\ second_arg = 0     (* k : the value
        of k *)
  | 97%N =>
      1 <= first_arg <= 1000 /\ second_arg = 0  (* a : the
        instance copied *)
  | _ => first_arg = 0 /\ second_arg = 0    (* e f b > < r g
    z : none *)
  end.

(** [@inside run_commands_correct] Valid input. *)
Record valid_input (instance_ids operations : list N)
    (first_args second_args : list Z) : Prop := {
  (* q lines follow, each "<id> <operation> [arg]" : one
     cell per line in each of the four columns *)
  vi_lengths : List.length operations = List.length
    instance_ids /\
               List.length first_args = List.length
            instance_ids /\
               List.length second_args = List.length
            instance_ids;
  (* the instance ID will be an integer from 1 to 1,000 *)
  vi_ids : Forall
    (fun instance_id => (1 <= instance_id <= 1000)%N)
             instance_ids;
  (* the operations are the following: a ? l u i e f b >
     < r k g s z *)
  vi_ops : Forall (fun operation =>
             In operation [97; 63; 108; 117; 105; 101; 102;
            98; 62; 60; 114;
                           107; 103; 115; 122]%N)
            operations;
  (* the arguments of each operation; keys and values are
     32-bit signed integers, a copy names an instance ID *)
  vi_args : forall j, (j < List.length instance_ids)%nat ->
              args_ok (nth j operations 0%N)
            (nth j first_args 0)
                      (nth j second_args 0);
}.

(** ** Correctness *)

(** [@requirement] [@short Execute commands on ordered
    key-value maps, including cursor movement and rank,
    lookup and size queries.] The outputs: the lines
    Kattis prints, from empty instances. *)
Definition run_commands_spec
  (instance_ids operations : list N )
  (first_args second_args : list Z )
  (output : list (option Z))
  : Prop :=
  output = replay init (commands instance_ids operations
    first_args
                                  second_args).

(** ** Interface *)

(** Execute [commands] on ordered key-value maps,
    including cursor movement and [rank], [lookup] and
    size queries.
    - Input [instance_ids]:
    - Input [operations]:
    - Input [first_args]:
    - Input [second_args]:
    - Output [output]: *)
Program run_commands :
  array uint -> array uint -> array sint -> array sint ->
    array (option sint).

(** ** Bridge *)

(** [@requirement run_commands_spec] [@fold full
    correctness statement] On valid represented inputs,
    the program returns a represented [output] satisfying
    [run_commands_spec]. *)
Specification run_commands_correct :
  forall (instance_ids operations : list N ) (first_args
    second_args : list Z )
         (instance_ids_arr operations_arr : array uint)
         (first_args_arr second_args_arr : array sint),
  valid_input instance_ids operations first_args second_args
    ->
  repr instance_ids_arr instance_ids -> repr operations_arr
    operations ->
  repr first_args_arr first_args -> repr second_args_arr
    second_args ->
  exists output : list (option Z),
    repr (run_commands instance_ids_arr operations_arr
      first_args_arr
                       second_args_arr) output /\
    run_commands_spec instance_ids operations first_args
      second_args output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
