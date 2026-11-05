(* @function        run_commands
   @signature       array uint -> array uint -> array sint -> array sint -> array (option sint)
   @math_signature  list N -> list N -> list Z -> list Z -> list (option Z)
   @summary         [run_commands ids ops xs ys] replays the statement's
                    command stream on the instances 1..1000 of an ordered
                    key -> value map, all initially empty, each with a cursor
                    that is unset or on a key; line j is "ids[j] ops[j] xs[j]
                    ys[j]", the operation as its character code, an absent
                    argument as 0.  The result holds one cell per rank, get
                    and size command, in order: the number printed, or None
                    where Kattis prints "-" (the cursor is unset).
*)

From Stdlib Require Import ZArith NArith List Uint63 PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope Z_scope.

(* Math side.  The contents of an instance: its (key, value) pairs in the
   tree's left-to-right order, i.e. by strictly increasing key. *)
Definition entries := list (Z * Z).

(* An instance: its contents and its cursor (the key of a node, or unset). *)
Definition inst := (entries * option Z)%type.

(* The first key of t, in left-to-right order, that satisfies p. *)
Fixpoint first_key (p : Z -> bool) (t : entries) : option Z :=
  match t with
  | [] => None
  | (k, _) :: t' => if p k then Some k else first_key p t'
  end.

(* Adds (k, v) in key order; t is unchanged if it already holds key k. *)
Fixpoint insert (k v : Z) (t : entries) : entries :=
  match t with
  | [] => [(k, v)]
  | (k', v') :: t' =>
      if k <? k' then (k, v) :: t
      else if k =? k' then t
      else (k', v') :: insert k v t'
  end.

Definition erase (c : Z) (t : entries) : entries :=
  filter (fun e => negb (fst e =? c)) t.

Definition set_value (c v : Z) (t : entries) : entries :=
  map (fun e => if fst e =? c then (c, v) else e) t.

Definition lookup (c : Z) (t : entries) : option Z :=
  option_map snd (find (fun e => fst e =? c) t).

(* The number of keys of t smaller than c. *)
Definition rank (c : Z) (t : entries) : Z :=
  Z.of_nat (List.length (filter (fun e => fst e <? c) t)).

(* The key at 0-based position k in left-to-right order. *)
Definition kth (k : Z) (t : entries) : option Z :=
  if 0 <=? k then option_map fst (nth_error t (Z.to_nat k)) else None.

Definition on_cursor (cur : option Z) (f : Z -> option Z) : option Z :=
  match cur with None => None | Some c => f c end.

(* The instances, by id; all empty with the cursor unset at the start. *)
Definition state := N -> inst.
Definition init : state := fun _ => ([], None).

(* One input line: instance id, operation code, first and second argument. *)
Definition command := (N * N * Z * Z)%type.

(* One command: the new state and the line it prints (none or one).  Every
   operation that returns a node (find, lower/upper bound, insert, front,
   back, successor, predecessor, k-th) sets the cursor to it, unset when it
   is the sentinel; erase and assignment unset it; assignment makes the
   instance a copy of instance x. *)
Definition step (s : state) (c : command) : state * list (option Z) :=
  let '(id, op, x, y) := c in
  let '(t, cur) := s id in
  let upd (i : inst) : state := fun j => if N.eqb j id then i else s j in
  let move (cur' : option Z) := (upd (t, cur'), @nil (option Z)) in
  let say (o : option Z) := (s, [o]) in
  match op with
  | 97%N  (* a *) => (upd (fst (s (Z.to_N x)), None), [])
  | 63%N  (* ? *) => move (first_key (fun k => k =? x) t)
  | 108%N (* l *) => move (first_key (fun k => x <=? k) t)
  | 117%N (* u *) => move (first_key (fun k => x <? k) t)
  | 105%N (* i *) => (upd (insert x y t, Some x), [])
  | 101%N (* e *) =>
      (upd (match cur with None => t | Some c => erase c t end, None), [])
  | 102%N (* f *) => move (first_key (fun _ => true) t)
  | 98%N  (* b *) => move (first_key (fun _ => true) (rev t))
  | 62%N  (* > *) => move (on_cursor cur (fun c => first_key (fun k => c <? k) t))
  | 60%N  (* < *) => move (on_cursor cur (fun c => first_key (fun k => k <? c) (rev t)))
  | 107%N (* k *) => move (kth x t)
  | 114%N (* r *) => say (option_map (fun c => rank c t) cur)
  | 103%N (* g *) => say (on_cursor cur (fun c => lookup c t))
  | 115%N (* s *) =>
      (upd (match cur with None => t | Some c => set_value c x t end, cur), [])
  | 122%N (* z *) => say (Some (Z.of_nat (List.length t)))
  | _ => (s, [])
  end.

Fixpoint replay (s : state) (cs : list command) : list (option Z) :=
  match cs with
  | [] => []
  | c :: cs' => let '(s', o) := step s c in o ++ replay s' cs'
  end.

(* The command lines, from the four columns. *)
Definition commands (ids ops : list N) (xs ys : list Z) : list command :=
  map (fun j => (nth j ids 0%N, nth j ops 0%N, nth j xs 0, nth j ys 0))
      (seq 0 (List.length ids)).

(* A 32-bit signed integer. *)
Definition int32 (v : Z) : Prop := - 2 ^ 31 <= v < 2 ^ 31.

(* The arguments a line of operation op carries; an absent one is 0. *)
Definition args_ok (op : N) (x y : Z) : Prop :=
  match op with
  | 63%N | 108%N | 117%N => int32 x /\ y = 0   (* ? l u : the key searched *)
  | 105%N => int32 x /\ int32 y                (* i : the key and the value *)
  | 115%N => int32 x /\ y = 0                  (* s : the value written *)
  | 107%N => int32 x /\ y = 0                  (* k : the value of k *)
  | 97%N => 1 <= x <= 1000 /\ y = 0            (* a : the instance copied *)
  | _ => x = 0 /\ y = 0                        (* e f b > < r g z : none *)
  end.

Record valid_input (ids ops : list N) (xs ys : list Z) : Prop := {
  (* q lines follow, each "<id> <operation> [arg]": one cell per line in
     each of the four columns *)
  vi_lengths : List.length ops = List.length ids /\
               List.length xs = List.length ids /\
               List.length ys = List.length ids;
  (* the instance ID will be an integer from 1 to 1,000 *)
  vi_ids : Forall (fun id => (1 <= id <= 1000)%N) ids;
  (* the operations are the following: a ? l u i e f b > < r k g s z *)
  vi_ops : Forall (fun op =>
             In op [97; 63; 108; 117; 105; 101; 102; 98; 62; 60; 114; 107;
                    103; 115; 122]%N) ops;
  (* the arguments of each operation; keys and values are 32-bit signed
     integers, a copy names an instance ID *)
  vi_args : forall j, (j < List.length ids)%nat ->
              args_ok (nth j ops 0%N) (nth j xs 0) (nth j ys 0);
}.

(* The output: the lines Kattis prints, from empty instances. *)
Definition run_commands_spec (ids ops : list N) (xs ys : list Z)
    (out : list (option Z)) : Prop :=
  out = replay init (commands ids ops xs ys).

Program run_commands :
  array uint -> array uint -> array sint -> array sint -> array (option sint).

Specification run_commands_correct :
  forall (ids ops : list N) (xs ys : list Z)
         (a b : array uint) (c d : array sint),
  valid_input ids ops xs ys ->
  repr a ids -> repr b ops -> repr c xs -> repr d ys ->
  exists out : list (option Z),
    repr (run_commands a b c d) out /\ run_commands_spec ids ops xs ys out.

(* The kernel primitives (int, array, float, string) and their axioms. *)
Allowed Primitive Axioms.
