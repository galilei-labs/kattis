(** * Water *)

(** ** Description *)

(** Compute the maximum flow between two designated vertices of an
    undirected capacitated network, initially and after each edge-capacity
    increase.

    [@kattis water]
    - Difficulty: 3.9
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 100$; at most $n(n-1)/2$ initial edges.
    - $1\text{ to }10{,}000$ updates; initial capacities and capacity increases from $1$
      to $1{,}000$.
    - Initial edges have distinct endpoint pairs. *)

(** ** Examples *)

(** - Input convention: Vertex, edge and update counts, followed by initial capacities and capacity-increase triples.
    - Output convention: Maximum flow from vertex 1 to 2 initially and after each update, one value per line. *)
(* Input:
3 2 1
1 3 10
2 3 1
2 3 15
Output:
1
10
*)

(** ** [@hide] Environment *)

(* @function        water
   @signature       uint -> array uint -> array uint -> array uint ->
                    array uint -> array uint -> array uint -> array uint
   @math_signature  N -> list N -> list N -> list N ->
                    list N -> list N -> list N -> list N
   @summary         [water station_count pipe_starts pipe_ends
                    pipe_capacities improvement_starts improvement_ends
                    improvement_amounts] gets station_count stations
                    1..station_count (1 the pumping station, 2 the mansion),
                    the initial pipes (pipe j joins pipe_starts_j and
                    pipe_ends_j with capacity pipe_capacities_j) and the k
                    improvements (improvement t adds capacity
                    improvement_amounts_t between improvement_starts_t and
                    improvement_ends_t). It returns k+1 values: value t is
                    the maximum amount of water that can flow from station 1
                    to station 2 once the first t improvements are made.
*)
From Stdlib Require Import ZArith NArith List Bool Uint63
  PArray.
From Respeced Require Import Repr.
Import ListNotations.
Open Scope N_scope.

(* Math side. The pipes of each section are three
   parallel lists, one per column of the lines "a b c". *)

(** ** Definitions *)

(** The number of elements of l. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** Element j of l (0 beyond the end). *)
Definition get (l : list N) (j : N) : N :=
  nth (N.to_nat j) l 0.

(** node is a [station]. *)
Definition station (station_count node : N) : Prop :=
  1 <= node <= station_count.

(** term 0 + term 1 + ... + term (count - 1). *)
Fixpoint sum_below (term : N -> N) (count : nat) : N :=
  match count with
  | O => 0
  | S count' => sum_below term count' + term
    (N.of_nat count')
  end.

(** The [capacity] between node and other of the first
    prefix_count pipes of the section starts ends
    amounts: a pipe joins its two stations in both
    directions, and capacities of the same pair add up
    (an improvement increases the pipe's [capacity]). *)
Definition cap_upto (starts ends amounts : list N)
  (prefix_count : N)
    (node other : N) : N :=
  sum_below (fun j => if (get starts j =? node) && (get ends
    j =? other)
                         || (get starts j =? other) &&
            (get ends j =? node)
                      then get amounts j else 0)
            (N.to_nat prefix_count).

(** The [capacity] between node and other after the first
    applied_count improvements. *)
Definition capacity
  (pipe_starts pipe_ends pipe_capacities : list N)
    (improvement_starts improvement_ends improvement_amounts
      : list N)
    (applied_count node other : N) : N :=
  cap_upto pipe_starts pipe_ends pipe_capacities
    (len pipe_starts) node other
  + cap_upto improvement_starts improvement_ends
    improvement_amounts
      applied_count node other.

(** term 1 + term 2 + ... + term count. *)
Fixpoint sum_stations (term : N -> Z) (count : nat) : Z :=
  match count with
  | O => 0%Z
  | S count' =>
    (sum_stations term count' + term (N.of_nat count))%Z
  end.

(** The net amount of [water] leaving [station] node
    under flow. *)
Definition net_out (station_count : N) (flow : N -> N -> Z)
  (node : N) : Z :=
  sum_stations (flow node) (N.to_nat station_count).

(** flow node other is the net amount of [water] sent
    from node to other through the pipes joining them: it
    is antisymmetric, at most the [capacity], and every
    [station] other than 1 and 2 keeps no [water]. *)
Definition is_flow (station_count : N)
  (capacity_of : N -> N -> N)
    (flow : N -> N -> Z) : Prop :=
  (forall node other, station station_count node ->
     station station_count other ->
     flow node other = (- flow other node)%Z) /\
  (forall node other, station station_count node ->
     station station_count other ->
     (flow node other <= Z.of_N (capacity_of node other))
       %Z) /\
  (forall node, station station_count node -> node <> 1 ->
    node <> 2 ->
     net_out station_count flow node = 0%Z).

(** amount is the maximum amount of [water] reaching the
    mansion: some flow brings amount, and no flow brings
    more. *)
Definition max_flow (station_count : N) (capacity_of : N ->
  N -> N)
    (amount : N) : Prop :=
  (exists flow, is_flow station_count capacity_of flow /\
     net_out station_count flow 1 = Z.of_N amount) /\
  (forall flow, is_flow station_count capacity_of flow ->
     (net_out station_count flow 1 <= Z.of_N amount)%Z).

(** [@inside water_correct] Input constraints based on the Kattis problem bounds, within which the implementation's correctness is guaranteed. *)
Record valid_input (station_count : N)
    (pipe_starts pipe_ends pipe_capacities : list N)
    (improvement_starts improvement_ends improvement_amounts
      : list N )
    : Prop := {
  (* 2 <= n <= 100 *)
  vi_n : 2 <= station_count <= 100;
  (* 0 <= p <= n(n-1)/2, the p lines of the initial pipes
     being "a b c" *)
  vi_p : len pipe_starts <= station_count *
    (station_count - 1) / 2;
  vi_pb : len pipe_ends = len pipe_starts;
  vi_pc : len pipe_capacities = len pipe_starts;
  (* 1 <= k <= 10 000, the k lines of the improvements
     being "a b c" *)
  vi_k : 1 <= len improvement_starts <= 10000;
  vi_ib : len improvement_ends = len improvement_starts;
  vi_ic : len improvement_amounts = len improvement_starts;
  (* initial pipes: 1 <= a < b <= n and 1 <= c <= 1 000 *)
  vi_pab : forall j, j < len pipe_starts ->
    1 <= get pipe_starts j < get pipe_ends j /\
    get pipe_ends j <= station_count;
  vi_pcap : forall j, j < len pipe_starts -> 1 <= get
    pipe_capacities j <= 1000;
  (* no (a, b) pair will appear more than once in this
     section *)
  vi_pdistinct : NoDup (combine pipe_starts pipe_ends);
  (* improvements: 1 <= a < b <= n and 1 <= c <= 1 000 *)
  vi_iab : forall t, t < len improvement_starts ->
    1 <= get improvement_starts t < get improvement_ends t
      /\
    get improvement_ends t <= station_count;
  vi_icap : forall t, t < len improvement_starts ->
    1 <= get improvement_amounts t <= 1000;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the maximum flow initially and after each capacity increase, in
    update order. *)
Definition water_spec
  (station_count : N)
  (pipe_starts pipe_ends pipe_capacities : list N)
  (improvement_starts improvement_ends improvement_amounts :
    list N )
  (output : list N)
  : Prop :=
  len output = len improvement_starts + 1 /\
  forall t, t < len output ->
    max_flow station_count
      (capacity pipe_starts pipe_ends pipe_capacities
         improvement_starts improvement_ends
           improvement_amounts t)
      (get output t).

(** ** Interface *)

(** Compute the maximum flow between two designated vertices of an undirected capacitated
    network, initially and after each edge-capacity increase.
    - Input [station_count]: Number of vertices in the network.
    - Input [pipe_starts]: First endpoint of each initial edge.
    - Input [pipe_ends]: Second endpoint of each initial edge.
    - Input [pipe_capacities]: Initial capacity of each edge.
    - Input [improvement_starts]: First endpoint of each capacity update.
    - Input [improvement_ends]: Second endpoint of each capacity update.
    - Input [improvement_amounts]: Capacity added by each corresponding update.
    - Output [output]: The output gives the maximum flow initially and after each capacity increase, in update order. *)
Program water : uint -> array uint -> array uint ->
  array uint ->
  array uint -> array uint -> array uint -> array uint.

(** ** Bridge *)

(** [@requirement water_spec] [@fold full correctness
    statement] On valid represented inputs, the program
    returns a represented [output] satisfying
    [water_spec]. *)
Specification water_correct :
  forall (station_count : N) (pipe_starts pipe_ends
    pipe_capacities : list N )
         (improvement_starts improvement_ends
           improvement_amounts : list N )
         (station_count_int : uint)
         (pipe_starts_arr pipe_ends_arr pipe_capacities_arr
           : array uint )
         (improvement_starts_arr improvement_ends_arr :
           array uint )
         (improvement_amounts_arr : array uint),
  valid_input station_count pipe_starts pipe_ends
    pipe_capacities
    improvement_starts improvement_ends improvement_amounts
      ->
  repr station_count_int station_count ->
  repr pipe_starts_arr pipe_starts -> repr pipe_ends_arr
    pipe_ends ->
  repr pipe_capacities_arr pipe_capacities ->
  repr improvement_starts_arr improvement_starts ->
  repr improvement_ends_arr improvement_ends ->
  repr improvement_amounts_arr improvement_amounts ->
  exists output : list N,
    repr (water station_count_int pipe_starts_arr
      pipe_ends_arr
            pipe_capacities_arr improvement_starts_arr
            improvement_ends_arr
            improvement_amounts_arr) output /\
    water_spec station_count pipe_starts pipe_ends
      pipe_capacities
      improvement_starts improvement_ends
        improvement_amounts output.

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
