(** * Water *)

(** ** Description *)

(** A water company sends water from its pumping station (station one) to
    a mansion (station two) through a network of stations and pipes. A pipe
    can carry water in either direction, up to its capacity. Intermediate
    stations pass on all the water they receive.

    Find the greatest amount of water the mansion can receive initially
    and after each improvement. An improvement permanently adds capacity
    between two stations, installing a pipe if necessary. Improvements
    accumulate: each answer includes all preceding increases.

    [@kattis water]
    - Difficulty: 3.9
    - CPU time limit: 2 seconds
    - Memory limit: 1024 MB

    **Kattis Bounds**
    - Vertex count: $2 \le n \le 100$; at most $n(n-1)/2$ initial edges.
    - Update count: $1 \le k \le 10^{4}$; initial capacities and capacity increases satisfy
      $1 \le c \le 10^{3}$.
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
                    It runs in at most c1 * ((n + 1)^2 * (C + k + 1) + p) +
                    c2 steps of the cost model on a valid input, n the
                    number of stations, p of pipes, k of improvements and C
                    the total capacity of the pipes and improvements
                    ([sizes]): every augmentation raises the flow by at
                    least one unit, the flow never exceeds the total
                    capacity, and an augmentation is one breadth-first
                    search over the n x n residual table plus a walk; the n
                    p bound of Edmonds-Karp on the number of augmentations
                    is not stated, for two constants c1, c2.
*)
From Stdlib Require Import ZArith NArith List Bool Uint63
  PArray.
From StdGalilei Require Import repr.
From KattisLib Require Import Cost.
Import ListNotations.
Open Scope N_scope.

(* The pipes of each section are three
   parallel lists, one per column of the lines "a b c". *)

(** ** Definitions *)

(** The number of elements of [l]. *)
Definition len {A} (l : list A) : N :=
  N.of_nat (List.length l).

(** The entry at zero-based index [j] in [l], or zero beyond the end. *)
Definition get (l : list N) (j : N) : N :=
  nth (N.to_nat j) l 0.

(** [node] is a valid one-based station number. *)
Definition station (station_count node : N) : Prop :=
  1 <= node <= station_count.

(** The sum of [term] over zero-based indices below [count]. *)
Fixpoint sum_below (term : N -> N) (count : nat) : N :=
  match count with
  | O => 0
  | S count' => sum_below term count' + term
    (N.of_nat count')
  end.

(** The combined undirected capacity between [node] and [other] from the first
    [prefix_count] listed pipes. Parallel pipes contribute additively. *)
Definition cap_upto (starts ends amounts : list N)
  (prefix_count : N)
    (node other : N) : N :=
  sum_below (fun j => if (get starts j =? node) && (get ends
    j =? other)
                         || (get starts j =? other) &&
            (get ends j =? node)
                      then get amounts j else 0)
            (N.to_nat prefix_count).

(** The capacity between [node] and [other] after the first [applied_count]
    improvements. *)
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

(** The sum of [term] over one-based station indices from one through [count]. *)
Fixpoint sum_stations (term : N -> Z) (count : nat) : Z :=
  match count with
  | O => 0%Z
  | S count' =>
    (sum_stations term count' + term (N.of_nat count))%Z
  end.

(** The net flow leaving station [node]. *)
Definition net_out (station_count : N) (flow : N -> N -> Z)
  (node : N) : Z :=
  sum_stations (flow node) (N.to_nat station_count).

(** [flow] assigns an antisymmetric net flow to each pair of stations, respecting
    capacity bounds and conserving flow at every station except source one and sink
    two. *)
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

(** Some valid flow attains [amount] at the sink, and no valid flow attains a
    greater amount. *)
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
  (* 1 <= k <= 10^4, the k lines of the improvements
     being "a b c" *)
  vi_k : 1 <= len improvement_starts <= 10000;
  vi_ib : len improvement_ends = len improvement_starts;
  vi_ic : len improvement_amounts = len improvement_starts;
  (* initial pipes: 1 <= a < b <= n and 1 <= c <= 10^3 *)
  vi_pab : forall j, j < len pipe_starts ->
    1 <= get pipe_starts j < get pipe_ends j /\
    get pipe_ends j <= station_count;
  vi_pcap : forall j, j < len pipe_starts -> 1 <= get
    pipe_capacities j <= 1000;
  (* no (a, b) pair will appear more than once in this
     section *)
  vi_pdistinct : NoDup (combine pipe_starts pipe_ends);
  (* improvements: 1 <= a < b <= n and 1 <= c <= 10^3 *)
  vi_iab : forall t, t < len improvement_starts ->
    1 <= get improvement_starts t < get improvement_ends t
      /\
    get improvement_ends t <= station_count;
  vi_icap : forall t, t < len improvement_starts ->
    1 <= get improvement_amounts t <= 1000;
}.

(** ** Correctness *)

(** [@requirement]
    The output gives the maximum water delivery from pumping station one to
    mansion station two, initially and after each cumulative pipe improvement. *)
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

(** ** Complexity *)

(** [@requirement] Runs in $O((V+1)^2(C+A+q+1)+E)$ steps, where $V$ is the station count, $E$ the initial pipe count, $q$ the number of improvements, $C$ the sum of initial pipe capacities, and $A$ the sum of improvement amounts. *)
Definition water_time_spec (c1 c2 n_station_count total_pipe_capacities total_improvement_amounts n_improvement_starts n_pipe_starts steps : nat) : Prop :=
  (steps <= c1 * ((n_station_count + 1) * (n_station_count + 1) * (total_pipe_capacities + total_improvement_amounts + n_improvement_starts + 1) + n_pipe_starts + 1) + c2)%nat.

(** ** Interface *)

(** Maximize water delivered from pumping station one to mansion station two,
    initially and after each permanent pipe-capacity improvement.
    - Input [station_count]: Number of water stations.
    - Input [pipe_starts]: First station of each original pipe.
    - Input [pipe_ends]: Second station of each corresponding pipe.
    - Input [pipe_capacities]: Capacity of each original pipe, usable in either direction.
    - Input [improvement_starts]: First station of each improvement.
    - Input [improvement_ends]: Second station of each corresponding improvement.
    - Input [improvement_amounts]: Additional capacity between the two stations; zero existing capacity is allowed.
    - Output [output]: Maximum water delivery initially, then after each improvement in order, including all increases so far. *)
Program water : uint -> array uint -> array uint ->
  array uint ->
  array uint -> array uint -> array uint -> array uint.

(** [@example water]
    - Sample: 1
    - Input [station_count]: 3
    - Input [pipe_starts]: [1; 2]
    - Input [pipe_ends]: [3; 3]
    - Input [pipe_capacities]: [10; 1]
    - Input [improvement_starts]: [2]
    - Input [improvement_ends]: [3]
    - Input [improvement_amounts]: [15]
    - Output [output]: [1; 10]
*)

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

(** ** Complexity *)

(** [@hide] [water_cost] is the cost translation of [water] (the judge
    recomputes it and compares) ... *)
Complexity water_cost for water.

(** [@fold complexity bound] ... and runs in at most c1 * ((n + 1)^2 * (C + k + 1) + p) + c2 steps of the cost model on a valid input, n the number of stations, p of pipes, k of improvements and C the total capacity of the pipes and improvements ([sizes]): every augmentation raises the flow by at least one unit, the flow never exceeds the total capacity, and an augmentation is one breadth-first search over the n x n residual table plus a walk; the n p bound of Edmonds-Karp on the number of augmentations is not stated, for two constants
    quantified before the inputs, on every valid input. [@requirement water_time_spec] *)
Specification water_time : exists c1 c2 : nat,
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
  water_time_spec c1 c2 (size station_count_int) (sizes pipe_capacities_arr) (sizes improvement_amounts_arr) (size improvement_starts_arr) (size pipe_starts_arr) (cost7 water_cost station_count_int pipe_starts_arr pipe_ends_arr pipe_capacities_arr improvement_starts_arr improvement_ends_arr improvement_amounts_arr).

(** [@hide] The permitted kernel primitives and their
    axioms. *)
Allowed Primitive Axioms.
