
val negb : bool -> bool



val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

val ltsb : Uint63.t -> Uint63.t -> bool

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

type sint = Uint63.t

type 'a answer =
| Impossible
| NegInfinity
| Distance of 'a

val bdec : bool -> bool

val for_acc : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val for_loop : (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1

val swap : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val sift_up : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val sift_down : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val hpush : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val hpop : Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t Marray.t

val adj_step :
  Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) ->
  Uint63.t Marray.t * Uint63.t Marray.t

val build_adj :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t
  Marray.t

val chain_acc :
  Uint63.t Marray.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val chain_fold :
  Uint63.t Marray.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1

val bfs_visit :
  Uint63.t Marray.t -> Uint63.t -> ((bool Marray.t * Uint63.t
  Marray.t) * Uint63.t) -> (bool Marray.t * Uint63.t Marray.t) * Uint63.t

val bfs_acc :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> ((bool Marray.t * Uint63.t Marray.t) * Uint63.t) -> bool
  Marray.t

val seed_step :
  bool Marray.t -> Uint63.t -> ((bool Marray.t * Uint63.t
  Marray.t) * Uint63.t) -> (bool Marray.t * Uint63.t Marray.t) * Uint63.t

val closure :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  bool Marray.t -> bool Marray.t

val copy_step :
  Uint63.t -> Uint63.t -> bool Marray.t -> Uint63.t -> bool Marray.t -> bool
  Marray.t

val reach_row :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> bool Marray.t -> bool Marray.t

val reach_matrix :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  bool Marray.t

val bf_edge :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t ->
  bool) -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val bf_round :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  (Uint63.t -> bool) -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t

val bf :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> (Uint63.t -> bool) -> Uint63.t Marray.t

val bad_step :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> bool Marray.t -> bool
  Marray.t

val iNF : Uint63.t

val relax :
  Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool Marray.t ->
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t) -> (Uint63.t Marray.t * Uint63.t
  Marray.t) * Uint63.t

val dij_body :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> bool Marray.t -> Uint63.t Marray.t -> (((Uint63.t
  Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t) -> ((Uint63.t
  Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t

val dij_acc :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
  (((Uint63.t Marray.t * bool Marray.t) * Uint63.t Marray.t) * Uint63.t) ->
  Uint63.t Marray.t

val dijkstra :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t Marray.t

val cell :
  Uint63.t -> bool Marray.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t answer

val negseed_step :
  Uint63.t -> bool Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> bool
  Marray.t -> bool Marray.t

val row_of :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t answer Marray.t

val apsp_rows :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool Marray.t -> Uint63.t
  Marray.t -> Uint63.t answer Marray.t Marray.t

val apsp_core :
  Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t answer
  Marray.t Marray.t

val allpairspath_impl :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t answer Marray.t Marray.t

val allpairspath :
  uint -> uint Marray.t -> uint Marray.t -> sint Marray.t -> sint answer
  Marray.t Marray.t
