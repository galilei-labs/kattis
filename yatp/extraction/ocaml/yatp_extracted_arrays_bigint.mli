
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val iNF : Uint63.t

val max_loop : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val true_loop : Uint63.t -> Uint63.t -> bool array -> bool array

val hsrc : Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t

val hdst : Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t

val deg_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array
  -> Uint63.t array

val start_loop :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array
  -> Uint63.t array * Uint63.t array

val fill_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t
  -> Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t
  array * Uint63.t array

type bst = { b_vis : Uint63.t array; b_comp : Uint63.t array;
             b_par : Uint63.t array; b_d : Uint63.t array; b_tail : Uint63.t;
             b_flag : bool }

val scan_step :
  bool array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  bst -> bst

val scan_loop :
  Uint63.t array -> Uint63.t array -> bool array -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst

val bfs_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
  Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst

val bfs_init :
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array
  -> Uint63.t array -> bst

val bfs :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
  Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array
  -> Uint63.t array -> bst

val rscan :
  Uint63.t array -> Uint63.t array -> bool array -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t array -> bool -> Uint63.t array * bool

val rpass :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> bool ->
  Uint63.t array * bool

val rloop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
  Uint63.t array -> Uint63.t -> Uint63.t array -> Uint63.t array

val relax :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> bool array ->
  Uint63.t array -> Uint63.t -> bst -> Uint63.t array

val sz_init :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array
  -> Uint63.t array * Uint63.t array

val sz_acc :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t array -> Uint63.t
  array -> Uint63.t array * Uint63.t array

val argmin :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> Uint63.t

val centroid :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  Uint63.t -> Uint63.t * (Uint63.t array * Uint63.t array)

type lct = { l_st : Uint63.t array; l_m : Uint63.t array; l_b : Uint63.t array }

val lkey : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val lc_insert :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> lct
  -> lct

val lc_query :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> lct -> Uint63.t

val ins_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> lct -> lct

val qry_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t -> lct -> Uint63.t array -> Uint63.t array

type mst = { m_vis : Uint63.t array; m_comp : Uint63.t array;
             m_par : Uint63.t array; m_d : Uint63.t array;
             m_sz : Uint63.t array; m_big : Uint63.t array; m_T : lct;
             m_best : Uint63.t array }

val pick : bool array -> Uint63.t -> Uint63.t -> Uint63.t

val process :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  Uint63.t -> bool array -> Uint63.t -> Uint63.t -> mst -> Uint63.t * mst

val main_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  Uint63.t -> Uint63.t -> Uint63.t -> bool array -> mst -> Uint63.t array

val sum_loop : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val yatp_impl :
  Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
  Uint63.t

val yatp : uint array -> uint array -> uint array -> uint array -> uint
