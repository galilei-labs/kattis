
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

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

type uint = Uint63.t

val bdec : bool -> bool

val nil : Uint63.t

type fh = { hkey : Uint63.t Marray.t; hpar : Uint63.t Marray.t;
            hchd : Uint63.t Marray.t; hlft : Uint63.t Marray.t;
            hrgt : Uint63.t Marray.t; hdeg : Uint63.t Marray.t;
            hmrk : Uint63.t Marray.t; hbuf : Uint63.t Marray.t;
            hmin : Uint63.t }

val s_key : fh -> Uint63.t -> Uint63.t -> fh

val s_par : fh -> Uint63.t -> Uint63.t -> fh

val s_chd : fh -> Uint63.t -> Uint63.t -> fh

val s_lft : fh -> Uint63.t -> Uint63.t -> fh

val s_rgt : fh -> Uint63.t -> Uint63.t -> fh

val s_deg : fh -> Uint63.t -> Uint63.t -> fh

val s_mrk : fh -> Uint63.t -> Uint63.t -> fh

val s_buf : fh -> Uint63.t -> Uint63.t -> fh

val s_min : fh -> Uint63.t -> fh

val ring_ins : fh -> Uint63.t -> Uint63.t -> fh

val root_add : fh -> Uint63.t -> fh

val fh_insert : fh -> Uint63.t -> Uint63.t -> fh

val fh_cut : fh -> Uint63.t -> Uint63.t -> fh

val ccut : fh -> Uint63.t -> Uint63.t -> fh

val fh_decrease : fh -> Uint63.t -> Uint63.t -> fh

val fh_link : fh -> Uint63.t -> Uint63.t -> fh

val link_loop : fh -> Uint63.t -> Uint63.t -> Uint63.t -> fh * Uint63.t

val proc : fh -> Uint63.t -> Uint63.t -> fh * Uint63.t

val walk : fh -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> fh * Uint63.t

val rebuild : fh -> Uint63.t -> Uint63.t -> fh

val fh_extract : fh -> fh * Uint63.t

val build :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t

val relax :
  fh -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> fh * Uint63.t Marray.t

val edges :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (fh * Uint63.t Marray.t) ->
  Uint63.t -> fh * Uint63.t Marray.t

val expand :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> (fh * Uint63.t Marray.t) -> Uint63.t -> fh * Uint63.t Marray.t

val dijk :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> (fh * Uint63.t Marray.t) -> Uint63.t -> Uint63.t option

val query :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t option

val qloop :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t option
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t option Marray.t

val fulltank_impl :
  uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t ->
  uint Marray.t -> uint Marray.t -> uint Marray.t -> uint option Marray.t

val fulltank :
  uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t ->
  uint Marray.t -> uint Marray.t -> uint Marray.t -> uint option Marray.t
