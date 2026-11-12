
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

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

val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t

val igcd : Uint63.t -> Uint63.t -> Uint63.t

val capf : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val fill_row :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t Marray.t

val fill_tab :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
  Marray.t

val amin : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val amax : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val rng_ok : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool

val sat :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> ((Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t

val amap :
  (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t Marray.t -> Uint63.t ->
  Uint63.t -> Uint63.t Marray.t

val relaxF :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t

val has_val : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val lscan :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t Marray.t

val layers :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val bfs : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val maxF : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t

val glob :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t

val cntl :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t

val count : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t

val rmin :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  -> Uint63.t -> Uint63.t

val no_height : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val liftF : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val lift : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t

val cnt_lift :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t Marray.t

val active :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> bool

val find_act :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> Uint63.t -> Uint63.t

val adm :
  Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  -> bool

val enq_pos : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

type st = { s_tbl : Uint63.t Marray.t; s_ex : Uint63.t Marray.t;
            s_h : Uint63.t Marray.t; s_cur : Uint63.t Marray.t;
            s_cnt : Uint63.t Marray.t; s_q : Uint63.t Marray.t;
            s_qh : Uint63.t; s_ql : Uint63.t; s_cu : Uint63.t; s_rl : 
            Uint63.t }

val mloop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
  -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val nn : Uint63.t Marray.t -> Uint63.t

val ss : Uint63.t Marray.t -> Uint63.t

val tt : Uint63.t Marray.t -> Uint63.t

val guard : Uint63.t Marray.t -> bool

val init_state : Uint63.t Marray.t -> st

val mazemovement_impl : uint Marray.t -> uint

val mazemovement : uint Marray.t -> uint
