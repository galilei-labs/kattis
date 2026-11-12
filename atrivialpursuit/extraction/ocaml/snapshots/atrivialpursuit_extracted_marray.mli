
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val lsr0 : Uint63.t -> Uint63.t -> Uint63.t

val land0 : Uint63.t -> Uint63.t -> Uint63.t

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val mulc : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val div : Uint63.t -> Uint63.t -> Uint63.t

val mod0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb : Uint63.t -> Uint63.t -> bool

val ltb : Uint63.t -> Uint63.t -> bool

val leb : Uint63.t -> Uint63.t -> bool

val diveucl_21 : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val make : Uint63.t -> 'a1 -> 'a1 Marray.t

val get : 'a1 Marray.t -> Uint63.t -> 'a1

val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t

val length : 'a1 Marray.t -> Uint63.t

val copy : 'a1 Marray.t -> 'a1 Marray.t

type uint = Uint63.t

val bdec : bool -> bool

val lIM : Uint63.t

val mulmod : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val pow_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val powmod : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t

val igcd : Uint63.t -> Uint63.t -> Uint63.t

val isq_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val isqrt : Uint63.t -> Uint63.t

val divfull : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val divpass :
  Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t Marray.t * Uint63.t

val mark_loop : bool Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t

val sieve_loop :
  bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t
  Marray.t * Uint63.t

val sieve : Uint63.t Marray.t * Uint63.t

val strip2 : Uint63.t -> Uint63.t -> Uint63.t * Uint63.t

val mr_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val mr_base : Uint63.t -> Uint63.t -> bool

val mr_comp : Uint63.t -> bool

type bres =
| BFound
| BComp
| BFail

val aLIM : Uint63.t

val find_base : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bres

val td_cert :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> (bres * Uint63.t) * Uint63.t

val rho_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val rHOC : Uint63.t

val rho_try : Uint63.t -> Uint63.t -> Uint63.t

type cres =
| CPrime
| CComp
| CFail

val t12 : Uint63.t

val base_res : bres -> cres

val certify : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> cres

val td_loop : Uint63.t -> Uint63.t -> bool

type kind =
| KPrime
| KSquare
| KSemi

val classify : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> kind

val mODP : Uint63.t

val fmod : Uint63.t -> Uint63.t -> Uint63.t

val contrib :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t

val step_acc :
  Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t) -> Uint63.t

val ph1 :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
  Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
  Marray.t * Uint63.t Marray.t) * Uint63.t

val refine : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val sel_get :
  bool -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t

val peel :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> bool -> Uint63.t -> Uint63.t -> Uint63.t ->
  (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

val ph2 :
  Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
  Uint63.t -> Uint63.t -> bool -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t

val atp_impl : uint -> uint Marray.t -> uint Marray.t -> uint

val atrivialpursuit : uint -> uint Marray.t -> uint Marray.t -> uint
