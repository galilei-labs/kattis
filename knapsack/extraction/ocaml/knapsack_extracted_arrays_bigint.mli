
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

val add : Uint63.t -> Uint63.t -> Uint63.t

val sub : Uint63.t -> Uint63.t -> Uint63.t

val mul : Uint63.t -> Uint63.t -> Uint63.t

val ltb : Uint63.t -> Uint63.t -> bool

type uint = Uint63.t

val bdec : bool -> bool

val item_loop :
  Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> bool
  array -> Uint63.t array * bool array

val items_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t array -> bool array -> Uint63.t array * bool array

val walk :
  Uint63.t array -> bool array -> Uint63.t -> Uint63.t -> Uint63.t ->
  Uint63.t -> Uint63.t array -> Uint63.t * Uint63.t array

val copy_loop :
  Uint63.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array

val knapsack_impl :
  Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t * Uint63.t array

val knapsack : uint -> uint array -> uint array -> uint * uint array
