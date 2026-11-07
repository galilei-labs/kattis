
(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val xor_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec xor_loop a n i acc =
  if bdec (ltb i n)
  then xor_loop a n (add i (Uint63.of_int (1))) (lxor0 acc (get a i))
  else acc

(** val odd_one_impl : uint Marray.t -> uint **)

let odd_one_impl a =
  xor_loop a (length a) (Uint63.of_int (0)) (Uint63.of_int (0))

module OddmanoutImpl =
 struct
  (** val odd_one : uint Marray.t -> uint **)

  let odd_one =
    odd_one_impl
 end
