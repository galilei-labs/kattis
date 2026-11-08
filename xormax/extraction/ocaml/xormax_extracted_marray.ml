
(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val reduce :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec reduce b c i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then if eqb (lsr0 c (sub i (Uint63.of_int (1)))) (Uint63.of_int (0))
       then reduce b c (sub i (Uint63.of_int (1)))
       else let bk = get b (sub i (Uint63.of_int (1))) in
            if eqb bk (Uint63.of_int (0))
            then set b (sub i (Uint63.of_int (1))) c
            else reduce b (lxor0 c bk) (sub i (Uint63.of_int (1)))
  else b

(** val build :
    uint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t **)

let rec build x n j b =
  if bdec (ltb j n)
  then build x n (add j (Uint63.of_int (1)))
         (reduce b (get x j) (Uint63.of_int (63)))
  else b

(** val greedy : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec greedy b r i =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let r' = lxor0 r (get b (sub i (Uint63.of_int (1)))) in
       greedy b (if ltb r r' then r' else r) (sub i (Uint63.of_int (1)))
  else r

(** val xormax_impl : uint Marray.t -> uint **)

let xormax_impl x =
  let b =
    build x (length x) (Uint63.of_int (0))
      (make (Uint63.of_int (63)) (Uint63.of_int (0)))
  in
  greedy b (Uint63.of_int (0)) (Uint63.of_int (63))

(** val xormax : uint Marray.t -> uint **)

let xormax =
  xormax_impl
