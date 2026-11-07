
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val row_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec row_loop y ai i lb j r =
  if bdec (ltb j lb)
  then let k = add i j in
       row_loop y ai i lb (add j (Uint63.of_int (1)))
         (set r k (add (get r k) (mul ai (get y j))))
  else r

(** val rows_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec rows_loop x y la lb i r =
  if bdec (ltb i la)
  then rows_loop x y la lb (add i (Uint63.of_int (1)))
         (row_loop y (get x i) i lb (Uint63.of_int (0)) r)
  else r

(** val polymul_impl : sint Marray.t -> sint Marray.t -> sint Marray.t **)

let polymul_impl x y =
  let la = length x in
  let lb = length y in
  if eqb la (Uint63.of_int (0))
  then make (Uint63.of_int (0)) (Uint63.of_int (0))
  else if eqb lb (Uint63.of_int (0))
       then make (Uint63.of_int (0)) (Uint63.of_int (0))
       else rows_loop x y la lb (Uint63.of_int (0))
              (make (sub (add la lb) (Uint63.of_int (1))) (Uint63.of_int (0)))

module Polymul1Impl =
 struct
  (** val polymul : sint Marray.t -> sint Marray.t -> sint Marray.t **)

  let polymul =
    polymul_impl
 end
