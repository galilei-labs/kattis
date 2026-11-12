
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val count_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec count_loop x n i acc =
  if bdec (ltb i n)
  then count_loop x n (add i (Uint63.of_int (1)))
         (if ltsb (get x i) (Uint63.of_int (0))
          then add acc (Uint63.of_int (1))
          else acc)
  else acc

(** val count_negatives_impl : sint Marray.t -> uint **)

let count_negatives_impl x =
  let n = length x in count_loop x n (Uint63.of_int (0)) (Uint63.of_int (0))

(** val count_negatives : sint Marray.t -> uint **)

let count_negatives =
  count_negatives_impl
