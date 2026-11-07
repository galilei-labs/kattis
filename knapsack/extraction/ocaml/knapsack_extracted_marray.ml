
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

(** val item_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> bool
    Marray.t -> Uint63.t Marray.t * bool Marray.t **)

let rec item_loop v w base k row dec =
  if bdec (ltb w k)
  then let c = sub k (Uint63.of_int (1)) in
       let cand = add (get row (sub c w)) v in
       if ltb (get row c) cand
       then item_loop v w base c (set row c cand) (set dec (add base c) true)
       else item_loop v w base c row dec
  else (row, dec)

(** val items_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t
    Marray.t * bool Marray.t **)

let rec items_loop xv xw n c1 i row dec =
  if bdec (ltb i n)
  then let rd = item_loop (get xv i) (get xw i) (mul i c1) c1 row dec in
       items_loop xv xw n c1 (add i (Uint63.of_int (1))) (fst rd) (snd rd)
  else (row, dec)

(** val walk :
    Uint63.t Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t * Uint63.t Marray.t **)

let rec walk xw dec c1 i c k out =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let j = sub i (Uint63.of_int (1)) in
       if get dec (add (mul j c1) c)
       then walk xw dec c1 j (sub c (get xw j)) (add k (Uint63.of_int (1)))
              (set out k j)
       else walk xw dec c1 j c k out
  else (k, out)

(** val copy_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec copy_loop src dst m j =
  if bdec (ltb j m)
  then copy_loop src (set dst j (get src j)) m (add j (Uint63.of_int (1)))
  else dst

(** val knapsack_impl :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t * Uint63.t
    Marray.t **)

let knapsack_impl cw xv xw =
  let n = length xv in
  let c1 = add cw (Uint63.of_int (1)) in
  let rd =
    items_loop xv xw n c1 (Uint63.of_int (0)) (make c1 (Uint63.of_int (0)))
      (make (mul n c1) false)
  in
  let bestv = get (fst rd) cw in
  let ko =
    walk xw (snd rd) c1 n cw (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
  in
  let k = fst ko in
  (bestv,
  (copy_loop (snd ko) (make k (Uint63.of_int (0))) k (Uint63.of_int (0))))

module KnapsackImpl =
 struct
  (** val knapsack :
      uint -> uint Marray.t -> uint Marray.t -> uint * uint Marray.t **)

  let knapsack =
    knapsack_impl
 end
