
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val bsearch :
    sint Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec bsearch x tails v lo hi =
  if bdec (ltb lo hi)
  then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       if bdec (ltsb (get x (get tails mid)) v)
       then bsearch x tails v (add mid (Uint63.of_int (1))) hi
       else bsearch x tails v lo mid
  else lo

(** val main_loop :
    sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t * (Uint63.t Marray.t * Uint63.t Marray.t) **)

let rec main_loop x n i l tails pred =
  if bdec (ltb i n)
  then let v = get x i in
       let k = bsearch x tails v (Uint63.of_int (0)) l in
       let p =
         if eqb k (Uint63.of_int (0))
         then (Uint63.of_int (0))
         else get tails (sub k (Uint63.of_int (1)))
       in
       let pred' = set pred i p in
       let tails' = set tails k i in
       main_loop x n (add i (Uint63.of_int (1)))
         (if eqb k l then add l (Uint63.of_int (1)) else l) tails' pred'
  else (l, (tails, pred))

(** val build :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec build pred c j res =
  if bdec (ltb (Uint63.of_int (0)) c)
  then build pred (sub c (Uint63.of_int (1))) (get pred j)
         (set res (sub c (Uint63.of_int (1))) j)
  else res

(** val lis_impl : sint Marray.t -> uint Marray.t **)

let lis_impl x =
  let n = length x in
  let (l, p) =
    main_loop x n (Uint63.of_int (0)) (Uint63.of_int (0))
      (make n (Uint63.of_int (0))) (make n (Uint63.of_int (0)))
  in
  let (tails, pred) = p in
  build pred l (get tails (sub l (Uint63.of_int (1))))
    (make l (Uint63.of_int (0)))

module LongincsubseqImpl =
 struct
  (** val lis : sint Marray.t -> uint Marray.t **)

  let lis =
    lis_impl
 end
