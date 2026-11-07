
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

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

(** val inf : Uint63.t **)

let inf =
  (Uint63.of_int (-1))

(** val min_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec min_loop g n i best =
  if bdec (ltb i n)
  then min_loop g n (add i (Uint63.of_int (1)))
         (if ltb (get g i) best then get g i else best)
  else best

(** val gcd_loop : Uint63.t -> Uint63.t -> Uint63.t **)

let rec gcd_loop u v =
  if bdec (eqb v (Uint63.of_int (0))) then u else gcd_loop v (mod0 u v)

(** val nxt : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let nxt m a' x =
  let y = add x a' in if ltb y m then y else sub y m

(** val scan :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec scan a m a' l j x p =
  if bdec (ltb j l)
  then scan a m a' l (add j (Uint63.of_int (1))) (nxt m a' x)
         (if ltb (get a x) (get a p) then x else p)
  else p

(** val relax :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec relax m a a' l1 j x cur a0 =
  if bdec (ltb j l1)
  then let y = nxt m a' x in
       let c = add cur a in
       let v = get a0 y in
       if ltb c v
       then relax m a a' l1 (add j (Uint63.of_int (1))) y c (set a0 y c)
       else relax m a a' l1 (add j (Uint63.of_int (1))) y v a0
  else a0

(** val classes :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec classes m a a' d l c a0 =
  if bdec (ltb c d)
  then let p = scan a0 m a' l (Uint63.of_int (0)) c c in
       let v = get a0 p in
       classes m a a' d l (add c (Uint63.of_int (1)))
         (if eqb v inf
          then a0
          else relax m a a' (sub l (Uint63.of_int (1))) (Uint63.of_int (0)) p
                 v a0)
  else a0

(** val item :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let item m a a0 =
  let a' = mod0 a m in
  let d = gcd_loop m a' in classes m a a' d (div m d) (Uint63.of_int (0)) a0

(** val items :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec items g n m i a =
  if bdec (ltb i n)
  then items g n m (add i (Uint63.of_int (1))) (item m (get g i) a)
  else a

(** val fillable_core : Uint63.t -> Uint63.t Marray.t -> bool **)

let fillable_core k g =
  let n = length g in
  let m = min_loop g n (Uint63.of_int (1)) (get g (Uint63.of_int (0))) in
  let a =
    items g n m (Uint63.of_int (0))
      (set (make m inf) (Uint63.of_int (0)) (Uint63.of_int (0)))
  in
  leb (get a (mod0 k m)) k

(** val fillable_impl : uint -> uint Marray.t -> bool **)

let fillable_impl =
  fillable_core

module Knapsack2Impl =
 struct
  (** val fillable : uint -> uint Marray.t -> bool **)

  let fillable =
    fillable_impl
 end
