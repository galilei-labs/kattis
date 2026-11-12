
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

(** val sqrt : Float64.t -> Float64.t **)

let sqrt = Float64.sqrt

(** val ltb0 : Float64.t -> Float64.t -> bool **)

let ltb0 = Float64.lt

(** val add0 : Float64.t -> Float64.t -> Float64.t **)

let add0 = Float64.add

(** val sub0 : Float64.t -> Float64.t -> Float64.t **)

let sub0 = Float64.sub

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

type uint = Uint63.t

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val wloop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let rec wloop hi f i s =
  if bdec (ltb i hi)
  then wloop hi f (add i (Uint63.of_int (1))) (f i s)
  else s

(** val loop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let loop =
  wloop

(** val dsq :
    sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let dsq x y i j =
  let dx = sub (get x i) (get x j) in
  let dy = sub (get y i) (get y j) in add (mul dx dx) (mul dy dy)

(** val wt :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Uint63.t
    -> Float64.t **)

let wt x y r i j =
  sub0 (sqrt (of_uint63 (dsq x y i j))) (of_uint63 (add (get r i) (get r j)))

(** val init_step :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Float64.t
    Marray.t -> Float64.t Marray.t **)

let init_step x y r v key =
  set key v (wt x y r (Uint63.of_int (0)) v)

(** val amin_step :
    Uint63.t -> bool Marray.t -> Float64.t Marray.t -> Uint63.t ->
    (Uint63.t * Float64.t) -> Uint63.t * Float64.t **)

let amin_step n inT key v st = match st with
| (b, bv) ->
  if get inT v
  then st
  else if eqb b n
       then (v, (get key v))
       else if ltb0 (get key v) bv then (v, (get key v)) else st

(** val upd_step :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> bool Marray.t ->
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t **)

let upd_step x y r inT b v key =
  if get inT v
  then key
  else let wv = wt x y r b v in
       if ltb0 wv (get key v) then set key v wv else key

(** val prim_step :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> Uint63.t -> Uint63.t
    -> ((bool Marray.t * Float64.t Marray.t) * Float64.t) -> (bool
    Marray.t * Float64.t Marray.t) * Float64.t **)

let prim_step x y r n _ = function
| (p, tot) ->
  let (inT, key) = p in
  let (b, _) = loop n (amin_step n inT key) (Uint63.of_int (0)) (n, zero) in
  let tot0 = add0 tot (get key b) in
  let inT0 = set inT b true in
  let key0 = loop n (upd_step x y r inT0 b) (Uint63.of_int (0)) key in
  ((inT0, key0), tot0)

(** val comsat :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> Float64.t **)

let comsat x y r =
  let n = length x in
  let inT = set (make n false) (Uint63.of_int (0)) true in
  let key = loop n (init_step x y r) (Uint63.of_int (0)) (make n zero) in
  let (_, tot) =
    loop n (prim_step x y r n) (Uint63.of_int (1)) ((inT, key), zero)
  in
  tot

(** val communicationssatellite :
    sint Marray.t -> sint Marray.t -> uint Marray.t -> Float64.t **)

let communicationssatellite =
  comsat
