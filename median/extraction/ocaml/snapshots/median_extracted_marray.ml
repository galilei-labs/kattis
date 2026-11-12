
(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

(** val div0 : Float64.t -> Float64.t -> Float64.t **)

let div0 = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val swap_with :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let swap_with y i j v =
  let w = get y i in set (set y i v) j w

(** val tst : bool -> Uint63.t -> Uint63.t -> bool **)

let tst strict x v =
  if strict then ltb v x else leb v x

(** val part :
    bool -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    -> Uint63.t Marray.t * Uint63.t **)

let rec part strict x hi y i j =
  if bdec (ltb j hi)
  then let v = get y j in
       if tst strict x v
       then part strict x hi (swap_with y i j v) (add i (Uint63.of_int (1)))
              (add j (Uint63.of_int (1)))
       else part strict x hi y i (add j (Uint63.of_int (1)))
  else (y, i)

(** val lcg : Uint63.t -> Uint63.t **)

let lcg s =
  add (mul s (Uint63.of_int (-2859235813007982803)))
    (Uint63.of_int (1442695040888963407))

(** val sel :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec sel k y lo hi seed =
  if bdec (ltb lo hi)
  then let s = lcg seed in
       let x = get y (add lo (mod0 (lsr0 s (Uint63.of_int (17))) (sub hi lo)))
       in
       let (y1, i) = part true x hi y lo lo in
       let (y2, m) = part false x hi y1 i i in
       if ltb k i
       then if bdec (ltb i hi) then sel k y2 lo i s else y2
       else if ltb k m
            then y2
            else if bdec (ltb lo m) then sel k y2 m hi s else y2
  else y

(** val maxl :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec maxl y k j acc =
  if bdec (ltb j k)
  then let v = get y j in
       maxl y k (add j (Uint63.of_int (1))) (if ltb acc v then v else acc)
  else acc

(** val seed0 : Uint63.t **)

let seed0 =
  (Uint63.of_int (88172645463325252))

(** val median_impl : uint Marray.t -> Float64.t **)

let median_impl x =
  let n = length x in
  let k = div n (Uint63.of_int (2)) in
  let y = sel k (copy x) (Uint63.of_int (0)) n seed0 in
  let u = get y k in
  if eqb (mod0 n (Uint63.of_int (2))) (Uint63.of_int (1))
  then of_uint63 u
  else let w = maxl y k (Uint63.of_int (1)) (get y (Uint63.of_int (0))) in
       div0 (of_uint63 (add w u)) (of_uint63 (Uint63.of_int (2)))

(** val median : uint Marray.t -> Float64.t **)

let median =
  median_impl
