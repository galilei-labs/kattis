
(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val is_zero : Uint63.t -> bool **)

let is_zero i =
  eqb i (Uint63.of_int (0))

(** val is_even : Uint63.t -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val m : Uint63.t **)

let m =
  (Uint63.of_int (1000000007))

(** val pow_loop : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pow_loop b e acc =
  if bdec (ltb (Uint63.of_int (0)) e)
  then pow_loop (mod0 (mul b b) m) (lsr0 e (Uint63.of_int (1)))
         (if is_even e then acc else mod0 (mul acc b) m)
  else acc

(** val powmod : Uint63.t -> Uint63.t -> Uint63.t **)

let powmod b e =
  pow_loop (mod0 b m) e (Uint63.of_int (1))

(** val cross_loop :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec cross_loop i r j s =
  if bdec (leb j r)
  then let j' = add j i in
       if bdec (ltb j j')
       then cross_loop i r j' (set s j (Uint63.of_int (0)))
       else set s j (Uint63.of_int (0))
  else s

(** val sieve_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec sieve_loop r i s =
  if bdec (leb (mul i i) r)
  then let s' =
         if eqb (get s i) (Uint63.of_int (0))
         then s
         else cross_loop i r (mul i i) s
       in
       if bdec (ltb i (add i (Uint63.of_int (1))))
       then sieve_loop r (add i (Uint63.of_int (1))) s'
       else s'
  else s

(** val sieve : Uint63.t -> Uint63.t Marray.t **)

let sieve r =
  sieve_loop r (Uint63.of_int (2))
    (set
      (set (make (add r (Uint63.of_int (1))) (Uint63.of_int (1)))
        (Uint63.of_int (0)) (Uint63.of_int (0)))
      (Uint63.of_int (1)) (Uint63.of_int (0)))

(** val prod_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let rec prod_loop s e l p acc =
  let acc' =
    if eqb (get s p) (Uint63.of_int (0))
    then acc
    else mod0 (mul (powmod p e) acc) m
  in
  if bdec (ltb l p)
  then prod_loop s e l (sub p (Uint63.of_int (1))) acc'
  else acc'

(** val primepower_impl : uint -> uint -> uint -> uint **)

let primepower_impl e l r =
  if ltb r l
  then (Uint63.of_int (1))
  else prod_loop (sieve r) e l r (Uint63.of_int (1))

(** val primepower : uint -> uint -> uint -> uint **)

let primepower =
  primepower_impl
