
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

(** val mark :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
    Marray.t **)

let rec mark c i cnt t j =
  if bdec (ltb t cnt)
  then mark (set c j true) i cnt (add t (Uint63.of_int (1))) (add j i)
  else c

(** val mark_from : bool Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let mark_from c w i =
  let s = mul i i in
  let cnt = add (div (sub w s) i) (Uint63.of_int (1)) in
  mark c i cnt (Uint63.of_int (0)) s

(** val sieve :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let rec sieve c w n i =
  if bdec (ltb i n)
  then if leb (mul i i) w
       then let c' = if get c i then c else mark_from c w i in
            sieve c' w n (add i (Uint63.of_int (1)))
       else c
  else c

(** val find :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t * Uint63.t
    Marray.t **)

let rec find par rk x =
  let y = get par x in
  if eqb y x
  then (x, par)
  else let z = get par y in
       if bdec (ltb (get rk x) (get rk z))
       then find (set par x z) rk z
       else (x, par)

(** val union :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let union par rk u v =
  let (ru, par1) = find par rk u in
  let (rv, par2) = find par1 rk v in
  if eqb ru rv
  then (par2, rk)
  else let ku = get rk ru in
       let kv = get rk rv in
       if ltb ku kv
       then ((set par2 ru rv), rk)
       else if ltb kv ku
            then ((set par2 rv ru), rk)
            else ((set par2 ru rv), (set rk rv (add kv (Uint63.of_int (1)))))

(** val ulink :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec ulink par rk q cnt t o =
  if bdec (ltb t cnt)
  then let (par', rk') = union par rk o (add o q) in
       ulink par' rk' q cnt (add t (Uint63.of_int (1))) (add o q)
  else (par, rk)

(** val first_off : Uint63.t -> Uint63.t -> Uint63.t **)

let first_off a q =
  mod0 (sub q (mod0 a q)) q

(** val uprimes :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec uprimes c a w n par rk q =
  if bdec (ltb q n)
  then let (par', rk') =
         if get c q
         then (par, rk)
         else let o0 = first_off a q in
              ulink par rk q (div (sub w o0) q) (Uint63.of_int (0)) o0
       in
       uprimes c a w n par' rk' (add q (Uint63.of_int (1)))
  else (par, rk)

(** val iota :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec iota par n i =
  if bdec (ltb i n)
  then iota (set par i i) n (add i (Uint63.of_int (1)))
  else par

(** val count :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec count par n o acc =
  if bdec (ltb o n)
  then count par n (add o (Uint63.of_int (1)))
         (if eqb (get par o) o then add acc (Uint63.of_int (1)) else acc)
  else acc

(** val numbersets_impl : uint -> uint -> uint -> uint **)

let numbersets_impl x y z =
  let w = sub y x in
  let n = add w (Uint63.of_int (1)) in
  let c = sieve (make n false) w n (Uint63.of_int (2)) in
  let par0 = iota (make n (Uint63.of_int (0))) n (Uint63.of_int (0)) in
  let rk0 = make n (Uint63.of_int (0)) in
  let (par, _) = uprimes c x w n par0 rk0 z in
  count par n (Uint63.of_int (0)) (Uint63.of_int (0))

(** val numbersets : uint -> uint -> uint -> uint **)

let numbersets =
  numbersets_impl
