
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val div2 : positive -> positive **)

  let div2 = function
  | XI p0 -> p0
  | XO p0 -> p0
  | XH -> XH

  (** val div2_up : positive -> positive **)

  let div2_up = function
  | XI p0 -> succ p0
  | XO p0 -> p0
  | XH -> XH

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val div2 : z -> z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | XH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val shiftl : z -> z -> z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (XO XH))) a p
  | Zneg p -> Pos.iter div2 a p
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

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

(** val ltb1 : Float64.t -> Float64.t -> bool **)

let ltb1 = Float64.lt

(** val mul0 : Float64.t -> Float64.t -> Float64.t **)

let mul0 = Float64.mul

(** val add1 : Float64.t -> Float64.t -> Float64.t **)

let add1 = Float64.add

(** val sub1 : Float64.t -> Float64.t -> Float64.t **)

let sub1 = Float64.sub

(** val div0 : Float64.t -> Float64.t -> Float64.t **)

let div0 = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

(** val normfr_mantissa : Float64.t -> Uint63.t **)

let normfr_mantissa = Float64.normfr_mantissa

(** val frshiftexp : Float64.t -> Float64.t * Uint63.t **)

let frshiftexp = Float64.frshiftexp

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val wloop :
    Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
    Uint63.t -> 'a1 -> 'a1 **)

let rec wloop hi cont f i s =
  if bdec (ltb0 i hi)
  then if cont i s
       then wloop hi cont f (add0 i (Uint63.of_int (1))) (f i s)
       else s
  else s

(** val loop :
    Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
    Uint63.t -> 'a1 -> 'a1 **)

let loop =
  wloop

(** val zofi_rec : Uint63.t -> z **)

let rec zofi_rec i =
  if bdec (eqb i (Uint63.of_int (0)))
  then Z0
  else let r = zofi_rec (div i (Uint63.of_int (2))) in
       let bit =
         if eqb (mod0 i (Uint63.of_int (2))) (Uint63.of_int (0))
         then Z0
         else Zpos XH
       in
       Z.add (Z.mul (Zpos (XO XH)) r) bit

(** val zofi : Uint63.t -> z **)

let zofi =
  zofi_rec

(** val dal : (z * z) -> z -> z **)

let dal d e =
  Z.shiftl (fst d) (Z.sub (snd d) e)

(** val dadd : (z * z) -> (z * z) -> z * z **)

let dadd a b =
  let e = Z.min (snd a) (snd b) in ((Z.add (dal a e) (dal b e)), e)

(** val dsub : (z * z) -> (z * z) -> z * z **)

let dsub a b =
  let e = Z.min (snd a) (snd b) in ((Z.sub (dal a e) (dal b e)), e)

(** val dmul : (z * z) -> (z * z) -> z * z **)

let dmul a b =
  ((Z.mul (fst a) (fst b)), (Z.add (snd a) (snd b)))

(** val dlt : (z * z) -> (z * z) -> bool **)

let dlt a b =
  let e = Z.min (snd a) (snd b) in Z.ltb (dal a e) (dal b e)

(** val fex : Float64.t -> z * z **)

let fex f =
  let (z0, e) = frshiftexp f in
  let m = zofi (normfr_mantissa z0) in
  ((if ltb1 f (Float64.of_float (0x0p+0)) then Z.opp m else m),
  (Z.sub (zofi e) (Zpos (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO
    XH))))))))))))))

(** val dex :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t -> z * z **)

let dex x y a b =
  let dx = dsub (fex (get x a)) (fex (get x b)) in
  let dy = dsub (fex (get y a)) (fex (get y b)) in
  dadd (dmul dx dx) (dmul dy dy)

(** val fd :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t ->
    Float64.t **)

let fd x y a b =
  let dx = sub1 (get x a) (get x b) in
  let dy = sub1 (get y a) (get y b) in add1 (mul0 dx dx) (mul0 dy dy)

(** val gx : Float64.t -> Float64.t -> Float64.t **)

let gx m p =
  let d = sub1 m p in mul0 d d

(** val c1e5 : Float64.t **)

let c1e5 =
  of_uint63 (Uint63.of_int (100000))

(** val c52 : Float64.t **)

let c52 =
  of_uint63 (Uint63.of_int (4503599627370496))

(** val cinit : Float64.t **)

let cinit =
  of_uint63 (Uint63.of_int (200001))

(** val tol : Float64.t **)

let tol =
  div0 (of_uint63 (Uint63.of_int (1))) (of_uint63 (Uint63.of_int (1024)))

(** val key : Float64.t -> Uint63.t -> Float64.t -> Uint63.t **)

let key s n1 f =
  let u = add1 (mul0 (add1 f c1e5) s) c52 in
  let k =
    sub0 (normfr_mantissa (fst (frshiftexp u)))
      (Uint63.of_int (4503599627370496))
  in
  if ltb0 k n1 then k else n1

(** val key_step :
    Float64.t Marray.t -> Float64.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let key_step x s n1 i k =
  set k i (key s n1 (get x i))

(** val count_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let count_step k i c =
  let b = get k i in let v = get c b in set c b (add0 v (Uint63.of_int (1)))

(** val prefix_step :
    Uint63.t -> (Uint63.t Marray.t * Uint63.t) -> Uint63.t Marray.t * Uint63.t **)

let prefix_step b = function
| (c, acc) -> let v = get c b in ((set c b acc), (add0 acc v))

(** val place_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t)
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let place_step k i = function
| (p, c) ->
  let b = get k i in
  let v = get c b in ((set p v i), (set c b (add0 v (Uint63.of_int (1)))))

(** val min_step :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Float64.t Marray.t
    -> Float64.t Marray.t **)

let min_step x k i m =
  let b = get k i in
  let xi = get x i in if ltb1 xi (get m b) then set m b xi else m

(** val cand_step :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> ((Float64.t * Uint63.t) * Uint63.t) ->
    (Float64.t * Uint63.t) * Uint63.t **)

let cand_step x y p p0 c st = match st with
| (p1, bj) ->
  let (bf, bi) = p1 in
  let q = get p c in
  let f = fd x y p0 q in
  if ltb1 (add1 bf tol) f
  then st
  else if dlt (dex x y p0 q) (dex x y bi bj) then ((f, p0), q) else st

(** val cand_cont :
    Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    ((Float64.t * Uint63.t) * Uint63.t) -> bool **)

let cand_cont x k m p p0 kp c = function
| (p1, _) ->
  let (bf, _) = p1 in
  let kq = get k (get p c) in
  if ltb0 kp kq
  then negb (ltb1 (add1 bf tol) (gx (get m kq) (get x p0)))
  else true

(** val sweep_step :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t ->
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    ((Float64.t * Uint63.t) * Uint63.t) -> (Float64.t * Uint63.t) * Uint63.t **)

let sweep_step x y k m p n a st =
  let p0 = get p a in
  loop n (cand_cont x k m p p0 (get k p0)) (cand_step x y p p0)
    (add0 a (Uint63.of_int (1))) st

(** val closestpair :
    Float64.t Marray.t -> Float64.t Marray.t -> uint * uint **)

let closestpair x y =
  let n = length x in
  if leb (Uint63.of_int (2)) n
  then let s = div0 (of_uint63 n) cinit in
       let n1 = sub0 n (Uint63.of_int (1)) in
       let k =
         loop n (fun _ _ -> true) (key_step x s n1) (Uint63.of_int (0))
           (make n (Uint63.of_int (0)))
       in
       let c =
         loop n (fun _ _ -> true) (count_step k) (Uint63.of_int (0))
           (make n (Uint63.of_int (0)))
       in
       let (c0, _) =
         loop n (fun _ _ -> true) prefix_step (Uint63.of_int (0)) (c,
           (Uint63.of_int (0)))
       in
       let (p, _) =
         loop n (fun _ _ -> true) (place_step k) (Uint63.of_int (0))
           ((make n (Uint63.of_int (0))), c0)
       in
       let m =
         loop n (fun _ _ -> true) (min_step x k) (Uint63.of_int (0))
           (make n cinit)
       in
       let (p0, j) =
         loop n (fun _ _ -> true) (sweep_step x y k m p n)
           (Uint63.of_int (0))
           (((fd x y (Uint63.of_int (0)) (Uint63.of_int (1))),
           (Uint63.of_int (0))), (Uint63.of_int (1)))
       in
       let (_, i) = p0 in (i, j)
  else ((Uint63.of_int (0)), (Uint63.of_int (1)))

module Closestpair1Impl =
 struct
  (** val closestpair :
      Float64.t Marray.t -> Float64.t Marray.t -> uint * uint **)

  let closestpair =
    closestpair
 end
