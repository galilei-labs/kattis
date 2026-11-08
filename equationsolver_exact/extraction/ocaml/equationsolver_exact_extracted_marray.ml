
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

type nat =
| O
| S of nat

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

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> false)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> false)
    | XH -> (match q with
             | XH -> true
             | _ -> false)
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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val even : z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | XO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | XO _ -> true
               | _ -> false)

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

module Coq_Z =
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

  (** val leb : z -> z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : z -> z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : z -> z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> true
             | _ -> false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> false)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q), r')
      else ((add (mul (Zpos (XO XH)) q) (Zpos XH)), (sub r' b))
    | XH -> if leb (Zpos (XO XH)) b then (Z0, (Zpos XH)) else ((Zpos XH), Z0)

  (** val div_eucl : z -> z -> z * z **)

  let div_eucl a b =
    match a with
    | Z0 -> (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q), Z0)
          | _ -> ((opp (add q (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q, r) = pos_div_eucl a' (Zpos b') in (q, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

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

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val eqb0 : Uint63.t -> Uint63.t -> bool **)

let eqb0 = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val size : nat **)

let size =
  S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val is_zero : Uint63.t -> bool **)

let is_zero i =
  eqb0 i (Uint63.of_int (0))

(** val is_even : Uint63.t -> bool **)

let is_even i =
  is_zero (land0 i (Uint63.of_int (1)))

(** val to_Z_rec : nat -> Uint63.t -> z **)

let rec to_Z_rec n i =
  match n with
  | O -> Z0
  | S n0 ->
    if is_even i
    then Z.double (to_Z_rec n0 (lsr0 i (Uint63.of_int (1))))
    else Z.succ_double (to_Z_rec n0 (lsr0 i (Uint63.of_int (1))))

(** val to_Z : Uint63.t -> z **)

let to_Z =
  to_Z_rec size

(** val of_pos_rec : nat -> positive -> Uint63.t **)

let rec of_pos_rec n p =
  match n with
  | O -> (Uint63.of_int (0))
  | S n0 ->
    (match p with
     | XI p0 ->
       lor0 (lsl0 (of_pos_rec n0 p0) (Uint63.of_int (1))) (Uint63.of_int (1))
     | XO p0 -> lsl0 (of_pos_rec n0 p0) (Uint63.of_int (1))
     | XH -> (Uint63.of_int (1)))

(** val of_pos : positive -> Uint63.t **)

let of_pos =
  of_pos_rec size

(** val of_Z : z -> Uint63.t **)

let of_Z = function
| Z0 -> (Uint63.of_int (0))
| Zpos p -> of_pos p
| Zneg p -> sub0 (Uint63.of_int (0)) (of_pos p)

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val abs0 : Float64.t -> Float64.t **)

let abs0 = Float64.abs

(** val opp0 : Float64.t -> Float64.t **)

let opp0 = Float64.opp

(** val eqb1 : Float64.t -> Float64.t -> bool **)

let eqb1 = Float64.eq

(** val ltb1 : Float64.t -> Float64.t -> bool **)

let ltb1 = Float64.lt

(** val leb0 : Float64.t -> Float64.t -> bool **)

let leb0 = Float64.le

(** val mul1 : Float64.t -> Float64.t -> Float64.t **)

let mul1 = Float64.mul

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

(** val ldshiftexp : Float64.t -> Uint63.t -> Float64.t **)

let ldshiftexp = Float64.ldshiftexp

(** val infinity : Float64.t **)

let infinity =
  (Float64.of_float (infinity))

(** val neg_infinity : Float64.t **)

let neg_infinity =
  (Float64.of_float (neg_infinity))

(** val nan : Float64.t **)

let nan =
  (Float64.of_float (nan))

(** val one : Float64.t **)

let one =
  (Float64.of_float (0x1p+0))

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

(** val neg_zero : Float64.t **)

let neg_zero =
  (Float64.of_float (-0x0p+0))

(** val is_nan : Float64.t -> bool **)

let is_nan f =
  negb (eqb1 f f)

(** val is_zero0 : Float64.t -> bool **)

let is_zero0 f =
  eqb1 f zero

(** val is_infinity : Float64.t -> bool **)

let is_infinity f =
  eqb1 (abs0 f) infinity

(** val is_finite : Float64.t -> bool **)

let is_finite x =
  negb ((||) (is_nan x) (is_infinity x))

(** val get_sign : Float64.t -> bool **)

let get_sign f =
  let f0 = if is_zero0 f then div0 one f else f in ltb1 f0 zero

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * z

(** val emin : z -> z -> z **)

let emin prec0 emax0 =
  Z.sub (Z.sub (Zpos (XI XH)) emax0) prec0

(** val fexp : z -> z -> z -> z **)

let fexp prec0 emax0 e =
  Z.max (Z.sub e prec0) (emin prec0 emax0)

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| XI p -> Pos.succ (digits2_pos p)
| XO p -> Pos.succ (digits2_pos p)
| XH -> XH

(** val zdigits2 : z -> z **)

let zdigits2 n = match n with
| Z0 -> n
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  match n with
  | XI n' -> iter_pos f n' (iter_pos f n' (f x))
  | XO n' -> iter_pos f n' (iter_pos f n' x)
  | XH -> f x

type location =
| Loc_Exact
| Loc_Inexact of comparison

type shr_record = { shr_m : z; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | XI p -> { shr_m = (Zpos p); shr_r = true; shr_s = s0 }
      | XO p -> { shr_m = (Zpos p); shr_r = false; shr_s = s0 }
      | XH -> { shr_m = Z0; shr_r = true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | XI p -> { shr_m = (Zneg p); shr_r = true; shr_s = s0 }
      | XO p -> { shr_m = (Zneg p); shr_r = false; shr_s = s0 }
      | XH -> { shr_m = Z0; shr_r = true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Loc_Inexact Gt else Loc_Inexact Eq
  else if shr_s0 then Loc_Inexact Lt else Loc_Exact

(** val shr_record_of_loc : z -> location -> shr_record **)

let shr_record_of_loc m = function
| Loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> z -> z -> shr_record * z **)

let shr mrs e n = match n with
| Zpos p -> ((iter_pos shr_1 p mrs), (Z.add e n))
| _ -> (mrs, e)

(** val shr_fexp : z -> z -> z -> z -> location -> shr_record * z **)

let shr_fexp prec0 emax0 m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec0 emax0 (Z.add (zdigits2 m) e)) e)

(** val round_nearest_even : z -> location -> z **)

let round_nearest_even mx = function
| Loc_Exact -> mx
| Loc_Inexact c ->
  (match c with
   | Eq -> if Z.even mx then mx else Z.add mx (Zpos XH)
   | Lt -> mx
   | Gt -> Z.add mx (Zpos XH))

(** val binary_round_aux :
    z -> z -> bool -> z -> z -> location -> spec_float **)

let binary_round_aux prec0 emax0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec0 emax0 mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec0 emax0
      (round_nearest_even mrs'.shr_m (loc_of_shr_record mrs')) e' Loc_Exact
  in
  (match mrs''.shr_m with
   | Z0 -> S754_zero sx
   | Zpos m ->
     if Z.leb e'' (Z.sub emax0 prec0)
     then S754_finite (sx, m, e'')
     else S754_infinity sx
   | Zneg _ -> S754_nan)

(** val new_location_even : z -> z -> location **)

let new_location_even nb_steps k =
  if Z.eqb k Z0
  then Loc_Exact
  else Loc_Inexact (Z.compare (Z.mul (Zpos (XO XH)) k) nb_steps)

(** val new_location_odd : z -> z -> location **)

let new_location_odd nb_steps k =
  if Z.eqb k Z0
  then Loc_Exact
  else Loc_Inexact
         (match Z.compare (Z.add (Z.mul (Zpos (XO XH)) k) (Zpos XH)) nb_steps with
          | Eq -> Lt
          | x -> x)

(** val new_location : z -> z -> location **)

let new_location nb_steps =
  if Z.even nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps

(** val sFdiv_core_binary :
    z -> z -> z -> z -> z -> z -> (z * z) * location **)

let sFdiv_core_binary prec0 emax0 m1 e1 m2 e2 =
  let d2 = zdigits2 m1 in
  let d3 = zdigits2 m2 in
  let e' =
    Z.min (fexp prec0 emax0 (Z.sub (Z.add d2 e1) (Z.add d3 e2))) (Z.sub e1 e2)
  in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' = match s with
           | Z0 -> m1
           | Zpos _ -> Z.shiftl m1 s
           | Zneg _ -> Z0 in
  let (q, r) = Z.div_eucl m' m2 in ((q, e'), (new_location m2 r))

(** val prec : z **)

let prec =
  Zpos (XI (XO (XI (XO (XI XH)))))

(** val emax : z **)

let emax =
  Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))

(** val shift : z **)

let shift =
  Zpos (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO (XO XH)))))))))))

type uint = Uint63.t

type 'v outcome =
| Unique of 'v
| Multiple
| Inconsistent

(** val zgcd_loop : z -> z -> z **)

let rec zgcd_loop a b =
  if Coq_Z.ltb Z0 b then zgcd_loop b (Coq_Z.modulo a b) else a

(** val zgcd : z -> z -> z **)

let zgcd a b =
  zgcd_loop (Coq_Z.abs a) (Coq_Z.abs b)

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

(** val i2z : Uint63.t -> z **)

let i2z =
  to_Z

(** val z2i : z -> Uint63.t **)

let z2i =
  of_Z

(** val ldexp' : Float64.t -> z -> Float64.t **)

let ldexp' f e =
  let e' =
    Coq_Z.max (Coq_Z.min e (Coq_Z.sub emax (emin prec emax)))
      (Coq_Z.sub (Coq_Z.sub (emin prec emax) emax) (Zpos XH))
  in
  ldshiftexp f (z2i (Coq_Z.add e' shift))

(** val sF2Prim' : spec_float -> Float64.t **)

let sF2Prim' = function
| S754_zero s -> if s then neg_zero else zero
| S754_infinity s -> if s then neg_infinity else infinity
| S754_nan -> nan
| S754_finite (s, m, e) ->
  let pm = of_uint63 (z2i (Zpos m)) in
  let f = ldexp' pm e in if s then opp0 f else f

(** val dec : Float64.t -> z * z **)

let dec f =
  if is_nan f
  then (Z0, Z0)
  else if is_zero0 f
       then (Z0, Z0)
       else if is_infinity f
            then (Z0, Z0)
            else let (r, e) = frshiftexp f in
                 let m = to_Z (normfr_mantissa r) in
                 ((if get_sign f then Coq_Z.opp m else m),
                 (Coq_Z.sub (Coq_Z.sub (to_Z e) shift) prec))

(** val scale : Float64.t -> z -> z **)

let scale f e =
  Coq_Z.shiftl (fst (dec f)) (Coq_Z.sub (snd (dec f)) e)

(** val qr : bool -> positive -> bool -> positive -> Float64.t **)

let qr sx mx sy my =
  let (p, lz) = sFdiv_core_binary prec emax (Zpos mx) Z0 (Zpos my) Z0 in
  let (mz, ez) = p in
  (match binary_round_aux prec emax (xorb sx sy) mz ez lz with
   | S754_finite (s, m, e) -> sF2Prim' (S754_finite (s, m, e))
   | _ -> zero)

(** val qround : z -> z -> Float64.t **)

let qround num den =
  match num with
  | Z0 -> zero
  | Zpos mx ->
    (match den with
     | Z0 -> zero
     | Zpos my -> qr false mx false my
     | Zneg my -> qr false mx true my)
  | Zneg mx ->
    (match den with
     | Z0 -> zero
     | Zpos my -> qr true mx false my
     | Zneg my -> qr true mx true my)

(** val row_exp : Uint63.t -> Float64.t Marray.t -> Float64.t -> z **)

let row_exp n row bi =
  loop n (fun _ _ -> true) (fun j e -> Coq_Z.min e (snd (dec (get row j))))
    (Uint63.of_int (0)) (Coq_Z.min Z0 (snd (dec bi)))

(** val fill_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t -> z -> z Marray.t
    -> z Marray.t **)

let fill_row n w i row e t =
  loop n (fun _ _ -> true) (fun j t0 ->
    set t0 (add0 (mul0 i w) j) (scale (get row j) e)) (Uint63.of_int (0)) t

(** val build_step :
    Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t
    -> Uint63.t -> z Marray.t -> z Marray.t **)

let build_step a b n w i t =
  let row = get a i in
  let bi = get b i in
  let e = row_exp n row bi in
  let t0 = fill_row n w i row e t in set t0 (add0 (mul0 i w) n) (scale bi e)

(** val build :
    Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t
    -> z Marray.t **)

let build a b n w =
  loop n (fun _ _ -> true) (build_step a b n w) (Uint63.of_int (0))
    (make (mul0 n w) Z0)

(** val find_piv :
    z Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let find_piv t n w c r =
  loop n (fun _ _ -> true) (fun i s ->
    if eqb0 s n
    then if Coq_Z.eqb (get t (add0 (mul0 i w) c)) Z0 then s else i
    else s) r n

(** val swap_rows :
    z Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> z Marray.t **)

let swap_rows t w q r =
  loop w (fun _ _ -> true) (fun j t0 ->
    let x = get t0 (add0 (mul0 r w) j) in
    let y = get t0 (add0 (mul0 q w) j) in
    set (set t0 (add0 (mul0 r w) j) y) (add0 (mul0 q w) j) x)
    (Uint63.of_int (0)) t

(** val upd_row :
    z Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> z -> z -> z Marray.t **)

let upd_row t w i r a b =
  loop w (fun _ _ -> true) (fun j t0 ->
    set t0 (add0 (mul0 i w) j)
      (Coq_Z.sub (Coq_Z.mul a (get t0 (add0 (mul0 i w) j)))
        (Coq_Z.mul b (get t0 (add0 (mul0 r w) j)))))
    (Uint63.of_int (0)) t

(** val row_gcd : z Marray.t -> Uint63.t -> Uint63.t -> z **)

let row_gcd t w i =
  loop w (fun _ _ -> true) (fun j g -> zgcd g (get t (add0 (mul0 i w) j)))
    (Uint63.of_int (0)) Z0

(** val div_row : z Marray.t -> Uint63.t -> Uint63.t -> z -> z Marray.t **)

let div_row t w i g =
  loop w (fun _ _ -> true) (fun j t0 ->
    set t0 (add0 (mul0 i w) j) (Coq_Z.div (get t0 (add0 (mul0 i w) j)) g))
    (Uint63.of_int (0)) t

(** val elim_row :
    Uint63.t -> Uint63.t -> Uint63.t -> z -> Uint63.t -> z Marray.t -> z
    Marray.t **)

let elim_row w c r a i t =
  if eqb0 i r
  then t
  else let b = get t (add0 (mul0 i w) c) in
       if Coq_Z.eqb b Z0
       then t
       else let t0 = upd_row t w i r a b in
            let g = row_gcd t0 w i in
            if Coq_Z.ltb (Zpos XH) g then div_row t0 w i g else t0

(** val col_step :
    Uint63.t -> Uint63.t -> Uint63.t -> (z Marray.t * Uint63.t) -> z
    Marray.t * Uint63.t **)

let col_step n w c = function
| (t, r) ->
  let q = find_piv t n w c r in
  if eqb0 q n
  then (t, r)
  else let t0 = swap_rows t w q r in
       let a = get t0 (add0 (mul0 r w) c) in
       ((loop n (fun _ _ -> true) (elim_row w c r a) (Uint63.of_int (0)) t0),
       (add0 r (Uint63.of_int (1))))

(** val eliminate :
    Uint63.t -> Uint63.t -> z Marray.t -> z Marray.t * Uint63.t **)

let eliminate n w t =
  loop n (fun _ _ -> true) (col_step n w) (Uint63.of_int (0)) (t,
    (Uint63.of_int (0)))

(** val inconsistent :
    z Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let inconsistent t n w r =
  loop n (fun _ _ -> true) (fun i fl ->
    (||) fl (negb (Coq_Z.eqb (get t (add0 (mul0 i w) n)) Z0))) r false

(** val output : z Marray.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t **)

let output t n w =
  loop n (fun _ _ -> true) (fun i out ->
    set out i (qround (get t (add0 (mul0 i w) n)) (get t (add0 (mul0 i w) i))))
    (Uint63.of_int (0)) (make n zero)

(** val solve_exact :
    uint -> Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t outcome **)

let solve_exact n a b =
  let w = add0 n (Uint63.of_int (1)) in
  let t = build a b n w in
  let (t0, r) = eliminate n w t in
  if inconsistent t0 n w r
  then Inconsistent
  else if ltb0 r n then Multiple else Unique (output t0 n w)

(** val fdot :
    Float64.t Marray.t -> Uint63.t -> Float64.t Marray.t -> Uint63.t ->
    Uint63.t -> Float64.t **)

let fdot x ox y oy len =
  loop len (fun _ _ -> true) (fun k s ->
    add1 s (mul1 (get x (add0 ox k)) (get y (add0 oy k))))
    (Uint63.of_int (0)) zero

type dy = z * z

(** val dadd : dy -> dy -> dy **)

let dadd x y =
  let (m1, e1) = x in
  let (m2, e2) = y in
  if Coq_Z.leb e1 e2
  then ((Coq_Z.add m1 (Coq_Z.shiftl m2 (Coq_Z.sub e2 e1))), e1)
  else ((Coq_Z.add (Coq_Z.shiftl m1 (Coq_Z.sub e1 e2)) m2), e2)

(** val dmul : dy -> dy -> dy **)

let dmul x y =
  ((Coq_Z.mul (fst x) (fst y)), (Coq_Z.add (snd x) (snd y)))

(** val dabs : dy -> dy **)

let dabs x =
  ((Coq_Z.abs (fst x)), (snd x))

(** val dneg : dy -> dy **)

let dneg x =
  ((Coq_Z.opp (fst x)), (snd x))

(** val dleb : dy -> dy -> bool **)

let dleb x y =
  Coq_Z.leb Z0 (fst (dadd y (dneg x)))

(** val dltb : dy -> dy -> bool **)

let dltb x y =
  Coq_Z.ltb Z0 (fst (dadd y (dneg x)))

(** val dzero : dy -> bool **)

let dzero x =
  Coq_Z.eqb (fst x) Z0

(** val dmax : dy -> dy -> dy **)

let dmax x y =
  if dleb x y then y else x

(** val d0 : dy **)

let d0 =
  (Z0, Z0)

(** val dint : z -> dy **)

let dint z0 =
  (z0, Z0)

(** val init_M :
    Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Uint63.t -> Uint63.t
    -> Float64.t Marray.t **)

let init_M xa xb n w =
  loop n (fun _ _ -> true) (fun i m ->
    let row = get xa i in
    let m0 =
      loop n (fun _ _ -> true) (fun j m0 ->
        set m0 (add0 (mul0 i w) j) (get row j)) (Uint63.of_int (0)) m
    in
    set m0 (add0 (mul0 i w) n) (get xb i)) (Uint63.of_int (0))
    (make (mul0 n w) zero)

(** val init_Q : Uint63.t -> Float64.t Marray.t **)

let init_Q n =
  loop n (fun _ _ -> true) (fun i q -> set q (add0 (mul0 i n) i) one)
    (Uint63.of_int (0)) (make (mul0 n n) zero)

(** val thr_scale : Float64.t **)

let thr_scale =
  (Float64.of_float (0x1p-40))

(** val col_thr :
    Float64.t Marray.t Marray.t -> Uint63.t -> Float64.t Marray.t **)

let col_thr xa n =
  loop n (fun _ _ -> true) (fun j t ->
    let m =
      loop n (fun _ _ -> true) (fun i m ->
        let v = abs0 (get (get xa i) j) in if ltb1 m v then v else m)
        (Uint63.of_int (0)) zero
    in
    set t j (mul1 m thr_scale)) (Uint63.of_int (0)) (make n zero)

(** val swap_f :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t
    Marray.t **)

let swap_f t w p r =
  loop w (fun _ _ -> true) (fun j t0 ->
    let x = get t0 (add0 (mul0 r w) j) in
    let y = get t0 (add0 (mul0 p w) j) in
    set (set t0 (add0 (mul0 r w) j) y) (add0 (mul0 p w) j) x)
    (Uint63.of_int (0)) t

(** val axpy_row :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Float64.t -> Float64.t Marray.t **)

let axpy_row t w i r lo f =
  loop w (fun _ _ -> true) (fun j t0 ->
    set t0 (add0 (mul0 i w) j)
      (sub1 (get t0 (add0 (mul0 i w) j))
        (mul1 f (get t0 (add0 (mul0 r w) j)))))
    lo t

(** val scale_row :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Float64.t -> Float64.t
    Marray.t **)

let scale_row t w i piv =
  loop w (fun _ _ -> true) (fun j t0 ->
    set t0 (add0 (mul0 i w) j) (div0 (get t0 (add0 (mul0 i w) j)) piv))
    (Uint63.of_int (0)) t

(** val tab : Uint63.t -> 'a1 -> (Uint63.t -> 'a1) -> 'a1 Marray.t **)

let tab n d f =
  loop n (fun _ _ -> true) (fun i t -> set t i (f i)) (Uint63.of_int (0))
    (make n d)

type fstate = { fs_M : Float64.t Marray.t; fs_Q : Float64.t Marray.t;
                fs_r : Uint63.t; fs_pc : Uint63.t Marray.t;
                fs_perm : Uint63.t Marray.t }

(** val fwd_col :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Uint63.t -> fstate -> fstate **)

let fwd_col n w thr c st =
  let r = st.fs_r in
  if ltb0 r n
  then let m = st.fs_M in
       let (p, mx) =
         loop n (fun _ _ -> true) (fun i pm ->
           let v = abs0 (get m (add0 (mul0 i w) c)) in
           if ltb1 (snd pm) v then (i, v) else pm) r (r, zero)
       in
       if leb0 mx (get thr c)
       then st
       else let m0 = swap_f m w p r in
            let q = swap_f st.fs_Q n p r in
            let piv = get m0 (add0 (mul0 r w) c) in
            let (m1, q0) =
              loop n (fun _ _ -> true) (fun i mq ->
                let (m1, q0) = mq in
                let f = div0 (get m1 (add0 (mul0 i w) c)) piv in
                let m2 = axpy_row m1 w i r (add0 c (Uint63.of_int (1))) f in
                ((set m2 (add0 (mul0 i w) c) zero),
                (axpy_row q0 n i r (Uint63.of_int (0)) f)))
                (add0 r (Uint63.of_int (1))) (m0, q)
            in
            let pm = st.fs_perm in
            let x = get pm p in
            let y = get pm r in
            { fs_M = m1; fs_Q = q0; fs_r = (add0 r (Uint63.of_int (1)));
            fs_pc = (set st.fs_pc r c); fs_perm = (set (set pm p y) r x) }
  else st

(** val forward :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> fstate **)

let forward n w thr m q =
  loop n (fun _ _ -> true) (fwd_col n w thr) (Uint63.of_int (0)) { fs_M = m;
    fs_Q = q; fs_r = (Uint63.of_int (0)); fs_pc =
    (make n (Uint63.of_int (0))); fs_perm =
    (tab n (Uint63.of_int (0)) (fun i -> i)) }

(** val backsub :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t * Float64.t Marray.t **)

let backsub n w m q =
  loop n (fun _ _ -> true) (fun t mq ->
    let (m0, q0) = mq in
    let i = sub0 (sub0 n (Uint63.of_int (1))) t in
    let piv = get m0 (add0 (mul0 i w) i) in
    let xi = div0 (get m0 (add0 (mul0 i w) n)) piv in
    let m1 = set m0 (add0 (mul0 i w) n) xi in
    let q1 = scale_row q0 n i piv in
    loop i (fun _ _ -> true) (fun i' mq0 ->
      let (m2, q2) = mq0 in
      let f = get m2 (add0 (mul0 i' w) i) in
      ((set m2 (add0 (mul0 i' w) n)
         (sub1 (get m2 (add0 (mul0 i' w) n)) (mul1 f xi))),
      (axpy_row q2 n i' i (Uint63.of_int (0)) f))) (Uint63.of_int (0)) (m1,
      q1))
    (Uint63.of_int (0)) (m, q)

(** val get_col :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t
    Marray.t **)

let get_col m n w c =
  loop n (fun _ _ -> true) (fun i x -> set x i (get m (add0 (mul0 i w) c)))
    (Uint63.of_int (0)) (make n zero)

(** val get_row :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t **)

let get_row q n i =
  loop n (fun _ _ -> true) (fun k x -> set x k (get q (add0 (mul0 i n) k)))
    (Uint63.of_int (0)) (make n zero)

(** val free_col : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let free_col pc n r =
  let isp =
    loop r (fun _ _ -> true) (fun t isp -> set isp (get pc t) true)
      (Uint63.of_int (0)) (make n false)
  in
  loop n (fun _ _ -> true) (fun c f ->
    if (&&) (eqb0 f n) (negb (get isp c)) then c else f) (Uint63.of_int (0)) n

(** val free_cols :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let free_cols pc n r =
  let isp =
    loop r (fun _ _ -> true) (fun t isp -> set isp (get pc t) true)
      (Uint63.of_int (0)) (make n false)
  in
  fst
    (loop n (fun _ _ -> true) (fun c st ->
      let (fc, cnt) = st in
      if get isp c
      then (fc, cnt)
      else ((set fc cnt c), (add0 cnt (Uint63.of_int (1)))))
      (Uint63.of_int (0)) ((make n (Uint63.of_int (0))), (Uint63.of_int (0))))

(** val echelon_solve :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool -> Float64.t Marray.t -> Float64.t Marray.t **)

let echelon_solve m pc n w r homog x =
  loop r (fun _ _ -> true) (fun s x0 ->
    let t = sub0 (sub0 r (Uint63.of_int (1))) s in
    let c = get pc t in
    let s0 = if homog then zero else get m (add0 (mul0 t w) n) in
    let acc =
      loop n (fun _ _ -> true) (fun j acc ->
        sub1 acc (mul1 (get m (add0 (mul0 t w) j)) (get x0 j)))
        (add0 c (Uint63.of_int (1))) s0
    in
    set x0 c (div0 acc (get m (add0 (mul0 t w) c)))) (Uint63.of_int (0)) x

(** val rat1 : Float64.t -> z * z **)

let rat1 f =
  let (m, e) = dec f in
  if Coq_Z.leb Z0 e
  then ((Coq_Z.shiftl m e), (Zpos XH))
  else let den = Coq_Z.shiftl (Zpos XH) (Coq_Z.opp e) in
       let st =
         loop (Uint63.of_int (64)) (fun _ st -> negb (snd st)) (fun _ st ->
           let (y, k0) = fst st in
           let (y0, k1) = y in
           let (y1, h0) = y0 in
           let (y2, h1) = y1 in
           let (an, ad) = y2 in
           let q = Coq_Z.div an ad in
           let h = Coq_Z.add (Coq_Z.mul q h1) h0 in
           let k = Coq_Z.add (Coq_Z.mul q k1) k0 in
           if Coq_Z.ltb (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
                (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
                (XO (XO (XO XH))))))))))))))))))))))))))))))) k
           then ((fst st), true)
           else let rem = Coq_Z.sub an (Coq_Z.mul q ad) in
                let close =
                  Coq_Z.leb
                    (Coq_Z.shiftl
                      (Coq_Z.abs
                        (Coq_Z.sub (Coq_Z.mul m k) (Coq_Z.mul h den)))
                      (Zpos (XO (XO (XO (XI (XO XH)))))))
                    (Coq_Z.mul (Coq_Z.abs m) k)
                in
                ((((((ad, rem), h), h1), k), k1),
                ((||) (Coq_Z.eqb rem Z0) close)))
           (Uint63.of_int (0)) ((((((m, den), (Zpos XH)), Z0), Z0), (Zpos
           XH)), false)
       in
       let (p, _) = fst st in
       let (p0, k1) = p in
       let (p1, _) = p0 in
       let (_, h1) = p1 in
       if Coq_Z.ltb Z0 k1 then (h1, k1) else (Z0, (Zpos XH))

(** val ratvec : Float64.t Marray.t -> Uint63.t -> z Marray.t * z **)

let ratvec x n =
  let (p, l) =
    loop n (fun _ _ -> true) (fun j st ->
      let (y, l) = st in
      let (h, k) = y in
      let (h0, k0) = rat1 (get x j) in
      (((set h j h0), (set k j k0)), (Coq_Z.mul (Coq_Z.div l (zgcd l k0)) k0)))
      (Uint63.of_int (0)) (((make n Z0), (make n (Zpos XH))), (Zpos XH))
  in
  let (h, k) = p in
  ((loop n (fun _ _ -> true) (fun j p0 ->
     set p0 j (Coq_Z.mul (get h j) (Coq_Z.div l (get k j))))
     (Uint63.of_int (0)) (make n Z0)),
  l)

(** val dsumf : Uint63.t -> (Uint63.t -> dy) -> dy **)

let dsumf len f =
  loop len (fun _ _ -> true) (fun k acc -> dadd acc (f k))
    (Uint63.of_int (0)) d0

(** val allf : Uint63.t -> (Uint63.t -> bool) -> bool **)

let allf len p =
  loop len (fun _ _ -> true) (fun k b -> (&&) b (p k)) (Uint63.of_int (0))
    true

(** val dsumb :
    Uint63.t -> (Uint63.t -> Float64.t) -> (Uint63.t -> Float64.t -> dy) ->
    dy * bool **)

let dsumb len g f =
  loop len (fun _ _ -> true) (fun k st ->
    let d = g k in ((dadd (fst st) (f k d)), ((&&) (snd st) (is_finite d))))
    (Uint63.of_int (0)) (d0, true)

(** val maxb : Uint63.t -> (Uint63.t -> dy * bool) -> dy * bool **)

let maxb len h =
  loop len (fun _ _ -> true) (fun i st ->
    let r = h i in ((dmax (fst st) (fst r)), ((&&) (snd st) (snd r))))
    (Uint63.of_int (0)) (d0, true)

(** val dsub : dy -> dy -> dy **)

let dsub x y =
  dadd x (dneg y)

(** val d1 : dy **)

let d1 =
  ((Zpos XH), Z0)

(** val transpose :
    Float64.t Marray.t Marray.t -> Uint63.t -> Float64.t Marray.t **)

let transpose xa n =
  loop n (fun _ _ -> true) (fun i t ->
    let row = get xa i in
    loop n (fun _ _ -> true) (fun j t0 ->
      set t0 (add0 (mul0 j n) i) (get row j)) (Uint63.of_int (0)) t)
    (Uint63.of_int (0)) (make (mul0 n n) zero)

(** val rowabs : Float64.t Marray.t Marray.t -> Uint63.t -> dy Marray.t **)

let rowabs xa n =
  loop n (fun _ _ -> true) (fun k s ->
    let row = get xa k in set s k (dsumf n (fun j -> dabs (dec (get row j)))))
    (Uint63.of_int (0)) (make n d0)

(** val erow :
    Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t -> dy Marray.t -> dy
    -> dy -> Uint63.t -> dy * bool **)

let erow n q aT s lamd mud2 i =
  let e =
    dsumb n (fun j -> fdot q (mul0 i n) aT (mul0 j n) n) (fun j d ->
      dabs (dsub (dint (if eqb0 i j then Zpos XH else Z0)) (dec d)))
  in
  let rr =
    dsumf n (fun k -> dmul (dabs (dec (get q (add0 (mul0 i n) k)))) (get s k))
  in
  ((dadd (dadd (fst e) (dmul lamd rr)) mud2), (snd e))

(** val rowR : Uint63.t -> Float64.t Marray.t -> Uint63.t -> dy * bool **)

let rowR n q i =
  ((dsumf n (fun k -> dabs (dec (get q (add0 (mul0 i n) k))))), true)

(** val resid :
    Uint63.t -> Float64.t Marray.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> dy -> dy -> Uint63.t -> dy * bool **)

let resid n xa xb xt lamd mud1 i =
  let row = get xa i in
  let d = fdot row (Uint63.of_int (0)) xt (Uint63.of_int (0)) n in
  ((dadd
     (dadd (dabs (dsub (dec (get xb i)) (dec d)))
       (dmul lamd
         (dsumf n (fun j -> dabs (dmul (dec (get row j)) (dec (get xt j)))))))
     mud1),
  (is_finite d))

(** val certify :
    Uint63.t -> Float64.t Marray.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t -> bool **)

let certify n xa xb aT q xt =
  let nz = i2z n in
  let lamd = ((Coq_Z.mul (Zpos (XI XH)) nz), (Zneg (XI (XO (XI (XO (XI
    XH)))))))
  in
  let mud1 = ((Coq_Z.mul (Zpos (XI XH)) nz), (Zneg (XI (XI (XO (XO (XI (XI
    (XO (XO (XO (XO XH))))))))))))
  in
  let mud2 = ((Coq_Z.mul (Coq_Z.mul (Zpos (XI XH)) nz) nz), (Zneg (XI (XI (XO
    (XO (XI (XI (XO (XO (XO (XO XH))))))))))))
  in
  let s = rowabs xa n in
  let (eps, ok1) = maxb n (erow n q aT s lamd mud2) in
  let (rho, _) = maxb n (rowR n q) in
  let (sig0, ok2) = maxb n (resid n xa xb xt lamd mud1) in
  (&&) ((&&) ((&&) ok1 ok2) (eqb0 (length xt) n))
    ((&&) (dltb eps d1)
      (dleb
        (dadd
          (dmul ((Zpos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))), Z0)
            (dmul rho sig0))
          eps)
        d1))

(** val zdot :
    Float64.t Marray.t -> Uint63.t -> z Marray.t -> Uint63.t -> dy **)

let zdot x o y len =
  dsumf len (fun k -> dmul (dec (get x (add0 o k))) (dint (get y k)))

(** val chk_incons :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> z Marray.t -> bool **)

let chk_incons aT xb n y =
  (&&) (allf n (fun j -> dzero (zdot aT (mul0 j n) y n)))
    (negb (dzero (zdot xb (Uint63.of_int (0)) y n)))

(** val chk_mult :
    Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Uint63.t -> z
    Marray.t -> z -> z Marray.t -> bool **)

let chk_mult xa xb n p q v =
  (&&)
    ((&&) (negb (Coq_Z.eqb q Z0))
      (negb (allf n (fun j -> Coq_Z.eqb (get v j) Z0))))
    (allf n (fun i ->
      let row = get xa i in
      (&&)
        (dzero
          (dsub (zdot row (Uint63.of_int (0)) p n)
            (dmul (dint q) (dec (get xb i)))))
        (dzero (zdot row (Uint63.of_int (0)) v n))))

(** val yv :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> z Marray.t **)

let yv q n r t =
  fst (ratvec (get_row q n (add0 r t)) n)

(** val mark_D :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
    Marray.t * Uint63.t Marray.t **)

let mark_D perm n r k =
  loop k (fun _ _ -> true) (fun t st ->
    let d = get perm (add0 r t) in ((set (fst st) d true), (set (snd st) d t)))
    (Uint63.of_int (0)) ((make n false), (make n (Uint63.of_int (0))))

(** val mark_C :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let mark_C fc n k =
  loop k (fun _ _ -> true) (fun t c -> set c (get fc t) true)
    (Uint63.of_int (0)) (make n false)

(** val chk_red :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> z Marray.t ->
    Uint63.t -> bool Marray.t -> bool **)

let chk_red aT xb n y d df =
  (&&)
    ((&&) (allf n (fun j -> dzero (zdot aT (mul0 j n) y n)))
      (dzero (zdot xb (Uint63.of_int (0)) y n)))
    ((&&) (negb (Coq_Z.eqb (get y d) Z0))
      (allf n (fun i ->
        (||) (negb (get df i)) ((||) (eqb0 i d) (Coq_Z.eqb (get y i) Z0)))))

(** val scan_null :
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool * bool **)

let scan_null aT xb q perm fc df n r k =
  loop k (fun _ _ -> true) (fun t s ->
    let y = yv q n r t in
    let d = get perm (add0 r t) in
    (((||) (fst s) (chk_incons aT xb n y)),
    ((&&) (snd s)
      ((&&) ((&&) (ltb0 d n) (ltb0 (get fc t) n)) (chk_red aT xb n y d df)))))
    (Uint63.of_int (0)) (false, (ltb0 r n))

(** val bentry :
    Float64.t Marray.t Marray.t -> bool Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> bool Marray.t -> Uint63.t -> Uint63.t -> Float64.t **)

let bentry xa df tix fc cf i j =
  if get df i
  then if eqb0 j (get fc (get tix i)) then one else zero
  else if get cf j then zero else get (get xa i) j

(** val padB :
    Float64.t Marray.t Marray.t -> Uint63.t -> bool Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> bool Marray.t -> Float64.t Marray.t
    Marray.t **)

let padB xa n df tix fc cf =
  tab n (make (Uint63.of_int (0)) zero) (fun i ->
    tab n zero (fun j -> bentry xa df tix fc cf i j))

(** val certify_inj :
    Uint63.t -> Float64.t Marray.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> bool **)

let certify_inj n xa aT q =
  let nz = i2z n in
  let lamd = ((Coq_Z.mul (Zpos (XI XH)) nz), (Zneg (XI (XO (XI (XO (XI
    XH)))))))
  in
  let mud2 = ((Coq_Z.mul (Coq_Z.mul (Zpos (XI XH)) nz) nz), (Zneg (XI (XI (XO
    (XO (XI (XI (XO (XO (XO (XO XH))))))))))))
  in
  let s = rowabs xa n in
  let (eps, ok1) = maxb n (erow n q aT s lamd mud2) in (&&) ok1 (dltb eps d1)

(** val padded_ok :
    Float64.t Marray.t Marray.t -> Uint63.t -> bool Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> bool Marray.t -> bool **)

let padded_ok xa n df tix fc cf =
  let b = padB xa n df tix fc cf in
  let w = add0 n (Uint63.of_int (1)) in
  let st = forward n w (col_thr b n) (init_M b (make n zero) n w) (init_Q n)
  in
  if eqb0 st.fs_r n
  then certify_inj n b (transpose b n) (snd (backsub n w st.fs_M st.fs_Q))
  else false

(** val solve :
    uint -> Float64.t Marray.t Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t outcome **)

let solve n xa xb =
  let w = add0 n (Uint63.of_int (1)) in
  let st = forward n w (col_thr xa n) (init_M xa xb n w) (init_Q n) in
  let aT = transpose xa n in
  if eqb0 st.fs_r n
  then let (m, q) = backsub n w st.fs_M st.fs_Q in
       let xt = get_col m n w n in
       if certify n xa xb aT q xt then Unique xt else solve_exact n xa xb
  else let m = st.fs_M in
       let r = st.fs_r in
       let k = if ltb0 r n then sub0 n r else (Uint63.of_int (0)) in
       let fc = free_cols st.fs_pc n r in
       let mD = mark_D st.fs_perm n r k in
       let df = fst mD in
       let tix = snd mD in
       let cf = mark_C fc n k in
       let sc = scan_null aT xb st.fs_Q st.fs_perm fc df n r k in
       if fst sc
       then Inconsistent
       else if if snd sc then padded_ok xa n df tix fc cf else false
            then Multiple
            else let f = free_col st.fs_pc n r in
                 let x0 = echelon_solve m st.fs_pc n w r false (make n zero)
                 in
                 let v =
                   echelon_solve m st.fs_pc n w r true
                     (set (make n zero) f one)
                 in
                 let (p, q) = ratvec x0 n in
                 if chk_mult xa xb n p q (fst (ratvec v n))
                 then Multiple
                 else solve_exact n xa xb
