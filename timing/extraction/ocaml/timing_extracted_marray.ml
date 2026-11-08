
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

  (** val shiftr : z -> z -> z **)

  let shiftr a n =
    shiftl a (opp n)
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

(** val abs : Float64.t -> Float64.t **)

let abs = Float64.abs

(** val opp0 : Float64.t -> Float64.t **)

let opp0 = Float64.opp

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val wloop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let rec wloop hi f i s =
  if bdec (ltb0 i hi)
  then wloop hi f (add0 i (Uint63.of_int (1))) (f i s)
  else s

(** val loop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

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

(** val iofp : positive -> Uint63.t **)

let rec iofp = function
| XI q -> add0 (mul0 (Uint63.of_int (2)) (iofp q)) (Uint63.of_int (1))
| XO q -> mul0 (Uint63.of_int (2)) (iofp q)
| XH -> (Uint63.of_int (1))

(** val iofz : z -> Uint63.t **)

let iofz = function
| Zpos p -> iofp p
| _ -> (Uint63.of_int (0))

(** val fex : Float64.t -> z * z **)

let fex f =
  let (z0, e) = frshiftexp f in
  let m = zofi (normfr_mantissa z0) in
  ((if ltb1 f (Float64.of_float (0x0p+0)) then Z.opp m else m),
  (Z.sub (zofi e) (Zpos (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO
    XH))))))))))))))

(** val pP : z **)

let pP =
  Zpos (XO (XO (XO (XO (XO (XI XH))))))

(** val oNE : z **)

let oNE =
  Z.shiftl (Zpos XH) pP

(** val fixv : Float64.t -> z **)

let fixv f =
  let d = fex f in Z.shiftl (fst d) (Z.add (snd d) pP)

(** val build : Uint63.t -> (Uint63.t -> z) -> z Marray.t **)

let build len f =
  loop len (fun k a -> set a k (f k)) (Uint63.of_int (0)) (make len Z0)

(** val dot :
    Uint63.t -> z Marray.t -> z Marray.t -> Uint63.t -> Uint63.t -> z **)

let dot s x y i j =
  loop s (fun k acc ->
    Z.add acc (Z.mul (get x (add0 (mul0 i s) k)) (get y (add0 (mul0 k s) j))))
    (Uint63.of_int (0)) Z0

(** val naive : Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t **)

let naive s x y =
  build (mul0 s s) (fun k -> dot s x y (div k s) (mod0 k s))

(** val quad :
    z Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> z Marray.t **)

let quad x s h di dj =
  build (mul0 h h) (fun k ->
    get x (add0 (mul0 (add0 di (div k h)) s) (add0 dj (mod0 k h))))

(** val madd : Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t **)

let madd h a b =
  build (mul0 h h) (fun k -> Z.add (get a k) (get b k))

(** val msub : Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t **)

let msub h a b =
  build (mul0 h h) (fun k -> Z.sub (get a k) (get b k))

(** val comb :
    Uint63.t -> Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t -> z
    Marray.t -> z Marray.t **)

let comb s h c11 c12 c21 c22 =
  build (mul0 s s) (fun k ->
    let i = div k s in
    let j = mod0 k s in
    if ltb0 i h
    then if ltb0 j h
         then get c11 (add0 (mul0 i h) j)
         else get c12 (add0 (mul0 i h) (sub0 j h))
    else if ltb0 j h
         then get c21 (add0 (mul0 (sub0 i h) h) j)
         else get c22 (add0 (mul0 (sub0 i h) h) (sub0 j h)))

(** val cut : Uint63.t **)

let cut =
  (Uint63.of_int (16))

(** val splitb : Uint63.t -> bool **)

let splitb s =
  (&&) (ltb0 cut s) (eqb (mod0 s (Uint63.of_int (2))) (Uint63.of_int (0)))

(** val strass : Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t **)

let rec strass s x y =
  if bdec (splitb s)
  then let h = div s (Uint63.of_int (2)) in
       let sr = fun a b -> strass h a b in
       let a11 = quad x s h (Uint63.of_int (0)) (Uint63.of_int (0)) in
       let a12 = quad x s h (Uint63.of_int (0)) h in
       let a21 = quad x s h h (Uint63.of_int (0)) in
       let a22 = quad x s h h h in
       let b11 = quad y s h (Uint63.of_int (0)) (Uint63.of_int (0)) in
       let b12 = quad y s h (Uint63.of_int (0)) h in
       let b21 = quad y s h h (Uint63.of_int (0)) in
       let b22 = quad y s h h h in
       let m1 = sr (madd h a11 a22) (madd h b11 b22) in
       let m2 = sr (madd h a21 a22) b11 in
       let m3 = sr a11 (msub h b12 b22) in
       let m4 = sr a22 (msub h b21 b11) in
       let m5 = sr (madd h a11 a12) b22 in
       let m6 = sr (msub h a21 a11) (madd h b11 b12) in
       let m7 = sr (msub h a12 a22) (madd h b21 b22) in
       comb s h (madd h (msub h (madd h m1 m4) m5) m7) (madd h m3 m5)
         (madd h m2 m4) (madd h (madd h (msub h m1 m2) m3) m6)
  else naive s x y

(** val mulr : Uint63.t -> z Marray.t -> z Marray.t -> z Marray.t **)

let mulr m x y =
  let c = strass m x y in build (mul0 m m) (fun k -> Z.shiftr (get c k) pP)

(** val ident : Uint63.t -> z Marray.t **)

let ident m =
  build (mul0 m m) (fun k -> if eqb (div k m) (mod0 k m) then oNE else Z0)

(** val link_step :
    Uint63.t -> uint Marray.t -> uint Marray.t -> Float64.t Marray.t ->
    Uint63.t -> z Marray.t -> z Marray.t **)

let link_step m xs xd xf l a =
  let s = get xs l in
  let d = get xd l in
  let f = fixv (get xf l) in
  let a1 = set a (add0 (mul0 d m) s) (Z.add (get a (add0 (mul0 d m) s)) f) in
  set a1 (add0 (mul0 s m) s) (Z.sub (get a1 (add0 (mul0 s m) s)) f)

(** val amat :
    Uint63.t -> Uint63.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> z Marray.t **)

let amat m l xs xd xf =
  loop l (link_step m xs xd xf) (Uint63.of_int (0)) (ident m)

(** val pw :
    Uint63.t -> Uint63.t -> z Marray.t option -> z Marray.t -> z Marray.t
    option **)

let rec pw m t r b =
  if bdec (eqb t (Uint63.of_int (0)))
  then r
  else let r' =
         if eqb (mod0 t (Uint63.of_int (2))) (Uint63.of_int (0))
         then r
         else Some (match r with
                    | Some x -> mulr m x b
                    | None -> b)
       in
       let t' = div t (Uint63.of_int (2)) in
       if eqb t' (Uint63.of_int (0)) then r' else pw m t' r' (mulr m b b)

(** val adj_step :
    Uint63.t -> uint Marray.t -> uint Marray.t -> Uint63.t -> bool Marray.t
    -> bool Marray.t **)

let adj_step n xs xd l a =
  let s = get xs l in
  let d = get xd l in
  if eqb s d
  then a
  else set (set a (add0 (mul0 s n) d) true) (add0 (mul0 d n) s) true

(** val faced_z : Uint63.t -> bool Marray.t -> z Marray.t -> Uint63.t -> z **)

let faced_z n adj v i =
  Z.add (get v i)
    (loop n (fun k acc ->
      if get adj (add0 (mul0 i n) k) then Z.add acc (get v k) else acc)
      (Uint63.of_int (0)) Z0)

(** val cv : z -> Float64.t **)

let cv z0 =
  div0
    (of_uint63
      (iofz
        (Z.shiftr z0
          (Z.sub (Z.mul (Zpos (XO XH)) pP) (Zpos (XO (XI (XI (XI XH)))))))))
    (of_uint63 (Uint63.of_int (1073741824)))

(** val conv : z -> Float64.t **)

let conv z0 =
  if Z.ltb z0 Z0 then opp0 (cv (Z.opp z0)) else cv z0

(** val timing_exact :
    uint -> Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> Float64.t **)

let timing_exact xt xu xs xd xf =
  let n = length xu in
  let l = length xs in
  let m =
    mul0 (div (add0 n (Uint63.of_int (7))) (Uint63.of_int (8)))
      (Uint63.of_int (8))
  in
  let a = amat m l xs xd xf in
  let rf = match pw m xt None a with
           | Some x -> x
           | None -> ident m in
  let uh = build m (fun s -> if ltb0 s n then fixv (get xu s) else Z0) in
  let v =
    build m (fun i ->
      loop m (fun k acc ->
        Z.add acc (Z.mul (get rf (add0 (mul0 i m) k)) (get uh k)))
        (Uint63.of_int (0)) Z0)
  in
  let adj =
    loop l (adj_step n xs xd) (Uint63.of_int (0)) (make (mul0 n n) false)
  in
  let best =
    loop n (fun i b -> Z.min b (faced_z n adj v i)) (Uint63.of_int (1))
      (faced_z n adj v (Uint63.of_int (0)))
  in
  conv best

(** val link_f :
    uint Marray.t -> uint Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t **)

let link_f xs xd xf v j w =
  let s = get xs j in
  let d = get xd j in
  if eqb s d
  then w
  else let a = mul1 (get xf j) (get v s) in
       let w1 = set w d (add1 (get w d) a) in set w1 s (sub1 (get w1 s) a)

(** val unit_f :
    Uint63.t -> uint Marray.t -> uint Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t **)

let unit_f l xs xd xf v =
  loop l (link_f xs xd xf v) (Uint63.of_int (0)) (copy v)

(** val cnt_step :
    uint Marray.t -> uint Marray.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let cnt_step xs xd j c =
  let s = get xs j in
  let d = get xd j in
  if eqb s d
  then c
  else let c1 = set c s (add0 (get c s) (Uint63.of_int (1))) in
       set c1 d (add0 (get c1 d) (Uint63.of_int (1)))

(** val faced_f :
    Uint63.t -> bool Marray.t -> Float64.t Marray.t -> Uint63.t -> Float64.t **)

let faced_f n adj v i =
  loop n (fun k acc ->
    if get adj (add0 (mul0 i n) k) then add1 acc (get v k) else acc)
    (Uint63.of_int (0)) (get v i)

(** val fmin : Float64.t -> Float64.t -> Float64.t **)

let fmin b x =
  if ltb1 x b then x else b

(** val dlt : z -> z -> z -> z -> bool **)

let dlt x a y b =
  if Z.leb a b
  then Z.ltb x (Z.shiftl y (Z.sub b a))
  else Z.ltb (Z.shiftl x (Z.sub a b)) y

(** val f_u : Float64.t **)

let f_u =
  (Float64.of_float (0x1p-52))

(** val f_K1 : Float64.t **)

let f_K1 =
  (Float64.of_float (0x1.00000004p+0))

(** val f_s30 : Float64.t **)

let f_s30 =
  (Float64.of_float (0x1p-30))

(** val out_step :
    uint Marray.t -> uint Marray.t -> Float64.t Marray.t -> Uint63.t ->
    Float64.t Marray.t -> Float64.t Marray.t **)

let out_step xs xd xf j o =
  let s = get xs j in
  let d = get xd j in
  if eqb s d then o else set o s (add1 (get o s) (get xf j))

(** val coef : Float64.t Marray.t -> Uint63.t -> Float64.t **)

let coef ou x =
  add1 (abs (sub1 (Float64.of_float (0x1p+0)) (get ou x))) f_s30

(** val kx : Uint63.t Marray.t -> Uint63.t -> Float64.t **)

let kx c x =
  mul1 (of_uint63 (add0 (add0 (get c x) (get c x)) (Uint63.of_int (3)))) f_u

(** val up : Float64.t -> Float64.t **)

let up y =
  add1 (mul1 y f_K1) f_u

(** val elink :
    uint Marray.t -> uint Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t -> Float64.t Marray.t -> Uint63.t -> (Float64.t
    Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t Marray.t **)

let elink xs xd xf v e j st =
  let s = get xs j in
  let d = get xd j in
  if eqb s d
  then st
  else let a = abs (mul1 (get xf j) (get v s)) in
       let ein = fst st in
       let mac = snd st in
       let mac1 = set mac d (add1 (get mac d) a) in
       ((set ein d (add1 (get ein d) (mul1 (get xf j) (get e s)))),
       (set mac1 s (add1 (get mac1 s) a)))

(** val efort :
    Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Uint63.t -> (Float64.t Marray.t * bool) -> Float64.t Marray.t * bool **)

let efort ou c v e ein mac x st =
  let y =
    up
      (add1 (add1 (mul1 (coef ou x) (get e x)) (get ein x))
        (mul1 (kx c x)
          (add1 (add1 (abs (get v x)) (get mac x))
            (Float64.of_float (0x1p+0)))))
  in
  ((set (fst st) x y), ((&&) (snd st) (leb0 y (Float64.of_float (0x1p+0)))))

(** val ebound :
    Uint63.t -> Uint63.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t Marray.t
    -> Float64.t Marray.t -> Float64.t Marray.t * bool **)

let ebound n l xs xd xf ou c v e =
  let st =
    loop l (elink xs xd xf v e) (Uint63.of_int (0))
      ((make n (Float64.of_float (0x0p+0))),
      (make n (Float64.of_float (0x0p+0))))
  in
  loop n (efort ou c v e (fst st) (snd st)) (Uint63.of_int (0))
    ((make n (Float64.of_float (0x0p+0))), true)

(** val tstep :
    Uint63.t -> Uint63.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    ((Float64.t Marray.t * Float64.t Marray.t) * bool) -> (Float64.t
    Marray.t * Float64.t Marray.t) * bool **)

let tstep n l xs xd xf ou c _ st = match st with
| (p, ok) ->
  let (v, e) = p in
  if ok
  then let r = ebound n l xs xd xf ou c v e in
       (((unit_f l xs xd xf v), (fst r)), (snd r))
  else st

(** val fpair :
    Uint63.t -> bool Marray.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Uint63.t -> Float64.t * Float64.t **)

let fpair n adj v e i =
  loop n (fun k st ->
    if get adj (add0 (mul0 i n) k)
    then ((add1 (fst st) (get e k)), (add1 (snd st) (abs (get v k))))
    else st) (Uint63.of_int (0)) ((get e i), (abs (get v i)))

(** val fbound :
    Uint63.t -> bool Marray.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Float64.t -> Uint63.t -> Float64.t **)

let fbound n adj v e nu i =
  let p = fpair n adj v e i in
  up (add1 (fst p) (mul1 nu (add1 (snd p) (Float64.of_float (0x1p+0)))))

(** val gmax : Uint63.t -> (Uint63.t -> Float64.t) -> Float64.t **)

let gmax n g =
  loop n (fun i m -> if ltb1 m (g i) then g i else m) (Uint63.of_int (0))
    (Float64.of_float (0x0p+0))

(** val fcheck : Float64.t -> Float64.t -> bool **)

let fcheck b o =
  let (mb, eb) = fex b in
  let (mo, eo) = fex o in
  (||) (dlt mb eb (Zpos XH) (Zneg (XO (XO (XI (XO XH))))))
    (dlt
      (Z.mul mb (Zpos (XI (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO XH))))))))))))))))))))))
      eb mo eo)

(** val timing_impl :
    uint -> Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> Float64.t **)

let timing_impl xt xu xs xd xf =
  let n = length xu in
  let l = length xs in
  let c =
    loop l (cnt_step xs xd) (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
  in
  let ou =
    loop l (out_step xs xd xf) (Uint63.of_int (0))
      (make n (Float64.of_float (0x0p+0)))
  in
  let (p, ok) =
    loop xt (tstep n l xs xd xf ou c) (Uint63.of_int (0)) ((xu,
      (make n (Float64.of_float (0x0p+0)))), true)
  in
  let (v, e) = p in
  if ok
  then let adj =
         loop l (adj_step n xs xd) (Uint63.of_int (0)) (make (mul0 n n) false)
       in
       let o =
         loop n (fun i b -> fmin b (faced_f n adj v i)) (Uint63.of_int (1))
           (faced_f n adj v (Uint63.of_int (0)))
       in
       let nu = mul1 (of_uint63 (add0 n (Uint63.of_int (1)))) f_u in
       let b = gmax n (fbound n adj v e nu) in
       if fcheck b o then o else timing_exact xt xu xs xd xf
  else timing_exact xt xu xs xd xf

(** val timing :
    uint -> Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> Float64.t
    Marray.t -> Float64.t **)

let timing =
  timing_impl
