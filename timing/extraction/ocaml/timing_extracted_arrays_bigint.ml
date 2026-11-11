
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

module Pos =
 struct
  (** val succ : Bigint.t -> Bigint.t **)

  let rec succ x =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p -> (fun x -> Bigint.shift_left x 1) (succ p))
      (fun p -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) p)
      (fun _ -> (fun x -> Bigint.shift_left x 1) Bigint.one)
      x

  (** val add : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec add x y =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.shift_left x 1) (add_carry p q))
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q))
        (fun _ -> (fun x -> Bigint.shift_left x 1) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q))
        (fun q -> (fun x -> Bigint.shift_left x 1) (add p q))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.shift_left x 1) (succ q))
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) q)
        (fun _ -> (fun x -> Bigint.shift_left x 1) Bigint.one)
        y)
      x

  (** val add_carry : Bigint.t -> Bigint.t -> Bigint.t **)

  and add_carry x y =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add_carry p q))
        (fun q -> (fun x -> Bigint.shift_left x 1) (add_carry p q))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.shift_left x 1) (add_carry p q))
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q))
        (fun _ -> (fun x -> Bigint.shift_left x 1) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (succ q))
        (fun q -> (fun x -> Bigint.shift_left x 1) (succ q))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
        y)
      x

  (** val pred_double : Bigint.t -> Bigint.t **)

  let rec pred_double x =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) p))
      (fun p -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
      (pred_double p))
      (fun _ -> Bigint.one)
      x

  (** val mul : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec mul x y =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p -> add y ((fun x -> Bigint.shift_left x 1) (mul p y)))
      (fun p -> (fun x -> Bigint.shift_left x 1) (mul p y))
      (fun _ -> y)
      x

  (** val iter : ('a1 -> 'a1) -> 'a1 -> Bigint.t -> 'a1 **)

  let rec iter f x n =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun n' -> f (iter f (iter f x n') n'))
      (fun n' -> iter f (iter f x n') n')
      (fun _ -> f x)
      n

  (** val div2 : Bigint.t -> Bigint.t **)

  let div2 p =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p0 -> p0)
      (fun p0 -> p0)
      (fun _ -> Bigint.one)
      p

  (** val div2_up : Bigint.t -> Bigint.t **)

  let div2_up p =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p0 -> succ p0)
      (fun p0 -> p0)
      (fun _ -> Bigint.one)
      p

  (** val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison **)

  let rec compare_cont r x y =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> compare_cont r p q)
        (fun q -> compare_cont Gt p q)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> compare_cont Lt p q)
        (fun q -> compare_cont r p q)
        (fun _ -> Gt)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun _ -> r)
        y)
      x

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare =
    compare_cont Eq
 end

module Z =
 struct
  (** val double : Bigint.t -> Bigint.t **)

  let double x =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.zero)
      (fun p -> ((fun x -> Bigint.shift_left x 1) p))
      (fun p -> Bigint.neg ((fun x -> Bigint.shift_left x 1) p))
      x

  (** val succ_double : Bigint.t -> Bigint.t **)

  let succ_double x =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.one)
      (fun p -> ((fun x -> Bigint.succ (Bigint.shift_left x 1)) p))
      (fun p -> Bigint.neg (Pos.pred_double p))
      x

  (** val pred_double : Bigint.t -> Bigint.t **)

  let pred_double x =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.neg Bigint.one)
      (fun p -> (Pos.pred_double p))
      (fun p -> Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      p))
      x

  (** val pos_sub : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec pos_sub x y =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> double (pos_sub p q))
        (fun q -> succ_double (pos_sub p q))
        (fun _ -> ((fun x -> Bigint.shift_left x 1) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> pred_double (pos_sub p q))
        (fun q -> double (pos_sub p q))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q -> Bigint.neg ((fun x -> Bigint.shift_left x 1) q))
        (fun q -> Bigint.neg (Pos.pred_double q))
        (fun _ -> Bigint.zero)
        y)
      x

  (** val add : Bigint.t -> Bigint.t -> Bigint.t **)

  let add = Bigint.add

  (** val opp : Bigint.t -> Bigint.t **)

  let opp = Bigint.neg

  (** val sub : Bigint.t -> Bigint.t -> Bigint.t **)

  let sub = Bigint.sub

  (** val mul : Bigint.t -> Bigint.t -> Bigint.t **)

  let mul = Bigint.mul

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare = (fun x y -> let s = Bigint.compare x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val leb : Bigint.t -> Bigint.t -> bool **)

  let leb = Bigint.le

  (** val ltb : Bigint.t -> Bigint.t -> bool **)

  let ltb = Bigint.lt

  (** val min : Bigint.t -> Bigint.t -> Bigint.t **)

  let min = Bigint.min

  (** val div2 : Bigint.t -> Bigint.t **)

  let div2 z0 =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.zero)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> (Pos.div2 p))
        (fun _ -> (Pos.div2 p))
        (fun _ -> Bigint.zero)
        p)
      (fun p -> Bigint.neg (Pos.div2_up p))
      z0

  (** val shiftl : Bigint.t -> Bigint.t -> Bigint.t **)

  let shiftl = Bigint.(fun x y ->
  let y = to_int y in
  if y < 0 then shift_right x (-y)
  else shift_left x y)

  (** val shiftr : Bigint.t -> Bigint.t -> Bigint.t **)

  let shiftr = Bigint.(fun x y ->
  let y = to_int y in
  if y < 0 then shift_left x (-y)
  else shift_right x y)
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

(** val zofi_rec : Uint63.t -> Bigint.t **)

let rec zofi_rec i =
  if bdec (eqb i (Uint63.of_int (0)))
  then Bigint.zero
  else let r = zofi_rec (div i (Uint63.of_int (2))) in
       let bit =
         if eqb (mod0 i (Uint63.of_int (2))) (Uint63.of_int (0))
         then Bigint.zero
         else Bigint.one
       in
       Z.add (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r) bit

(** val zofi : Uint63.t -> Bigint.t **)

let zofi =
  zofi_rec

(** val iofp : Bigint.t -> Uint63.t **)

let rec iofp p =
  (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
    (fun q ->
    add0 (mul0 (Uint63.of_int (2)) (iofp q)) (Uint63.of_int (1)))
    (fun q -> mul0 (Uint63.of_int (2)) (iofp q))
    (fun _ -> (Uint63.of_int (1)))
    p

(** val iofz : Bigint.t -> Uint63.t **)

let iofz z0 =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> (Uint63.of_int (0)))
    (fun p -> iofp p)
    (fun _ -> (Uint63.of_int (0)))
    z0

(** val fex : Float64.t -> Bigint.t * Bigint.t **)

let fex f =
  let (z0, e) = frshiftexp f in
  let m = zofi (normfr_mantissa z0) in
  ((if ltb1 f (Float64.of_float (0x0p+0)) then Z.opp m else m),
  (Z.sub (zofi e) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    Bigint.one)))))))))))))

(** val pP : Bigint.t **)

let pP =
  ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))

(** val oNE : Bigint.t **)

let oNE =
  Z.shiftl Bigint.one pP

(** val fixv : Float64.t -> Bigint.t **)

let fixv f =
  let d = fex f in Z.shiftl (fst d) (Z.add (snd d) pP)

(** val build : Uint63.t -> (Uint63.t -> Bigint.t) -> Bigint.t array **)

let build len f =
  loop len (fun k a ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a k (f k))
    (Uint63.of_int (0))
    ((fun n d -> Array.make (Uint63.hash n) d) len Bigint.zero)

(** val dot :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t ->
    Bigint.t **)

let dot s x y i j =
  loop s (fun k acc ->
    Z.add acc
      (Z.mul
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x
          (add0 (mul0 i s) k))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y
          (add0 (mul0 k s) j))))
    (Uint63.of_int (0)) Bigint.zero

(** val naive :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array **)

let naive s x y =
  build (mul0 s s) (fun k -> dot s x y (div k s) (mod0 k s))

(** val quad :
    Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Bigint.t array **)

let quad x s h di dj =
  build (mul0 h h) (fun k ->
    (fun a i -> Array.unsafe_get a (Uint63.hash i)) x
      (add0 (mul0 (add0 di (div k h)) s) (add0 dj (mod0 k h))))

(** val madd :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array **)

let madd h a b =
  build (mul0 h h) (fun k ->
    Z.add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) a k)
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b k))

(** val msub :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array **)

let msub h a b =
  build (mul0 h h) (fun k ->
    Z.sub ((fun a i -> Array.unsafe_get a (Uint63.hash i)) a k)
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b k))

(** val comb :
    Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t
    array -> Bigint.t array -> Bigint.t array **)

let comb s h c11 c12 c21 c22 =
  build (mul0 s s) (fun k ->
    let i = div k s in
    let j = mod0 k s in
    if ltb0 i h
    then if ltb0 j h
         then (fun a i -> Array.unsafe_get a (Uint63.hash i)) c11
                (add0 (mul0 i h) j)
         else (fun a i -> Array.unsafe_get a (Uint63.hash i)) c12
                (add0 (mul0 i h) (sub0 j h))
    else if ltb0 j h
         then (fun a i -> Array.unsafe_get a (Uint63.hash i)) c21
                (add0 (mul0 (sub0 i h) h) j)
         else (fun a i -> Array.unsafe_get a (Uint63.hash i)) c22
                (add0 (mul0 (sub0 i h) h) (sub0 j h)))

(** val cut : Uint63.t **)

let cut =
  (Uint63.of_int (16))

(** val splitb : Uint63.t -> bool **)

let splitb s =
  (&&) (ltb0 cut s) (eqb (mod0 s (Uint63.of_int (2))) (Uint63.of_int (0)))

(** val strass :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array **)

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

(** val mulr :
    Uint63.t -> Bigint.t array -> Bigint.t array -> Bigint.t array **)

let mulr m x y =
  let c = strass m x y in
  build (mul0 m m) (fun k ->
    Z.shiftr ((fun a i -> Array.unsafe_get a (Uint63.hash i)) c k) pP)

(** val ident : Uint63.t -> Bigint.t array **)

let ident m =
  build (mul0 m m) (fun k ->
    if eqb (div k m) (mod0 k m) then oNE else Bigint.zero)

(** val link_step :
    Uint63.t -> uint array -> uint array -> Float64.t array -> Uint63.t ->
    Bigint.t array -> Bigint.t array **)

let link_step m xs xd xf l a =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs l in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd l in
  let f = fixv ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xf l) in
  let a1 =
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a
      (add0 (mul0 d m) s)
      (Z.add
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) a
          (add0 (mul0 d m) s))
        f)
  in
  (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a1
    (add0 (mul0 s m) s)
    (Z.sub
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) a1 (add0 (mul0 s m) s))
      f)

(** val amat :
    Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
    Bigint.t array **)

let amat m l xs xd xf =
  loop l (link_step m xs xd xf) (Uint63.of_int (0)) (ident m)

(** val pw :
    Uint63.t -> Uint63.t -> Bigint.t array option -> Bigint.t array ->
    Bigint.t array option **)

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
    Uint63.t -> uint array -> uint array -> Uint63.t -> bool array -> bool
    array **)

let adj_step n xs xd l a =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs l in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd l in
  if eqb s d
  then a
  else (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a
           (add0 (mul0 s n) d) true)
         (add0 (mul0 d n) s) true

(** val faced_z :
    Uint63.t -> bool array -> Bigint.t array -> Uint63.t -> Bigint.t **)

let faced_z n adj v i =
  Z.add ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v i)
    (loop n (fun k acc ->
      if (fun a i -> Array.unsafe_get a (Uint63.hash i)) adj
           (add0 (mul0 i n) k)
      then Z.add acc ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v k)
      else acc) (Uint63.of_int (0)) Bigint.zero)

(** val cv : Bigint.t -> Float64.t **)

let cv z0 =
  div0
    (of_uint63
      (iofz
        (Z.shiftr z0
          (Z.sub (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) pP)
            ((fun x -> Bigint.shift_left x 1)
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))))
    (of_uint63 (Uint63.of_int (1073741824)))

(** val conv : Bigint.t -> Float64.t **)

let conv z0 =
  if Z.ltb z0 Bigint.zero then opp0 (cv (Z.opp z0)) else cv z0

(** val timing_exact :
    uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
    Float64.t **)

let timing_exact xt xu xs xd xf =
  let n = (fun a -> Uint63.of_int (Array.length a)) xu in
  let l = (fun a -> Uint63.of_int (Array.length a)) xs in
  let m =
    mul0 (div (add0 n (Uint63.of_int (7))) (Uint63.of_int (8)))
      (Uint63.of_int (8))
  in
  let a = amat m l xs xd xf in
  let rf = match pw m xt None a with
           | Some x -> x
           | None -> ident m in
  let uh =
    build m (fun s ->
      if ltb0 s n
      then fixv ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xu s)
      else Bigint.zero)
  in
  let v =
    build m (fun i ->
      loop m (fun k acc ->
        Z.add acc
          (Z.mul
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) rf
              (add0 (mul0 i m) k))
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) uh k)))
        (Uint63.of_int (0)) Bigint.zero)
  in
  let adj =
    loop l (adj_step n xs xd) (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) false)
  in
  let best =
    loop n (fun i b -> Z.min b (faced_z n adj v i)) (Uint63.of_int (1))
      (faced_z n adj v (Uint63.of_int (0)))
  in
  conv best

(** val link_f :
    uint array -> uint array -> Float64.t array -> Float64.t array ->
    Uint63.t -> Float64.t array -> Float64.t array **)

let link_f xs xd xf v j w =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs j in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd j in
  if eqb s d
  then w
  else let a =
         mul1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xf j)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v s)
       in
       let w1 =
         (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) w d
           (add1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w d) a)
       in
       (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) w1 s
         (sub1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w1 s) a)

(** val unit_f :
    Uint63.t -> uint array -> uint array -> Float64.t array -> Float64.t
    array -> Float64.t array **)

let unit_f l xs xd xf v =
  loop l (link_f xs xd xf v) (Uint63.of_int (0)) (Array.copy v)

(** val cnt_step :
    uint array -> uint array -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let cnt_step xs xd j c =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs j in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd j in
  if eqb s d
  then c
  else let c1 =
         (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c s
           (add0 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) c s)
             (Uint63.of_int (1)))
       in
       (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c1 d
         (add0 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) c1 d)
           (Uint63.of_int (1)))

(** val faced_f :
    Uint63.t -> bool array -> Float64.t array -> Uint63.t -> Float64.t **)

let faced_f n adj v i =
  loop n (fun k acc ->
    if (fun a i -> Array.unsafe_get a (Uint63.hash i)) adj (add0 (mul0 i n) k)
    then add1 acc ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v k)
    else acc) (Uint63.of_int (0))
    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v i)

(** val fmin : Float64.t -> Float64.t -> Float64.t **)

let fmin b x =
  if ltb1 x b then x else b

(** val dlt : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> bool **)

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
    uint array -> uint array -> Float64.t array -> Uint63.t -> Float64.t
    array -> Float64.t array **)

let out_step xs xd xf j o =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs j in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd j in
  if eqb s d
  then o
  else (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) o s
         (add1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) o s)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xf j))

(** val coef : Float64.t array -> Uint63.t -> Float64.t **)

let coef ou x =
  add1
    (abs
      (sub1 (Float64.of_float (0x1p+0))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) ou x)))
    f_s30

(** val kx : Uint63.t array -> Uint63.t -> Float64.t **)

let kx c x =
  mul1
    (of_uint63
      (add0
        (add0 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) c x)
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) c x))
        (Uint63.of_int (3))))
    f_u

(** val up : Float64.t -> Float64.t **)

let up y =
  add1 (mul1 y f_K1) f_u

(** val elink :
    uint array -> uint array -> Float64.t array -> Float64.t array ->
    Float64.t array -> Uint63.t -> (Float64.t array * Float64.t array) ->
    Float64.t array * Float64.t array **)

let elink xs xd xf v e j st =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs j in
  let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd j in
  if eqb s d
  then st
  else let a =
         abs
           (mul1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xf j)
             ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v s))
       in
       let ein = fst st in
       let mac = snd st in
       let mac1 =
         (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) mac d
           (add1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) mac d) a)
       in
       (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) ein d
          (add1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) ein d)
            (mul1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xf j)
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) e s)))),
       ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) mac1 s
         (add1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) mac1 s) a)))

(** val efort :
    Float64.t array -> Uint63.t array -> Float64.t array -> Float64.t array
    -> Float64.t array -> Float64.t array -> Uint63.t -> (Float64.t
    array * bool) -> Float64.t array * bool **)

let efort ou c v e ein mac x st =
  let y =
    up
      (add1
        (add1
          (mul1 (coef ou x)
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) e x))
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) ein x))
        (mul1 (kx c x)
          (add1
            (add1 (abs ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v x))
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) mac x))
            (Float64.of_float (0x1p+0)))))
  in
  (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) (fst st) x y),
  ((&&) (snd st) (leb0 y (Float64.of_float (0x1p+0)))))

(** val ebound :
    Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
    Float64.t array -> Uint63.t array -> Float64.t array -> Float64.t array
    -> Float64.t array * bool **)

let ebound n l xs xd xf ou c v e =
  let st =
    loop l (elink xs xd xf v e) (Uint63.of_int (0))
      (((fun n d -> Array.make (Uint63.hash n) d) n
         (Float64.of_float (0x0p+0))),
      ((fun n d -> Array.make (Uint63.hash n) d) n
        (Float64.of_float (0x0p+0))))
  in
  loop n (efort ou c v e (fst st) (snd st)) (Uint63.of_int (0))
    (((fun n d -> Array.make (Uint63.hash n) d) n (Float64.of_float (0x0p+0))),
    true)

(** val tstep :
    Uint63.t -> Uint63.t -> uint array -> uint array -> Float64.t array ->
    Float64.t array -> Uint63.t array -> Uint63.t -> ((Float64.t
    array * Float64.t array) * bool) -> (Float64.t array * Float64.t
    array) * bool **)

let tstep n l xs xd xf ou c _ st = match st with
| (p, ok) ->
  let (v, e) = p in
  if ok
  then let r = ebound n l xs xd xf ou c v e in
       (((unit_f l xs xd xf v), (fst r)), (snd r))
  else st

(** val fpair :
    Uint63.t -> bool array -> Float64.t array -> Float64.t array -> Uint63.t
    -> Float64.t * Float64.t **)

let fpair n adj v e i =
  loop n (fun k st ->
    if (fun a i -> Array.unsafe_get a (Uint63.hash i)) adj (add0 (mul0 i n) k)
    then ((add1 (fst st)
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) e k)),
           (add1 (snd st)
             (abs ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v k))))
    else st) (Uint63.of_int (0))
    (((fun a i -> Array.unsafe_get a (Uint63.hash i)) e i),
    (abs ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v i)))

(** val fbound :
    Uint63.t -> bool array -> Float64.t array -> Float64.t array -> Float64.t
    -> Uint63.t -> Float64.t **)

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
  (||)
    (dlt mb eb Bigint.one (Bigint.neg ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) Bigint.one))))))
    (dlt
      (Z.mul mb ((fun x -> Bigint.succ (Bigint.shift_left x 1))
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) Bigint.one)))))))))))))))))))))
      eb mo eo)

(** val timing_impl :
    uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
    Float64.t **)

let timing_impl xt xu xs xd xf =
  let n = (fun a -> Uint63.of_int (Array.length a)) xu in
  let l = (fun a -> Uint63.of_int (Array.length a)) xs in
  let c =
    loop l (cnt_step xs xd) (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))
  in
  let ou =
    loop l (out_step xs xd xf) (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n
        (Float64.of_float (0x0p+0)))
  in
  let (p, ok) =
    loop xt (tstep n l xs xd xf ou c) (Uint63.of_int (0)) ((xu,
      ((fun n d -> Array.make (Uint63.hash n) d) n
        (Float64.of_float (0x0p+0)))),
      true)
  in
  let (v, e) = p in
  if ok
  then let adj =
         loop l (adj_step n xs xd) (Uint63.of_int (0))
           ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) false)
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
    uint -> Float64.t array -> uint array -> uint array -> Float64.t array ->
    Float64.t **)

let timing =
  timing_impl
