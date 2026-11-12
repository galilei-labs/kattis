
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

  (** val eqb : Bigint.t -> Bigint.t -> bool **)

  let rec eqb p q =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        (fun _ -> false)
        q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun q0 -> eqb p0 q0)
        (fun _ -> false)
        q)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q)
      p
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

  (** val eqb : Bigint.t -> Bigint.t -> bool **)

  let eqb = Bigint.equal

  (** val max : Bigint.t -> Bigint.t -> Bigint.t **)

  let max = Bigint.max

  (** val min : Bigint.t -> Bigint.t -> Bigint.t **)

  let min = Bigint.min

  (** val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' =
        add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r) Bigint.one
      in
      if ltb r' b
      then ((mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q), r')
      else ((add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q)
              Bigint.one),
             (sub r' b)))
      (fun a' ->
      let (q, r) = pos_div_eucl a' b in
      let r' = mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r in
      if ltb r' b
      then ((mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q), r')
      else ((add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q)
              Bigint.one),
             (sub r' b)))
      (fun _ ->
      if leb ((fun x -> Bigint.shift_left x 1) Bigint.one) b
      then (Bigint.zero, Bigint.one)
      else (Bigint.one, Bigint.zero))
      a

  (** val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t **)

  let div_eucl = Bigint.(fun x y ->
  match sign y with
  | 0 -> (zero, x)
  | 1 -> ediv_rem x y
  | _ -> let (q, r) = ediv_rem (add (of_int (-1)) x) y in
          (add (of_int (-1)) q, add (add (of_int 1) y) r))

  (** val div : Bigint.t -> Bigint.t -> Bigint.t **)

  let div = Bigint.(fun x y ->
  match sign y with
  | 0 -> zero
  | 1 -> ediv x y
  | _ -> add (of_int (-1)) (ediv (add (of_int (-1)) x) y))

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
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val div0 : Uint63.t -> Uint63.t -> Uint63.t **)

let div0 = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb0 : Uint63.t -> Uint63.t -> bool **)

let eqb0 = Uint63.equal

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val leb0 : Uint63.t -> Uint63.t -> bool **)

let leb0 = Uint63.le

(** val opp0 : Float64.t -> Float64.t **)

let opp0 = Float64.opp

(** val ltb1 : Float64.t -> Float64.t -> bool **)

let ltb1 = Float64.lt

(** val mul1 : Float64.t -> Float64.t -> Float64.t **)

let mul1 = Float64.mul

(** val div1 : Float64.t -> Float64.t -> Float64.t **)

let div1 = Float64.div

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

(** val zofi_rec : Uint63.t -> Bigint.t **)

let rec zofi_rec i =
  if bdec (eqb0 i (Uint63.of_int (0)))
  then Bigint.zero
  else let r = zofi_rec (div0 i (Uint63.of_int (2))) in
       let bit =
         if eqb0 (mod0 i (Uint63.of_int (2))) (Uint63.of_int (0))
         then Bigint.zero
         else Bigint.one
       in
       Z.add (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r) bit

(** val zofi : Uint63.t -> Bigint.t **)

let zofi =
  zofi_rec

(** val pos2int : Bigint.t -> Uint63.t **)

let rec pos2int p =
  (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
    (fun q ->
    add0 (mul0 (Uint63.of_int (2)) (pos2int q)) (Uint63.of_int (1)))
    (fun q -> mul0 (Uint63.of_int (2)) (pos2int q))
    (fun _ -> (Uint63.of_int (1)))
    p

(** val z2int : Bigint.t -> Uint63.t **)

let z2int z0 =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> (Uint63.of_int (0)))
    (fun p -> pos2int p)
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

(** val fconv : Float64.t option -> (Bigint.t * Bigint.t) option **)

let fconv = function
| Some f -> Some (fex f)
| None -> None

(** val iconv : uint option -> (Bigint.t * Bigint.t) option **)

let iconv = function
| Some v -> Some ((zofi v), Bigint.zero)
| None -> None

type sums = { sP : Bigint.t; sK : Bigint.t; sKK : Bigint.t; sY : Bigint.t;
              sKY : Bigint.t; sG : Bigint.t }

(** val sums0 : sums **)

let sums0 =
  { sP = Bigint.zero; sK = Bigint.zero; sKK = Bigint.zero; sY = Bigint.zero;
    sKY = Bigint.zero; sG = Bigint.zero }

(** val acc_step :
    ('a1 -> (Bigint.t * Bigint.t) option) -> 'a1 array -> Uint63.t -> sums ->
    sums **)

let acc_step conv x i s =
  match conv ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x i) with
  | Some d ->
    let m = fst d in
    let e = snd d in
    let k = zofi i in
    let p = Z.add s.sP Bigint.one in
    let sK0 = Z.add s.sK k in
    let sKK0 = Z.add s.sKK (Z.mul k k) in
    if Z.eqb m Bigint.zero
    then { sP = p; sK = sK0; sKK = sKK0; sY = s.sY; sKY = s.sKY; sG = s.sG }
    else let g = Z.min s.sG e in
         let y = Z.shiftl m (Z.sub e g) in
         let sh = Z.sub s.sG g in
         { sP = p; sK = sK0; sKK = sKK0; sY = (Z.add (Z.shiftl s.sY sh) y);
         sKY = (Z.add (Z.shiftl s.sKY sh) (Z.mul k y)); sG = g }
  | None -> s

(** val col_sums :
    ('a1 -> (Bigint.t * Bigint.t) option) -> 'a1 array -> sums **)

let col_sums conv x =
  loop ((fun a -> Uint63.of_int (Array.length a)) x) (fun _ _ -> true)
    (acc_step conv x) (Uint63.of_int (0)) sums0

type fitr = { fc0 : Bigint.t; fc1 : Bigint.t; fden : Bigint.t }

(** val fit : sums -> Bigint.t -> fitr option **)

let fit s sc =
  let p = s.sP in
  let sK0 = s.sK in
  if Z.ltb p ((fun x -> Bigint.shift_left x 1) Bigint.one)
  then None
  else let d = Z.sub (Z.mul p s.sKK) (Z.mul sK0 sK0) in
       let b = Z.sub (Z.mul p s.sKY) (Z.mul sK0 s.sY) in
       let n0 = Z.sub (Z.mul s.sY d) (Z.mul b sK0) in
       let n1 = Z.mul b p in
       let den = Z.mul p d in
       let e = Z.add s.sG sc in
       if Z.leb Bigint.zero e
       then Some { fc0 = (Z.shiftl n0 e); fc1 = (Z.shiftl n1 e); fden = den }
       else Some { fc0 = n0; fc1 = n1; fden = (Z.shiftl den (Z.opp e)) }

(** val rnd_at : fitr -> Bigint.t -> Bigint.t **)

let rnd_at f t =
  Z.div
    (Z.add
      (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one)
        (Z.add f.fc0 (Z.mul f.fc1 t)))
      f.fden)
    (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) f.fden)

(** val clampZ : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t **)

let clampZ lo hi v =
  Z.max lo (Z.min hi v)

(** val fl_of_Z : Bigint.t -> Float64.t **)

let fl_of_Z z0 =
  if Z.ltb z0 Bigint.zero
  then opp0 (of_uint63 (z2int (Z.opp z0)))
  else of_uint63 (z2int z0)

(** val c20 : Float64.t **)

let c20 =
  div1 (of_uint63 (Uint63.of_int (1))) (of_uint63 (Uint63.of_int (1048576)))

(** val fout :
    fitr option -> Bigint.t -> Bigint.t -> Bigint.t -> Float64.t option **)

let fout fo lo hi t =
  match fo with
  | Some f ->
    Some
      (mul1
        (fl_of_Z
          (clampZ
            (Z.mul lo ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              Bigint.one)))))))))))))))))))))
            (Z.mul hi ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1)
              Bigint.one)))))))))))))))))))))
            (rnd_at f t)))
        c20)
  | None -> None

(** val iout :
    fitr option -> Bigint.t -> Bigint.t -> Bigint.t -> uint option **)

let iout fo lo hi t =
  match fo with
  | Some f -> Some (z2int (clampZ lo hi (rnd_at f t)))
  | None -> None

type out =
  ((Float64.t option array * uint option array) * Float64.t option
  array) * uint option array

(** val out_step :
    fitr option -> fitr option -> fitr option -> fitr option -> Bigint.t ->
    Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> out -> out **)

let out_step ft fd fs fh nt nd ns nh i = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  let j = zofi i in
  (((((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a i
       (fout ft (Bigint.neg ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.succ (Bigint.shift_left x 1))
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))
         ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.succ (Bigint.shift_left x 1))
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)))))
         (Z.add nt j))),
  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b i
    (iout fd Bigint.zero ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) Bigint.one)))))))) (Z.add nd j)))),
  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c i
    (fout fs Bigint.zero ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) Bigint.one)))))) (Z.add ns j)))),
  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) d i
    (iout fh Bigint.zero ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))
      (Z.add nh j))))

(** val vedurspa_impl :
    Float64.t option array -> uint option array -> Float64.t option array ->
    uint option array -> uint -> out **)

let vedurspa_impl xt xd xs xh m =
  let ft =
    fit (col_sums fconv xt) ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) Bigint.one))))
  in
  let fd = fit (col_sums iconv xd) Bigint.zero in
  let fs =
    fit (col_sums fconv xs) ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) Bigint.one))))
  in
  let fh = fit (col_sums iconv xh) Bigint.zero in
  let l =
    if leb0 m (Uint63.of_int 4194303) then m else (Uint63.of_int 4194303)
  in
  loop l (fun _ _ -> true)
    (out_step ft fd fs fh
      (zofi ((fun a -> Uint63.of_int (Array.length a)) xt))
      (zofi ((fun a -> Uint63.of_int (Array.length a)) xd))
      (zofi ((fun a -> Uint63.of_int (Array.length a)) xs))
      (zofi ((fun a -> Uint63.of_int (Array.length a)) xh)))
    (Uint63.of_int (0))
    (((((fun n d -> Array.make (Uint63.hash n) d) l None),
    ((fun n d -> Array.make (Uint63.hash n) d) l None)),
    ((fun n d -> Array.make (Uint63.hash n) d) l None)),
    ((fun n d -> Array.make (Uint63.hash n) d) l None))

(** val vedurspa :
    Float64.t option array -> uint option array -> Float64.t option array ->
    uint option array -> uint -> ((Float64.t option array * uint option
    array) * Float64.t option array) * uint option array **)

let vedurspa =
  vedurspa_impl
