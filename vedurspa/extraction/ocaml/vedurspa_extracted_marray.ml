
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

  (** val div : z -> z -> z **)

  let div a b =
    let (q, _) = div_eucl a b in q

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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val max_length : Uint63.t **)

let max_length = Marray.max_length

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

(** val zofi_rec : Uint63.t -> z **)

let rec zofi_rec i =
  if bdec (eqb0 i (Uint63.of_int (0)))
  then Z0
  else let r = zofi_rec (div0 i (Uint63.of_int (2))) in
       let bit =
         if eqb0 (mod0 i (Uint63.of_int (2))) (Uint63.of_int (0))
         then Z0
         else Zpos XH
       in
       Z.add (Z.mul (Zpos (XO XH)) r) bit

(** val zofi : Uint63.t -> z **)

let zofi =
  zofi_rec

(** val pos2int : positive -> Uint63.t **)

let rec pos2int = function
| XI q -> add0 (mul0 (Uint63.of_int (2)) (pos2int q)) (Uint63.of_int (1))
| XO q -> mul0 (Uint63.of_int (2)) (pos2int q)
| XH -> (Uint63.of_int (1))

(** val z2int : z -> Uint63.t **)

let z2int = function
| Zpos p -> pos2int p
| _ -> (Uint63.of_int (0))

(** val fex : Float64.t -> z * z **)

let fex f =
  let (z0, e) = frshiftexp f in
  let m = zofi (normfr_mantissa z0) in
  ((if ltb1 f (Float64.of_float (0x0p+0)) then Z.opp m else m),
  (Z.sub (zofi e) (Zpos (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO
    XH))))))))))))))

(** val fconv : Float64.t option -> (z * z) option **)

let fconv = function
| Some f -> Some (fex f)
| None -> None

(** val iconv : uint option -> (z * z) option **)

let iconv = function
| Some v -> Some ((zofi v), Z0)
| None -> None

type sums = { sP : z; sK : z; sKK : z; sY : z; sKY : z; sG : z }

(** val sums0 : sums **)

let sums0 =
  { sP = Z0; sK = Z0; sKK = Z0; sY = Z0; sKY = Z0; sG = Z0 }

(** val acc_step :
    ('a1 -> (z * z) option) -> 'a1 Marray.t -> Uint63.t -> sums -> sums **)

let acc_step conv x i s =
  match conv (get x i) with
  | Some d ->
    let m = fst d in
    let e = snd d in
    let k = zofi i in
    let p = Z.add s.sP (Zpos XH) in
    let sK0 = Z.add s.sK k in
    let sKK0 = Z.add s.sKK (Z.mul k k) in
    if Z.eqb m Z0
    then { sP = p; sK = sK0; sKK = sKK0; sY = s.sY; sKY = s.sKY; sG = s.sG }
    else let g = Z.min s.sG e in
         let y = Z.shiftl m (Z.sub e g) in
         let sh = Z.sub s.sG g in
         { sP = p; sK = sK0; sKK = sKK0; sY = (Z.add (Z.shiftl s.sY sh) y);
         sKY = (Z.add (Z.shiftl s.sKY sh) (Z.mul k y)); sG = g }
  | None -> s

(** val col_sums : ('a1 -> (z * z) option) -> 'a1 Marray.t -> sums **)

let col_sums conv x =
  loop (length x) (fun _ _ -> true) (acc_step conv x) (Uint63.of_int (0))
    sums0

type fitr = { fc0 : z; fc1 : z; fden : z }

(** val fit : sums -> z -> fitr option **)

let fit s sc =
  let p = s.sP in
  let sK0 = s.sK in
  if Z.ltb p (Zpos (XO XH))
  then None
  else let d = Z.sub (Z.mul p s.sKK) (Z.mul sK0 sK0) in
       let b = Z.sub (Z.mul p s.sKY) (Z.mul sK0 s.sY) in
       let n0 = Z.sub (Z.mul s.sY d) (Z.mul b sK0) in
       let n1 = Z.mul b p in
       let den = Z.mul p d in
       let e = Z.add s.sG sc in
       if Z.leb Z0 e
       then Some { fc0 = (Z.shiftl n0 e); fc1 = (Z.shiftl n1 e); fden = den }
       else Some { fc0 = n0; fc1 = n1; fden = (Z.shiftl den (Z.opp e)) }

(** val rnd_at : fitr -> z -> z **)

let rnd_at f t =
  Z.div (Z.add (Z.mul (Zpos (XO XH)) (Z.add f.fc0 (Z.mul f.fc1 t))) f.fden)
    (Z.mul (Zpos (XO XH)) f.fden)

(** val clampZ : z -> z -> z -> z **)

let clampZ lo hi v =
  Z.max lo (Z.min hi v)

(** val fl_of_Z : z -> Float64.t **)

let fl_of_Z z0 =
  if Z.ltb z0 Z0
  then opp0 (of_uint63 (z2int (Z.opp z0)))
  else of_uint63 (z2int z0)

(** val c20 : Float64.t **)

let c20 =
  div1 (of_uint63 (Uint63.of_int (1))) (of_uint63 (Uint63.of_int (1048576)))

(** val fout : fitr option -> z -> z -> z -> Float64.t option **)

let fout fo lo hi t =
  match fo with
  | Some f ->
    Some
      (mul1
        (fl_of_Z
          (clampZ
            (Z.mul lo (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
              (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))))))))))))))
            (Z.mul hi (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
              (XO (XO (XO (XO (XO (XO (XO (XO XH))))))))))))))))))))))
            (rnd_at f t)))
        c20)
  | None -> None

(** val iout : fitr option -> z -> z -> z -> uint option **)

let iout fo lo hi t =
  match fo with
  | Some f -> Some (z2int (clampZ lo hi (rnd_at f t)))
  | None -> None

type out =
  ((Float64.t option Marray.t * uint option Marray.t) * Float64.t option
  Marray.t) * uint option Marray.t

(** val out_step :
    fitr option -> fitr option -> fitr option -> fitr option -> z -> z -> z
    -> z -> Uint63.t -> out -> out **)

let out_step ft fd fs fh nt nd ns nh i = function
| (p, d) ->
  let (p0, c) = p in
  let (a, b) = p0 in
  let j = zofi i in
  ((((set a i
       (fout ft (Zneg (XO (XI (XO (XO (XI XH)))))) (Zpos (XO (XI (XO (XO (XI
         XH)))))) (Z.add nt j))),
  (set b i
    (iout fd Z0 (Zpos (XO (XO (XO (XI (XO (XI (XI (XO XH)))))))))
      (Z.add nd j)))),
  (set c i (fout fs Z0 (Zpos (XO (XO (XO (XO (XI (XO XH))))))) (Z.add ns j)))),
  (set d i (iout fh Z0 (Zpos (XO (XI (XI (XI (XO (XI XH))))))) (Z.add nh j))))

(** val vedurspa_impl :
    Float64.t option Marray.t -> uint option Marray.t -> Float64.t option
    Marray.t -> uint option Marray.t -> uint -> out **)

let vedurspa_impl xt xd xs xh m =
  let ft = fit (col_sums fconv xt) (Zpos (XO (XO (XI (XO XH))))) in
  let fd = fit (col_sums iconv xd) Z0 in
  let fs = fit (col_sums fconv xs) (Zpos (XO (XO (XI (XO XH))))) in
  let fh = fit (col_sums iconv xh) Z0 in
  let l = if leb0 m max_length then m else max_length in
  loop l (fun _ _ -> true)
    (out_step ft fd fs fh (zofi (length xt)) (zofi (length xd))
      (zofi (length xs)) (zofi (length xh)))
    (Uint63.of_int (0)) ((((make l None), (make l None)), (make l None)),
    (make l None))

(** val vedurspa :
    Float64.t option Marray.t -> uint option Marray.t -> Float64.t option
    Marray.t -> uint option Marray.t -> uint -> ((Float64.t option
    Marray.t * uint option Marray.t) * Float64.t option Marray.t) * uint
    option Marray.t **)

let vedurspa =
  vedurspa_impl
