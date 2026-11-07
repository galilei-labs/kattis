
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

(** val ltb1 : Float64.t -> Float64.t -> bool **)

let ltb1 = Float64.lt

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

(** val fex : Float64.t -> z * z **)

let fex f =
  let (z0, e) = frshiftexp f in
  let m = zofi (normfr_mantissa z0) in
  ((if ltb1 f (Float64.of_float (0x0p+0)) then Z.opp m else m),
  (Z.sub (zofi e) (Zpos (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO
    XH))))))))))))))

(** val expo_step :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> z -> z **)

let expo_step x y i e =
  Z.min e (Z.min (snd (fex (get x i))) (snd (fex (get y i))))

(** val grid_step :
    Float64.t Marray.t -> Float64.t Marray.t -> z -> Uint63.t -> (z
    Marray.t * z Marray.t) -> z Marray.t * z Marray.t **)

let grid_step x y e i st =
  ((set (fst st) i (dal (fex (get x i)) e)),
    (set (snd st) i (dal (fex (get y i)) e)))

(** val dz : z Marray.t -> z Marray.t -> Uint63.t -> Uint63.t -> z **)

let dz gX gY a b =
  let dx = Z.sub (get gX a) (get gX b) in
  let dy = Z.sub (get gY a) (get gY b) in Z.add (Z.mul dx dx) (Z.mul dy dy)

(** val key_init :
    z Marray.t -> z Marray.t -> Uint63.t -> z Marray.t -> z Marray.t **)

let key_init gX gY w k =
  set k w (dz gX gY (Uint63.of_int (0)) w)

(** val amin_step :
    Uint63.t -> Uint63.t Marray.t -> z Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let amin_step n rk k w b =
  if (&&) (eqb (get rk w) n) ((||) (eqb b n) (Z.ltb (get k w) (get k b)))
  then w
  else b

(** val relax_step :
    z Marray.t -> z Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> (z Marray.t * Uint63.t Marray.t) -> z Marray.t * Uint63.t
    Marray.t **)

let relax_step gX gY n rk v w st =
  if eqb (get rk w) n
  then let d = dz gX gY v w in
       if Z.ltb d (get (fst st) w)
       then ((set (fst st) w d), (set (snd st) w v))
       else st
  else st

(** val prim_step :
    z Marray.t -> z Marray.t -> Uint63.t -> Uint63.t -> ((Uint63.t
    Marray.t * z Marray.t) * Uint63.t Marray.t) -> (Uint63.t Marray.t * z
    Marray.t) * Uint63.t Marray.t **)

let prim_step gX gY n k st =
  let rk = fst (fst st) in
  let v =
    loop n (fun _ _ -> true) (amin_step n rk (snd (fst st)))
      (Uint63.of_int (0)) n
  in
  let rk' = set rk v k in
  let kP =
    loop n (fun _ _ -> true) (relax_step gX gY n rk' v) (Uint63.of_int (0))
      ((snd (fst st)), (snd st))
  in
  ((rk', (fst kP)), (snd kP))

type dS =
  (((Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t) * Uint63.t
  Marray.t) * Uint63.t

(** val ds_it : dS -> Uint63.t Marray.t **)

let ds_it s =
  fst (fst (fst (fst s)))

(** val ds_stk : dS -> Uint63.t Marray.t **)

let ds_stk s =
  snd (fst (fst (fst s)))

(** val ds_sp : dS -> Uint63.t **)

let ds_sp s =
  snd (fst (fst s))

(** val ds_out : dS -> Uint63.t Marray.t **)

let ds_out s =
  snd (fst s)

(** val ds_cnt : dS -> Uint63.t **)

let ds_cnt =
  snd

(** val dfs_step : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> dS -> dS **)

let dfs_step n p _ s =
  let it = ds_it s in
  let stk = ds_stk s in
  let sp = ds_sp s in
  let out = ds_out s in
  let cnt = ds_cnt s in
  let u = get stk (sub0 sp (Uint63.of_int (1))) in
  let c = get it u in
  if ltb0 c n
  then let it' = set it u (add0 c (Uint63.of_int (1))) in
       if (&&) (eqb (get p c) u) (negb (eqb c (Uint63.of_int (0))))
       then ((((it', (set stk sp c)), (add0 sp (Uint63.of_int (1)))),
              (set out cnt c)), (add0 cnt (Uint63.of_int (1))))
       else ((((it', stk), sp), out), cnt)
  else ((((it, stk), (sub0 sp (Uint63.of_int (1)))), out), cnt)

(** val tsp_impl :
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t Marray.t **)

let tsp_impl x y =
  let n = length x in
  let e = loop n (fun _ _ -> true) (expo_step x y) (Uint63.of_int (0)) Z0 in
  let g =
    loop n (fun _ _ -> true) (grid_step x y e) (Uint63.of_int (0))
      ((make n Z0), (make n Z0))
  in
  let gX = fst g in
  let gY = snd g in
  let k0 =
    loop n (fun _ _ -> true) (key_init gX gY) (Uint63.of_int (0)) (make n Z0)
  in
  let rk0 = set (make n n) (Uint63.of_int (0)) (Uint63.of_int (0)) in
  let pR =
    loop n (fun _ _ -> true) (prim_step gX gY n) (Uint63.of_int (1)) ((rk0,
      k0), (make n (Uint63.of_int (0))))
  in
  let s =
    loop (add0 (add0 (mul0 n n) n) (Uint63.of_int (1))) (fun _ s ->
      ltb0 (Uint63.of_int (0)) (ds_sp s)) (dfs_step n (snd pR))
      (Uint63.of_int (0)) (((((make n (Uint63.of_int (0))),
      (make n (Uint63.of_int (0)))), (Uint63.of_int (1))),
      (make n (Uint63.of_int (0)))), (Uint63.of_int (1)))
  in
  ds_out s

module TspImpl =
 struct
  (** val tsp : Float64.t Marray.t -> Float64.t Marray.t -> uint Marray.t **)

  let tsp =
    tsp_impl
 end
