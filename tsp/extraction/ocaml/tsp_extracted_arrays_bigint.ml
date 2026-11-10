
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

(** val dal : (Bigint.t * Bigint.t) -> Bigint.t -> Bigint.t **)

let dal d e =
  Z.shiftl (fst d) (Z.sub (snd d) e)

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

(** val expo_step :
    Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t -> Bigint.t **)

let expo_step x y i e =
  Z.min e
    (Z.min (snd (fex ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x i)))
      (snd (fex ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y i))))

(** val grid_step :
    Float64.t array -> Float64.t array -> Bigint.t -> Uint63.t -> (Bigint.t
    array * Bigint.t array) -> Bigint.t array * Bigint.t array **)

let grid_step x y e i st =
  (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) (fst st) i
     (dal (fex ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x i)) e)),
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) (snd st) i
      (dal (fex ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y i)) e)))

(** val dz :
    Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t **)

let dz gX gY a b =
  let dx =
    Z.sub ((fun a i -> Array.unsafe_get a (Uint63.hash i)) gX a)
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) gX b)
  in
  let dy =
    Z.sub ((fun a i -> Array.unsafe_get a (Uint63.hash i)) gY a)
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) gY b)
  in
  Z.add (Z.mul dx dx) (Z.mul dy dy)

(** val key_init :
    Bigint.t array -> Bigint.t array -> Uint63.t -> Bigint.t array ->
    Bigint.t array **)

let key_init gX gY w k =
  (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) k w
    (dz gX gY (Uint63.of_int (0)) w)

(** val amin_step :
    Uint63.t -> Uint63.t array -> Bigint.t array -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let amin_step n rk k w b =
  if (&&) (eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) rk w) n)
       ((||) (eqb b n)
         (Z.ltb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) k w)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) k b)))
  then w
  else b

(** val relax_step :
    Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t array ->
    Uint63.t -> Uint63.t -> (Bigint.t array * Uint63.t array) -> Bigint.t
    array * Uint63.t array **)

let relax_step gX gY n rk v w st =
  if eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) rk w) n
  then let d = dz gX gY v w in
       if Z.ltb d ((fun a i -> Array.unsafe_get a (Uint63.hash i)) (fst st) w)
       then (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) 
               (fst st) w d),
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                (snd st) w v))
       else st
  else st

(** val prim_step :
    Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> ((Uint63.t
    array * Bigint.t array) * Uint63.t array) -> (Uint63.t array * Bigint.t
    array) * Uint63.t array **)

let prim_step gX gY n k st =
  let rk = fst (fst st) in
  let v =
    loop n (fun _ _ -> true) (amin_step n rk (snd (fst st)))
      (Uint63.of_int (0)) n
  in
  let rk' = (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) rk v k in
  let kP =
    loop n (fun _ _ -> true) (relax_step gX gY n rk' v) (Uint63.of_int (0))
      ((snd (fst st)), (snd st))
  in
  ((rk', (fst kP)), (snd kP))

type dS =
  (((Uint63.t array * Uint63.t array) * Uint63.t) * Uint63.t array) * Uint63.t

(** val ds_it : dS -> Uint63.t array **)

let ds_it s =
  fst (fst (fst (fst s)))

(** val ds_stk : dS -> Uint63.t array **)

let ds_stk s =
  snd (fst (fst (fst s)))

(** val ds_sp : dS -> Uint63.t **)

let ds_sp s =
  snd (fst (fst s))

(** val ds_out : dS -> Uint63.t array **)

let ds_out s =
  snd (fst s)

(** val ds_cnt : dS -> Uint63.t **)

let ds_cnt =
  snd

(** val dfs_step : Uint63.t -> Uint63.t array -> Uint63.t -> dS -> dS **)

let dfs_step n p _ s =
  let it = ds_it s in
  let stk = ds_stk s in
  let sp = ds_sp s in
  let out = ds_out s in
  let cnt = ds_cnt s in
  let u =
    (fun a i -> Array.unsafe_get a (Uint63.hash i)) stk
      (sub0 sp (Uint63.of_int (1)))
  in
  let c = (fun a i -> Array.unsafe_get a (Uint63.hash i)) it u in
  if ltb0 c n
  then let it' =
         (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) it u
           (add0 c (Uint63.of_int (1)))
       in
       if (&&) (eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) p c) u)
            (negb (eqb c (Uint63.of_int (0))))
       then ((((it',
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) stk sp
                c)),
              (add0 sp (Uint63.of_int (1)))),
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) out cnt
                c)),
              (add0 cnt (Uint63.of_int (1))))
       else ((((it', stk), sp), out), cnt)
  else ((((it, stk), (sub0 sp (Uint63.of_int (1)))), out), cnt)

(** val tsp_impl : Float64.t array -> Float64.t array -> Uint63.t array **)

let tsp_impl x y =
  let n = (fun a -> Uint63.of_int (Array.length a)) x in
  let e =
    loop n (fun _ _ -> true) (expo_step x y) (Uint63.of_int (0)) Bigint.zero
  in
  let g =
    loop n (fun _ _ -> true) (grid_step x y e) (Uint63.of_int (0))
      (((fun n d -> Array.make (Uint63.hash n) d) n Bigint.zero),
      ((fun n d -> Array.make (Uint63.hash n) d) n Bigint.zero))
  in
  let gX = fst g in
  let gY = snd g in
  let k0 =
    loop n (fun _ _ -> true) (key_init gX gY) (Uint63.of_int (0))
      ((fun n d -> Array.make (Uint63.hash n) d) n Bigint.zero)
  in
  let rk0 =
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
      ((fun n d -> Array.make (Uint63.hash n) d) n n) (Uint63.of_int (0))
      (Uint63.of_int (0))
  in
  let pR =
    loop n (fun _ _ -> true) (prim_step gX gY n) (Uint63.of_int (1)) ((rk0,
      k0), ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0))))
  in
  let s =
    loop (add0 (add0 (mul0 n n) n) (Uint63.of_int (1))) (fun _ s ->
      ltb0 (Uint63.of_int (0)) (ds_sp s)) (dfs_step n (snd pR))
      (Uint63.of_int (0))
      ((((((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0))),
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))),
      (Uint63.of_int (1))),
      ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)))),
      (Uint63.of_int (1)))
  in
  ds_out s

(** val tsp : Float64.t array -> Float64.t array -> uint array **)

let tsp =
  tsp_impl
