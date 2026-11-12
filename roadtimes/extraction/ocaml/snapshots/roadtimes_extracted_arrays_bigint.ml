
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

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



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
        (fun q0 -> (fun x -> Bigint.shift_left x 1)
        (add_carry p q0))
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q0))
        (fun _ -> (fun x -> Bigint.shift_left x 1) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q0))
        (fun q0 -> (fun x -> Bigint.shift_left x 1) (add p q0))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) p)
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.shift_left x 1) (succ q0))
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        q0)
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
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add_carry p q0))
        (fun q0 -> (fun x -> Bigint.shift_left x 1)
        (add_carry p q0))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.shift_left x 1)
        (add_carry p q0))
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q0))
        (fun _ -> (fun x -> Bigint.shift_left x 1) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (succ q0))
        (fun q0 -> (fun x -> Bigint.shift_left x 1) (succ q0))
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
        (fun q0 -> compare_cont r p q0)
        (fun q0 -> compare_cont Gt p q0)
        (fun _ -> Gt)
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> compare_cont Lt p q0)
        (fun q0 -> compare_cont r p q0)
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

  let rec eqb p q0 =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        (fun _ -> false)
        q0)
      (fun p0 ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun q1 -> eqb p0 q1)
        (fun _ -> false)
        q0)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun _ -> false)
        (fun _ -> true)
        q0)
      p
 end

module Coq_Pos =
 struct
  (** val succ : Bigint.t -> Bigint.t **)

  let rec succ = Bigint.succ

  (** val add : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec add = Bigint.add

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
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add_carry p q0))
        (fun q0 -> (fun x -> Bigint.shift_left x 1)
        (add_carry p q0))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) (succ p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.shift_left x 1)
        (add_carry p q0))
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (add p q0))
        (fun _ -> (fun x -> Bigint.shift_left x 1) (succ p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> (fun x -> Bigint.succ (Bigint.shift_left x 1))
        (succ q0))
        (fun q0 -> (fun x -> Bigint.shift_left x 1) (succ q0))
        (fun _ -> (fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
        y)
      x

  (** val mul : Bigint.t -> Bigint.t -> Bigint.t **)

  let rec mul = Bigint.mul
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
        (fun q0 -> double (pos_sub p q0))
        (fun q0 -> succ_double (pos_sub p q0))
        (fun _ -> ((fun x -> Bigint.shift_left x 1) p))
        y)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> pred_double (pos_sub p q0))
        (fun q0 -> double (pos_sub p q0))
        (fun _ -> (Pos.pred_double p))
        y)
      (fun _ ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun q0 -> Bigint.neg ((fun x -> Bigint.shift_left x 1)
        q0))
        (fun q0 -> Bigint.neg (Pos.pred_double q0))
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

  (** val to_pos : Bigint.t -> Bigint.t **)

  let to_pos z0 =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.one)
      (fun p -> p)
      (fun _ -> Bigint.one)
      z0

  (** val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t **)

  let rec pos_div_eucl a b =
    (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' =
        add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r) Bigint.one
      in
      if ltb r' b
      then ((mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q0), r')
      else ((add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q0)
              Bigint.one),
             (sub r' b)))
      (fun a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul ((fun x -> Bigint.shift_left x 1) Bigint.one) r in
      if ltb r' b
      then ((mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q0), r')
      else ((add (mul ((fun x -> Bigint.shift_left x 1) Bigint.one) q0)
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

  (** val modulo : Bigint.t -> Bigint.t -> Bigint.t **)

  let modulo = Bigint.(fun x y ->
  match sign y with
  | 0 -> x
  | 1 -> erem x y
  | _ -> add y (add (of_int 1) (erem (add (of_int (-1)) x) y)))

  (** val abs : Bigint.t -> Bigint.t **)

  let abs = Bigint.abs
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

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

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val div1 : Float64.t -> Float64.t -> Float64.t **)

let div1 = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

type q = { qnum : Bigint.t; qden : Bigint.t }

(** val inject_Z : Bigint.t -> q **)

let inject_Z x =
  { qnum = x; qden = Bigint.one }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum y.qden) (Z.mul y.qnum x.qden)); qden =
    (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> { qnum = Bigint.zero; qden = Bigint.one })
    (fun p -> { qnum = x.qden; qden = p })
    (fun p -> { qnum = (Bigint.neg x.qden); qden = p })
    x.qnum

type uint = Uint63.t

type sint = Uint63.t

(** val zgcd : Bigint.t -> Bigint.t -> Bigint.t **)

let zgcd = Bigint.gcd

(** val odec : 'a1 option -> 'a1 option **)

let odec = function
| Some x -> Some x
| None -> None

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

(** val forl :
    Uint63.t -> Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> 'a1 -> 'a1 **)

let forl lo hi f s =
  loop hi (fun _ _ -> true) f lo s

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

(** val zofs : Uint63.t -> Bigint.t **)

let zofs i =
  if ltb0 i (Uint63.of_int (-4611686018427387904))
  then zofi i
  else Z.sub (zofi i) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
         Bigint.one)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val iofz_rec : Bigint.t -> Uint63.t **)

let rec iofz_rec z0 =
  if bdec (Z.ltb Bigint.zero z0)
  then let r =
         iofz_rec (Z.div z0 ((fun x -> Bigint.shift_left x 1) Bigint.one))
       in
       if Z.eqb (Z.modulo z0 ((fun x -> Bigint.shift_left x 1) Bigint.one))
            Bigint.zero
       then add0 r r
       else add0 (add0 r r) (Uint63.of_int (1))
  else (Uint63.of_int (0))

(** val iofz : Bigint.t -> Uint63.t **)

let iofz =
  iofz_rec

(** val qred : q -> q **)

let qred q0 =
  let n = q0.qnum in
  let d = q0.qden in
  let g = zgcd n d in { qnum = (Z.div n g); qden = (Z.to_pos (Z.div d g)) }

(** val qsub : q -> q -> q **)

let qsub a b =
  qred (qminus a b)

(** val qmul : q -> q -> q **)

let qmul a b =
  qred (qmult a b)

(** val qltb : q -> q -> bool **)

let qltb a b =
  Z.ltb (Z.mul a.qnum b.qden) (Z.mul b.qnum a.qden)

(** val qzerob : q -> bool **)

let qzerob a =
  Z.eqb a.qnum Bigint.zero

type sState = (q array * q array) * Uint63.t array

(** val sT : sState -> q array **)

let sT st =
  fst (fst st)

(** val sO : sState -> q array **)

let sO st =
  snd (fst st)

(** val sB : sState -> Uint63.t array **)

let sB =
  snd

(** val lc : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let lc n e0 p =
  if eqb0 p (Uint63.of_int (0))
  then n
  else sub0 (add0 e0 p) (Uint63.of_int (1))

(** val enter : Uint63.t -> bool array -> q array -> Uint63.t option **)

let enter n al o =
  loop n (fun _ st -> match st with
                      | Some _ -> false
                      | None -> true)
    (fun j _ ->
    if (&&) ((fun a i -> Array.unsafe_get a (Uint63.hash i)) al j)
         (qltb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) o j) { qnum =
           Bigint.zero; qden = Bigint.one })
    then Some j
    else None) (Uint63.of_int (0)) None

(** val lexless :
    q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let lexless t w n e0 m k r s =
  let tks =
    (fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 k w) s)
  in
  let trs =
    (fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 r w) s)
  in
  let st =
    loop (add0 m (Uint63.of_int (1))) (fun _ st ->
      eqb0 st (Uint63.of_int (0))) (fun p _ ->
      let c = lc n e0 p in
      let a =
        qmult
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
            (add0 (mul0 k w) c))
          trs
      in
      let b =
        qmult
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
            (add0 (mul0 r w) c))
          tks
      in
      if qltb a b
      then (Uint63.of_int (1))
      else if qltb b a then (Uint63.of_int (2)) else (Uint63.of_int (0)))
      (Uint63.of_int (0)) (Uint63.of_int (0))
  in
  eqb0 st (Uint63.of_int (1))

(** val leave :
    q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t option **)

let leave t w n e0 m s =
  forl (Uint63.of_int (0)) m (fun k best ->
    if qltb { qnum = Bigint.zero; qden = Bigint.one }
         ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
           (add0 (mul0 k w) s))
    then (match best with
          | Some r -> if lexless t w n e0 m k r s then Some k else Some r
          | None -> Some k)
    else best) None

(** val scale_row : q array -> Uint63.t -> Uint63.t -> q -> q array **)

let scale_row t w r inv =
  forl (Uint63.of_int (0)) w (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 r w) j)
      (qmul
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
          (add0 (mul0 r w) j))
        inv))
    t

(** val elim_row :
    q array -> Uint63.t -> Uint63.t -> Uint63.t -> q -> q array **)

let elim_row t w r k f =
  forl (Uint63.of_int (0)) w (fun j t0 ->
    let a =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0 (add0 (mul0 r w) j)
    in
    if qzerob a
    then t0
    else (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
           (add0 (mul0 k w) j)
           (qsub
             ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
               (add0 (mul0 k w) j))
             (qmult f a)))
    t

(** val elim_all :
    q array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> q array **)

let elim_all t w m r s =
  forl (Uint63.of_int (0)) m (fun k t0 ->
    if eqb0 k r
    then t0
    else let f =
           (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
             (add0 (mul0 k w) s)
         in
         if qzerob f then t0 else elim_row t0 w r k f)
    t

(** val elim_obj :
    q array -> q array -> Uint63.t -> Uint63.t -> q -> q array **)

let elim_obj o t w r f =
  forl (Uint63.of_int (0)) w (fun j o0 ->
    let a =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 r w) j)
    in
    if qzerob a
    then o0
    else (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) o0 j
           (qsub ((fun a i -> Array.unsafe_get a (Uint63.hash i)) o0 j)
             (qmult f a)))
    o

(** val pivot :
    Uint63.t -> Uint63.t -> sState -> Uint63.t -> Uint63.t -> sState **)

let pivot w m st r s =
  let t = sT st in
  let o = sO st in
  let b = sB st in
  let t1 =
    scale_row t w r
      (qinv
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
          (add0 (mul0 r w) s)))
  in
  let t2 = elim_all t1 w m r s in
  let o2 =
    elim_obj o t2 w r ((fun a i -> Array.unsafe_get a (Uint63.hash i)) o s)
  in
  ((t2, o2), ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b r s))

(** val sloop : Uint63.t -> Uint63.t -> bool array -> sState -> sState **)

let rec sloop m e0 al st =
  match odec (enter (add0 e0 m) al (sO st)) with
  | Some s0 ->
    (match odec
             (leave (sT st) (add0 (add0 e0 m) (Uint63.of_int (1)))
               (add0 e0 m) e0 m s0) with
     | Some s1 ->
       sloop m e0 al (pivot (add0 (add0 e0 m) (Uint63.of_int (1))) m st s1 s0)
     | None -> st)
  | None -> st

(** val canon_obj :
    q array -> Uint63.t array -> q array -> Uint63.t -> Uint63.t -> q array **)

let canon_obj t b c w m =
  forl (Uint63.of_int (0)) m (fun k o ->
    let f =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) c
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) b k)
    in
    if qzerob f then o else elim_obj o t w k f) (Array.copy c)

(** val binit : Uint63.t -> Uint63.t -> Uint63.t array **)

let binit m e0 =
  forl (Uint63.of_int (0)) m (fun k b ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) b k (add0 e0 k))
    ((fun n d -> Array.make (Uint63.hash n) d) m (Uint63.of_int (0)))

(** val cart : Uint63.t -> Uint63.t -> Uint63.t -> q array **)

let cart w a0 n =
  forl a0 n (fun j c ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c j { qnum =
      Bigint.one; qden = Bigint.one })
    ((fun n d -> Array.make (Uint63.hash n) d) w { qnum = Bigint.zero; qden =
      Bigint.one })

(** val st0 : q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState **)

let st0 t0 m e0 a0 =
  let b0 = binit m e0 in
  ((t0,
  (canon_obj t0 b0
    (cart (add0 (add0 e0 m) (Uint63.of_int (1))) a0 (add0 e0 m))
    (add0 (add0 e0 m) (Uint63.of_int (1))) m)),
  b0)

(** val phase1 : q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState **)

let phase1 t0 m e0 a0 =
  sloop m e0 ((fun n d -> Array.make (Uint63.hash n) d) (add0 e0 m) true)
    (st0 t0 m e0 a0)

(** val al2 : q array -> Uint63.t -> Uint63.t -> bool array **)

let al2 o1 a0 n =
  forl (Uint63.of_int (0)) n (fun j a ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a j
      ((&&) (ltb0 j a0)
        (qzerob ((fun a i -> Array.unsafe_get a (Uint63.hash i)) o1 j))))
    ((fun n d -> Array.make (Uint63.hash n) d) n false)

(** val mk2 : sState -> q array -> Uint63.t -> Uint63.t -> sState **)

let mk2 st1 carr w m =
  (((Array.copy (sT st1)), (canon_obj (sT st1) (sB st1) carr w m)),
    (Array.copy (sB st1)))

(** val phase2 :
    q array -> Uint63.t -> Uint63.t -> Uint63.t -> sState -> bool array -> q
    array -> q **)

let phase2 _ m e0 _ st1 al carr =
  if bdec
       ((&&)
         (eqb0 ((fun a -> Uint63.of_int (Array.length a)) carr)
           (add0 (add0 e0 m) (Uint63.of_int (1))))
         (qzerob
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) carr (add0 e0 m))))
  then let st3 =
         sloop m e0 al (mk2 st1 carr (add0 (add0 e0 m) (Uint63.of_int (1))) m)
       in
       qopp
         ((fun a i -> Array.unsafe_get a (Uint63.hash i)) (sO st3)
           (add0 e0 m))
  else { qnum = Bigint.zero; qden = Bigint.one }

(** val fill2 :
    Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t array ->
    Uint63.t array **)

let fill2 n g a =
  forl (Uint63.of_int (0)) n (fun i a0 ->
    forl (Uint63.of_int (0)) n (fun j a1 ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a1
        (add0 (mul0 i n) j) (g i j))
      a0)
    a

(** val flatten : Uint63.t -> Uint63.t array array -> Uint63.t array **)

let flatten n x =
  fill2 n (fun i j ->
    (fun a i -> Array.unsafe_get a (Uint63.hash i))
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x i) j)
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) (Uint63.of_int (0)))

(** val isroad : Uint63.t -> bool **)

let isroad e =
  ltsb (Uint63.of_int (0)) e

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (1073741824))

(** val fw_cell :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
    array * Uint63.t array) -> Uint63.t array * Uint63.t array **)

let fw_cell n k i j st =
  let d = fst st in
  let x = snd st in
  let a =
    add0
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d (add0 (mul0 i n) k))
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d (add0 (mul0 k n) j))
  in
  if ltb0 a
       ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d (add0 (mul0 i n) j))
  then (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) d
          (add0 (mul0 i n) j) a),
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) x
           (add0 (mul0 i n) j)
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x
             (add0 (mul0 i n) k))))
  else st

(** val fw_iter :
    Uint63.t -> Uint63.t -> (Uint63.t array * Uint63.t array) -> Uint63.t
    array * Uint63.t array **)

let fw_iter n k st =
  forl (Uint63.of_int (0)) n (fun i st1 ->
    forl (Uint63.of_int (0)) n (fun j st2 -> fw_cell n k i j st2) st1) st

(** val fw : Uint63.t -> Uint63.t array -> Uint63.t array * Uint63.t array **)

let fw n w =
  let d0 =
    fill2 n (fun i j ->
      if eqb0 i j
      then (Uint63.of_int (0))
      else if isroad
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w
                  (add0 (mul0 i n) j))
           then (fun a i -> Array.unsafe_get a (Uint63.hash i)) w
                  (add0 (mul0 i n) j)
           else iNF)
      ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n)
        (Uint63.of_int (0)))
  in
  let x0 =
    fill2 n (fun _ j -> j)
      ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n)
        (Uint63.of_int (0)))
  in
  forl (Uint63.of_int (0)) n (fun k st -> fw_iter n k st) (d0, x0)

(** val scan_roads :
    Uint63.t -> Uint63.t array -> (Uint63.t array * Uint63.t array) * Uint63.t **)

let scan_roads n w =
  forl (Uint63.of_int (0)) (mul0 n n) (fun p st ->
    let i = fst (fst st) in
    let p0 = snd (fst st) in
    let e = snd st in
    if isroad ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w p)
    then ((((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) i p e),
           ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) p0 e p)),
           (add0 e (Uint63.of_int (1))))
    else st)
    ((((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n)
        (Uint63.of_int (0))),
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) (Uint63.of_int (0)))),
    (Uint63.of_int (0)))

(** val walk :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let rec walk n d e d0 x i cur cnt =
  if eqb0 cur d
  then cnt
  else let v =
         (fun a i -> Array.unsafe_get a (Uint63.hash i)) x
           (add0 (mul0 cur n) d)
       in
       if bdec
            (ltb0
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d0
                (add0 (mul0 v n) d))
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d0
                (add0 (mul0 cur n) d)))
       then let e0 =
              (fun a i -> Array.unsafe_get a (Uint63.hash i)) i
                (add0 (mul0 cur n) v)
            in
            walk n d e d0 x i v
              (if ltb0 e0 e
               then (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                      cnt e0
                      (add0
                        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt
                          e0)
                        (Uint63.of_int (1)))
               else cnt)
       else cnt

(** val route_cnt :
    Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t
    array -> Uint63.t -> Uint63.t -> Uint63.t array **)

let route_cnt n e d x i s d0 =
  walk n d0 e d x i s
    ((fun n d -> Array.make (Uint63.hash n) d) e (Uint63.of_int (0)))

(** val bound_rows :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array -> q
    array -> q array **)

let bound_rows e w n w0 p t =
  forl (Uint63.of_int (0)) e (fun e0 t0 ->
    let u =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) w0
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) p e0)
    in
    let t1 =
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 e0 w) e0) { qnum = Bigint.one; qden = Bigint.one }
    in
    let t2 =
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t1
        (add0 (mul0 e0 w) (add0 e e0)) { qnum = Bigint.one; qden =
        Bigint.one }
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t2
      (add0 (mul0 e0 w) n)
      (if isroad u
       then inject_Z (zofs u)
       else { qnum = Bigint.zero; qden = Bigint.one }))
    t

(** val deliv_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array ->
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> Uint63.t -> q array -> q array **)

let deliv_row n e w n0 d x i rs rd rt k t =
  let s = (fun a i -> Array.unsafe_get a (Uint63.hash i)) rs k in
  let d0 = (fun a i -> Array.unsafe_get a (Uint63.hash i)) rd k in
  let cnt = route_cnt n e d x i s d0 in
  let b =
    Z.sub (zofi ((fun a i -> Array.unsafe_get a (Uint63.hash i)) rt k))
      (zofi
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d
          (add0 (mul0 s n) d0)))
  in
  let i0 = add0 e k in
  let t0 =
    forl (Uint63.of_int (0)) e (fun e0 t0 ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 i0 w) e0)
        (inject_Z
          (if Z.ltb b Bigint.zero
           then Z.opp
                  (zofi
                    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt e0))
           else zofi ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt e0))))
      t
  in
  let t1 =
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i0 w) (add0 (add0 e e) k)) { qnum = Bigint.one; qden =
      Bigint.one }
  in
  (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t1
    (add0 (mul0 i0 w) n0) (inject_Z (Z.abs b))

(** val build_T :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> Uint63.t array -> q array **)

let build_T n e r w d x i p rs rd rt =
  let m = add0 e r in
  let w0 = add0 (add0 e m) (Uint63.of_int (1)) in
  let n0 = add0 e m in
  let t =
    bound_rows e w0 n0 w p
      ((fun n d -> Array.make (Uint63.hash n) d) (mul0 m w0) { qnum =
        Bigint.zero; qden = Bigint.one })
  in
  forl (Uint63.of_int (0)) r (fun k t0 ->
    deliv_row n e w0 n0 d x i rs rd rt k t0) t

(** val guard : Uint63.t -> Uint63.t -> bool **)

let guard e r =
  (&&)
    ((&&)
      ((&&) (leb0 (Uint63.of_int (1)) (add0 e r))
        (leb0 e (Uint63.of_int (2048))))
      (leb0 r (Uint63.of_int (2048))))
    (leb0 (mul0 (add0 e r) (add0 (add0 e (add0 e r)) (Uint63.of_int (1))))
      (Uint63.of_int (4194303)))

(** val qcost : Uint63.t -> Uint63.t -> Uint63.t array -> bool -> q array **)

let qcost e w cnt neg =
  forl (Uint63.of_int (0)) e (fun e0 c ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c e0
      (inject_Z
        (if neg
         then Z.opp
                (zofi
                  ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt e0))
         else zofi ((fun a i -> Array.unsafe_get a (Uint63.hash i)) cnt e0))))
    ((fun n d -> Array.make (Uint63.hash n) d) w { qnum = Bigint.zero; qden =
      Bigint.one })

(** val two36 : Uint63.t **)

let two36 =
  (Uint63.of_int (68719476736))

(** val q2f : q -> Float64.t **)

let q2f q0 =
  let mz =
    Z.div
      (Z.mul q0.qnum ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
        ((fun x -> Bigint.shift_left x 1)
        Bigint.one)))))))))))))))))))))))))))))))))))))
      q0.qden
  in
  div1 (of_uint63 (iofz mz)) (of_uint63 two36)

(** val aget : Uint63.t array -> Uint63.t -> Uint63.t **)

let aget =
  (fun a i -> Array.unsafe_get a (Uint63.hash i))

(** val dq : Uint63.t -> Uint63.t array -> Uint63.t -> Uint63.t -> q **)

let dq n d s d0 =
  inject_Z
    (zofi
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) d (add0 (mul0 s n) d0)))

(** val vq :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> q array -> sState -> bool array -> Uint63.t -> Uint63.t
    -> bool -> q **)

let vq n e rR d x i t0 st1 al s d0 neg =
  phase2 t0 (add0 e rR) e (add0 e e) st1 al
    (qcost e (add0 (add0 e (add0 e rR)) (Uint63.of_int (1)))
      (route_cnt n e d x i s d0) neg)

(** val qans :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> q array -> sState -> bool array -> Uint63.t -> Uint63.t
    -> Float64.t * Float64.t **)

let qans n e rR d x i t0 st1 al s d0 =
  ((q2f (qplus (dq n d s d0) (vq n e rR d x i t0 st1 al s d0 false))),
    (q2f (qminus (dq n d s d0) (vq n e rR d x i t0 st1 al s d0 true))))

(** val answers :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> q array -> Uint63.t array -> Uint63.t array ->
    (Float64.t * Float64.t) array **)

let answers n e rR d x i t0 xqs xqd =
  let st1 = phase1 t0 (add0 e rR) e (add0 e e) in
  let al = al2 (sO st1) (add0 e e) (add0 e (add0 e rR)) in
  forl (Uint63.of_int (0)) ((fun a -> Uint63.of_int (Array.length a)) xqs)
    (fun j out ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) out j
      (qans n e rR d x i t0 st1 al (aget xqs j) (aget xqd j)))
    ((fun n d -> Array.make (Uint63.hash n) d)
      ((fun a -> Uint63.of_int (Array.length a)) xqs) (zero, zero))

(** val roadtimes_impl :
    sint array array -> uint array -> uint array -> uint array -> uint array
    -> uint array -> (Float64.t * Float64.t) array **)

let roadtimes_impl xdist xrs xrd xrt xqs xqd =
  let n = (fun a -> Uint63.of_int (Array.length a)) xdist in
  let w = flatten n xdist in
  let fW = fw n w in
  let d = fst fW in
  let x = snd fW in
  let sR = scan_roads n w in
  let i = fst (fst sR) in
  let p = snd (fst sR) in
  let e = snd sR in
  let rR = (fun a -> Uint63.of_int (Array.length a)) xrs in
  if bdec (guard e rR)
  then let t0 = build_T n e rR w d x i p xrs xrd xrt in
       answers n e rR d x i t0 xqs xqd
  else (fun n d -> Array.make (Uint63.hash n) d)
         ((fun a -> Uint63.of_int (Array.length a)) xqs) (zero, zero)

(** val roadtimes :
    sint array array -> uint array -> uint array -> uint array -> uint array
    -> uint array -> (Float64.t * Float64.t) array **)

let roadtimes =
  roadtimes_impl
