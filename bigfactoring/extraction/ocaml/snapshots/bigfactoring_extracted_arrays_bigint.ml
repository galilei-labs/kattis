
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

  (** val modulo : Bigint.t -> Bigint.t -> Bigint.t **)

  let modulo = Bigint.(fun x y ->
  match sign y with
  | 0 -> x
  | 1 -> erem x y
  | _ -> add y (add (of_int 1) (erem (add (of_int (-1)) x) y)))

  (** val even : Bigint.t -> bool **)

  let even z0 =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> true)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> false)
        (fun _ -> true)
        (fun _ -> false)
        p)
      z0

  (** val abs : Bigint.t -> Bigint.t **)

  let abs = Bigint.abs

  (** val odd : Bigint.t -> bool **)

  let odd z0 =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> false)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      (fun p ->
      (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> true)
        p)
      z0
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val zgcd : Bigint.t -> Bigint.t -> Bigint.t **)

let zgcd = Bigint.gcd

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val dguard : Bigint.t -> Bigint.t -> bool **)

let dguard m d =
  (&&) ((&&) (Z.ltb Bigint.one d) (Z.ltb Bigint.zero m))
    (Z.eqb (Z.modulo m d) Bigint.zero)

(** val guard : Bigint.t -> Bigint.t -> bool **)

let guard x m =
  (&&) (Z.leb Bigint.zero x) (Z.ltb x m)

(** val pm_loop : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t **)

let rec pm_loop b e m acc =
  if bdec (Z.ltb Bigint.zero e)
  then pm_loop (Z.modulo (Z.mul b b) m)
         (Z.div e ((fun x -> Bigint.shift_left x 1) Bigint.one)) m
         (if Z.odd e then Z.modulo (Z.mul acc b) m else acc)
  else Z.modulo acc m

(** val powmod : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t **)

let powmod b e m =
  pm_loop (Z.modulo b m) e m Bigint.one

(** val strip : Bigint.t -> Uint63.t -> Bigint.t * Uint63.t **)

let rec strip d s =
  if bdec (Z.ltb Bigint.zero d)
  then if Z.even d
       then strip (Z.div d ((fun x -> Bigint.shift_left x 1) Bigint.one))
              (add0 s (Uint63.of_int (1)))
       else (d, s)
  else (d, s)

(** val sq_loop : Bigint.t -> Bigint.t -> Uint63.t -> bool **)

let rec sq_loop n x k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let x0 = Z.modulo (Z.mul x x) n in
       if Z.eqb x0 (Z.sub n Bigint.one)
       then true
       else sq_loop n x0 (sub0 k (Uint63.of_int (1)))
  else false

(** val mr_base : Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t -> bool **)

let mr_base n d s a =
  let x = powmod a d n in
  if (||) (Z.eqb x Bigint.one) (Z.eqb x (Z.sub n Bigint.one))
  then true
  else sq_loop n x (sub0 s (Uint63.of_int (1)))

(** val miller_rabin : Bigint.t -> bool **)

let miller_rabin n =
  let (d, s) = strip (Z.sub n Bigint.one) (Uint63.of_int (0)) in
  (&&)
    ((&&)
      ((&&)
        ((&&)
          ((&&)
            ((&&)
              ((&&)
                ((&&)
                  ((&&)
                    ((&&)
                      ((&&)
                        (mr_base n d s ((fun x -> Bigint.shift_left x 1)
                          Bigint.one))
                        (mr_base n d s
                          ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                          Bigint.one)))
                      (mr_base n d s
                        ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                        ((fun x -> Bigint.shift_left x 1) Bigint.one))))
                    (mr_base n d s
                      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                      Bigint.one))))
                  (mr_base n d s
                    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                    ((fun x -> Bigint.shift_left x 1) Bigint.one)))))
                (mr_base n d s
                  ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                  ((fun x -> Bigint.shift_left x 1)
                  ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                  Bigint.one)))))
              (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                ((fun x -> Bigint.shift_left x 1)
                ((fun x -> Bigint.shift_left x 1)
                ((fun x -> Bigint.shift_left x 1) Bigint.one))))))
            (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
              ((fun x -> Bigint.succ (Bigint.shift_left x 1))
              ((fun x -> Bigint.shift_left x 1)
              ((fun x -> Bigint.shift_left x 1) Bigint.one))))))
          (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.shift_left x 1) Bigint.one))))))
        (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
          ((fun x -> Bigint.shift_left x 1)
          ((fun x -> Bigint.succ (Bigint.shift_left x 1))
          ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))
      (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
        ((fun x -> Bigint.succ (Bigint.shift_left x 1))
        ((fun x -> Bigint.succ (Bigint.shift_left x 1))
        ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one))))))
    (mr_base n d s ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1)
      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
      ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
      Bigint.one))))))

(** val rho_f : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t **)

let rho_f n c y =
  Z.modulo (Z.add (Z.mul y y) c) n

(** val rho_iter :
    Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t **)

let rec rho_iter n c y k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then rho_iter n c (rho_f n c y) (sub0 k (Uint63.of_int (1)))
  else y

(** val rho_batch :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t ->
    Bigint.t * Bigint.t **)

let rec rho_batch n c x y q k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let y0 = rho_f n c y in
       rho_batch n c x y0 (Z.modulo (Z.mul q (Z.abs (Z.sub x y0))) n)
         (sub0 k (Uint63.of_int (1)))
  else (y, q)

(** val rho_m : Uint63.t **)

let rho_m =
  (Uint63.of_int (128))

(** val rho_inner :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t ->
    Uint63.t -> ((Bigint.t * Bigint.t) * Bigint.t) * Bigint.t **)

let rec rho_inner n c x y q r k =
  if bdec ((&&) (ltb0 k r) (ltb0 k (add0 k rho_m)))
  then let t = if ltb0 (sub0 r k) rho_m then sub0 r k else rho_m in
       let (y', q') = rho_batch n c x y q t in
       let g = zgcd q' n in
       if Z.eqb g Bigint.one
       then rho_inner n c x y' q' r (add0 k rho_m)
       else (((g, y), y'), q')
  else (((Bigint.one, y), y), q)

(** val rho_rmax : Uint63.t **)

let rho_rmax =
  (Uint63.of_int (33554432))

(** val rho_back :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t **)

let rec rho_back n c x ys k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let ys0 = rho_f n c ys in
       let g = zgcd (Z.abs (Z.sub x ys0)) n in
       if Z.eqb g Bigint.one
       then rho_back n c x ys0 (sub0 k (Uint63.of_int (1)))
       else g
  else n

(** val rho_outer :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t **)

let rec rho_outer n c y q r =
  let y0 = rho_iter n c y r in
  let (p, q') = rho_inner n c y y0 q r (Uint63.of_int (0)) in
  let (p0, y') = p in
  let (g, ys) = p0 in
  if Z.eqb g Bigint.one
  then if bdec ((&&) (ltb0 r rho_rmax) (ltb0 r (mul0 r (Uint63.of_int (2)))))
       then rho_outer n c y' q' (mul0 r (Uint63.of_int (2)))
       else Bigint.zero
  else if Z.eqb g n
       then rho_back n c y ys (add0 rho_m (Uint63.of_int (1)))
       else g

(** val rho_try : Bigint.t -> Bigint.t -> Uint63.t -> Bigint.t **)

let rec rho_try n c k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let g =
         rho_outer n c ((fun x -> Bigint.shift_left x 1) Bigint.one)
           Bigint.one (Uint63.of_int (1))
       in
       if (&&) (Z.ltb Bigint.one g) (Z.ltb g n)
       then g
       else rho_try n (Z.add c Bigint.one) (sub0 k (Uint63.of_int (1)))
  else Bigint.zero

(** val rho : Bigint.t -> Bigint.t **)

let rho n =
  rho_try n Bigint.one (Uint63.of_int (20))

(** val cAP : Uint63.t **)

let cAP =
  (Uint63.of_int (128))

(** val push :
    Bigint.t array -> Uint63.t -> Bigint.t -> Bigint.t array * Uint63.t **)

let push acc cnt p =
  (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) acc cnt p),
    (add0 cnt (Uint63.of_int (1))))

(** val divout :
    Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t ->
    (Bigint.t * Bigint.t array) * Uint63.t **)

let rec divout m d acc cnt =
  if bdec (dguard m d)
  then let (acc', cnt') = push acc cnt d in divout (Z.div m d) d acc' cnt'
  else ((m, acc), cnt)

(** val trial :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t ->
    ((Bigint.t * Bigint.t) * Bigint.t array) * Uint63.t **)

let rec trial b m d acc cnt =
  if bdec (Z.ltb d b)
  then if Z.ltb m (Z.mul d d)
       then (((m, d), acc), cnt)
       else let (p, cnt') = divout m d acc cnt in
            let (m', acc') = p in trial b m' (Z.add d Bigint.one) acc' cnt'
  else (((m, d), acc), cnt)

(** val b0 : Bigint.t **)

let b0 =
  ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)))))))))

(** val fallback :
    Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t
    array * Uint63.t **)

let fallback m lo acc cnt =
  let (p, cnt') =
    trial (Z.add m ((fun x -> Bigint.shift_left x 1) Bigint.one)) m lo acc cnt
  in
  let (p0, acc') = p in
  let (r, _) = p0 in
  if Z.ltb Bigint.one r then push acc' cnt' r else (acc', cnt')

(** val all_q :
    Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Uint63.t -> bool **)

let rec all_q r a qs qc i =
  if bdec (ltb0 i qc)
  then let q = (fun a i -> Array.unsafe_get a (Uint63.hash i)) qs i in
       if (&&) (ltb0 (Uint63.of_int (0)) i)
            (Z.eqb q
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) qs
                (sub0 i (Uint63.of_int (1)))))
       then all_q r a qs qc (add0 i (Uint63.of_int (1)))
       else if Z.eqb
                 (zgcd
                   (Z.sub (powmod a (Z.div (Z.sub r Bigint.one) q) r)
                     Bigint.one)
                   r)
                 Bigint.one
            then all_q r a qs qc (add0 i (Uint63.of_int (1)))
            else false
  else true

(** val lucas_ok :
    Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> bool **)

let lucas_ok r a qs qc =
  (&&) (Z.eqb (powmod a (Z.sub r Bigint.one) r) Bigint.one)
    (all_q r a qs qc (Uint63.of_int (0)))

(** val cert_try :
    Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t -> Uint63.t -> bool **)

let rec cert_try r qs qc a k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then if lucas_ok r a qs qc
       then true
       else cert_try r qs qc (Z.add a Bigint.one) (sub0 k (Uint63.of_int (1)))
  else false

(** val certify : Bigint.t -> Bigint.t array -> Uint63.t -> bool **)

let certify r qs qc =
  cert_try r qs qc ((fun x -> Bigint.shift_left x 1) Bigint.one)
    (Uint63.of_int (1000))

(** val fac :
    Bigint.t -> Bigint.t -> Bigint.t array -> Uint63.t -> Bigint.t
    array * Uint63.t **)

let rec fac m lo acc cnt =
  let (p, cnt1) = trial b0 m lo acc cnt in
  let (p0, acc1) = p in
  let (r, d) = p0 in
  if Z.ltb r (Z.mul d d)
  then if Z.ltb Bigint.one r then push acc1 cnt1 r else (acc1, cnt1)
  else if miller_rabin r
       then if bdec (guard (Z.sub r Bigint.one) m)
            then let (qs, qc) =
                   fac (Z.sub r Bigint.one) ((fun x -> Bigint.shift_left x 1)
                     Bigint.one)
                     ((fun n d -> Array.make (Uint63.hash n) d) cAP
                       Bigint.zero)
                     (Uint63.of_int (0))
                 in
                 if certify r qs qc
                 then push acc1 cnt1 r
                 else fallback r d acc1 cnt1
            else fallback r d acc1 cnt1
       else let g = rho r in
            if (&&) ((&&) (Z.ltb Bigint.one g) (Z.ltb g r))
                 (Z.eqb (Z.modulo r g) Bigint.zero)
            then if bdec (guard g m)
                 then if bdec (guard (Z.div r g) m)
                      then let (acc2, cnt2) = fac g b0 acc1 cnt1 in
                           fac (Z.div r g) b0 acc2 cnt2
                      else fallback r d acc1 cnt1
                 else fallback r d acc1 cnt1
            else fallback r d acc1 cnt1

(** val copy :
    Bigint.t array -> Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t array **)

let rec copy src dst n i =
  if bdec (ltb0 i n)
  then copy src
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) dst i
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) src i))
         n (add0 i (Uint63.of_int (1)))
  else dst

(** val sink : Bigint.t array -> Uint63.t -> Bigint.t array **)

let rec sink a j =
  if bdec (ltb0 (Uint63.of_int (0)) j)
  then let x =
         (fun a i -> Array.unsafe_get a (Uint63.hash i)) a
           (sub0 j (Uint63.of_int (1)))
       in
       let y = (fun a i -> Array.unsafe_get a (Uint63.hash i)) a j in
       if Z.ltb y x
       then sink
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) a
                  (sub0 j (Uint63.of_int (1))) y)
                j x)
              (sub0 j (Uint63.of_int (1)))
       else a
  else a

(** val isort : Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t array **)

let rec isort a n i =
  if bdec (ltb0 i n)
  then isort (sink a i) n (add0 i (Uint63.of_int (1)))
  else a

(** val bigfactoring_impl : Bigint.t -> Bigint.t array **)

let bigfactoring_impl n =
  let (acc, cnt) =
    fac n ((fun x -> Bigint.shift_left x 1) Bigint.one)
      ((fun n d -> Array.make (Uint63.hash n) d) cAP Bigint.zero)
      (Uint63.of_int (0))
  in
  let out =
    copy acc ((fun n d -> Array.make (Uint63.hash n) d) cnt Bigint.zero) cnt
      (Uint63.of_int (0))
  in
  isort out cnt (Uint63.of_int (1))

(** val bigfactoring : Bigint.t -> Bigint.t array **)

let bigfactoring =
  bigfactoring_impl
