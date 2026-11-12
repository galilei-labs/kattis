
(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  if b1 then if b2 then false else true else b2

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

  let add x y =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> y)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> x)
        (fun y' -> (Pos.add x' y'))
        (fun y' -> pos_sub x' y')
        y)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> x)
        (fun y' -> pos_sub y' x')
        (fun y' -> Bigint.neg (Pos.add x' y'))
        y)
      x

  (** val opp : Bigint.t -> Bigint.t **)

  let opp x =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.zero)
      (fun x0 -> Bigint.neg x0)
      (fun x0 -> x0)
      x

  (** val sub : Bigint.t -> Bigint.t -> Bigint.t **)

  let sub m n =
    add m (opp n)

  (** val mul : Bigint.t -> Bigint.t -> Bigint.t **)

  let mul x y =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> Bigint.zero)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> Bigint.zero)
        (fun y' -> (Pos.mul x' y'))
        (fun y' -> Bigint.neg (Pos.mul x' y'))
        y)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> Bigint.zero)
        (fun y' -> Bigint.neg (Pos.mul x' y'))
        (fun y' -> (Pos.mul x' y'))
        y)
      x

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare x y =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> Eq)
        (fun _ -> Lt)
        (fun _ -> Gt)
        y)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> Gt)
        (fun y' -> Pos.compare x' y')
        (fun _ -> Gt)
        y)
      (fun x' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> Lt)
        (fun _ -> Lt)
        (fun y' -> compOpp (Pos.compare x' y'))
        y)
      x

  (** val leb : Bigint.t -> Bigint.t -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> false
    | _ -> true

  (** val ltb : Bigint.t -> Bigint.t -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> true
    | _ -> false

  (** val eqb : Bigint.t -> Bigint.t -> bool **)

  let eqb x y =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> true)
        (fun _ -> false)
        (fun _ -> false)
        y)
      (fun p ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        (fun _ -> false)
        y)
      (fun p ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> false)
        (fun _ -> false)
        (fun q -> Pos.eqb p q)
        y)
      x

  (** val max : Bigint.t -> Bigint.t -> Bigint.t **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : Bigint.t -> Bigint.t -> Bigint.t **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

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

  let div_eucl a b =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> (Bigint.zero, Bigint.zero))
      (fun a' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> (Bigint.zero, a))
        (fun _ -> pos_div_eucl a' b)
        (fun b' ->
        let (q, r) = pos_div_eucl a' b' in
        ((fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
           (fun _ -> ((opp q), Bigint.zero))
           (fun _ -> ((opp (add q Bigint.one)), (add b r)))
           (fun _ -> ((opp (add q Bigint.one)), (add b r)))
           r))
        b)
      (fun a' ->
      (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
        (fun _ -> (Bigint.zero, a))
        (fun _ ->
        let (q, r) = pos_div_eucl a' b in
        ((fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
           (fun _ -> ((opp q), Bigint.zero))
           (fun _ -> ((opp (add q Bigint.one)), (sub b r)))
           (fun _ -> ((opp (add q Bigint.one)), (sub b r)))
           r))
        (fun b' -> let (q, r) = pos_div_eucl a' b' in (q, (opp r)))
        b)
      a

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

  let shiftl a n =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> a)
      (fun p ->
      Pos.iter (mul ((fun x -> Bigint.shift_left x 1) Bigint.one)) a p)
      (fun p -> Pos.iter div2 a p)
      n
 end

module Coq_Z =
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

  (** val modulo : Bigint.t -> Bigint.t -> Bigint.t **)

  let modulo = Bigint.(fun x y ->
  match sign y with
  | 0 -> x
  | 1 -> erem x y
  | _ -> add y (add (of_int 1) (erem (add (of_int (-1)) x) y)))

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

  (** val abs : Bigint.t -> Bigint.t **)

  let abs = Bigint.abs
 end

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

(** val to_Z : Uint63.t -> Bigint.t **)

let to_Z = Bigint.of_uint63

(** val of_Z : Bigint.t -> Uint63.t **)

let of_Z = Bigint.to_uint63

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

(** val is_zero : Float64.t -> bool **)

let is_zero f =
  eqb1 f zero

(** val is_infinity : Float64.t -> bool **)

let is_infinity f =
  eqb1 (abs0 f) infinity

(** val is_finite : Float64.t -> bool **)

let is_finite x =
  negb ((||) (is_nan x) (is_infinity x))

(** val get_sign : Float64.t -> bool **)

let get_sign f =
  let f0 = if is_zero f then div0 one f else f in ltb1 f0 zero

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * Bigint.t * Bigint.t

(** val emin : Bigint.t -> Bigint.t -> Bigint.t **)

let emin prec0 emax0 =
  Z.sub
    (Z.sub ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one) emax0)
    prec0

(** val fexp : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t **)

let fexp prec0 emax0 e =
  Z.max (Z.sub e prec0) (emin prec0 emax0)

(** val digits2_pos : Bigint.t -> Bigint.t **)

let rec digits2_pos n =
  (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
    (fun p -> Pos.succ (digits2_pos p))
    (fun p -> Pos.succ (digits2_pos p))
    (fun _ -> Bigint.one)
    n

(** val zdigits2 : Bigint.t -> Bigint.t **)

let zdigits2 n =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> n)
    (fun p -> (digits2_pos p))
    (fun p -> (digits2_pos p))
    n

(** val iter_pos : ('a1 -> 'a1) -> Bigint.t -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
    (fun n' -> iter_pos f n' (iter_pos f n' (f x)))
    (fun n' -> iter_pos f n' (iter_pos f n' x))
    (fun _ -> f x)
    n

type location =
| Loc_Exact
| Loc_Inexact of comparison

type shr_record = { shr_m : Bigint.t; shr_r : bool; shr_s : bool }

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = (||) r s in
  ((fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
     (fun _ -> { shr_m = Bigint.zero; shr_r = false; shr_s = s0 })
     (fun p0 ->
     (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
       (fun p -> { shr_m = p; shr_r = true; shr_s = s0 })
       (fun p -> { shr_m = p; shr_r = false; shr_s = s0 })
       (fun _ -> { shr_m = Bigint.zero; shr_r = true; shr_s = s0 })
       p0)
     (fun p0 ->
     (fun f2p1 f2p f1 p ->
  if Bigint.le p Bigint.one then f1 () else
  let q = Bigint.shift_right p 1 in
  if Bigint.testbit p 0 then f2p1 q else f2p q)
       (fun p -> { shr_m = (Bigint.neg p); shr_r = true; shr_s =
       s0 })
       (fun p -> { shr_m = (Bigint.neg p); shr_r = false; shr_s =
       s0 })
       (fun _ -> { shr_m = Bigint.zero; shr_r = true; shr_s = s0 })
       p0)
     m)

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  if shr_r0
  then if shr_s0 then Loc_Inexact Gt else Loc_Inexact Eq
  else if shr_s0 then Loc_Inexact Lt else Loc_Exact

(** val shr_record_of_loc : Bigint.t -> location -> shr_record **)

let shr_record_of_loc m = function
| Loc_Exact -> { shr_m = m; shr_r = false; shr_s = false }
| Loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = true; shr_s = false }
   | Lt -> { shr_m = m; shr_r = false; shr_s = true }
   | Gt -> { shr_m = m; shr_r = true; shr_s = true })

(** val shr : shr_record -> Bigint.t -> Bigint.t -> shr_record * Bigint.t **)

let shr mrs e n =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> (mrs, e))
    (fun p -> ((iter_pos shr_1 p mrs), (Z.add e n)))
    (fun _ -> (mrs, e))
    n

(** val shr_fexp :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> location ->
    shr_record * Bigint.t **)

let shr_fexp prec0 emax0 m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec0 emax0 (Z.add (zdigits2 m) e)) e)

(** val round_nearest_even : Bigint.t -> location -> Bigint.t **)

let round_nearest_even mx = function
| Loc_Exact -> mx
| Loc_Inexact c ->
  (match c with
   | Eq -> if Z.even mx then mx else Z.add mx Bigint.one
   | Lt -> mx
   | Gt -> Z.add mx Bigint.one)

(** val binary_round_aux :
    Bigint.t -> Bigint.t -> bool -> Bigint.t -> Bigint.t -> location ->
    spec_float **)

let binary_round_aux prec0 emax0 sx mx ex lx =
  let (mrs', e') = shr_fexp prec0 emax0 mx ex lx in
  let (mrs'', e'') =
    shr_fexp prec0 emax0
      (round_nearest_even mrs'.shr_m (loc_of_shr_record mrs')) e' Loc_Exact
  in
  ((fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
     (fun _ -> S754_zero sx)
     (fun m ->
     if Z.leb e'' (Z.sub emax0 prec0)
     then S754_finite (sx, m, e'')
     else S754_infinity sx)
     (fun _ -> S754_nan)
     mrs''.shr_m)

(** val new_location_even : Bigint.t -> Bigint.t -> location **)

let new_location_even nb_steps k =
  if Z.eqb k Bigint.zero
  then Loc_Exact
  else Loc_Inexact
         (Z.compare (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) k)
           nb_steps)

(** val new_location_odd : Bigint.t -> Bigint.t -> location **)

let new_location_odd nb_steps k =
  if Z.eqb k Bigint.zero
  then Loc_Exact
  else Loc_Inexact
         (match Z.compare
                  (Z.add
                    (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one) k)
                    Bigint.one)
                  nb_steps with
          | Eq -> Lt
          | x -> x)

(** val new_location : Bigint.t -> Bigint.t -> location **)

let new_location nb_steps =
  if Z.even nb_steps
  then new_location_even nb_steps
  else new_location_odd nb_steps

(** val sFdiv_core_binary :
    Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t ->
    (Bigint.t * Bigint.t) * location **)

let sFdiv_core_binary prec0 emax0 m1 e1 m2 e2 =
  let d2 = zdigits2 m1 in
  let d3 = zdigits2 m2 in
  let e' =
    Z.min (fexp prec0 emax0 (Z.sub (Z.add d2 e1) (Z.add d3 e2))) (Z.sub e1 e2)
  in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' =
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> m1)
      (fun _ -> Z.shiftl m1 s)
      (fun _ -> Bigint.zero)
      s
  in
  let (q, r) = Z.div_eucl m' m2 in ((q, e'), (new_location m2 r))

(** val prec : Bigint.t **)

let prec =
  ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)))))

(** val emax : Bigint.t **)

let emax =
  ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    Bigint.one))))))))))

(** val shift : Bigint.t **)

let shift =
  ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) Bigint.one)))))))))))

type uint = Uint63.t

type 'v outcome =
| Unique of 'v
| Multiple
| Inconsistent

(** val zgcd : Bigint.t -> Bigint.t -> Bigint.t **)

let zgcd = Bigint.gcd

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

(** val i2z : Uint63.t -> Bigint.t **)

let i2z =
  to_Z

(** val z2i : Bigint.t -> Uint63.t **)

let z2i =
  of_Z

(** val ldexp' : Float64.t -> Bigint.t -> Float64.t **)

let ldexp' f e =
  let e' =
    Coq_Z.max (Coq_Z.min e (Coq_Z.sub emax (emin prec emax)))
      (Coq_Z.sub (Coq_Z.sub (emin prec emax) emax) Bigint.one)
  in
  ldshiftexp f (z2i (Coq_Z.add e' shift))

(** val sF2Prim' : spec_float -> Float64.t **)

let sF2Prim' = function
| S754_zero s -> if s then neg_zero else zero
| S754_infinity s -> if s then neg_infinity else infinity
| S754_nan -> nan
| S754_finite (s, m, e) ->
  let pm = of_uint63 (z2i m) in let f = ldexp' pm e in if s then opp0 f else f

(** val dec : Float64.t -> Bigint.t * Bigint.t **)

let dec f =
  if is_nan f
  then (Bigint.zero, Bigint.zero)
  else if is_zero f
       then (Bigint.zero, Bigint.zero)
       else if is_infinity f
            then (Bigint.zero, Bigint.zero)
            else let (r, e) = frshiftexp f in
                 let m = to_Z (normfr_mantissa r) in
                 ((if get_sign f then Coq_Z.opp m else m),
                 (Coq_Z.sub (Coq_Z.sub (to_Z e) shift) prec))

(** val scale : Float64.t -> Bigint.t -> Bigint.t **)

let scale f e =
  Coq_Z.shiftl (fst (dec f)) (Coq_Z.sub (snd (dec f)) e)

(** val qr : bool -> Bigint.t -> bool -> Bigint.t -> Float64.t **)

let qr sx mx sy my =
  let (p, lz) = sFdiv_core_binary prec emax mx Bigint.zero my Bigint.zero in
  let (mz, ez) = p in
  (match binary_round_aux prec emax (xorb sx sy) mz ez lz with
   | S754_finite (s, m, e) -> sF2Prim' (S754_finite (s, m, e))
   | _ -> zero)

(** val qround : Bigint.t -> Bigint.t -> Float64.t **)

let qround num den =
  (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
    (fun _ -> zero)
    (fun mx ->
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> zero)
      (fun my -> qr false mx false my)
      (fun my -> qr false mx true my)
      den)
    (fun mx ->
    (fun fz fp fn z -> let s = Bigint.sign z in
  if s = 0 then fz () else if s > 0 then fp z
  else fn (Bigint.neg z))
      (fun _ -> zero)
      (fun my -> qr true mx false my)
      (fun my -> qr true mx true my)
      den)
    num

(** val row_exp : Uint63.t -> Float64.t array -> Float64.t -> Bigint.t **)

let row_exp n row bi =
  loop n (fun _ _ -> true) (fun j e ->
    Coq_Z.min e
      (snd (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j))))
    (Uint63.of_int (0)) (Coq_Z.min Bigint.zero (snd (dec bi)))

(** val fill_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array -> Bigint.t ->
    Bigint.t array -> Bigint.t array **)

let fill_row n w i row e t =
  loop n (fun _ _ -> true) (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i w) j)
      (scale ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j) e))
    (Uint63.of_int (0)) t

(** val build_step :
    Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
    Uint63.t -> Bigint.t array -> Bigint.t array **)

let build_step a b n w i t =
  let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) a i in
  let bi = (fun a i -> Array.unsafe_get a (Uint63.hash i)) b i in
  let e = row_exp n row bi in
  let t0 = fill_row n w i row e t in
  (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
    (add0 (mul0 i w) n) (scale bi e)

(** val build :
    Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
    Bigint.t array **)

let build a b n w =
  loop n (fun _ _ -> true) (build_step a b n w) (Uint63.of_int (0))
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n w) Bigint.zero)

(** val find_piv :
    Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let find_piv t n w c r =
  loop n (fun _ _ -> true) (fun i s ->
    if eqb0 s n
    then if Coq_Z.eqb
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
                (add0 (mul0 i w) c))
              Bigint.zero
         then s
         else i
    else s) r n

(** val swap_rows :
    Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array **)

let swap_rows t w q r =
  loop w (fun _ _ -> true) (fun j t0 ->
    let x =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0 (add0 (mul0 r w) j)
    in
    let y =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0 (add0 (mul0 q w) j)
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 r w) j) y)
      (add0 (mul0 q w) j) x)
    (Uint63.of_int (0)) t

(** val upd_row :
    Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t ->
    Bigint.t -> Bigint.t array **)

let upd_row t w i r a b =
  loop w (fun _ _ -> true) (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i w) j)
      (Coq_Z.sub
        (Coq_Z.mul a
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
            (add0 (mul0 i w) j)))
        (Coq_Z.mul b
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
            (add0 (mul0 r w) j)))))
    (Uint63.of_int (0)) t

(** val row_gcd : Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t **)

let row_gcd t w i =
  loop w (fun _ _ -> true) (fun j g ->
    zgcd g
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 i w) j)))
    (Uint63.of_int (0)) Bigint.zero

(** val div_row :
    Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t array **)

let div_row t w i g =
  loop w (fun _ _ -> true) (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i w) j)
      (Coq_Z.div
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
          (add0 (mul0 i w) j))
        g))
    (Uint63.of_int (0)) t

(** val elim_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t -> Uint63.t -> Bigint.t
    array -> Bigint.t array **)

let elim_row w c r a i t =
  if eqb0 i r
  then t
  else let b =
         (fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 i w) c)
       in
       if Coq_Z.eqb b Bigint.zero
       then t
       else let t0 = upd_row t w i r a b in
            let g = row_gcd t0 w i in
            if Coq_Z.ltb Bigint.one g then div_row t0 w i g else t0

(** val col_step :
    Uint63.t -> Uint63.t -> Uint63.t -> (Bigint.t array * Uint63.t) ->
    Bigint.t array * Uint63.t **)

let col_step n w c = function
| (t, r) ->
  let q = find_piv t n w c r in
  if eqb0 q n
  then (t, r)
  else let t0 = swap_rows t w q r in
       let a =
         (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
           (add0 (mul0 r w) c)
       in
       ((loop n (fun _ _ -> true) (elim_row w c r a) (Uint63.of_int (0)) t0),
       (add0 r (Uint63.of_int (1))))

(** val eliminate :
    Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array * Uint63.t **)

let eliminate n w t =
  loop n (fun _ _ -> true) (col_step n w) (Uint63.of_int (0)) (t,
    (Uint63.of_int (0)))

(** val inconsistent :
    Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let inconsistent t n w r =
  loop n (fun _ _ -> true) (fun i fl ->
    (||) fl
      (negb
        (Coq_Z.eqb
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
            (add0 (mul0 i w) n))
          Bigint.zero)))
    r false

(** val output : Bigint.t array -> Uint63.t -> Uint63.t -> Float64.t array **)

let output t n w =
  loop n (fun _ _ -> true) (fun i out ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) out i
      (qround
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
          (add0 (mul0 i w) n))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
          (add0 (mul0 i w) i))))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n zero)

(** val solve_exact :
    uint -> Float64.t array array -> Float64.t array -> Float64.t array
    outcome **)

let solve_exact n a b =
  let w = add0 n (Uint63.of_int (1)) in
  let t = build a b n w in
  let (t0, r) = eliminate n w t in
  if inconsistent t0 n w r
  then Inconsistent
  else if ltb0 r n then Multiple else Unique (output t0 n w)

(** val fdot :
    Float64.t array -> Uint63.t -> Float64.t array -> Uint63.t -> Uint63.t ->
    Float64.t **)

let fdot x ox y oy len =
  loop len (fun _ _ -> true) (fun k s ->
    add1 s
      (mul1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x (add0 ox k))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y (add0 oy k))))
    (Uint63.of_int (0)) zero

type dy = Bigint.t * Bigint.t

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
  Coq_Z.leb Bigint.zero (fst (dadd y (dneg x)))

(** val dltb : dy -> dy -> bool **)

let dltb x y =
  Coq_Z.ltb Bigint.zero (fst (dadd y (dneg x)))

(** val dzero : dy -> bool **)

let dzero x =
  Coq_Z.eqb (fst x) Bigint.zero

(** val dmax : dy -> dy -> dy **)

let dmax x y =
  if dleb x y then y else x

(** val d0 : dy **)

let d0 =
  (Bigint.zero, Bigint.zero)

(** val dint : Bigint.t -> dy **)

let dint z0 =
  (z0, Bigint.zero)

(** val init_M :
    Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
    Float64.t array **)

let init_M xa xb n w =
  loop n (fun _ _ -> true) (fun i m ->
    let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i in
    let m0 =
      loop n (fun _ _ -> true) (fun j m0 ->
        (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) m0
          (add0 (mul0 i w) j)
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j))
        (Uint63.of_int (0)) m
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) m0
      (add0 (mul0 i w) n)
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xb i))
    (Uint63.of_int (0))
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n w) zero)

(** val init_Q : Uint63.t -> Float64.t array **)

let init_Q n =
  loop n (fun _ _ -> true) (fun i q ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) q
      (add0 (mul0 i n) i) one)
    (Uint63.of_int (0))
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) zero)

(** val thr_scale : Float64.t **)

let thr_scale =
  (Float64.of_float (0x1p-40))

(** val col_thr : Float64.t array array -> Uint63.t -> Float64.t array **)

let col_thr xa n =
  loop n (fun _ _ -> true) (fun j t ->
    let m =
      loop n (fun _ _ -> true) (fun i m ->
        let v =
          abs0
            ((fun a i -> Array.unsafe_get a (Uint63.hash i))
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i) j)
        in
        if ltb1 m v then v else m) (Uint63.of_int (0)) zero
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t j
      (mul1 m thr_scale))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n zero)

(** val swap_f :
    Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array **)

let swap_f t w p r =
  loop w (fun _ _ -> true) (fun j t0 ->
    let x =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0 (add0 (mul0 r w) j)
    in
    let y =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0 (add0 (mul0 p w) j)
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 r w) j) y)
      (add0 (mul0 p w) j) x)
    (Uint63.of_int (0)) t

(** val axpy_row :
    Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Float64.t -> Float64.t array **)

let axpy_row t w i r lo f =
  loop w (fun _ _ -> true) (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i w) j)
      (sub1
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
          (add0 (mul0 i w) j))
        (mul1 f
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
            (add0 (mul0 r w) j)))))
    lo t

(** val scale_row :
    Float64.t array -> Uint63.t -> Uint63.t -> Float64.t -> Float64.t array **)

let scale_row t w i piv =
  loop w (fun _ _ -> true) (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i w) j)
      (div0
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
          (add0 (mul0 i w) j))
        piv))
    (Uint63.of_int (0)) t

(** val tab : Uint63.t -> 'a1 -> (Uint63.t -> 'a1) -> 'a1 array **)

let tab n d f =
  loop n (fun _ _ -> true) (fun i t ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t i (f i))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n d)

type fstate = { fs_M : Float64.t array; fs_Q : Float64.t array;
                fs_r : Uint63.t; fs_pc : Uint63.t array;
                fs_perm : Uint63.t array }

(** val fwd_col :
    Uint63.t -> Uint63.t -> Float64.t array -> Uint63.t -> fstate -> fstate **)

let fwd_col n w thr c st =
  let r = st.fs_r in
  if ltb0 r n
  then let m = st.fs_M in
       let (p, mx) =
         loop n (fun _ _ -> true) (fun i pm ->
           let v =
             abs0
               ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m
                 (add0 (mul0 i w) c))
           in
           if ltb1 (snd pm) v then (i, v) else pm) r (r, zero)
       in
       if leb0 mx ((fun a i -> Array.unsafe_get a (Uint63.hash i)) thr c)
       then st
       else let m0 = swap_f m w p r in
            let q = swap_f st.fs_Q n p r in
            let piv =
              (fun a i -> Array.unsafe_get a (Uint63.hash i)) m0
                (add0 (mul0 r w) c)
            in
            let (m1, q0) =
              loop n (fun _ _ -> true) (fun i mq ->
                let (m1, q0) = mq in
                let f =
                  div0
                    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m1
                      (add0 (mul0 i w) c))
                    piv
                in
                let m2 = axpy_row m1 w i r (add0 c (Uint63.of_int (1))) f in
                (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) m2
                   (add0 (mul0 i w) c) zero),
                (axpy_row q0 n i r (Uint63.of_int (0)) f)))
                (add0 r (Uint63.of_int (1))) (m0, q)
            in
            let pm = st.fs_perm in
            let x = (fun a i -> Array.unsafe_get a (Uint63.hash i)) pm p in
            let y = (fun a i -> Array.unsafe_get a (Uint63.hash i)) pm r in
            { fs_M = m1; fs_Q = q0; fs_r = (add0 r (Uint63.of_int (1)));
            fs_pc =
            ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) st.fs_pc
              r c);
            fs_perm =
            ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) pm p y)
              r x) }
  else st

(** val forward :
    Uint63.t -> Uint63.t -> Float64.t array -> Float64.t array -> Float64.t
    array -> fstate **)

let forward n w thr m q =
  loop n (fun _ _ -> true) (fwd_col n w thr) (Uint63.of_int (0)) { fs_M = m;
    fs_Q = q; fs_r = (Uint63.of_int (0)); fs_pc =
    ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0)));
    fs_perm = (tab n (Uint63.of_int (0)) (fun i -> i)) }

(** val backsub :
    Uint63.t -> Uint63.t -> Float64.t array -> Float64.t array -> Float64.t
    array * Float64.t array **)

let backsub n w m q =
  loop n (fun _ _ -> true) (fun t mq ->
    let (m0, q0) = mq in
    let i = sub0 (sub0 n (Uint63.of_int (1))) t in
    let piv =
      (fun a i -> Array.unsafe_get a (Uint63.hash i)) m0 (add0 (mul0 i w) i)
    in
    let xi =
      div0
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m0
          (add0 (mul0 i w) n))
        piv
    in
    let m1 =
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) m0
        (add0 (mul0 i w) n) xi
    in
    let q1 = scale_row q0 n i piv in
    loop i (fun _ _ -> true) (fun i' mq0 ->
      let (m2, q2) = mq0 in
      let f =
        (fun a i -> Array.unsafe_get a (Uint63.hash i)) m2
          (add0 (mul0 i' w) i)
      in
      (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) m2
         (add0 (mul0 i' w) n)
         (sub1
           ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m2
             (add0 (mul0 i' w) n))
           (mul1 f xi))),
      (axpy_row q2 n i' i (Uint63.of_int (0)) f))) (Uint63.of_int (0)) (m1,
      q1))
    (Uint63.of_int (0)) (m, q)

(** val get_col :
    Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array **)

let get_col m n w c =
  loop n (fun _ _ -> true) (fun i x ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) x i
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m (add0 (mul0 i w) c)))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n zero)

(** val get_row :
    Float64.t array -> Uint63.t -> Uint63.t -> Float64.t array **)

let get_row q n i =
  loop n (fun _ _ -> true) (fun k x ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) x k
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) q (add0 (mul0 i n) k)))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n zero)

(** val free_col : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t **)

let free_col pc n r =
  let isp =
    loop r (fun _ _ -> true) (fun t isp ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) isp
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) pc t) true)
      (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n false)
  in
  loop n (fun _ _ -> true) (fun c f ->
    if (&&) (eqb0 f n)
         (negb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) isp c))
    then c
    else f) (Uint63.of_int (0)) n

(** val free_cols :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array **)

let free_cols pc n r =
  let isp =
    loop r (fun _ _ -> true) (fun t isp ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) isp
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) pc t) true)
      (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n false)
  in
  fst
    (loop n (fun _ _ -> true) (fun c st ->
      let (fc, cnt) = st in
      if (fun a i -> Array.unsafe_get a (Uint63.hash i)) isp c
      then (fc, cnt)
      else (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) fc cnt c),
             (add0 cnt (Uint63.of_int (1)))))
      (Uint63.of_int (0))
      (((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0))),
      (Uint63.of_int (0))))

(** val echelon_solve :
    Float64.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t ->
    bool -> Float64.t array -> Float64.t array **)

let echelon_solve m pc n w r homog x =
  loop r (fun _ _ -> true) (fun s x0 ->
    let t = sub0 (sub0 r (Uint63.of_int (1))) s in
    let c = (fun a i -> Array.unsafe_get a (Uint63.hash i)) pc t in
    let s0 =
      if homog
      then zero
      else (fun a i -> Array.unsafe_get a (Uint63.hash i)) m
             (add0 (mul0 t w) n)
    in
    let acc =
      loop n (fun _ _ -> true) (fun j acc ->
        sub1 acc
          (mul1
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m
              (add0 (mul0 t w) j))
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x0 j)))
        (add0 c (Uint63.of_int (1))) s0
    in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) x0 c
      (div0 acc
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) m
          (add0 (mul0 t w) c))))
    (Uint63.of_int (0)) x

(** val rat1 : Float64.t -> Bigint.t * Bigint.t **)

let rat1 f =
  let (m, e) = dec f in
  if Coq_Z.leb Bigint.zero e
  then ((Coq_Z.shiftl m e), Bigint.one)
  else let den = Coq_Z.shiftl Bigint.one (Coq_Z.opp e) in
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
           if Coq_Z.ltb ((fun x -> Bigint.shift_left x 1)
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
                Bigint.one)))))))))))))))))))))))))))))) k
           then ((fst st), true)
           else let rem = Coq_Z.sub an (Coq_Z.mul q ad) in
                let close =
                  Coq_Z.leb
                    (Coq_Z.shiftl
                      (Coq_Z.abs
                        (Coq_Z.sub (Coq_Z.mul m k) (Coq_Z.mul h den)))
                      ((fun x -> Bigint.shift_left x 1)
                      ((fun x -> Bigint.shift_left x 1)
                      ((fun x -> Bigint.shift_left x 1)
                      ((fun x -> Bigint.succ (Bigint.shift_left x 1))
                      ((fun x -> Bigint.shift_left x 1) Bigint.one))))))
                    (Coq_Z.mul (Coq_Z.abs m) k)
                in
                ((((((ad, rem), h), h1), k), k1),
                ((||) (Coq_Z.eqb rem Bigint.zero) close)))
           (Uint63.of_int (0)) ((((((m, den), Bigint.one), Bigint.zero),
           Bigint.zero), Bigint.one), false)
       in
       let (p, _) = fst st in
       let (p0, k1) = p in
       let (p1, _) = p0 in
       let (_, h1) = p1 in
       if Coq_Z.ltb Bigint.zero k1
       then (h1, k1)
       else (Bigint.zero, Bigint.one)

(** val ratvec : Float64.t array -> Uint63.t -> Bigint.t array * Bigint.t **)

let ratvec x n =
  let (p, l) =
    loop n (fun _ _ -> true) (fun j st ->
      let (y, l) = st in
      let (h, k) = y in
      let (h0, k0) =
        rat1 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x j)
      in
      ((((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) h j h0),
      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) k j k0)),
      (Coq_Z.mul (Coq_Z.div l (zgcd l k0)) k0))) (Uint63.of_int (0))
      ((((fun n d -> Array.make (Uint63.hash n) d) n Bigint.zero),
      ((fun n d -> Array.make (Uint63.hash n) d) n Bigint.one)), Bigint.one)
  in
  let (h, k) = p in
  ((loop n (fun _ _ -> true) (fun j p0 ->
     (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) p0 j
       (Coq_Z.mul ((fun a i -> Array.unsafe_get a (Uint63.hash i)) h j)
         (Coq_Z.div l ((fun a i -> Array.unsafe_get a (Uint63.hash i)) k j))))
     (Uint63.of_int (0))
     ((fun n d -> Array.make (Uint63.hash n) d) n Bigint.zero)),
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
  (Bigint.one, Bigint.zero)

(** val transpose : Float64.t array array -> Uint63.t -> Float64.t array **)

let transpose xa n =
  loop n (fun _ _ -> true) (fun i t ->
    let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i in
    loop n (fun _ _ -> true) (fun j t0 ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 j n) i)
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j))
      (Uint63.of_int (0)) t)
    (Uint63.of_int (0))
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n n) zero)

(** val rowabs : Float64.t array array -> Uint63.t -> dy array **)

let rowabs xa n =
  loop n (fun _ _ -> true) (fun k s ->
    let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa k in
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) s k
      (dsumf n (fun j ->
        dabs (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j)))))
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n d0)

(** val erow :
    Uint63.t -> Float64.t array -> Float64.t array -> dy array -> dy -> dy ->
    Uint63.t -> dy * bool **)

let erow n q aT s lamd mud2 i =
  let e =
    dsumb n (fun j -> fdot q (mul0 i n) aT (mul0 j n) n) (fun j d ->
      dabs
        (dsub (dint (if eqb0 i j then Bigint.one else Bigint.zero)) (dec d)))
  in
  let rr =
    dsumf n (fun k ->
      dmul
        (dabs
          (dec
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) q
              (add0 (mul0 i n) k))))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) s k))
  in
  ((dadd (dadd (fst e) (dmul lamd rr)) mud2), (snd e))

(** val rowR : Uint63.t -> Float64.t array -> Uint63.t -> dy * bool **)

let rowR n q i =
  ((dsumf n (fun k ->
     dabs
       (dec
         ((fun a i -> Array.unsafe_get a (Uint63.hash i)) q
           (add0 (mul0 i n) k))))),
    true)

(** val resid :
    Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array
    -> dy -> dy -> Uint63.t -> dy * bool **)

let resid n xa xb xt lamd mud1 i =
  let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i in
  let d = fdot row (Uint63.of_int (0)) xt (Uint63.of_int (0)) n in
  ((dadd
     (dadd
       (dabs
         (dsub (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xb i))
           (dec d)))
       (dmul lamd
         (dsumf n (fun j ->
           dabs
             (dmul
               (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j))
               (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xt j)))))))
     mud1),
  (is_finite d))

(** val certify :
    Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array
    -> Float64.t array -> Float64.t array -> bool **)

let certify n xa xb aT q xt =
  let nz = i2z n in
  let lamd =
    ((Coq_Z.mul ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
       nz),
    (Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)))))))
  in
  let mud1 =
    ((Coq_Z.mul ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
       nz),
    (Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    Bigint.one))))))))))))
  in
  let mud2 =
    ((Coq_Z.mul
       (Coq_Z.mul ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
         nz)
       nz),
    (Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    Bigint.one))))))))))))
  in
  let s = rowabs xa n in
  let (eps, ok1) = maxb n (erow n q aT s lamd mud2) in
  let (rho, _) = maxb n (rowR n q) in
  let (sig0, ok2) = maxb n (resid n xa xb xt lamd mud1) in
  (&&)
    ((&&) ((&&) ok1 ok2)
      (eqb0 ((fun a -> Uint63.of_int (Array.length a)) xt) n))
    ((&&) (dltb eps d1)
      (dleb
        (dadd
          (dmul (((fun x -> Bigint.shift_left x 1)
            ((fun x -> Bigint.shift_left x 1)
            ((fun x -> Bigint.shift_left x 1)
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.shift_left x 1)
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            ((fun x -> Bigint.succ (Bigint.shift_left x 1))
            Bigint.one))))))))), Bigint.zero) (dmul rho sig0))
          eps)
        d1))

(** val zdot :
    Float64.t array -> Uint63.t -> Bigint.t array -> Uint63.t -> dy **)

let zdot x o y len =
  dsumf len (fun k ->
    dmul (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) x (add0 o k)))
      (dint ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y k)))

(** val chk_incons :
    Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t array -> bool **)

let chk_incons aT xb n y =
  (&&) (allf n (fun j -> dzero (zdot aT (mul0 j n) y n)))
    (negb (dzero (zdot xb (Uint63.of_int (0)) y n)))

(** val chk_mult :
    Float64.t array array -> Float64.t array -> Uint63.t -> Bigint.t array ->
    Bigint.t -> Bigint.t array -> bool **)

let chk_mult xa xb n p q v =
  (&&)
    ((&&) (negb (Coq_Z.eqb q Bigint.zero))
      (negb
        (allf n (fun j ->
          Coq_Z.eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) v j)
            Bigint.zero))))
    (allf n (fun i ->
      let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i in
      (&&)
        (dzero
          (dsub (zdot row (Uint63.of_int (0)) p n)
            (dmul (dint q)
              (dec ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xb i)))))
        (dzero (zdot row (Uint63.of_int (0)) v n))))

(** val yv :
    Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array **)

let yv q n r t =
  fst (ratvec (get_row q n (add0 r t)) n)

(** val mark_D :
    Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> bool
    array * Uint63.t array **)

let mark_D perm n r k =
  loop k (fun _ _ -> true) (fun t st ->
    let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) perm (add0 r t) in
    (((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) (fst st) d true),
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) (snd st) d t)))
    (Uint63.of_int (0)) (((fun n d -> Array.make (Uint63.hash n) d) n false),
    ((fun n d -> Array.make (Uint63.hash n) d) n (Uint63.of_int (0))))

(** val mark_C : Uint63.t array -> Uint63.t -> Uint63.t -> bool array **)

let mark_C fc n k =
  loop k (fun _ _ -> true) (fun t c ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) c
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) fc t) true)
    (Uint63.of_int (0)) ((fun n d -> Array.make (Uint63.hash n) d) n false)

(** val chk_red :
    Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t array ->
    Uint63.t -> bool array -> bool **)

let chk_red aT xb n y d df =
  (&&)
    ((&&) (allf n (fun j -> dzero (zdot aT (mul0 j n) y n)))
      (dzero (zdot xb (Uint63.of_int (0)) y n)))
    ((&&)
      (negb
        (Coq_Z.eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y d)
          Bigint.zero))
      (allf n (fun i ->
        (||) (negb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) df i))
          ((||) (eqb0 i d)
            (Coq_Z.eqb ((fun a i -> Array.unsafe_get a (Uint63.hash i)) y i)
              Bigint.zero)))))

(** val scan_null :
    Float64.t array -> Float64.t array -> Float64.t array -> Uint63.t array
    -> Uint63.t array -> bool array -> Uint63.t -> Uint63.t -> Uint63.t ->
    bool * bool **)

let scan_null aT xb q perm fc df n r k =
  loop k (fun _ _ -> true) (fun t s ->
    let y = yv q n r t in
    let d = (fun a i -> Array.unsafe_get a (Uint63.hash i)) perm (add0 r t) in
    (((||) (fst s) (chk_incons aT xb n y)),
    ((&&) (snd s)
      ((&&)
        ((&&) (ltb0 d n)
          (ltb0 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) fc t) n))
        (chk_red aT xb n y d df)))))
    (Uint63.of_int (0)) (false, (ltb0 r n))

(** val bentry :
    Float64.t array array -> bool array -> Uint63.t array -> Uint63.t array
    -> bool array -> Uint63.t -> Uint63.t -> Float64.t **)

let bentry xa df tix fc cf i j =
  if (fun a i -> Array.unsafe_get a (Uint63.hash i)) df i
  then if eqb0 j
            ((fun a i -> Array.unsafe_get a (Uint63.hash i)) fc
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) tix i))
       then one
       else zero
  else if (fun a i -> Array.unsafe_get a (Uint63.hash i)) cf j
       then zero
       else (fun a i -> Array.unsafe_get a (Uint63.hash i))
              ((fun a i -> Array.unsafe_get a (Uint63.hash i)) xa i) j

(** val padB :
    Float64.t array array -> Uint63.t -> bool array -> Uint63.t array ->
    Uint63.t array -> bool array -> Float64.t array array **)

let padB xa n df tix fc cf =
  tab n ((fun n d -> Array.make (Uint63.hash n) d) (Uint63.of_int (0)) zero)
    (fun i -> tab n zero (fun j -> bentry xa df tix fc cf i j))

(** val certify_inj :
    Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array
    -> bool **)

let certify_inj n xa aT q =
  let nz = i2z n in
  let lamd =
    ((Coq_Z.mul ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
       nz),
    (Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)))))))
  in
  let mud2 =
    ((Coq_Z.mul
       (Coq_Z.mul ((fun x -> Bigint.succ (Bigint.shift_left x 1)) Bigint.one)
         nz)
       nz),
    (Bigint.neg ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.succ (Bigint.shift_left x 1))
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    ((fun x -> Bigint.shift_left x 1) ((fun x -> Bigint.shift_left x 1)
    Bigint.one))))))))))))
  in
  let s = rowabs xa n in
  let (eps, ok1) = maxb n (erow n q aT s lamd mud2) in (&&) ok1 (dltb eps d1)

(** val padded_ok :
    Float64.t array array -> Uint63.t -> bool array -> Uint63.t array ->
    Uint63.t array -> bool array -> bool **)

let padded_ok xa n df tix fc cf =
  let b = padB xa n df tix fc cf in
  let w = add0 n (Uint63.of_int (1)) in
  let st =
    forward n w (col_thr b n)
      (init_M b ((fun n d -> Array.make (Uint63.hash n) d) n zero) n w)
      (init_Q n)
  in
  if eqb0 st.fs_r n
  then certify_inj n b (transpose b n) (snd (backsub n w st.fs_M st.fs_Q))
  else false

(** val solve :
    uint -> Float64.t array array -> Float64.t array -> Float64.t array
    outcome **)

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
                 let x0 =
                   echelon_solve m st.fs_pc n w r false
                     ((fun n d -> Array.make (Uint63.hash n) d) n zero)
                 in
                 let v =
                   echelon_solve m st.fs_pc n w r true
                     ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                       ((fun n d -> Array.make (Uint63.hash n) d) n zero) f
                       one)
                 in
                 let (p, q) = ratvec x0 n in
                 if chk_mult xa xb n p q (fst (ratvec v n))
                 then Multiple
                 else solve_exact n xa xb
