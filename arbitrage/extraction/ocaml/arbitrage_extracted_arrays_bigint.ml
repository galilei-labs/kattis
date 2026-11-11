
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

  (** val mul : Bigint.t -> Bigint.t -> Bigint.t **)

  let mul = Bigint.mul

  (** val pow_pos : Bigint.t -> Bigint.t -> Bigint.t **)

  let pow_pos z0 =
    Pos.iter (mul z0) Bigint.one

  (** val pow : Bigint.t -> Bigint.t -> Bigint.t **)

  let pow = Bigint.(fun x y ->
  if sign y < 0 then zero else pow x (to_int y))

  (** val compare : Bigint.t -> Bigint.t -> comparison **)

  let compare = (fun x y -> let s = Bigint.compare x y in
  if s = 0 then Eq else if s < 0 then Lt else Gt)

  (** val ltb : Bigint.t -> Bigint.t -> bool **)

  let ltb = Bigint.lt
 end

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val head0 : Uint63.t -> Uint63.t **)

let head0 = Uint63.head0

(** val ltb1 : Float64.t -> Float64.t -> bool **)

let ltb1 = Float64.lt

(** val leb0 : Float64.t -> Float64.t -> bool **)

let leb0 = Float64.le

(** val mul1 : Float64.t -> Float64.t -> Float64.t **)

let mul1 = Float64.mul

(** val div0 : Float64.t -> Float64.t -> Float64.t **)

let div0 = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

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

(** val primes : Uint63.t array **)

let primes =
  (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
        ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
          ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
            ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                        ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                          ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                            ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                      ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                        ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                          ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                            ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                              ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                                ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                                  ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a)
                                                    ((fun n d -> Array.make (Uint63.hash n) d)
                                                      (Uint63.of_int (25))
                                                      (Uint63.of_int (0)))
                                                    (Uint63.of_int (0))
                                                    (Uint63.of_int (2)))
                                                  (Uint63.of_int (1))
                                                  (Uint63.of_int (3)))
                                                (Uint63.of_int (2))
                                                (Uint63.of_int (5)))
                                              (Uint63.of_int (3))
                                              (Uint63.of_int (7)))
                                            (Uint63.of_int (4))
                                            (Uint63.of_int (11)))
                                          (Uint63.of_int (5))
                                          (Uint63.of_int (13)))
                                        (Uint63.of_int (6))
                                        (Uint63.of_int (17)))
                                      (Uint63.of_int (7))
                                      (Uint63.of_int (19)))
                                    (Uint63.of_int (8)) (Uint63.of_int (23)))
                                  (Uint63.of_int (9)) (Uint63.of_int (29)))
                                (Uint63.of_int (10)) (Uint63.of_int (31)))
                              (Uint63.of_int (11)) (Uint63.of_int (37)))
                            (Uint63.of_int (12)) (Uint63.of_int (41)))
                          (Uint63.of_int (13)) (Uint63.of_int (43)))
                        (Uint63.of_int (14)) (Uint63.of_int (47)))
                      (Uint63.of_int (15)) (Uint63.of_int (53)))
                    (Uint63.of_int (16)) (Uint63.of_int (59)))
                  (Uint63.of_int (17)) (Uint63.of_int (61)))
                (Uint63.of_int (18)) (Uint63.of_int (67)))
              (Uint63.of_int (19)) (Uint63.of_int (71)))
            (Uint63.of_int (20)) (Uint63.of_int (73)))
          (Uint63.of_int (21)) (Uint63.of_int (79)))
        (Uint63.of_int (22)) (Uint63.of_int (83)))
      (Uint63.of_int (23)) (Uint63.of_int (89)))
    (Uint63.of_int (24)) (Uint63.of_int (97))

(** val dvd1 : Uint63.t -> Uint63.t -> Uint63.t **)

let dvd1 n x =
  if eqb (mod0 n x) (Uint63.of_int (0))
  then (Uint63.of_int (1))
  else (Uint63.of_int (0))

(** val mlt : Uint63.t -> Uint63.t -> Uint63.t **)

let mlt n p =
  let p2 = mul0 p p in
  let p3 = mul0 p2 p in
  let p4 = mul0 p3 p in
  let p5 = mul0 p4 p in
  let p6 = mul0 p5 p in
  add0
    (add0 (add0 (add0 (add0 (dvd1 n p) (dvd1 n p2)) (dvd1 n p3)) (dvd1 n p4))
      (dvd1 n p5))
    (dvd1 n p6)

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

(** val ex_step :
    (Uint63.t -> Uint63.t) -> Uint63.t -> ((bool * Bigint.t) * Bigint.t) ->
    (bool * Bigint.t) * Bigint.t **)

let ex_step dv t s = match s with
| (p, q) ->
  let (_, p0) = p in
  let d = dv t in
  if ltsb (Uint63.of_int (0)) d
  then ((true,
         (Z.mul p0
           (Z.pow
             (zofi ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes t))
             (zofi d)))),
         q)
  else if ltsb d (Uint63.of_int (0))
       then ((true, p0),
              (Z.mul q
                (Z.pow
                  (zofi
                    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes t))
                  (zofi (sub (Uint63.of_int (0)) d)))))
       else s

(** val exact_gt : (Uint63.t -> Uint63.t) -> bool **)

let exact_gt dv =
  let (p, q) =
    loop (Uint63.of_int (25)) (fun _ _ -> true) (ex_step dv)
      (Uint63.of_int (0)) ((false, Bigint.one), Bigint.one)
  in
  let (nz, p0) = p in if nz then Z.ltb q p0 else false

(** val f_one : Float64.t **)

let f_one =
  of_uint63 (Uint63.of_int (1))

(** val f_two : Float64.t **)

let f_two =
  of_uint63 (Uint63.of_int (2))

(** val f_c0 : Float64.t **)

let f_c0 =
  of_uint63 (Uint63.of_int (1048576))

(** val f_c1 : Float64.t **)

let f_c1 =
  of_uint63 (Uint63.of_int (1048577))

(** val cap : Uint63.t **)

let cap =
  (Uint63.of_int (1048576))

(** val bIAS : Uint63.t **)

let bIAS =
  (Uint63.of_int (1073741824))

(** val mulcell :
    Float64.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t ->
    (Float64.t * Uint63.t) * Uint63.t **)

let mulcell m1 e1 n1 m2 e2 n2 =
  let p = mul1 m1 m2 in
  let n = add0 (add0 n1 n2) (Uint63.of_int (2)) in
  let n' = if ltb0 cap n then add0 cap (Uint63.of_int (1)) else n in
  if leb0 f_two p
  then (((div0 p f_two), (add0 (sub (add0 e1 e2) bIAS) (Uint63.of_int (1)))),
         n')
  else ((p, (sub (add0 e1 e2) bIAS)), n')

(** val ratecell :
    Uint63.t -> Uint63.t -> (Float64.t * Uint63.t) * Uint63.t **)

let ratecell a b =
  let ha = head0 a in
  let hb = head0 b in
  let num = if ltb0 ha hb then lsl0 b (sub hb ha) else b in
  let den = if ltb0 ha hb then a else lsl0 a (sub ha hb) in
  let r = div0 (of_uint63 num) (of_uint63 den) in
  let e = sub (add0 bIAS ha) hb in
  if ltb1 r f_one
  then (((mul1 r f_two), (sub e (Uint63.of_int (1)))), (Uint63.of_int (2)))
  else ((r, e), (Uint63.of_int (2)))

(** val fcmp :
    Float64.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t ->
    bool option **)

let fcmp m1 e1 n1 m2 e2 n2 =
  if (||) (ltb0 cap n1) (ltb0 cap n2)
  then None
  else if leb (add0 e2 (Uint63.of_int (2))) e1
       then Some true
       else if leb (add0 e1 (Uint63.of_int (2))) e2
            then Some false
            else let x = if ltb0 e2 e1 then mul1 m1 f_two else m1 in
                 let y = if ltb0 e1 e2 then mul1 m2 f_two else m2 in
                 if ltb1 (mul1 y f_c1) (mul1 x f_c0)
                 then Some true
                 else if ltb1 (mul1 x f_c1) (mul1 y f_c0)
                      then Some false
                      else None

type tabs = { tPR : bool array; tMA : Float64.t array; tEX : Uint63.t array;
              tCN : Uint63.t array; tVT : Uint63.t array }

(** val wr_head :
    tabs -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t -> Uint63.t array
    -> tabs **)

let wr_head t q m e n v =
  { tPR =
    ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.tPR q true);
    tMA = ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.tMA q m);
    tEX = ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.tEX q e);
    tCN = ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t.tCN q n);
    tVT = v }

(** val vadd :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let vadd bd b1 b2 v =
  loop (Uint63.of_int (25)) (fun _ _ -> true) (fun t w ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) w (add0 bd t)
      (add0 ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w (add0 b1 t))
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) w (add0 b2 t))))
    (Uint63.of_int (0)) v

(** val vset :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t array -> Uint63.t array **)

let vset bd a b v =
  loop (Uint63.of_int (25)) (fun _ _ -> true) (fun t w ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) w (add0 bd t)
      (sub (mlt b ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes t))
        (mlt a ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes t))))
    (Uint63.of_int (0)) v

(** val init_step :
    Uint63.t -> Uint63.t array -> Uint63.t array -> Uint63.t array ->
    Uint63.t array -> Uint63.t -> tabs -> tabs **)

let init_step c xs xd xa xb r t =
  let u = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xs r in
  let v = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xd r in
  let a = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xa r in
  let b = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xb r in
  let q = add0 (mul0 u c) v in
  let (p, n) = ratecell a b in
  let (m, e) = p in
  let better =
    if (fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tPR q
    then (match fcmp m e n
                  ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tMA q)
                  ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tEX q)
                  ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tCN q) with
          | Some g -> g
          | None ->
            exact_gt (fun t0 ->
              sub
                (sub
                  (mlt b
                    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes
                      t0))
                  (mlt a
                    ((fun a i -> Array.unsafe_get a (Uint63.hash i)) primes
                      t0)))
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tVT
                  (add0 (mul0 (Uint63.of_int (25)) q) t0))))
    else true
  in
  if better
  then wr_head t q m e n (vset (mul0 (Uint63.of_int (25)) q) a b t.tVT)
  else t

(** val fw_j :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (tabs * bool) ->
    tabs * bool **)

let fw_j c k i j s =
  let t = fst s in
  if eqb j k
  then s
  else let qkj = add0 (mul0 k c) j in
       if (fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tPR qkj
       then let qik = add0 (mul0 i c) k in
            let qij = add0 (mul0 i c) j in
            let (p, n) =
              mulcell
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tMA qik)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tEX qik)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tCN qik)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tMA qkj)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tEX qkj)
                ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tCN qkj)
            in
            let (m, e) = p in
            let bik = mul0 (Uint63.of_int (25)) qik in
            let bkj = mul0 (Uint63.of_int (25)) qkj in
            let bij = mul0 (Uint63.of_int (25)) qij in
            let ex =
              if eqb i j
              then (match fcmp m e n f_one bIAS (Uint63.of_int (0)) with
                    | Some g -> g
                    | None ->
                      exact_gt (fun t0 ->
                        add0
                          ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                            t.tVT (add0 bik t0))
                          ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                            t.tVT (add0 bkj t0))))
              else false
            in
            if ex
            then (t, true)
            else let better =
                   if (fun a i -> Array.unsafe_get a (Uint63.hash i)) t.tPR
                        qij
                   then (match fcmp m e n
                                 ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                   t.tMA qij)
                                 ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                   t.tEX qij)
                                 ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                   t.tCN qij) with
                         | Some g -> g
                         | None ->
                           exact_gt (fun t0 ->
                             sub
                               (add0
                                 ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                   t.tVT (add0 bik t0))
                                 ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                   t.tVT (add0 bkj t0)))
                               ((fun a i -> Array.unsafe_get a (Uint63.hash i))
                                 t.tVT (add0 bij t0))))
                   else true
                 in
                 if better
                 then ((wr_head t qij m e n (vadd bij bik bkj t.tVT)), false)
                 else s
       else s

(** val fw_i :
    Uint63.t -> Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool **)

let fw_i c k i s =
  if eqb i k
  then s
  else if (fun a i -> Array.unsafe_get a (Uint63.hash i)) (fst s).tPR
            (add0 (mul0 i c) k)
       then loop c (fun _ s0 -> negb (snd s0)) (fw_j c k i)
              (Uint63.of_int (0)) s
       else s

(** val fw_k : Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool **)

let fw_k c k s =
  loop c (fun _ s0 -> negb (snd s0)) (fw_i c k) (Uint63.of_int (0)) s

(** val arbitrage_impl :
    uint -> uint array -> uint array -> uint array -> uint array -> bool **)

let arbitrage_impl c xs xd xa xb =
  let cc = mul0 c c in
  let t0 = { tPR = ((fun n d -> Array.make (Uint63.hash n) d) cc false);
    tMA = ((fun n d -> Array.make (Uint63.hash n) d) cc f_one); tEX =
    ((fun n d -> Array.make (Uint63.hash n) d) cc (Uint63.of_int (0))); tCN =
    ((fun n d -> Array.make (Uint63.hash n) d) cc (Uint63.of_int (0))); tVT =
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 (Uint63.of_int (25)) cc)
      (Uint63.of_int (0))) }
  in
  let t1 =
    loop ((fun a -> Uint63.of_int (Array.length a)) xs) (fun _ _ -> true)
      (init_step c xs xd xa xb) (Uint63.of_int (0)) t0
  in
  snd
    (loop c (fun _ s -> negb (snd s)) (fw_k c) (Uint63.of_int (0)) (t1,
      false))

(** val arbitrage :
    uint -> uint array -> uint array -> uint array -> uint array -> bool **)

let arbitrage =
  arbitrage_impl
