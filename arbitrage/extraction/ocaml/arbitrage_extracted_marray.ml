
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

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

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

(** val primes : Uint63.t Marray.t **)

let primes =
  set
    (set
      (set
        (set
          (set
            (set
              (set
                (set
                  (set
                    (set
                      (set
                        (set
                          (set
                            (set
                              (set
                                (set
                                  (set
                                    (set
                                      (set
                                        (set
                                          (set
                                            (set
                                              (set
                                                (set
                                                  (set
                                                    (make
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

(** val ex_step :
    (Uint63.t -> Uint63.t) -> Uint63.t -> ((bool * z) * z) -> (bool * z) * z **)

let ex_step dv t s = match s with
| (p, q) ->
  let (_, p0) = p in
  let d = dv t in
  if ltsb (Uint63.of_int (0)) d
  then ((true, (Z.mul p0 (Z.pow (zofi (get primes t)) (zofi d)))), q)
  else if ltsb d (Uint63.of_int (0))
       then ((true, p0),
              (Z.mul q
                (Z.pow (zofi (get primes t))
                  (zofi (sub (Uint63.of_int (0)) d)))))
       else s

(** val exact_gt : (Uint63.t -> Uint63.t) -> bool **)

let exact_gt dv =
  let (p, q) =
    loop (Uint63.of_int (25)) (fun _ _ -> true) (ex_step dv)
      (Uint63.of_int (0)) ((false, (Zpos XH)), (Zpos XH))
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

type tabs = { tPR : bool Marray.t; tMA : Float64.t Marray.t;
              tEX : Uint63.t Marray.t; tCN : Uint63.t Marray.t;
              tVT : Uint63.t Marray.t }

(** val wr_head :
    tabs -> Uint63.t -> Float64.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> tabs **)

let wr_head t q m e n v =
  { tPR = (set t.tPR q true); tMA = (set t.tMA q m); tEX = (set t.tEX q e);
    tCN = (set t.tCN q n); tVT = v }

(** val vadd :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let vadd bd b1 b2 v =
  loop (Uint63.of_int (25)) (fun _ _ -> true) (fun t w ->
    set w (add0 bd t) (add0 (get w (add0 b1 t)) (get w (add0 b2 t))))
    (Uint63.of_int (0)) v

(** val vset :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let vset bd a b v =
  loop (Uint63.of_int (25)) (fun _ _ -> true) (fun t w ->
    set w (add0 bd t) (sub (mlt b (get primes t)) (mlt a (get primes t))))
    (Uint63.of_int (0)) v

(** val init_step :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t -> tabs -> tabs **)

let init_step c xs xd xa xb r t =
  let u = get xs r in
  let v = get xd r in
  let a = get xa r in
  let b = get xb r in
  let q = add0 (mul0 u c) v in
  let (p, n) = ratecell a b in
  let (m, e) = p in
  let better =
    if get t.tPR q
    then (match fcmp m e n (get t.tMA q) (get t.tEX q) (get t.tCN q) with
          | Some g -> g
          | None ->
            exact_gt (fun t0 ->
              sub (sub (mlt b (get primes t0)) (mlt a (get primes t0)))
                (get t.tVT (add0 (mul0 (Uint63.of_int (25)) q) t0))))
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
       if get t.tPR qkj
       then let qik = add0 (mul0 i c) k in
            let qij = add0 (mul0 i c) j in
            let (p, n) =
              mulcell (get t.tMA qik) (get t.tEX qik) (get t.tCN qik)
                (get t.tMA qkj) (get t.tEX qkj) (get t.tCN qkj)
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
                        add0 (get t.tVT (add0 bik t0))
                          (get t.tVT (add0 bkj t0))))
              else false
            in
            if ex
            then (t, true)
            else let better =
                   if get t.tPR qij
                   then (match fcmp m e n (get t.tMA qij) (get t.tEX qij)
                                 (get t.tCN qij) with
                         | Some g -> g
                         | None ->
                           exact_gt (fun t0 ->
                             sub
                               (add0 (get t.tVT (add0 bik t0))
                                 (get t.tVT (add0 bkj t0)))
                               (get t.tVT (add0 bij t0))))
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
  else if get (fst s).tPR (add0 (mul0 i c) k)
       then loop c (fun _ s0 -> negb (snd s0)) (fw_j c k i)
              (Uint63.of_int (0)) s
       else s

(** val fw_k : Uint63.t -> Uint63.t -> (tabs * bool) -> tabs * bool **)

let fw_k c k s =
  loop c (fun _ s0 -> negb (snd s0)) (fw_i c k) (Uint63.of_int (0)) s

(** val arbitrage_impl :
    uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> bool **)

let arbitrage_impl c xs xd xa xb =
  let cc = mul0 c c in
  let t0 = { tPR = (make cc false); tMA = (make cc f_one); tEX =
    (make cc (Uint63.of_int (0))); tCN = (make cc (Uint63.of_int (0))); tVT =
    (make (mul0 (Uint63.of_int (25)) cc) (Uint63.of_int (0))) }
  in
  let t1 =
    loop (length xs) (fun _ _ -> true) (init_step c xs xd xa xb)
      (Uint63.of_int (0)) t0
  in
  snd
    (loop c (fun _ s -> negb (snd s)) (fw_k c) (Uint63.of_int (0)) (t1,
      false))

module ArbitrageImpl =
 struct
  (** val arbitrage :
      uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
      Marray.t -> bool **)

  let arbitrage =
    arbitrage_impl
 end
