
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

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val even : z -> bool **)

  let even = function
  | Z0 -> true
  | Zpos p -> (match p with
               | XO _ -> true
               | _ -> false)
  | Zneg p -> (match p with
               | XO _ -> true
               | _ -> false)

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val odd : z -> bool **)

  let odd = function
  | Z0 -> false
  | Zpos p -> (match p with
               | XO _ -> false
               | _ -> true)
  | Zneg p -> (match p with
               | XO _ -> false
               | _ -> true)
 end

(** val add0 : Uint63.t -> Uint63.t -> Uint63.t **)

let add0 = Uint63.add

(** val sub0 : Uint63.t -> Uint63.t -> Uint63.t **)

let sub0 = Uint63.sub

(** val mul0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mul0 = Uint63.mul

(** val ltb0 : Uint63.t -> Uint63.t -> bool **)

let ltb0 = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val zgcd_loop : z -> z -> z **)

let rec zgcd_loop a b =
  if Z.ltb Z0 b then zgcd_loop b (Z.modulo a b) else a

(** val zgcd : z -> z -> z **)

let zgcd a b =
  zgcd_loop (Z.abs a) (Z.abs b)

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val dguard : z -> z -> bool **)

let dguard m d =
  (&&) ((&&) (Z.ltb (Zpos XH) d) (Z.ltb Z0 m)) (Z.eqb (Z.modulo m d) Z0)

(** val guard : z -> z -> bool **)

let guard x m =
  (&&) (Z.leb Z0 x) (Z.ltb x m)

(** val pm_loop : z -> z -> z -> z -> z **)

let rec pm_loop b e m acc =
  if bdec (Z.ltb Z0 e)
  then pm_loop (Z.modulo (Z.mul b b) m) (Z.div e (Zpos (XO XH))) m
         (if Z.odd e then Z.modulo (Z.mul acc b) m else acc)
  else Z.modulo acc m

(** val powmod : z -> z -> z -> z **)

let powmod b e m =
  pm_loop (Z.modulo b m) e m (Zpos XH)

(** val strip : z -> Uint63.t -> z * Uint63.t **)

let rec strip d s =
  if bdec (Z.ltb Z0 d)
  then if Z.even d
       then strip (Z.div d (Zpos (XO XH))) (add0 s (Uint63.of_int (1)))
       else (d, s)
  else (d, s)

(** val sq_loop : z -> z -> Uint63.t -> bool **)

let rec sq_loop n x k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let x0 = Z.modulo (Z.mul x x) n in
       if Z.eqb x0 (Z.sub n (Zpos XH))
       then true
       else sq_loop n x0 (sub0 k (Uint63.of_int (1)))
  else false

(** val mr_base : z -> z -> Uint63.t -> z -> bool **)

let mr_base n d s a =
  let x = powmod a d n in
  if (||) (Z.eqb x (Zpos XH)) (Z.eqb x (Z.sub n (Zpos XH)))
  then true
  else sq_loop n x (sub0 s (Uint63.of_int (1)))

(** val miller_rabin : z -> bool **)

let miller_rabin n =
  let (d, s) = strip (Z.sub n (Zpos XH)) (Uint63.of_int (0)) in
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
                      ((&&) (mr_base n d s (Zpos (XO XH)))
                        (mr_base n d s (Zpos (XI XH))))
                      (mr_base n d s (Zpos (XI (XO XH)))))
                    (mr_base n d s (Zpos (XI (XI XH)))))
                  (mr_base n d s (Zpos (XI (XI (XO XH))))))
                (mr_base n d s (Zpos (XI (XO (XI XH))))))
              (mr_base n d s (Zpos (XI (XO (XO (XO XH)))))))
            (mr_base n d s (Zpos (XI (XI (XO (XO XH)))))))
          (mr_base n d s (Zpos (XI (XI (XI (XO XH)))))))
        (mr_base n d s (Zpos (XI (XO (XI (XI XH)))))))
      (mr_base n d s (Zpos (XI (XI (XI (XI XH)))))))
    (mr_base n d s (Zpos (XI (XO (XI (XO (XO XH)))))))

(** val rho_f : z -> z -> z -> z **)

let rho_f n c y =
  Z.modulo (Z.add (Z.mul y y) c) n

(** val rho_iter : z -> z -> z -> Uint63.t -> z **)

let rec rho_iter n c y k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then rho_iter n c (rho_f n c y) (sub0 k (Uint63.of_int (1)))
  else y

(** val rho_batch : z -> z -> z -> z -> z -> Uint63.t -> z * z **)

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
    z -> z -> z -> z -> z -> Uint63.t -> Uint63.t -> ((z * z) * z) * z **)

let rec rho_inner n c x y q r k =
  if bdec ((&&) (ltb0 k r) (ltb0 k (add0 k rho_m)))
  then let t = if ltb0 (sub0 r k) rho_m then sub0 r k else rho_m in
       let (y', q') = rho_batch n c x y q t in
       let g = zgcd q' n in
       if Z.eqb g (Zpos XH)
       then rho_inner n c x y' q' r (add0 k rho_m)
       else (((g, y), y'), q')
  else ((((Zpos XH), y), y), q)

(** val rho_rmax : Uint63.t **)

let rho_rmax =
  (Uint63.of_int (33554432))

(** val rho_back : z -> z -> z -> z -> Uint63.t -> z **)

let rec rho_back n c x ys k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let ys0 = rho_f n c ys in
       let g = zgcd (Z.abs (Z.sub x ys0)) n in
       if Z.eqb g (Zpos XH)
       then rho_back n c x ys0 (sub0 k (Uint63.of_int (1)))
       else g
  else n

(** val rho_outer : z -> z -> z -> z -> Uint63.t -> z **)

let rec rho_outer n c y q r =
  let y0 = rho_iter n c y r in
  let (p, q') = rho_inner n c y y0 q r (Uint63.of_int (0)) in
  let (p0, y') = p in
  let (g, ys) = p0 in
  if Z.eqb g (Zpos XH)
  then if bdec ((&&) (ltb0 r rho_rmax) (ltb0 r (mul0 r (Uint63.of_int (2)))))
       then rho_outer n c y' q' (mul0 r (Uint63.of_int (2)))
       else Z0
  else if Z.eqb g n
       then rho_back n c y ys (add0 rho_m (Uint63.of_int (1)))
       else g

(** val rho_try : z -> z -> Uint63.t -> z **)

let rec rho_try n c k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then let g = rho_outer n c (Zpos (XO XH)) (Zpos XH) (Uint63.of_int (1)) in
       if (&&) (Z.ltb (Zpos XH) g) (Z.ltb g n)
       then g
       else rho_try n (Z.add c (Zpos XH)) (sub0 k (Uint63.of_int (1)))
  else Z0

(** val rho : z -> z **)

let rho n =
  rho_try n (Zpos XH) (Uint63.of_int (20))

(** val cAP : Uint63.t **)

let cAP =
  (Uint63.of_int (128))

(** val push : z Marray.t -> Uint63.t -> z -> z Marray.t * Uint63.t **)

let push acc cnt p =
  ((set acc cnt p), (add0 cnt (Uint63.of_int (1))))

(** val divout :
    z -> z -> z Marray.t -> Uint63.t -> (z * z Marray.t) * Uint63.t **)

let rec divout m d acc cnt =
  if bdec (dguard m d)
  then let (acc', cnt') = push acc cnt d in divout (Z.div m d) d acc' cnt'
  else ((m, acc), cnt)

(** val trial :
    z -> z -> z -> z Marray.t -> Uint63.t -> ((z * z) * z Marray.t) * Uint63.t **)

let rec trial b m d acc cnt =
  if bdec (Z.ltb d b)
  then if Z.ltb m (Z.mul d d)
       then (((m, d), acc), cnt)
       else let (p, cnt') = divout m d acc cnt in
            let (m', acc') = p in trial b m' (Z.add d (Zpos XH)) acc' cnt'
  else (((m, d), acc), cnt)

(** val b0 : z **)

let b0 =
  Zpos (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))

(** val fallback :
    z -> z -> z Marray.t -> Uint63.t -> z Marray.t * Uint63.t **)

let fallback m lo acc cnt =
  let (p, cnt') = trial (Z.add m (Zpos (XO XH))) m lo acc cnt in
  let (p0, acc') = p in
  let (r, _) = p0 in
  if Z.ltb (Zpos XH) r then push acc' cnt' r else (acc', cnt')

(** val all_q : z -> z -> z Marray.t -> Uint63.t -> Uint63.t -> bool **)

let rec all_q r a qs qc i =
  if bdec (ltb0 i qc)
  then let q = get qs i in
       if (&&) (ltb0 (Uint63.of_int (0)) i)
            (Z.eqb q (get qs (sub0 i (Uint63.of_int (1)))))
       then all_q r a qs qc (add0 i (Uint63.of_int (1)))
       else if Z.eqb
                 (zgcd
                   (Z.sub (powmod a (Z.div (Z.sub r (Zpos XH)) q) r) (Zpos
                     XH))
                   r)
                 (Zpos XH)
            then all_q r a qs qc (add0 i (Uint63.of_int (1)))
            else false
  else true

(** val lucas_ok : z -> z -> z Marray.t -> Uint63.t -> bool **)

let lucas_ok r a qs qc =
  (&&) (Z.eqb (powmod a (Z.sub r (Zpos XH)) r) (Zpos XH))
    (all_q r a qs qc (Uint63.of_int (0)))

(** val cert_try : z -> z Marray.t -> Uint63.t -> z -> Uint63.t -> bool **)

let rec cert_try r qs qc a k =
  if bdec (ltb0 (Uint63.of_int (0)) k)
  then if lucas_ok r a qs qc
       then true
       else cert_try r qs qc (Z.add a (Zpos XH)) (sub0 k (Uint63.of_int (1)))
  else false

(** val certify : z -> z Marray.t -> Uint63.t -> bool **)

let certify r qs qc =
  cert_try r qs qc (Zpos (XO XH)) (Uint63.of_int (1000))

(** val fac : z -> z -> z Marray.t -> Uint63.t -> z Marray.t * Uint63.t **)

let rec fac m lo acc cnt =
  let (p, cnt1) = trial b0 m lo acc cnt in
  let (p0, acc1) = p in
  let (r, d) = p0 in
  if Z.ltb r (Z.mul d d)
  then if Z.ltb (Zpos XH) r then push acc1 cnt1 r else (acc1, cnt1)
  else if miller_rabin r
       then if bdec (guard (Z.sub r (Zpos XH)) m)
            then let (qs, qc) =
                   fac (Z.sub r (Zpos XH)) (Zpos (XO XH)) (make cAP Z0)
                     (Uint63.of_int (0))
                 in
                 if certify r qs qc
                 then push acc1 cnt1 r
                 else fallback r d acc1 cnt1
            else fallback r d acc1 cnt1
       else let g = rho r in
            if (&&) ((&&) (Z.ltb (Zpos XH) g) (Z.ltb g r))
                 (Z.eqb (Z.modulo r g) Z0)
            then if bdec (guard g m)
                 then if bdec (guard (Z.div r g) m)
                      then let (acc2, cnt2) = fac g b0 acc1 cnt1 in
                           fac (Z.div r g) b0 acc2 cnt2
                      else fallback r d acc1 cnt1
                 else fallback r d acc1 cnt1
            else fallback r d acc1 cnt1

(** val copy :
    z Marray.t -> z Marray.t -> Uint63.t -> Uint63.t -> z Marray.t **)

let rec copy src dst n i =
  if bdec (ltb0 i n)
  then copy src (set dst i (get src i)) n (add0 i (Uint63.of_int (1)))
  else dst

(** val sink : z Marray.t -> Uint63.t -> z Marray.t **)

let rec sink a j =
  if bdec (ltb0 (Uint63.of_int (0)) j)
  then let x = get a (sub0 j (Uint63.of_int (1))) in
       let y = get a j in
       if Z.ltb y x
       then sink (set (set a (sub0 j (Uint63.of_int (1))) y) j x)
              (sub0 j (Uint63.of_int (1)))
       else a
  else a

(** val isort : z Marray.t -> Uint63.t -> Uint63.t -> z Marray.t **)

let rec isort a n i =
  if bdec (ltb0 i n)
  then isort (sink a i) n (add0 i (Uint63.of_int (1)))
  else a

(** val bigfactoring_impl : z -> z Marray.t **)

let bigfactoring_impl n =
  let (acc, cnt) = fac n (Zpos (XO XH)) (make cAP Z0) (Uint63.of_int (0)) in
  let out = copy acc (make cnt Z0) cnt (Uint63.of_int (0)) in
  isort out cnt (Uint63.of_int (1))

(** val bigfactoring : z -> z Marray.t **)

let bigfactoring =
  bigfactoring_impl
