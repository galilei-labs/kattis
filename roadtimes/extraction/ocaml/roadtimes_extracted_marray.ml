
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

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)



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
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
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
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q0 =
    match p with
    | XI p0 -> (match q0 with
                | XI q1 -> eqb p0 q1
                | _ -> false)
    | XO p0 -> (match q0 with
                | XO q1 -> eqb p0 q1
                | _ -> false)
    | XH -> (match q0 with
             | XH -> true
             | _ -> false)
 end

module Coq_Pos =
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
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y
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
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
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
                 | Zpos q0 -> Pos.eqb p q0
                 | _ -> false)
    | Zneg p -> (match y with
                 | Zneg q0 -> Pos.eqb p q0
                 | _ -> false)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val pos_div_eucl : positive -> z -> z * z **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (XO XH)) r) (Zpos XH) in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
    | XO a' ->
      let (q0, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (XO XH)) r in
      if ltb r' b
      then ((mul (Zpos (XO XH)) q0), r')
      else ((add (mul (Zpos (XO XH)) q0) (Zpos XH)), (sub r' b))
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
         let (q0, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> (Z0, a)
       | Zpos _ ->
         let (q0, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> ((opp q0), Z0)
          | _ -> ((opp (add q0 (Zpos XH))), (sub b r)))
       | Zneg b' -> let (q0, r) = pos_div_eucl a' (Zpos b') in (q0, (opp r)))

  (** val div : z -> z -> z **)

  let div a b =
    let (q0, _) = div_eucl a b in q0

  (** val modulo : z -> z -> z **)

  let modulo a b =
    let (_, r) = div_eucl a b in r

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val copy : 'a1 Marray.t -> 'a1 Marray.t **)

let copy = Marray.copy

(** val div1 : Float64.t -> Float64.t -> Float64.t **)

let div1 = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

(** val zero : Float64.t **)

let zero =
  (Float64.of_float (0x0p+0))

type q = { qnum : z; qden : positive }

(** val inject_Z : z -> q **)

let inject_Z x =
  { qnum = x; qden = XH }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

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
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

type uint = Uint63.t

type sint = Uint63.t

(** val zgcd_loop : z -> z -> z **)

let rec zgcd_loop a b =
  if Z.ltb Z0 b then zgcd_loop b (Z.modulo a b) else a

(** val zgcd : z -> z -> z **)

let zgcd a b =
  zgcd_loop (Z.abs a) (Z.abs b)

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

(** val zofs : Uint63.t -> z **)

let zofs i =
  if ltb0 i (Uint63.of_int (-4611686018427387904))
  then zofi i
  else Z.sub (zofi i) (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         XH))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val iofz_rec : z -> Uint63.t **)

let rec iofz_rec z0 =
  if bdec (Z.ltb Z0 z0)
  then let r = iofz_rec (Z.div z0 (Zpos (XO XH))) in
       if Z.eqb (Z.modulo z0 (Zpos (XO XH))) Z0
       then add0 r r
       else add0 (add0 r r) (Uint63.of_int (1))
  else (Uint63.of_int (0))

(** val iofz : z -> Uint63.t **)

let iofz =
  iofz_rec

(** val qred : q -> q **)

let qred q0 =
  let n = q0.qnum in
  let d = Zpos q0.qden in
  let g = zgcd n d in { qnum = (Z.div n g); qden = (Z.to_pos (Z.div d g)) }

(** val qsub : q -> q -> q **)

let qsub a b =
  qred (qminus a b)

(** val qmul : q -> q -> q **)

let qmul a b =
  qred (qmult a b)

(** val qltb : q -> q -> bool **)

let qltb a b =
  Z.ltb (Z.mul a.qnum (Zpos b.qden)) (Z.mul b.qnum (Zpos a.qden))

(** val qzerob : q -> bool **)

let qzerob a =
  Z.eqb a.qnum Z0

type sState = (q Marray.t * q Marray.t) * Uint63.t Marray.t

(** val sT : sState -> q Marray.t **)

let sT st =
  fst (fst st)

(** val sO : sState -> q Marray.t **)

let sO st =
  snd (fst st)

(** val sB : sState -> Uint63.t Marray.t **)

let sB =
  snd

(** val lc : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let lc n e0 p =
  if eqb0 p (Uint63.of_int (0))
  then n
  else sub0 (add0 e0 p) (Uint63.of_int (1))

(** val enter : Uint63.t -> bool Marray.t -> q Marray.t -> Uint63.t option **)

let enter n al o =
  loop n (fun _ st -> match st with
                      | Some _ -> false
                      | None -> true)
    (fun j _ ->
    if (&&) (get al j) (qltb (get o j) { qnum = Z0; qden = XH })
    then Some j
    else None) (Uint63.of_int (0)) None

(** val lexless :
    q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let lexless t w n e0 m k r s =
  let tks = get t (add0 (mul0 k w) s) in
  let trs = get t (add0 (mul0 r w) s) in
  let st =
    loop (add0 m (Uint63.of_int (1))) (fun _ st ->
      eqb0 st (Uint63.of_int (0))) (fun p _ ->
      let c = lc n e0 p in
      let a = qmult (get t (add0 (mul0 k w) c)) trs in
      let b = qmult (get t (add0 (mul0 r w) c)) tks in
      if qltb a b
      then (Uint63.of_int (1))
      else if qltb b a then (Uint63.of_int (2)) else (Uint63.of_int (0)))
      (Uint63.of_int (0)) (Uint63.of_int (0))
  in
  eqb0 st (Uint63.of_int (1))

(** val leave :
    q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t option **)

let leave t w n e0 m s =
  forl (Uint63.of_int (0)) m (fun k best ->
    if qltb { qnum = Z0; qden = XH } (get t (add0 (mul0 k w) s))
    then (match best with
          | Some r -> if lexless t w n e0 m k r s then Some k else Some r
          | None -> Some k)
    else best) None

(** val scale_row : q Marray.t -> Uint63.t -> Uint63.t -> q -> q Marray.t **)

let scale_row t w r inv =
  forl (Uint63.of_int (0)) w (fun j t0 ->
    set t0 (add0 (mul0 r w) j) (qmul (get t0 (add0 (mul0 r w) j)) inv)) t

(** val elim_row :
    q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> q -> q Marray.t **)

let elim_row t w r k f =
  forl (Uint63.of_int (0)) w (fun j t0 ->
    let a = get t0 (add0 (mul0 r w) j) in
    if qzerob a
    then t0
    else set t0 (add0 (mul0 k w) j)
           (qsub (get t0 (add0 (mul0 k w) j)) (qmult f a)))
    t

(** val elim_all :
    q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> q Marray.t **)

let elim_all t w m r s =
  forl (Uint63.of_int (0)) m (fun k t0 ->
    if eqb0 k r
    then t0
    else let f = get t0 (add0 (mul0 k w) s) in
         if qzerob f then t0 else elim_row t0 w r k f)
    t

(** val elim_obj :
    q Marray.t -> q Marray.t -> Uint63.t -> Uint63.t -> q -> q Marray.t **)

let elim_obj o t w r f =
  forl (Uint63.of_int (0)) w (fun j o0 ->
    let a = get t (add0 (mul0 r w) j) in
    if qzerob a then o0 else set o0 j (qsub (get o0 j) (qmult f a))) o

(** val pivot :
    Uint63.t -> Uint63.t -> sState -> Uint63.t -> Uint63.t -> sState **)

let pivot w m st r s =
  let t = sT st in
  let o = sO st in
  let b = sB st in
  let t1 = scale_row t w r (qinv (get t (add0 (mul0 r w) s))) in
  let t2 = elim_all t1 w m r s in
  let o2 = elim_obj o t2 w r (get o s) in ((t2, o2), (set b r s))

(** val sloop : Uint63.t -> Uint63.t -> bool Marray.t -> sState -> sState **)

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
    q Marray.t -> Uint63.t Marray.t -> q Marray.t -> Uint63.t -> Uint63.t ->
    q Marray.t **)

let canon_obj t b c w m =
  forl (Uint63.of_int (0)) m (fun k o ->
    let f = get c (get b k) in if qzerob f then o else elim_obj o t w k f)
    (copy c)

(** val binit : Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let binit m e0 =
  forl (Uint63.of_int (0)) m (fun k b -> set b k (add0 e0 k))
    (make m (Uint63.of_int (0)))

(** val cart : Uint63.t -> Uint63.t -> Uint63.t -> q Marray.t **)

let cart w a0 n =
  forl a0 n (fun j c -> set c j { qnum = (Zpos XH); qden = XH })
    (make w { qnum = Z0; qden = XH })

(** val st0 : q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> sState **)

let st0 t0 m e0 a0 =
  let b0 = binit m e0 in
  ((t0,
  (canon_obj t0 b0
    (cart (add0 (add0 e0 m) (Uint63.of_int (1))) a0 (add0 e0 m))
    (add0 (add0 e0 m) (Uint63.of_int (1))) m)),
  b0)

(** val phase1 : q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> sState **)

let phase1 t0 m e0 a0 =
  sloop m e0 (make (add0 e0 m) true) (st0 t0 m e0 a0)

(** val al2 : q Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t **)

let al2 o1 a0 n =
  forl (Uint63.of_int (0)) n (fun j a ->
    set a j ((&&) (ltb0 j a0) (qzerob (get o1 j)))) (make n false)

(** val mk2 : sState -> q Marray.t -> Uint63.t -> Uint63.t -> sState **)

let mk2 st1 carr w m =
  (((copy (sT st1)), (canon_obj (sT st1) (sB st1) carr w m)), (copy (sB st1)))

(** val phase2 :
    q Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> sState -> bool Marray.t
    -> q Marray.t -> q **)

let phase2 _ m e0 _ st1 al carr =
  if bdec
       ((&&) (eqb0 (length carr) (add0 (add0 e0 m) (Uint63.of_int (1))))
         (qzerob (get carr (add0 e0 m))))
  then let st3 =
         sloop m e0 al (mk2 st1 carr (add0 (add0 e0 m) (Uint63.of_int (1))) m)
       in
       qopp (get (sO st3) (add0 e0 m))
  else { qnum = Z0; qden = XH }

(** val fill2 :
    Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t) -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let fill2 n g a =
  forl (Uint63.of_int (0)) n (fun i a0 ->
    forl (Uint63.of_int (0)) n (fun j a1 ->
      set a1 (add0 (mul0 i n) j) (g i j)) a0)
    a

(** val flatten :
    Uint63.t -> Uint63.t Marray.t Marray.t -> Uint63.t Marray.t **)

let flatten n x =
  fill2 n (fun i j -> get (get x i) j) (make (mul0 n n) (Uint63.of_int (0)))

(** val isroad : Uint63.t -> bool **)

let isroad e =
  ltsb (Uint63.of_int (0)) e

(** val iNF : Uint63.t **)

let iNF =
  (Uint63.of_int (1073741824))

(** val fw_cell :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t * Uint63.t Marray.t **)

let fw_cell n k i j st =
  let d = fst st in
  let x = snd st in
  let a = add0 (get d (add0 (mul0 i n) k)) (get d (add0 (mul0 k n) j)) in
  if ltb0 a (get d (add0 (mul0 i n) j))
  then ((set d (add0 (mul0 i n) j) a),
         (set x (add0 (mul0 i n) j) (get x (add0 (mul0 i n) k))))
  else st

(** val fw_iter :
    Uint63.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let fw_iter n k st =
  forl (Uint63.of_int (0)) n (fun i st1 ->
    forl (Uint63.of_int (0)) n (fun j st2 -> fw_cell n k i j st2) st1) st

(** val fw :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let fw n w =
  let d0 =
    fill2 n (fun i j ->
      if eqb0 i j
      then (Uint63.of_int (0))
      else if isroad (get w (add0 (mul0 i n) j))
           then get w (add0 (mul0 i n) j)
           else iNF)
      (make (mul0 n n) (Uint63.of_int (0)))
  in
  let x0 = fill2 n (fun _ j -> j) (make (mul0 n n) (Uint63.of_int (0))) in
  forl (Uint63.of_int (0)) n (fun k st -> fw_iter n k st) (d0, x0)

(** val scan_roads :
    Uint63.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) * Uint63.t **)

let scan_roads n w =
  forl (Uint63.of_int (0)) (mul0 n n) (fun p st ->
    let i = fst (fst st) in
    let p0 = snd (fst st) in
    let e = snd st in
    if isroad (get w p)
    then (((set i p e), (set p0 e p)), (add0 e (Uint63.of_int (1))))
    else st) (((make (mul0 n n) (Uint63.of_int (0))),
    (make (mul0 n n) (Uint63.of_int (0)))), (Uint63.of_int (0)))

(** val walk :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec walk n d e d0 x i cur cnt =
  if eqb0 cur d
  then cnt
  else let v = get x (add0 (mul0 cur n) d) in
       if bdec
            (ltb0 (get d0 (add0 (mul0 v n) d)) (get d0 (add0 (mul0 cur n) d)))
       then let e0 = get i (add0 (mul0 cur n) v) in
            walk n d e d0 x i v
              (if ltb0 e0 e
               then set cnt e0 (add0 (get cnt e0) (Uint63.of_int (1)))
               else cnt)
       else cnt

(** val route_cnt :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let route_cnt n e d x i s d0 =
  walk n d0 e d x i s (make e (Uint63.of_int (0)))

(** val bound_rows :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> q Marray.t -> q Marray.t **)

let bound_rows e w n w0 p t =
  forl (Uint63.of_int (0)) e (fun e0 t0 ->
    let u = get w0 (get p e0) in
    let t1 = set t0 (add0 (mul0 e0 w) e0) { qnum = (Zpos XH); qden = XH } in
    let t2 =
      set t1 (add0 (mul0 e0 w) (add0 e e0)) { qnum = (Zpos XH); qden = XH }
    in
    set t2 (add0 (mul0 e0 w) n)
      (if isroad u then inject_Z (zofs u) else { qnum = Z0; qden = XH }))
    t

(** val deliv_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> q Marray.t -> q Marray.t **)

let deliv_row n e w n0 d x i rs rd rt k t =
  let s = get rs k in
  let d0 = get rd k in
  let cnt = route_cnt n e d x i s d0 in
  let b = Z.sub (zofi (get rt k)) (zofi (get d (add0 (mul0 s n) d0))) in
  let i0 = add0 e k in
  let t0 =
    forl (Uint63.of_int (0)) e (fun e0 t0 ->
      set t0 (add0 (mul0 i0 w) e0)
        (inject_Z
          (if Z.ltb b Z0 then Z.opp (zofi (get cnt e0)) else zofi (get cnt e0))))
      t
  in
  let t1 =
    set t0 (add0 (mul0 i0 w) (add0 (add0 e e) k)) { qnum = (Zpos XH); qden =
      XH }
  in
  set t1 (add0 (mul0 i0 w) n0) (inject_Z (Z.abs b))

(** val build_T :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> q
    Marray.t **)

let build_T n e r w d x i p rs rd rt =
  let m = add0 e r in
  let w0 = add0 (add0 e m) (Uint63.of_int (1)) in
  let n0 = add0 e m in
  let t = bound_rows e w0 n0 w p (make (mul0 m w0) { qnum = Z0; qden = XH })
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

(** val qcost :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> bool -> q Marray.t **)

let qcost e w cnt neg =
  forl (Uint63.of_int (0)) e (fun e0 c ->
    set c e0
      (inject_Z
        (if neg then Z.opp (zofi (get cnt e0)) else zofi (get cnt e0))))
    (make w { qnum = Z0; qden = XH })

(** val two36 : Uint63.t **)

let two36 =
  (Uint63.of_int (68719476736))

(** val q2f : q -> Float64.t **)

let q2f q0 =
  let mz =
    Z.div
      (Z.mul q0.qnum (Zpos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
        (XO (XO (XO (XO (XO (XO (XO XH))))))))))))))))))))))))))))))))))))))
      (Zpos q0.qden)
  in
  div1 (of_uint63 (iofz mz)) (of_uint63 two36)

(** val aget : Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let aget =
  get

(** val dq : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> q **)

let dq n d s d0 =
  inject_Z (zofi (get d (add0 (mul0 s n) d0)))

(** val vq :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> q Marray.t -> sState -> bool Marray.t ->
    Uint63.t -> Uint63.t -> bool -> q **)

let vq n e rR d x i t0 st1 al s d0 neg =
  phase2 t0 (add0 e rR) e (add0 e e) st1 al
    (qcost e (add0 (add0 e (add0 e rR)) (Uint63.of_int (1)))
      (route_cnt n e d x i s d0) neg)

(** val qans :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> q Marray.t -> sState -> bool Marray.t ->
    Uint63.t -> Uint63.t -> Float64.t * Float64.t **)

let qans n e rR d x i t0 st1 al s d0 =
  ((q2f (qplus (dq n d s d0) (vq n e rR d x i t0 st1 al s d0 false))),
    (q2f (qminus (dq n d s d0) (vq n e rR d x i t0 st1 al s d0 true))))

(** val answers :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> q Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> (Float64.t * Float64.t) Marray.t **)

let answers n e rR d x i t0 xqs xqd =
  let st1 = phase1 t0 (add0 e rR) e (add0 e e) in
  let al = al2 (sO st1) (add0 e e) (add0 e (add0 e rR)) in
  forl (Uint63.of_int (0)) (length xqs) (fun j out ->
    set out j (qans n e rR d x i t0 st1 al (aget xqs j) (aget xqd j)))
    (make (length xqs) (zero, zero))

(** val roadtimes_impl :
    sint Marray.t Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> uint Marray.t -> uint Marray.t -> (Float64.t * Float64.t) Marray.t **)

let roadtimes_impl xdist xrs xrd xrt xqs xqd =
  let n = length xdist in
  let w = flatten n xdist in
  let fW = fw n w in
  let d = fst fW in
  let x = snd fW in
  let sR = scan_roads n w in
  let i = fst (fst sR) in
  let p = snd (fst sR) in
  let e = snd sR in
  let rR = length xrs in
  if bdec (guard e rR)
  then let t0 = build_T n e rR w d x i p xrs xrd xrt in
       answers n e rR d x i t0 xqs xqd
  else make (length xqs) (zero, zero)

(** val roadtimes :
    sint Marray.t Marray.t -> uint Marray.t -> uint Marray.t -> uint Marray.t
    -> uint Marray.t -> uint Marray.t -> (Float64.t * Float64.t) Marray.t **)

let roadtimes =
  roadtimes_impl
