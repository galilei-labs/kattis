
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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type sint = Uint63.t

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

(** val loop :
    (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let rec loop f hi i s =
  if bdec (ltb0 i hi)
  then loop f hi (add0 i (Uint63.of_int (1))) (f i s)
  else s

(** val for_ :
    Uint63.t -> Uint63.t -> 'a1 -> (Uint63.t -> 'a1 -> 'a1) -> 'a1 **)

let for_ lo hi s f =
  loop f hi lo s

(** val uconv : Uint63.t -> z **)

let rec uconv x =
  if bdec (eqb0 x (Uint63.of_int (0)))
  then Z0
  else Z.add (Z.mul (Zpos (XO XH)) (uconv (div0 x (Uint63.of_int (2)))))
         (if eqb0 (mod0 x (Uint63.of_int (2))) (Uint63.of_int (0))
          then Z0
          else Zpos XH)

(** val sconv : sint -> z **)

let sconv x =
  if ltb0 x (Uint63.of_int (-4611686018427387904))
  then uconv x
  else Z.opp (uconv (sub0 (Uint63.of_int (0)) x))

(** val ztab :
    Uint63.t -> Uint63.t -> sint Marray.t Marray.t -> z Marray.t **)

let ztab n m xe =
  for_ (Uint63.of_int (0)) n (make (mul0 n m) Z0) (fun i t ->
    let row = get xe i in
    for_ (Uint63.of_int (0)) m t (fun j t0 ->
      set t0 (add0 (mul0 i m) j) (sconv (get row j))))

(** val upd_row :
    Uint63.t -> Uint63.t -> Uint63.t -> z -> z -> z Marray.t -> z Marray.t **)

let upd_row m i s p f t =
  for_ (Uint63.of_int (0)) m t (fun j t0 ->
    set t0 (add0 (mul0 i m) j)
      (Z.sub (Z.mul p (get t0 (add0 (mul0 i m) j)))
        (Z.mul f (get t0 (add0 (mul0 s m) j)))))

(** val row_gcd : Uint63.t -> Uint63.t -> z Marray.t -> z **)

let row_gcd m i t =
  for_ (Uint63.of_int (0)) m Z0 (fun j g ->
    zgcd g (get t (add0 (mul0 i m) j)))

(** val div_row : Uint63.t -> Uint63.t -> z -> z Marray.t -> z Marray.t **)

let div_row m i g t =
  for_ (Uint63.of_int (0)) m t (fun j t0 ->
    set t0 (add0 (mul0 i m) j) (Z.div (get t0 (add0 (mul0 i m) j)) g))

(** val norm_row : Uint63.t -> Uint63.t -> z Marray.t -> z Marray.t **)

let norm_row m i t =
  let g = row_gcd m i t in if Z.ltb (Zpos XH) g then div_row m i g t else t

(** val elim_rows :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> z Marray.t -> z Marray.t **)

let elim_rows n m s c t =
  let p = get t (add0 (mul0 s m) c) in
  for_ (Uint63.of_int (0)) n t (fun i t0 ->
    if eqb0 i s
    then t0
    else let f = get t0 (add0 (mul0 i m) c) in
         if Z.eqb f Z0 then t0 else norm_row m i (upd_row m i s p f t0))

(** val find_piv :
    Uint63.t -> Uint63.t -> Uint63.t -> z Marray.t -> bool Marray.t ->
    Uint63.t **)

let find_piv n m c t u =
  for_ (Uint63.of_int (0)) n n (fun i r ->
    if eqb0 r n
    then if get u i
         then r
         else if Z.eqb (get t (add0 (mul0 i m) c)) Z0 then r else i
    else r)

(** val col_step :
    Uint63.t -> Uint63.t -> Uint63.t -> (z Marray.t * bool Marray.t) -> z
    Marray.t * bool Marray.t **)

let col_step n m c st =
  let t = fst st in
  let u = snd st in
  let s = find_piv n m c t u in
  if eqb0 s n then st else ((elim_rows n m s c t), (set u s true))

(** val count_nz : Uint63.t -> Uint63.t -> z Marray.t -> Uint63.t **)

let count_nz m i t =
  for_ (Uint63.of_int (0)) m (Uint63.of_int (0)) (fun j k ->
    if Z.eqb (get t (add0 (mul0 i m) j)) Z0
    then k
    else add0 k (Uint63.of_int (1)))

(** val valid_impl : uint -> sint Marray.t Marray.t -> bool **)

let valid_impl xm xe =
  let n = length xe in
  let st =
    for_ (Uint63.of_int (0)) xm ((ztab n xm xe), (make n false))
      (col_step n xm)
  in
  let t = fst st in
  for_ (Uint63.of_int (0)) n true (fun i b ->
    if b then negb (eqb0 (count_nz xm i t) (Uint63.of_int (1))) else false)

module DimensionalanalysisImpl =
 struct
  (** val valid : uint -> sint Marray.t Marray.t -> bool **)

  let valid =
    valid_impl
 end
