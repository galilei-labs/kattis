
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
 end

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

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb0 : Uint63.t -> Uint63.t -> bool **)

let leb0 = Uint63.le

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val gloop :
    Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1)
    -> Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1 **)

let rec gloop c n f u i j a =
  if bdec (ltb u n)
  then let a' = f u i j a in
       let j1 = add0 j (Uint63.of_int (1)) in
       let e = eqb j1 c in
       gloop c n f (add0 u (Uint63.of_int (1)))
         (if e then add0 i (Uint63.of_int (1)) else i)
         (if e then (Uint63.of_int (0)) else j1) a'
  else a

(** val grid_fold :
    Uint63.t -> Uint63.t -> (Uint63.t -> Uint63.t -> Uint63.t -> 'a1 -> 'a1)
    -> 'a1 -> 'a1 **)

let grid_fold c n f a =
  gloop c n f (Uint63.of_int (0)) (Uint63.of_int (0)) (Uint63.of_int (0)) a

(** val m48 : Uint63.t **)

let m48 =
  (Uint63.of_int (281474976710656))

(** val absdiff : Uint63.t -> Uint63.t -> Uint63.t **)

let absdiff a b =
  if ltb a b then sub b a else sub a b

(** val denom :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let denom hh i j i' j' =
  let di = absdiff i i' in
  let dj = absdiff j j' in add0 (add0 (mul0 di di) (mul0 dj dj)) hh

(** val lo_sum :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let lo_sum s c n hh i j =
  grid_fold c n (fun u i' j' acc ->
    add0 acc (div (mul0 m48 (get s u)) (denom hh i j i' j')))
    (Uint63.of_int (0))

(** val zofint_aux : Uint63.t -> z **)

let rec zofint_aux x =
  if bdec (eqb x (Uint63.of_int (0)))
  then Z0
  else let r = zofint_aux (div x (Uint63.of_int (2))) in
       if eqb (mod0 x (Uint63.of_int (2))) (Uint63.of_int (0))
       then Z.mul (Zpos (XO XH)) r
       else Z.add (Z.mul (Zpos (XO XH)) r) (Zpos XH)

(** val zofint : Uint63.t -> z **)

let zofint =
  zofint_aux

(** val exact_sum :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> z * z **)

let exact_sum s c n hh i j =
  grid_fold c n (fun u i' j' pq ->
    let d = zofint (denom hh i j i' j') in
    let sv = zofint (get s u) in
    ((Z.add (Z.mul (fst pq) d) (Z.mul sv (snd pq))), (Z.mul (snd pq) d)))
    (Z0, (Zpos XH))

(** val lit_cell :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let lit_cell s c n b hh i j =
  let lo = lo_sum s c n hh i j in
  let mb = mul0 m48 b in
  if leb0 mb lo
  then true
  else if ltb (add0 lo n) mb
       then false
       else let pq = exact_sum s c n hh i j in
            Z.leb (Z.mul (zofint b) (snd pq)) (fst pq)

(** val lit_arr :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool
    Marray.t **)

let lit_arr s c n b hh =
  grid_fold c n (fun u i j a -> set a u (lit_cell s c n b hh i j))
    (make n false)

(** val flat :
    Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let flat xg c n =
  grid_fold c n (fun u i j a -> set a u (get (get xg i) j))
    (make n (Uint63.of_int (0)))

(** val capf : bool -> bool -> Uint63.t **)

let capf x y =
  if (&&) x y then (Uint63.of_int (43)) else (Uint63.of_int (11))

(** val init_res :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let init_res lt c n =
  grid_fold c n (fun u _ _ r ->
    let c1 = capf (get lt u) (get lt (add0 u (Uint63.of_int (1)))) in
    let c2 = capf (get lt u) (get lt (add0 u c)) in
    set (set r (mul0 (Uint63.of_int (2)) u) c1)
      (add0 (mul0 (Uint63.of_int (2)) u) (Uint63.of_int (1))) c2)
    (make (mul0 (Uint63.of_int (2)) n) (Uint63.of_int (0)))

(** val nbr : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let nbr c p d =
  if eqb d (Uint63.of_int (0))
  then add0 p (Uint63.of_int (1))
  else if eqb d (Uint63.of_int (1))
       then sub p (Uint63.of_int (1))
       else if eqb d (Uint63.of_int (2)) then add0 p c else sub p c

(** val opp : Uint63.t -> Uint63.t **)

let opp d =
  if eqb d (Uint63.of_int (0))
  then (Uint63.of_int (1))
  else if eqb d (Uint63.of_int (1))
       then (Uint63.of_int (0))
       else if eqb d (Uint63.of_int (2))
            then (Uint63.of_int (3))
            else (Uint63.of_int (2))

(** val slot : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let slot c p d =
  if eqb d (Uint63.of_int (0))
  then mul0 (Uint63.of_int (2)) p
  else if eqb d (Uint63.of_int (1))
       then mul0 (Uint63.of_int (2)) (sub p (Uint63.of_int (1)))
       else if eqb d (Uint63.of_int (2))
            then add0 (mul0 (Uint63.of_int (2)) p) (Uint63.of_int (1))
            else add0 (mul0 (Uint63.of_int (2)) (sub p c)) (Uint63.of_int (1))

(** val fwd : Uint63.t -> bool **)

let fwd d =
  (||) (eqb d (Uint63.of_int (0))) (eqb d (Uint63.of_int (2)))

(** val resid :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let resid lt res c p d =
  let k = slot c p d in
  if fwd d
  then get res k
  else sub (mul0 (Uint63.of_int (2)) (capf (get lt p) (get lt (nbr c p d))))
         (get res k)

(** val aug :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let aug res c p d dl =
  let k = slot c p d in
  if fwd d
  then set res k (sub (get res k) dl)
  else set res k (add0 (get res k) dl)

type bst = { bd : Uint63.t Marray.t; bp : Uint63.t Marray.t;
             bq : Uint63.t Marray.t; bt : Uint63.t }

(** val visit :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> bst -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool -> bst **)

let visit lt res c st v dv d = function
| true ->
  let w = nbr c v d in
  if ltb (Uint63.of_int (0)) (resid lt res c v d)
  then if eqb (get st.bd w) (Uint63.of_int (0))
       then { bd = (set st.bd w (add0 dv (Uint63.of_int (1)))); bp =
              (set st.bp w d); bq = (set st.bq st.bt w); bt =
              (add0 st.bt (Uint63.of_int (1))) }
       else st
  else st
| false -> st

(** val bfs_loop :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    bst -> bst **)

let rec bfs_loop lt res c n head st =
  if bdec (ltb head n)
  then if ltb head st.bt
       then let v = get st.bq head in
            let dv = get st.bd v in
            let j = mod0 v c in
            let st1 =
              visit lt res c st v dv (Uint63.of_int (0))
                (ltb (add0 j (Uint63.of_int (1))) c)
            in
            let st2 =
              visit lt res c st1 v dv (Uint63.of_int (1))
                (ltb (Uint63.of_int (0)) j)
            in
            let st3 =
              visit lt res c st2 v dv (Uint63.of_int (2)) (ltb (add0 v c) n)
            in
            let st4 = visit lt res c st3 v dv (Uint63.of_int (3)) (leb0 c v)
            in
            bfs_loop lt res c n (add0 head (Uint63.of_int (1))) st4
       else st
  else st

(** val root_step :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> bst -> bst **)

let root_step lt u _ _ st =
  if get lt u
  then st
  else { bd = (set st.bd u (Uint63.of_int (1))); bp =
         (set st.bp u (Uint63.of_int (4))); bq = (set st.bq st.bt u); bt =
         (add0 st.bt (Uint63.of_int (1))) }

(** val roots : bool Marray.t -> Uint63.t -> Uint63.t -> bst **)

let roots lt c n =
  grid_fold c n (root_step lt) { bd = (make n (Uint63.of_int (0))); bp =
    (make n (Uint63.of_int (0))); bq = (make n (Uint63.of_int (0))); bt =
    (Uint63.of_int (0)) }

(** val bfs :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bst **)

let bfs lt res c n =
  bfs_loop lt res c n (Uint63.of_int (0)) (roots lt c n)

(** val is_border : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let is_border r c i j =
  (||)
    ((||)
      ((||) (eqb i (Uint63.of_int (0))) (eqb i (sub r (Uint63.of_int (1)))))
      (eqb j (Uint63.of_int (0))))
    (eqb j (sub c (Uint63.of_int (1))))

(** val fb_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let fb_step dist r c n u i j acc =
  if (&&)
       ((&&) (is_border r c i j)
         (negb (eqb (get dist u) (Uint63.of_int (0)))))
       ((||) (eqb acc n) (ltb (get dist u) (get dist acc)))
  then u
  else acc

(** val find_border :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let find_border dist r c n =
  grid_fold c n (fb_step dist r c n) n

(** val tmin :
    bool Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec tmin lt res c par dist v dl =
  let d = get par v in
  if ltb d (Uint63.of_int (4))
  then let p = nbr c v (opp d) in
       if bdec (ltb (get dist p) (get dist v))
       then let r = resid lt res c p d in
            tmin lt res c par dist p (if ltb r dl then r else dl)
       else dl
  else dl

(** val tapp :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec tapp c par dist dl v res =
  let d = get par v in
  if ltb d (Uint63.of_int (4))
  then let p = nbr c v (opp d) in
       if bdec (ltb (get dist p) (get dist v))
       then tapp c par dist dl p (aug res c p d dl)
       else res
  else res

(** val flow_loop :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t **)

let rec flow_loop lt r c n b res f =
  let st = bfs lt res c n in
  let w = find_border st.bd r c n in
  if eqb w n
  then f
  else let dl = tmin lt res c st.bp st.bd w (Uint63.of_int (1000)) in
       let res' = tapp c st.bp st.bd dl w res in
       let f' = add0 f dl in
       if bdec ((&&) (ltb f f') (leb0 f' b))
       then flow_loop lt r c n b res' f'
       else f

(** val darkness_impl : uint -> uint -> uint Marray.t Marray.t -> uint **)

let darkness_impl xb xh xg =
  let r = length xg in
  let c = length (get xg (Uint63.of_int (0))) in
  let n = mul0 r c in
  let s = flat xg c n in
  let lt = lit_arr s c n xb (mul0 xh xh) in
  let res = init_res lt c n in
  let b = mul0 (Uint63.of_int (86)) n in
  flow_loop lt r c n b res (Uint63.of_int (0))

(** val darkness : uint -> uint -> uint Marray.t Marray.t -> uint **)

let darkness =
  darkness_impl
