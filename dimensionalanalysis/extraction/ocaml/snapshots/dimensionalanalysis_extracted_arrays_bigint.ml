
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

type uint = Uint63.t

type sint = Uint63.t

(** val zgcd : Bigint.t -> Bigint.t -> Bigint.t **)

let zgcd = Bigint.gcd

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

(** val uconv : Uint63.t -> Bigint.t **)

let rec uconv x =
  if bdec (eqb0 x (Uint63.of_int (0)))
  then Bigint.zero
  else Z.add
         (Z.mul ((fun x -> Bigint.shift_left x 1) Bigint.one)
           (uconv (div0 x (Uint63.of_int (2)))))
         (if eqb0 (mod0 x (Uint63.of_int (2))) (Uint63.of_int (0))
          then Bigint.zero
          else Bigint.one)

(** val sconv : sint -> Bigint.t **)

let sconv x =
  if ltb0 x (Uint63.of_int (-4611686018427387904))
  then uconv x
  else Z.opp (uconv (sub0 (Uint63.of_int (0)) x))

(** val ztab : Uint63.t -> Uint63.t -> sint array array -> Bigint.t array **)

let ztab n m xe =
  for_ (Uint63.of_int (0)) n
    ((fun n d -> Array.make (Uint63.hash n) d) (mul0 n m) Bigint.zero)
    (fun i t ->
    let row = (fun a i -> Array.unsafe_get a (Uint63.hash i)) xe i in
    for_ (Uint63.of_int (0)) m t (fun j t0 ->
      (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
        (add0 (mul0 i m) j)
        (sconv ((fun a i -> Array.unsafe_get a (Uint63.hash i)) row j))))

(** val upd_row :
    Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t -> Bigint.t
    array -> Bigint.t array **)

let upd_row m i s p f t =
  for_ (Uint63.of_int (0)) m t (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i m) j)
      (Z.sub
        (Z.mul p
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
            (add0 (mul0 i m) j)))
        (Z.mul f
          ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
            (add0 (mul0 s m) j)))))

(** val row_gcd : Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t **)

let row_gcd m i t =
  for_ (Uint63.of_int (0)) m Bigint.zero (fun j g ->
    zgcd g
      ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 i m) j)))

(** val div_row :
    Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t array -> Bigint.t array **)

let div_row m i g t =
  for_ (Uint63.of_int (0)) m t (fun j t0 ->
    (fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) t0
      (add0 (mul0 i m) j)
      (Z.div
        ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
          (add0 (mul0 i m) j))
        g))

(** val norm_row :
    Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array **)

let norm_row m i t =
  let g = row_gcd m i t in if Z.ltb Bigint.one g then div_row m i g t else t

(** val elim_rows :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array ->
    Bigint.t array **)

let elim_rows n m s c t =
  let p =
    (fun a i -> Array.unsafe_get a (Uint63.hash i)) t (add0 (mul0 s m) c)
  in
  for_ (Uint63.of_int (0)) n t (fun i t0 ->
    if eqb0 i s
    then t0
    else let f =
           (fun a i -> Array.unsafe_get a (Uint63.hash i)) t0
             (add0 (mul0 i m) c)
         in
         if Z.eqb f Bigint.zero
         then t0
         else norm_row m i (upd_row m i s p f t0))

(** val find_piv :
    Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array -> bool array ->
    Uint63.t **)

let find_piv n m c t u =
  for_ (Uint63.of_int (0)) n n (fun i r ->
    if eqb0 r n
    then if (fun a i -> Array.unsafe_get a (Uint63.hash i)) u i
         then r
         else if Z.eqb
                   ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
                     (add0 (mul0 i m) c))
                   Bigint.zero
              then r
              else i
    else r)

(** val col_step :
    Uint63.t -> Uint63.t -> Uint63.t -> (Bigint.t array * bool array) ->
    Bigint.t array * bool array **)

let col_step n m c st =
  let t = fst st in
  let u = snd st in
  let s = find_piv n m c t u in
  if eqb0 s n
  then st
  else ((elim_rows n m s c t),
         ((fun a i v -> Array.unsafe_set a (Uint63.hash i) v; a) u s true))

(** val count_nz : Uint63.t -> Uint63.t -> Bigint.t array -> Uint63.t **)

let count_nz m i t =
  for_ (Uint63.of_int (0)) m (Uint63.of_int (0)) (fun j k ->
    if Z.eqb
         ((fun a i -> Array.unsafe_get a (Uint63.hash i)) t
           (add0 (mul0 i m) j))
         Bigint.zero
    then k
    else add0 k (Uint63.of_int (1)))

(** val valid_impl : uint -> sint array array -> bool **)

let valid_impl xm xe =
  let n = (fun a -> Uint63.of_int (Array.length a)) xe in
  let st =
    for_ (Uint63.of_int (0)) xm ((ztab n xm xe),
      ((fun n d -> Array.make (Uint63.hash n) d) n false)) (col_step n xm)
  in
  let t = fst st in
  for_ (Uint63.of_int (0)) n true (fun i b ->
    if b then negb (eqb0 (count_nz xm i t) (Uint63.of_int (1))) else false)

(** val valid : uint -> sint array array -> bool **)

let valid =
  valid_impl
