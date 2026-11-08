
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true



(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val mod0 : Uint63.t -> Uint63.t -> Uint63.t **)

let mod0 = Uint63.rem

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

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

(** val sqrt : Float64.t -> Float64.t **)

let sqrt = Float64.sqrt

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val wloop :
    Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
    Uint63.t -> 'a1 -> 'a1 **)

let rec wloop hi cont f i s =
  if bdec (ltb i hi)
  then if cont i s
       then wloop hi cont f (add i (Uint63.of_int (1))) (f i s)
       else s
  else s

(** val loop :
    Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
    Uint63.t -> 'a1 -> 'a1 **)

let loop =
  wloop

(** val encode : Uint63.t -> Uint63.t -> Uint63.t **)

let encode x y =
  add (mul (add x (Uint63.of_int (1000))) (Uint63.of_int (2048)))
    (add y (Uint63.of_int (1000)))

(** val kneg : Uint63.t **)

let kneg =
  (Uint63.of_int (4098000))

(** val cx : Uint63.t -> Uint63.t **)

let cx k =
  sub (div k (Uint63.of_int (2048))) (Uint63.of_int (1000))

(** val cy : Uint63.t -> Uint63.t **)

let cy k =
  sub (mod0 k (Uint63.of_int (2048))) (Uint63.of_int (1000))

(** val mcross : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let mcross a1 a2 b1 b2 =
  sub (mul (sub (cx a2) (cx a1)) (sub (cy b2) (cy b1)))
    (mul (sub (cy a2) (cy a1)) (sub (cx b2) (cx b1)))

(** val msq : Uint63.t -> Uint63.t -> Uint63.t **)

let msq a b =
  let dx = add (cx a) (cx b) in
  let dy = add (cy a) (cy b) in add (mul dx dx) (mul dy dy)

(** val key_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t **)

let key_step x y i a =
  set a i (encode (get x i) (get y i))

(** val merge_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
    (Uint63.t * Uint63.t) * Uint63.t Marray.t **)

let merge_step src mid hi k = function
| (p, d) ->
  let (i, j) = p in
  if (&&) (ltb i mid) ((||) (leb hi j) (leb (get src i) (get src j)))
  then (((add i (Uint63.of_int (1))), j), (set d k (get src i)))
  else ((i, (add j (Uint63.of_int (1)))), (set d k (get src j)))

(** val merge :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let merge src lo mid hi d =
  let (_, d0) =
    loop hi (fun _ _ -> true) (merge_step src mid hi) lo ((lo, mid), d)
  in
  d0

(** val pass_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let pass_step src n w c d =
  let lo = mul c (add w w) in
  let mid = if ltb (add lo w) n then add lo w else n in
  let hi = if ltb (add lo (add w w)) n then add lo (add w w) else n in
  merge src lo mid hi d

(** val merge_pass :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t **)

let merge_pass src d n w =
  loop (div (sub (add n (add w w)) (Uint63.of_int (1))) (add w w))
    (fun _ _ -> true) (pass_step src n w) (Uint63.of_int (0)) d

(** val msort_rec :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec msort_rec n w a b =
  if bdec ((&&) (ltb w n) (ltb w (add w w)))
  then msort_rec n (add w w) (merge_pass a b n w) a
  else a

(** val msort : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let msort a n =
  msort_rec n (Uint63.of_int (1)) a (make n (Uint63.of_int (0)))

(** val dedup_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) ->
    Uint63.t Marray.t * Uint63.t **)

let dedup_step a i = function
| (q, m) ->
  let a0 = get a i in
  if eqb a0 (get q (sub m (Uint63.of_int (1))))
  then (q, m)
  else ((set q m a0), (add m (Uint63.of_int (1))))

(** val neg_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let neg_step q m i b =
  set b i (sub kneg (get q (sub (sub m (Uint63.of_int (1))) i)))

(** val pops : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec pops st c t =
  if bdec
       ((&&) (ltb (Uint63.of_int (1)) t)
         (negb
           (ltsb (Uint63.of_int (0))
             (mcross (get st (sub t (Uint63.of_int (2))))
               (get st (sub t (Uint63.of_int (1))))
               (get st (sub t (Uint63.of_int (2)))) c))))
  then pops st c (sub t (Uint63.of_int (1)))
  else t

(** val chain_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) ->
    Uint63.t Marray.t * Uint63.t **)

let chain_step q i = function
| (st0, t) ->
  let c = get q i in
  let t0 = pops st0 c t in ((set st0 t0 c), (add t0 (Uint63.of_int (1))))

(** val chain :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let chain q m =
  loop m (fun _ _ -> true) (chain_step q) (Uint63.of_int (1))
    ((make m (get q (Uint63.of_int (0)))), (Uint63.of_int (1)))

(** val cal_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> ((Uint63.t * Uint63.t) * Uint63.t) ->
    (Uint63.t * Uint63.t) * Uint63.t **)

let cal_step l n lL lN _ = function
| (p, best) ->
  let (j, k) = p in
  let d = msq (get l j) (get n k) in
  let best0 = if ltb best d then d else best in
  if (&&) (ltb j lL)
       ((||) (eqb k lN)
         (ltsb (Uint63.of_int (0))
           (mcross (get l j) (get l (add j (Uint63.of_int (1)))) (get n k)
             (get n (add k (Uint63.of_int (1)))))))
  then (((add j (Uint63.of_int (1))), k), best0)
  else ((j, (add k (Uint63.of_int (1)))), best0)

(** val calipers :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let calipers l n lL lN =
  let (p, best) =
    loop (add lL lN) (fun _ _ -> true) (cal_step l n lL lN)
      (Uint63.of_int (0)) (((Uint63.of_int (0)), (Uint63.of_int (0))),
      (Uint63.of_int (0)))
  in
  let (j, k) = p in
  let d = msq (get l j) (get n k) in if ltb best d then d else best

(** val diam2 : Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t **)

let diam2 x y =
  let n = length x in
  let a =
    loop n (fun _ _ -> true) (key_step x y) (Uint63.of_int (0))
      (make n (Uint63.of_int (0)))
  in
  let a0 = msort a n in
  let (q, m) =
    loop n (fun _ _ -> true) (dedup_step a0) (Uint63.of_int (1))
      ((make n (get a0 (Uint63.of_int (0)))), (Uint63.of_int (1)))
  in
  if ltb m (Uint63.of_int (2))
  then (Uint63.of_int (0))
  else let q2 =
         loop m (fun _ _ -> true) (neg_step q m) (Uint63.of_int (0))
           (make m (Uint63.of_int (0)))
       in
       let (l, tL) = chain q m in
       let (n0, tN) = chain q2 m in
       calipers l n0 (sub tL (Uint63.of_int (1))) (sub tN (Uint63.of_int (1)))

(** val roberthood : sint Marray.t -> sint Marray.t -> Float64.t **)

let roberthood x y =
  sqrt (of_uint63 (diam2 x y))
