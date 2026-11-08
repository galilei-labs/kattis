
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

(** val ltb0 : Float64.t -> Float64.t -> bool **)

let ltb0 = Float64.lt

(** val leb0 : Float64.t -> Float64.t -> bool **)

let leb0 = Float64.le

type uint = Uint63.t

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

(** val iota : Uint63.t -> Uint63.t Marray.t **)

let iota n =
  loop n (fun _ _ -> true) (fun i a -> set a i i) (Uint63.of_int (0))
    (make n (Uint63.of_int (0)))

(** val merge_step :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
    (Uint63.t * Uint63.t) * Uint63.t Marray.t **)

let merge_step le src mid hi k = function
| (p, dst) ->
  let (i, j) = p in
  if ltb i mid
  then if ltb j hi
       then if le (get src i) (get src j)
            then (((add i (Uint63.of_int (1))), j), (set dst k (get src i)))
            else ((i, (add j (Uint63.of_int (1)))), (set dst k (get src j)))
       else (((add i (Uint63.of_int (1))), j), (set dst k (get src i)))
  else ((i, (add j (Uint63.of_int (1)))), (set dst k (get src j)))

(** val merge :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let merge le src dst lo mid hi =
  snd
    (loop hi (fun _ _ -> true) (merge_step le src mid hi) lo ((lo, mid), dst))

(** val seg_mid : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let seg_mid n w lo =
  if ltb (add lo w) n then add lo w else n

(** val pass :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let pass le n w src dst =
  let w2 = add w w in
  loop (div (sub (add n w2) (Uint63.of_int (1))) w2) (fun _ _ -> true)
    (fun s d ->
    let lo = mul s w2 in merge le src d lo (seg_mid n w lo) (seg_mid n w2 lo))
    (Uint63.of_int (0)) dst

(** val msort :
    (Uint63.t -> Uint63.t -> bool) -> Uint63.t -> Uint63.t Marray.t **)

let msort le n =
  snd
    (fst
      (loop (Uint63.of_int (23)) (fun _ st -> ltb (fst (fst st)) n)
        (fun _ st ->
        let (p, dst) = st in
        let (w, src) = p in (((add w w), (pass le n w src dst)), src))
        (Uint63.of_int (0)) (((Uint63.of_int (1)), (iota n)),
        (make n (Uint63.of_int (0))))))

(** val bs :
    Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec bs p p0 v lo hi =
  if bdec (ltb lo hi)
  then if ltb0
            (get p (get p0 (add lo (div (sub hi lo) (Uint63.of_int (2)))))) v
       then bs p p0 v
              (add (add lo (div (sub hi lo) (Uint63.of_int (2))))
                (Uint63.of_int (1)))
              hi
       else bs p p0 v lo (add lo (div (sub hi lo) (Uint63.of_int (2))))
  else lo

(** val lbound :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Float64.t ->
    Uint63.t **)

let lbound p p0 n v =
  bs p p0 v (Uint63.of_int (0)) n

(** val mk_ids :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let mk_ids p p0 n =
  loop n (fun _ _ -> true) (fun i a -> set a i (lbound p p0 n (get p i)))
    (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val blk : Uint63.t -> Uint63.t **)

let blk n =
  loop n (fun _ b -> ltb (mul b b) n) (fun _ b -> add b (Uint63.of_int (1)))
    (Uint63.of_int (0)) (Uint63.of_int (1))

(** val mo_le :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let mo_le ls rs b a b0 =
  let ba = div (sub (get ls a) (Uint63.of_int (1))) b in
  let bb = div (sub (get ls b0) (Uint63.of_int (1))) b in
  if ltb ba bb
  then true
  else if ltb bb ba then false else leb (get rs a) (get rs b0)

(** val add0 :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let add0 ids pos cnt ge =
  let v = get ids pos in
  let c = add (get cnt v) (Uint63.of_int (1)) in
  ((set cnt v c), (set ge c (add (get ge c) (Uint63.of_int (1)))))

(** val rem :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rem ids pos cnt ge =
  let v = get ids pos in
  let c = get cnt v in
  ((set cnt v (sub c (Uint63.of_int (1)))),
  (set ge c (sub (get ge c) (Uint63.of_int (1)))))

(** val move :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t ->
    ((Uint63.t * Uint63.t) * Uint63.t Marray.t) * Uint63.t Marray.t **)

let rec move ids tl tr l r cnt ge =
  if bdec (ltb tl l)
  then let (c, g) = add0 ids (sub l (Uint63.of_int (1))) cnt ge in
       move ids tl tr (sub l (Uint63.of_int (1))) r c g
  else if bdec (ltb r tr)
       then let (c, g) = add0 ids r cnt ge in
            move ids tl tr l (add r (Uint63.of_int (1))) c g
       else if bdec (ltb l tl)
            then let (c, g) = rem ids l cnt ge in
                 move ids tl tr (add l (Uint63.of_int (1))) r c g
            else if bdec (ltb tr r)
                 then let (c, g) = rem ids (sub r (Uint63.of_int (1))) cnt ge
                      in
                      move ids tl tr l (sub r (Uint63.of_int (1))) c g
                 else (((l, r), cnt), ge)

(** val mo_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> ((((Uint63.t * Uint63.t) * Uint63.t
    Marray.t) * Uint63.t Marray.t) * bool Marray.t) ->
    (((Uint63.t * Uint63.t) * Uint63.t Marray.t) * Uint63.t Marray.t) * bool
    Marray.t **)

let mo_step ids ls rs q k = function
| (p, ans) ->
  let (p0, ge) = p in
  let (p1, cnt) = p0 in
  let (l, r) = p1 in
  let q0 = get q k in
  let tl = sub (get ls q0) (Uint63.of_int (1)) in
  let tr = get rs q0 in
  let (p2, ge') = move ids tl tr l r cnt ge in
  ((p2, ge'),
  (set ans q0
    (ltb (Uint63.of_int (0))
      (get ge'
        (add (div (sub tr tl) (Uint63.of_int (2))) (Uint63.of_int (1)))))))

(** val farm :
    Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t **)

let farm p ls rs =
  let n = length p in
  let m = length ls in
  let p0 = msort (fun a b -> leb0 (get p a) (get p b)) n in
  let ids = mk_ids p p0 n in
  let q = msort (mo_le ls rs (blk n)) m in
  snd
    (loop m (fun _ _ -> true) (mo_step ids ls rs q) (Uint63.of_int (0))
      (((((Uint63.of_int (0)), (Uint63.of_int (0))),
      (make n (Uint63.of_int (0)))),
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))),
      (make m false)))

(** val farmingmars :
    Float64.t Marray.t -> uint Marray.t -> uint Marray.t -> bool Marray.t **)

let farmingmars =
  farm
