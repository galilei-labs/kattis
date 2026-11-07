
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

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

(** val guard : Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let guard c lo hi =
  (&&) (ltb lo hi) (ltb c (sub hi lo))

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

(** val merge_step :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> ((Uint63.t * Uint63.t) * Uint63.t Marray.t) ->
    (Uint63.t * Uint63.t) * Uint63.t Marray.t **)

let merge_step key a mid hi k = function
| (p, t) ->
  let (i, j) = p in
  if ltb i mid
  then if leb hi j
       then (((add i (Uint63.of_int (1))), j), (set t k (get a i)))
       else let a0 = get a i in
            let b = get a j in
            if leb0 (get key a0) (get key b)
            then (((add i (Uint63.of_int (1))), j), (set t k a0))
            else ((i, (add j (Uint63.of_int (1)))), (set t k b))
  else ((i, (add j (Uint63.of_int (1)))), (set t k (get a j)))

(** val merge :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let merge key lo mid hi a t =
  let (_, t0) =
    loop hi (fun _ _ -> true) (merge_step key a mid hi) lo ((lo, mid), t)
  in
  t0

(** val copy_step :
    Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let copy_step k = function
| (a, t) -> ((set a k (get t k)), t)

(** val merge_copy :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let merge_copy key lo mid hi a t =
  let t0 = merge key lo mid hi a t in
  loop hi (fun _ _ -> true) copy_step lo (a, t0)

(** val msort_rec :
    Float64.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort_rec key lo hi a t =
  if bdec (guard (Uint63.of_int (1)) lo hi)
  then let m = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       let (a0, t0) = msort_rec key lo m a t in
       let (a1, t1) = msort_rec key m hi a0 t0 in merge_copy key lo m hi a1 t1
  else (a, t)

(** val iota_step : Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let iota_step k p =
  set p k k

(** val scan_cont :
    Float64.t Marray.t -> Uint63.t Marray.t -> Float64.t -> Uint63.t ->
    (((Uint63.t * bool) * Float64.t) * Uint63.t) -> bool **)

let scan_cont ls p cur p0 _ =
  leb0 (get ls (get p p0)) cur

(** val scan_step :
    Float64.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    (((Uint63.t * bool) * Float64.t) * Uint63.t) ->
    ((Uint63.t * bool) * Float64.t) * Uint63.t **)

let scan_step rs p p0 = function
| (p1, bi) ->
  let (p2, best) = p1 in
  let (_, f) = p2 in
  let i = get p p0 in
  let r = get rs i in
  if leb0 best r
  then ((((add p0 (Uint63.of_int (1))), true), r), i)
  else ((((add p0 (Uint63.of_int (1))), f), best), bi)

(** val adv : Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let adv n q q' =
  (&&) (ltb q q') (leb q' n)

(** val sweep :
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t -> Uint63.t
    Marray.t -> (Uint63.t Marray.t * Uint63.t) option **)

let rec sweep ls rs b p n q cnt cur w =
  let (p0, bi) =
    loop n (scan_cont ls p cur) (scan_step rs p) q (((q, false), cur),
      (Uint63.of_int (0)))
  in
  let (p1, best) = p0 in
  let (q', found) = p1 in
  if (&&) found ((||) (eqb cnt (Uint63.of_int (0))) (ltb0 cur best))
  then let w0 = set w cnt bi in
       if leb0 b best
       then Some (w0, (add cnt (Uint63.of_int (1))))
       else if bdec (adv n q q')
            then sweep ls rs b p n q' (add cnt (Uint63.of_int (1))) best w0
            else None
  else None

(** val copy_out :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let copy_out w k o =
  set o k (get w k)

(** val cover :
    Float64.t -> Float64.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    uint Marray.t option **)

let cover x y ls rs =
  let n = length ls in
  let p =
    loop n (fun _ _ -> true) iota_step (Uint63.of_int (0))
      (make n (Uint63.of_int (0)))
  in
  let (p0, _) =
    msort_rec ls (Uint63.of_int (0)) n p (make n (Uint63.of_int (0)))
  in
  (match sweep ls rs y p0 n (Uint63.of_int (0)) (Uint63.of_int (0)) x
           (make n (Uint63.of_int (0))) with
   | Some p1 ->
     let (w, k) = p1 in
     Some
     (loop k (fun _ _ -> true) (copy_out w) (Uint63.of_int (0))
       (make k (Uint63.of_int (0))))
   | None -> None)

module IntervalcoverImpl =
 struct
  (** val cover :
      Float64.t -> Float64.t -> Float64.t Marray.t -> Float64.t Marray.t ->
      uint Marray.t option **)

  let cover =
    cover
 end
