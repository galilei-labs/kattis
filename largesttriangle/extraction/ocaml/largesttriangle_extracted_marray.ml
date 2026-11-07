
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

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

(** val sH : Uint63.t **)

let sH =
  (Uint63.of_int (67108864))

(** val oFF : Uint63.t **)

let oFF =
  (Uint63.of_int (1152921504606846976))

(** val crs :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t **)

let crs ax ay bx by_ cx cy =
  add (sub (mul (sub bx ax) (sub cy ay)) (mul (sub cx ax) (sub by_ ay))) oFF

(** val merge_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((Uint63.t
    Marray.t * Uint63.t) * Uint63.t) -> (Uint63.t
    Marray.t * Uint63.t) * Uint63.t **)

let merge_step a mid hi k = function
| (p, j) ->
  let (t, i) = p in
  if (&&) (ltb i mid) ((||) (leb hi j) (leb (get a i) (get a j)))
  then (((set t k (get a i)), (add i (Uint63.of_int (1)))), j)
  else (((set t k (get a j)), i), (add j (Uint63.of_int (1))))

(** val merge :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t **)

let merge a t lo mid hi =
  let (p, _) =
    loop hi (fun _ _ -> true) (merge_step a mid hi) lo ((t, lo), mid)
  in
  let (t', _) = p in t'

(** val copy_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let copy_step t k a =
  set a k (get t k)

(** val msort :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec msort a t lo hi =
  if bdec ((&&) (ltb lo hi) (ltb (Uint63.of_int (1)) (sub hi lo)))
  then let mid = add lo (div (sub hi lo) (Uint63.of_int (2))) in
       let (a1, t1) = msort a t lo mid in
       let (a2, t2) = msort a1 t1 mid hi in
       let t3 = merge a2 t2 lo mid hi in
       ((loop hi (fun _ _ -> true) (copy_step t3) lo a2), t3)
  else (a, t)

(** val sort : Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let sort k n =
  fst (msort k (make n (Uint63.of_int (0))) (Uint63.of_int (0)) n)

(** val dedup_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t) ->
    Uint63.t Marray.t * Uint63.t **)

let dedup_step s t = function
| (d, m) ->
  if (||) (eqb m (Uint63.of_int (0)))
       (ltb (get d (sub m (Uint63.of_int (1)))) (get s t))
  then ((set d m (get s t)), (add m (Uint63.of_int (1))))
  else (d, m)

(** val decode_step :
    Uint63.t Marray.t -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t)
    -> Uint63.t Marray.t * Uint63.t Marray.t **)

let decode_step d u = function
| (pX, pY) ->
  let d0 = get d u in ((set pX u (div d0 sH)), (set pY u (mod0 d0 sH)))

(** val popl :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t **)

let rec popl x y sT s r =
  if bdec (ltb (Uint63.of_int (1)) r)
  then let i1 = get sT (sub r (Uint63.of_int (2))) in
       let i2 = get sT (sub r (Uint63.of_int (1))) in
       if leb
            (crs (get x i1) (get y i1) (get x i2) (get y i2) (get x s)
              (get y s))
            oFF
       then popl x y sT s (sub r (Uint63.of_int (1)))
       else r
  else r

(** val pass_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t) -> Uint63.t Marray.t * Uint63.t **)

let pass_step x y s = function
| (sT, r) ->
  let r' = popl x y sT s r in ((set sT r' s), (add r' (Uint63.of_int (1))))

(** val pass :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t **)

let pass x y m =
  loop m (fun _ _ -> true) (pass_step x y) (Uint63.of_int (1))
    ((make m (Uint63.of_int (0))), (Uint63.of_int (1)))

(** val rev_step :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rev_step x m s r =
  set r s (get x (sub (sub m (Uint63.of_int (1))) s))

(** val low_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let low_step pX pY lS t = function
| (hX, hY) ->
  let v = get lS t in ((set hX t (get pX v)), (set hY t (get pY v)))

(** val up_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let up_step rX rY uS a t = function
| (hX, hY) ->
  let v = get uS (add (sub t a) (Uint63.of_int (1))) in
  ((set hX t (get rX v)), (set hY t (get rY v)))

(** val climb :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec climb hX hY hm xi yi xj yj k gk =
  if bdec (ltb k hm)
  then let k1 = add k (Uint63.of_int (1)) in
       let g1 = crs xi yi xj yj (get hX k1) (get hY k1) in
       if leb gk g1 then climb hX hY hm xi yi xj yj k1 g1 else k
  else k

(** val jloop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec jloop hX hY hm xi yi j k best =
  if bdec (ltb j hm)
  then let xj = get hX j in
       let yj = get hY j in
       let k1 = if ltb j k then k else add j (Uint63.of_int (1)) in
       let k2 =
         climb hX hY hm xi yi xj yj k1
           (crs xi yi xj yj (get hX k1) (get hY k1))
       in
       let g = crs xi yi xj yj (get hX k2) (get hY k2) in
       jloop hX hY hm xi yi (add j (Uint63.of_int (1))) k2
         (if ltb best g then g else best)
  else best

(** val sweep_step :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let sweep_step hX hY h i best =
  jloop hX hY (sub h (Uint63.of_int (1))) (get hX i) (get hY i)
    (add i (Uint63.of_int (1))) (add i (Uint63.of_int (2))) best

(** val sweep :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let sweep hX hY h =
  loop (sub h (Uint63.of_int (2))) (fun _ _ -> true) (sweep_step hX hY h)
    (Uint63.of_int (0)) oFF

(** val fzero : Float64.t **)

let fzero =
  of_uint63 (Uint63.of_int (0))

(** val largest_triangle_impl :
    uint Marray.t -> uint Marray.t -> Float64.t **)

let largest_triangle_impl x y =
  let n = length x in
  let k =
    loop n (fun _ _ -> true) (fun i k ->
      set k i (add (mul (get x i) sH) (get y i))) (Uint63.of_int (0))
      (make n (Uint63.of_int (0)))
  in
  let s = sort k n in
  let (d, m) =
    loop n (fun _ _ -> true) (dedup_step s) (Uint63.of_int (0))
      ((make n (Uint63.of_int (0))), (Uint63.of_int (0)))
  in
  if ltb m (Uint63.of_int (3))
  then fzero
  else let (pX, pY) =
         loop m (fun _ _ -> true) (decode_step d) (Uint63.of_int (0))
           ((make m (Uint63.of_int (0))), (make m (Uint63.of_int (0))))
       in
       let (lS, a) = pass pX pY m in
       let rX =
         loop m (fun _ _ -> true) (rev_step pX m) (Uint63.of_int (0))
           (make m (Uint63.of_int (0)))
       in
       let rY =
         loop m (fun _ _ -> true) (rev_step pY m) (Uint63.of_int (0))
           (make m (Uint63.of_int (0)))
       in
       let (uS, b) = pass rX rY m in
       let h = sub (add a b) (Uint63.of_int (2)) in
       if ltb h (Uint63.of_int (3))
       then fzero
       else let (hX, hY) =
              loop h (fun _ _ -> true) (up_step rX rY uS a) a
                (loop a (fun _ _ -> true) (low_step pX pY lS)
                  (Uint63.of_int (0)) ((make h (Uint63.of_int (0))),
                  (make h (Uint63.of_int (0)))))
            in
            let best = sweep hX hY h in
            div0 (of_uint63 (sub best oFF)) (of_uint63 (Uint63.of_int (2)))

module LargesttriangleImpl =
 struct
  (** val largest_triangle : uint Marray.t -> uint Marray.t -> Float64.t **)

  let largest_triangle =
    largest_triangle_impl
 end
