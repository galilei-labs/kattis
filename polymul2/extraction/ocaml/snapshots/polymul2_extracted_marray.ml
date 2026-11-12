
(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

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

(** val sqrt : Float64.t -> Float64.t **)

let sqrt = Float64.sqrt

(** val opp : Float64.t -> Float64.t **)

let opp = Float64.opp

(** val mul0 : Float64.t -> Float64.t -> Float64.t **)

let mul0 = Float64.mul

(** val add0 : Float64.t -> Float64.t -> Float64.t **)

let add0 = Float64.add

(** val sub0 : Float64.t -> Float64.t -> Float64.t **)

let sub0 = Float64.sub

(** val div : Float64.t -> Float64.t -> Float64.t **)

let div = Float64.div

(** val of_uint63 : Uint63.t -> Float64.t **)

let of_uint63 = Float64.of_uint63

(** val normfr_mantissa : Float64.t -> Uint63.t **)

let normfr_mantissa = Float64.normfr_mantissa

(** val frshiftexp : Float64.t -> Float64.t * Uint63.t **)

let frshiftexp = Float64.frshiftexp

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val wloop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let rec wloop hi f i s =
  if bdec (ltb i hi)
  then wloop hi f (add i (Uint63.of_int (1))) (f i s)
  else s

(** val loop :
    Uint63.t -> (Uint63.t -> 'a1 -> 'a1) -> Uint63.t -> 'a1 -> 'a1 **)

let loop =
  wloop

(** val lg_find : Uint63.t -> Uint63.t -> Uint63.t **)

let rec lg_find l k =
  if bdec (ltb k (Uint63.of_int (62)))
  then if leb l (lsl0 (Uint63.of_int (1)) k)
       then k
       else lg_find l (add k (Uint63.of_int (1)))
  else k

(** val log2up : Uint63.t -> Uint63.t **)

let log2up l =
  lg_find l (Uint63.of_int (0))

(** val tw_cell :
    Uint63.t -> Uint63.t -> Float64.t -> Float64.t -> Uint63.t -> (Float64.t
    Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t Marray.t **)

let tw_cell m hm bc bs k = function
| (tre, tim) ->
  let src = add hm (lsr0 k (Uint63.of_int (1))) in
  let ar = get tre src in
  let ai = get tim src in
  if eqb (land0 k (Uint63.of_int (1))) (Uint63.of_int (0))
  then ((set tre (add m k) ar), (set tim (add m k) ai))
  else ((set tre (add m k) (sub0 (mul0 ar bc) (mul0 ai bs))),
         (set tim (add m k) (add0 (mul0 ar bs) (mul0 ai bc))))

(** val tw_stage :
    Uint63.t -> (((Float64.t Marray.t * Float64.t
    Marray.t) * Float64.t) * Float64.t) -> ((Float64.t Marray.t * Float64.t
    Marray.t) * Float64.t) * Float64.t **)

let tw_stage s = function
| (p, bs) ->
  let (p0, bc) = p in
  let m = lsl0 (Uint63.of_int (1)) s in
  let c' =
    sqrt
      (mul0 (add0 (Float64.of_float (0x1p+0)) bc) (Float64.of_float (0x1p-1)))
  in
  (((loop m
      (tw_cell m (lsl0 (Uint63.of_int (1)) (sub s (Uint63.of_int (1)))) bc bs)
      (Uint63.of_int (0)) p0),
  c'), (div bs (mul0 (Float64.of_float (0x1p+1)) c')))

(** val build_tw :
    Uint63.t -> Uint63.t -> Float64.t Marray.t * Float64.t Marray.t **)

let build_tw lg n =
  let tre =
    set (make n (Float64.of_float (0x0p+0))) (Uint63.of_int (1))
      (Float64.of_float (0x1p+0))
  in
  let tim = make n (Float64.of_float (0x0p+0)) in
  let (p, _) =
    loop lg tw_stage (Uint63.of_int (1)) (((tre, tim),
      (Float64.of_float (0x0p+0))), (Float64.of_float (0x1p+0)))
  in
  let (p0, _) = p in p0

(** val bfly :
    Uint63.t -> Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Uint63.t -> (Float64.t Marray.t * Float64.t Marray.t) -> Float64.t
    Marray.t * Float64.t Marray.t **)

let bfly sh m half neg sre sim tre tim j = function
| (dre, dim) ->
  let q = lsr0 j sh in
  let i1 = add j (lsl0 q sh) in
  let i2 = add i1 (lsl0 (Uint63.of_int (1)) sh) in
  let wr = get tre (add m q) in
  let wi = if neg then opp (get tim (add m q)) else get tim (add m q) in
  let ur = get sre i1 in
  let ui = get sim i1 in
  let vr = get sre i2 in
  let vi = get sim i2 in
  let tr = sub0 (mul0 wr vr) (mul0 wi vi) in
  let ti = add0 (mul0 wr vi) (mul0 wi vr) in
  ((set (set dre j (add0 ur tr)) (add j half) (sub0 ur tr)),
  (set (set dim j (add0 ui ti)) (add j half) (sub0 ui ti)))

(** val fft_stage :
    Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t -> Float64.t Marray.t
    -> Uint63.t -> (((Float64.t Marray.t * Float64.t Marray.t) * Float64.t
    Marray.t) * Float64.t Marray.t) -> ((Float64.t Marray.t * Float64.t
    Marray.t) * Float64.t Marray.t) * Float64.t Marray.t **)

let fft_stage lg half neg tre tim s = function
| (p, dim) ->
  let (p0, dre) = p in
  let (sre, sim) = p0 in
  (((loop half
      (bfly (sub (sub lg (Uint63.of_int (1))) s) (lsl0 (Uint63.of_int (1)) s)
        half neg sre sim tre tim)
      (Uint63.of_int (0)) (dre, dim)),
  sre), sim)

(** val fft :
    Uint63.t -> Uint63.t -> bool -> Float64.t Marray.t -> Float64.t Marray.t
    -> Float64.t Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t * Float64.t Marray.t **)

let fft lg half neg tre tim re im =
  let n = add half half in
  let (p, _) =
    loop lg (fft_stage lg half neg tre tim) (Uint63.of_int (0)) (((re, im),
      (make n (Float64.of_float (0x0p+0)))),
      (make n (Float64.of_float (0x0p+0))))
  in
  let (p0, _) = p in p0

(** val kOFF : Uint63.t **)

let kOFF =
  (Uint63.of_int (34905131040))

(** val limb : Uint63.t -> Uint63.t -> Float64.t **)

let limb c i =
  sub0
    (of_uint63
      (land0 (lsr0 (add c kOFF) (mul (Uint63.of_int (6)) i))
        (Uint63.of_int (63))))
    (Float64.of_float (0x1p+5))

(** val load :
    sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t **)

let load x n n0 i =
  loop n (fun t a -> set a t (limb (get x t) i)) (Uint63.of_int (0))
    (make n0 (Float64.of_float (0x0p+0)))

(** val copy_out :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    (Float64.t Marray.t * Float64.t Marray.t) -> Float64.t
    Marray.t * Float64.t Marray.t **)

let copy_out n off yr yi st =
  loop n (fun k st0 ->
    let (bR, bI) = st0 in
    ((set bR (add off k) (get yr k)), (set bI (add off k) (get yi k))))
    (Uint63.of_int (0)) st

(** val nL : Uint63.t **)

let nL =
  (Uint63.of_int (6))

(** val fwd_all :
    sint Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t
    -> Float64.t Marray.t -> Float64.t Marray.t * Float64.t Marray.t **)

let fwd_all x n lg half tre tim =
  let n0 = add half half in
  loop nL (fun i st ->
    let (yr, yi) =
      fft lg half false tre tim (load x n n0 i)
        (make n0 (Float64.of_float (0x0p+0)))
    in
    copy_out n0 (mul i n0) yr yi st) (Uint63.of_int (0))
    ((make (mul nL n0) (Float64.of_float (0x0p+0))),
    (make (mul nL n0) (Float64.of_float (0x0p+0))))

(** val cacc :
    Float64.t -> Float64.t -> Float64.t -> Float64.t ->
    (Float64.t * Float64.t) -> Float64.t * Float64.t **)

let cacc ar ai br bi = function
| (qr, qi) ->
  ((add0 qr (sub0 (mul0 ar br) (mul0 ai bi))),
    (add0 qi (add0 (mul0 ar bi) (mul0 ai br))))

(** val pterm :
    Uint63.t -> Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t
    Marray.t -> Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t ->
    (Float64.t * Float64.t) -> Float64.t * Float64.t **)

let pterm w n k aR aI bR bI i st =
  if (&&) (leb i w) (ltb (sub w i) nL)
  then cacc (get aR (add (mul i n) k)) (get aI (add (mul i n) k))
         (get bR (add (mul (sub w i) n) k))
         (get bI (add (mul (sub w i) n) k)) st
  else st

(** val pcell :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t -> Uint63.t -> (Float64.t
    Marray.t * Float64.t Marray.t) -> Float64.t Marray.t * Float64.t Marray.t **)

let pcell g n aR aI bR bI k = function
| (pr, pim) ->
  let (q0r, q0i) =
    loop nL (pterm (add g g) n k aR aI bR bI) (Uint63.of_int (0))
      ((Float64.of_float (0x0p+0)), (Float64.of_float (0x0p+0)))
  in
  let (q1r, q1i) =
    loop nL (pterm (add (add g g) (Uint63.of_int (1))) n k aR aI bR bI)
      (Uint63.of_int (0)) ((Float64.of_float (0x0p+0)),
      (Float64.of_float (0x0p+0)))
  in
  ((set pr k (sub0 q0r q1i)), (set pim k (add0 q0i q1r)))

(** val products :
    Uint63.t -> Uint63.t -> Float64.t Marray.t -> Float64.t Marray.t ->
    Float64.t Marray.t -> Float64.t Marray.t -> Float64.t
    Marray.t * Float64.t Marray.t **)

let products g n aR aI bR bI =
  loop n (pcell g n aR aI bR bI) (Uint63.of_int (0))
    ((make n (Float64.of_float (0x0p+0))),
    (make n (Float64.of_float (0x0p+0))))

(** val mAGIC : Float64.t **)

let mAGIC =
  (Float64.of_float (0x1.8p+52))

(** val mAGICI : Uint63.t **)

let mAGICI =
  (Uint63.of_int (6755399441055744))

(** val toint : Float64.t -> Uint63.t **)

let toint z =
  let (f, _) = frshiftexp (add0 z mAGIC) in sub (normfr_mantissa f) mAGICI

(** val accum :
    Uint63.t -> Uint63.t -> Float64.t -> Float64.t Marray.t -> Float64.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let accum g l invN yr yi r =
  loop l (fun q r0 ->
    let d0 = toint (mul0 (get yr q) invN) in
    let d1 = toint (mul0 (get yi q) invN) in
    set r0 q
      (add (add (get r0 q) (lsl0 d0 (mul (Uint63.of_int (12)) g)))
        (lsl0 d1 (add (mul (Uint63.of_int (12)) g) (Uint63.of_int (6))))))
    (Uint63.of_int (0)) r

(** val polymul_impl : sint Marray.t -> sint Marray.t -> sint Marray.t **)

let polymul_impl x y =
  let na = length x in
  let nb = length y in
  let l = sub (add na nb) (Uint63.of_int (1)) in
  let lg = log2up l in
  let half = lsl0 (Uint63.of_int (1)) (sub lg (Uint63.of_int (1))) in
  let n = add half half in
  let (tre, tim) = build_tw lg n in
  let (aR, aI) = fwd_all x na lg half tre tim in
  let (bR, bI) = fwd_all y nb lg half tre tim in
  let invN = div (Float64.of_float (0x1p+0)) (of_uint63 n) in
  loop nL (fun g r ->
    let (pr, pim) = products g n aR aI bR bI in
    let (yr, yi) = fft lg half true tre tim pr pim in accum g l invN yr yi r)
    (Uint63.of_int (0)) (make l (Uint63.of_int (0)))

(** val polymul : sint Marray.t -> sint Marray.t -> sint Marray.t **)

let polymul =
  polymul_impl
