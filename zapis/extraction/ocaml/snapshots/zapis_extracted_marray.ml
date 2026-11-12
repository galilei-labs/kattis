
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

type char63 = Uint63.t

type string = Pstring.t

(** val length : string -> Uint63.t **)

let length = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val mOD : Uint63.t **)

let mOD =
  (Uint63.of_int (100000))

(** val capm : Uint63.t -> Uint63.t **)

let capm v =
  if ltb v mOD then v else mOD

(** val okp : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let okp a b o c =
  (&&) ((||) (eqb a o) (eqb a (Uint63.of_int (63))))
    ((||) (eqb b c) (eqb b (Uint63.of_int (63))))

(** val pcode : Uint63.t -> Uint63.t -> Uint63.t **)

let pcode a b =
  add
    (add
      (if okp a b (Uint63.of_int (40)) (Uint63.of_int (41))
       then (Uint63.of_int (1))
       else (Uint63.of_int (0)))
      (if okp a b (Uint63.of_int (91)) (Uint63.of_int (93))
       then (Uint63.of_int (1))
       else (Uint63.of_int (0))))
    (if okp a b (Uint63.of_int (123)) (Uint63.of_int (125))
     then (Uint63.of_int (1))
     else (Uint63.of_int (0)))

(** val ixi : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let ixi w a b =
  mul (Uint63.of_int (2)) (add (mul a w) b)

(** val inner :
    string -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec inner x tb w ci ii j kk t r c =
  if bdec (ltb (Uint63.of_int (0)) t)
  then let p = pcode ci (get0 x kk) in
       let ia = ixi w (add ii (Uint63.of_int (1))) kk in
       let ib = ixi w (add kk (Uint63.of_int (1))) j in
       let ra = get tb ia in
       let ca = get tb (add ia (Uint63.of_int (1))) in
       let rb = get tb ib in
       let cb = get tb (add ib (Uint63.of_int (1))) in
       inner x tb w ci ii j (add kk (Uint63.of_int (2)))
         (sub t (Uint63.of_int (1)))
         (mod0 (add r (mul (mod0 (mul p ra) mOD) rb)) mOD)
         (capm (add c (capm (mul (capm (mul p ca)) cb))))
  else (r, c)

(** val middle :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec middle x w h l m ii tb =
  if bdec (ltb ii m)
  then let j = add ii l in
       let b0 =
         if eqb h (Uint63.of_int (0))
         then (Uint63.of_int (1))
         else (Uint63.of_int (0))
       in
       let rc =
         inner x tb w (get0 x ii) ii j (add ii (Uint63.of_int (1))) h b0 b0
       in
       let p = ixi w ii j in
       middle x w h l m (add ii (Uint63.of_int (1)))
         (set (set tb p (fst rc)) (add p (Uint63.of_int (1))) (snd rc))
  else tb

(** val outer :
    string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec outer x n w hm h tb =
  if bdec (ltb h hm)
  then let l = mul (Uint63.of_int (2)) h in
       outer x n w hm (add h (Uint63.of_int (1)))
         (middle x w h l (add (sub n l) (Uint63.of_int (1)))
           (Uint63.of_int (0)) tb)
  else tb

(** val zapis_impl : string -> uint * bool **)

let zapis_impl x =
  let n = length x in
  let w = add n (Uint63.of_int (1)) in
  let tb =
    outer x n w (add (div n (Uint63.of_int (2))) (Uint63.of_int (1)))
      (Uint63.of_int (0))
      (make (mul (Uint63.of_int (2)) (mul w w)) (Uint63.of_int (0)))
  in
  let p = ixi w (Uint63.of_int (0)) n in
  ((get tb p), (leb mOD (get tb (add p (Uint63.of_int (1))))))

(** val zapis : string -> uint * bool **)

let zapis =
  zapis_impl
