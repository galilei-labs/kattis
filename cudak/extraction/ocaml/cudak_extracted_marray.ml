
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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val vcell :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let vcell t base t0 c =
  if leb c t0 then get t (add base (sub t0 c)) else (Uint63.of_int (0))

(** val rowsum :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec rowsum t base t0 c d acc =
  if bdec (ltb d c)
  then rowsum t base t0 c (add d (Uint63.of_int (1)))
         (add acc (vcell t base t0 d))
  else acc

(** val fill :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec fill t s s1 n idx k u =
  if bdec (ltb idx n)
  then fill
         (set t idx
           (rowsum t (mul (sub k (Uint63.of_int (1))) s1) u
             (Uint63.of_int (10)) (Uint63.of_int (0)) (Uint63.of_int (0))))
         s s1 n (add idx (Uint63.of_int (1)))
         (if eqb u s then add k (Uint63.of_int (1)) else k)
         (if eqb u s then (Uint63.of_int (0)) else add u (Uint63.of_int (1)))
  else t

(** val digits : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * Uint63.t **)

let rec digits b d q =
  if bdec
       ((&&) (ltb d (Uint63.of_int (15)))
         (leb (mul q (Uint63.of_int (10))) b))
  then digits b (add d (Uint63.of_int (1))) (mul q (Uint63.of_int (10)))
  else (d, q)

(** val walk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t **)

let rec walk t s1 j p r t0 acc =
  if bdec (ltb (Uint63.of_int (0)) j)
  then let c = div r p in
       let acc' =
         rowsum t (mul (sub j (Uint63.of_int (1))) s1) t0 c
           (Uint63.of_int (0)) acc
       in
       if ltb t0 c
       then acc'
       else walk t s1 (sub j (Uint63.of_int (1)))
              (div p (Uint63.of_int (10))) (mod0 r p) (sub t0 c) acc'
  else if eqb t0 (Uint63.of_int (0)) then add acc (Uint63.of_int (1)) else acc

(** val pick :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t * Uint63.t **)

let rec pick t base t0 c r =
  if bdec ((&&) (ltb c (Uint63.of_int (9))) (ltb (vcell t base t0 c) r))
  then pick t base t0 (add c (Uint63.of_int (1))) (sub r (vcell t base t0 c))
  else (c, r)

(** val minwalk :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec minwalk t s1 j t0 r x =
  if bdec (ltb (Uint63.of_int (0)) j)
  then let cr =
         pick t (mul (sub j (Uint63.of_int (1))) s1) t0 (Uint63.of_int (0)) r
       in
       minwalk t s1 (sub j (Uint63.of_int (1))) (sub t0 (fst cr)) (snd cr)
         (add (mul x (Uint63.of_int (10))) (fst cr))
  else x

(** val cudak_impl : uint -> uint -> uint -> uint * uint **)

let cudak_impl a b s =
  let s1 = add s (Uint63.of_int (1)) in
  let dq = digits b (Uint63.of_int (1)) (Uint63.of_int (1)) in
  let d = fst dq in
  let q = snd dq in
  let n = mul d s1 in
  let t =
    fill
      (set (make n (Uint63.of_int (0))) (Uint63.of_int (0))
        (Uint63.of_int (1)))
      s s1 n s1 (Uint63.of_int (1)) (Uint63.of_int (0))
  in
  let cb = walk t s1 d q b s (Uint63.of_int (0)) in
  let ca = walk t s1 d q (sub a (Uint63.of_int (1))) s (Uint63.of_int (0)) in
  ((sub cb ca),
  (minwalk t s1 d s (add ca (Uint63.of_int (1))) (Uint63.of_int (0))))

(** val cudak : uint -> uint -> uint -> uint * uint **)

let cudak =
  cudak_impl
