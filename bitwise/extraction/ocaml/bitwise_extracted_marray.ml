
(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lor0 = Uint63.l_or

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val cell : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let cell a n x =
  if ltb x n then get a x else get a (sub x n)

(** val hasbit : Uint63.t -> Uint63.t -> bool **)

let hasbit v b =
  eqb (land0 (lsr0 v b) (Uint63.of_int (1))) (Uint63.of_int (1))

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec scan a p n b i nb q =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let x = sub i (Uint63.of_int (1)) in
       let nb' = if hasbit (cell a n x) b then i else nb in
       let p0 = get p x in
       scan a p n b x nb' (set q x (if ltb p0 nb' then nb' else p0))
  else q

(** val newptr :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t **)

let newptr a p q n b =
  let n2 = mul (Uint63.of_int (2)) n in
  scan a p n b n2 (add n2 (Uint63.of_int (1)))
    (set (set q n2 (add n2 (Uint63.of_int (1)))) (add n2 (Uint63.of_int (1)))
      (add n2 (Uint63.of_int (1))))

(** val dedup :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    (Uint63.t * Uint63.t Marray.t) * Uint63.t Marray.t **)

let rec dedup q v s w i w' v' s' =
  if bdec (ltb i w)
  then let v0 = get q (get v i) in
       let s0 = get s i in
       if (&&) (ltb (Uint63.of_int (0)) w')
            (eqb (get v' (sub w' (Uint63.of_int (1)))) v0)
       then dedup q v s w (add i (Uint63.of_int (1))) w' v'
              (set s' (sub w' (Uint63.of_int (1))) s0)
       else dedup q v s w (add i (Uint63.of_int (1)))
              (add w' (Uint63.of_int (1))) (set v' w' v0) (set s' w' s0)
  else ((w', v'), s')

(** val levels :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    (((Uint63.t * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let rec levels q t w v s v' s' =
  if bdec (ltb (Uint63.of_int (0)) t)
  then let (p, s2) =
         dedup q v s w (Uint63.of_int (0)) (Uint63.of_int (0)) v' s'
       in
       let (w2, v2) = p in levels q (sub t (Uint63.of_int (1))) w2 v2 s2 v s
  else ((((w, v), s), v'), s')

(** val check :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> bool **)

let rec check v s n w j =
  if bdec (ltb j w)
  then if leb (get v j) (add (get s j) n)
       then true
       else check v s n w (add j (Uint63.of_int (1)))
  else false

(** val init :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let rec init l j v s =
  if bdec (ltb j l)
  then init l (add j (Uint63.of_int (1))) (set v j j) (set s j j)
  else (v, s)

(** val test :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    (((bool * Uint63.t Marray.t) * Uint63.t Marray.t) * Uint63.t
    Marray.t) * Uint63.t Marray.t **)

let test q n k v s v' s' =
  let f0 = get q (Uint63.of_int (0)) in
  let l1 =
    add
      (if ltb f0 (sub n (Uint63.of_int (1)))
       then f0
       else sub n (Uint63.of_int (1)))
      (Uint63.of_int (1))
  in
  let (v1, s1) = init l1 (Uint63.of_int (0)) v s in
  let (p, s3) = levels q k l1 v1 s1 v' s' in
  let (p0, v3) = p in
  let (p1, s2) = p0 in
  let (w, v2) = p1 in
  (((((check v2 s2 n w (Uint63.of_int (0))), v2), s2), v3), s3)

(** val bits :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t **)

let rec bits a n k b ans p q v s v' s' =
  if bdec (ltb (Uint63.of_int (0)) b)
  then let j = sub b (Uint63.of_int (1)) in
       let q1 = newptr a p q n j in
       let (p0, s2) = test q1 n k v s v' s' in
       let (p1, v2) = p0 in
       let (p2, s1) = p1 in
       let (ok, v1) = p2 in
       if ok
       then bits a n k j (lor0 ans (lsl0 (Uint63.of_int (1)) j)) q1 p v1 s1
              v2 s2
       else bits a n k j ans p q1 v1 s1 v2 s2
  else ans

(** val init_ptr :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec init_ptr m x p =
  if bdec (ltb x m)
  then init_ptr m (add x (Uint63.of_int (1)))
         (set p x (add x (Uint63.of_int (1))))
  else p

(** val best_and_impl : uint -> uint Marray.t -> uint **)

let best_and_impl k a =
  let n = length a in
  let n2 = mul (Uint63.of_int (2)) n in
  let p0 =
    init_ptr (add n2 (Uint63.of_int (1))) (Uint63.of_int (0))
      (make (add n2 (Uint63.of_int (2))) (Uint63.of_int (0)))
  in
  let p = set p0 (add n2 (Uint63.of_int (1))) (add n2 (Uint63.of_int (1))) in
  bits a n k (Uint63.of_int (30)) (Uint63.of_int (0)) p
    (make (add n2 (Uint63.of_int (2))) (Uint63.of_int (0)))
    (make n (Uint63.of_int (0))) (make n (Uint63.of_int (0)))
    (make n (Uint63.of_int (0))) (make n (Uint63.of_int (0)))

module BitwiseImpl =
 struct
  (** val best_and : uint -> uint Marray.t -> uint **)

  let best_and =
    best_and_impl
 end
