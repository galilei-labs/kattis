
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val land0 : Uint63.t -> Uint63.t -> Uint63.t **)

let land0 = Uint63.l_and

(** val lxor0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lxor0 = Uint63.l_xor

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val hmul : Uint63.t **)

let hmul =
  (Uint63.of_int (-2177342782468422677))

(** val hidx : Uint63.t -> Uint63.t -> Uint63.t **)

let hidx sh k =
  lsr0 (mul k hmul) sh

(** val find : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec find t k i =
  if bdec (ltb i (length t))
  then let x = get t i in
       if (||) (eqb x (Uint63.of_int (0))) (eqb x k)
       then i
       else find t k (add i (Uint63.of_int (1)))
  else i

(** val find0 : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let find0 sh t k =
  find t k (hidx sh k)

(** val lookup : Uint63.t -> Uint63.t Marray.t -> Uint63.t -> bool **)

let lookup sh t k =
  let j = find0 sh t k in (&&) (ltb j (length t)) (eqb (get t j) k)

(** val insert :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t * bool **)

let insert sh t k =
  let j = find0 sh t k in
  if ltb j (length t)
  then if eqb (get t j) (Uint63.of_int (0))
       then ((set t j k), true)
       else (t, true)
  else (t, false)

(** val key : Uint63.t -> Uint63.t -> Uint63.t **)

let key s l =
  add (add (lsl0 s (Uint63.of_int (50))) l) (Uint63.of_int (1))

(** val pdfs :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool **)

let rec pdfs d n l a base2 sh t c free len r v =
  if bdec (eqb r (Uint63.of_int (0)))
  then let l0 = add len (get d (add (mul c n) a)) in
       if leb l0 l
       then lookup sh t (key (lxor0 base2 free) (sub l l0))
       else false
  else if bdec (ltb v n)
       then let bv = lsl0 (Uint63.of_int (1)) v in
            if eqb (land0 free bv) (Uint63.of_int (0))
            then pdfs d n l a base2 sh t c free len r
                   (add v (Uint63.of_int (1)))
            else let l0 = add len (get d (add (mul c n) v)) in
                 if leb l0 l
                 then if pdfs d n l a base2 sh t v (lxor0 free bv) l0
                           (sub r (Uint63.of_int (1))) (Uint63.of_int (0))
                      then true
                      else pdfs d n l a base2 sh t c free len r
                             (add v (Uint63.of_int (1)))
                 else pdfs d n l a base2 sh t c free len r
                        (add v (Uint63.of_int (1)))
       else false

(** val leafins :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t Marray.t * bool **)

let leafins d n l a m fr2 base2 k2 sh size t k =
  let (t1, b) = insert sh t k in
  if b
  then (t1, false)
  else if pdfs d n l a base2 sh t1 m fr2 (Uint63.of_int (0)) k2
            (Uint63.of_int (0))
       then (t1, true)
       else ((fst (insert sh (make size (Uint63.of_int (0))) k)), false)

(** val idfs :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t * bool **)

let rec idfs d n l a m fp need fr2 base2 k2 sh size t c free len r v =
  if bdec (eqb r (Uint63.of_int (0)))
  then let l0 = add len (get d (add (mul c n) m)) in
       if leb l0 l
       then leafins d n l a m fr2 base2 k2 sh size t (key (lxor0 fp free) l0)
       else (t, false)
  else if bdec (ltb v n)
       then let bv = lsl0 (Uint63.of_int (1)) v in
            if eqb (land0 free bv) (Uint63.of_int (0))
            then idfs d n l a m fp need fr2 base2 k2 sh size t c free len r
                   (add v (Uint63.of_int (1)))
            else if (&&) (eqb r (Uint63.of_int (1)))
                      (negb
                        (eqb (land0 need (lxor0 free bv)) (Uint63.of_int (0))))
                 then idfs d n l a m fp need fr2 base2 k2 sh size t c free
                        len r (add v (Uint63.of_int (1)))
                 else let l0 = add len (get d (add (mul c n) v)) in
                      if leb l0 l
                      then let (t1, b) =
                             idfs d n l a m fp need fr2 base2 k2 sh size t v
                               (lxor0 free bv) l0 (sub r (Uint63.of_int (1)))
                               (Uint63.of_int (0))
                           in
                           if b
                           then (t1, true)
                           else idfs d n l a m fp need fr2 base2 k2 sh size
                                  t1 c free len r (add v (Uint63.of_int (1)))
                      else idfs d n l a m fp need fr2 base2 k2 sh size t c
                             free len r (add v (Uint63.of_int (1)))
       else (t, false)

(** val search_m :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let search_m d n l a k1 k2 sh size m =
  let fp =
    lxor0 (sub (lsl0 (Uint63.of_int (1)) a) (Uint63.of_int (1)))
      (lsl0 (Uint63.of_int (1)) m)
  in
  let need =
    if (&&) (eqb (land0 n (Uint63.of_int (1))) (Uint63.of_int (0)))
         (leb (Uint63.of_int (4)) n)
    then lsl0 (Uint63.of_int (1))
           (if eqb m (Uint63.of_int (0))
            then (Uint63.of_int (1))
            else (Uint63.of_int (0)))
    else (Uint63.of_int (0))
  in
  let fr2 = lxor0 fp need in
  let (t, b) =
    idfs d n l a m fp need fr2 need k2 sh size
      (make size (Uint63.of_int (0))) a fp (Uint63.of_int (0)) k1
      (Uint63.of_int (0))
  in
  if b
  then true
  else pdfs d n l a need sh t m fr2 (Uint63.of_int (0)) k2 (Uint63.of_int (0))

(** val mloop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let rec mloop d n l a k1 k2 sh size m =
  if bdec (ltb m a)
  then if search_m d n l a k1 k2 sh size m
       then true
       else mloop d n l a k1 k2 sh size (add m (Uint63.of_int (1)))
  else false

(** val fill :
    Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fill x n n0 i d =
  if bdec (ltb i n0)
  then fill x n n0 (add i (Uint63.of_int (1)))
         (set d i (get (get x (div i n)) (mod0 i n)))
  else d

(** val logcap : Uint63.t -> Uint63.t **)

let logcap n =
  if leb n (Uint63.of_int (8))
  then (Uint63.of_int (7))
  else if eqb n (Uint63.of_int (9))
       then (Uint63.of_int (9))
       else if eqb n (Uint63.of_int (10))
            then (Uint63.of_int (11))
            else if eqb n (Uint63.of_int (11))
                 then (Uint63.of_int (13))
                 else if eqb n (Uint63.of_int (12))
                      then (Uint63.of_int (15))
                      else if eqb n (Uint63.of_int (13))
                           then (Uint63.of_int (17))
                           else (Uint63.of_int (20))

(** val indoor : uint Marray.t Marray.t -> uint -> bool **)

let indoor x l =
  let n = length x in
  let n0 = mul n n in
  let d = fill x n n0 (Uint63.of_int (0)) (make n0 (Uint63.of_int (0))) in
  let a = sub n (Uint63.of_int (1)) in
  let k1 = div (sub n (Uint63.of_int (2))) (Uint63.of_int (2)) in
  let k2 = sub (sub n (Uint63.of_int (2))) k1 in
  let b = logcap n in
  mloop d n l a k1 k2 (sub (Uint63.of_int (63)) b)
    (add (lsl0 (Uint63.of_int (1)) b) (Uint63.of_int (256)))
    (Uint63.of_int (0))

module IndoorienteeringImpl =
 struct
  (** val indoorienteering : uint Marray.t Marray.t -> uint -> bool **)

  let indoorienteering =
    indoor
 end
