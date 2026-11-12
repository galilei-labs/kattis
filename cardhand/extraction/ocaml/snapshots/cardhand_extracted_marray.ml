
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

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type char63 = Uint63.t

type string = Pstring.t

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val imax : Uint63.t -> Uint63.t -> Uint63.t **)

let imax a b =
  if ltb a b then b else a

(** val sidx_m : Uint63.t -> Uint63.t **)

let sidx_m c =
  if eqb c (Uint63.of_int (115))
  then (Uint63.of_int (0))
  else if eqb c (Uint63.of_int (104))
       then (Uint63.of_int (1))
       else if eqb c (Uint63.of_int (100))
            then (Uint63.of_int (2))
            else (Uint63.of_int (3))

(** val rank_m : Uint63.t -> Uint63.t **)

let rank_m c =
  if leb c (Uint63.of_int (57))
  then sub c (Uint63.of_int (50))
  else if eqb c (Uint63.of_int (84))
       then (Uint63.of_int (8))
       else if eqb c (Uint63.of_int (74))
            then (Uint63.of_int (9))
            else if eqb c (Uint63.of_int (81))
                 then (Uint63.of_int (10))
                 else if eqb c (Uint63.of_int (75))
                      then (Uint63.of_int (11))
                      else (Uint63.of_int (12))

(** val pw4 : Uint63.t -> Uint63.t **)

let pw4 s =
  if eqb s (Uint63.of_int (0))
  then (Uint63.of_int (1))
  else if eqb s (Uint63.of_int (1))
       then (Uint63.of_int (4))
       else if eqb s (Uint63.of_int (2))
            then (Uint63.of_int (16))
            else (Uint63.of_int (64))

(** val pw2 : Uint63.t -> Uint63.t **)

let pw2 s =
  if eqb s (Uint63.of_int (0))
  then (Uint63.of_int (256))
  else if eqb s (Uint63.of_int (1))
       then (Uint63.of_int (512))
       else if eqb s (Uint63.of_int (2))
            then (Uint63.of_int (1024))
            else (Uint63.of_int (2048))

(** val sg_m : Uint63.t -> Uint63.t -> Uint63.t **)

let sg_m t s =
  mod0 (div t (pw4 s)) (Uint63.of_int (4))

(** val dr_m : Uint63.t -> Uint63.t -> Uint63.t **)

let dr_m t s =
  mod0 (div t (pw2 s)) (Uint63.of_int (2))

(** val key_m : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let key_m t s r =
  add (mul (sg_m t s) (Uint63.of_int (13)))
    (if eqb (dr_m t s) (Uint63.of_int (1))
     then r
     else sub (Uint63.of_int (12)) r)

(** val inj_m : Uint63.t -> bool **)

let inj_m t =
  let a = sg_m t (Uint63.of_int (0)) in
  let b = sg_m t (Uint63.of_int (1)) in
  let c = sg_m t (Uint63.of_int (2)) in
  let d = sg_m t (Uint63.of_int (3)) in
  (&&)
    ((&&)
      ((&&) ((&&) ((&&) (negb (eqb a b)) (negb (eqb a c))) (negb (eqb a d)))
        (negb (eqb b c)))
      (negb (eqb b d)))
    (negb (eqb c d))

(** val prep :
    string Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec prep x n i sU rK =
  if bdec (ltb i n)
  then let w = get x i in
       prep x n (add i (Uint63.of_int (1)))
         (set sU i (sidx_m (get0 w (Uint63.of_int (1)))))
         (set rK i (rank_m (get0 w (Uint63.of_int (0)))))
  else (sU, rK)

(** val keys :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let rec keys t sU rK n i k p =
  if bdec (ltb i n)
  then let k0 = key_m t (get sU i) (get rK i) in
       keys t sU rK n (add i (Uint63.of_int (1))) (set k i k0)
         (set p k0 (Uint63.of_int (1)))
  else (k, p)

(** val compact :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t * Uint63.t **)

let rec compact p k b m =
  if bdec (ltb k (Uint63.of_int (52)))
  then if eqb (get p k) (Uint63.of_int (1))
       then compact p (add k (Uint63.of_int (1))) (set b m k)
              (add m (Uint63.of_int (1)))
       else compact p (add k (Uint63.of_int (1))) b m
  else (b, m)

(** val dp :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec dp k b m w q t =
  if bdec (ltb (Uint63.of_int (0)) q)
  then let q' = sub q (Uint63.of_int (1)) in
       let i = div q' m in
       let j = mod0 q' m in
       let c =
         if eqb (get k i) (get b j)
         then add
                (get t
                  (add (mul (add i (Uint63.of_int (1))) w)
                    (add j (Uint63.of_int (1)))))
                (Uint63.of_int (1))
         else imax (get t (add (mul (add i (Uint63.of_int (1))) w) j))
                (get t (add (mul i w) (add j (Uint63.of_int (1)))))
       in
       dp k b m w q' (set t (add (mul i w) j) c)
  else t

(** val lcs_for :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let lcs_for t sU rK n =
  let (k, p) =
    keys t sU rK n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make (Uint63.of_int (52)) (Uint63.of_int (0)))
  in
  let (b, m) =
    compact p (Uint63.of_int (0))
      (make (Uint63.of_int (52)) (Uint63.of_int (0))) (Uint63.of_int (0))
  in
  let w = add m (Uint63.of_int (1)) in
  let t0 =
    dp k b m w (mul n m)
      (make (mul (add n (Uint63.of_int (1))) w) (Uint63.of_int (0)))
  in
  get t0 (Uint63.of_int (0))

(** val search :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t **)

let rec search sU rK n t best =
  if bdec (ltb t (Uint63.of_int (4096)))
  then search sU rK n (add t (Uint63.of_int (1)))
         (if inj_m t then imax best (lcs_for t sU rK n) else best)
  else best

(** val min_moves_impl : string Marray.t -> uint **)

let min_moves_impl x =
  let n = length x in
  let (sU, rK) =
    prep x n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))
      (make n (Uint63.of_int (0)))
  in
  sub n (search sU rK n (Uint63.of_int (0)) (Uint63.of_int (0)))

(** val min_moves : string Marray.t -> uint **)

let min_moves =
  min_moves_impl
