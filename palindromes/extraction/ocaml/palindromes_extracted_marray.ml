
(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

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

type char63 = Uint63.t

type string = Pstring.t

(** val length0 : string -> Uint63.t **)

let length0 = Pstring.length

(** val get0 : string -> Uint63.t -> char63 **)

let get0 = Pstring.get

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val lowb : Uint63.t -> Uint63.t **)

let lowb j =
  sub j (land0 j (sub j (Uint63.of_int (1))))

(** val fen_add :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec fen_add t n j delta =
  if bdec ((&&) (ltb (Uint63.of_int (0)) j) (leb j n))
  then let t' = set t j (add (get t j) delta) in
       let nj = add j (lowb j) in
       if bdec (ltb j nj) then fen_add t' n nj delta else t'
  else t

(** val fen_sum : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec fen_sum t j acc =
  if bdec (ltb (Uint63.of_int (0)) j)
  then fen_sum t (land0 j (sub j (Uint63.of_int (1)))) (add acc (get t j))
  else acc

(** val imin : Uint63.t -> Uint63.t -> Uint63.t **)

let imin a b =
  if ltb a b then a else b

(** val hcond : string -> Uint63.t -> Uint63.t -> Uint63.t -> bool **)

let hcond x n q k =
  (&&)
    ((&&) (leb k (lsr0 q (Uint63.of_int (1))))
      (ltb (add (lsr0 (add q (Uint63.of_int (1))) (Uint63.of_int (1))) k) n))
    (eqb (get0 x (sub (lsr0 q (Uint63.of_int (1))) k))
      (get0 x (add (lsr0 (add q (Uint63.of_int (1))) (Uint63.of_int (1))) k)))

(** val expand : string -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec expand x n q k =
  if bdec (ltb k n)
  then if hcond x n q k then expand x n q (add k (Uint63.of_int (1))) else k
  else k

(** val man :
    string -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let rec man x n n2 cnt q q0 rb =
  if bdec (ltb q n2)
  then let bq = lsr0 (add q (Uint63.of_int (1))) (Uint63.of_int (1)) in
       let k0 =
         if ltb bq rb
         then imin (get cnt (sub (add q0 q0) q)) (sub rb bq)
         else (Uint63.of_int (0))
       in
       let c = expand x n q k0 in
       if ltb rb (add bq c)
       then man x n n2 (set cnt q c) (add q (Uint63.of_int (1))) q (add bq c)
       else man x n n2 (set cnt q c) (add q (Uint63.of_int (1))) q0 rb
  else cnt

(** val manacher : string -> Uint63.t Marray.t **)

let manacher x =
  let n = length0 x in
  man x n (add n n) (make (add n n) (Uint63.of_int (0))) (Uint63.of_int (0))
    (Uint63.of_int (0)) (Uint63.of_int (0))

(** val tab_loop :
    (Uint63.t -> Uint63.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec tab_loop f n i a =
  if bdec (ltb i n)
  then tab_loop f n (add i (Uint63.of_int (1))) (set a i (f i))
  else a

(** val tab : Uint63.t -> (Uint63.t -> Uint63.t) -> Uint63.t Marray.t **)

let tab n f =
  tab_loop f n (Uint63.of_int (0)) (make n (Uint63.of_int (0)))

(** val build :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec build ts m k head next =
  if bdec (ltb k m)
  then let t = get ts k in
       let h = get head t in
       build ts m (add k (Uint63.of_int (1)))
         (set head t (add k (Uint63.of_int (1)))) (set next k h)
  else (head, next)

(** val fadd :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t **)

let fadd =
  fen_add

(** val fsum : Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let fsum t j =
  fen_sum t j (Uint63.of_int (0))

(** val fval :
    (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t -> Uint63.t **)

let fval t a =
  add (fsum (fst t) (add a (Uint63.of_int (1))))
    (mul a (fsum (snd t) (add a (Uint63.of_int (1)))))

(** val walk :
    Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t * Uint63.t
    Marray.t) -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let rec walk as_ next t v ptr =
  if bdec (ltb (Uint63.of_int (0)) ptr)
  then let k = sub ptr (Uint63.of_int (1)) in
       let nx = get next k in
       let v' = set v k (fval t (get as_ k)) in
       if bdec (ltb nx ptr) then walk as_ next t v' nx else v'
  else v

(** val insert :
    Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let insert nN t i di =
  let dd = imin di (add i (Uint63.of_int (1))) in
  let lft = sub (add i (Uint63.of_int (1))) dd in
  let t0 = fadd (fst t) nN (Uint63.of_int (1)) dd in
  let t1 = fadd t0 nN (add lft (Uint63.of_int (2))) lft in
  let t2 =
    fadd t1 nN (add i (Uint63.of_int (2)))
      (sub (Uint63.of_int (0)) (add i (Uint63.of_int (1))))
  in
  let t3 =
    fadd (snd t) nN (add lft (Uint63.of_int (2)))
      (sub (Uint63.of_int (0)) (Uint63.of_int (1)))
  in
  let t4 = fadd t3 nN (add i (Uint63.of_int (2))) (Uint63.of_int (1)) in
  (t2, t4)

(** val sweep :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t **)

let rec sweep d as_ head next n n1 nN t v tau =
  if bdec (ltb tau n1)
  then let v' = walk as_ next t v (get head tau) in
       let t' = if ltb tau n then insert nN t tau (get d tau) else t in
       sweep d as_ head next n n1 nN t' v' (add tau (Uint63.of_int (1)))
  else v

(** val lsum_all :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let lsum_all n m d as_ ts =
  let hn =
    build ts m (Uint63.of_int (0))
      (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
      (make m (Uint63.of_int (0)))
  in
  let nN = add n (Uint63.of_int (2)) in
  sweep d as_ (fst hn) (snd hn) n (add n (Uint63.of_int (1))) nN
    ((make (add nN (Uint63.of_int (1))) (Uint63.of_int (0))),
    (make (add nN (Uint63.of_int (1))) (Uint63.of_int (0))))
    (make m (Uint63.of_int (0))) (Uint63.of_int (0))

(** val fam :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> bool -> Uint63.t Marray.t **)

let fam n m cnt xl xr par rev =
  let d =
    tab n (fun i ->
      get cnt
        (add
          (mul (Uint63.of_int (2))
            (if rev then sub (sub n (Uint63.of_int (1))) i else i))
          par))
  in
  let as_ =
    tab m (fun k ->
      if rev
      then sub n (sub (get xr k) par)
      else sub (get xl k) (Uint63.of_int (1)))
  in
  let ts =
    tab m (fun k ->
      let h = lsr0 (sub (add (get xl k) (get xr k)) par) (Uint63.of_int (1))
      in
      if rev then sub n h else h)
  in
  lsum_all n m d as_ ts

(** val palindromes_impl :
    string -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

let palindromes_impl x xl xr =
  let n = length0 x in
  let m = length xl in
  let cnt = manacher x in
  let v0 = fam n m cnt xl xr (Uint63.of_int (0)) false in
  let v1 = fam n m cnt xl xr (Uint63.of_int (0)) true in
  let v2 = fam n m cnt xl xr (Uint63.of_int (1)) false in
  let v3 = fam n m cnt xl xr (Uint63.of_int (1)) true in
  tab m (fun k -> add (add (add (get v0 k) (get v1 k)) (get v2 k)) (get v3 k))

module PalindromesImpl =
 struct
  (** val palindromes :
      string -> uint Marray.t -> uint Marray.t -> uint Marray.t **)

  let palindromes =
    palindromes_impl
 end
