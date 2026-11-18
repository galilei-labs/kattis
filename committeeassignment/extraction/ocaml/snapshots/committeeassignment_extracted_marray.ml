
type comparison =
| Eq
| Lt
| Gt

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val mul : Uint63.t -> Uint63.t -> Uint63.t **)

let mul = Uint63.mul

(** val div : Uint63.t -> Uint63.t -> Uint63.t **)

let div = Uint63.div

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type string = Pstring.t

(** val compare : string -> string -> comparison **)

let compare = (fun x y -> let c = Pstring.compare x y in if c = 0 then Eq else if c < 0 then Lt else Gt)

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val midp : Uint63.t -> Uint63.t -> Uint63.t **)

let midp lo hi =
  add lo (div (sub hi lo) (Uint63.of_int (2)))

(** val lb : string Marray.t -> string -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec lb k s lo hi =
  if bdec (ltb lo hi)
  then (match compare (get k (midp lo hi)) s with
        | Lt -> lb k s (add (midp lo hi) (Uint63.of_int (1))) hi
        | _ -> lb k s lo (midp lo hi))
  else lo

(** val look : string Marray.t -> Uint63.t -> string -> Uint63.t **)

let look k p s =
  lb k s (Uint63.of_int (0)) p

(** val shift : string Marray.t -> Uint63.t -> Uint63.t -> string Marray.t **)

let rec shift k t j =
  if bdec (ltb t j)
  then shift (set k j (get k (sub j (Uint63.of_int (1))))) t
         (sub j (Uint63.of_int (1)))
  else k

(** val is_eq : comparison -> bool **)

let is_eq = function
| Eq -> true
| _ -> false

(** val insert :
    string Marray.t -> Uint63.t -> string -> string Marray.t * Uint63.t **)

let insert k p s =
  let t = look k p s in
  if (&&) (ltb t p) (is_eq (compare (get k t) s))
  then (k, p)
  else ((set (shift k t p) t s), (add p (Uint63.of_int (1))))

(** val build :
    string Marray.t -> string Marray.t -> Uint63.t -> Uint63.t -> string
    Marray.t -> Uint63.t -> string Marray.t * Uint63.t **)

let rec build y z m i k p =
  if bdec (ltb i m)
  then let (k1, p1) = insert k p (get y i) in
       let (k2, p2) = insert k1 p1 (get z i) in
       build y z m (add i (Uint63.of_int (1))) k2 p2
  else (k, p)

(** val fill :
    string Marray.t -> string Marray.t -> string Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> bool Marray.t -> bool Marray.t **)

let rec fill y z k p m i tbl =
  if bdec (ltb i m)
  then let u = look k p (get y i) in
       let v = look k p (get z i) in
       fill y z k p m (add i (Uint63.of_int (1)))
         (set (set tbl (add (mul u p) v) true) (add (mul v p) u) true)
  else tbl

(** val okc :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t -> bool **)

let rec okc tbl p v c col u =
  if bdec (ltb u v)
  then if (&&) (get tbl (add (mul u p) v)) (eqb (get col u) c)
       then false
       else okc tbl p v c col (add u (Uint63.of_int (1)))
  else true

(** val lim : Uint63.t -> Uint63.t -> Uint63.t **)

let lim used k =
  if ltb used k then add used (Uint63.of_int (1)) else k

(** val bump : Uint63.t -> Uint63.t -> Uint63.t **)

let bump used c =
  if ltb used (add c (Uint63.of_int (1)))
  then add c (Uint63.of_int (1))
  else used

(** val srch :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    -> Uint63.t Marray.t -> bool * Uint63.t Marray.t **)

let rec srch tbl p k v c used col =
  if bdec (ltb v p)
  then if bdec (ltb c (lim used k))
       then if okc tbl p v c col (Uint63.of_int (0))
            then let (b, col2) =
                   srch tbl p k (add v (Uint63.of_int (1)))
                     (Uint63.of_int (0)) (bump used c) (set col v c)
                 in
                 if b
                 then (true, col2)
                 else srch tbl p k v (add c (Uint63.of_int (1))) used col2
            else srch tbl p k v (add c (Uint63.of_int (1))) used col
       else (false, col)
  else (true, col)

(** val deepen :
    bool Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t **)

let rec deepen tbl p p0 k col =
  if bdec (ltb k p0)
  then let (r, col2) =
         srch tbl p k (Uint63.of_int (0)) (Uint63.of_int (0))
           (Uint63.of_int (0)) col
       in
       if r then k else deepen tbl p p0 (add k (Uint63.of_int (1))) col2
  else p0

(** val committees_impl :
    uint -> string Marray.t -> string Marray.t -> uint **)

let committees_impl _ y z =
  let m = length y in
  let (k, p) =
    build y z m (Uint63.of_int (0))
      (make (add m m) (Pstring.unsafe_of_string "")) (Uint63.of_int (0))
  in
  let tbl = fill y z k p m (Uint63.of_int (0)) (make (mul p p) false) in
  let p0 = if ltb p (Uint63.of_int (1)) then (Uint63.of_int (1)) else p in
  deepen tbl p p0 (Uint63.of_int (1)) (make p0 (Uint63.of_int (0)))

(** val committees : uint -> string Marray.t -> string Marray.t -> uint **)

let committees =
  committees_impl
