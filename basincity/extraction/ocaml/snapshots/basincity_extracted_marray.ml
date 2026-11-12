
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

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

(** val exists4 : (Uint63.t -> bool) -> Uint63.t -> bool **)

let exists4 f d =
  (||)
    ((||)
      ((||) ((&&) (ltb (Uint63.of_int (0)) d) (f (Uint63.of_int (0))))
        ((&&) (ltb (Uint63.of_int (1)) d) (f (Uint63.of_int (1)))))
      ((&&) (ltb (Uint63.of_int (2)) d) (f (Uint63.of_int (2)))))
    ((&&) (ltb (Uint63.of_int (3)) d) (f (Uint63.of_int (3))))

(** val forall4 : (Uint63.t -> bool) -> Uint63.t -> bool **)

let forall4 f d =
  (&&)
    ((&&)
      ((&&) ((||) (negb (ltb (Uint63.of_int (0)) d)) (f (Uint63.of_int (0))))
        ((||) (negb (ltb (Uint63.of_int (1)) d)) (f (Uint63.of_int (1)))))
      ((||) (negb (ltb (Uint63.of_int (2)) d)) (f (Uint63.of_int (2)))))
    ((||) (negb (ltb (Uint63.of_int (3)) d)) (f (Uint63.of_int (3))))

(** val b2i : bool -> Uint63.t **)

let b2i = function
| true -> (Uint63.of_int (1))
| false -> (Uint63.of_int (0))

(** val count4 : (Uint63.t -> bool) -> Uint63.t -> Uint63.t **)

let count4 f d =
  add
    (add
      (add (b2i ((&&) (ltb (Uint63.of_int (0)) d) (f (Uint63.of_int (0)))))
        (b2i ((&&) (ltb (Uint63.of_int (1)) d) (f (Uint63.of_int (1))))))
      (b2i ((&&) (ltb (Uint63.of_int (2)) d) (f (Uint63.of_int (2))))))
    (b2i ((&&) (ltb (Uint63.of_int (3)) d) (f (Uint63.of_int (3)))))

(** val nbr : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let nbr nb v j =
  get nb (add (mul (Uint63.of_int (4)) v) j)

(** val adjb :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool **)

let adjb nb dg a x =
  exists4 (fun j -> eqb x (nbr nb a j)) (get dg a)

(** val alive : Uint63.t Marray.t -> Uint63.t -> bool **)

let alive rm x =
  eqb (get rm x) (Uint63.of_int (0))

(** val mark1 :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let mark1 w k rm =
  if eqb (get rm w) (Uint63.of_int (0)) then set rm w k else rm

(** val unmark1 :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let unmark1 w k rm =
  if eqb (get rm w) k then set rm w (Uint63.of_int (0)) else rm

(** val mark :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let mark nb dg u k rm =
  let d = get dg u in
  let rm0 = mark1 u k rm in
  let rm1 =
    if ltb (Uint63.of_int (0)) d
    then mark1 (nbr nb u (Uint63.of_int (0))) k rm0
    else rm0
  in
  let rm2 =
    if ltb (Uint63.of_int (1)) d
    then mark1 (nbr nb u (Uint63.of_int (1))) k rm1
    else rm1
  in
  let rm3 =
    if ltb (Uint63.of_int (2)) d
    then mark1 (nbr nb u (Uint63.of_int (2))) k rm2
    else rm2
  in
  if ltb (Uint63.of_int (3)) d
  then mark1 (nbr nb u (Uint63.of_int (3))) k rm3
  else rm3

(** val unmark :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let unmark nb dg u k rm =
  let d = get dg u in
  let rm0 = unmark1 u k rm in
  let rm1 =
    if ltb (Uint63.of_int (0)) d
    then unmark1 (nbr nb u (Uint63.of_int (0))) k rm0
    else rm0
  in
  let rm2 =
    if ltb (Uint63.of_int (1)) d
    then unmark1 (nbr nb u (Uint63.of_int (1))) k rm1
    else rm1
  in
  let rm3 =
    if ltb (Uint63.of_int (2)) d
    then unmark1 (nbr nb u (Uint63.of_int (2))) k rm2
    else rm2
  in
  if ltb (Uint63.of_int (3)) d
  then unmark1 (nbr nb u (Uint63.of_int (3))) k rm3
  else rm3

(** val deg :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t **)

let deg nb dg rm v =
  count4 (fun j -> alive rm (nbr nb v j)) (get dg v)

(** val simp :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> bool **)

let simp nb dg rm v =
  let d = get dg v in
  forall4 (fun j1 ->
    forall4 (fun j2 ->
      (||)
        ((||) ((||) (leb j2 j1) (negb (alive rm (nbr nb v j1))))
          (negb (alive rm (nbr nb v j2))))
        (adjb nb dg (nbr nb v j1) (nbr nb v j2)))
      d)
    d

(** val cnt_loop :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec cnt_loop n rm i acc =
  if bdec (ltb i n)
  then cnt_loop n rm (add i (Uint63.of_int (1)))
         (if alive rm i then add acc (Uint63.of_int (1)) else acc)
  else acc

(** val sel_loop :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t * bool **)

let rec sel_loop n nb dg rm i best bd =
  if bdec (ltb i n)
  then if alive rm i
       then if simp nb dg rm i
            then (i, true)
            else let d = deg nb dg rm i in
                 if ltb d bd
                 then sel_loop n nb dg rm (add i (Uint63.of_int (1))) i d
                 else sel_loop n nb dg rm (add i (Uint63.of_int (1))) best bd
       else sel_loop n nb dg rm (add i (Uint63.of_int (1))) best bd
  else (best, false)

(** val child :
    Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t ->
    bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    bool * Uint63.t Marray.t **)

let child nb dg rec0 k u rm =
  let rm1 = mark nb dg u k rm in
  let (b, rm2) = rec0 rm1 in (b, (unmark nb dg u k rm2))

(** val try_slot :
    Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t ->
    bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t -> Uint63.t ->
    (bool * Uint63.t Marray.t) -> bool * Uint63.t Marray.t **)

let try_slot nb dg rec0 k v j = function
| (b, rm) ->
  if b
  then (true, rm)
  else if ltb j (get dg v)
       then let u = nbr nb v j in
            if alive rm u then child nb dg rec0 k u rm else (false, rm)
       else (false, rm)

(** val node :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> (Uint63.t Marray.t
    -> bool * Uint63.t Marray.t) -> Uint63.t -> Uint63.t Marray.t ->
    bool * Uint63.t Marray.t **)

let node n nb dg rec0 k rm =
  if leb (mul (Uint63.of_int (5)) k)
       (cnt_loop n rm (Uint63.of_int (0)) (Uint63.of_int (0)))
  then (true, rm)
  else let (v, s) =
         sel_loop n nb dg rm (Uint63.of_int (0)) n (Uint63.of_int (5))
       in
       if s
       then child nb dg rec0 k v rm
       else if ltb v n
            then try_slot nb dg rec0 k v (Uint63.of_int (3))
                   (try_slot nb dg rec0 k v (Uint63.of_int (2))
                     (try_slot nb dg rec0 k v (Uint63.of_int (1))
                       (try_slot nb dg rec0 k v (Uint63.of_int (0))
                         (child nb dg rec0 k v rm))))
            else (false, rm)

(** val search :
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t Marray.t -> bool * Uint63.t Marray.t **)

let rec search n nb dg k rm =
  if bdec (eqb k (Uint63.of_int (0)))
  then (true, rm)
  else node n nb dg (fun rm' ->
         search n nb dg (sub k (Uint63.of_int (1))) rm') k rm

(** val fill_dg :
    Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t **)

let rec fill_dg y n i dg =
  if bdec (ltb i n)
  then fill_dg y n (add i (Uint63.of_int (1))) (set dg i (length (get y i)))
  else dg

(** val put_slot :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let put_slot row b j nb =
  if ltb j (length row)
  then set nb (add b j) (sub (get row j) (Uint63.of_int (1)))
  else nb

(** val fill_nb :
    Uint63.t Marray.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t **)

let rec fill_nb y n i nb =
  if bdec (ltb i n)
  then let row = get y i in
       let b = mul (Uint63.of_int (4)) i in
       fill_nb y n (add i (Uint63.of_int (1)))
         (put_slot row b (Uint63.of_int (3))
           (put_slot row b (Uint63.of_int (2))
             (put_slot row b (Uint63.of_int (1))
               (put_slot row b (Uint63.of_int (0)) nb))))
  else nb

(** val basincity_impl : uint -> uint Marray.t Marray.t -> bool **)

let basincity_impl k y =
  let n = length y in
  let dg = fill_dg y n (Uint63.of_int (0)) (make n (Uint63.of_int (0))) in
  let nb =
    fill_nb y n (Uint63.of_int (0))
      (make (mul (Uint63.of_int (4)) n) (Uint63.of_int (0)))
  in
  fst (search n nb dg k (make n (Uint63.of_int (0))))

(** val basincity : uint -> uint Marray.t Marray.t -> bool **)

let basincity =
  basincity_impl
