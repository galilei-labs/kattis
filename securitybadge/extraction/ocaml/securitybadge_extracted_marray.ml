
(** val negb : bool -> bool **)

let negb = function
| true -> false
| false -> true

(** val fst : ('a1 * 'a2) -> 'a1 **)

let fst = function
| (x, _) -> x

(** val snd : ('a1 * 'a2) -> 'a2 **)

let snd = function
| (_, y) -> y

(** val lsl0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsl0 = Uint63.l_sl

(** val lsr0 : Uint63.t -> Uint63.t -> Uint63.t **)

let lsr0 = Uint63.l_sr

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

(** val merge :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec merge src mid hi i j k dst =
  if bdec (ltb i mid)
  then if bdec (ltb j hi)
       then if leb (get src i) (get src j)
            then merge src mid hi (add i (Uint63.of_int (1))) j
                   (add k (Uint63.of_int (1))) (set dst k (get src i))
            else merge src mid hi i (add j (Uint63.of_int (1)))
                   (add k (Uint63.of_int (1))) (set dst k (get src j))
       else merge src mid hi (add i (Uint63.of_int (1))) j
              (add k (Uint63.of_int (1))) (set dst k (get src i))
  else if bdec (ltb j hi)
       then merge src mid hi i (add j (Uint63.of_int (1)))
              (add k (Uint63.of_int (1))) (set dst k (get src j))
       else dst

(** val mid_of : Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let mid_of m w lo =
  if ltb w (sub m lo) then add lo w else m

(** val pass :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec pass src m w lo dst =
  if bdec (ltb lo m)
  then let mid = mid_of m w lo in
       let hi = mid_of m w mid in
       pass src m w hi (merge src mid hi lo mid lo dst)
  else dst

(** val sort_loop :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec sort_loop m w src dst =
  if bdec (ltb w m)
  then sort_loop m (add w w) (pass src m w (Uint63.of_int (0)) dst) src
  else src

(** val msort : Uint63.t Marray.t -> Uint63.t Marray.t **)

let msort a =
  sort_loop (length a) (Uint63.of_int (1)) a
    (make (length a) (Uint63.of_int (0)))

(** val src_of : Uint63.t -> Uint63.t **)

let src_of key =
  lsr0 key (Uint63.of_int (13))

(** val idx_of : Uint63.t -> Uint63.t **)

let idx_of key =
  sub key (lsl0 (lsr0 key (Uint63.of_int (13))) (Uint63.of_int (13)))

(** val keys_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec keys_loop xla l i k =
  if bdec (ltb i l)
  then keys_loop xla l (add i (Uint63.of_int (1)))
         (set k i (add (lsl0 (get xla i) (Uint63.of_int (13))) i))
  else k

(** val st_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec st_loop k p st =
  if bdec (ltb (Uint63.of_int (0)) p)
  then st_loop k (sub p (Uint63.of_int (1)))
         (set st (src_of (get k (sub p (Uint63.of_int (1)))))
           (sub p (Uint63.of_int (1))))
  else st

(** val bnd_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec bnd_loop xlx xly l i b =
  if bdec (ltb i l)
  then bnd_loop xlx xly l (add i (Uint63.of_int (1)))
         (set (set b (add (add i i) (Uint63.of_int (2))) (get xlx i))
           (add (add i i) (Uint63.of_int (3)))
           (add (get xly i) (Uint63.of_int (1))))
  else b

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> (Uint63.t
    Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec scan k xlb xlx xly l u k0 stamp p vis stk sp =
  if bdec (ltb p l)
  then let key = get k p in
       if eqb (src_of key) u
       then let i = idx_of key in
            let v = get xlb i in
            if (&&)
                 ((&&) ((&&) (leb (get xlx i) k0) (leb k0 (get xly i)))
                   (negb (eqb (get vis v) stamp)))
                 (ltb v (length vis))
            then scan k xlb xlx xly l u k0 stamp (add p (Uint63.of_int (1)))
                   (set vis v stamp) (set stk sp v)
                   (add sp (Uint63.of_int (1)))
            else scan k xlb xlx xly l u k0 stamp (add p (Uint63.of_int (1)))
                   vis stk sp
       else ((vis, stk), sp)
  else ((vis, stk), sp)

(** val dfs :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t
    Marray.t * Uint63.t Marray.t **)

let rec dfs k st xlb xlx xly l k0 stamp vis stk sp =
  if bdec (ltb (Uint63.of_int (0)) sp)
  then let u = get stk (sub sp (Uint63.of_int (1))) in
       let r =
         scan k xlb xlx xly l u k0 stamp (get st u) vis stk
           (sub sp (Uint63.of_int (1)))
       in
       dfs k st xlb xlx xly l k0 stamp (fst (fst r)) (snd (fst r)) (snd r)
  else (vis, stk)

(** val count_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> Uint63.t **)

let rec count_loop k st xlb xlx xly s l m s0 d j vis stk acc =
  if bdec (ltb j m)
  then let p = get s (sub j (Uint63.of_int (1))) in
       let q = get s j in
       if ltb p q
       then let r =
              dfs k st xlb xlx xly l p j (set vis s0 j)
                (set stk (Uint63.of_int (0)) s0) (Uint63.of_int (1))
            in
            count_loop k st xlb xlx xly s l m s0 d
              (add j (Uint63.of_int (1))) (fst r) (snd r)
              (if eqb (get (fst r) d) j then add acc (sub q p) else acc)
       else count_loop k st xlb xlx xly s l m s0 d
              (add j (Uint63.of_int (1))) vis stk acc
  else acc

(** val securitybadge_core :
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t **)

let securitybadge_core n b s d xla xlb xlx xly =
  let l = length xla in
  let k =
    msort (keys_loop xla l (Uint63.of_int (0)) (make l (Uint63.of_int (0))))
  in
  let st = st_loop k l (make (add n (Uint63.of_int (2))) l) in
  let m = add (add l l) (Uint63.of_int (2)) in
  let s0 =
    msort
      (bnd_loop xlx xly l (Uint63.of_int (0))
        (set
          (set (make m (Uint63.of_int (0))) (Uint63.of_int (0))
            (Uint63.of_int (1)))
          (Uint63.of_int (1)) (add b (Uint63.of_int (1)))))
  in
  count_loop k st xlb xlx xly s0 l m s d (Uint63.of_int (1))
    (make (add n (Uint63.of_int (1))) (Uint63.of_int (0)))
    (make (add n (Uint63.of_int (1))) (Uint63.of_int (0))) (Uint63.of_int (0))

(** val securitybadge_impl :
    uint -> uint -> uint -> uint -> uint Marray.t -> uint Marray.t -> uint
    Marray.t -> uint Marray.t -> uint **)

let securitybadge_impl =
  securitybadge_core

module SecuritybadgeImpl =
 struct
  (** val securitybadge :
      uint -> uint -> uint -> uint -> uint Marray.t -> uint Marray.t -> uint
      Marray.t -> uint Marray.t -> uint **)

  let securitybadge =
    securitybadge_impl
 end
