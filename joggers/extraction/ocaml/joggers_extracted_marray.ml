
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

(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val ep :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let ep xa xb m k =
  if ltb k m then get xa k else get xb (sub k m)

(** val oth :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let oth xa xb m k =
  if ltb k m then get xb k else get xa (sub k m)

(** val eid : Uint63.t -> Uint63.t -> Uint63.t **)

let eid m k =
  if ltb k m then k else sub k m

(** val lamp_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> bool Marray.t -> bool
    Marray.t **)

let rec lamp_loop xl l i inl =
  if bdec (ltb i l)
  then lamp_loop xl l (add i (Uint63.of_int (1))) (set inl (get xl i) true)
  else inl

(** val cnt_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec cnt_loop xa xb m k i cnt =
  if bdec (ltb i k)
  then let w = ep xa xb m i in
       cnt_loop xa xb m k (add i (Uint63.of_int (1)))
         (set cnt w (add (get cnt w) (Uint63.of_int (1))))
  else cnt

(** val off_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec off_loop cnt v v0 off cur =
  if bdec (ltb v0 v)
  then let o = get off v0 in
       off_loop cnt v (add v0 (Uint63.of_int (1)))
         (set off (add v0 (Uint63.of_int (1))) (add o (get cnt v0)))
         (set cur v0 o)
  else (off, cur)

(** val fill_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fill_loop xa xb m k i cur adj =
  if bdec (ltb i k)
  then let w = ep xa xb m i in
       let c = get cur w in
       fill_loop xa xb m k (add i (Uint63.of_int (1)))
         (set cur w (add c (Uint63.of_int (1)))) (set adj c i)
  else adj

type bst = { vis : bool Marray.t; dst : Uint63.t Marray.t;
             par : Uint63.t Marray.t; pe : Uint63.t Marray.t;
             ord : Uint63.t Marray.t; tl : Uint63.t }

(** val scan_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    bst -> bst **)

let rec scan_loop xa xb xd m adj u du hi i st =
  if bdec (ltb i hi)
  then let k = get adj i in
       let w = oth xa xb m k in
       let st' =
         if get st.vis w
         then st
         else let e = eid m k in
              { vis = (set st.vis w true); dst =
              (set st.dst w (add du (get xd e))); par = (set st.par w u);
              pe = (set st.pe w e); ord = (set st.ord st.tl w); tl =
              (add st.tl (Uint63.of_int (1))) }
       in
       scan_loop xa xb xd m adj u du hi (add i (Uint63.of_int (1))) st'
  else st

(** val bfs_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> bst -> bst **)

let rec bfs_loop xa xb xd m adj off h st =
  if bdec (ltb h st.tl)
  then let u = get st.ord h in
       let st' =
         scan_loop xa xb xd m adj u (get st.dst u)
           (get off (add u (Uint63.of_int (1)))) (get off u) st
       in
       bfs_loop xa xb xd m adj off (add h (Uint63.of_int (1))) st'
  else st

(** val sweep_loop :
    Uint63.t -> bool Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t -> bool Marray.t -> Uint63.t -> Uint63.t **)

let rec sweep_loop s inl ord0 par0 dst0 i ch c =
  if bdec (ltb (Uint63.of_int (0)) i)
  then let v = get ord0 i in
       let p = get par0 v in
       let dp = get dst0 p in
       if (&&)
            ((&&) (ltb (add dp dp) s) (negb ((||) (get inl v) (get ch v))))
            (negb ((||) (get inl p) (get ch p)))
       then sweep_loop s inl ord0 par0 dst0 (sub i (Uint63.of_int (1)))
              (set ch p true) (add c (Uint63.of_int (1)))
       else sweep_loop s inl ord0 par0 dst0 (sub i (Uint63.of_int (1))) ch c
  else c

(** val joggers_impl :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t **)

let joggers_impl n s xa xb xd xl =
  let m = length xa in
  let k = add m m in
  let v = add n (Uint63.of_int (1)) in
  let inl = lamp_loop xl (length xl) (Uint63.of_int (0)) (make v false) in
  let cnt =
    cnt_loop xa xb m k (Uint63.of_int (0)) (make v (Uint63.of_int (0)))
  in
  let oc =
    off_loop cnt v (Uint63.of_int (0))
      (make (add v (Uint63.of_int (1))) (Uint63.of_int (0)))
      (make v (Uint63.of_int (0)))
  in
  let adj =
    fill_loop xa xb m k (Uint63.of_int (0)) (snd oc)
      (make k (Uint63.of_int (0)))
  in
  let st0 = { vis = (set (make v false) (Uint63.of_int (1)) true); dst =
    (make v (Uint63.of_int (0))); par = (make v (Uint63.of_int (0))); pe =
    (make v (Uint63.of_int (0))); ord =
    (set (make n (Uint63.of_int (0))) (Uint63.of_int (0)) (Uint63.of_int (1)));
    tl = (Uint63.of_int (1)) }
  in
  let st = bfs_loop xa xb xd m adj (fst oc) (Uint63.of_int (0)) st0 in
  sweep_loop s inl st.ord st.par st.dst (sub st.tl (Uint63.of_int (1)))
    (make v false) (Uint63.of_int (0))

module JoggersImpl =
 struct
  (** val joggers :
      uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t -> uint
      Marray.t -> uint **)

  let joggers =
    joggers_impl
 end
