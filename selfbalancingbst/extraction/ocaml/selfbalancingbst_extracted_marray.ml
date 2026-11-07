
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val eqb : Uint63.t -> Uint63.t -> bool **)

let eqb = Uint63.equal

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val make : Uint63.t -> 'a1 -> 'a1 Marray.t **)

let make = Marray.make

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val set : 'a1 Marray.t -> Uint63.t -> 'a1 -> 'a1 Marray.t **)

let set = Marray.set

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type uint = Uint63.t

type sint = Uint63.t

type color =
| Red
| Black

type tree =
| Leaf
| Node of color * tree * Uint63.t * Uint63.t * Uint63.t * tree

(** val size : tree -> Uint63.t **)

let size = function
| Leaf -> (Uint63.of_int (0))
| Node (_, _, _, _, s, _) -> s

(** val node : color -> tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let node c l k v r =
  Node (c, l, k, v, (add (add (size l) (size r)) (Uint63.of_int (1))), r)

(** val key_lt : Uint63.t -> Uint63.t -> bool **)

let key_lt =
  ltsb

(** val makeBlack : tree -> tree **)

let makeBlack = function
| Leaf -> Leaf
| Node (_, l, k, v, s, r) -> Node (Black, l, k, v, s, r)

(** val makeRed : tree -> tree **)

let makeRed = function
| Leaf -> Leaf
| Node (_, l, k, v, s, r) -> Node (Red, l, k, v, s, r)

(** val lbal : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let lbal l k v r =
  match l with
  | Leaf -> node Black l k v r
  | Node (c0, a, x, vx, _, c) ->
    (match c0 with
     | Red ->
       (match a with
        | Leaf ->
          (match c with
           | Leaf -> node Black l k v r
           | Node (c1, b, y, vy, _, c2) ->
             (match c1 with
              | Red ->
                node Red (node Black a x vx b) y vy (node Black c2 k v r)
              | Black -> node Black l k v r))
        | Node (c1, a0, x0, vx0, _, b) ->
          (match c1 with
           | Red ->
             node Red (node Black a0 x0 vx0 b) x vx (node Black c k v r)
           | Black ->
             (match c with
              | Leaf -> node Black l k v r
              | Node (c2, b0, y, vy, _, c3) ->
                (match c2 with
                 | Red ->
                   node Red (node Black a x vx b0) y vy (node Black c3 k v r)
                 | Black -> node Black l k v r))))
     | Black -> node Black l k v r)

(** val rbal : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let rbal l k v r = match r with
| Leaf -> node Black l k v r
| Node (c0, b, y, vy, _, d) ->
  (match c0 with
   | Red ->
     (match b with
      | Leaf ->
        (match d with
         | Leaf -> node Black l k v r
         | Node (c1, c, z, vz, _, d0) ->
           (match c1 with
            | Red -> node Red (node Black l k v b) y vy (node Black c z vz d0)
            | Black -> node Black l k v r))
      | Node (c1, b0, y0, vy0, _, c) ->
        (match c1 with
         | Red -> node Red (node Black l k v b0) y0 vy0 (node Black c y vy d)
         | Black ->
           (match d with
            | Leaf -> node Black l k v r
            | Node (c2, c3, z, vz, _, d0) ->
              (match c2 with
               | Red ->
                 node Red (node Black l k v b) y vy (node Black c3 z vz d0)
               | Black -> node Black l k v r))))
   | Black -> node Black l k v r)

(** val rbal' : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let rbal' l k v r = match r with
| Leaf -> node Black l k v r
| Node (c0, b, z, vz, _, d) ->
  (match c0 with
   | Red ->
     (match b with
      | Leaf ->
        (match d with
         | Leaf -> node Black l k v r
         | Node (c1, c, z0, vz0, _, d0) ->
           (match c1 with
            | Red ->
              node Red (node Black l k v b) z vz (node Black c z0 vz0 d0)
            | Black -> node Black l k v r))
      | Node (c1, b0, y, vy, _, c) ->
        (match c1 with
         | Red ->
           (match d with
            | Leaf ->
              node Red (node Black l k v b0) y vy (node Black c z vz d)
            | Node (c2, c3, z0, vz0, _, d0) ->
              (match c2 with
               | Red ->
                 node Red (node Black l k v b) z vz (node Black c3 z0 vz0 d0)
               | Black ->
                 node Red (node Black l k v b0) y vy (node Black c z vz d)))
         | Black ->
           (match d with
            | Leaf -> node Black l k v r
            | Node (c2, c3, z0, vz0, _, d0) ->
              (match c2 with
               | Red ->
                 node Red (node Black l k v b) z vz (node Black c3 z0 vz0 d0)
               | Black -> node Black l k v r))))
   | Black -> node Black l k v r)

(** val ins : Uint63.t -> Uint63.t -> tree -> tree **)

let rec ins x vx t = match t with
| Leaf -> node Red Leaf x vx Leaf
| Node (c, l, y, vy, _, r) ->
  if key_lt x y
  then (match c with
        | Red -> node Red (ins x vx l) y vy r
        | Black -> lbal (ins x vx l) y vy r)
  else if eqb x y
       then t
       else (match c with
             | Red -> node Red l y vy (ins x vx r)
             | Black -> rbal l y vy (ins x vx r))

(** val insert_t : Uint63.t -> Uint63.t -> tree -> tree **)

let insert_t x vx t =
  makeBlack (ins x vx t)

(** val lbalS : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let lbalS l k v r =
  match l with
  | Leaf ->
    (match r with
     | Leaf -> node Red l k v r
     | Node (c0, a, z, vz, _, c) ->
       (match c0 with
        | Red ->
          (match a with
           | Leaf -> node Red l k v r
           | Node (c1, a0, y, vy, _, b) ->
             (match c1 with
              | Red -> node Red l k v r
              | Black ->
                node Red (node Black l k v a0) y vy (rbal' b z vz (makeRed c))))
        | Black -> rbal' l k v (node Red a z vz c)))
  | Node (c, a, x, vx, _, b) ->
    (match c with
     | Red -> node Red (node Black a x vx b) k v r
     | Black ->
       (match r with
        | Leaf -> node Red l k v r
        | Node (c0, a0, z, vz, _, c1) ->
          (match c0 with
           | Red ->
             (match a0 with
              | Leaf -> node Red l k v r
              | Node (c2, a1, y, vy, _, b0) ->
                (match c2 with
                 | Red -> node Red l k v r
                 | Black ->
                   node Red (node Black l k v a1) y vy
                     (rbal' b0 z vz (makeRed c1))))
           | Black -> rbal' l k v (node Red a0 z vz c1))))

(** val rbalS : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let rbalS l k v r = match r with
| Leaf ->
  (match l with
   | Leaf -> node Red l k v r
   | Node (c0, a, x, vx, _, b) ->
     (match c0 with
      | Red ->
        (match b with
         | Leaf -> node Red l k v r
         | Node (c1, b0, y, vy, _, c) ->
           (match c1 with
            | Red -> node Red l k v r
            | Black ->
              node Red (lbal (makeRed a) x vx b0) y vy (node Black c k v r)))
      | Black -> lbal (node Red a x vx b) k v r))
| Node (c0, b, y, vy, _, c) ->
  (match c0 with
   | Red -> node Red l k v (node Black b y vy c)
   | Black ->
     (match l with
      | Leaf -> node Red l k v r
      | Node (c1, a, x, vx, _, b0) ->
        (match c1 with
         | Red ->
           (match b0 with
            | Leaf -> node Red l k v r
            | Node (c2, b1, y0, vy0, _, c3) ->
              (match c2 with
               | Red -> node Red l k v r
               | Black ->
                 node Red (lbal (makeRed a) x vx b1) y0 vy0
                   (node Black c3 k v r)))
         | Black -> lbal (node Red a x vx b0) k v r)))

(** val append : tree -> tree -> tree **)

let rec append l = match l with
| Leaf -> (fun r -> r)
| Node (lc, ll, lx, lv, _, lr) ->
  let rec append_l r = match r with
  | Leaf -> l
  | Node (rc, rl, rx, rv, _, rr) ->
    (match lc with
     | Red ->
       (match rc with
        | Red ->
          let lrl = append lr rl in
          (match lrl with
           | Leaf -> node Red ll lx lv (node Red lrl rx rv rr)
           | Node (c, lr', x, vx, _, rl') ->
             (match c with
              | Red ->
                node Red (node Red ll lx lv lr') x vx (node Red rl' rx rv rr)
              | Black -> node Red ll lx lv (node Red lrl rx rv rr)))
        | Black -> node Red ll lx lv (append lr r))
     | Black ->
       (match rc with
        | Red -> node Red (append_l rl) rx rv rr
        | Black ->
          let lrl = append lr rl in
          (match lrl with
           | Leaf -> lbalS ll lx lv (node Black lrl rx rv rr)
           | Node (c, lr', x, vx, _, rl') ->
             (match c with
              | Red ->
                node Red (node Black ll lx lv lr') x vx
                  (node Black rl' rx rv rr)
              | Black -> lbalS ll lx lv (node Black lrl rx rv rr)))))
  in append_l

(** val del : Uint63.t -> tree -> tree **)

let rec del x = function
| Leaf -> Leaf
| Node (_, a, y, vy, _, b) ->
  if key_lt x y
  then (match a with
        | Leaf -> node Red (del x a) y vy b
        | Node (c, _, _, _, _, _) ->
          (match c with
           | Red -> node Red (del x a) y vy b
           | Black -> lbalS (del x a) y vy b))
  else if eqb x y
       then append a b
       else (match b with
             | Leaf -> node Red a y vy (del x b)
             | Node (c, _, _, _, _, _) ->
               (match c with
                | Red -> node Red a y vy (del x b)
                | Black -> rbalS a y vy (del x b)))

(** val delete_t : Uint63.t -> tree -> tree **)

let delete_t x t =
  makeBlack (del x t)

(** val find_t : Uint63.t -> tree -> Uint63.t option **)

let rec find_t x = function
| Leaf -> None
| Node (_, l, k, _, _, r) ->
  if key_lt x k then find_t x l else if eqb x k then Some k else find_t x r

(** val lower_t : Uint63.t -> tree -> Uint63.t option **)

let rec lower_t x = function
| Leaf -> None
| Node (_, l, k, _, _, r) ->
  if key_lt k x
  then lower_t x r
  else (match lower_t x l with
        | Some z -> Some z
        | None -> Some k)

(** val upper_t : Uint63.t -> tree -> Uint63.t option **)

let rec upper_t x = function
| Leaf -> None
| Node (_, l, k, _, _, r) ->
  if key_lt x k
  then (match upper_t x l with
        | Some z -> Some z
        | None -> Some k)
  else upper_t x r

(** val pred_t : Uint63.t -> tree -> Uint63.t option **)

let rec pred_t x = function
| Leaf -> None
| Node (_, l, k, _, _, r) ->
  if key_lt k x
  then (match pred_t x r with
        | Some z -> Some z
        | None -> Some k)
  else pred_t x l

(** val front_t : tree -> Uint63.t option **)

let rec front_t = function
| Leaf -> None
| Node (_, l, k, _, _, _) ->
  (match front_t l with
   | Some z -> Some z
   | None -> Some k)

(** val back_t : tree -> Uint63.t option **)

let rec back_t = function
| Leaf -> None
| Node (_, _, k, _, _, r) ->
  (match back_t r with
   | Some z -> Some z
   | None -> Some k)

(** val kth_t : Uint63.t -> tree -> Uint63.t option **)

let rec kth_t n = function
| Leaf -> None
| Node (_, l, k, _, _, r) ->
  let sl = size l in
  if ltb n sl
  then kth_t n l
  else if eqb n sl
       then Some k
       else kth_t (sub (sub n sl) (Uint63.of_int (1))) r

(** val rank_t : Uint63.t -> tree -> Uint63.t **)

let rec rank_t x = function
| Leaf -> (Uint63.of_int (0))
| Node (_, l, k, _, _, r) ->
  if key_lt x k
  then rank_t x l
  else if eqb x k
       then size l
       else add (add (size l) (Uint63.of_int (1))) (rank_t x r)

(** val lookup_t : Uint63.t -> tree -> Uint63.t option **)

let rec lookup_t x = function
| Leaf -> None
| Node (_, l, k, v, _, r) ->
  if key_lt x k
  then lookup_t x l
  else if eqb x k then Some v else lookup_t x r

(** val setv_t : Uint63.t -> Uint63.t -> tree -> tree **)

let rec setv_t x w = function
| Leaf -> Leaf
| Node (c, l, k, v, s, r) ->
  if key_lt x k
  then Node (c, (setv_t x w l), k, v, s, r)
  else if eqb x k
       then Node (c, l, k, w, s, r)
       else Node (c, l, k, v, s, (setv_t x w r))

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val is_out : Uint63.t -> bool **)

let is_out op =
  (||) ((||) (eqb op (Uint63.of_int (114))) (eqb op (Uint63.of_int (103))))
    (eqb op (Uint63.of_int (122)))

(** val count_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec count_loop ops q j acc =
  if bdec (ltb j q)
  then count_loop ops q (add j (Uint63.of_int (1)))
         (if is_out (get ops j) then add acc (Uint63.of_int (1)) else acc)
  else acc

(** val on_cur :
    Uint63.t option -> (Uint63.t -> Uint63.t option) -> Uint63.t option **)

let on_cur cur f =
  match cur with
  | Some c -> f c
  | None -> None

(** val exec :
    tree Marray.t -> Uint63.t option Marray.t -> Uint63.t option Marray.t ->
    Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> ((tree
    Marray.t * Uint63.t option Marray.t) * Uint63.t option
    Marray.t) * Uint63.t **)

let exec t c o p id op x y =
  let t0 = get t id in
  let cur = get c id in
  if eqb op (Uint63.of_int (97))
  then ((((set t id (get t x)), (set c id None)), o), p)
  else if eqb op (Uint63.of_int (63))
       then (((t, (set c id (find_t x t0))), o), p)
       else if eqb op (Uint63.of_int (108))
            then (((t, (set c id (lower_t x t0))), o), p)
            else if eqb op (Uint63.of_int (117))
                 then (((t, (set c id (upper_t x t0))), o), p)
                 else if eqb op (Uint63.of_int (105))
                      then ((((set t id (insert_t x y t0)),
                             (set c id (Some x))), o), p)
                      else if eqb op (Uint63.of_int (101))
                           then ((((set t id
                                     (match cur with
                                      | Some c0 -> delete_t c0 t0
                                      | None -> t0)),
                                  (set c id None)), o), p)
                           else if eqb op (Uint63.of_int (102))
                                then (((t, (set c id (front_t t0))), o), p)
                                else if eqb op (Uint63.of_int (98))
                                     then (((t, (set c id (back_t t0))), o),
                                            p)
                                     else if eqb op (Uint63.of_int (62))
                                          then (((t,
                                                 (set c id
                                                   (on_cur cur (fun c0 ->
                                                     upper_t c0 t0)))),
                                                 o), p)
                                          else if eqb op (Uint63.of_int (60))
                                               then (((t,
                                                      (set c id
                                                        (on_cur cur
                                                          (fun c0 ->
                                                          pred_t c0 t0)))),
                                                      o), p)
                                               else if eqb op
                                                         (Uint63.of_int (107))
                                                    then (((t,
                                                           (set c id
                                                             (if ltsb x
                                                                   (Uint63.of_int (0))
                                                              then None
                                                              else kth_t x t0))),
                                                           o), p)
                                                    else if eqb op
                                                              (Uint63.of_int (114))
                                                         then (((t, c),
                                                                (set o p
                                                                  (on_cur cur
                                                                    (fun c0 ->
                                                                    Some
                                                                    (rank_t
                                                                    c0 t0))))),
                                                                (add p
                                                                  (Uint63.of_int (1))))
                                                         else if eqb op
                                                                   (Uint63.of_int (103))
                                                              then (((t, c),
                                                                    (set o p
                                                                    (on_cur
                                                                    cur
                                                                    (fun c0 ->
                                                                    lookup_t
                                                                    c0 t0)))),
                                                                    (add p
                                                                    (Uint63.of_int (1))))
                                                              else if 
                                                                    eqb op
                                                                    (Uint63.of_int (115))
                                                                   then 
                                                                    (((
                                                                    (set t id
                                                                    (match cur with
                                                                    | Some c0 ->
                                                                    setv_t c0
                                                                    x t0
                                                                    | None ->
                                                                    t0)), c),
                                                                    o), p)
                                                                   else 
                                                                    if 
                                                                    eqb op
                                                                    (Uint63.of_int (122))
                                                                    then 
                                                                    (((t, c),
                                                                    (set o p
                                                                    (Some
                                                                    (size t0)))),
                                                                    (add p
                                                                    (Uint63.of_int (1))))
                                                                    else 
                                                                    (((t, c),
                                                                    o), p)

(** val run_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t -> Uint63.t -> tree Marray.t -> Uint63.t option
    Marray.t -> Uint63.t option Marray.t -> Uint63.t -> Uint63.t option
    Marray.t **)

let rec run_loop ids ops xs ys q j t c o p =
  if bdec (ltb j q)
  then let (p0, p') =
         exec t c o p (get ids j) (get ops j) (get xs j) (get ys j)
       in
       let (p1, o') = p0 in
       let (t', c') = p1 in
       run_loop ids ops xs ys q (add j (Uint63.of_int (1))) t' c' o' p'
  else o

(** val run_impl :
    uint Marray.t -> uint Marray.t -> sint Marray.t -> sint Marray.t -> sint
    option Marray.t **)

let run_impl ids ops xs ys =
  let q = length ids in
  let n = count_loop ops q (Uint63.of_int (0)) (Uint63.of_int (0)) in
  run_loop ids ops xs ys q (Uint63.of_int (0))
    (make (Uint63.of_int (1001)) Leaf) (make (Uint63.of_int (1001)) None)
    (make n None) (Uint63.of_int (0))

module SelfbalancingbstImpl =
 struct
  (** val run_commands :
      uint Marray.t -> uint Marray.t -> sint Marray.t -> sint Marray.t ->
      sint option Marray.t **)

  let run_commands =
    run_impl
 end
