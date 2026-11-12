
(** val add : Uint63.t -> Uint63.t -> Uint63.t **)

let add = Uint63.add

(** val sub : Uint63.t -> Uint63.t -> Uint63.t **)

let sub = Uint63.sub

(** val ltb : Uint63.t -> Uint63.t -> bool **)

let ltb = Uint63.lt

(** val leb : Uint63.t -> Uint63.t -> bool **)

let leb = Uint63.le

(** val ltsb : Uint63.t -> Uint63.t -> bool **)

let ltsb = Uint63.lts

(** val lesb : Uint63.t -> Uint63.t -> bool **)

let lesb = Uint63.les

(** val get : 'a1 Marray.t -> Uint63.t -> 'a1 **)

let get = Marray.get

(** val length : 'a1 Marray.t -> Uint63.t **)

let length = Marray.length

type sint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

type tree =
| Leaf
| Node of tree * Uint63.t * Uint63.t * tree * Uint63.t

(** val height : tree -> Uint63.t **)

let height = function
| Leaf -> (Uint63.of_int (0))
| Node (_, _, _, _, h) -> h

(** val hmax : Uint63.t -> Uint63.t -> Uint63.t **)

let hmax a b =
  if ltb a b then b else a

(** val node : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let node l k v r =
  Node (l, k, v, r, (add (hmax (height l) (height r)) (Uint63.of_int (1))))

(** val bal : tree -> Uint63.t -> Uint63.t -> tree -> tree **)

let bal l k v r =
  let hl = height l in
  let hr = height r in
  if ltb (add hr (Uint63.of_int (2))) hl
  then (match l with
        | Leaf -> node l k v r
        | Node (ll, lk, lv, lr, _) ->
          if leb (height lr) (height ll)
          then node ll lk lv (node lr k v r)
          else (match lr with
                | Leaf -> node l k v r
                | Node (lrl, lrk, lrv, lrr, _) ->
                  node (node ll lk lv lrl) lrk lrv (node lrr k v r)))
  else if ltb (add hl (Uint63.of_int (2))) hr
       then (match r with
             | Leaf -> node l k v r
             | Node (rl, rk, rv, rr, _) ->
               if leb (height rl) (height rr)
               then node (node l k v rl) rk rv rr
               else (match rl with
                     | Leaf -> node l k v r
                     | Node (rll, rlk, rlv, rlr, _) ->
                       node (node l k v rll) rlk rlv (node rlr rk rv rr)))
       else node l k v r

(** val insert : Uint63.t -> Uint63.t -> tree -> tree **)

let rec insert k v = function
| Leaf -> Node (Leaf, k, v, Leaf, (Uint63.of_int (1)))
| Node (l, k', v', r, h) ->
  if ltsb k k'
  then bal (insert k v l) k' v' r
  else if ltsb k' k then bal l k' v' (insert k v r) else Node (l, k, v, r, h)

(** val remove_min :
    tree -> Uint63.t -> Uint63.t -> tree -> (Uint63.t * Uint63.t) * tree **)

let rec remove_min l k v r =
  match l with
  | Leaf -> ((k, v), r)
  | Node (ll, lk, lv, lr, _) ->
    let (p, l') = remove_min ll lk lv lr in (p, (bal l' k v r))

(** val merge : tree -> tree -> tree **)

let merge l r =
  match l with
  | Leaf -> r
  | Node (_, _, _, _, _) ->
    (match r with
     | Leaf -> l
     | Node (rl, rk, rv, rr, _) ->
       let (p, r') = remove_min rl rk rv rr in
       let (mk, mv) = p in bal l mk mv r')

(** val remove : Uint63.t -> tree -> tree **)

let rec remove k = function
| Leaf -> Leaf
| Node (l, k', v', r, _) ->
  if ltsb k k'
  then bal (remove k l) k' v' r
  else if ltsb k' k then bal l k' v' (remove k r) else merge l r

(** val between : Uint63.t -> Uint63.t -> tree -> bool **)

let rec between lo hi = function
| Leaf -> false
| Node (l, k, _, r, _) ->
  if lesb k lo
  then between lo hi r
  else if lesb hi k then between lo hi l else true

(** val build :
    sint Marray.t -> sint Marray.t -> Uint63.t -> Uint63.t -> tree -> tree **)

let rec build x1 x2 n i t =
  if bdec (ltb i n)
  then build x1 x2 n (add i (Uint63.of_int (1)))
         (insert (get x2 i) (add n i) (insert (get x1 i) i t))
  else t

(** val step :
    Uint63.t -> sint Marray.t -> sint Marray.t -> Uint63.t -> tree -> tree
    option **)

let step n y1 y2 v s =
  if ltb v n
  then let lo = get y1 v in
       let hi = get y2 v in
       if between lo hi s
       then None
       else Some
              (insert hi (Uint63.of_int (0))
                (insert lo (Uint63.of_int (0)) s))
  else let i = sub v n in
       let lo = get y1 i in
       let hi = get y2 i in
       let s' = remove hi (remove lo s) in
       if between lo hi s' then None else Some s'

(** val sweep :
    Uint63.t -> sint Marray.t -> sint Marray.t -> tree -> tree -> tree option **)

let rec sweep n y1 y2 t s =
  match t with
  | Leaf -> Some s
  | Node (l, _, v, r, _) ->
    (match sweep n y1 y2 l s with
     | Some s1 ->
       (match step n y1 y2 v s1 with
        | Some s2 -> sweep n y1 y2 r s2
        | None -> None)
     | None -> None)

(** val intersecting_rectangles_impl :
    sint Marray.t -> sint Marray.t -> sint Marray.t -> sint Marray.t -> bool **)

let intersecting_rectangles_impl x1 y1 x2 y2 =
  let n = length x1 in
  let ev = build x1 x2 n (Uint63.of_int (0)) Leaf in
  (match sweep n y1 y2 ev Leaf with
   | Some _ -> false
   | None -> true)

(** val intersecting_rectangles :
    sint Marray.t -> sint Marray.t -> sint Marray.t -> sint Marray.t -> bool **)

let intersecting_rectangles =
  intersecting_rectangles_impl
