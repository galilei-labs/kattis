
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

type uint = Uint63.t

(** val bdec : bool -> bool **)

let bdec = function
| true -> true
| false -> false

(** val cnt_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec cnt_loop col m i deg =
  if bdec (ltb i m)
  then let v = get col i in
       cnt_loop col m (add i (Uint63.of_int (1)))
         (set deg v (add (get deg v) (Uint63.of_int (1))))
  else deg

(** val pre_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec pre_loop deg n i acc pos =
  if bdec (ltb i n)
  then pre_loop deg n (add i (Uint63.of_int (1))) (add acc (get deg i))
         (set pos i acc)
  else pos

(** val fill_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec fill_loop col base m i pos adj =
  if bdec (ltb i m)
  then let v = get col i in
       let p = get pos v in
       fill_loop col base m (add i (Uint63.of_int (1)))
         (set pos v (add p (Uint63.of_int (1)))) (set adj p (add base i))
  else (pos, adj)

(** val other :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let other ea eb m hh =
  if ltb hh m then get eb hh else get ea (sub hh m)

(** val nb_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec nb_loop ea eb adj m e s mark stk sp =
  if bdec (ltb s e)
  then let w = other ea eb m (get adj s) in
       if eqb (get mark w) (Uint63.of_int (0))
       then nb_loop ea eb adj m e (add s (Uint63.of_int (1)))
              (set mark w (Uint63.of_int (1))) (set stk sp w)
              (add sp (Uint63.of_int (1)))
       else nb_loop ea eb adj m e (add s (Uint63.of_int (1))) mark stk sp
  else ((mark, stk), sp)

(** val dfs_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t ->
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t -> Uint63.t Marray.t * Uint63.t **)

let rec dfs_loop ea eb adj deg pos n m t mark stk sp lv l =
  if bdec (ltb t n)
  then if ltb (Uint63.of_int (0)) sp
       then let v = get stk (sub sp (Uint63.of_int (1))) in
            let dv = get deg v in
            let e = get pos v in
            let lv' = if eqb dv (Uint63.of_int (1)) then set lv l v else lv in
            let l' =
              if eqb dv (Uint63.of_int (1))
              then add l (Uint63.of_int (1))
              else l
            in
            let (p, sp') =
              nb_loop ea eb adj m e (sub e dv) mark stk
                (sub sp (Uint63.of_int (1)))
            in
            let (mark', stk') = p in
            dfs_loop ea eb adj deg pos n m (add t (Uint63.of_int (1))) mark'
              stk' sp' lv' l'
       else (lv, l)
  else (lv, l)

(** val root_loop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec root_loop deg n i =
  if bdec (ltb i n)
  then if leb (Uint63.of_int (2)) (get deg i)
       then i
       else root_loop deg n (add i (Uint63.of_int (1)))
  else (Uint63.of_int (0))

(** val out_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec out_loop lv a c i xs ys =
  if bdec (ltb i c)
  then out_loop lv a c (add i (Uint63.of_int (1))) (set xs i (get lv i))
         (set ys i (get lv (add i a)))
  else (xs, ys)

(** val kingpin_impl :
    Uint63.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t * Uint63.t Marray.t **)

let kingpin_impl n _ ea eb =
  let m = sub n (Uint63.of_int (1)) in
  let deg0 = cnt_loop ea m (Uint63.of_int (0)) (make n (Uint63.of_int (0))) in
  let deg = cnt_loop eb m (Uint63.of_int (0)) deg0 in
  let pos0 =
    pre_loop deg n (Uint63.of_int (0)) (Uint63.of_int (0))
      (make n (Uint63.of_int (0)))
  in
  let (pos1, adj1) =
    fill_loop ea (Uint63.of_int (0)) m (Uint63.of_int (0)) pos0
      (make (add m m) (Uint63.of_int (0)))
  in
  let (pos, adj) = fill_loop eb m m (Uint63.of_int (0)) pos1 adj1 in
  let r = root_loop deg n (Uint63.of_int (0)) in
  let mark = set (make n (Uint63.of_int (0))) r (Uint63.of_int (1)) in
  let stk = set (make n (Uint63.of_int (0))) (Uint63.of_int (0)) r in
  let (lv, l) =
    dfs_loop ea eb adj deg pos n m (Uint63.of_int (0)) mark stk
      (Uint63.of_int (1)) (make n (Uint63.of_int (0))) (Uint63.of_int (0))
  in
  let a = lsr0 l (Uint63.of_int (1)) in
  let c = sub l a in
  out_loop lv a c (Uint63.of_int (0)) (make c (Uint63.of_int (0)))
    (make c (Uint63.of_int (0)))

module KingpinescapeImpl =
 struct
  (** val kingpin_escape :
      uint -> uint -> uint Marray.t -> uint Marray.t -> uint Marray.t * uint
      Marray.t **)

  let kingpin_escape =
    kingpin_impl
 end
