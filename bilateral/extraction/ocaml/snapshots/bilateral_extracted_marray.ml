
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

(** val nV : Uint63.t **)

let nV =
  (Uint63.of_int (1000))

(** val nP : Uint63.t **)

let nP =
  (Uint63.of_int (1001))

(** val nM : Uint63.t **)

let nM =
  (Uint63.of_int (2000))

(** val deg_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t
    Marray.t -> Uint63.t Marray.t **)

let rec deg_loop x ex m k d =
  if bdec (ltb k m)
  then let a = get x k in
       deg_loop x ex m (add k (Uint63.of_int (1)))
         (if eqb a ex
          then d
          else let u = sub a (Uint63.of_int (1000)) in
               set d u (add (get d u) (Uint63.of_int (1))))
  else d

(** val off_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec off_loop d u o =
  if bdec (ltb u nV)
  then off_loop d (add u (Uint63.of_int (1)))
         (set o (add u (Uint63.of_int (1))) (add (get o u) (get d u)))
  else o

(** val fill_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t **)

let rec fill_loop x y ex m k pos tg =
  if bdec (ltb k m)
  then let a = get x k in
       if eqb a ex
       then fill_loop x y ex m (add k (Uint63.of_int (1))) pos tg
       else let u = sub a (Uint63.of_int (1000)) in
            let p = get pos u in
            fill_loop x y ex m (add k (Uint63.of_int (1)))
              (set pos u (add p (Uint63.of_int (1))))
              (set tg p (sub (get y k) (Uint63.of_int (2000))))
  else tg

(** val root_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> (Uint63.t Marray.t * Uint63.t Marray.t) * Uint63.t **)

let rec root_loop mL u q qp t =
  if bdec (ltb u nV)
  then if ltb (get mL u) nV
       then root_loop mL (add u (Uint63.of_int (1))) q qp t
       else root_loop mL (add u (Uint63.of_int (1))) (set q t u)
              (set qp u (add t (Uint63.of_int (1))))
              (add t (Uint63.of_int (1)))
  else ((q, qp), t)

type sres =
| SFound of Uint63.t * Uint63.t Marray.t * Uint63.t Marray.t
| SCont of Uint63.t Marray.t * Uint63.t Marray.t * Uint63.t Marray.t
   * Uint63.t

(** val scan :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t ->
    Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t
    -> Uint63.t -> sres **)

let rec scan tg mR u pe p q qp pr t =
  if bdec (ltb p pe)
  then let v = get tg p in
       if eqb (get pr v) (Uint63.of_int (0))
       then let pr0 = set pr v (add u (Uint63.of_int (1))) in
            let w = get mR v in
            if ltb w nV
            then if eqb (get qp w) (Uint63.of_int (0))
                 then scan tg mR u pe (add p (Uint63.of_int (1))) (set q t w)
                        (set qp w (add t (Uint63.of_int (1)))) pr0
                        (add t (Uint63.of_int (1)))
                 else scan tg mR u pe (add p (Uint63.of_int (1))) q qp pr0 t
            else SFound (v, qp, pr0)
       else scan tg mR u pe (add p (Uint63.of_int (1))) q qp pr t
  else SCont (q, qp, pr, t)

type bres =
| BFound of Uint63.t * Uint63.t Marray.t * Uint63.t Marray.t
| BFail of Uint63.t Marray.t * Uint63.t Marray.t

(** val bfs :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    -> Uint63.t -> Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t
    Marray.t -> bres **)

let rec bfs off tg mR h t q qp pr =
  if bdec (ltb h nV)
  then if ltb h t
       then let u = get q h in
            (match scan tg mR u (get off (add u (Uint63.of_int (1))))
                     (get off u) q qp pr t with
             | SFound (v, qp0, pr0) -> BFound (v, qp0, pr0)
             | SCont (q0, qp0, pr0, t0) ->
               bfs off tg mR (add h (Uint63.of_int (1))) t0 q0 qp0 pr0)
       else BFail (qp, pr)
  else BFail (qp, pr)

(** val walk :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec walk qp pr v mL mR =
  let u = sub (get pr v) (Uint63.of_int (1)) in
  let old = get mL u in
  let mL' = set mL u v in
  let mR' = set mR v u in
  if ltb old nV
  then if bdec
            (ltb (get qp (sub (get pr old) (Uint63.of_int (1))))
              (get qp (sub (get pr v) (Uint63.of_int (1)))))
       then walk qp pr old mL' mR'
       else (mL', mR')
  else (mL', mR')

(** val phases :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t -> Uint63.t Marray.t * Uint63.t Marray.t **)

let rec phases off tg it mL mR =
  if bdec (ltb it nP)
  then let (p, t) =
         root_loop mL (Uint63.of_int (0)) (make nV (Uint63.of_int (0)))
           (make nV (Uint63.of_int (0))) (Uint63.of_int (0))
       in
       let (q, qp) = p in
       (match bfs off tg mR (Uint63.of_int (0)) t q qp
                (make nV (Uint63.of_int (0))) with
        | BFound (v, qp0, pr) ->
          let (mL0, mR0) = walk qp0 pr v mL mR in
          phases off tg (add it (Uint63.of_int (1))) mL0 mR0
        | BFail (qp0, pr) -> (qp0, pr))
  else ((make nV (Uint63.of_int (0))), (make nV (Uint63.of_int (0))))

(** val mark_loop :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t
    -> Uint63.t Marray.t **)

let rec mark_loop qp pr i mk =
  if bdec (ltb i nM)
  then mark_loop qp pr (add i (Uint63.of_int (1)))
         (if ltb i nV
          then if eqb (get qp i) (Uint63.of_int (0))
               then set mk i (Uint63.of_int (1))
               else mk
          else if eqb (get pr (sub i nV)) (Uint63.of_int (0))
               then mk
               else set mk i (Uint63.of_int (1)))
  else mk

(** val engine :
    Uint63.t Marray.t -> Uint63.t Marray.t -> Uint63.t -> Uint63.t Marray.t **)

let engine x y ex =
  let m = length x in
  let d = deg_loop x ex m (Uint63.of_int (0)) (make nV (Uint63.of_int (0))) in
  let off = off_loop d (Uint63.of_int (0)) (make nP (Uint63.of_int (0))) in
  let pos = off_loop d (Uint63.of_int (0)) (make nP (Uint63.of_int (0))) in
  let tg =
    fill_loop x y ex m (Uint63.of_int (0)) pos (make m (Uint63.of_int (0)))
  in
  let (qp, pr) = phases off tg (Uint63.of_int (0)) (make nV nV) (make nV nV)
  in
  mark_loop qp pr (Uint63.of_int (0)) (make nM (Uint63.of_int (0)))

(** val cnt_loop : Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t **)

let rec cnt_loop mk i c =
  if bdec (ltb i nM)
  then cnt_loop mk (add i (Uint63.of_int (1)))
         (if eqb (get mk i) (Uint63.of_int (0))
          then c
          else add c (Uint63.of_int (1)))
  else c

(** val out_loop :
    Uint63.t Marray.t -> Uint63.t -> Uint63.t -> Uint63.t Marray.t ->
    Uint63.t Marray.t **)

let rec out_loop mk i p out =
  if bdec (ltb i nM)
  then if eqb (get mk i) (Uint63.of_int (0))
       then out_loop mk (add i (Uint63.of_int (1))) p out
       else out_loop mk (add i (Uint63.of_int (1)))
              (add p (Uint63.of_int (1)))
              (set out p (add (Uint63.of_int (1000)) i))
  else out

(** val count_marks : Uint63.t Marray.t -> Uint63.t **)

let count_marks mk =
  cnt_loop mk (Uint63.of_int (0)) (Uint63.of_int (0))

(** val build : Uint63.t Marray.t -> Uint63.t Marray.t **)

let build mk =
  out_loop mk (Uint63.of_int (0)) (Uint63.of_int (0))
    (make (count_marks mk) (Uint63.of_int (0)))

(** val bilateral_impl : uint Marray.t -> uint Marray.t -> uint Marray.t **)

let bilateral_impl x y =
  let mk1 = engine x y (Uint63.of_int (1009)) in
  let mk0 = engine x y (Uint63.of_int (0)) in
  build
    (if leb (add (count_marks mk1) (Uint63.of_int (1))) (count_marks mk0)
     then set mk1 (Uint63.of_int (9)) (Uint63.of_int (1))
     else mk0)

(** val bilateral : uint Marray.t -> uint Marray.t -> uint Marray.t **)

let bilateral =
  bilateral_impl
