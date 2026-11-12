
val xorb : bool -> bool -> bool

val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

module Pos :
 sig
  val succ : Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val add_carry : Bigint.t -> Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val iter : ('a1 -> 'a1) -> 'a1 -> Bigint.t -> 'a1

  val div2 : Bigint.t -> Bigint.t

  val div2_up : Bigint.t -> Bigint.t

  val compare_cont : comparison -> Bigint.t -> Bigint.t -> comparison

  val compare : Bigint.t -> Bigint.t -> comparison

  val eqb : Bigint.t -> Bigint.t -> bool
 end

module Z :
 sig
  val double : Bigint.t -> Bigint.t

  val succ_double : Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val pos_sub : Bigint.t -> Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val opp : Bigint.t -> Bigint.t

  val sub : Bigint.t -> Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val compare : Bigint.t -> Bigint.t -> comparison

  val leb : Bigint.t -> Bigint.t -> bool

  val ltb : Bigint.t -> Bigint.t -> bool

  val eqb : Bigint.t -> Bigint.t -> bool

  val max : Bigint.t -> Bigint.t -> Bigint.t

  val min : Bigint.t -> Bigint.t -> Bigint.t

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val even : Bigint.t -> bool

  val div2 : Bigint.t -> Bigint.t

  val shiftl : Bigint.t -> Bigint.t -> Bigint.t
 end

module Coq_Z :
 sig
  val double : Bigint.t -> Bigint.t

  val succ_double : Bigint.t -> Bigint.t

  val pred_double : Bigint.t -> Bigint.t

  val pos_sub : Bigint.t -> Bigint.t -> Bigint.t

  val add : Bigint.t -> Bigint.t -> Bigint.t

  val opp : Bigint.t -> Bigint.t

  val sub : Bigint.t -> Bigint.t -> Bigint.t

  val mul : Bigint.t -> Bigint.t -> Bigint.t

  val compare : Bigint.t -> Bigint.t -> comparison

  val leb : Bigint.t -> Bigint.t -> bool

  val ltb : Bigint.t -> Bigint.t -> bool

  val eqb : Bigint.t -> Bigint.t -> bool

  val max : Bigint.t -> Bigint.t -> Bigint.t

  val min : Bigint.t -> Bigint.t -> Bigint.t

  val pos_div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div_eucl : Bigint.t -> Bigint.t -> Bigint.t * Bigint.t

  val div : Bigint.t -> Bigint.t -> Bigint.t

  val modulo : Bigint.t -> Bigint.t -> Bigint.t

  val div2 : Bigint.t -> Bigint.t

  val shiftl : Bigint.t -> Bigint.t -> Bigint.t

  val abs : Bigint.t -> Bigint.t
 end

val add0 : Uint63.t -> Uint63.t -> Uint63.t

val sub0 : Uint63.t -> Uint63.t -> Uint63.t

val mul0 : Uint63.t -> Uint63.t -> Uint63.t

val eqb0 : Uint63.t -> Uint63.t -> bool

val ltb0 : Uint63.t -> Uint63.t -> bool

val to_Z : Uint63.t -> Bigint.t

val of_Z : Bigint.t -> Uint63.t

val abs0 : Float64.t -> Float64.t

val opp0 : Float64.t -> Float64.t

val eqb1 : Float64.t -> Float64.t -> bool

val ltb1 : Float64.t -> Float64.t -> bool

val leb0 : Float64.t -> Float64.t -> bool

val mul1 : Float64.t -> Float64.t -> Float64.t

val add1 : Float64.t -> Float64.t -> Float64.t

val sub1 : Float64.t -> Float64.t -> Float64.t

val div0 : Float64.t -> Float64.t -> Float64.t

val of_uint63 : Uint63.t -> Float64.t

val normfr_mantissa : Float64.t -> Uint63.t

val frshiftexp : Float64.t -> Float64.t * Uint63.t

val ldshiftexp : Float64.t -> Uint63.t -> Float64.t

val infinity : Float64.t

val neg_infinity : Float64.t

val nan : Float64.t

val one : Float64.t

val zero : Float64.t

val neg_zero : Float64.t

val is_nan : Float64.t -> bool

val is_zero : Float64.t -> bool

val is_infinity : Float64.t -> bool

val is_finite : Float64.t -> bool

val get_sign : Float64.t -> bool

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * Bigint.t * Bigint.t

val emin : Bigint.t -> Bigint.t -> Bigint.t

val fexp : Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t

val digits2_pos : Bigint.t -> Bigint.t

val zdigits2 : Bigint.t -> Bigint.t

val iter_pos : ('a1 -> 'a1) -> Bigint.t -> 'a1 -> 'a1

type location =
| Loc_Exact
| Loc_Inexact of comparison

type shr_record = { shr_m : Bigint.t; shr_r : bool; shr_s : bool }

val shr_1 : shr_record -> shr_record

val loc_of_shr_record : shr_record -> location

val shr_record_of_loc : Bigint.t -> location -> shr_record

val shr : shr_record -> Bigint.t -> Bigint.t -> shr_record * Bigint.t

val shr_fexp :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> location ->
  shr_record * Bigint.t

val round_nearest_even : Bigint.t -> location -> Bigint.t

val binary_round_aux :
  Bigint.t -> Bigint.t -> bool -> Bigint.t -> Bigint.t -> location ->
  spec_float

val new_location_even : Bigint.t -> Bigint.t -> location

val new_location_odd : Bigint.t -> Bigint.t -> location

val new_location : Bigint.t -> Bigint.t -> location

val sFdiv_core_binary :
  Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t -> Bigint.t ->
  (Bigint.t * Bigint.t) * location

val prec : Bigint.t

val emax : Bigint.t

val shift : Bigint.t

type uint = Uint63.t

type 'v outcome =
| Unique of 'v
| Multiple
| Inconsistent

val zgcd : Bigint.t -> Bigint.t -> Bigint.t

val bdec : bool -> bool

val wloop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val loop :
  Uint63.t -> (Uint63.t -> 'a1 -> bool) -> (Uint63.t -> 'a1 -> 'a1) ->
  Uint63.t -> 'a1 -> 'a1

val i2z : Uint63.t -> Bigint.t

val z2i : Bigint.t -> Uint63.t

val ldexp' : Float64.t -> Bigint.t -> Float64.t

val sF2Prim' : spec_float -> Float64.t

val dec : Float64.t -> Bigint.t * Bigint.t

val scale : Float64.t -> Bigint.t -> Bigint.t

val qr : bool -> Bigint.t -> bool -> Bigint.t -> Float64.t

val qround : Bigint.t -> Bigint.t -> Float64.t

val row_exp : Uint63.t -> Float64.t array -> Float64.t -> Bigint.t

val fill_row :
  Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array -> Bigint.t -> Bigint.t
  array -> Bigint.t array

val build_step :
  Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
  Uint63.t -> Bigint.t array -> Bigint.t array

val build :
  Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
  Bigint.t array

val find_piv :
  Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t

val swap_rows :
  Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array

val upd_row :
  Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t
  -> Bigint.t array

val row_gcd : Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t

val div_row :
  Bigint.t array -> Uint63.t -> Uint63.t -> Bigint.t -> Bigint.t array

val elim_row :
  Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t -> Uint63.t -> Bigint.t array
  -> Bigint.t array

val col_step :
  Uint63.t -> Uint63.t -> Uint63.t -> (Bigint.t array * Uint63.t) -> Bigint.t
  array * Uint63.t

val eliminate :
  Uint63.t -> Uint63.t -> Bigint.t array -> Bigint.t array * Uint63.t

val inconsistent : Bigint.t array -> Uint63.t -> Uint63.t -> Uint63.t -> bool

val output : Bigint.t array -> Uint63.t -> Uint63.t -> Float64.t array

val solve_exact :
  uint -> Float64.t array array -> Float64.t array -> Float64.t array outcome

val fdot :
  Float64.t array -> Uint63.t -> Float64.t array -> Uint63.t -> Uint63.t ->
  Float64.t

type dy = Bigint.t * Bigint.t

val dadd : dy -> dy -> dy

val dmul : dy -> dy -> dy

val dabs : dy -> dy

val dneg : dy -> dy

val dleb : dy -> dy -> bool

val dltb : dy -> dy -> bool

val dzero : dy -> bool

val dmax : dy -> dy -> dy

val d0 : dy

val dint : Bigint.t -> dy

val init_M :
  Float64.t array array -> Float64.t array -> Uint63.t -> Uint63.t ->
  Float64.t array

val init_Q : Uint63.t -> Float64.t array

val thr_scale : Float64.t

val col_thr : Float64.t array array -> Uint63.t -> Float64.t array

val swap_f :
  Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array

val axpy_row :
  Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Uint63.t ->
  Float64.t -> Float64.t array

val scale_row :
  Float64.t array -> Uint63.t -> Uint63.t -> Float64.t -> Float64.t array

val tab : Uint63.t -> 'a1 -> (Uint63.t -> 'a1) -> 'a1 array

type fstate = { fs_M : Float64.t array; fs_Q : Float64.t array;
                fs_r : Uint63.t; fs_pc : Uint63.t array;
                fs_perm : Uint63.t array }

val fwd_col :
  Uint63.t -> Uint63.t -> Float64.t array -> Uint63.t -> fstate -> fstate

val forward :
  Uint63.t -> Uint63.t -> Float64.t array -> Float64.t array -> Float64.t
  array -> fstate

val backsub :
  Uint63.t -> Uint63.t -> Float64.t array -> Float64.t array -> Float64.t
  array * Float64.t array

val get_col :
  Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Float64.t array

val get_row : Float64.t array -> Uint63.t -> Uint63.t -> Float64.t array

val free_col : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t

val free_cols : Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t array

val echelon_solve :
  Float64.t array -> Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t ->
  bool -> Float64.t array -> Float64.t array

val rat1 : Float64.t -> Bigint.t * Bigint.t

val ratvec : Float64.t array -> Uint63.t -> Bigint.t array * Bigint.t

val dsumf : Uint63.t -> (Uint63.t -> dy) -> dy

val allf : Uint63.t -> (Uint63.t -> bool) -> bool

val dsumb :
  Uint63.t -> (Uint63.t -> Float64.t) -> (Uint63.t -> Float64.t -> dy) ->
  dy * bool

val maxb : Uint63.t -> (Uint63.t -> dy * bool) -> dy * bool

val dsub : dy -> dy -> dy

val d1 : dy

val transpose : Float64.t array array -> Uint63.t -> Float64.t array

val rowabs : Float64.t array array -> Uint63.t -> dy array

val erow :
  Uint63.t -> Float64.t array -> Float64.t array -> dy array -> dy -> dy ->
  Uint63.t -> dy * bool

val rowR : Uint63.t -> Float64.t array -> Uint63.t -> dy * bool

val resid :
  Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array ->
  dy -> dy -> Uint63.t -> dy * bool

val certify :
  Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array ->
  Float64.t array -> Float64.t array -> bool

val zdot : Float64.t array -> Uint63.t -> Bigint.t array -> Uint63.t -> dy

val chk_incons :
  Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t array -> bool

val chk_mult :
  Float64.t array array -> Float64.t array -> Uint63.t -> Bigint.t array ->
  Bigint.t -> Bigint.t array -> bool

val yv : Float64.t array -> Uint63.t -> Uint63.t -> Uint63.t -> Bigint.t array

val mark_D :
  Uint63.t array -> Uint63.t -> Uint63.t -> Uint63.t -> bool array * Uint63.t
  array

val mark_C : Uint63.t array -> Uint63.t -> Uint63.t -> bool array

val chk_red :
  Float64.t array -> Float64.t array -> Uint63.t -> Bigint.t array ->
  Uint63.t -> bool array -> bool

val scan_null :
  Float64.t array -> Float64.t array -> Float64.t array -> Uint63.t array ->
  Uint63.t array -> bool array -> Uint63.t -> Uint63.t -> Uint63.t ->
  bool * bool

val bentry :
  Float64.t array array -> bool array -> Uint63.t array -> Uint63.t array ->
  bool array -> Uint63.t -> Uint63.t -> Float64.t

val padB :
  Float64.t array array -> Uint63.t -> bool array -> Uint63.t array ->
  Uint63.t array -> bool array -> Float64.t array array

val certify_inj :
  Uint63.t -> Float64.t array array -> Float64.t array -> Float64.t array ->
  bool

val padded_ok :
  Float64.t array array -> Uint63.t -> bool array -> Uint63.t array ->
  Uint63.t array -> bool array -> bool

val solve :
  uint -> Float64.t array array -> Float64.t array -> Float64.t array outcome
