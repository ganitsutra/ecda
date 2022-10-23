
type __ = Obj.t

val length : 'a1 list -> int

val add : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

type reflect =
| ReflectT
| ReflectF

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

val nth : int -> 'a1 list -> 'a1 -> 'a1

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

val lt_eq_lt_dec : int -> int -> bool option

val le_lt_dec : int -> int -> bool

val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool

val lt_dec : int -> int -> bool

val reflect_intro : bool -> reflect

module Decidable :
 sig
  type coq_type = { eqb : (__ -> __ -> bool); eqP : (__ -> __ -> reflect) }

  type coq_E = __

  val eqb : coq_type -> coq_E -> coq_E -> bool
 end

val nat_eqP : int -> int -> reflect

val nat_eqType : Decidable.coq_type

val memb :
  Decidable.coq_type -> Decidable.coq_E -> Decidable.coq_E list -> bool

val uniq : Decidable.coq_type -> Decidable.coq_E list -> Decidable.coq_E list

type order = { id : int; otime : int; oquantity : int; oprice : int }

val w0 : order

type transaction = { idb : int; ida : int; tquantity : int }

val t_eqb : transaction -> transaction -> bool

val t_eqP : transaction -> transaction -> reflect

val transact_eqType : Decidable.coq_type

val qty : transaction list -> int -> int -> int

val ids_bid_aux : transaction list -> int list

val ids_ask_aux : transaction list -> int list

val cform_aux : transaction list -> int list -> int list -> transaction list

val cform : transaction list -> transaction list

type command =
| Buy
| Sell
| Del

type instruction = { cmd : command; ord : order }

val action0 : command

val tau0 : instruction

module TB :
 sig
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  val empty : tree

  val max_elt : tree -> elt option

  type t = tree

  val makeBlack : tree -> tree

  val makeRed : tree -> tree

  val lbal : tree -> order -> tree -> tree

  val rbal : tree -> order -> tree -> tree

  val rbal' : tree -> order -> tree -> tree

  val lbalS : tree -> order -> tree -> tree

  val rbalS : tree -> order -> tree -> tree

  val ins : order -> tree -> tree

  val add : order -> tree -> tree

  val append : tree -> tree -> tree

  val del : order -> tree -> tree

  val remove : order -> tree -> tree
 end

module TA :
 sig
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  val empty : tree

  val max_elt : tree -> elt option

  type t = tree

  val makeBlack : tree -> tree

  val makeRed : tree -> tree

  val lbal : tree -> order -> tree -> tree

  val rbal : tree -> order -> tree -> tree

  val rbal' : tree -> order -> tree -> tree

  val lbalS : tree -> order -> tree -> tree

  val rbalS : tree -> order -> tree -> tree

  val ins : order -> tree -> tree

  val add : order -> tree -> tree

  val append : tree -> tree -> tree

  val del : order -> tree -> tree

  val remove : order -> tree -> tree
 end

module T_id :
 sig
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

  val empty : tree

  type t = tree

  val makeBlack : tree -> tree

  val makeRed : tree -> tree

  val lbal : tree -> order -> tree -> tree

  val rbal : tree -> order -> tree -> tree

  val rbal' : tree -> order -> tree -> tree

  val lbalS : tree -> order -> tree -> tree

  val rbalS : tree -> order -> tree -> tree

  val ins : order -> tree -> tree

  val add : order -> tree -> tree

  val append : tree -> tree -> tree

  val del : order -> tree -> tree

  val remove : order -> tree -> tree
 end

val bt : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> TB.t

val at : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> TA.t

val mt : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> transaction list

val b_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t

val a_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t

val match_ask :
  TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val match_bid :
  TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val search_order : T_id.t -> int -> T_id.elt option

val del_order :
  TB.t -> TA.t -> int -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val process_instruction :
  TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val iterate :
  (TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> instruction list -> int
  -> (((TB.tree*TA.tree)*T_id.tree)*T_id.tree)*transaction list

val iterated :
  (TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> instruction list -> int
  -> (((TB.tree*TA.tree)*T_id.tree)*T_id.tree)*transaction list

val main :
  instruction list -> int -> (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list
