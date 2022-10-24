
val sub : int -> int -> int

module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool

  val ltb : int -> int -> bool
 end

type color =
| Red
| Black

module Color :
 sig
  type t = color
 end

val lt_eq_lt_dec : int -> int -> bool option

type order = { id : int; otime : int; oquantity : int; oprice : int }

type transaction = { idb : int; ida : int; tquantity : int }

type command =
| Buy
| Sell
| Del

type instruction = { cmd : command; ord : order }

val pr1 : ('a1 * 'a2) -> 'a1

val pr2 : ('a1 * 'a2) -> 'a2

module TB :
 sig
  type elt = order

  type tree =
  | Leaf
  | Node of Color.t * tree * order * tree

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

val bt_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t

val at_id : ((((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list) -> T_id.t

val eMatch_ask :
  TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val eMatch_bid :
  TB.t -> TA.t -> TA.elt -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val search_order : T_id.t -> int -> T_id.elt option

val eDel_order :
  TB.t -> TA.t -> int -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list

val eProcess_instruction :
  TB.t -> TA.t -> instruction -> T_id.t -> T_id.t ->
  (((TB.t*TA.t)*T_id.t)*T_id.t)*transaction list
