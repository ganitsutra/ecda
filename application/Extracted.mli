
type __ = Obj.t

val length : 'a1 list -> int

val add : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val leb : int -> int -> bool

val ltb : int -> int -> bool

type reflect =
| ReflectT
| ReflectF

val nth : int -> 'a1 list -> 'a1 -> 'a1

val lt_eq_lt_dec : int -> int -> bool option

val le_lt_dec : int -> int -> bool

val le_gt_dec : int -> int -> bool

val le_dec : int -> int -> bool

val lt_dec : int -> int -> bool

val reflect_intro : bool -> reflect

val putin : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> 'a1 list

val sort : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

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

val delete_order : order list -> int -> order list

type transaction = { idb : int; ida : int; tquantity : int }

val t_eqb : transaction -> transaction -> bool

val t_eqP : transaction -> transaction -> reflect

val transact_eqType : Decidable.coq_type

val blist : ((order list*order list)*transaction list) -> order list

val alist : ((order list*order list)*transaction list) -> order list

val mlist : ((order list*order list)*transaction list) -> transaction list

val qty : transaction list -> int -> int -> int

val ids_bid_aux : transaction list -> int list

val ids_ask_aux : transaction list -> int list

val cform_aux : transaction list -> int list -> int list -> transaction list

val cform : transaction list -> transaction list

val bcompetitive : order -> order -> bool

val acompetitive : order -> order -> bool

type command =
| Buy
| Sell
| Del

type instruction = { cmd : command; ord : order }

val action0 : command

val tau0 : instruction

val iterate :
  (order list -> order list -> instruction -> (order list*order
  list)*transaction list) -> instruction list -> int -> (order list*order
  list)*transaction list

val iterated :
  (order list -> order list -> instruction -> (order list*order
  list)*transaction list) -> instruction list -> int -> (order list*order
  list)*transaction list

val match_ask :
  order list -> order list -> order -> (order list*order list)*transaction
  list

val match_bid :
  order list -> order list -> order -> (order list*order list)*transaction
  list

val del_order :
  order list -> order list -> int -> (order list*order list)*transaction list

val process_instruction :
  order list -> order list -> instruction -> (order list*order
  list)*transaction list

val main : instruction list -> int -> (order list*order list)*transaction list
