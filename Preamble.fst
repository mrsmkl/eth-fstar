open FStar.All
open FStar.UInt160
open FStar.UInt256
open FStar.Heap
open FStar.List
open FStar.UInt

type msg = {
  sender : UInt160.t;
  value: UInt256.t;
  now : UInt256.t;
}

val set : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl -> (key -> vl)
let set #key #vl f ind x ind2 = if ind = ind2 then x else f ind2

val get : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl
let get #key #vl f ind = f ind

val address_to_uint : UInt160.t -> UInt256.t
let address_to_uint a =
  let x : uint_t 160 = UInt160.v a in
  let y : uint_t 256 = UInt.to_uint_t 256 x in
  UInt256.uint_to_t y

val uint_to_address : UInt256.t -> UInt160.t
let uint_to_address a = UInt160.uint_to_t (UInt.to_uint_t 160 (UInt256.v a))

val list_length : #a:Type -> list a -> UInt256.t
let list_length #a lst = UInt256.uint_to_t (UInt.to_uint_t 256 (List.length lst))

val list_nth : #a:Type -> list a -> UInt256.t -> ML a
let list_nth #a lst n = List.nth lst (UInt256.v n)

val list_set : #a:Type -> list a -> UInt256.t -> a -> ML (list a)
let list_set #a lst n elem =
  let n = UInt256.v n in
  List.mapi (fun i a -> if i = n then elem else a) lst 

exception SolidityThrow
exception SolidityReturn
exception SolidityBadReturn

val do_call : #state:Type -> #ret:Type -> (state -> ML (option ret * state)) -> state -> ML (option ret * state)
let do_call #state #ret meth st =
  try meth st
  with SolidityThrow -> (None, st)

val bool_and : bool -> bool -> Tot bool
let bool_and a b = a && b

val bool_or : bool -> bool -> Tot bool
let bool_or a b = a || b

