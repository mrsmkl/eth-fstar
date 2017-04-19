
(******************)
module Token
open FStar.All
open FStar.UInt160
open FStar.UInt256
open FStar.Heap
open FStar.List
open FStar.UInt

type msg = {
  sender : UInt160.t;
  value: UInt256.t;
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




(* Storage state *)
noeq type state = {
balance : UInt160.t -> UInt256.t;
}



(* Contract methods *)
val method_Token : msg -> state -> UInt256.t -> ML (option (unit) * state)
let method_Token msg state n =
let s = alloc state in
let ret = alloc None in
try
s := {!s with balance = set (!s).balance ((msg).sender) (n) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_send : msg -> state -> UInt160.t -> UInt256.t -> ML (option (unit) * state)
let method_send msg state a amount =
let s = alloc state in
let ret = alloc None in
try
if UInt256.lt (get (!s).balance ((msg).sender)) (amount)
then (raise SolidityThrow; ())
else ();

s := {!s with balance = set (!s).balance ((msg).sender) (UInt256.sub_mod (get (!s).balance ((msg).sender)) (amount)) };
s := {!s with balance = set (!s).balance (a) (UInt256.add_mod (get (!s).balance (a)) (amount)) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)
