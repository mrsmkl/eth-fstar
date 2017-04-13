open FStar.All
open FStar.UInt160
open FStar.UInt256
open FStar.Heap

type msg = {
sender : UInt160.t;
}

val set : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl -> (key -> vl)
let set #key #vl f ind x ind2 = if ind = ind2 then x else f ind2

val get : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl
let get #key #vl f ind = f ind

exception SolidityThrow
exception SolidityReturn

val do_call : #state:Type -> #ret:Type -> (state -> ML (option ret * state)) -> state -> ML (option ret * state)
let do_call #state #ret meth st =
  try meth st
  with SolidityThrow -> (None, st)

(*

Could generate this kind of setters and getters in methods:

let balance_set addr x = s := {!s with balance = set (!s).balance addr x } in
let balance_get addr = get (!s).balance addr in

*)

