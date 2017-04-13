
(******************)
module Token

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

exception EvmThrow

val do_call : #state:Type -> #ret:Type -> (state -> ML (option ret * state)) -> state -> ML (option ret * state)
let do_call #state #ret meth st =
  try meth st
  with EvmThrow -> (None, st)




(* Storage state *)
noeq type state = {
balance : (UInt160.t -> UInt256.t);
}

noeq type mut_state = {
m_balance : ref (UInt160.t -> UInt256.t);
}


let test () =
  let foo = Some 123 in
  match foo with
  | None -> assert False
  | Some k -> ()


(* Contract methods *)
val method_Token : msg -> mut_state -> UInt256.t -> ML (option unit)
let method_Token msg state n =
let ret = alloc None in
state.m_balance := set !(state.m_balance) ((msg).sender) (n);
!ret


val method_send : msg -> state -> UInt160.t -> UInt256.t -> ML (option (unit) * state)
let method_send msg state a amount =
let s = alloc state in
let balance_set addr x = s := {!s with balance = set (!s).balance addr x } in
let balance_get addr = get (!s).balance addr in

let ret = alloc None in
if UInt256.lt (get (!s).balance ((msg).sender)) (amount)
then (raise EvmThrow; ())
else ();
balance_set ((msg).sender) (UInt256.sub_mod (balance_get ((msg).sender)) (amount));
balance_set (a) (UInt256.add_mod (balance_get (a)) (amount));
(!ret, !s)


