
(******************)
module Pyramid
open FStar.All
open FStar.UInt160
open FStar.UInt256
open FStar.Heap

type msg = {
  sender : UInt160.t;
  value: UInt256.t;
}

val set : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl -> (key -> vl)
let set #key #vl f ind x ind2 = if ind = ind2 then x else f ind2

val get : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl
let get #key #vl f ind = f ind

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

(*

Could generate this kind of setters and getters in methods:

let balance_set addr x = s := {!s with balance = set (!s).balance addr x } in
let balance_get addr = get (!s).balance addr in

*)




(* Storage state *)
noeq type state = {
parent : UInt160.t -> UInt160.t;
balance : UInt160.t -> UInt256.t;
invite : UInt160.t -> UInt160.t;
invites_left : UInt160.t -> UInt256.t;
joined : UInt160.t -> bool;
}
let uint256_10 = UInt256.uint_to_t (10)
let address_0 = UInt160.uint_to_t (0)
let uint256_1 = UInt256.uint_to_t (1)


let uint256_0 = UInt256.uint_to_t (0)




let uint256_3 = UInt256.uint_to_t (3)






(* Contract methods *)
val method_calc : msg -> state -> UInt256.t -> ML (option (UInt256.t) * state)
let method_calc msg state level =
let s = alloc state in
let ret = alloc None in
try
ret := Some(uint256_10); raise SolidityReturn;
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_doInvite : msg -> state -> UInt160.t -> ML (option (unit) * state)
let method_doInvite msg state addr =
let s = alloc state in
let ret = alloc None in
try
if op_disEquality (get (!s).invite (addr)) (address_0)
then (raise SolidityThrow; ())
else ();

s := {!s with invite = set (!s).invite (addr) ((msg).sender) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (UInt256.sub_mod (get (!s).invites_left ((msg).sender)) (uint256_1)) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_cancelInvite : msg -> state -> UInt160.t -> ML (option (unit) * state)
let method_cancelInvite msg state addr =
let s = alloc state in
let ret = alloc None in
try
if bool_or (get (!s).joined (addr)) (op_disEquality (get (!s).invite (addr)) ((msg).sender))
then (raise SolidityThrow; ())
else ();

s := {!s with invite = set (!s).invite (addr) (address_0) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (UInt256.add_mod (get (!s).invites_left ((msg).sender)) (uint256_1)) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_pull : msg -> state -> unit -> ML (option (unit) * state)
let method_pull msg state () =
let s = alloc state in
let ret = alloc None in
try
let sum = alloc (get (!s).balance ((msg).sender)) in

s := {!s with balance = set (!s).balance ((msg).sender) (uint256_0) };
();
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_join : msg -> state -> unit -> ML (option (unit) * state)
let method_join msg state () =
let s = alloc state in
let ret = alloc None in
try
if UInt256.lt ((msg).value) (uint256_1)
then (raise SolidityThrow; ())
else ();

if get (!s).joined ((msg).sender)
then (raise SolidityThrow; ())
else ();

if bool_and (op_disEquality (get (!s).invite ((msg).sender)) (address_0)) (UInt256.gt (get (!s).invites_left (get (!s).invite ((msg).sender))) (uint256_0))
then (let par = alloc (get (!s).invite ((msg).sender)) in

s := {!s with parent = set (!s).parent ((msg).sender) (!par) };
s := {!s with joined = set (!s).joined ((msg).sender) (true) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (uint256_3) };
let i = alloc (uint256_0) in
let rec loop_199 () : ML unit =
if not (UInt256.lt (!i) (uint256_10)) then () else (
s := {!s with balance = set (!s).balance (!par) (UInt256.add_mod (get (!s).balance (!par)) (let (ret,st) = method_calc msg !s
!i in (s := st; match ret with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn))) };
par := get (!s).parent (!par);i := UInt256.add_mod (!i) (uint256_1);loop_199 ()) in loop_199(); ())
else ();

(!ret, !s)
with SolidityReturn -> (!ret, !s)
