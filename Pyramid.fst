
(******************)
module Pyramid
open FStar.All
open FStar.UInt160
open FStar.UInt256
open FStar.Heap
open FStar.List
open FStar.UInt

type msg = {
  sender : UInt160.t;
  this : UInt160.t;
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

val update_balance : UInt160.t -> UInt160.t -> UInt256.t -> (UInt160.t -> UInt256.t) -> (UInt160.t -> UInt256.t)
let update_balance sender addr v bal x =
   if addr = x then UInt256.add_mod v (bal x) else
   if addr = sender then UInt256.sub_mod (bal x) v else bal x

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

type event = unit



(* Storage state *)
noeq type state = {
events__: list event; balance__ : UInt160.t -> UInt256.t;
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



assume type inv : state -> Type
assume val call_env : state -> state
assume val call_spec : st:state -> Lemma (requires inv st) (ensures inv (call_env st))



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
if op_disEquality ((get (!s).invite (addr))) (address_0)
then (raise SolidityThrow; ())
else ();

s := {!s with invite = set (!s).invite (addr) ((msg).sender) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (UInt256.sub_mod ((get (!s).invites_left ((msg).sender))) (uint256_1)) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_cancelInvite : msg -> state -> UInt160.t -> ML (option (unit) * state)
let method_cancelInvite msg state addr =
let s = alloc state in
let ret = alloc None in
try
if bool_or ((get (!s).joined (addr))) (op_disEquality ((get (!s).invite (addr))) ((msg).sender))
then (raise SolidityThrow; ())
else ();

s := {!s with invite = set (!s).invite (addr) (address_0) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (UInt256.add_mod ((get (!s).invites_left ((msg).sender))) (uint256_1)) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_pull : msg -> state -> unit -> ML (option (unit) * state)
let method_pull msg state () =
let s = alloc state in
let ret = alloc None in
try
let sum = alloc ((get (!s).balance ((msg).sender))) in

s := {!s with balance = set (!s).balance ((msg).sender) (uint256_0) };
(let value__ = !sum in
let recv__ = (msg).sender in
if UInt256.lt ((!s).balance__ msg.this) value__ then raise SolidityThrow else
( s := {!s with balance__ = update_balance msg.this recv__ value__ (!s).balance__};
  s := call_env !s ));
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

if (get (!s).joined ((msg).sender))
then (raise SolidityThrow; ())
else ();

if bool_and (op_disEquality ((get (!s).invite ((msg).sender))) (address_0)) (UInt256.gt ((get (!s).invites_left ((get (!s).invite ((msg).sender))))) (uint256_0))
then (let par = alloc ((get (!s).invite ((msg).sender))) in

s := {!s with parent = set (!s).parent ((msg).sender) (!par) };
s := {!s with joined = set (!s).joined ((msg).sender) (true) };
s := {!s with invites_left = set (!s).invites_left ((msg).sender) (uint256_3) };
let i = alloc (uint256_0) in
let rec loop_199 () : ML unit =
if not (UInt256.lt (!i) (uint256_10)) then () else (
s := {!s with balance = set (!s).balance (!par) (UInt256.add_mod ((get (!s).balance (!par))) ((let (ret__,st__) = method_calc msg !s
!i in
 (s := st__; match ret__ with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn)))) };
par := (get (!s).parent (!par));i := UInt256.add_mod (!i) (uint256_1);loop_199 ()) in loop_199(); ())
else ();

(!ret, !s)
with SolidityReturn -> (!ret, !s)
