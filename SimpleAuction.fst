
(******************)
module SimpleAuction
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

type event =
|HighestBidIncreased : UInt160.t -> UInt256.t -> event
|AuctionEnded : UInt160.t -> UInt256.t -> event


(* Storage state *)
noeq type state = {
events: list event;
beneficiary : UInt160.t;
auctionStart : UInt256.t;
biddingTime : UInt256.t;
highestBidder : UInt160.t;
highestBid : UInt256.t;
pendingReturns : UInt160.t -> UInt256.t;
ended : bool;
}
val method_HighestBidIncreased : msg -> state -> UInt160.t -> UInt256.t -> ML (option unit * state)
let method_HighestBidIncreased msg state bidder amount =
 let state = {state with events = HighestBidIncreased bidder amount :: state.events} in
(Some (), state)

val method_AuctionEnded : msg -> state -> UInt160.t -> UInt256.t -> ML (option unit * state)
let method_AuctionEnded msg state winner amount =
 let state = {state with events = AuctionEnded winner amount :: state.events} in
(Some (), state)

let address_0 = UInt160.uint_to_t (0)
let uint256_0 = UInt256.uint_to_t (0)







(* Contract methods *)
val method_SimpleAuction : msg -> state -> UInt256.t -> UInt160.t -> ML (option (unit) * state)
let method_SimpleAuction msg state _biddingTime _beneficiary =
let s = alloc state in
let ret = alloc None in
try
s := {!s with beneficiary = (_beneficiary) };
s := {!s with auctionStart = (msg.now) };
s := {!s with biddingTime = (_biddingTime) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_bid : msg -> state -> unit -> ML (option (unit) * state)
let method_bid msg state () =
let s = alloc state in
let ret = alloc None in
try
if UInt256.gt (msg.now) (UInt256.add_mod ((!s).auctionStart) ((!s).biddingTime))
then (raise SolidityThrow; ())
else ();

if UInt256.lte ((msg).value) ((!s).highestBid)
then (raise SolidityThrow; ())
else ();

if op_disEquality ((!s).highestBidder) (address_0)
then (s := {!s with pendingReturns = set (!s).pendingReturns ((!s).highestBidder) (UInt256.add_mod ((get (!s).pendingReturns ((!s).highestBidder))) ((!s).highestBid)) }; ())
else ();

s := {!s with highestBidder = ((msg).sender) };
s := {!s with highestBid = ((msg).value) };
(let (ret__,st__) = method_HighestBidIncreased msg !s
(msg).sender(msg).value in
 (s := st__; match ret__ with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn));
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_withdraw : msg -> state -> unit -> ML (option (bool) * state)
let method_withdraw msg state () =
let s = alloc state in
let ret = alloc None in
try
let amount = alloc ((get (!s).pendingReturns ((msg).sender))) in

if UInt256.gt (!amount) (uint256_0)
then (s := {!s with pendingReturns = set (!s).pendingReturns ((msg).sender) (uint256_0) };
if op_Negation (false)
then (s := {!s with pendingReturns = set (!s).pendingReturns ((msg).sender) (!amount) };
ret := Some(false); raise SolidityReturn; ())
else ();
 ())
else ();

ret := Some(true); raise SolidityReturn;
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_auctionEnd : msg -> state -> unit -> ML (option (unit) * state)
let method_auctionEnd msg state () =
let s = alloc state in
let ret = alloc None in
try
if UInt256.lte (msg.now) (UInt256.add_mod ((!s).auctionStart) ((!s).biddingTime))
then (raise SolidityThrow; ())
else ();

if (!s).ended
then (raise SolidityThrow; ())
else ();

s := {!s with ended = (true) };
(let (ret__,st__) = method_AuctionEnded msg !s
(!s).highestBidder(!s).highestBid in
 (s := st__; match ret__ with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn));
if op_Negation (false)
then (raise SolidityThrow; ())
else ();

(!ret, !s)
with SolidityReturn -> (!ret, !s)
