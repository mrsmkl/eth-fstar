
(******************)
module Ballot
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

val default_address : UInt160.t
let default_address = UInt160.uint_to_t 0

val default_uint256 : UInt256.t
let default_uint256 = UInt256.uint_to_t 0

val default_uint : UInt256.t
let default_uint = UInt256.uint_to_t 0

let one_uint = UInt256.uint_to_t 1
let one_uint256 = UInt256.uint_to_t 1

val uint256_incr : UInt256.t -> UInt256.t
let uint256_incr x = UInt256.add_mod x (UInt256.uint_to_t 1)

val uint256_decr : UInt256.t -> UInt256.t
let uint256_decr x = UInt256.sub_mod x (UInt256.uint_to_t 1)

val default_bytes32 : UInt256.t
let default_bytes32 = UInt256.uint_to_t 0

val default_bool : bool
let default_bool = false

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

noeq type struct_Voter = {
weight : UInt256.t;
voted : bool;
delegate : UInt160.t;
vote : UInt256.t;
}
let default_Voter = {
weight = default_uint;
voted = default_bool;
delegate = default_address;
vote = default_uint;
}

noeq type struct_Proposal = {
name : UInt256.t;
voteCount : UInt256.t;
}
let default_Proposal = {
name = default_bytes32;
voteCount = default_uint;
}

type event = unit



(* Storage state *)
noeq type state = {
events__: list event; balance__ : UInt160.t -> UInt256.t;
chairperson : UInt160.t;
voters : UInt160.t -> struct_Voter;
proposals : list (struct_Proposal);
}
let default_state = {
events__ = []; balance__ = (fun x -> default_uint);
chairperson = default_address;
voters = (fun x -> default_Voter);
proposals = [];
}
val method_Voter : msg -> state -> UInt256.t -> bool -> UInt160.t -> UInt256.t -> ML (option (struct_Voter) * state)
let method_Voter msg state weight voted delegate vote = (Some ({
  weight = weight;
  voted = voted;
  delegate = delegate;
  vote = vote;
}), state)
val method_Proposal : msg -> state -> UInt256.t -> UInt256.t -> ML (option (struct_Proposal) * state)
let method_Proposal msg state name voteCount = (Some ({
  name = name;
  voteCount = voteCount;
}), state)
let uint256_1 = UInt256.uint_to_t (1)
let uint256_0 = UInt256.uint_to_t (0)








assume type inv : state -> Type
assume val call_env : state -> state
assume val call_spec : st:state -> Lemma (requires inv st) (ensures inv (call_env st))



(* Contract methods *)
val method_Ballot : msg -> state -> list (UInt256.t) -> ML (option (unit) * state)
let method_Ballot msg state proposalNames =
let s = alloc state in
let ret = alloc None in
try
s := {!s with chairperson = ((msg).sender) };
let base = (get (!s).voters ((!s).chairperson))in
let base = {base with weight = (uint256_1) } in
s := {!s with voters = set (!s).voters ((!s).chairperson) (base) };
let i = alloc (uint256_0) in
let rec loop_65 () : ML unit =
if not (UInt256.lt (!i) (list_length (proposalNames))) then () else (
s := {!s with proposals = ((!s).proposals @ [ (let (ret__,st__) = method_Proposal msg !s
(list_nth (proposalNames) (!i))uint256_0 in
 (s := st__; match ret__ with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn))]) };i := uint256_incr (!i);loop_65 ()) in loop_65();
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_giveRightToVote : msg -> state -> UInt160.t -> ML (option (unit) * state)
let method_giveRightToVote msg state voter =
let s = alloc state in
let ret = alloc None in
try
if bool_or (op_disEquality ((msg).sender) ((!s).chairperson)) (((get (!s).voters (voter))).voted)
then (raise SolidityThrow; ())
else ();

let base = (get (!s).voters (voter))in
let base = {base with weight = (uint256_1) } in
s := {!s with voters = set (!s).voters (voter) (base) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_delegate : msg -> state -> UInt160.t -> ML (option (unit) * state)
let method_delegate msg state to_ =
let s = alloc state in
let ret = alloc None in
try
let to = alloc (to_) in

let sender = alloc ((get (!s).voters ((msg).sender))) in

if (!sender).voted
then (raise SolidityThrow; ())
else ();

if op_Equality (!to) ((msg).sender)
then (raise SolidityThrow; ())
else ();

let rec loop_140 () : ML unit =
if not (op_disEquality (((get (!s).voters (!to))).delegate) (uint_to_address uint256_0)) then () else (
to := ((get (!s).voters (!to))).delegate;
if op_Equality (!to) ((msg).sender)
then (raise SolidityThrow; ())
else ();
loop_140 ()) in loop_140();
sender := { !sender with voted = true };
sender := { !sender with delegate = !to };
let delegate = alloc ((get (!s).voters (!to))) in

if (!delegate).voted
then (let base = (list_nth ((!s).proposals) ((!delegate).vote))in
let base = {base with voteCount = (UInt256.add_mod (((list_nth ((!s).proposals) ((!delegate).vote))).voteCount) ((!sender).weight)) } in
s := {!s with proposals = list_set ((!s).proposals) ((!delegate).vote) (base) }; ())
else (delegate := { !delegate with weight = UInt256.add_mod ((!delegate).weight) ((!sender).weight) }; ());

(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_vote : msg -> state -> UInt256.t -> ML (option (unit) * state)
let method_vote msg state proposal =
let s = alloc state in
let ret = alloc None in
try
let sender = alloc ((get (!s).voters ((msg).sender))) in

if (!sender).voted
then (raise SolidityThrow; ())
else ();

sender := { !sender with voted = true };
sender := { !sender with vote = proposal };
let base = (list_nth ((!s).proposals) (proposal))in
let base = {base with voteCount = (UInt256.add_mod (((list_nth ((!s).proposals) (proposal))).voteCount) ((!sender).weight)) } in
s := {!s with proposals = list_set ((!s).proposals) (proposal) (base) };
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_winningProposal : msg -> state -> unit -> ML (option (UInt256.t) * state)
let method_winningProposal msg state () =
let s = alloc state in
let ret = alloc None in
try
let winningProposal = alloc (uint256_0) in

let winningVoteCount = alloc (uint256_0) in

let p = alloc (uint256_0) in
let rec loop_262 () : ML unit =
if not (UInt256.lt (!p) (list_length ((!s).proposals))) then () else (
if UInt256.gt (((list_nth ((!s).proposals) (!p))).voteCount) (!winningVoteCount)
then (winningVoteCount := ((list_nth ((!s).proposals) (!p))).voteCount;
winningProposal := !p; ())
else ();
p := uint256_incr (!p);loop_262 ()) in loop_262();
ret := Some(!winningProposal); raise SolidityReturn;
(!ret, !s)
with SolidityReturn -> (!ret, !s)


val method_winnerName : msg -> state -> unit -> ML (option (UInt256.t) * state)
let method_winnerName msg state () =
let s = alloc state in
let ret = alloc None in
try
ret := Some(((list_nth ((!s).proposals) ((let (ret__,st__) = method_winningProposal msg !s
() in
 (s := st__; match ret__ with Some x -> x | None -> (* assert False ; *) raise SolidityBadReturn))))).name); raise SolidityReturn;
(!ret, !s)
with SolidityReturn -> (!ret, !s)
