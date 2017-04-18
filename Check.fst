module Check

open FStar.All
open FStar.UInt64
open FStar.Heap

exception Test

(*

let main () =
  let i : ref UInt256.t = alloc (UInt256.uint_to_t 0) in
  let rec loop () : ML unit = if UInt256.gt !i (UInt256.uint_to_t 100) then () else ( i := UInt256.add_mod !i (UInt256.uint_to_t 1) ; loop () ) in
  loop ();
  if (raise Test ; 1) + 2 = 3 then ()
*)

let test j = 
  let i = alloc (UInt256.uint_to_t (0)) in
  if j < 10 then raise Test;
  let rec loop_199 () : ML unit =
    if not (UInt256.lt (!i) (let lit : UInt256.t = UInt256.uint_to_t (10) in lit)) then () else (
    i := UInt256.add_mod (!i) (let lit : UInt256.t = UInt256.uint_to_t (1) in lit);loop_199 ()) in
  loop_199()

