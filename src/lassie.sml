signature LASSIE =
sig
    val g : term -> proofs
    val b : unit -> proof
    val e : tactic -> proof
    val p : unit -> proof
end;

structure lassie : LASSIE =
struct

val the_proofs = ref (Manager.initial_proofs());
fun proofs() = !the_proofs;
fun top_proof() = Manager.current_proof(proofs());

                          (* What is a goal_tree? *)
(* fun new_goaltree g = *)
(*    (the_proofs := Manager.add (Manager.new_goaltree g) (proofs()); *)
(*     proofs()); *)

fun new_goalstack g f =
   (the_proofs := Manager.add (Manager.new_goalstack g f) (proofs());
    proofs());
fun set_goal g = new_goalstack g Lib.I;
fun g trm = set_goal ([], trm)

fun b () =
    (the_proofs := Manager.hd_opr Manager.backup (proofs());
     top_proof());

fun e tac =
   (say "OK..\n";
    the_proofs := Manager.hd_opr (Manager.expand tac) (proofs());
    top_proof())
  handle err => Raise err;

fun p () = Manager.hd_proj I (proofs())
        handle Manager.NO_PROOFS =>
         (say "No goalstack is currently being managed.\n";
          raise mk_HOL_ERR "proofManagerLib" "p" "")

end;
		 
		 (* Sending a packet to the webserver *)
		 
(* val my_query = "qqqqq" *)
(* val my_vector = Byte.stringToBytes my_query	  *)
(* val my_list = List.map Word8.fromInt [1,2,3,4] *)
(* val my_array = Word8Array.fromList my_list *)
(* val my_slice = Word8ArraySlice.slice(my_array, 0, NONE) *)

(* val my_ia = INetSock.toAddr *)
(* 		(Option.valOf (NetHostDB.fromString "127.0.0.1"), *)
(* 		 8410) *)
(* val my_socket = INetSock.UDP.socket() *)

(* val q = sendArrTo (my_socket, my_ia, my_slice); *)
			 
