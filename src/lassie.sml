structure lassie : LASSIE =
struct

fun sleep t =
    let
	val wakeUp = Time.+ (Time.now(), Time.fromReal(t))
	fun wait () = if Time.> (Time.now(), wakeUp) then () else wait ()
    in
	wait ()
    end

fun flush instream = case TextIO.canInput(instream, 5000) of
			 SOME _ => (TextIO.input(instream); flush(instream))
		       | NONE => ()
				     
fun launchSempre () = 
    let
	val LASSIEDIR = case OS.Process.getEnv "LASSIEDIR" of
			    SOME s => s
			  | NONE => raise Fail "Variable LASSIEDIR not defined in environment";
	(* SEMPRE's run script is dependent on being at the top of its directory *)
	val _ = OS.FileSys.chDir (LASSIEDIR ^ "/sempre")
				 
	val instream' = Unix.textInstreamOf(Unix.execute("interactive/run",["-n","@mode=lassie"]))
					  
	val execCommand = TextIO.input(instream')
				      
	val (cmd::args)	= String.tokens Char.isSpace execCommand

	val (instream, outstream) = Unix.streamsOf(Unix.execute(cmd,args))

	(* Need to wait for all intro text before flushing it, more than 4k chars *)
	fun wait instream = case TextIO.canInput(instream, 4000) of
				SOME 4000 => ()
			      | _ => wait instream
    in	  
	wait instream; flush instream; (ref instream, ref outstream)
    end

val (inref,outref) = launchSempre();

fun waitIO () = case TextIO.canInput(!inref, 5000) of
		    NONE => waitIO()
		  | SOME _ => ()

fun readIO () = case TextIO.canInput(!inref, 5000) of
		    NONE => ""
		  | SOME _ => TextIO.input(!inref) ^ (readIO())

(* send a command to SEMPRE *)
fun s cmd = (readIO(); (* flush *)
	     TextIO.output(!outref, cmd ^ "\n");
	     waitIO();
	     sleep 0.05; (* reading IO immediately only returns whitespaces *)
	     readIO())

    
										       
                      (* Manipulating a goalstack *)

(* val the_proofs = ref (Manager.initial_proofs()); *)
(* fun proofs() = !the_proofs; *)
(* fun top_proof() = Manager.current_proof(proofs()); *)

(* fun new_goalstack g f = *)
(*    (the_proofs := Manager.add (Manager.new_goalstack g f) (proofs()); *)
(*     proofs()); *)
(* fun set_goal g = new_goalstack g Lib.I; *)
(* fun g trm = set_goal ([], trm) *)

(* fun b () = *)
(*     (the_proofs := Manager.hd_opr Manager.backup (proofs()); *)
(*      top_proof()); *)

(* fun e tac = *)
(*    (say "OK..\n"; *)
(*     the_proofs := Manager.hd_opr (Manager.expand tac) (proofs()); *)
(*     top_proof()) *)
(*   handle err => Raise err; *)

(* fun p () = Manager.hd_proj I (proofs()) *)
(*         handle Manager.NO_PROOFS => *)
(*          (say "No goalstack is currently being managed.\n"; *)
(*           raise mk_HOL_ERR "proofManagerLib" "p" "") *)


										       
