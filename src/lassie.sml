structure lassie =
struct

fun sleep t =
    let
	val wakeUp = Time.+ (Time.now(), Time.fromReal(t))
	fun wait () = if Time.> (Time.now(), wakeUp) then () else wait ()
    in
	wait ()
    end

fun flush instream = case TextIO.canInput(instream, 5000) of
			 SOME n => if n = 0 then ()
				   else (TextIO.input(instream); flush(instream))
		       | NONE => ()

(* run SEMPRE as a subprocess, through its run script returns outstream of its shell *)
fun launchSempre () = 
    let
	val LASSIEDIR = case OS.Process.getEnv "LASSIEDIR" of
			    SOME s => s
			  | NONE => raise Fail "Variable LASSIEDIR not defined in environment";
	(* SEMPRE's run script is dependent on being at the top of its directory *)
	val _ = OS.FileSys.chDir (LASSIEDIR ^ "/sempre")
	val instream' = Unix.textInstreamOf(Unix.executeInEnv("interactive/run",["-n","@mode=lassie"],Posix.ProcEnv.environ()))
	val execCommand = TextIO.input(instream')
	val (cmd::args)	= String.tokens Char.isSpace execCommand
	val (instr,outstr) = Unix.streamsOf(Unix.execute(cmd,args))
    in
	(ref instr, ref outstr)
    end

val (inStreamRef, outStreamRef) = launchSempre()
val SEMPRE_OUTPUT = ref (SOME {candidates= [{score= 0.0,
					     prob= ~1.0,
					     anchored= true,
					     formula= "do nothing",
					     value= NO_TAC}],
			       stats= {cmd= "q",
				       size= 2,
				       status= "Core"},
			       lines= [""]})
val socketPath = "interactive/sempre-out-socket.sml"
val historyPath = "interactive/last-sempre-output.sml"
		      
		      
fun writeSempre (cmd : string) =
    let
	val _ = if OS.FileSys.access (socketPath, []) then OS.FileSys.remove socketPath else ()
    in
	TextIO.output(!outStreamRef, (String.toString cmd) ^ "\n")
    end

(* read SEMPRE's response from the "socket" file once there and remove it *)
fun readSempre () =
    if not (OS.FileSys.access ("interactive/sempre-out-socket.sml", [])) then readSempre()
    else (sleep 0.1; (* Allow SEMPRE to finish writing *)
	  use socketPath;
	  if OS.FileSys.access (historyPath, []) then OS.FileSys.remove historyPath else ();
	  OS.FileSys.rename {old = socketPath, new = historyPath})
	     
(* naturalize-an-utterance tactic *)
fun semtac utt : tactic =
    (writeSempre utt;
     readSempre();
     case !SEMPRE_OUTPUT of
	 NONE => raise Fail "SEMPRE wrote an empty response"
       | SOME response => case #candidates response of
			      [] => raise Fail "SEMPRE did not understand the utterance, you can provide a definition"
			    | deriv::tail => #value deriv
    )
	
fun las uttl : tactic = case uttl of
			    [] => ALL_TAC
			  | utt::tail => (semtac utt) THEN (las tail)
						      
(* run the content of a string as SML code *)
fun runString string =
    let
	val instream' = Unix.textInstreamOf(Unix.execute("/bin/echo",[string]))
	val getChar = fn () => TextIO.input1 instream'
    in
	PolyML.compiler (getChar, []) ()
    end

end


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
