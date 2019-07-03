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
			 SOME _ => (TextIO.input(instream); flush(instream))
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
    in
	Unix.textOutstreamOf(Unix.execute(cmd,args))
    end

val outStreamRef = ref (launchSempre())
val SEMPRE_OUTPUT = ref Tactical.NO_TAC

fun writeSempre (cmd : string) = TextIO.output(!outStreamRef, (String.toString cmd) ^ "\n")
fun readSempre () =
    let
	val _ = use "interactive/sempre-out-socket.sml";
    in
	!SEMPRE_OUTPUT (* ideally, all parsed commands return unit *)
    end

(* send an utterance to SEMPRE and evaluate the response *)
fun s cmd = ( writeSempre cmd;
	      sleep 0.1;
	      proofManagerLib.e (readSempre()) )


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
