structure lassie =
struct

val map = List.map

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
	val (instr,outstr) = case String.tokens Char.isSpace execCommand of
				 [] => raise Fail "Run script returned no arguments"
			       | cmd::args => Unix.streamsOf(Unix.execute(cmd,args))
    in
	(ref instr, ref outstr)
    end

val (inStreamRef, outStreamRef) = launchSempre()
val SEMPRE_OUTPUT = ref (SOME {candidates= [{score= 0.0,
					     prob= ~1.0,
					     anchored= true,
					     formula= "",
					     value= NO_TAC}],
			       stats= {cmd= "q",
				       size= 2,
				       status= "Core"},
			       lines= [""]})
val lastUtterance = ref ""
val socketPath = "interactive/sempre-out-socket.sml"
val historyPath = "interactive/last-sempre-output.sml"
		      
(* send a string to sempre *)
fun writeSempre (cmd : string) =
    let
	val _ = if OS.FileSys.access (socketPath, []) then OS.FileSys.remove socketPath else ()
	val _ = lastUtterance := cmd
    in
	TextIO.output(!outStreamRef, cmd ^ "\n")
    end

exception LassieException of string
				 
(* read SEMPRE's response from the "socket" file once there and remove it *)
(* returns a derivation (i.e. the first candidate) *)
fun readSempre () =
    if not (OS.FileSys.access ("interactive/sempre-out-socket.sml", [])) then readSempre()
    else (sleep 0.1; (* Allow SEMPRE to finish writing *)
	  use socketPath;
	  if OS.FileSys.access (historyPath, []) then OS.FileSys.remove historyPath else ();
	  OS.FileSys.rename {old = socketPath, new = historyPath};
	  case !SEMPRE_OUTPUT of
	      NONE => raise Fail ("SEMPRE returned an empty response to utterance `" ^ (!lastUtterance) ^ "`")
	    | SOME response => case #candidates response of 
				   [] => raise LassieException ("Lassie did not understand the utterance "
								^ (!lastUtterance)
								^ ", you may provide a definition using lassie.def")
					       
				 | deriv::tail => deriv
	 )
	     
(* naturalize-an-utterance tactic *)
fun semtac utt : tactic = ( writeSempre utt; #value (readSempre()) )

(* same but on lists *)
fun las uttl : tactic = case uttl of
			    [] => ALL_TAC
			  | utt::tail => (semtac utt) THEN (las tail)

(* define an utterance in terms of a list of utterances*)
fun def ndum niens =
    let
	(* for each utterance of the definition, get its logical form *)
	val getFormula = fn u => let
			      val _ = writeSempre u
			      val deriv = readSempre()
			  in
			      [u, #formula deriv]
			  end
	val quot = fn s => "\"" ^ s ^ "\""
	val quot' = fn s => "\\\"" ^ s ^ "\\\""
	val list2string = fn l => "[" ^ (String.concatWith "," l) ^ "]"
	val definiens = niens |> (map getFormula)
			      |> (map (map quot'))
			      |> (map list2string)
			      |> list2string
    in
	writeSempre ("(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")")
    end
	
(* run the content of a string as SML code *)
fun runString string =
    let
	val instream' = Unix.textInstreamOf(Unix.execute("/bin/echo",[string]))
	val getChar = fn () => TextIO.input1 instream'
    in
	PolyML.compiler (getChar, []) ()
    end

end
