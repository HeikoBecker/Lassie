structure Lassie =   
struct
val map = List.map
exception LassieException of string
			    
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

(* wait for the SEMPRE prompt; signifies end of execution *)
fun waitSempre instream =
    let
	val s = TextIO.input(instream);
    in
	if String.isSuffix "\n> " s orelse s = "> " then ()
	(* else if s = "" then raise LassieException "Reached EOS? Empty string was read."  *)
	else waitSempre instream
    end	
				     
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
	val _ = waitSempre(instr);
    in
	(ref instr, ref outstr)
    end

val (instream, outstream) = launchSempre()
val SEMPRE_OUTPUT = ref (SOME {candidates= [{score= 0.0,
					     prob= ~1.0,
					     anchored= true,
					     formula= "",
					     value= "NO_TAC",
					     tactic= NO_TAC}],
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
	val _ = TextIO.output(!outstream, cmd ^ "\n")
    in
	waitSempre(!instream)
    end
	
				 
(* read SEMPRE's response from the "socket" file once there and remove it *)
(* returns a derivation (i.e. the first candidate) *)
fun readSempre utt =
    let
	val _ = sleep 0.1; (* socket file seems to appear a bit after end of execution *)	 
	val _ = if not (OS.FileSys.access (socketPath, []))
		then raise LassieException ("Socket file missing after call to SEMPRE: " ^ socketPath)
		else ()
    in
	use socketPath;
	if OS.FileSys.access (historyPath, []) then OS.FileSys.remove historyPath else ();
	OS.FileSys.rename {old = socketPath, new = historyPath};
	case !SEMPRE_OUTPUT of
	    NONE => raise Fail ("SEMPRE returned an empty response to utterance `" ^ utt ^ "`")
	  | SOME response => case #candidates response of 
				 [] => raise LassieException ("Did not understand the utterance "
							      ^ utt
							      ^ ", you may provide a definition using lassie.def")  
			       | deriv::tail => (deriv, tail) (* ensures at least one derivation *)
    end

(* send a NL query to sempre and return at least a derivation *)
fun sempre utt = (writeSempre utt; readSempre utt)

(* parse and return most likely tactic *)
fun nltac utt : tactic = utt |> sempre |> fst |> #tactic
fun nltacl uttl : tactic = case uttl of
			       [] => ALL_TAC
			     | utt::tail => (nltac utt) THEN (nltacl tail)

(* tell sempre you accepted a derivation; affects future weights *)
fun accept (utt, formula) : unit =
    let
	fun quot s = "\"" ^ s ^ "\""
    in
	writeSempre ("(:accept " ^ (quot utt) ^ " " ^ (quot formula) ^ ")")
    end
								
(* interactively parse utterances, allow for selection of preferred derivation, then evaluation *)
fun lassie utt =
    let
	val _ = print ("Trying to parse " ^ utt ^ "\n")
	val derivations = utt |> sempre |> (fn (hd,tl) => hd::tl)
	fun dprinter derivs idx =
	    case derivs of
		[] => ()
	      | d::ds => (print ("\nDerivation [" ^ Int.toString idx ^ "]:\n"
				     ^ "\tFormula: " ^ (#formula d) ^ "\n"
				     ^ "\tValue: " ^ (#value d) ^ "\n\n");
			      dprinter ds (idx + 1))
    in
	dprinter derivations 1; (* if no index is given, just print the derivations *)
	fn idx => if idx > length derivations orelse idx < 1 then
		      raise LassieException "Derivation index out of bounds"
		  else
		      let
			  val d = List.nth (derivations, (idx - 1))
		      in
			  accept (utt, #formula d);
			  print ("Accepted derivation [" ^ Int.toString idx ^ "]\n");
			  proofManagerLib.e (#tactic d)
		      end
    end			      
	
(* define an utterance in terms of a list of utterances*)
fun def ndum niens : unit =
    let
	(* for each utterance of the definition, get its logical form *)
	fun getFormula u = [u, (u |> sempre |> fst |> #formula)]
			       
	(* formatting *)
	fun quot s = "\"" ^ s ^ "\""
	fun quot' s = "\\\"" ^ s ^ "\\\""
	fun list2string l = "[" ^ (String.concatWith "," l) ^ "]"
								  
	val definiens = niens |> (map getFormula)
			      |> (map (map quot'))
			      |> (map list2string)
			      |> list2string
    in
	writeSempre ("(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")")
    end

fun addRule lhs rhs sem : unit =
    let 
	fun paren str =
	    let
		val clist = String.explode str
	    in
		if (hd clist = #"(" andalso last clist = #")") then str
		else "(" ^ str ^ ")"
	    end
    in
	writeSempre ("(rule " ^ lhs ^ " " ^  paren rhs ^ " " ^ paren sem ^ ")")
    end

end
    
