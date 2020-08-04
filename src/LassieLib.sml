(**
  Structure LassieLib

  Implements the main communication interface between HOL4 and SEMPRE
**)
structure LassieLib =
struct

  open Abbrev Tactical Manager;
  open LassieUtilsLib LassieParserLib;

  exception LassieException of string;

  datatype SempreParse = Tactic of tactic | Command of unit -> proof;

  type sempre_response =
    { formula: string,
      result: SempreParse};

  type ambiguity_warning =
    { set : string list,
      span: string };

  datatype AmbiguityWarning =
    Warning of ambiguity_warning;

  val map = List.map
  fun mem x l = List.exists (fn x' => x = x') l
  val LASSIEPROMPT = "|>";
  val LASSIESEP = ref ".";

  val knownJargon :(string * (unit->unit)) list ref= ref [];

  val sempreResponse :sempre_response list ref = ref [];

  val ambiguityWarning : AmbiguityWarning option ref = ref NONE;

  val lastUtterance = ref "";

  val LASSIEDIR =
    let val lDir = getOSVar "LASSIEDIR" in
    if (endsWith lDir #"/") then lDir else (lDir ^ "/") end;
  (* val socketPath = LASSIEDIR ^ "sempre/interactive/sempre-out-socket.sml"; *)
  val historyPath = LASSIEDIR ^ "sempre/interactive/last-sempre-output.sml";

  (**************************************)
  (*           Communication            *)
  (**************************************)
  val logging = ref false;

  (* wait for the SEMPRE prompt; signifies end of execution
     returns the complete string read from SEMPRE *)
  fun waitSempre instream :string =
    let
      val s = TextIO.input(instream);
      val _ = if !logging then print s else ()
    in
      if String.isSuffix "\n> " s orelse s = "> " then s
      (* else if s = "" then raise LassieException "Reached EOS? Empty string was read."  *)
      else s ^ (waitSempre instream)
    end;

  (* run SEMPRE as a subprocess through the run script
   returns in- and outstream of its shell *)
  fun launchSempre () =
    let
      val currDir = OS.FileSys.getDir();
      (* SEMPRE's run script is dependent on being at the top of its directory *)
      val _ = OS.FileSys.chDir (LASSIEDIR ^ "/sempre")
      val instream' =
        Unix.textInstreamOf
          (Unix.executeInEnv("interactive/run",["-n","@mode=lassie"],
          Posix.ProcEnv.environ()))
      val execCommand = TextIO.input(instream')
      val (instr,outstr) =
        case String.tokens Char.isSpace execCommand of
          [] => raise Fail "Run script returned no arguments"
          | cmd::args => Unix.streamsOf(Unix.execute(cmd,args))
      val _ = waitSempre(instr);
      val _ = OS.FileSys.chDir currDir;
    in
      (ref instr, ref outstr)
    end;

  (* Start SEMPRE when the Lib file is loaded
    TODO: Box into a function? *)
  val (instream, outstream) = launchSempre();

  (* send a string to sempre *)
  fun writeSempre (cmd : string) =
    let
      (* not needed anymore as we do not load from the socket file
      val _ = if OS.FileSys.access (socketPath, []) then OS.FileSys.remove socketPath else () *)
      val _ = lastUtterance := cmd
      val _ = if !logging then (print "Writing "; print cmd; print "\n") else ()
      val _ = TextIO.output(!outstream, cmd ^ "\n")
      val _ = TextIO.flushOut(!outstream)
    in
      ()
    end;

  (* Splits the response of SEMPRE into separate components based on matching
    pairs of { and } *)
  fun prepareResponse s =
  List.foldl
    (fn (xs, ys) =>
      ys @ (LassieUtilsLib.string_split xs #"}")) [] (LassieUtilsLib.string_split s #"{");

  (* Extracts text starting with descr from list xs *)
  fun getPart descr xs =
    case xs of
    [] => NONE
    | x::[] => NONE
    | x::y::xs =>
       if (String.isSuffix descr x) then
         SOME(y,xs)
       else getPart descr (y::xs);

  (* Removes a trailing quotation mark " from s *)
  fun strip_quotmark s =
    let val xs = explode s in
      if hd xs = #"\"" then implode (tl xs) else s end;

  (* read SEMPRE's response from stdin *)
  (* returns a derivation (i.e. the first candidate) of type sempre_response *)
  (* TODO: Ambiguities ? *)
  fun readSempre () :sempre_response=
  let
    val response = waitSempre (!instream) |> prepareResponse;
    val (theFormula,theResponse) =
      case getPart "Top formula " response of
      NONE => raise LassieException "Could not extract formula"
      | SOME (formula,remainder) =>
      case getPart "Top value " remainder of
      NONE => raise LassieException "Could not extract value"
      | SOME (response,remainder) =>
        (String.map (fn c => if (c = #"\n") then #" " else c) formula, response)
    val cleanedResponse =
      LassieUtilsLib.get_suffix_after_match "(string " theResponse
      |> explode |> List.rev |> implode
      |> LassieUtilsLib.get_suffix_after_match ")" (* TODO: This may be too fragile...*)
      |> explode |> List.rev |> implode
      |> strip_quotmark |> explode |> List.rev |> implode
      |> strip_quotmark |> explode |> List.rev |> implode
      |> String.map (fn c => if (c = #"$") then #" " else c)
    val _ = if !logging then (print "\n"; print cleanedResponse; print "\n") else ();
    val tac = LassieParserLib.parse cleanedResponse;
  in
    { formula= theFormula, result = Tactic tac}
  end;

  (* send a NL query to sempre and return at least a derivation *)
  fun sempre utt = (writeSempre utt; readSempre ());

  (*************************************)
  (*          Main interface           *)
  (*************************************)
  fun listStrip ls1 ls2 =
    case (ls1, ls2) of
    ([], _) => ls2
    | (i1::ls1, i2::ls2) => if (i1 = i2) then listStrip ls1 ls2 else []
    | (_,_) => [];

  fun removeTrailing str fullStr =
    implode (rev (listStrip (List.rev (explode str)) (List.rev (explode fullStr))));

  (* parse and return most likely tactic *)
  fun nltac (utt:'a frag list) : tactic=
    let
     val uttStr1 =
        case utt of
        [QUOTE s] => LassieUtilsLib.preprocess s
        | _ => raise LassieException "";
      val uttStr =
        String.translate
          (fn c => if c = #"\n" then " " else if Char.isCntrl c then "" else implode [c]) uttStr1;
      val _ =
        if (not (String.isSuffix (! LASSIESEP) uttStr)) then
          raise LassieException "Tactics must end with LASSIESEP"
        else ();
      val theStrings = LassieUtilsLib.string_split uttStr #" ";
    in
      snd (List.foldl (fn (str, (strAcc, tac)) =>
          if (String.isSuffix (! LASSIESEP) str) then
            let
              val theString = strAcc ^ " " ^ (removeTrailing (! LASSIESEP) str);
              val t = sempre theString;
            in
              case #result t of
              Tactic t => ("",tac THEN t)
              | Command c => raise LassieException "Command found during tactic"
            end
          else (strAcc ^ " " ^ str, tac)) ("", ALL_TAC) theStrings)
    end;

  (* define an utterance in terms of a list of utterances*)
  fun def ndum niens : string =
    let
      (* for each utterance of the definition, get its logical form *)
      fun getFormula u = [u, (u |> sempre |> #formula |> escape |> escape)]
      (* formatting *)
      fun quot s = "\"" ^ s ^ "\""
      fun quot' s = "\\\"" ^ s ^ "\\\""
      fun list2string l = "[" ^ (String.concatWith "," l) ^ "]"
      fun stripAllSpaces s = explode s |> stripSpaces |> explode |> List.rev
        |> stripSpaces |> explode |> List.rev |> implode;
      val definiens =
        niens |> (map getFormula)
              |> map (map stripAllSpaces)
              |> (map (map quot'))
              |> (map list2string)
              |> list2string
      val theDef = "(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")"
      val _ = if (!logging) then (print "Defining:\n"; print theDef; print "\n\n") else ()
      val _ = writeSempre ("(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")")
      val res = waitSempre(!instream)
      val _ = (if (!logging) then print res else ())
    in
      if (String.isPrefix "Invalid" res) then
        (print "BUG"; def ndum niens)
      else res
    end;

  fun addRule lhs rhs sem anchoring : unit =
    let
      fun paren str =
        let
          val clist = String.explode str
        in
          if (hd clist = #"(" andalso last clist = #")") then str
          else "(" ^ str ^ ")"
        end
    in
      (writeSempre ("(rule " ^ lhs ^ " " ^  paren rhs ^ " " ^ paren sem ^ " " ^ paren anchoring ^ ")");
      waitSempre (!instream); ())
    end;

  fun addIDRule (cat:string) (str:string) (anchoring:string) : unit =
    addRule cat str ("ConstantFn ( string \"" ^ str ^ "\")") anchoring;

  (** Adding a custom SML tactic to the grammar **)
  fun addCustomTactic tac str : unit =
    (addIDRule "$tactic" ("TAC$"^str) "anchored 1";
    LassieParserLib.addCustomTactic tac str);

  (** Adding a custom SML thm tactic to the grammar **)
  fun addCustomThmTactic tac : unit =
    addIDRule "$thm->tactic" tac "anchored 1";

  (** Adding a custom SML thmlist tactic to the grammar **)
  fun addCustomThmlistTactic tac : unit =
    addIDRule "$thmlist->tactic" tac "anchored 1";

  fun addCustomTermTactic tac : unit =
    addIDRule "$term->tactic" tac "anchored 1";

  fun printGrammar () : unit =
    let
      val prev = !logging;
      val _ = logging := true;
      val _ = writeSempre ("(grammar)");
      val _ = waitSempre (!instream);
      val _ = logging := prev;
    in
      () end;

  fun registerJargon (name:string) (loader:unit->unit) =
    knownJargon := (name, loader):: !knownJargon;

  fun knownJargons () = !knownJargon;

  fun loadJargon (n:string) = (map (fn (s,f) => if s = n then f() else ()) (!knownJargon); ());

(*
  local
    fun printHelp () =
      (
      map (fn x => print (x ^"\n"))
        [ "",
          "=======================================",
          "======= Lassie Interactive Mode =======",
          "=======================================",
          " ",
          "Send natural language commands with the same keybinding as the one",
          "used to send code to you running HOL4 session.",
          "The commands will be send to Lassie and evaluated.",
          "HOL4 keybindings still work as before.",
          "Sending \"exit\" quits the session and clears the goal state,",
          "\"pause\" quits the session and keeps the goal state.",
          ""
        ]; ());
  fun getAll instream =
    case TextIO.canInput (instream,1) of
    NONE => ""
    | SOME _ =>
      (case TextIO.input1 instream of
      NONE => ""
      | SOME c => implode [c] ^ (getAll instream))
  in
    fun proveVerbose () =
      let
        (* Set up prompt; wait for input *)
        val _ = print LASSIEPROMPT;
        val theText =
          case (TextIO.inputLine (TextIO.stdIn)) of
          NONE => raise LassieException "Error getting input"
          | SOME s => LassieUtilsLib.preprocess (s ^ (getAll (TextIO.stdIn)))
        val theTrueText =
          LassieUtilsLib.preprocess theText
      in
        (* Handle exit keyword separately TODO: Make command? *)
        if (theTrueText = "exit;\n")
        then (print " Exiting\n") (* ProofRecorderLib.reset()) *)
        (* Handle pause keyword separately TODO: Make command? *)
        else if (theTrueText = "pause;\n")
        then (print "Pausing proof.\nReturn with LassieLib.proveVerbose().\n")
        (* help keyword *)
        else if (theTrueText = "help;\n")
        then (printHelp(); proveVerbose())
        (* Proof step or command was given, parse with SEMPRE *)
        else
          let
            (* Remove semicolons and line-breaks from string *)
           val theString = String.translate
                              (fn x => if ((x = #"\n") orelse (x = #";")) then "" else implode [x])
                              theTrueText;
            (* Get a tactic from SEMPRE *)
            val res = theString |> sempre |> fst
            val theTactic = #value res;
            val theResult = #result res;
            val _ = case theResult of
                    Command c => SOME (c ())
                    | _ => NONE;
            val _ = case theResult of
                    Tactic t => et (theTactic, t)
                    | _ => raise LassieException "No valid parse found; Please provide a command or a tactic."

            (* first print the current goal *)
            val _  = print "\n";
            val t = proofManagerLib.pp_proof (proofManagerLib.p());
            val _ = PolyML.prettyPrint (print, 80) t;
            val _  = print "\n";
            (*
            val done =
              (let val _ = proofManagerLib.top_goal(); in false end
              handle HOL_ERR _=> true); *)
          in
            (*
            if (done)
            then (print ("Finished proof;\nPrinting proofscript\n\n" ^
                        ProofRecorderLib.pp_finished (hd(! ProofRecorderLib.finished)));
                  ProofRecorderLib.reset())
            else *)
            (proveVerbose())
          end
        end
  end;
*)

(** UNUSED

  fun showList lst : string =
    let
      fun helper l s = foldl (fn (s1,s2) => s2 ^ ", "^ s1) s l
    in
      case lst of
        [] => "[]"
        | hd::tl => "[ " ^ helper tl hd ^ " ]"
    end;

  fun printAmbiguities () =
    case !ambiguityWarning of
      NONE => ()
    | SOME (Warning warning) =>
        let val _ = print
          ("Warning (ambiguity)-\n   Lassie could not disambiguate the expression\n      `"
          ^ (#span warning)
          ^ "`\n   in the description. Possible interpretations include:\n      "
          ^ showList (#set warning)
          ^ ".\n   Lassie might be able to parse the description if you are more specific.\n\n")
        in
          ambiguityWarning := NONE
        end;

  (* tell sempre you accepted a derivation; affects future weights *)
  fun accept (utt, formula) : unit =
    let
      fun quot s = "\"" ^ s ^ "\""
    in
      writeSempre ("(:accept " ^ (quot (escape utt)) ^ " " ^ (quot (escape formula)) ^ ")")
    end;

  (* interactively parse utterances, allow for selection of preferred derivation, then evaluation *)
  (*
  fun lassie utt : int -> proof =
    let
      val _ = print ("Trying to parse `" ^ utt ^ "`...\n\n")
      val derivations = utt |> sempre |> (fn (hd,tl) => hd::tl)
      fun dprinter derivs idx =
        case derivs of
          [] => ()
          | d::ds => (print ("\nDerivation [" ^ Int.toString idx ^ "]:\n"
               ^ "\tFormula: " ^ simplifyAbsoluteNames (#formula d) ^ "\n"
               ^ "\tValue: " ^ (normalize (#value d)) ^ "\n\n");
              dprinter ds (idx + 1))
    in
      dprinter derivations 1; (* if no index is given, just print the derivations *)
      fn (idx : int) =>
        if idx > length derivations orelse idx < 1
          then raise LassieException "Derivation index out of bounds"
          else
            let
              val d = List.nth (derivations, (idx - 1))
            in
              accept (utt, #formula d);
              print ("Accepted derivation [" ^ Int.toString idx ^ "]\n");
              case #result d of
              Command c => c ()
              | Tactic t => proofManagerLib.e t
            end
    end;

  (*
  fun nltacl uttl : tactic =
    case uttl of
      [] => ALL_TAC
      | utt::tail => (nltac utt) THEN (nltacl tail);
  *)

(*
  (* define an utterance in terms of a list of utterances*)
  fun def (tac:'a frag list) (tacDescriptions:'a frag list list) : unit =
    let
      (* for each utterance of the definition, get its logical form *)
      fun getFormula u = [u, (u |> sempre |> fst |> #formula |> escape |> escape)]
      (* formatting *)
      fun quot s = "\"" ^ s ^ "\""
      fun quot' s = "\\\"" ^ s ^ "\\\""
      fun list2string l = "[" ^ (String.concatWith "," l) ^ "]"

      val definiens =
        tacDescriptions
              |> (map (fn q => case q of [QUOTE s] => preprocess s | _ => ""))
              |> (fn sl => if (!logging) then (map (fn s => print (s^"\n")) sl; sl) else sl)
              |> (map getFormula)
              |> (map (map quot'))
              |> (map list2string)
              |> list2string
      val ndum = case tac of [QUOTE s] => preprocess s | _ => ""
      val theDef = "(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")"
    in
      if (!logging) then print theDef else ();
      writeSempre ("(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")")
    end;
*)
*)
**)

end
