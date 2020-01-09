structure LassieLib =
struct

  open Abbrev Tactical Manager;
  open LassieUtilsLib ProofRecorderLib;

  exception LassieException of string;

  datatype SempreParse = Tactic of tactic | Command of unit -> proof;

  type sempre_response =
    { score: real,
      prob:real,
      value: string,
      formula: string,
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

  val sempreResponse :sempre_response list ref = ref [];

  val ambiguityWarning : AmbiguityWarning option ref = ref NONE;

  val lastUtterance = ref "";

  val LASSIEDIR = let val lDir = getOSVar "LASSIEDIR"; in
    if (endsWith lDir #"/") then lDir else (lDir ^ "/") end;
  val socketPath = LASSIEDIR ^ "sempre/interactive/sempre-out-socket.sml";
  val historyPath = LASSIEDIR ^ "sempre/interactive/last-sempre-output.sml";

  fun showList lst : string =
    let
      fun helper l s = foldl (fn (s1,s2) => s2 ^ ", "^ s1) s l
    in
      case lst of
        [] => "[]"
        | hd::tl => "[ " ^ helper tl hd ^ " ]"
    end;

  (**************************************)
  (*           Communication            *)
  (**************************************)
  val logging = ref false;

  (* wait for the SEMPRE prompt; signifies end of execution *)
  fun waitSempre instream :string =
    let
      val s = TextIO.input(instream);
      val _ = if !logging then print s else ()
    in
      if String.isSuffix "\n> " s orelse s = "> " then s
      (* else if s = "" then raise LassieException "Reached EOS? Empty string was read."  *)
      else s ^ (waitSempre instream)
    end;

  (* run SEMPRE as a subprocess, through its run script returns in- and outstream of its shell *)
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

  (* Start SEMPRE when the Lib file is loaded *)
  val (instream, outstream) = launchSempre();

  (* send a string to sempre *)
  fun writeSempre (cmd : string) =
    let
      val _ = if OS.FileSys.access (socketPath, []) then OS.FileSys.remove socketPath else ()
      val _ = lastUtterance := cmd
      val _ = TextIO.output(!outstream, cmd ^ "\n")
      val _ =  waitSempre(!instream)
    in
      ()
    end;

  fun printAmbiguities () =
    case !ambiguityWarning of
      NONE => ()
    | SOME (Warning warning) =>
        let val _ = print ("Warning (ambiguity)-\n   Lassie could not disambiguate the expression\n      `"
                           ^ (#span warning)
                           ^ "`\n   in the utterance. Possible interpretations include:\n      "
                           ^ showList (#set warning)
                           ^ ".\n   Lassie might be able to parse the utterance if you are more specific.\n\n")
        in
          ambiguityWarning := NONE
        end

  (* read SEMPRE's response from the "socket" file once there and remove it *)
  (* returns a derivation (i.e. the first candidate) *)
  fun readSempre utt : sempre_response * sempre_response list=
    let
      val _ = sleep 0.1; (* socket file seems to appear a bit after end of execution *)
      val _ =
        if not (OS.FileSys.access (socketPath, []))
        then raise LassieException ("Socket file missing after call to SEMPRE: " ^ socketPath)
        else ()
    in
      QUse.use socketPath;
      if OS.FileSys.access (historyPath, []) then OS.FileSys.remove historyPath else ();
      OS.FileSys.rename {old = socketPath, new = historyPath};
      case !sempreResponse of
        (* [] => raise LassieException ("Problem reading SEMPRE's response (empty response record)")
        | SOME response =>
          case #candidates response of *)
            [] =>
              let
                val _ = printAmbiguities()
              in
                raise LassieException ("Could not parse the utterance `"
                   ^ utt
                   ^ "`, you can provide a definition using LassieLib.def")
              end
            | deriv::tail => (deriv, tail) (* ensures at least one derivation *)
    end;

  (* send a NL query to sempre and return at least a derivation *)
  fun sempre utt = (writeSempre utt; readSempre utt);

  (* tell sempre you accepted a derivation; affects future weights *)
  fun accept (utt, formula) : unit =
    let
      fun quot s = "\"" ^ s ^ "\""
    in
      writeSempre ("(:accept " ^ (quot (escape utt)) ^ " " ^ (quot (escape formula)) ^ ")")
    end;

  (*************************************)
  (*          Main interface           *)
  (*************************************)
  (* interactively parse utterances, allow for selection of preferred derivation, then evaluation *)
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

  (* FIXME *)
  fun listStrip ls1 ls2 =
    case (ls1, ls2) of
    ([], _) => ls2
    | (i1::ls1, i2::ls2) => if (i1 = i2) then listStrip ls1 ls2 else []
    | (_,_) => [];

  fun strip str fullStr =
    implode (rev (listStrip (List.rev (explode str)) (List.rev (explode fullStr))));

  (* parse and return most likely tactic *)
  fun nltac utt : tactic =
    let
      val _ = if (not (String.isSuffix (! LASSIESEP) utt)) then raise LassieException "Tactics must end with LASSIESEP" else ();
      val theStrings = LassieUtilsLib.string_split utt #" ";
    in
      snd (List.foldl
        (fn (str, (strAcc,tAcc)) =>
          if (String.isSuffix (! LASSIESEP) str) then
            let
              val theString = strAcc ^ " " ^ (strip (! LASSIESEP) str);
              val theResult = theString |> sempre |> fst;
              val _ = if (! logging) then print (#formula theResult) else ();
              val theTac = (#result theResult)
            in
              case theTac of
              Command c => raise LassieException ("Entered a command when a tactic was expected")
              | Tactic t => ("",tAcc THEN t)
            end
          else (strAcc ^ " " ^ str,tAcc)) ("", ALL_TAC) theStrings)
  end;

  fun nltacl uttl : tactic =
    case uttl of
      [] => ALL_TAC
      | utt::tail => (nltac utt) THEN (nltacl tail);

  (* define an utterance in terms of a list of utterances*)
  fun def ndum niens : unit =
    let
      (* for each utterance of the definition, get its logical form *)
      fun getFormula u = [u, (u |> sempre |> fst |> #formula |> escape |> escape)]
      (* formatting *)
      fun quot s = "\"" ^ s ^ "\""
      fun quot' s = "\\\"" ^ s ^ "\\\""
      fun list2string l = "[" ^ (String.concatWith "," l) ^ "]"

      val definiens =
        niens |> (map getFormula)
              |> (map (map quot'))
              |> (map list2string)
              |> list2string
      val theDef = "(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")"
    in
      if (!logging) then print theDef else ();
      writeSempre ("(:def " ^ (quot ndum) ^ " " ^ (quot definiens) ^ ")")
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
      writeSempre ("(rule " ^ lhs ^ " " ^  paren rhs ^ " " ^ paren sem ^ " " ^ paren anchoring ^ ")")
    end;

  fun addIDRule (cat:string) (str:string) (anchoring:string) : unit =
    addRule cat str ("ConstantFn ( string \"" ^ str ^ "\")") anchoring;

  (** Adding a custom SML tactic to the grammar **)
  fun addCustomTactic tac : unit =
    addIDRule "$tactic" tac "anchored 1";

  (** Adding a custom SML thm tactic to the grammar **)
  fun addCustomThmTactic tac : unit =
    addIDRule "$thm->tactic" tac "anchored 1";

  (** Adding a custom SML thmlist tactic to the grammar **)
  fun addCustomThmlistTactic tac : unit =
    addIDRule "$thmlist->tactic" tac "anchored 1";

  fun printGrammar () : unit =
    let
      val prev = !logging;
      val _ = logging := true;
      val _ = writeSempre ("(grammar)");
      val _ = logging := prev;
    in
      () end;


  fun stripSpaces s =
    case s of
     [] => ""
    | c::cs => if (c = #" ")
              then stripSpaces cs
              else implode (c::cs);

  fun preprocess s =
    let
      val strs = LassieUtilsLib.string_split s #")"
      val remainder =
        if (String.isPrefix "(*#loc" (hd (strs)))
        then tl (strs)
        else strs
      in
        if String.isPrefix " " (hd remainder)
        then String.concatWith ")" (stripSpaces (explode (hd remainder)) :: (tl remainder))
        else String.concatWith ")"remainder
    end;

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
    fun proveInteractive () =
      let
        (* Set up prompt; wait for input *)
        val _ = print LASSIEPROMPT;
        val theText =
          case (TextIO.inputLine (TextIO.stdIn)) of
          NONE => raise LassieException "Error getting input"
          | SOME s => preprocess (s ^ (getAll (TextIO.stdIn)))
        val theTrueText =
          preprocess theText
      in
        (* Handle exit keyword separately TODO: Make command? *)
        if (theTrueText = "exit;\n")
        then (print " Exiting\n") (* ProofRecorderLib.reset()) *)
        (* Handle pause keyword separately TODO: Make command? *)
        else if (theTrueText = "pause;\n")
        then (print "Pausing proof.\nReturn with LassieLib.proveInteractive().\n")
        (* help keyword *)
        else if (theTrueText = "help;\n")
        then (printHelp(); proveInteractive())
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
            (proveInteractive())
          end
        end
  end;

end
