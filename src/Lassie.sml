structure Lassie =
struct

val map = List.map
fun mem x l = List.exists (fn x' => x = x') l

exception LassieException of string

(*********************************)
(*            Utils              *)
(*********************************)
fun sleep t =
    let
  val wakeUp = Time.+ (Time.now(), Time.fromReal(t))
  fun wait () = if Time.> (Time.now(), wakeUp) then () else wait ()
    in
  wait ()
    end

fun flushStream instream = case TextIO.canInput(instream, 5000) of
             SOME n => if n = 0 then ()
           else (TextIO.input(instream); flushStream(instream))
           | NONE => ()

(* some string editing to remove long package names esp. in call formulas *)
fun simplifyAbsoluteNames str =
    let
  fun isSep s =  mem s [#" ", #"(", #")", #"\""]
  fun append s l = case l of
           [] => [s]
         | hd::tl => (s ^ hd)::tl
  val tokens = List.foldl (fn (c,l) => if isSep c then ""::(String.str c)::l else append (String.str c) l)
        []
        (List.rev (String.explode str))
  fun isNotEmpty s = not (s = "")
  fun getLocalName s = List.hd (List.rev (String.tokens (fn c => c = #".") s))
    in
  String.concat (map getLocalName (List.filter isNotEmpty tokens))
    end

(* escape quotes and backslashes before writing to a string *)
fun escape str =
    let
  val escEsc = map (fn c => if c = "\\" then "\\\\" else c)
  val escQuotes = map (fn c => if c = "\"" then "\\\"" else c)
    in
  str |> String.explode
      |> map String.str
      |> escEsc
      |> escQuotes
      |> String.concat
    end

(* normalize a string representing an HOL4 expression for viewing *)
fun normalize str =
    let
  (* spcae out function applications through direct parens e.g. map(f)lst *)
  fun injectSpc sl =
      case sl of
    s1::s2::tl => if (s2 = "(" andalso not (mem s1 ["("," ",")"]))
         orelse
         (s1 = ")" andalso not (mem s2 [")"," "]))
            then injectSpc (s1::" "::s2::tl)
            else s1::(injectSpc (s2::tl))
        | other => other
  (* rewrite string with a minimal number of parentheses *)
  fun paren str b = if b then ("("::str) @ [")"] else str
  fun rmParens left p right =
      case right of
    [] => (left, false, []) (* base case *)
        | c::tail =>
    if c = ")" then (left, p, tail) (* base case of rec calls *)
    else if c = "(" then
        let (* inductive case *)
      val (left', p', right') = rmParens [] false tail (* rec *)
      (* if nothing on left do not parenthesize, applications are left associative *)
      val left' = if left = [] then left' else paren left' p'
      val left' = if left' = [] then ["(",")"] else left' (* unit *)
        in rmParens (left @ left') p right' end (* continue *)
    else rmParens (left@[c]) (p orelse c = " ") tail
  val (retStr, _, _) = rmParens [] false ( str |> String.explode
                 |> (map String.str)
                 |> injectSpc )
    in
  String.concat retStr
    end


(**************************************)
(*           Communication            *)
(**************************************)
val logging = ref false;

(* wait for the SEMPRE prompt; signifies end of execution *)
fun waitSempre instream =
    let
  val s = TextIO.input(instream);
  val _ = if !logging then print s else ()
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

val SEMPRE_RESPONSE = ref (SOME {candidates= [{score= 0.0,
                 prob= ~1.0,
                 anchored= true,
                 formula= "",
                 value= "NO_TAC",
                 tactic= NO_TAC}],
         stats= {cmd= "q",
           size= 2,
           status= "Core"},
         lines= [""]})
val _ = SEMPRE_RESPONSE := NONE

val AMBIGUITY_WARNING = ref (SOME {set= [""],  span= ""})
val _ = AMBIGUITY_WARNING := NONE

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

fun showList lst : string =
    let
  fun helper l s = case l of
           [] => "[" ^ s ^ "]"
         | hd::tl => helper tl (s ^ "," ^ hd)
    in
  case lst of
      [] => "[]"
    | hd::tl => helper (rev tl) hd
    end

fun printAmbiguities () =
    case !AMBIGUITY_WARNING of
  NONE => ()
      | SOME warning => print ("Warning (ambiguity)-\n   Lassie could not disambiguate the expression\n      `"
             ^ (#span warning)
             ^ "`\n   in the utterance. Possible interpretations include:\n      "
             ^ showList (#set warning)
             ^ ".\n   Lassie might be able to parse the utterance if you are more specific.\n\n")

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
  case !SEMPRE_RESPONSE of
      NONE => raise LassieException ("Problem reading SEMPRE's response (empty response record)")
    | SOME response => case #candidates response of
         [] => let
          val _ = printAmbiguities()
            in
          raise LassieException ("Could not parse the utterance `"
               ^ utt
               ^ "`, you can provide a definition using Lassie.def")
            end
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
  writeSempre ("(:accept " ^ (quot (escape utt)) ^ " " ^ (quot (escape formula)) ^ ")")
    end


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
  fn (idx : int) => if idx > length derivations orelse idx < 1 then
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
  fun getFormula u = [u, (u |> sempre |> fst |> #formula |> escape |> escape)]

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
