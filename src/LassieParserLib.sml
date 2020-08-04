(**
  structure LassieParserLib
  Implements a parser from the intermediate language produced by
  SEMPRE into HOL4 tactics by looking them up in a map provided by
  TacticMap.sml
**)
structure LassieParserLib =
struct

  open Abbrev Tactical Manager Conv BoundedRewrites;
  open LassieUtilsLib TacticMap;

  exception NoParseException of string;

  val tacticMap = ref TacticMap.stdTree;

  val thmModifs = ["Once", "GSYM"];

  datatype token =
    Tac of string
    | Tacl of string
    | TacComb of string
    | TmComb of string
    | ThmTac of string
    | ThmListTac of string
    | QuotTac of string
    | AsmTestTac of string
    | AsmMatchTac of string
    | QuotSpecThmTac of string
    | QuotListSpecThmTac of string
    | Thm of string
    | ThmList of string list
    | ThmModif of string
    | TermStart
    | TermEnd
    | LBrac
    | RBrac
    | ListStart
    | ListEnd
    | ListSep;

  fun lex (strs:string list) : (token * string list) option =
    case strs of
    [] =>  NONE
    | "(" :: strs => SOME (LBrac, strs)
    | ")" :: strs => SOME (RBrac, strs)
    | "[" :: strs => SOME (ListStart, strs)
    | "]" :: strs => SOME (ListEnd, strs)
    | "," :: strs => SOME (ListSep, strs)
    | "TERMSTART" :: strs => SOME (TermStart, strs)
    | "TERMEND" :: strs => SOME (TermEnd, strs)
    | s1::[]=> NONE
    | descr::txt::strs =>
      case descr of
      "TAC" => SOME (Tac txt, strs)
      | "TACL" => SOME (Tacl txt, strs)
      | "TACCOMB" => SOME (TacComb txt, strs)
      | "TERMCOMB" => SOME (TmComb txt, strs)
      | "THMTAC" => SOME (ThmTac txt, strs)
      | "THMLISTTAC" => SOME (ThmListTac txt, strs)
      | "QUOTTAC" => SOME (QuotTac txt, strs)
      | "ASMTESTTAC" => SOME (AsmTestTac txt, strs)
      | "ASMMATCHTAC" => SOME (AsmMatchTac txt, strs)
      | "QUOTSPECTHMTAC" => SOME (QuotSpecThmTac txt, strs)
      | "QUOTLISTSPECTHMTAC" => SOME (QuotListSpecThmTac txt, strs)
      | "THM" => SOME (Thm txt, strs)
      | s => if (List.exists (fn a => a = s) thmModifs) then
              SOME (ThmModif s, txt::strs)
              else NONE;

  fun findThm (name:string) :thm option =
    let val spl = LassieUtilsLib.string_split name #"."
      val cmp =
        if (List.length spl = 1) then
          fn ((theory, theorem), stmt) => hd spl = theorem
        else
          fn ((theory, theorem), stmt) =>
            (LassieUtilsLib.get_prefix_before_match "Theory" (hd spl)) = theory andalso
            hd (tl spl) = theorem
    in
      case List.find cmp (DB.listDB()) of
      NONE => NONE
      | SOME (_, (th, _)) =>  SOME th
    end;

  fun parseThm (strs:string list) : (thm * string list) =
    case lex strs of
    NONE => raise NoParseException "No theorem identifier found where theorem was expected"
    | SOME (ThmModif s, strs1) =>
      let val (th, strs2) = parseThm strs1 in
      case s of
      "Once" => (Once th, strs2)
      | "GSYM" => (GSYM th, strs2)
      | _ => raise NoParseException ("Invalid theorem modifier "^s^" found\n")
      end
    | SOME (Thm th, strs) =>
      (case findThm th of
      NONE => raise NoParseException ("Could not find theorem " ^ th ^ " in current context")
      | SOME th => (th, strs))
    | SOME _ => raise NoParseException "Could not parse a theorem";

  fun peek (s:string list) :token =
    case lex s of
    SOME (tok, strs) => tok
    | _ =>  raise (NoParseException "Could not look into next token when expecting a token\n")

  local
    fun readList strs singleton endTok sep =
        if (case lex strs of
            NONE => false
            | SOME (tok, strs2) => tok = endTok) then ([], snd (valOf (lex strs)))
        else
        let val (th, strs2) = singleton strs in
        if (case lex strs2 of
            NONE => false
            | SOME (tok, strs3) => tok = endTok) then ([th], snd (valOf (lex strs2)))
        else
          let
            val strs3 = sep strs2
            val (ths, strs4) = readList strs3 singleton endTok sep
          in
            (th :: ths, strs4)
          end
        end
  in
  fun parseList (strs:string list) singleton startTok endTok sep =
    case lex strs of
    SOME (tok,strs) =>
      if (tok = startTok) then readList strs singleton endTok sep
      else raise NoParseException "No valid list"
    |  _ => raise NoParseException "No valid theorem list"
  end;

  fun consumeListSep strs =
    case lex strs of
    SOME (ListSep, strs2) => strs2
    | _ => raise NoParseException "No list separator found";

  fun parseThmList strs = parseList strs parseThm ListStart ListEnd consumeListSep;

  fun consumeTmSep strs = strs;

  fun parseTm (strs:string list) :(term frag list * string list) =
    let
        val (tm, strs) =
          parseList strs (fn (ss:string list) => (hd ss, tl ss)) TermStart TermEnd consumeTmSep
        val fullTm = foldl (fn (s1,s2) => if s2 = "" then s1 else s1 ^ " " ^ s2) "" (List.rev tm)
    in
      ([QUOTE fullTm], strs)
    end;

  fun parseTmList strs =
    parseList strs parseTm ListStart ListEnd consumeListSep;

  fun parseThmTactic strs =
    case lex strs of
    SOME (ThmTac str, strs) =>
      (case TacticMap.lookupTac str (!tacticMap) of
      SOME (ThmTactic th) => (th, strs)
      | _ => raise NoParseException ("Theorem tactic " ^ str ^ " not found \n"))
    | _ => raise NoParseException ("No theorem tactic found where it was expected\n");

  local
    fun parsePartial (inp:string list) :(tactic * string list) =
      case lex inp of
      SOME (Tac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
          SOME (Tactic t) => (t,strs)
          | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
      | SOME (ThmTac str, strs) =>
        let val (thTac, strs) = parseThmTactic inp
            val (th, strs) = parseThm strs in
            (thTac th, strs)
        end
      | SOME (ThmListTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
          SOME (ThmListTactic thsTac) =>
            let val (thms, strs) = parseThmList strs in
              (thsTac thms, strs)
            end
          | _ => raise NoParseException ("Thmlist tactic " ^ str ^ " not found\n"))
      | SOME (QuotTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
          SOME (QuotTactic qt) =>
            let val (tm, strs) = parseTm strs in
              (qt tm, strs)
            end
          | _ => raise NoParseException ("Quotation tactic" ^ str ^ " not found\n"))
      | SOME (AsmTestTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
        SOME (AsmTestTactic t) =>
          let val (thTac, strs) = parseThmTactic strs in
            (t thTac, strs)
          end
        | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
      | SOME (AsmMatchTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
        SOME (AsmMatchTactic t) =>
          let val (tm, strs2) = parseTm strs
              val (thTac, strs3) = parseThmTactic strs2
          in
            (t tm thTac, strs3)
          end
        | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
      | SOME (QuotSpecThmTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
        SOME (QuotSpecThmTactic t) =>
          let
            val (tm, strs2) = parseTm strs
            val (thTac, strs3) = parseThmTactic strs2
            val (thm, strs4) = parseThm strs3
          in
            (t tm thTac thm, strs4)
          end
        | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
      | SOME (QuotListSpecThmTac str, strs) =>
        (case TacticMap.lookupTac str (!tacticMap) of
        SOME (QuotListSpecThmTactic t) =>
          let
            val (tms, strs2) = parseTmList strs
            val (thTac, strs3) = parseThmTactic strs2
            val (thm, strs4) = parseThm strs3
          in
            (t tms thTac thm, strs4)
          end
        | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
      | _ =>  raise NoParseException "Cannot parse input string";
    fun parseFull (inp:string list) : (tactic * string list) =
      let val (t1, strs1) =
        (case peek inp of
        TermStart =>
          let val (tm, strs2) = parseTm inp in
          case lex strs2 of
          SOME (TmComb str, strs3) =>
            (case TacticMap.lookupTac str (!tacticMap) of
            SOME (TermComb tc) =>
              let val (tac, strs4) = parseFull strs3 in
                (tc (tm,tac), strs4)
              end
            | _ => raise NoParseException ("Term combinator " ^ str ^ " not found\n"))
          | _ => raise NoParseException ("Unsupported tactic structure in " ^ (foldl (fn (a,b) => b ^ a) "" inp))
          end
        | LBrac =>
          let val (t1, strs1) = parseFull (snd (valOf (lex inp))) in
            case peek strs1 of
            RBrac => (t1, snd (valOf (lex strs1)))
            | _ => raise NoParseException "Unmatched parenthesis"
          end
        | _ => parsePartial inp)
      in
        case lex strs1 of
        SOME (TacComb str, strs2) =>
          (case TacticMap.lookupTac str (!tacticMap) of
          SOME (TacticComb t) =>
              let val (t2, strs3) = parseFull strs2 in
                (t (t1, t2), strs3)
              end
          | _ => raise NoParseException ("Tactic combinator " ^ str ^ " not found\n"))
        | _ => (t1, strs1)
      end;
  in
    fun parse (sempreResp:string) :tactic =
      let
        val inp = LassieUtilsLib.string_split sempreResp #" "
        val inp = List.rev (foldl (fn (s,ss) => if s = "" then ss else s::ss) [] inp)
     in
        fst (parseFull inp)
      end;
  end;

  fun addCustomTactic (tac:tactic) (str:string) =
    tacticMap := insTac (str, tac) (!tacticMap);

end;
