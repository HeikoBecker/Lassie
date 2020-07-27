(**
  structure LassieParserLib
  Implements a parser from the intermediate language produced by
  SEMPRE into HOL4 tactics by looking them up in a map provided by
  TacticMap.sml
**)
structure LassieParserLib =
struct

  open Abbrev Tactical Manager;
  open LassieUtilsLib TacticMap;

  exception NoParseException of string;

  datatype token =
    Tac of string
    | Tacl of string
    | TacComb of string
    | ThmTac of string
    | ThmListTac of string
    | QuotTac of string
    | AsmTestTac of string
    | AsmMatchTac of string
    | QuotSpecThmTac of string
    | QuotListSpecThmTac of string
    | Thm of string
    | ThmList of string list
    | TermStart
    | TermEnd
    | ListStart
    | ListEnd
    | ListSep;

  fun lex (strs:string list) : (token * string list) option =
    case strs of
    [] =>  NONE
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
      | "THMTAC" => SOME (ThmTac txt, strs)
      | "THMLISTTAC" => SOME (ThmListTac txt, strs)
      | "QUOTTAC" => SOME (QuotTac txt, strs)
      | "ASMTESTTAC" => SOME (AsmTestTac txt, strs)
      | "ASMMATCHTAC" => SOME (AsmMatchTac txt, strs)
      | "QUOTSPECTHMTAC" => SOME (QuotSpecThmTac txt, strs)
      | "QUOTLISTSPECTHMTAC" => SOME (QuotListSpecThmTac txt, strs)
      | "THM" => SOME (Thm txt, strs)
      | _ =>  NONE;

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
    | SOME (Thm th, strs) =>
      (case findThm th of
      NONE => raise NoParseException ("Could not find theorem " ^ th ^ " in current context")
      | SOME th => (th, strs))
    | SOME _ => raise NoParseException "Could not parse a theorem";

  local
    fun readList strs singleton endTok =
      let
        val (th, strs) = singleton strs
        val (ths, strs2) = readList strs singleton endTok
      in
        (th :: ths, strs2)
      end
      handle e =>
        case lex strs of
        SOME (tok, strs) =>
          if (tok = endTok) then ([], strs)
          else raise NoParseException "No valid list"
        | _ => raise NoParseException "No valid list"
  in
  fun parseList (strs:string list) singleton startTok endTok =
    case lex strs of
    SOME (tok,strs) =>
      if (tok = startTok) then readList strs singleton endTok
      else raise NoParseException "No valid list"
    |  _ => raise NoParseException "No valid theorem list"
  end;

  fun parseThmList strs = parseList strs parseThm ListStart ListEnd;

  fun parseTm (strs:string list) :(term frag list * string list) =
    let
        val (tm, strs) =
          parseList strs (fn (ss:string list) => (hd ss, tl ss)) TermStart TermEnd
    in
      (List.map QUOTE tm, strs)
    end;

  fun parseTmList strs =
    parseList strs parseTm ListStart ListEnd;

  fun parseThmTactic strs =
    case lex strs of
    SOME (ThmTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
      SOME (ThmTactic th) => (th, strs)
      | _ => raise NoParseException ("Theorem tactic " ^ str ^ " not found \n"))
    | _ => raise NoParseException ("No theorem tactic found where it was expected\n");

local
  fun parsePartial (inp:string list) :(tactic * string list) =
    case lex inp of
    SOME (Tac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
        SOME (Tactic t) => (t,strs)
        | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
    | SOME (ThmTac str, strs) =>
      let val (thTac, strs) = parseThmTactic inp
          val (th, strs) = parseThm strs in
          (thTac th, strs)
      end
    | SOME (ThmListTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
        SOME (ThmListTactic thsTac) =>
          let val (thms, strs) = parseThmList strs in
            (thsTac thms, strs)
          end
        | _ => raise NoParseException ("Thmlist tactic " ^ str ^ " not found\n"))
    | SOME (QuotTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
        SOME (QuotTactic qt) =>
          let val (tm, strs) = parseTm strs in
            (qt tm, strs)
          end
        | _ => raise NoParseException ("Quotation tactic" ^ str ^ " not found\n"))
    | SOME (AsmTestTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
      SOME (AsmTestTactic t) =>
        let val (thTac, strs) = parseThmTactic strs in
          (t thTac, strs)
        end
      | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
    | SOME (AsmMatchTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
      SOME (AsmMatchTactic t) =>
        let val (tm, strs2) = parseTm strs
            val (thTac, strs3) = parseThmTactic strs2
        in
          (t tm thTac, strs)
        end
      | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
    | SOME (QuotSpecThmTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
      SOME (QuotSpecThmTactic t) =>
        let
          val (tm, strs2) = parseTm strs
          val (thTac, strs3) = parseThmTactic strs2
          val (thm, strs4) = parseThm strs3
        in
          (t tm thTac thm, strs)
        end
      | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
    | SOME (QuotListSpecThmTac str, strs) =>
      (case TacticMap.lookupTac str TacticMap.stdTree of
      SOME (QuotListSpecThmTactic t) =>
        let
          val (tms, strs2) = parseTmList strs
          val (thTac, strs3) = parseThmTactic strs2
          val (thm, strs4) = parseThm strs3
        in
          (t tms thTac thm, strs)
        end
      | _ => raise NoParseException ("Tactic " ^ str ^ " not found\n"))
    | _ =>  raise NoParseException "Cannot parse input string";
  fun parseFull (inp:string list) : (tactic * string list) =
    let val (t1, strs1) = parsePartial inp in
      case lex strs1 of
      SOME (TacComb str, strs2) =>
        (case TacticMap.lookupTac str TacticMap.stdTree of
        SOME (TacticComb t) =>
          let val (t2, strs3) = parsePartial strs2 in
            (t (t1, t2), strs3)
          end
        | _ => raise NoParseException ("Tactic combinator " ^ str ^ " not found\n"))
      | _ => (t1,strs1)
    end;
  in
  fun parse (sempreResp:string) :tactic =
    let val inp = LassieUtilsLib.string_split sempreResp #" " in
      fst (parseFull inp)
    end;
  end;

end;
