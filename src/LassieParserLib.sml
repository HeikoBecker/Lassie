structure LassieParserLib =
struct

  open Abbrev Tactical Manager;
  open LassieUtilsLib TacticMap;

  exception NoParseException of string;

  datatype token =
    Tactic of string
    | ThmTactic of string
    | ThmListTactic of string
    | TermTactic of string
    | TermListTactic of string
    | QuotTactic of string
    | QuotListTactic of string
    | Tactical of string
    | Thm of string
    | ThmList of string list
    | Term of string
    | TermList of string list
    | ListStart
    | ListEnd
    | ListSep;

  fun next (s1:string) (strs:string list) =
    case strs of
    [] => false
    | s2::strs => s1 = s2;

  fun lex (strs:string list) : (token * string list) option =
    case strs of
    [] =>  NONE
    | "[" :: strs => SOME (ListStart, strs)
    | "]" :: strs => SOME (ListEnd, strs)
    | "," :: strs => SOME (ListSep, strs)
    | s1::[]=> NONE
    | descr::txt::strs =>
      case descr of
      "TACTIC" => SOME (Tactic txt, strs)
      | "THMTACTIC" => SOME (ThmTactic txt, strs)
      | "THMLISTACTIC" => SOME (ThmListTactic txt, strs)
      | "TERMTACTIC" => SOME (TermTactic txt, strs)
      | "TERMLISTTACTIC" => SOME (TermListTactic txt, strs)
      | "QUOTTACTIC" => SOME (QuotTactic txt, strs)
      | "QUOTLISTTACTIC" => SOME (QuotListTactic txt, strs)
      | "TACTICAL" => SOME (Tactical txt, strs)
      | "THM" => SOME (Thm txt, strs)
      | "TERM" => SOME (Term txt, strs)
      | _ =>  NONE;

  fun parseThm (strs:string list) : (token * string list) option =
    lex strs;

  fun findThm (name:string) :thm option =
   case List.find (fn ((theory,theorem),stmt) => theorem = name) (DB.listDB()) of
   NONE => NONE
   | SOME (_, (th, _)) =>  SOME th;

  fun parse (sempreResp:string) :tactic =
    case lex (LassieUtilsLib.string_split sempreResp #" ") of
    NONE => raise NoParseException "Cannot parse input string"
    | SOME (nextTac, strs) =>
      case nextTac of
      Tactic str =>
        (case TacticMap.lookupTac str TacticMap.stdTree of
        NONE => raise NoParseException ("Tactic " ^ str ^ " not found\n")
        | SOME (Tac t) => t
        | SOME _ => raise NoParseException ("Tactic " ^ str ^ " not defined"))
      | ThmTactic str =>
        (case TacticMap.lookupTac str TacticMap.stdTree of
        NONE => raise NoParseException ("Theorem tactic " ^ str ^ " not found\n")
        | SOME (ThmTac thTac) =>
          (case parseThm strs of
          NONE => raise NoParseException ("No theorem argument provided")
          | SOME (Thm thStr, strs) =>
            (case findThm thStr of
            NONE => raise NoParseException ("Could not find theorem " ^thStr)
            | SOME th => thTac th)
          | SOME _ => raise NoParseException ("No theorem argument defined"))
        | SOME _ => raise NoParseException ("Theorem tactic " ^ str ^ " not defined"))
      | _ =>  raise NoParseException "";


end;
