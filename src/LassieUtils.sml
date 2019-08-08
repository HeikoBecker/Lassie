structure LassieUtils =
struct

(*********************************)
(*            Utils              *)
(*********************************)
fun sleep t =
  let
    val wakeUp = Time.+ (Time.now(), Time.fromReal(t))
    fun wait () = if Time.> (Time.now(), wakeUp) then () else wait ()
  in
    wait ()
  end;

fun flushStream instream =
  case TextIO.canInput(instream, 5000) of
    NONE -> ()
    | SOME n =>
      if n = 0 then ()
      else (TextIO.input(instream); flushStream(instream));

(* some string editing to remove long package names esp. in call formulas *)
fun simplifyAbsoluteNames str =
  let
    fun isSep s = mem s [#" ", #"(", #")", #"\""]
    fun append s l =
      case l of
        [] => [s]
        | hd::tl => (s ^ hd)::tl
    val tokens =
      List.foldl
        (fn (c,l) => if isSep c then ""::(String.str c)::l else append (String.str c) l)
        []
        (List.rev (String.explode str))
    fun isNotEmpty s = not (s = "")
    fun getLocalName s = List.hd (List.rev (String.tokens (fn c => c = #".") s))
  in
    String.concat (map getLocalName (List.filter isNotEmpty tokens))
  end;

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
  end;

(* normalize a string representing an HOL4 expression for viewing *)
fun normalize str =
  let
  (* space out function applications through direct parens e.g. map(f)lst *)
    fun injectSpc sl =
      case sl of
        s1::s2::tl =>
          if (s2 = "(" andalso not (mem s1 ["("," ",")"])) orelse
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
          else if c = "("
          then
            let (* inductive case *)
              val (left', p', right') = rmParens [] false tail (* rec *)
              (* if nothing on left do not parenthesize, applications are left associative *)
              val left' = if left = [] then left' else paren left' p'
              val left' = if left' = [] then ["(",")"] else left' (* unit *)
            in
              rmParens (left @ left') p right'
            end (* continue *)
          else rmParens (left@[c]) (p orelse c = " ") tail
    val (retStr, _, _) =
      rmParens [] false ( str |> String.explode
                              |> (map String.str)
                              |> injectSpc )
  in
    String.concat retStr
  end;

exception VariableUndefined of string;

  fun getOSVar name =
    case OS.Process.getEnv name of
    | NONE => raise VariableUndefined "Variable " ^ s ^ " not defined in environment"
    | SOME s => s;

end