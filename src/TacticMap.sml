(**
  Structure: TacticMap

  Uses the association map implemented in AssocMap.sml that maps strings to
  tactic "closures".
  Lassie uses it internally to map the SEMPRE returned intermediate language
  into concrete HOL4 tactics code
**)
structure TacticMap =
struct

  open Lib Tactic Tactical bossLib;

  datatype tacticClos =
    Tac of tactic
    | TacComb of (tactic -> tactic)
    | TermTac of (term -> tactic)
    | QuotTac of (term quotation -> tactic)
    | ThmTac of (thm -> tactic)
    | TermListTac of (term list -> tactic)
    | ThmListTac of (thm list -> tactic);

  fun empty (_:unit) = AssocMap.Leaf;

  fun insertTac (s:string) (t:tacticClos) (tr:(string,tacticClos) AssocMap.tree) =
    AssocMap.append s t tr String.compare;

  fun lookupTac (s:string) (tr:(string,tacticClos) AssocMap.tree) =
    AssocMap.lookup s tr String.compare;

  (* Define a standard Lassie Tree that has rudimentary support for the most
     common tactics *)
  val stdTree =
    insertTac "cheat" (Tac cheat) (empty ())
      |> insertTac "strip_tac" (Tac strip_tac)
      |> insertTac "fs" (ThmListTac fs)
      |> insertTac "rpt" (TacComb rpt)
      |> insertTac "imp_res_tac" (ThmTac imp_res_tac)
      |> insertTac "Cases" (Tac Cases)
      |> insertTac "Cases_on" (QuotTac Cases_on)
      |> insertTac "Induct" (Tac Induct)
      |> insertTac "Induct_on" (QuotTac Induct_on);

end;
