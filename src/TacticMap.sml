(**
  Structure: TacticMap

  Uses the association map implemented in AssocMap.sml that maps strings to
  tactic "closures".
  Lassie uses it internally to map the SEMPRE returned intermediate language
  into concrete HOL4 tactics code
**)
structure TacticMap =
struct

  open Lib Tactic Tactical Rewrite bossLib mesonLib;

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

  fun insertThmListTac (s:string) (t:thm list -> tactic) =
    insertTac s (ThmListTac t);

  (* Define a standard Lassie Tree that has rudimentary support for the most
     common tactics *)
  val stdTree =
    insertTac "cheat" (Tac cheat) (empty ())
      |> insertTac "strip_tac" (Tac strip_tac)
      |> insertTac "gen_tac" (Tac gen_tac)
      |> insertTac "Cases" (Tac Cases)
      |> insertTac "Induct" (Tac Induct)
      |> insertThmListTac "asm_rewrite_tac" asm_rewrite_tac
      |> insertThmListTac "rewrite_tac" rewrite_tac
      |> insertThmListTac "once_rewrite_tac" once_rewrite_tac
      |> insertThmListTac "once_asm_rewrite_tac" once_asm_rewrite_tac
      |> insertThmListTac "simp" simp
      |> insertThmListTac "fs" fs
      |> insertThmListTac "rfs" rfs
      |> insertThmListTac "rw" rw
      |> insertThmListTac "metis_tac" metis_tac
      |> insertThmListTac "MESON_TAC" MESON_TAC
      |> insertTac "rpt" (TacComb rpt)
      |> insertTac "imp_res_tac" (ThmTac imp_res_tac)
      |> insertTac "Cases_on" (QuotTac Cases_on)
      |> insertTac "Induct_on" (QuotTac Induct_on);

end;
