structure arithTacticsLib =
struct
  open LassieLib;

  local open arithmeticTheory in end;
  val _ =
    let
    fun jargon () =
      let val _ =
        map (fn (a,b) => LassieLib.def a [b]) [
          ("simplify", "THMLISTTAC$fs [ ]"),
          ("simplify with [ADD_ASSOC]", "THMLISTTAC$fs [ ADD_ASSOC ]"),
          ("follows from [ADD_ASSOC]", "THMLISTTAC$metis_tac [ ADD_ASSOC ]"),
          ("rewrite [ADD_ASSOC]" ,"THMLISTTAC$rw [ADD_ASSOC]"),
          ("trivial using [ADD_ASSOC]",
          "TAC$all_tac TACCOMB$THEN ( THMLISTTAC$fs [ ADD_ASSOC ] TACCOMB$THEN TAC$NO_TAC) TACCOMB$ORELSE (THMLISTTAC$rw [ ADD_ASSOC ] TACCOMB$THEN TAC$NO_TAC) TACCOMB$ORELSE THMLISTTAC$metis_tac [ ADD_ASSOC ]"),
          ("perform an induction on 't'", "QUOTTAC$Induct_on ' t '"),
          ("perform a case split", "TAC$Cases"),
          ("perform a case split for 't'", "QUOTTAC$Cases_on ' t '"),
          ("Complete Induction on 't'", "QUOTTAC$completeInduct_on ' t '"),
          ("suppose not", "ASMTESTTAC$spose_not_then THMTAC$assume_tac"),
          ("show 'T' using (TAC$gen_tac)" ,"' T ' TERMCOMB$by TAC$gen_tac"),
          ("we further know 'T'", "' T ' TERMCOMB$by THMLISTTAC$rw [ ]"),
          ("we can derive 'T' from [ADD_ASSOC]", "' T ' TERMCOMB$by THMLISTTAC$rw [ ADD_ASSOC ]"),
          ("thus ADD_ASSOC for 'n'", "QUOTSPECTHMTAC$qspec_then ' n ' THMTAC$assume_tac ADD_ASSOC")
        ]
      in () end;
  in
    LassieLib.registerJargon "Arithmetic" (jargon)
  end

end;
