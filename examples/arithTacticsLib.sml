structure arithTacticsLib =
struct
  open LassieLib;

  local open arithmeticTheory in end;
  fun fs_all g = let val thms = map (fn (a,th) => th) (DB.theorems "-") in fs thms g end;
  val _ =
    let
    fun jargon () =
      let
        val _ = LassieLib.addCustomTactic fs_all "fs_all";
        val _ =
        map (fn (a,b) => (LassieLib.def a [b])) [
          (`simplify`, `TAC$fs_all`),
          (`simplify with [ADD_ASSOC]`, `THMLISTTAC$fs [ ADD_ASSOC ]`),
          (`use [ADD_ASSOC] to simplify`, `THMLISTTAC$fs [ ADD_ASSOC ]`),
          (`follows from [ADD_ASSOC]`, `THMLISTTAC$metis_tac [ ADD_ASSOC ]`),
          (`rewrite [ADD_ASSOC]` ,`THMLISTTAC$rw [ADD_ASSOC]`),
          (`trivial using [ADD_ASSOC]`,
          `TAC$all_tac TACCOMB$THEN ( THMLISTTAC$fs [ ADD_ASSOC ] TACCOMB$THEN TAC$NO_TAC) TACCOMB$ORELSE (THMLISTTAC$rw [ ADD_ASSOC ] TACCOMB$THEN TAC$NO_TAC) TACCOMB$ORELSE THMLISTTAC$metis_tac [ ADD_ASSOC ]`),
          (‘trivial’, ‘trivial using []’),
          (`perform an induction on 't'`, `QUOTTAC$Induct_on ' t '`),
          (`Induction on 't'`, `QUOTTAC$Induct_on ' t '`),
          (`perform a case split`, `TAC$Cases`),
          (`perform a case split for 't'`, `QUOTTAC$Cases_on ' t '`),
          (`Complete Induction on 't'`, `QUOTTAC$completeInduct_on ' t '`),
          (`suppose not`, `ASMTESTTAC$spose_not_then THMTAC$assume_tac`),
          (`show 'T' using (TAC$gen_tac)` ,`' T ' TERMCOMB$by TAC$gen_tac`),
          (`we further know 'T'`, `' T ' TERMCOMB$by THMLISTTAC$rw [ ]`),
          (`we can derive 'T' from [ADD_ASSOC]`, `' T ' TERMCOMB$by THMLISTTAC$rw [ ADD_ASSOC ]`),
          (`thus ADD_ASSOC for 'n'`, `QUOTSPECTHMTAC$qspec_then ' n ' THMTAC$assume_tac ADD_ASSOC`),
          (‘'T' suffices to show the goal’, ‘'T' TERMCOMB$suffices_by (THMLISTTAC$fs[])’),
          (`it suffices to show that the arguments are equal`, `TAC$AP_TERM_TAC`),
          (`it suffices to show that the functions are equal`, `TAC$AP_THM_TAC`)
        ]
      in () end;
  in
    LassieLib.registerJargon "Arithmetic" (jargon)
  end

end;
