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
          (`simplify`, `fs_all`),
          (`simplify with [ADD_ASSOC]`, `fs [ ADD_ASSOC ]`),
          (`use [ADD_ASSOC] to simplify`, `fs [ ADD_ASSOC ]`),
          (`follows from [ADD_ASSOC]`, `metis_tac [ ADD_ASSOC ]`),
          (`rewrite [ADD_ASSOC]` ,`rw [ADD_ASSOC]`),
          (`trivial using [ADD_ASSOC]`,
          `all_tac THEN ( fs [ ADD_ASSOC ] THEN NO_TAC) ORELSE (rw [ ADD_ASSOC ] THEN NO_TAC) ORELSE metis_tac [ ADD_ASSOC ]`),
          (‘trivial’, ‘trivial using []’),
          (`perform an induction on 't'`, `Induct_on ' t '`),
          (`Induction on 't'`, `Induct_on ' t '`),
          (`perform a case split`, `Cases`),
          (`perform a case split for 't'`, `Cases_on ' t '`),
          (`Complete Induction on 't'`, `completeInduct_on ' t '`),
          (`suppose not`, `spose_not_then assume_tac`),
          (`show 'T' using (gen_tac)` ,`' T ' by gen_tac`),
          (`we further know 'T'`, `' T ' by rw [ ]`),
          (`we can derive 'T' from [ADD_ASSOC]`, `' T ' by rw [ ADD_ASSOC ]`),
          (`thus ADD_ASSOC for 'n'`, `qspec_then ' n ' assume_tac ADD_ASSOC`),
          (‘'T' suffices to show the goal’, ‘'T' suffices_by (fs[])’),
          (`it suffices to show that the arguments are equal`, `AP_TERM_TAC`),
          (`it suffices to show that the functions are equal`, `AP_THM_TAC`)
        ]
      in () end;
  in
    LassieLib.registerJargon "Arithmetic" (jargon)
  end

end;
