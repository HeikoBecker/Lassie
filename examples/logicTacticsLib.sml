structure logicTacticsLib =
struct

  open LassieLib;

  local open realTheory in end;
  val _ =
    let
    fun jargon () =
      let
        val _ =
        map (fn (a,b) => (def a [b])) [
          (* Case splitting *)
          (`case split`, `(TACL$rpt TAC$conj_tac TACCOMB$ORELSE TAC$EQ_TAC) TACCOMB$ORELSE TAC$Cases`),
          (`case split for 's'`,`QUOTTAC$Cases_on 's'`),
          (`perform a case split`,`case split`),
          (`specialize for 'T'`,`ASMTESTTAC$first_x_assum QUOTSPECTHMTAC$qspec_then ' T ' THMTAC$assume_tac`),
          (`assume the contrary`,`TAC$CCONTR_TAC`),
          (* Automation a la textbook *)
          (`trivial`,`THMLISTTAC$metis_tac [ ]`),
          (`trivial using [CONJ_COMM]`, `THMLISTTAC$metis_tac [ CONJ_COMM ]`),
          (`follows trivially`,`THMLISTTAC$fs [ ]`),
          (`follows from [ADD_COMM]`, `THMLISTTAC$fs [ ADD_COMM ]`),
          (* Simplification *)
          (`simplify`, `THMLISTTAC$fs [ ]`),
          (`simplify with [CONJ_COMM]`, `THMLISTTAC$fs [ CONJ_COMM ]`),
          (`simplify conclusion`, `THMLISTTAC$simp [ ]`),
          (`simplify conclusion with [CONJ_COMM]`, `THMLISTTAC$simp [ CONJ_COMM ]`),
          (* lc aliases *)
          (`try TAC$gen_tac`, `TACL$TRY TAC$gen_tac`),
          (* `try solving with [CONJ_COMM]` [`TRY simp [CONJ_COMM]`]; *)
          (* Textbook style tactics for existentials, modus ponens, ... *)
          (`choose 'e'`, `QUOTTAC$qexists_tac ' e '`),
          (`use transitivity for 'x'`, `THMTAC$irule REAL_LE_TRANS TACCOMB$THEN QUOTTAC$qexists_tac ' x '`),
          (`use REAL_LE_TRANS`, `THMTAC$irule REAL_LE_TRANS`),
          (`resolve with REAL_NEG_INV`, `THMTAC$imp_res_tac REAL_NEG_INV`),
          (`induction on 'n'`, `QUOTTAC$Induct_on ' n '`),
          (* rewriting *)
          (`rewrite once [REAL_INV_1OVER]`, `THMLISTTAC$once_rewrite_tac [ REAL_INV_1OVER ]`),
          (`rewrite once [<- REAL_INV_1OVER]`, `THMLISTTAC$once_rewrite_tac [ GSYM REAL_INV_1OVER ]`),
          (`rewrite with [REAL_INV_1OVER]`, `THMLISTTAC$rewrite_tac [REAL_INV_1OVER]`),
          (`rewrite with [<- REAL_INV_1OVER]`, `THMLISTTAC$rewrite_tac [GSYM REAL_INV_1OVER]`),
          (`rewrite assumptions`, `THMLISTTAC$asm_rewrite_tac []`),
          (`rewrite assumptions and [ADD_ASSOC] `, `THMLISTTAC$asm_rewrite_tac [ADD_ASSOC]`),
          (* subgoals *)
          (`we show first 'T'`, `QUOTTAC$sg 'T'`),
          (`we show next 'T'`, `we show first 'T'`),
          (`we show 'T' using (TAC$gen_tac)`, `'T' TERMCOMB$by TAC$gen_tac`),
          (`we know 'T'`, `'T' TERMCOMB$by (THMLISTTAC$fs [ ])`),
          (`thus 'T'`, `we know 'T'`),
          (`'T' using (TAC$cheat)`, `'T' TERMCOMB$by (TAC$cheat)`),
          (`it suffices to show 'T' because (TAC$gen_tac)`, `'T' TERMCOMB$suffices_by (TAC$gen_tac)`)
        ]
      in () end;
  in
    LassieLib.registerJargon "Logic" (jargon)
  end

end;
