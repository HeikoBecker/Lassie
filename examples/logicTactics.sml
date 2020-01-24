(* Case splitting *)
val _ = LassieLib.def `case split` [`all_tac THEN (rpt conj_tac ORELSE EQ_TAC) ORELSE Cases`];
val _ = LassieLib.def `case split for 's'` [`Cases_on 's'`];
val _ = LassieLib.def `perform a case split` [`case split`];
val _ = LassieLib.def `specialize for 'T'` [`first_x_assum qspec_then 'T' assume_tac`];
val _ = LassieLib.def `assume the contrary` [`CCONTR_TAC`];

(* Automation a la textbook *)
val _ = LassieLib.def `trivial` [`metis_tac []`];
val _ = LassieLib.def `trivial using [CONJ_COMM]`
                      [`metis_tac [CONJ_COMM]`];
val _ = LassieLib.def `follows trivially` [`fs []`];
val _ = LassieLib.def `follows from [ADD_COMM]` [`fs[ADD_COMM]`];

(* Simplification *)
val _ = LassieLib.def `simplify` [`fs []`];
val _ = LassieLib.def `simplify with [CONJ_COMM]` [`fs [CONJ_COMM]`];

(* lc aliases *)
val _ = LassieLib.def `try gen_tac` [`TRY gen_tac`];
(* val _ = LassieLib.def `try solving with [CONJ_COMM]` [`TRY simp [CONJ_COMM]`]; *)

(* Textbook style tactics for existentials, modus ponens, ... *)
val _ = LassieLib.def `choose 'e'` [`qexists_tac 'e'`];
val _ = LassieLib.def `use transitivity for 'x'` [`irule REAL_LE_TRANS THEN qexists_tac 'x'`];
val _ = LassieLib.def `use REAL_LE_TRANS` [`irule REAL_LE_TRANS`];
val _ = LassieLib.def `resolve with REAL_NEG_INV` [`imp_res_tac REAL_NEG_INV`];
val _ = LassieLib.def `induction on 'n'` [`Induct_on 'n'`];

(* rewriting *)
val _ = LassieLib.def `rewrite once [REAL_INV_1OVER]` [`once_rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite once [<- REAL_INV_1OVER]` [`once_rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [REAL_INV_1OVER]` [`rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [<- REAL_INV_1OVER]` [`rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite assumptions` [`asm_rewrite_tac []`];
val _ = LassieLib.def `rewrite assumptions and [ADD_ASSOC] ` [`asm_rewrite_tac [ADD_ASSOC]`];

(* subgoals *)
val _ = LassieLib.def `we show first 'T'` [`sg 'T'`];
val _ = LassieLib.def `we show next 'T'` [`we show first 'T'`];
val _ = LassieLib.def `we show 'T' using (gen_tac)` [`'T' by (gen_tac)`];
val _ = LassieLib.def `we know 'T'` [`'T' by (fs[])`];
val _ = LassieLib.def `thus 'T'` [`we know 'T'`];
val _ = LassieLib.def `'T' using (fs[])` [`'T' by ( fs[] )`];
val _ = LassieLib.def `it suffices to show 'T' because (gen_tac)` [`'T' suffices_by (gen_tac)`];
