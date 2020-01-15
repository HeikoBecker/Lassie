open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib lcsymtacs;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib;

val _ = new_theory "tactics";

fun add_Lassie_definition (t:'a frag list) (tDef:'a frag list list) :unit =
  let
    val _ = LassieLib.def t tDef;
    val tStr = case t of [QUOTE s] => LassieUtilsLib.preprocess s | _ => raise LassieException ""
    val tDefStr = map (fn tStr => case tStr of [QUOTE s] => " `" ^ LassieUtilsLib.preprocess s ^ "` " | _ => raise LassieException "") tDef
    val tDefQuoteString = List.foldl  (fn (s, acc) => acc ^ ", " ^ s) (hd tDefStr) (tl tDefStr)
    val add_text = "val _ = LassieLib.def `" ^ tStr ^ "` [" ^ tDefQuoteString ^ "];"
  in
    (print add_text; adjoin_to_theory { sig_ps = NONE, struct_ps = SOME (fn _ => PP.add_string add_text)})
  end;

val _ = add_Lassie_definition `introduce variables` [`lcsymtacs.gen_tac`];
val _ = add_Lassie_definition `introduce variables and assumptions` [`rpt lcsymtacs.strip_tac`];

val _ = export_theory();

(*
      val add_t = "val _ = FloverTactics.eval_funs :=``" ^ term_to_string t ^ "`` :: (!FloverTactics.eval_funs);"
      val _ = adjoin_to_theory
                  { sig_ps = NONE,
                    struct_ps =
                    SOME (fn _ => PP.add_string add_t)};
  in
  eval_funs := t :: (!eval_funs)
  end;

val _ = LassieLib.addCustomTactic "REAL_ASM_ARITH_TAC";
val _ = LassieLib.addCustomTactic "impl_tac";
val _ = LassieLib.addCustomTactic "cheat";
val _ = LassieLib.addCustomTactic "EQ_TAC";

val _ = LassieLib.def `introduce variables` [`rpt gen_tac`];
val _ = LassieLib.def `introduce variables and assumptions` [`rpt strip_tac`];
val _ = LassieLib.def `case split for 's'` [`Cases_on 's'`];
val _ = LassieLib.def `case split` [`(rpt conj_tac ORELSE EQ_TAC) ORELSE Cases`];
val _ = LassieLib.def `trivial using [CONJ_COMM]` [`metis_tac [CONJ_COMM]`];
val _ = LassieLib.def `simplify with [CONJ_COMM]` [`simp [CONJ_COMM]`];
val _ = LassieLib.def `try solving with [CONJ_COMM]` [`TRY simp [CONJ_COMM]`];
val _ = LassieLib.def `choose 'e'` [`qexists_tac 'e'`];
val _ = LassieLib.def `use transitivity for 'x'` [`irule REAL_LE_TRANS THEN qexists_tac 'x'`];
val _ = LassieLib.def `use REAL_LE_TRANS` [`irule REAL_LE_TRANS`];
val _ = LassieLib.def `perform a case split` [`rpt conj_tac`];
val _ = LassieLib.def `we show first 'T'` [`sg 'T'`];
val _ = LassieLib.def `we show 'T' using (gen_tac)` [`'T' by (gen_tac)`];
val _ = LassieLib.def `introduce assumptions` [`rpt strip_tac`];
val _ = LassieLib.def `rewrite once [REAL_INV_1OVER]` [`once_rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite once [<- REAL_INV_1OVER]` [`once_rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [REAL_INV_1OVER]` [`rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [<- REAL_INV_1OVER]` [`rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `we show next 'T'` [`we show first 'T'`];
val _ = LassieLib.def `'T' using (fs[])` [`'T' by ( fs[] )`];
val _ = LassieLib.def `we know 'T'` [`'T' by (REAL_ASM_ARITH_TAC)`];
val _ = LassieLib.def `thus 'T'` [`we know 'T'`];
val _ = LassieLib.def `resolve with REAL_NEG_INV` [`imp_res_tac REAL_NEG_INV`];
val _ = LassieLib.def `follows from [CONJ_COMM]` [`asm_rewrite_tac [CONJ_COMM] THEN fs[CONJ_COMM]`];
val _ = LassieLib.def `gen_tac . gen_tac` [`gen_tac THEN gen_tac`];
val _ = LassieLib.def `gen_tac .` [`gen_tac THEN all_tac`];

val _ = export_theory();
*)
