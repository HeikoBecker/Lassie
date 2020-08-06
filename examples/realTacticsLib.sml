structure realTacticsLib =
struct

  open LassieLib;

  local open realTheory RealArith in end;
  val _ =
    let
      fun jargon () =
        let val _ = LassieLib.addCustomTactic RealArith.REAL_ASM_ARITH_TAC "REAL_ASM_ARITH_TAC"
        val _ = LassieLib.addCustomTactic DECIDE_TAC "DECIDE_TAC"
        val _ = LassieLib.addCustomTactic impl_tac "impl_tac"
        val _ = LassieLib.addCustomTactic EQ_TAC "EQ_TAC"
        val rw_th = fn thm => once_rewrite_tac[thm];
        val _ = LassieLib.addCustomThmTactic rw_th "rw_th";
        val _ =
          map (fn (a,b) => (def a [b])) [
          (* intro tactics *)
            (`introduce variables`, `TACL$rpt TAC$gen_tac`),
            (`introduce assumptions`, `TACL$rpt TAC$strip_tac`),
            (`introduce variables and assumptions`, `TACL$rpt TAC$strip_tac`),
          (* Custom tactic *)
            (`rewrite last assumption`, `ASMTESTTAC$pop_assum THMTAC$rw_th`),
            (‘trivial’, ‘TAC$REAL_ASM_ARITH_TAC’),
            (`we know 'T'`, `'T' TERMCOMB$by (TAC$REAL_ASM_ARITH_TAC)`)
          ]
        in () end
    in
      LassieLib.registerJargon "Reals" jargon
    end;
end;
