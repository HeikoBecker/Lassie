val _ = LassieLib.def `follows from [ADD_ASSOC]` [`metis_tac [ADD_ASSOC]`];
val _ = LassieLib.def `trivial using [ADD_ASSOC]`
          [`all_tac THEN (fs [ADD_ASSOC] THEN NO_TAC) ORELSE (rw [ADD_ASSOC] THEN NO_TAC) ORELSE metis_tac [ADD_ASSOC]`];
val _ = LassieLib.def `rewrite [ADD_ASSOC]` [`rw [ADD_ASSOC]`];
val _ = LassieLib.def `perform an induction on 't'` [`Induct_on 't'`];
val _ = LassieLib.def `perform a case split` [`Cases`];
val _ = LassieLib.def `perform a case split for 't'` [`Cases_on 't'`];
val _ = LassieLib.def `Complete Induction on 't'` [`completeInduct_on 't'`];
val _ = LassieLib.def `show 'T' using (gen_tac)` [`'T' by (gen_tac)`];
val _ = LassieLib.def `we further know 'T'` [`'T' by (rw[])`];
val _ = LassieLib.def `we can derive 'T' from [ADD_ASSOC]` [`'T' by (rw[ADD_ASSOC])`];
val _ = LassieLib.def `suppose not` [`spose_not_then assume_tac`]
val _ = LassieLib.def `thus ADD_ASSOC for 'n'` [`qspec_then 'n' assume_tac ADD_ASSOC`];
val _ = LassieLib.def `simplify` [`fs[]`];
val _ = LassieLib.def `simplify with [ADD_ASSOC]` [`fs [ADD_ASSOC]`];
