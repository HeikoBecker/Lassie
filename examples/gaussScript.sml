open BasicProvers Defn HolKernel Parse Tactic
     arithmeticTheory boolLib boolSimps bossLib;
open LassieLib arithTacticsLib;

val _ = new_theory "gauss";

val _ = LassieLib.loadJargon "Arithmetic";

Definition sum_def:
  sum 0 = 0 ∧
  sum n = n + sum (n-1)
End

Theorem gaussian_sum:
  ∀ n.
    sum n = (n * (n + 1)) DIV 2
Proof
  nltac ‘
   Induction on 'n'. simplify.
   simplify with [GSYM ADD_DIV_ADD_DIV, GSYM DIV2_def].
   it suffices to show that the arguments are equal.
   show 'SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)' using (simplify with [MULT_CLAUSES]).
   simplify.
   show 'n * (n + 1) = SUC n * n' using (trivial using [MULT_CLAUSES, MULT_SYM]).
   simplify.’
  (* Induct_on ‘n’
  \\ simp[sum_def]
  \\ simp[GSYM ADD_DIV_ADD_DIV, GSYM DIV2_def]
  \\ AP_TERM_TAC
  \\ ‘SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)’ by fs[MULT_CLAUSES]
  \\ simp[]
  \\ ‘n * (n + 1) = SUC n * n’ by metis_tac[MULT_CLAUSES, MULT_SYM]
  \\ simp[] *)
QED

val _ = export_theory();
