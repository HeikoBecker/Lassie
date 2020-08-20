
open BasicProvers Defn HolKernel Parse Tactic
     arithmeticTheory boolLib boolSimps bossLib;
open LassieLib arithTacticsLib realTacticsLib logicTacticsLib;

val _ = new_theory "gauss";

val _ = LassieLib.loadJargon "Arithmetic";
val _ = LassieLib.loadJargon "Logic";

Definition sum_def:
  sum (0:num) = 0 ∧
  sum n = n + sum (n-1)
End

Theorem gaussian_sum:
  ∀ n.
    sum n = (n * (n + 1)) DIV 2
Proof
  nltac ‘
   Induction on 'n'.
   Goal 'sum 0 = 0 * (0 + 1) DIV 2'.
     simplify.
   End.
   Goal 'sum (SUC n) = SUC n * (SUC n + 1) DIV 2'.
     use [sum_def, GSYM ADD_DIV_ADD_DIV] to simplify.
     '2 * SUC n + n * (n + 1) = SUC n * (SUC n + 1)' suffices to show the goal.
     show 'SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)' using (simplify with [MULT_CLAUSES]).
     simplify.
     show 'n * (n + 1) = SUC n * n' using (trivial using [MULT_CLAUSES, MULT_SYM]).
     show '2 * SUC n = SUC n + SUC n' using (trivial using []).
     show 'n * (SUC n + 1) = SUC n * n + n' using (trivial using []).
     rewrite assumptions. simplify.
   End.’
  (* Induct_on ‘n’
  >- simp[sum_def]
  >- fs[sum_def, GSYM ADD_DIV_ADD_DIV]
  \\ ‘2 * SUC n + n * (n + 1) = SUC n * (SUC n + 1)’ suffices_by (fs[])
  \\ ‘SUC n * (SUC n + 1) = (SUC n + 1) + n * (SUC n + 1)’ by fs[MULT_CLAUSES]
  \\ simp[]
  \\ ‘n * (n + 1) = SUC n * n’ by metis_tac[MULT_CLAUSES, MULT_SYM]
  \\ simp[] *)
QED

val _ = export_theory();
