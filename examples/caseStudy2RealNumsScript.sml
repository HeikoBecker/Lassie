open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib lcsymtacs;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib;

val _ = new_theory "caseStudy2RealNums";

val rw_th = fn thm => once_rewrite_tac[thm];

QUse.use "realTactics.sml";

Theorem binom1:
  ! (a b:real). (a + b) pow 2 = a pow 2 + 2 * a * b + b pow 2
Proof
  LassieLib.nltac `
    introduce variables and assumptions.
  rewrite once [POW_2].
  rewrite once [REAL_LDISTRIB].
  rewrite once [REAL_RDISTRIB].
  rewrite with [<- REAL_ADD_ASSOC].
  simplify with [REAL_EQ_RADD].
  rewrite with [REAL_ADD_ASSOC].
  simplify with [REAL_EQ_LADD]. trivial.`
  (*
  rpt strip_tac
  \\ once_rewrite_tac [POW_2]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ once_rewrite_tac [REAL_RDISTRIB]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_RADD]
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_LADD]
  \\ `b * a = a * b` by (fs[REAL_MUL_COMM])
  \\ simp[REAL_DOUBLE, REAL_MUL_ASSOC] *)
QED

Theorem binom2:
  ! (a b:real). (a - b) pow 2 = a pow 2 - 2 * a * b + b pow 2
Proof
  LassieLib.nltac `
    introduce variables and assumptions.
    rewrite with [POW_2, real_sub, REAL_LDISTRIB, REAL_RDISTRIB].
    rewrite with [<- REAL_ADD_ASSOC].
    simplify with [REAL_EQ_RADD].
    rewrite once [REAL_NEG_MUL2].
    rewrite with [REAL_ADD_ASSOC].
    simplify with [REAL_EQ_LADD]. trivial.`
  (*
  rpt strip_tac
  \\ once_rewrite_tac [POW_2]
  \\ once_rewrite_tac [real_sub]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ once_rewrite_tac [REAL_RDISTRIB]
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ once_rewrite_tac [REAL_NEG_MUL2]
  \\ simp[REAL_EQ_RADD]
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ simp[REAL_EQ_LADD]
  \\ `-b * a = a * -b` by (fs[REAL_MUL_COMM])
  \\ simp[REAL_DOUBLE, GSYM REAL_NEG_LMUL, GSYM REAL_NEG_RMUL, REAL_MUL_ASSOC] *)
QED

val sum_of_cubes_def = Define `
  (sum_of_cubes 0 = 0:real) /\
  (sum_of_cubes (SUC n) = (&(SUC n)) pow 3 + sum_of_cubes n)`;

val sum_def = Define `
  (sum 0 = 0:real) /\
  (sum (SUC n) = (&(SUC n) + sum n))`

Theorem gaussian_sum:
  ! n. (sum n = (((&n):real) * (1 + &n)) / 2)
Proof
  Induct_on `n`
  \\ fs[sum_def, REAL_DIV_LZERO] (* note: no fs[sum_def] here! *)
  \\ pop_assum (fn thm=> once_rewrite_tac [GSYM thm] \\ assume_tac thm)
  \\ fs[MULT]
  \\ qspec_then `n` (fn thm => once_rewrite_tac [thm]) MULT_SYM
  \\ `SUC n + 1 = SUC (SUC n)`
      by (pop_assum kall_tac \\ Induct_on `n` \\ fs[])
  \\ qpat_x_assum `SUC n + 1 = _` (fn thm => once_rewrite_tac [thm])
  \\ `SUC (SUC n) * n = n + n + n * n`
      by (fs[MULT])
  \\ qpat_x_assum `SUC (SUC n) * _ = _` (fn thm => once_rewrite_tac [thm])
  \\ `n + n + n * n + 1 = SUC n + n * (n + 1)`
      by (once_rewrite_tac [ADD1] \\ once_rewrite_tac [LEFT_ADD_DISTRIB]
          \\ rewrite_tac [ADD_ASSOC, MULT_RIGHT_1] \\ fs[])
  \\ qpat_x_assum `n + n + _ + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ rewrite_tac [ADD_ASSOC]
  \\ `SUC n + SUC n = 2 * (SUC n)`
      by (fs[])
  \\ qpat_x_assum `SUC n + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM REAL_MUL, GSYM REAL_ADD]
  \\ rewrite_tac [GSYM REAL_DIV_ADD]
  \\ rewrite_tac [real_div]
  \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
  \\ fs[REAL_MUL_RINV]
  \\ fs[REAL_MUL_ASSOC]
QED

Theorem pow_3:
  n pow 3 = n * n * n
Proof
  `3 = SUC 2` by (fs[])
  \\ pop_assum rw_th
  \\ fs[pow, POW_2] \\ REAL_ASM_ARITH_TAC
QED

(**
  The sum of cubed numbers up to n is the squared sum
**)
Theorem sum_of_cubes_is_squared_sum:
  ! n. sum_of_cubes n = (sum n) pow 2
Proof
  LassieLib.nltac `
    induction on 'n'.
    simplify with [sum_of_cubes_def, sum_def, POW_2].
    rewrite with [REAL_LDISTRIB, REAL_RDISTRIB, REAL_ADD_ASSOC].
    it suffices to show '&SUC n pow 3 = &SUC n * &SUC n + &SUC n * sum n + sum n * &SUC n'
      because (simplify with [REAL_EQ_LADD]).
    we know '& SUC n * sum n + sum n * &SUC n = 2 * (sum n * & SUC n)'.
    rewrite once [<- REAL_ADD_ASSOC].
    rewrite last assumption.
    simplify with [pow_3].
    rewrite with [gaussian_sum, real_div, REAL_MUL_ASSOC].
    we know '2 * &n * (1 + &n) * inv 2 = 2 * inv 2 * & n * (1 + &n)'.
    rewrite last assumption.
    simplify with [REAL_MUL_RINV].
    we show 'n + 1 = SUC n' using (simplify with []).
    rewrite last assumption. simplify with [].
    we show '3 = SUC (SUC (SUC 0)) and 2 = (SUC (SUC 0))' using (simplify with []).
    rewrite last assumption. rewrite last assumption.
    rewrite with [EXP].
    we show 'SUC n = n + 1' using (simplify with []).
    rewrite last assumption.
    rewrite with [MULT_RIGHT_1, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_LEFT_1].`
QED

(*
    \\ fs[pow_3]
    \\ once_rewrite_tac [REAL_ADD_ASSOC]
    \\ pop_assum rw_th
    \\ once_rewrite_tac [gaussian_sum]
    \\ once_rewrite_tac [real_div]
    \\ rewrite_tac [REAL_MUL_ASSOC]
    \\ `2 * &n * (1 + &n) * inv 2 = 2 * inv 2 * & n * (1 + &n)` by (REAL_ASM_ARITH_TAC)
    \\ pop_assum rw_th
    \\ simp [REAL_MUL_RINV]
    \\ `(SUC n) ** 3 = (SUC n)**2 + (SUC n)**2 * n`
        by (`3= SUC (SUC (SUC 0))` by (fs[]) \\ pop_assum rw_th
            \\ `2 = SUC(SUC 0)` by (fs[]) \\ pop_assum rw_th
            \\ rewrite_tac[EXP]
            \\ `SUC n = n + 1` by (fs[])
            \\ pop_assum rw_th
            \\ rewrite_tac [MULT_RIGHT_1, RIGHT_ADD_DISTRIB, LEFT_ADD_DISTRIB, MULT_LEFT_1]
            \\ fs[])
    \\ pop_assum rw_th
    \\ `n + 1 = SUC n` by (fs[])
    \\ pop_assum rw_th \\ fs[]
QED
*)
(*
Theorem binom3:
  ! (a b:real). (a + b) * (a - b) = a pow 2 - b pow 2
Proof
  rpt strip_tac
  \\ rewrite_tac [POW_2]
  \\ once_rewrite_tac [real_sub]
  \\ once_rewrite_tac [REAL_LDISTRIB]
  \\ once_rewrite_tac [REAL_RDISTRIB]
  \\ `a * - b = - b * a` by (fs[REAL_MUL_COMM])
  \\ rewrite_tac [GSYM REAL_ADD_ASSOC]
  \\ simp [REAL_EQ_LADD]
  \\ rewrite_tac [REAL_NEG_RMUL]
  \\ qspec_then `b * -b` assume_tac REAL_ADD_LID
  \\ pop_assum (fn thm => once_rewrite_tac [GSYM thm])
  \\ rewrite_tac [REAL_ADD_ASSOC]
  \\ simp [REAL_EQ_RADD, REAL_ADD_RID]
  \\ rewrite_tac [GSYM REAL_NEG_LMUL]
  \\ rewrite_tac [GSYM real_sub]
  \\ MATCH_ACCEPT_TAC REAL_SUB_REFL
QED

(*
  Gaussian formula
*)
val sum_def = Define `
  (sum 0 = 0:real) /\
  (sum (SUC n) = (&(SUC n) + sum n))`

Theorem gaussian_sum:
  ! n. (sum n = (((&n):real) * (1 + &n)) / 2)
Proof
  Induct_on `n`
  \\ fs[sum_def, REAL_DIV_LZERO] (* note: no fs[sum_def] here! *)
  \\ pop_assum (fn thm=> once_rewrite_tac [GSYM thm] \\ assume_tac thm)
  \\ fs[MULT]
  \\ qspec_then `n` (fn thm => once_rewrite_tac [thm]) MULT_SYM
  \\ `SUC n + 1 = SUC (SUC n)`
      by (pop_assum kall_tac \\ Induct_on `n` \\ fs[])
  \\ qpat_x_assum `SUC n + 1 = _` (fn thm => once_rewrite_tac [thm])
  \\ `SUC (SUC n) * n = n + n + n * n`
      by (fs[MULT])
  \\ qpat_x_assum `SUC (SUC n) * _ = _` (fn thm => once_rewrite_tac [thm])
  \\ `n + n + n * n + 1 = SUC n + n * (n + 1)`
      by (once_rewrite_tac [ADD1] \\ once_rewrite_tac [LEFT_ADD_DISTRIB]
          \\ rewrite_tac [ADD_ASSOC, MULT_RIGHT_1] \\ fs[])
  \\ qpat_x_assum `n + n + _ + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ rewrite_tac [ADD_ASSOC]
  \\ `SUC n + SUC n = 2 * (SUC n)`
      by (fs[])
  \\ qpat_x_assum `SUC n + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ once_rewrite_tac [MULT_COMM]
  \\ rewrite_tac [GSYM REAL_MUL, GSYM REAL_ADD]
  \\ rewrite_tac [GSYM REAL_DIV_ADD]
  \\ rewrite_tac [real_div]
  \\ rewrite_tac [GSYM REAL_MUL_ASSOC]
  \\ fs[REAL_MUL_RINV]
  \\ fs[REAL_MUL_ASSOC]
QED

(*
  The sum of all n uneven numbers is n^2
*)
val square_number_def = Define `
  (square_number (0:num) = 1:real) /\
  (square_number (SUC n) = ((2:real) * (&(SUC n)) + &1) + square_number n)`

Theorem square_number_is_square:
  ! n. square_number n = (&n+1) * (&n+1)
Proof
  Induct_on `n`
  >- (fs[Once square_number_def])
  \\ simp[Once square_number_def]
  \\ once_rewrite_tac [SUM_SQUARED]
  \\ once_rewrite_tac [MULT_RIGHT_1]
  \\ once_rewrite_tac [ADD1]
  \\ once_rewrite_tac [SUM_SQUARED]
  \\ once_rewrite_tac [MULT_RIGHT_1]
  \\ fs[]
QED

*)

val _ = export_theory();
