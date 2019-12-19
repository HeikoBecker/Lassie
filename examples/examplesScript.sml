open bossLib realTheory arithmeticTheory RealArith;
open LassieLib;

val _ = new_theory "examples";

fun rw thm = rewrite_tac [thm]
val use_last_assum = pop_assum rw

fun impl_subgoal_tac th =
    let
	val hyp_to_prove = lhand (concl th)
    in
	SUBGOAL_THEN hyp_to_prove (fn thm => assume_tac (MP th thm))
    end;

Theorem binom1:
  ! (a b:real). (a + b) pow 2 = a pow 2 + 2 * a * b + b pow 2
Proof
remove quantifier

rpt strip_tac
\\ fs [POW_2]
\\ fs [REAL_RDISTRIB, REAL_LDISTRIB, REAL_ADD_ASSOC]
\\ fs [GSYM REAL_DOUBLE]
\\ fs [REAL_RDISTRIB, REAL_ADD_ASSOC]
\\ fs [REAL_MUL_SYM]
QED

Theorem binom2:
  ! (a b:real). (a - b) pow 2 = a pow 2 - 2 * a * b + b pow 2
Proof
rpt strip_tac
\\ fs [POW_2]
\\ fs [REAL_SUB_RDISTRIB, REAL_SUB_LDISTRIB]
\\ fs [GSYM REAL_DOUBLE]
\\ fs [real_sub]
\\ fs [REAL_NEG_ADD, REAL_NEG_LMUL]
\\ fs [REAL_RDISTRIB]
\\ fs [REAL_ADD_ASSOC]
\\ fs [GSYM REAL_NEG_LMUL]
\\ fs [REAL_MUL_SYM]
QED

Theorem binom3:
  ! (a b:real). (a + b) * (a - b) = a pow 2 - b pow 2
Proof
rpt strip_tac
\\ fs [POW_2]
\\ fs [REAL_RDISTRIB, REAL_SUB_LDISTRIB]
\\ fs [real_sub]
\\ fs [REAL_NEG_LMUL]
\\ fs [REAL_ADD_ASSOC]
\\ fs [GSYM REAL_NEG_LMUL]
\\ fs [REAL_MUL_SYM]
\\ fs [GSYM REAL_ADD_ASSOC]
QED

val _ = ParseExtras.temp_tight_equality();

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
>-(fs[sum_def] \\ fs[REAL_DIV_LZERO])
\\ fs [sum_def]
\\ fs [real_div]
\\ rewrite_tac [GSYM REAL_MUL, GSYM REAL_ADD]
\\ rewrite_tac [REAL]
\\ rewrite_tac [REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB]
\\ rewrite_tac [REAL_MUL_RID, REAL_MUL_LID]
\\ rewrite_tac [REAL_ADD_ASSOC]
\\ fs [GSYM REAL_ADD_SYM]
\\ once_rewrite_tac [REAL_ADD_ASSOC]
\\ fs [REAL_DOUBLE]
\\ ` 2 * inv 2 = 1` by (irule REAL_MUL_RINV \\ fs[])
\\ fs [REAL_ADD_ASSOC]
\\ fs [REAL_ADD_SYM]
\\ fs [REAL_ADD_ASSOC]
\\ fs [GSYM real_div]
\\ fs [REAL_HALF_DOUBLE]
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
>-(fs [square_number_def])
\\ fs [square_number_def]
\\ fs [SUM_SQUARED]
\\ fs [REAL]
\\ fs [SUC_ONE_ADD]
\\ fs [LEFT_ADD_DISTRIB]
\\ fs [SUM_SQUARED]
QED

val sum_of_cubes_def = Define `
  (sum_of_cubes 0 = 0:real) /\
  (sum_of_cubes (SUC n) = (&(SUC n)) pow 3 + sum_of_cubes n)`;
(**
  The sum of cubed numbers up to n is the squared sum
**)
Theorem sum_of_cubes_is_squared_sum:
  ! n. sum_of_cubes n = (sum n) pow 2
Proof
Induct_on `n`
>-(fs [sum_of_cubes_def, sum_def, POW_2]) (* Base case *)

(* Definitions and identities *)
\\ fs [sum_def, sum_of_cubes_def, gaussian_sum]

(* Destruct 3 *)
\\ `3 = SUC 2` by DECIDE_TAC
\\ use_last_assum

(* expanding... *)
\\ rewrite_tac [pow, POW_2, REAL]
\\ rewrite_tac [REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB]

\\ rewrite_tac [real_div]
\\ rewrite_tac [REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB]
\\ rewrite_tac [REAL_MUL_ASSOC]
\\ rewrite_tac [REAL_ADD_ASSOC]

\\ rewrite_tac [GSYM REAL_ADD, GSYM REAL_MUL]
\\ rewrite_tac [REAL_ADD_RDISTRIB, REAL_ADD_LDISTRIB]

\\ rewrite_tac [REAL_MUL_ASSOC]
\\ rewrite_tac [REAL_ADD_ASSOC]
\\ rewrite_tac [REAL_MUL_RID, REAL_MUL_LID]
(* ...expanded *)

\\ fs [] (* simplify *)

\\ once_rewrite_tac [REAL_MUL_SYM]
\\ fs [REAL_MUL_ASSOC]
\\ ntac 2 (once_rewrite_tac [REAL_MUL_SYM] \\ fs[GSYM real_div])

(* Reorder and REFL *)
\\ `&(n + n²) + &n³ / 2 + &n² / 2 + &n + 1 + &n² / 2 + &n / 2 + &n³ / 2 +
    &n² / 2 + &n² / 2 + &n / 2 =
   (&n² / 2 + &n² / 2) + (&n² / 2 + &n² / 2) + (&n /2 + &n / 2) + &(n + n²) + (&n³ / 2 + &n³ / 2) + &n + 1 `
  by (REAL_ASM_ARITH_TAC)

\\ use_last_assum
\\ fs[REAL_HALF_DOUBLE]
QED

val SOS2_def = Define `
  (SOS2 0 = 0) /\
  (SOS2 (SUC n) = SUC n * SUC n + SOS2 n)`;

Theorem sos2_3:
  ! n. 3 * (SOS2 n) = ((n * (n+1))*(2 * n + 1)) DIV 2
Proof
Induct_on `n`
>-(fs [SOS2_def])
\\ fs [SOS2_def]

\\ rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
\\ use_last_assum
\\ fs [ADD1]
\\ fs [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]

(* Nat *)
\\ `3 = SUC 2` by DECIDE_TAC
\\ use_last_assum
\\ `2 = SUC 1` by DECIDE_TAC
\\ use_last_assum
\\ `1 = SUC 0` by DECIDE_TAC
\\ use_last_assum

(* Expanding *)
\\ STRIP_ASSUME_TAC EXP
\\ first_assum (fn thm => once_rewrite_tac [thm])
\\ first_assum (fn thm => once_rewrite_tac [thm])
\\ first_x_assum (fn thm => once_rewrite_tac [thm])
\\ first_x_assum (fn thm => once_rewrite_tac [thm])
\\ rewrite_tac [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
\\ fs[]

\\ `13 * n + (2 * n³ + (9 * n² + 6))
  = ((6 * n) * 2) + (n + 2 * n³ + 9 * n² + 6)`
  by (fs [])
\\ use_last_assum

\\ qspec_then `2`
  impl_subgoal_tac
  ADD_DIV_RWT
>-(DECIDE_TAC)

\\ pop_assum
  (fn thm => qspecl_then
    [`6 * n * 2`, `n + 2 * n³ + 9 * n² + 6`]
    impl_subgoal_tac
    thm)
>-(DISJ1_TAC \\ fs [])
\\ use_last_assum

\\ qspecl_then
  [`2`, `6 * n`]
  assume_tac
  MULT_DIV
\\ first_x_assum impl_subgoal_tac
>-(DECIDE_TAC)
\\ use_last_assum

\\ `n + 2 * n³ + 9 * n² + 6
  = (n + (2 * n³ + 3 * n²)) + ((3 * (n EXP 2) + 3) * 2)`
  by (fs [])
\\ use_last_assum

\\ qspec_then `2` impl_subgoal_tac ADD_DIV_RWT
>-(DECIDE_TAC)

\\ pop_assum
  (fn thm => qspecl_then
    [`n + (2 * n³ + 3 * n²)`,`(3 * n² + 3) * 2`]
    impl_subgoal_tac
    thm)
>-(DISJ2_TAC \\ fs [])
\\ use_last_assum

\\ qspecl_then
  [`2`,`3 * n² + 3`]
  (fn thm => fs [thm])
  MULT_DIV
QED

val _ = export_theory();
