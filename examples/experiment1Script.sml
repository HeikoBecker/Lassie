open bossLib realTheory arithmeticTheory RealArith;
open Lassie;

val _ = new_theory "experiment1";

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
rpt strip_tac
\\ fs [POW_2]
\\ fs [REAL_RDISTRIB, REAL_LDISTRIB, REAL_ADD_ASSOC]
\\ fs [GSYM REAL_DOUBLE]
\\ fs [REAL_RDISTRIB, REAL_ADD_ASSOC]
\\ fs [REAL_MUL_SYM]
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

val sum_def = Define `
  (sum 0 = 0) /\
  (sum (SUC n) = (SUC n + sum n))`

Theorem gaussian_sum
  `! n. (sum n = (n * (1 + n)) DIV 2)`
  (Induct_on `n` \\ fs[sum_def] (* note: no fs[sum_def] here! *)
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
      by (fs[] )
  \\ qpat_x_assum `SUC n + _ = _` (fn thm => once_rewrite_tac [thm])
  \\ once_rewrite_tac [MULT_COMM]
  \\ fs[ADD_DIV_ADD_DIV])

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