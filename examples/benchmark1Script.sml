open bossLib realTheory arithmeticTheory RealArith;
open LassieLib;

val _ = new_theory "benchmark1";

Definition min4_def:
min4 a b c d = min a (min b (min c d))
End

Definition max4_def:
  max4 a b c d = max a (max b (max c d))
End

infix 3 |>;
fun (s1:(goal, thm) gentactic) |> (s2:string) = s1 \\ LassieLib.nltac s2;

(** Setup SEMPRE **)
LassieLib.def "repeat strip_tac" ["rpt strip_tac"];
LassieLib.def "introduce variables" ["repeat gen_tac"];
LassieLib.def "maybe Cases" ["TRY Cases"];
LassieLib.def "simplify with [min4_def]" ["simp [min4_def]"];
LassieLib.def "perform a case split" ["repeat conj_tac"];
LassieLib.def "try solving with [min4_def]" ["TRY simp [min4_def]"];
LassieLib.def "choose `e`" ["qexists_tac `e`"];
LassieLib.def "use REAL_LE_TRANS" ["irule REAL_LE_TRANS"];

(* Tests *)

LassieLib.nltac "rpt strip_tac";
LassieLib.nltac "repeat gen_tac";

Theorem min4_correct:
  ! a b c d.
    let m = min4 a b c d in
      m <= a /\ m <= b /\ m <= c /\ m <= d
Proof
  LassieLib.nltac "introduce variables"
  |> "simplify with [min4_def]"
  |> "perform a case split"
  |> "try solving with [REAL_MIN_LE1]"
  |> "use REAL_LE_TRANS"
  |> "choose `min b (min c d)`"
  |> "simplify with [REAL_MIN_LE1, REAL_MIN_LE2]"
  |> "use REAL_LE_TRANS"
  |> "choose `(min c d)`"
  |> "simplify with [REAL_MIN_LE1, REAL_MIN_LE2]"
QED

rpt strip_tac \\fs [min4_def] \\ conj_tac \\
try (fs [REAL_MIN_LE1]) \\ conj_tac
>- (`min b (min c d) <= b` by fs[REAL_MIN_LE1] \\
   match_mp_tac REAL_LE_TRANS \\
   HINT_EXISTS_TAC \\
   fs [REAL_MIN_LE2])
>- (conj_tac
    >- (`min c d <= c` by fs [REAL_MIN_LE1] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       `min b (min c d) <= min c d` by fs[REAL_MIN_LE2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] )
    >- (`min c d <= d` by fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2] \\
       match_mp_tac REAL_LE_TRANS \\
       `min b (min c d) <= min c d` by fs[REAL_MIN_LE2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_MIN_LE2])));

val max4_correct = store_thm ("max4_correct",
``!a b c d.
  let m = max4 a b c d in
    a <= m /\ b <= m /\ c <= m /\ d <= m``,
rpt strip_tac \\fs [max4_def] \\ conj_tac \\
try (fs [REAL_LE_MAX1]) \\ conj_tac
>-(`b <= max b (max c d)` by fs[REAL_LE_MAX1] \\
match_mp_tac REAL_LE_TRANS \\
HINT_EXISTS_TAC \\
fs [REAL_LE_MAX2])
>- (conj_tac
    >- (`c <= max c d` by fs [REAL_LE_MAX1] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       `max c d <= max b (max c d)` by fs[REAL_LE_MAX2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] )
    >- (`d <= max c d` by fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] \\
       match_mp_tac REAL_LE_TRANS \\
       `max c d <= max b (max c d)` by fs[REAL_LE_MAX2] \\
       HINT_EXISTS_TAC \\
       fs [REAL_LE_MAX2] )));
