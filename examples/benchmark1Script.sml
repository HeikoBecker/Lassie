open BasicProvers Defn HolKernel Parse SatisfySimps Tactic monadsyntax boolTheory bossLib lcsymtacs;
open realTheory arithmeticTheory realTheory realLib RealArith;
open LassieLib;

val _ = new_theory "benchmark1";

Definition min4_def:
min4 a b c d = min a (min b (min c d))
End

Definition max4_def:
  max4 a b c d = max a (max b (max c d))
End

infix 3 ||;
fun (s1:(goal, thm) gentactic) || (s2:string) = s1 \\ LassieLib.nltac s2;

infix 4 ^^;
fun (str1:string) ^^ (str2:string) = str1 ^ " " ^ str2;
(**
  Formalization of real valued interval arithmetic
  Used in soundness proofs for error bound validator.
**)

val _ = temp_overload_on("abs",``real$abs``);
val _ = temp_overload_on("max",``real$max``);
val _ = temp_overload_on("min",``real$min``);
(**
  Define validity of an interval, requiring that the lower bound is less than or equal to the upper bound.
  Containement is defined such that if x is contained in the interval, it must lie between the lower and upper bound.
**)
Definition valid_def:
  valid ((lo,hi):(real # real)) = (lo <= hi)
End

Definition contained_def:
  contained (a:real) (lo,hi) = (lo <= a /\ a <= hi)
End

Definition absIntvUpd_def:
absIntvUpd (op:real->real->real) (iv1:real#real) (iv2:real#real) =
(
  min4 (op (FST iv1) (FST iv2))
       (op (FST iv1) (SND iv2))
       (op (SND iv1) (FST iv2))
       (op (SND iv1) (SND iv2)),
  max4 (op (FST iv1) (FST iv2))
       (op (FST iv1) (SND iv2))
       (op (SND iv1) (FST iv2))
       (op (SND iv1) (SND iv2))
)
End

Definition widenInterval_def:
widenInterval (iv:real#real) (v:real) = ((FST iv - v), (SND iv + v))
End

Definition negateInterval_def:
negateInterval (iv:real#real) = ((- SND iv), (- FST iv))
End

Definition invertInterval_def:
  invertInterval (iv:real#real)  = (1 /(SND iv), 1 /(FST iv))
End

Definition addInterval_def:
  addInterval (iv1:real#real) (iv2:real#real) = absIntvUpd (+) iv1 iv2
End

Definition subtractInterval_def:
 subtractInterval (iv1:real#real) (iv2:real#real) = addInterval iv1 (negateInterval iv2)
End

Definition multInterval_def:
  multInterval (iv1:real#real) (iv2:real#real) = absIntvUpd ( * ) iv1 iv2
End

Definition divideInterval_def:
  divideInterval iv1 iv2 = multInterval iv1 (invertInterval iv2)
End

Definition minAbsFun_def:
  minAbsFun iv = min (abs (FST iv)) (abs (SND iv))
End

(** Lassie definitions **)
LassieLib.addCustomTactic "REAL_ASM_ARITH_TAC";
LassieLib.addCustomTactic "impl_tac";

LassieLib.def "introduce variables" ["rpt gen_tac"];
(* LassieLib.def "case split for ` s `" ["Cases_on ` s `"]; *)
LassieLib.def "trivial using [CONJ_COMM]" ["metis_tac [CONJ_COMM]"];
LassieLib.def "simplify with [min4_def]" ["simp [min4_def]"];
LassieLib.def "try solving with [min4_def]" ["TRY simp [min4_def]"];
(* LassieLib.def "choose `e`" ["qexists_tac `e`"]; *)
LassieLib.def "use REAL_LE_TRANS" ["irule REAL_LE_TRANS"];
LassieLib.def "perform a case split" ["rpt conj_tac"];
(* LassieLib.def "we show first `T`" ["sg `T`"]; *)

Theorem contained_implies_valid:
  !(a:real) (iv:real#real).
  contained a iv ==> valid iv
Proof
  LassieLib.nltac "introduce variables. case split for `iv`. trivial using [contained_def, valid_def, REAL_LE_TRANS]."
QED

Theorem min4_correct:
  ! a b c d.
    let m = min4 a b c d in
      m <= a /\ m <= b /\ m <= c /\ m <= d
Proof
  LassieLib.nltac (
  "introduce variables."
  ^^ "simplify with [min4_def]."
  ^^ "perform a case split."
  ^^ "try solving with [REAL_MIN_LE1]."
  ^^ "use REAL_LE_TRANS."
  ^^ "choose `min b (min c d)`."
  ^^ "simplify with [REAL_MIN_LE1, REAL_MIN_LE2]."
  ^^ "use REAL_LE_TRANS."
  ^^ "choose `(min c d)`."
  ^^ "simplify with [REAL_MIN_LE1, REAL_MIN_LE2].")
QED

Theorem max4_correct:
  !a b c d.
    let m = max4 a b c d in
      a <= m /\ b <= m /\ c <= m /\ d <= m
Proof
  LassieLib.nltac (
  "introduce variables."
  ^^ "simplify with [max4_def]."
  ^^ "perform a case split."
  ^^ "try solving with [REAL_LE_MAX1]."
  ^^ "use REAL_LE_TRANS."
  ^^ "choose `max b (max c d)`."
  ^^ "simplify with [REAL_LE_MAX1, REAL_LE_MAX2]."
  ^^ "use REAL_LE_TRANS."
  ^^ "choose `(max c d)`."
  ^^ "simplify with [REAL_LE_MAX1, REAL_LE_MAX2].")
QED

Theorem interval_negation_valid:
  ! iv a.
    contained a iv ==> contained (- a) (negateInterval iv)
Proof
  LassieLib.nltac (
  "introduce variables."
  ^^ "case split for `iv`."
  ^^ "try solving with [contained_def, negateInterval_def, REAL_LE_TRANS].")
QED

Theorem iv_neg_preserves_valid:
  !iv.
    valid iv ==> valid (negateInterval iv)
Proof
  LassieLib.nltac (
  "introduce variables."
  ^^ "case split for `iv`."
  ^^ "simplify with [valid_def, negateInterval_def].")
QED

LassieLib.def "introduce assumptions" ["rpt strip_tac"];
LassieLib.def "rewrite once [REAL_INV_1OVER]" ["once_rewrite_tac [REAL_INV_1OVER]"];
LassieLib.def "rewrite once [<- REAL_INV_1OVER]" ["once_rewrite_tac [GSYM REAL_INV_1OVER]"];
LassieLib.def "rewrite with [REAL_INV_1OVER]" ["rewrite_tac [REAL_INV_1OVER]"];
LassieLib.def "rewrite with [<- REAL_INV_1OVER]" ["rewrite_tac [GSYM REAL_INV_1OVER]"];
LassieLib.def "we show next `T`" ["we show first `T`"];
LassieLib.def "resolve with REAL_NEG_INV" ["imp_res_tac REAL_NEG_INV"];

val REAL_INV_LE_ANTIMONO = store_thm ("REAL_INV_LE_ANTIMONO",
  ``! x y. 0 < x /\ 0 < y ==> (inv x <= inv y <=> y <= x)``,
  rpt strip_tac
  \\ `inv x < inv y <=> y < x`
    by (MATCH_MP_TAC REAL_INV_LT_ANTIMONO \\ fs [])
  \\ EQ_TAC
  \\ fs [REAL_LE_LT]
  \\ STRIP_TAC
  \\ fs [REAL_INV_INJ]);

Theorem interval_inversion_valid:
  !iv a.
    (SND iv < 0 \/ 0 < FST iv) /\ contained a iv ==>
      contained (inv a) (invertInterval iv)
Proof
  LassieLib.nltac (
  "introduce variables."
  ^^ "case split for `iv`."
  ^^ "simplify with [contained_def, invertInterval_def]."
  ^^ "introduce assumptions."
  ^^ "rewrite once [<- REAL_INV_1OVER].")
  >- (
    LassieLib.nltac "rewrite once [ <- REAL_LE_NEG]."
    || "we show first `a < 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "we show next `a <> 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "we show next `r < 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "we show next `r <> 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ `inv(-a) ≤ inv (-r) <=> (- r) <= - a`
      by (LassieLib.nltac "use REAL_INV_LE_ANTIMONO THEN simplify with [].")
    || "resolve with REAL_NEG_INV."
    || "asm_rewrite_tac[]."
    || "fs [].")
  >- (
    LassieLib.nltac "rewrite once [<- REAL_LE_NEG]."
    || "we show first `a < 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "we show next `a <> 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "we show next `q <> 0`."
    >- (LassieLib.nltac "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "resolve with REAL_NEG_INV."
    \\ `inv (-q) <= inv (-a) <=> (-a) <= (-q)`
      by (LassieLib.nltac "use REAL_INV_LE_ANTIMONO THEN simplify with [] THEN REAL_ASM_ARITH_TAC.")
    || "asm_rewrite_tac[]."
    || "fs[].")
  >- (
    LassieLib.nltac "rewrite with [<- REAL_INV_1OVER]."
    || "we show first `inv r <= inv a <=> a <= r`."
    >- (
      LassieLib.nltac "use REAL_INV_LE_ANTIMONO."
      || "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "fs[].")
  \\ LassieLib.nltac "rewrite with [<- REAL_INV_1OVER]."
  || "we show first `inv a <= inv q <=> q <= a`."
    >- (
      LassieLib.nltac "use REAL_INV_LE_ANTIMONO."
      || "REAL_ASM_ARITH_TAC.")
    \\ LassieLib.nltac "fs[]."
QED

val _ = export_theory();
