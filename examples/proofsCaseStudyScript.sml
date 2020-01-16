open BasicProvers Defn HolKernel Parse Conv SatisfySimps Tactic monadsyntax
     boolTheory bossLib lcsymtacs;

open realTheory arithmeticTheory realLib RealArith;

open LassieLib;

val _ = new_theory "proofsCaseStudy";

Definition min4_def:
min4 a b c d = min a (min b (min c d))
End

Definition max4_def:
  max4 a b c d = max a (max b (max c d))
End

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
val _ = LassieLib.addCustomTactic "REAL_ASM_ARITH_TAC";
val _ = LassieLib.addCustomTactic "impl_tac";
val _ = LassieLib.addCustomTactic "cheat";

val _ = LassieLib.def `introduce variables` [`rpt gen_tac`];
val _ = LassieLib.def `introduce assumptions` [`rpt strip_tac`];
val _ = LassieLib.def `introduce variables and assumptions` [`rpt strip_tac`];

val _ = LassieLib.def `case split` [`(rpt conj_tac ORELSE EQ_TAC) ORELSE Cases`];
val _ = LassieLib.def `case split for 's'` [`Cases_on 's'`];
val _ = LassieLib.def `perform a case split` [`case split`];
val _ = LassieLib.def `trivial` [`metis_tac []`];
val _ = LassieLib.def `trivial using [CONJ_COMM]` [`metis_tac [CONJ_COMM]`];

val _ = LassieLib.def `simplify` [`simp []`];
val _ = LassieLib.def `simplify with [min4_def]` [`simp [min4_def]`];
val _ = LassieLib.def `try gen_tac` [`TRY gen_tac`];
(* val _ = LassieLib.def `try solving with [min4_def]` [`TRY simp [min4_def]`]; *)
val _ = LassieLib.def `choose 'e'` [`qexists_tac 'e'`];
val _ = LassieLib.def `use REAL_LE_TRANS` [`irule REAL_LE_TRANS`];
val _ = LassieLib.def `we show first 'T'` [`sg 'T'`];

val _ = LassieLib.def `use transitivity for 'x'` [`irule REAL_LE_TRANS THEN qexists_tac 'x'`];
val _ = LassieLib.def `resolve with REAL_NEG_INV` [`imp_res_tac REAL_NEG_INV`];

val _ = LassieLib.def `rewrite once [REAL_INV_1OVER]` [`once_rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite once [<- REAL_INV_1OVER]` [`once_rewrite_tac [GSYM REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [REAL_INV_1OVER]` [`rewrite_tac [REAL_INV_1OVER]`];
val _ = LassieLib.def `rewrite with [<- REAL_INV_1OVER]` [`rewrite_tac [GSYM REAL_INV_1OVER]`];

val _ = LassieLib.def `we show next 'T'` [`we show first 'T'`];
val _ = LassieLib.def `'T' using (fs[])` [`'T' by ( fs[] )`];
val _ = LassieLib.def `we know 'T'` [`'T' by (REAL_ASM_ARITH_TAC)`];
val _ = LassieLib.def `we show 'T' using (gen_tac)` [`'T' by (gen_tac)`];
val _ = LassieLib.def `thus 'T'` [`we know 'T'`];

val _ = LassieLib.def `follows trivially` [`fs []`];
val _ = LassieLib.def `follows from [ADD_COMM]` [`fs[ADD_COMM]`];

val _ = LassieLib.def `rewrite assumptions` [`asm_rewrite_tac []`];
val _ = LassieLib.def `rewrite assumptions and [ADD_ASSOC] ` [`asm_rewrite_tac [ADD_ASSOC]`];

Theorem contained_implies_valid:
  !(a:real) (iv:real#real).
  contained a iv ==> valid iv
Proof
  LassieLib.nltac `
    introduce variables.
    case split for 'iv'.
    trivial using [contained_def, valid_def, REAL_LE_TRANS].`
QED

Theorem min4_correct:
  ! a b c d.
    let m = min4 a b c d in
      m <= a /\ m <= b /\ m <= c /\ m <= d
Proof
  LassieLib.nltac `
  introduce variables. simplify with [min4_def]. perform a case split.
  try simplify with [REAL_MIN_LE1].
  use transitivity for 'min b (min c d)'.
  simplify with [REAL_MIN_LE1, REAL_MIN_LE2].
  use transitivity for 'min c d'.
  simplify with [REAL_MIN_LE1, REAL_MIN_LE2].`
QED

Theorem max4_correct:
  !a b c d.
    let m = max4 a b c d in
      a <= m /\ b <= m /\ c <= m /\ d <= m
Proof
  LassieLib.nltac `
  introduce variables. simplify with [max4_def]. perform a case split.
  try simplify with [REAL_LE_MAX1].
  use transitivity for 'max b (max c d)'.
  simplify with [REAL_LE_MAX1, REAL_LE_MAX2].
  use transitivity for 'max c d'.
  simplify with [REAL_LE_MAX1, REAL_LE_MAX2].`
QED

Theorem interval_negation_valid:
  ! iv a.
    contained a iv ==> contained (- a) (negateInterval iv)
Proof
  LassieLib.nltac `
  introduce variables. case split for 'iv'.
  simplify with [contained_def, negateInterval_def, REAL_LE_TRANS].`
QED

Theorem iv_neg_preserves_valid:
  !iv.
    valid iv ==> valid (negateInterval iv)
Proof
  LassieLib.nltac `
  introduce variables.
  case split for 'iv'.
  simplify with [valid_def, negateInterval_def].`
QED

Theorem REAL_INV_LE_ANTIMONO[local]:
  ! x y.
    0 < x /\ 0 < y ==>
    (inv x <= inv y <=> y <= x)
Proof
  LassieLib.nltac `
    introduce variables and assumptions.
    we show 'inv x < inv y <=> y < x' using (use REAL_INV_LT_ANTIMONO THEN follows trivially).
    case split.
    simplify with [REAL_LE_LT].
    introduce assumptions.
    follows from [REAL_INV_INJ].`
QED

Theorem interval_inversion_valid:
  !iv a.
    (SND iv < 0 \/ 0 < FST iv) /\ contained a iv ==>
      contained (inv a) (invertInterval iv)
Proof
  LassieLib.nltac `
  introduce variables.
  case split for 'iv'.
  simplify with [contained_def, invertInterval_def].
  introduce assumptions.
  rewrite once [<- REAL_INV_1OVER].`
  >- (
    LassieLib.nltac `
    rewrite once [ <- REAL_LE_NEG]. we know 'a < 0'. thus 'a <> 0'.
    we know 'r < 0'. thus 'r <> 0'.
    'inv(-a) <= inv (-r) <=> (- r) <= -a' by (use REAL_INV_LE_ANTIMONO THEN simplify with []).
    resolve with REAL_NEG_INV. rewrite assumptions and []. follows trivially.`)
  >- (
    LassieLib.nltac `
    rewrite once [<- REAL_LE_NEG].
    we know 'a < 0'. thus 'a <> 0'. we know 'q <> 0'.
    resolve with REAL_NEG_INV.
    'inv (-q) <= inv (-a) <=> (-a) <= (-q)' by (use REAL_INV_LE_ANTIMONO THEN simplify with [] THEN REAL_ASM_ARITH_TAC).
    rewrite assumptions and []. follows trivially.`)
  >- (
    LassieLib.nltac `
      rewrite with [<- REAL_INV_1OVER].
      'inv r <= inv a <=> a <= r' by (use REAL_INV_LE_ANTIMONO THEN REAL_ASM_ARITH_TAC).
      follows trivially.`)
  \\ LassieLib.nltac `
    rewrite with [<- REAL_INV_1OVER].
    'inv a <= inv q <=> q <= a' by (use REAL_INV_LE_ANTIMONO THEN REAL_ASM_ARITH_TAC).
    follows trivially.`
QED

val _ = export_theory();
