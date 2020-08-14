open BasicProvers Defn HolKernel Parse SatisfySimps Tactic monadsyntax boolTheory bossLib;
open LassieLib;

val _ = new_theory "LassieTest";

val this_can_never_be_a_thm = Q.store_thm ("test", `T`, fs[]);

val t = LassieLib.nltac ‘TAC$cheat. TAC$cheat. TAC$cheat. TAC$cheat.’

val t = LassieLib.nltac ‘TAC$Cases.’;

val t = LassieLib.nltac ‘QUOTTAC$Cases_on ' x '.’

val t = LassieLib.nltac ‘THMLISTTAC$fs [ arithmeticTheory.ADD_ASSOC ].’

val t = LassieLib.def `test123` [`TAC$cheat`];

val t = LassieLib.nltac ‘test123.’;

val t = LassieLib.nltac ‘THMTAC$imp_res_tac test.’;

val t = LassieLib.nltac ‘(QUOTSPECTHMTAC$qspec_then ' x ' THMTAC$irule test).’

val t = LassieLib.def `resolve_with test` [`THMTAC$imp_res_tac test`];

val t = LassieLib.nltac ‘resolve_with CONJ_COMM.’;

val t = LassieLib.nltac ‘THMLISTTAC$fs [ test , test ].’;

val t = LassieLib.nltac ‘TAC$cheat TACCOMB$THEN TAC$cheat.’

val t = LassieLib.nltac ‘' T ' TERMCOMB$by TAC$cheat.’

val t = LassieLib.nltac ‘Goal 1. TAC$cheat.’
(*
val _ = LassieLib.nltac `Cases.`;
val _ = LassieLib.nltac `rpt Cases.`;
val _ = LassieLib.nltac `drule this_can_never_be_a_thm.`;
val _ = LassieLib.nltac `fs [ this_can_never_be_a_thm ].`;
val _ = LassieLib.nltac `rewrite_tac [ CONJ_COMM ].`;
val _ = LassieLib.nltac `Cases THEN Cases.`;
(* val _ = LassieLib.nltac `qexists_tac `e``; *)

(** Testing custom tactics **)
val awesomeTac = rpt gen_tac \\ rpt conj_tac \\ rpt strip_tac;

val _ = LassieLib.addCustomTactic "awesomeTac";
val _ = LassieLib.nltac `awesomeTac.`;

fun awesomeThmTac thm = mp_tac thm;

val _ = LassieLib.addCustomThmTactic "awesomeThmTac";
val _ = LassieLib.nltac `awesomeThmTac CONJ_COMM.`;

val _ = LassieLib.def `repeat strip_tac` [`rpt strip_tac`];
val _ = LassieLib.def `simplify with [CONJ_COMM]` [`simp [CONJ_COMM]`];

(* Tests generalization *)
val _ = LassieLib.nltac `repeat simplify with [].`;
val _ = LassieLib.nltac `repeat simplify with [CONJ_COMM] THEN gen_tac.`;

(* More advanced tactics *)
(* val _ = LassieLib.nltac `qpat_x_assum `T` assume_tac.`; *)
val _ = LassieLib.nltac `first_x_assum assume_tac.`;
val _ = LassieLib.nltac `qspec_then 'T' assume_tac CONJ_COMM.`;
val _ = LassieLib.nltac `qspecl_then ['T','F'] assume_tac CONJ_COMM.`;

Theorem test:
  T
Proof
  LassieLib.nltac `fs[].`
QED
*)

val _ = export_theory();
