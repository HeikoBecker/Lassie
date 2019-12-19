open BasicProvers Defn HolKernel Parse SatisfySimps Tactic monadsyntax boolTheory bossLib lcsymtacs;
open LassieLib;

val _ = new_theory "LassieTests";

val this_can_never_be_a_thm = Q.prove (`T`, fs[]);

val _ = LassieLib.nltac "Cases";
val _ = LassieLib.nltac "rpt Cases";
val _ = LassieLib.nltac "drule this_can_never_be_a_thm";
val _ = LassieLib.nltac "fs [ this_can_never_be_a_thm ]";
val _ = LassieLib.nltac "rewrite_tac [ CONJ_COMM ] ";
val _ = LassieLib.nltac "Cases THEN Cases";
(* val _ = LassieLib.nltac "qexists_tac `e`"; *)

(** Testing custom tactics **)
val awesomeTac = rpt gen_tac \\ rpt conj_tac \\ rpt strip_tac;

val _ = LassieLib.addCustomTactic "awesomeTac";
val _ = LassieLib.nltac "awesomeTac";

fun awesomeThmTac thm = mp_tac thm;

val _ = LassieLib.addCustomThmTactic "awesomeThmTac";
val _ = LassieLib.nltac "awesomeThmTac CONJ_COMM";

LassieLib.def "repeat strip_tac" ["rpt strip_tac"];
LassieLib.def "simplify with []" ["simp []"];

printGrammar()

(* Tests generalization *)
val _ = LassieLib.nltac "repeat gen_tac";

val _ = export_theory();
