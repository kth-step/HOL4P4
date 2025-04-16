open HolKernel boolLib Parse bossLib;

val _ = new_theory "cake_baseline";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_progLib;

intLib.deprecate_int();
val _ = (max_print_depth := 1000);

open p4_exec_sem_cakeProgTheory;
open p4_cake_transformLib p4_cake_auxLib;

val _ = translation_extends "p4_exec_sem_cakeProg";

(* Creates baseline FFI program (same as test2, but in CakeML) *)

p4_baseline_ffiLib.get_baseline_program (Theory.current_theory());

val _ = export_theory ();
