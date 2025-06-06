open HolKernel boolLib Parse bossLib;

val _ = new_theory "cake_baseline";

(* CakeML: *)
open preamble ml_translatorLib ml_progLib basisProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 1000);

val _ = translation_extends "basisProg";

(* Creates baseline FFI-using program (same as ffi_test, but all functionality written directly in CakeML) *)
cake_baseline_ffiLib.get_baseline_program (Theory.current_theory());

val _ = export_theory ();
