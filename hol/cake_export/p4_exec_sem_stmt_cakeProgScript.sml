open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_sem_stmt_cakeProg";
     
open p4Syntax;
open p4Theory;
open p4_auxTheory;
open p4_exec_semTheory;

(* CakeML: *)
open preamble ml_translatorLib ml_translatorTheory ml_progLib basisProgTheory mlmapTheory basisFunctionsLib
     astPP comparisonTheory;

open p4_exec_sem_e_cakeProgTheory;

intLib.deprecate_int();
val _ = (max_print_depth := 100);

val _ = translation_extends "p4_exec_sem_e_cakeProg";

val _ = ml_prog_update (open_module "p4_exec_sem_stmt_cake");


val _ = translate bitstringTheory.n2v_def;


val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
