structure apply_trans_to_IOLib :> apply_trans_to_IOLib = struct


open HolKernel Parse boolLib bossLib;
open optionTheory bdd_sptrees_genTheory pairTheory bdd_genTheory tables_specTheory tables_spec_oldTheory policy_specTheory pred_specTheory;

open sptrees_bdd_trans_ProgTheory;
open preamble basis ml_translatorLib ;

open miscTheory ;
open fromSexpTheory;


val _ = translation_extends "sptrees_bdd_trans_Prog";


val _ = type_abbrev("action_policy_type", “:((string# num list) action_expr) policy”);



fun time_stage (stage_name, timer_cpu, timer_real) = 
        let
            val cpu_time = Timer.checkCPUTimer timer_cpu
            val real_time = Timer.checkRealTimer timer_real
            val _ = HOL_MESG (stage_name ^ " completed in: " ^ 
                          Time.toString (#usr cpu_time) ^ " user, " ^ 
                          Time.toString (#sys cpu_time) ^ " system, " ^ 
                          Time.toString real_time ^ " real\n")
        in
            (cpu_time, real_time)
end





fun sptrees_gen_bdds_policy_and_table (var_policy, policy_order, policy_full_order) =

let

val start_cpu_stage2_io = Timer.startCPUTimer ();
val start_real_stage2_io = Timer.startRealTimer (); 


Definition policy_order_test_def:
 policy_order_test = (^policy_order:string list)
End

val r = translate policy_order_test_def;

Definition policy_content_test_def:
  policy_content_test = (^var_policy:action_policy_type)
End

val r = translate policy_content_test_def;


Definition policy_main_hol4_def:
  policy_main_hol4 =
  case sp_mk_BDD_policy policy_content_test  policy_order_test of
  | NONE => NONE
  | SOME (r,sp_edges,sp_labels) => SOME (r,
                                         ((toSortedAList sp_edges):edges),
                                         ((toSortedAList sp_labels): (((string#num list) action_expr) policy, (string#num list) action_expr) labelings) )
End





val r = translate policy_main_hol4_def;


val res = append_prog o process_topdecs $
                      ‘fun main () =
                       let
                        val args = CommandLine.arguments()
                       in
                         (case policy_main_hol4 of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>
                              (
                              TextIO.print "(" ;
                              TextIO.print (Int.toString (fst bdd));
                              (TextIO.print "n , \n");

                              TextIO.print "(" ;
                              print_tuple_list (fst (snd (bdd))) ;
                              TextIO.print "):edges , \n";

                              TextIO.print "(" ;
                              print_list_label (snd (snd (bdd))) ;
                              TextIO.print "): (((string#num list) action_expr) policy, (string#num list) action_expr) labelings";

                              TextIO.print ")"
                              )

                         )
                         end ;’
                     ;


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs;



val _ = astToSexprLib.write_ast_to_file "../../bdd_cake_test/test_bdd_policy.sexp" prog;

val _ = time_stage ("Stage 2 from var policy to sexp - cakeML trans ", start_cpu_stage2_io, start_real_stage2_io);
val start_cpu_stage2_io2 = Timer.startCPUTimer ();
val start_real_stage2_io2 = Timer.startRealTimer (); 

val status_compile_sexp = OS.Process.system  "cd ../../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S"

val _ = if OS.Process.isSuccess status_compile_sexp
        then print "Ja, policy cakeML compilation completed\n"
        else (print "Nej, policy cakeML compilation failed\n";
              OS.Process.exit OS.Process.failure)

val status_cc = OS.Process.system  "cd ../../bdd_cake_test/ && cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm"

val _ = if OS.Process.isSuccess status_cc 
        then print "Ja, policy cc compilation completed\n"
        else (print "Nej, policy cc compilation failed\n";
              OS.Process.exit OS.Process.failure)

val status_exec = OS.Process.system  "cd ../../bdd_cake_test/ && time ./test_bdd_policy.cake > bdd_policy_cakeml_export.txt";

val _ = if OS.Process.isSuccess status_exec 
        then print "Ja, policy cc compilation completed\n"
        else (print "Nej, policy cc compilation failed\n";
              OS.Process.exit OS.Process.failure)

val _ = time_stage ("Stage 2 cakeML compiliation var policy to bdd ", start_cpu_stage2_io2, start_real_stage2_io2);
val start_cpu_stage2_io3 = Timer.startCPUTimer ();
val start_real_stage2_io3 = Timer.startRealTimer (); 

(*

cp test_bdd_policy.sexp ../../bdd_cake_test

CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_policy.sexp > test_bdd_policy.cake.S

cc test_bdd_policy.cake.S basis_ffi.c -lm -o test_bdd_policy.cake -lm

time ./test_bdd_policy.cake > bdd_policy_cakeml_export.txt


*)








val ins = TextIO.openIn "../../bdd_cake_test/bdd_policy_cakeml_export.txt";
val policy_content_str = TextIO.inputAll ins;
val _ = TextIO.closeIn ins;

val _ = time_stage ("Stage 2 from Policy to var BDD total ", start_cpu_stage2_io, start_real_stage2_io);

(*open Term;*)

val policy_bdd_content_term =
    let
        (* Clean the string by removing newlines and backslash escapes *)
        fun clean s =
            let
                val chars = String.explode s
                fun process [] = []
                  | process (#"\\" :: #"n" :: rest) = process rest  (* remove \n *)
                  | process (c :: rest) = c :: process rest
            in
                String.implode (process chars)
            end

        val cleaned = clean policy_content_str
        val parsed = Parse.Term [QUOTE cleaned]
    in
        parsed
end;





val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto = bdd_utilsLib.bdd_to_tables_iterative policy_bdd_content_term test_groupings;



Definition table_content_test_def:
  table_content_test = (^gen_var_table_auto : action_table_type)
End

val r = translate table_content_test_def;


Definition table_main_hol4_def:
  table_main_hol4 =
  case sp_mk_BDD_table table_content_test policy_order_test of
  | NONE => NONE
  | SOME (r,sp_edges,sp_labels) => SOME (r,
                                         ((toSortedAList sp_edges):edges),
                                         ((toSortedAList sp_labels): (action_table_type, (string#num list) action_expr) labelings) )
End


val r = translate table_main_hol4_def;


val res = append_prog o process_topdecs $
                      ‘fun main () =
                       let
                        val args = CommandLine.arguments()
                       in
                         (case table_main_hol4 of
                            None => (TextIO.print "No BDD can be created \n")
                          | Some bdd =>
                              (
                              TextIO.print "(" ;
                              TextIO.print (Int.toString (fst bdd));
                              (TextIO.print "n , \n");

                              TextIO.print "(" ;
                              print_tuple_list (fst (snd (bdd))) ;
                              TextIO.print "):edges , \n";

                              TextIO.print "(" ;
                              print_list_tables_lbl (snd (snd (bdd))) ;
                              TextIO.print "): (action_table_type, (string#num list) action_expr) labelings)"
                              )

                         )
                         end ;
’;


val prog =
  ``SNOC
    (Dlet unknown_loc (Pcon NONE [])
      (App Opapp [Var (Short "main"); Con NONE []]))
    ^(get_ml_prog_state() |> get_prog)
  `` |> EVAL |> concl |> rhs;



val _ = astToSexprLib.write_ast_to_file "../../bdd_cake_test/test_bdd_table.sexp" prog;

val _ = time_stage ("Stage 2 prepp out table and recompile cakeml translation ", start_cpu_stage2_io3, start_real_stage2_io3);
val start_cpu_stage2_io4 = Timer.startCPUTimer ();
val start_real_stage2_io4 = Timer.startRealTimer (); 



val status = OS.Process.system  "cd ../../bdd_cake_test/ && CML_STACK_SIZE=2048 CML_HEAP_SIZE=8192 ./cake --sexp=true --exclude_prelude=true --skip_type_inference=false --jump=false --reg_alg=0 < test_bdd_table.sexp > test_bdd_table.cake.S && cc test_bdd_table.cake.S basis_ffi.c -lm -o test_bdd_table.cake -lm && time ./test_bdd_table.cake > bdd_table_cakeml_export.txt"

val _ = if OS.Process.isSuccess status
        then print "Ja, table cakeML compilation completed\n"
        else (print "Nej, table cakeML compilation failed\n";
              OS.Process.exit OS.Process.failure)



(*
reset_translation
val _ = astPP.enable_astPP ();
val _ = (max_print_depth := 200);
*)



val ins = TextIO.openIn "../../bdd_cake_test/bdd_table_cakeml_export.txt";
val tbl_content_str = TextIO.inputAll ins;
val _ = TextIO.closeIn ins;




val table_bdd_content_term =
    let
        (* Clean the string by removing newlines and backslash escapes *)
        fun clean s =
            let
                val chars = String.explode s
                fun process [] = []
                  | process (#"\\" :: #"n" :: rest) = process rest  (* remove \n *)
                  | process (c :: rest) = c :: process rest
            in
                String.implode (process chars)
            end

        val cleaned = clean tbl_content_str
        val parsed = Parse.Term [QUOTE cleaned]
    in
        parsed
end;



val _ = time_stage ("Stage 2 cakeML compiliation var table to BDD ", start_cpu_stage2_io4, start_real_stage2_io4);

val _ = time_stage ("Stage 2 from TABLE to var BDD total ", start_cpu_stage2_io3, start_real_stage2_io3);

in 
(policy_bdd_content_term, gen_var_table_auto, table_bdd_content_term)
end;



end;