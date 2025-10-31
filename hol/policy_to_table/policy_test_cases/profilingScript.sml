open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;
open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open alistTheory;
open numeralTheory;
open set_relationTheory;
open pred_setLib;

open p4_auxTheory;
open bdd_genTheory;
open numeralTheory;
open alistTheory;


open pred_specTheory;


open bdd_genTheory;
open policy_arith_to_varTheory;

open bdd_utilsLib;
open fwd_proofLib;   


val _ = new_theory "internet_firewall_4";

val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("h", type_record [("srcPort", type_length 16);
                                        ("dstPort", type_length 16);
                                        ("srcNAT", type_length 16);
                                        ("dstNAT", type_length 16)])]”;

(************************************************)

(* rule 1 *)

val is_srcPort_le_57222 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;
val is_srcPort_ge_57222 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;

val is_dstPort_le_53 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;
val is_dstPort_ge_53 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;

val is_srcNAT_le_54587 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54587 16))”;
val is_srcNAT_ge_54587 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54587 16))”;

val is_dstNAT_le_53 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 53 16))”;
val is_dstNAT_ge_53 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 53 16))”;


val arith_policy_rule1 = “((arith_and (arith_a ^is_srcPort_le_57222)
                          (arith_and (arith_a ^is_srcPort_ge_57222)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_54587)
                          (arith_and (arith_a ^is_srcNAT_ge_54587)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 2 *)

val is_srcPort_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcPort_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstPort_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstPort_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;

val is_srcNAT_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcNAT_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstNAT_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstNAT_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;


val arith_policy_rule2 = “((arith_and (arith_a ^is_srcPort_le_56258)
                          (arith_and (arith_a ^is_srcPort_ge_56258)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_56258)
                          (arith_and (arith_a ^is_srcNAT_ge_56258)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 3 *)

val is_srcPort_le_6881 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;
val is_srcPort_ge_6881 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;

val is_dstPort_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstPort_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;

val is_srcNAT_le_43265 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;
val is_srcNAT_ge_43265 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;

val is_dstNAT_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstNAT_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;


val arith_policy_rule3 = “((arith_and (arith_a ^is_srcPort_le_6881)
                          (arith_and (arith_a ^is_srcPort_ge_6881)
                          (arith_and (arith_a ^is_dstPort_le_50321)
                          (arith_and (arith_a ^is_dstPort_ge_50321)
                          (arith_and (arith_a ^is_srcNAT_le_43265)
                          (arith_and (arith_a ^is_srcNAT_ge_43265)
                          (arith_and (arith_a ^is_dstNAT_le_50321)
                                   (arith_a ^is_dstNAT_ge_50321)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 4 *)

val is_srcPort_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcPort_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;

val is_srcNAT_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcNAT_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;


val arith_policy_rule4 = “((arith_and (arith_a ^is_srcPort_le_50553)
                          (arith_and (arith_a ^is_srcPort_ge_50553)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_50553)
                          (arith_and (arith_a ^is_srcNAT_ge_50553)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))) ,
                           action ("allow",[])):single_rule”;

(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;

(* Combined arith policy list *)
val arith_policy = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule_default
]:single_rule list”;



(* Combined policy mapping *)
val policy_me =   “[
    ("is_srcPort_le_57222", ^is_srcPort_le_57222);
    ("is_srcPort_ge_57222", ^is_srcPort_ge_57222);
    ("is_dstPort_le_53", ^is_dstPort_le_53);
    ("is_dstPort_ge_53", ^is_dstPort_ge_53);
    ("is_srcNAT_le_54587", ^is_srcNAT_le_54587);
    ("is_srcNAT_ge_54587", ^is_srcNAT_ge_54587);
    ("is_dstNAT_le_53", ^is_dstNAT_le_53);
    ("is_dstNAT_ge_53", ^is_dstNAT_ge_53);
    ("is_srcPort_le_56258", ^is_srcPort_le_56258);
    ("is_srcPort_ge_56258", ^is_srcPort_ge_56258);
    ("is_dstPort_le_3389", ^is_dstPort_le_3389);
    ("is_dstPort_ge_3389", ^is_dstPort_ge_3389);
    ("is_srcNAT_le_56258", ^is_srcNAT_le_56258);
    ("is_srcNAT_ge_56258", ^is_srcNAT_ge_56258);
    ("is_dstNAT_le_3389", ^is_dstNAT_le_3389);
    ("is_dstNAT_ge_3389", ^is_dstNAT_ge_3389);
    ("is_srcPort_le_6881", ^is_srcPort_le_6881);
    ("is_srcPort_ge_6881", ^is_srcPort_ge_6881);
    ("is_dstPort_le_50321", ^is_dstPort_le_50321);
    ("is_dstPort_ge_50321", ^is_dstPort_ge_50321);
    ("is_srcNAT_le_43265", ^is_srcNAT_le_43265);
    ("is_srcNAT_ge_43265", ^is_srcNAT_ge_43265);
    ("is_dstNAT_le_50321", ^is_dstNAT_le_50321);
    ("is_dstNAT_ge_50321", ^is_dstNAT_ge_50321);
    ("is_srcPort_le_50553", ^is_srcPort_le_50553);
    ("is_srcPort_ge_50553", ^is_srcPort_ge_50553);
    ("is_srcNAT_le_50553", ^is_srcNAT_le_50553);
    ("is_srcNAT_ge_50553", ^is_srcNAT_ge_50553);
]”;

(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321"]”;


val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;



val eval_table_full_opt_auto =
   EVAL “mk_BDDPred_opt_new table_structure (0,[],[(0, (id_non_termn NONE , 0))], [0,^gen_var_table_auto]) [] ^policy_order 1”;



    


(*convert arith policy to var policy*)        
val arith_policy_eval = EVAL “convert_arith_to_var_policy ^arith_policy ^policy_me”;
val var_policy = optionSyntax.dest_some (rhs (concl arith_policy_eval));

    
(* first establish distinction of domain and range of me*)
val policy_me_fst_distinct = EVAL “ALL_DISTINCT (MAP FST ^policy_me)”;
val policy_me_snd_distinct = EVAL “ALL_DISTINCT (MAP SND ^policy_me)”;

val all_distinct_conj = CONJ policy_me_fst_distinct policy_me_snd_distinct;

    
(* Theorem of correctness for conversion from arith policy to var policy *)
val arith_policy_var_policy_thm = REWRITE_RULE[all_distinct_conj, arith_policy_eval]
(ISPECL[arith_policy, var_policy, policy_me] policy_airth_to_var_sem_conversion_correct);  



                       
(* create BDD of var policy  *)
val eval_policy_full_opt = EVAL “mk_BDDPred_opt policy_structure (0,[],[(0, non_termn (NONE, ^var_policy))]) [] ^policy_order 1”;
val eval_policy_full_opt_rhs = optionSyntax.dest_some (rhs (concl eval_policy_full_opt));


(* automatically generate a var table from the var policy's BDD via sml*)
val test_groupings = rhs(concl(EVAL policy_full_order));
val gen_var_table_auto =  bdd_utilsLib.bdd_to_tables_iterative eval_policy_full_opt_rhs test_groupings;


      
(*******************************)

val eval_table_full_layer1 = time EVAL
      “mk_BDDPred_new table_structure (0n,[],[(0n, id_non_termn (NONE), 0n)], [(0n, ^gen_var_table_auto)]) [] ["is_srcPort_le_57222"] 1n”;


val eval_table_full_layer1_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer1));



val eval_table_full_opt_layer1 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer1_rhs ^policy_order”;
val eval_table_full_opt_layer1_rhs = (rhs (concl eval_table_full_opt_layer1));




    
    (***********************)
val eval_table_full_layer2 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer1_rhs [] ["is_srcPort_ge_57222"] 3”;

val eval_table_full_layer2_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer2));


val eval_table_full_opt_layer2 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer2_rhs ^policy_order”;
val eval_table_full_opt_layer2_rhs = (rhs (concl eval_table_full_opt_layer2));


    (***********************)
val eval_table_full_layer3 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer2_rhs [] ["is_srcPort_le_56258"] 5”;

val eval_table_full_layer3_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer3));


val eval_table_full_opt_layer3 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer3_rhs ^policy_order”;
val eval_table_full_opt_layer3_rhs = (rhs (concl eval_table_full_opt_layer3));

(*****************)

val eval_table_full_layer4 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer3_rhs [] ["is_srcPort_ge_56258"] 9”;

val eval_table_full_layer4_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer4));


val eval_table_full_opt_layer4 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer4_rhs ^policy_order”;
val eval_table_full_opt_layer4_rhs = (rhs (concl eval_table_full_opt_layer4));


(************************)


val eval_table_full_layer5 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer4_rhs [] ["is_srcPort_le_6881"] 15”;

val eval_table_full_layer5_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer5));


val eval_table_full_opt_layer5 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer5_rhs ^policy_order”;
val eval_table_full_opt_layer5_rhs = (rhs (concl eval_table_full_opt_layer5));


(********************)



val eval_table_full_layer6 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer5_rhs [] ["is_srcPort_ge_6881"] 23”;

val eval_table_full_layer6_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer6));


val eval_table_full_opt_layer6 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer6_rhs ^policy_order”;
val eval_table_full_opt_layer6_rhs = (rhs (concl eval_table_full_opt_layer6));



(********************)

val eval_table_full_layer7 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer6_rhs [] ["is_srcPort_le_50553"] 37”;

val eval_table_full_layer7_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer7));


val eval_table_full_opt_layer7 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer7_rhs ^policy_order”;
val eval_table_full_opt_layer7_rhs = (rhs (concl eval_table_full_opt_layer7));



(********************)


val eval_table_full_layer8 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer7_rhs [] ["is_srcPort_ge_50553"] 53”;

val eval_table_full_layer8_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer8));


val eval_table_full_opt_layer8 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer8_rhs ^policy_order”;
val eval_table_full_opt_layer8_rhs = (rhs (concl eval_table_full_opt_layer8));



(**********************)

val eval_table_full_layer9 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer8_rhs [] ["is_dstPort_le_53"] 82”;

val eval_table_full_layer9_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer9));


val eval_table_full_opt_layer9 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer9_rhs ^policy_order”;
val eval_table_full_opt_layer9_rhs = (rhs (concl eval_table_full_opt_layer9));


(*******************)

val eval_table_full_layer10 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer9_rhs [] ["is_dstPort_ge_53"] 97”;

val eval_table_full_layer10_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer10));


val eval_table_full_opt_layer10 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer10_rhs ^policy_order”;
val eval_table_full_opt_layer10_rhs = (rhs (concl eval_table_full_opt_layer10));


(*********************)

val eval_table_full_layer11 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer10_rhs [] ["is_dstPort_le_3389"] 126”;

val eval_table_full_layer11_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer11));


val eval_table_full_opt_layer11 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer11_rhs ^policy_order”;
val eval_table_full_opt_layer11_rhs = (rhs (concl eval_table_full_opt_layer11));



(*****************************)


val eval_table_full_layer12 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer11_rhs [] ["is_dstPort_ge_3389"] 153”;

val eval_table_full_layer12_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer12));


val eval_table_full_opt_layer12 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer12_rhs ^policy_order”;
val eval_table_full_opt_layer12_rhs = (rhs (concl eval_table_full_opt_layer12));



(*************************************)

val eval_table_full_layer13 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer12_rhs [] ["is_dstPort_le_50321"] 182”;

val eval_table_full_layer13_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer13));


val eval_table_full_opt_layer13 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer13_rhs ^policy_order”;
val eval_table_full_opt_layer13_rhs = (rhs (concl eval_table_full_opt_layer13));


(*************************************)

val eval_table_full_layer14 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer13_rhs [] ["is_dstPort_ge_50321"] 205”;

val eval_table_full_layer14_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer14));


val eval_table_full_opt_layer14 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer14_rhs ^policy_order”;
val eval_table_full_opt_layer14_rhs = (rhs (concl eval_table_full_opt_layer14));


(*************************************)



val eval_table_full_layer15 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer14_rhs [] ["is_srcNAT_le_43265"] 234”;

val eval_table_full_layer15_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer15));


val eval_table_full_opt_layer15 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer15_rhs ^policy_order”;
val eval_table_full_opt_layer15_rhs = (rhs (concl eval_table_full_opt_layer15));



(***************************************)


val eval_table_full_layer16 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer15_rhs [] ["is_srcNAT_ge_43265"] 263”;

val eval_table_full_layer16_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer16));


val eval_table_full_opt_layer16 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer16_rhs ^policy_order”;
val eval_table_full_opt_layer16_rhs = (rhs (concl eval_table_full_opt_layer16));



(*******************************)


val eval_table_full_layer17 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer16_rhs [] ["is_srcNAT_le_50553"] 292”;

val eval_table_full_layer17_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer17));


val eval_table_full_opt_layer17 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer17_rhs ^policy_order”;
val eval_table_full_opt_layer17_rhs = (rhs (concl eval_table_full_opt_layer17));

        
(********************************)


val eval_table_full_layer18 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer17_rhs [] ["is_srcNAT_ge_50553"] 319”;

val eval_table_full_layer18_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer18));


val eval_table_full_opt_layer18 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer18_rhs ^policy_order”;
val eval_table_full_opt_layer18_rhs = (rhs (concl eval_table_full_opt_layer18));



(*******************************)



val eval_table_full_layer19 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer18_rhs [] ["is_dstNAT_le_53"] 348”;

val eval_table_full_layer19_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer19));


val eval_table_full_opt_layer19 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer19_rhs ^policy_order”;
val eval_table_full_opt_layer19_rhs = (rhs (concl eval_table_full_opt_layer19));



(*****************************)



val eval_table_full_layer20 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer19_rhs [] ["is_dstNAT_ge_53"] 371”;

val eval_table_full_layer20_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer20));


val eval_table_full_opt_layer20 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer20_rhs ^policy_order”;
val eval_table_full_opt_layer20_rhs = (rhs (concl eval_table_full_opt_layer20));



(*********************************)


val eval_table_full_layer21 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer20_rhs [] ["is_dstNAT_le_3389"] 400”;

val eval_table_full_layer21_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer21));


val eval_table_full_opt_layer21 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer21_rhs ^policy_order”;
val eval_table_full_opt_layer21_rhs = (rhs (concl eval_table_full_opt_layer21));




(********************************)


val eval_table_full_layer22 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer21_rhs [] ["is_dstNAT_ge_3389"] 427”;

val eval_table_full_layer22_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer22));


val eval_table_full_opt_layer22 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer22_rhs ^policy_order”;
val eval_table_full_opt_layer22_rhs = (rhs (concl eval_table_full_opt_layer22));



(*********************************)

val eval_table_full_layer23 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer22_rhs [] ["is_dstNAT_le_50321"] 456”;

val eval_table_full_layer23_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer23));


val eval_table_full_opt_layer23 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer23_rhs ^policy_order”;
val eval_table_full_opt_layer23_rhs = (rhs (concl eval_table_full_opt_layer23));




(*****************************)



val eval_table_full_layer24 = time EVAL
      “mk_BDDPred_new table_structure ^eval_table_full_opt_layer23_rhs [] ["is_dstNAT_ge_50321"] 479”;

val eval_table_full_layer24_rhs = optionSyntax.dest_some (rhs (concl eval_table_full_layer24));


val eval_table_full_opt_layer24 = EVAL
      “ optimize_bdd_new ^eval_table_full_layer24_rhs ^policy_order”;
val eval_table_full_opt_layer24_rhs = (rhs (concl eval_table_full_opt_layer24));

val _ = export_theory ();
