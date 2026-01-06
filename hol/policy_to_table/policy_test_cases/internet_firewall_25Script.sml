open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib; 


val _ = new_theory "internet_firewall_25";

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

(* rule 5 *)

val is_srcPort_le_50002 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;
val is_srcPort_ge_50002 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;

val is_dstPort_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstPort_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;

val is_srcNAT_le_45848 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;
val is_srcNAT_ge_45848 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;

val is_dstNAT_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstNAT_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;


val arith_policy_rule5 = “((arith_and (arith_a ^is_srcPort_le_50002)
                          (arith_and (arith_a ^is_srcPort_ge_50002)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_45848)
                          (arith_and (arith_a ^is_srcNAT_ge_45848)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 6 *)

val is_srcPort_le_51465 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;
val is_srcPort_ge_51465 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;

val is_srcNAT_le_39975 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 39975 16))”;
val is_srcNAT_ge_39975 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 39975 16))”;


val arith_policy_rule6 = “((arith_and (arith_a ^is_srcPort_le_51465)
                          (arith_and (arith_a ^is_srcPort_ge_51465)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_39975)
                          (arith_and (arith_a ^is_srcNAT_ge_39975)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 7 *)

val is_srcPort_le_60513 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;
val is_srcPort_ge_60513 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;

val is_dstPort_le_47094 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;
val is_dstPort_ge_47094 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;

val is_srcNAT_le_45469 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45469 16))”;
val is_srcNAT_ge_45469 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45469 16))”;

val is_dstNAT_le_47094 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 47094 16))”;
val is_dstNAT_ge_47094 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 47094 16))”;


val arith_policy_rule7 = “((arith_and (arith_a ^is_srcPort_le_60513)
                          (arith_and (arith_a ^is_srcPort_ge_60513)
                          (arith_and (arith_a ^is_dstPort_le_47094)
                          (arith_and (arith_a ^is_dstPort_ge_47094)
                          (arith_and (arith_a ^is_srcNAT_le_45469)
                          (arith_and (arith_a ^is_srcNAT_ge_45469)
                          (arith_and (arith_a ^is_dstNAT_le_47094)
                                   (arith_a ^is_dstNAT_ge_47094)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 8 *)

val is_srcPort_le_50049 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;
val is_srcPort_ge_50049 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;

val is_srcNAT_le_21285 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 21285 16))”;
val is_srcNAT_ge_21285 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 21285 16))”;


val arith_policy_rule8 = “((arith_and (arith_a ^is_srcPort_le_50049)
                          (arith_and (arith_a ^is_srcPort_ge_50049)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_21285)
                          (arith_and (arith_a ^is_srcNAT_ge_21285)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 9 *)

val is_srcPort_le_52244 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;
val is_srcPort_ge_52244 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;

val is_dstPort_le_58774 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;
val is_dstPort_ge_58774 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;

val is_srcNAT_le_2211 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2211 16))”;
val is_srcNAT_ge_2211 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2211 16))”;

val is_dstNAT_le_58774 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 58774 16))”;
val is_dstNAT_ge_58774 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 58774 16))”;


val arith_policy_rule9 = “((arith_and (arith_a ^is_srcPort_le_52244)
                          (arith_and (arith_a ^is_srcPort_ge_52244)
                          (arith_and (arith_a ^is_dstPort_le_58774)
                          (arith_and (arith_a ^is_dstPort_ge_58774)
                          (arith_and (arith_a ^is_srcNAT_le_2211)
                          (arith_and (arith_a ^is_srcNAT_ge_2211)
                          (arith_and (arith_a ^is_dstNAT_le_58774)
                                   (arith_a ^is_dstNAT_ge_58774)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 10 *)

val is_srcPort_le_50627 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;
val is_srcPort_ge_50627 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;

val is_srcNAT_le_16215 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16215 16))”;
val is_srcNAT_ge_16215 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16215 16))”;


val arith_policy_rule10 = “((arith_and (arith_a ^is_srcPort_le_50627)
                          (arith_and (arith_a ^is_srcPort_ge_50627)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_16215)
                          (arith_and (arith_a ^is_srcNAT_ge_16215)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 11 *)

val is_srcPort_le_43676 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 43676 16))”;
val is_srcPort_ge_43676 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 43676 16))”;

val is_dstPort_le_80 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 80 16))”;
val is_dstPort_ge_80 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 80 16))”;

val is_srcNAT_le_45378 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45378 16))”;
val is_srcNAT_ge_45378 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45378 16))”;

val is_dstNAT_le_80 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 80 16))”;
val is_dstNAT_ge_80 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 80 16))”;


val arith_policy_rule11 = “((arith_and (arith_a ^is_srcPort_le_43676)
                          (arith_and (arith_a ^is_srcPort_ge_43676)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_45378)
                          (arith_and (arith_a ^is_srcNAT_ge_45378)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 12 *)

val is_srcPort_le_52190 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52190 16))”;
val is_srcPort_ge_52190 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52190 16))”;

val is_srcNAT_le_16680 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16680 16))”;
val is_srcNAT_ge_16680 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16680 16))”;


val arith_policy_rule12 = “((arith_and (arith_a ^is_srcPort_le_52190)
                          (arith_and (arith_a ^is_srcPort_ge_52190)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_16680)
                          (arith_and (arith_a ^is_srcNAT_ge_16680)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 13 *)

val is_srcPort_le_50690 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50690 16))”;
val is_srcPort_ge_50690 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50690 16))”;

val is_srcNAT_le_20479 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 20479 16))”;
val is_srcNAT_ge_20479 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 20479 16))”;


val arith_policy_rule13 = “((arith_and (arith_a ^is_srcPort_le_50690)
                          (arith_and (arith_a ^is_srcPort_ge_50690)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_20479)
                          (arith_and (arith_a ^is_srcNAT_ge_20479)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 14 *)

val is_srcPort_le_55597 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 55597 16))”;
val is_srcPort_ge_55597 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 55597 16))”;

val is_srcNAT_le_45448 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45448 16))”;
val is_srcNAT_ge_45448 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45448 16))”;


val arith_policy_rule14 = “((arith_and (arith_a ^is_srcPort_le_55597)
                          (arith_and (arith_a ^is_srcPort_ge_55597)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_45448)
                          (arith_and (arith_a ^is_srcNAT_ge_45448)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 15 *)

val is_srcPort_le_49164 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 49164 16))”;
val is_srcPort_ge_49164 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 49164 16))”;

val is_srcNAT_le_45916 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45916 16))”;
val is_srcNAT_ge_45916 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45916 16))”;


val arith_policy_rule15 = “((arith_and (arith_a ^is_srcPort_le_49164)
                          (arith_and (arith_a ^is_srcPort_ge_49164)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_45916)
                          (arith_and (arith_a ^is_srcNAT_ge_45916)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 16 *)

val is_srcPort_le_36887 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 36887 16))”;
val is_srcPort_ge_36887 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 36887 16))”;

val is_srcNAT_le_63451 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 63451 16))”;
val is_srcNAT_ge_63451 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 63451 16))”;


val arith_policy_rule16 = “((arith_and (arith_a ^is_srcPort_le_36887)
                          (arith_and (arith_a ^is_srcPort_ge_36887)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_63451)
                          (arith_and (arith_a ^is_srcNAT_ge_63451)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 17 *)

val is_srcPort_le_1939 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 1939 16))”;
val is_srcPort_ge_1939 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 1939 16))”;

val is_srcNAT_le_33288 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 33288 16))”;
val is_srcNAT_ge_33288 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 33288 16))”;


val arith_policy_rule17 = “((arith_and (arith_a ^is_srcPort_le_1939)
                          (arith_and (arith_a ^is_srcPort_ge_1939)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_33288)
                          (arith_and (arith_a ^is_srcNAT_ge_33288)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 18 *)

val is_srcPort_le_50281 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50281 16))”;
val is_srcPort_ge_50281 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50281 16))”;

val is_srcNAT_le_33175 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 33175 16))”;
val is_srcNAT_ge_33175 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 33175 16))”;


val arith_policy_rule18 = “((arith_and (arith_a ^is_srcPort_le_50281)
                          (arith_and (arith_a ^is_srcPort_ge_50281)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_33175)
                          (arith_and (arith_a ^is_srcNAT_ge_33175)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 19 *)

val is_srcNAT_le_51448 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 51448 16))”;
val is_srcNAT_ge_51448 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 51448 16))”;


val arith_policy_rule19 = “((arith_and (arith_a ^is_srcPort_le_57222)
                          (arith_and (arith_a ^is_srcPort_ge_57222)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_51448)
                          (arith_and (arith_a ^is_srcNAT_ge_51448)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 20 *)

val is_srcPort_le_56710 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56710 16))”;
val is_srcPort_ge_56710 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56710 16))”;

val is_srcNAT_le_57885 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 57885 16))”;
val is_srcNAT_ge_57885 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 57885 16))”;


val arith_policy_rule20 = “((arith_and (arith_a ^is_srcPort_le_56710)
                          (arith_and (arith_a ^is_srcPort_ge_56710)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_57885)
                          (arith_and (arith_a ^is_srcNAT_ge_57885)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 21 *)

val is_srcPort_le_48488 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 48488 16))”;
val is_srcPort_ge_48488 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 48488 16))”;

val is_srcNAT_le_26104 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 26104 16))”;
val is_srcNAT_ge_26104 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 26104 16))”;


val arith_policy_rule21 = “((arith_and (arith_a ^is_srcPort_le_48488)
                          (arith_and (arith_a ^is_srcPort_ge_48488)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_26104)
                          (arith_and (arith_a ^is_srcNAT_ge_26104)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 22 *)

val is_srcPort_le_50691 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50691 16))”;
val is_srcPort_ge_50691 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50691 16))”;

val is_srcNAT_le_62082 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 62082 16))”;
val is_srcNAT_ge_62082 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 62082 16))”;


val arith_policy_rule22 = “((arith_and (arith_a ^is_srcPort_le_50691)
                          (arith_and (arith_a ^is_srcPort_ge_50691)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_62082)
                          (arith_and (arith_a ^is_srcNAT_ge_62082)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 23 *)

val is_srcPort_le_50693 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50693 16))”;
val is_srcPort_ge_50693 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50693 16))”;

val is_srcNAT_le_54649 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54649 16))”;
val is_srcNAT_ge_54649 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 54649 16))”;


val arith_policy_rule23 = “((arith_and (arith_a ^is_srcPort_le_50693)
                          (arith_and (arith_a ^is_srcPort_ge_50693)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_54649)
                          (arith_and (arith_a ^is_srcNAT_ge_54649)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 24 *)

val is_srcPort_le_1940 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 1940 16))”;
val is_srcPort_ge_1940 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 1940 16))”;

val is_srcNAT_le_23603 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 23603 16))”;
val is_srcNAT_ge_23603 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 23603 16))”;


val arith_policy_rule24 = “((arith_and (arith_a ^is_srcPort_le_1940)
                          (arith_and (arith_a ^is_srcPort_ge_1940)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_23603)
                          (arith_and (arith_a ^is_srcNAT_ge_23603)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 25 *)

val is_srcPort_le_50172 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50172 16))”;
val is_srcPort_ge_50172 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50172 16))”;

val is_srcNAT_le_37056 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 37056 16))”;
val is_srcNAT_ge_37056 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 37056 16))”;


val arith_policy_rule25 = “((arith_and (arith_a ^is_srcPort_le_50172)
                          (arith_and (arith_a ^is_srcPort_ge_50172)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_37056)
                          (arith_and (arith_a ^is_srcNAT_ge_37056)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;

(* Combined arith policy list *)
val arith_policy = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule5;
    ^arith_policy_rule6;
    ^arith_policy_rule7;
    ^arith_policy_rule8;
    ^arith_policy_rule9;
    ^arith_policy_rule10;
    ^arith_policy_rule11;
    ^arith_policy_rule12;
    ^arith_policy_rule13;
    ^arith_policy_rule14;
    ^arith_policy_rule15;
    ^arith_policy_rule16;
    ^arith_policy_rule17;
    ^arith_policy_rule18;
    ^arith_policy_rule19;
    ^arith_policy_rule20;
    ^arith_policy_rule21;
    ^arith_policy_rule22;
    ^arith_policy_rule23;
    ^arith_policy_rule24;
    ^arith_policy_rule25;
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
    ("is_srcPort_le_50002", ^is_srcPort_le_50002);
    ("is_srcPort_ge_50002", ^is_srcPort_ge_50002);
    ("is_dstPort_le_443", ^is_dstPort_le_443);
    ("is_dstPort_ge_443", ^is_dstPort_ge_443);
    ("is_srcNAT_le_45848", ^is_srcNAT_le_45848);
    ("is_srcNAT_ge_45848", ^is_srcNAT_ge_45848);
    ("is_dstNAT_le_443", ^is_dstNAT_le_443);
    ("is_dstNAT_ge_443", ^is_dstNAT_ge_443);
    ("is_srcPort_le_51465", ^is_srcPort_le_51465);
    ("is_srcPort_ge_51465", ^is_srcPort_ge_51465);
    ("is_srcNAT_le_39975", ^is_srcNAT_le_39975);
    ("is_srcNAT_ge_39975", ^is_srcNAT_ge_39975);
    ("is_srcPort_le_60513", ^is_srcPort_le_60513);
    ("is_srcPort_ge_60513", ^is_srcPort_ge_60513);
    ("is_dstPort_le_47094", ^is_dstPort_le_47094);
    ("is_dstPort_ge_47094", ^is_dstPort_ge_47094);
    ("is_srcNAT_le_45469", ^is_srcNAT_le_45469);
    ("is_srcNAT_ge_45469", ^is_srcNAT_ge_45469);
    ("is_dstNAT_le_47094", ^is_dstNAT_le_47094);
    ("is_dstNAT_ge_47094", ^is_dstNAT_ge_47094);
    ("is_srcPort_le_50049", ^is_srcPort_le_50049);
    ("is_srcPort_ge_50049", ^is_srcPort_ge_50049);
    ("is_srcNAT_le_21285", ^is_srcNAT_le_21285);
    ("is_srcNAT_ge_21285", ^is_srcNAT_ge_21285);
    ("is_srcPort_le_52244", ^is_srcPort_le_52244);
    ("is_srcPort_ge_52244", ^is_srcPort_ge_52244);
    ("is_dstPort_le_58774", ^is_dstPort_le_58774);
    ("is_dstPort_ge_58774", ^is_dstPort_ge_58774);
    ("is_srcNAT_le_2211", ^is_srcNAT_le_2211);
    ("is_srcNAT_ge_2211", ^is_srcNAT_ge_2211);
    ("is_dstNAT_le_58774", ^is_dstNAT_le_58774);
    ("is_dstNAT_ge_58774", ^is_dstNAT_ge_58774);
    ("is_srcPort_le_50627", ^is_srcPort_le_50627);
    ("is_srcPort_ge_50627", ^is_srcPort_ge_50627);
    ("is_srcNAT_le_16215", ^is_srcNAT_le_16215);
    ("is_srcNAT_ge_16215", ^is_srcNAT_ge_16215);
    ("is_srcPort_le_43676", ^is_srcPort_le_43676);
    ("is_srcPort_ge_43676", ^is_srcPort_ge_43676);
    ("is_dstPort_le_80", ^is_dstPort_le_80);
    ("is_dstPort_ge_80", ^is_dstPort_ge_80);
    ("is_srcNAT_le_45378", ^is_srcNAT_le_45378);
    ("is_srcNAT_ge_45378", ^is_srcNAT_ge_45378);
    ("is_dstNAT_le_80", ^is_dstNAT_le_80);
    ("is_dstNAT_ge_80", ^is_dstNAT_ge_80);
    ("is_srcPort_le_52190", ^is_srcPort_le_52190);
    ("is_srcPort_ge_52190", ^is_srcPort_ge_52190);
    ("is_srcNAT_le_16680", ^is_srcNAT_le_16680);
    ("is_srcNAT_ge_16680", ^is_srcNAT_ge_16680);
    ("is_srcPort_le_50690", ^is_srcPort_le_50690);
    ("is_srcPort_ge_50690", ^is_srcPort_ge_50690);
    ("is_srcNAT_le_20479", ^is_srcNAT_le_20479);
    ("is_srcNAT_ge_20479", ^is_srcNAT_ge_20479);
    ("is_srcPort_le_55597", ^is_srcPort_le_55597);
    ("is_srcPort_ge_55597", ^is_srcPort_ge_55597);
    ("is_srcNAT_le_45448", ^is_srcNAT_le_45448);
    ("is_srcNAT_ge_45448", ^is_srcNAT_ge_45448);
    ("is_srcPort_le_49164", ^is_srcPort_le_49164);
    ("is_srcPort_ge_49164", ^is_srcPort_ge_49164);
    ("is_srcNAT_le_45916", ^is_srcNAT_le_45916);
    ("is_srcNAT_ge_45916", ^is_srcNAT_ge_45916);
    ("is_srcPort_le_36887", ^is_srcPort_le_36887);
    ("is_srcPort_ge_36887", ^is_srcPort_ge_36887);
    ("is_srcNAT_le_63451", ^is_srcNAT_le_63451);
    ("is_srcNAT_ge_63451", ^is_srcNAT_ge_63451);
    ("is_srcPort_le_1939", ^is_srcPort_le_1939);
    ("is_srcPort_ge_1939", ^is_srcPort_ge_1939);
    ("is_srcNAT_le_33288", ^is_srcNAT_le_33288);
    ("is_srcNAT_ge_33288", ^is_srcNAT_ge_33288);
    ("is_srcPort_le_50281", ^is_srcPort_le_50281);
    ("is_srcPort_ge_50281", ^is_srcPort_ge_50281);
    ("is_srcNAT_le_33175", ^is_srcNAT_le_33175);
    ("is_srcNAT_ge_33175", ^is_srcNAT_ge_33175);
    ("is_srcNAT_le_51448", ^is_srcNAT_le_51448);
    ("is_srcNAT_ge_51448", ^is_srcNAT_ge_51448);
    ("is_srcPort_le_56710", ^is_srcPort_le_56710);
    ("is_srcPort_ge_56710", ^is_srcPort_ge_56710);
    ("is_srcNAT_le_57885", ^is_srcNAT_le_57885);
    ("is_srcNAT_ge_57885", ^is_srcNAT_ge_57885);
    ("is_srcPort_le_48488", ^is_srcPort_le_48488);
    ("is_srcPort_ge_48488", ^is_srcPort_ge_48488);
    ("is_srcNAT_le_26104", ^is_srcNAT_le_26104);
    ("is_srcNAT_ge_26104", ^is_srcNAT_ge_26104);
    ("is_srcPort_le_50691", ^is_srcPort_le_50691);
    ("is_srcPort_ge_50691", ^is_srcPort_ge_50691);
    ("is_srcNAT_le_62082", ^is_srcNAT_le_62082);
    ("is_srcNAT_ge_62082", ^is_srcNAT_ge_62082);
    ("is_srcPort_le_50693", ^is_srcPort_le_50693);
    ("is_srcPort_ge_50693", ^is_srcPort_ge_50693);
    ("is_srcNAT_le_54649", ^is_srcNAT_le_54649);
    ("is_srcNAT_ge_54649", ^is_srcNAT_ge_54649);
    ("is_srcPort_le_1940", ^is_srcPort_le_1940);
    ("is_srcPort_ge_1940", ^is_srcPort_ge_1940);
    ("is_srcNAT_le_23603", ^is_srcNAT_le_23603);
    ("is_srcNAT_ge_23603", ^is_srcNAT_ge_23603);
    ("is_srcPort_le_50172", ^is_srcPort_le_50172);
    ("is_srcPort_ge_50172", ^is_srcPort_ge_50172);
    ("is_srcNAT_le_37056", ^is_srcNAT_le_37056);
    ("is_srcNAT_ge_37056", ^is_srcNAT_ge_37056);
]”;

(*
(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002";"is_srcPort_le_51465";"is_srcPort_ge_51465";"is_srcPort_le_60513";"is_srcPort_ge_60513";"is_srcPort_le_50049";"is_srcPort_ge_50049";"is_srcPort_le_52244";"is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627";"is_srcPort_le_43676";"is_srcPort_ge_43676";"is_srcPort_le_52190";"is_srcPort_ge_52190";"is_srcPort_le_50690";"is_srcPort_ge_50690";"is_srcPort_le_55597";"is_srcPort_ge_55597";"is_srcPort_le_49164";"is_srcPort_ge_49164";"is_srcPort_le_36887";"is_srcPort_ge_36887";"is_srcPort_le_1939";"is_srcPort_ge_1939";"is_srcPort_le_50281";"is_srcPort_ge_50281";"is_srcPort_le_56710";"is_srcPort_ge_56710";"is_srcPort_le_48488";"is_srcPort_ge_48488";"is_srcPort_le_50691";"is_srcPort_ge_50691";"is_srcPort_le_50693";"is_srcPort_ge_50693";"is_srcPort_le_1940";"is_srcPort_ge_1940";"is_srcPort_le_50172";"is_srcPort_ge_50172"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321";"is_dstPort_le_443";"is_dstPort_ge_443";"is_dstPort_le_47094";"is_dstPort_ge_47094";"is_dstPort_le_58774";"is_dstPort_ge_58774";"is_dstPort_le_80";"is_dstPort_ge_80"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553";"is_srcNAT_le_45848";"is_srcNAT_ge_45848";"is_srcNAT_le_39975";"is_srcNAT_ge_39975";"is_srcNAT_le_45469";"is_srcNAT_ge_45469";"is_srcNAT_le_21285";"is_srcNAT_ge_21285";"is_srcNAT_le_2211";"is_srcNAT_ge_2211";"is_srcNAT_le_16215";"is_srcNAT_ge_16215";"is_srcNAT_le_45378";"is_srcNAT_ge_45378";"is_srcNAT_le_16680";"is_srcNAT_ge_16680";"is_srcNAT_le_20479";"is_srcNAT_ge_20479";"is_srcNAT_le_45448";"is_srcNAT_ge_45448";"is_srcNAT_le_45916";"is_srcNAT_ge_45916";"is_srcNAT_le_63451";"is_srcNAT_ge_63451";"is_srcNAT_le_33288";"is_srcNAT_ge_33288";"is_srcNAT_le_33175";"is_srcNAT_ge_33175";"is_srcNAT_le_51448";"is_srcNAT_ge_51448";"is_srcNAT_le_57885";"is_srcNAT_ge_57885";"is_srcNAT_le_26104";"is_srcNAT_ge_26104";"is_srcNAT_le_62082";"is_srcNAT_ge_62082";"is_srcNAT_le_54649";"is_srcNAT_ge_54649";"is_srcNAT_le_23603";"is_srcNAT_ge_23603";"is_srcNAT_le_37056";"is_srcNAT_ge_37056"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321";"is_dstNAT_le_443";"is_dstNAT_ge_443";"is_dstNAT_le_47094";"is_dstNAT_ge_47094";"is_dstNAT_le_58774";"is_dstNAT_ge_58774";"is_dstNAT_le_80";"is_dstNAT_ge_80"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002"; "is_srcPort_ge_50002"; "is_srcPort_le_51465"; "is_srcPort_ge_51465"; "is_srcPort_le_60513"; "is_srcPort_ge_60513"; "is_srcPort_le_50049"; "is_srcPort_ge_50049"; "is_srcPort_le_52244"; "is_srcPort_ge_52244"; "is_srcPort_le_50627"; "is_srcPort_ge_50627"; "is_srcPort_le_43676"; "is_srcPort_ge_43676"; "is_srcPort_le_52190"; "is_srcPort_ge_52190"; "is_srcPort_le_50690"; "is_srcPort_ge_50690"; "is_srcPort_le_55597"; "is_srcPort_ge_55597"; "is_srcPort_le_49164"; "is_srcPort_ge_49164"; "is_srcPort_le_36887"; "is_srcPort_ge_36887"; "is_srcPort_le_1939"; "is_srcPort_ge_1939"; "is_srcPort_le_50281"; "is_srcPort_ge_50281"; "is_srcPort_le_56710"; "is_srcPort_ge_56710"; "is_srcPort_le_48488"; "is_srcPort_ge_48488"; "is_srcPort_le_50691"; "is_srcPort_ge_50691"; "is_srcPort_le_50693"; "is_srcPort_ge_50693"; "is_srcPort_le_1940"; "is_srcPort_ge_1940"; "is_srcPort_le_50172"; "is_srcPort_ge_50172"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_dstPort_le_443"; "is_dstPort_ge_443"; "is_dstPort_le_47094"; "is_dstPort_ge_47094"; "is_dstPort_le_58774"; "is_dstPort_ge_58774"; "is_dstPort_le_80"; "is_dstPort_ge_80"; "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; "is_srcNAT_le_45848"; "is_srcNAT_ge_45848"; "is_srcNAT_le_39975"; "is_srcNAT_ge_39975"; "is_srcNAT_le_45469"; "is_srcNAT_ge_45469"; "is_srcNAT_le_21285"; "is_srcNAT_ge_21285"; "is_srcNAT_le_2211"; "is_srcNAT_ge_2211"; "is_srcNAT_le_16215"; "is_srcNAT_ge_16215"; "is_srcNAT_le_45378"; "is_srcNAT_ge_45378"; "is_srcNAT_le_16680"; "is_srcNAT_ge_16680"; "is_srcNAT_le_20479"; "is_srcNAT_ge_20479"; "is_srcNAT_le_45448"; "is_srcNAT_ge_45448"; "is_srcNAT_le_45916"; "is_srcNAT_ge_45916"; "is_srcNAT_le_63451"; "is_srcNAT_ge_63451"; "is_srcNAT_le_33288"; "is_srcNAT_ge_33288"; "is_srcNAT_le_33175"; "is_srcNAT_ge_33175"; "is_srcNAT_le_51448"; "is_srcNAT_ge_51448"; "is_srcNAT_le_57885"; "is_srcNAT_ge_57885"; "is_srcNAT_le_26104"; "is_srcNAT_ge_26104"; "is_srcNAT_le_62082"; "is_srcNAT_ge_62082"; "is_srcNAT_le_54649"; "is_srcNAT_ge_54649"; "is_srcNAT_le_23603"; "is_srcNAT_ge_23603"; "is_srcNAT_le_37056"; "is_srcNAT_ge_37056"; "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321"; "is_dstNAT_le_443"; "is_dstNAT_ge_443"; "is_dstNAT_le_47094"; "is_dstNAT_ge_47094"; "is_dstNAT_le_58774"; "is_dstNAT_ge_58774"; "is_dstNAT_le_80"; "is_dstNAT_ge_80"]”;
(************************************************)
*)

val policy_order = ``[
  "is_srcPort_le_57222"; "is_srcPort_ge_57222";
  "is_dstPort_le_53"; "is_dstPort_ge_53";
  "is_srcNAT_le_54587"; "is_srcNAT_ge_54587";
  "is_dstNAT_le_53"; "is_dstNAT_ge_53";
  "is_srcPort_le_56258"; "is_srcPort_ge_56258";
  "is_dstPort_le_3389"; "is_dstPort_ge_3389";
  "is_srcNAT_le_56258"; "is_srcNAT_ge_56258";
  "is_dstNAT_le_3389"; "is_dstNAT_ge_3389";
  "is_srcPort_le_6881"; "is_srcPort_ge_6881";
  "is_dstPort_le_50321"; "is_dstPort_ge_50321";
  "is_srcNAT_le_43265"; "is_srcNAT_ge_43265";
  "is_dstNAT_le_50321"; "is_dstNAT_ge_50321";
  "is_srcPort_le_50553"; "is_srcPort_ge_50553";
  "is_srcNAT_le_50553"; "is_srcNAT_ge_50553";
  "is_srcPort_le_50002"; "is_srcPort_ge_50002";
  "is_dstPort_le_443"; "is_dstPort_ge_443";
  "is_srcNAT_le_45848"; "is_srcNAT_ge_45848";
  "is_dstNAT_le_443"; "is_dstNAT_ge_443";
  "is_srcPort_le_51465"; "is_srcPort_ge_51465";
  "is_srcNAT_le_39975"; "is_srcNAT_ge_39975";
  "is_srcPort_le_60513"; "is_srcPort_ge_60513";
  "is_dstPort_le_47094"; "is_dstPort_ge_47094";
  "is_srcNAT_le_45469"; "is_srcNAT_ge_45469";
  "is_dstNAT_le_47094"; "is_dstNAT_ge_47094";
  "is_srcPort_le_50049"; "is_srcPort_ge_50049";
  "is_srcNAT_le_21285"; "is_srcNAT_ge_21285";
  "is_srcPort_le_52244"; "is_srcPort_ge_52244";
  "is_dstPort_le_58774"; "is_dstPort_ge_58774";
  "is_srcNAT_le_2211"; "is_srcNAT_ge_2211";
  "is_dstNAT_le_58774"; "is_dstNAT_ge_58774";
  "is_srcPort_le_50627"; "is_srcPort_ge_50627";
  "is_srcNAT_le_16215"; "is_srcNAT_ge_16215";
  "is_srcPort_le_43676"; "is_srcPort_ge_43676";
  "is_dstPort_le_80"; "is_dstPort_ge_80";
  "is_srcNAT_le_45378"; "is_srcNAT_ge_45378";
  "is_dstNAT_le_80"; "is_dstNAT_ge_80";
  "is_srcPort_le_52190"; "is_srcPort_ge_52190";
  "is_srcNAT_le_16680"; "is_srcNAT_ge_16680";
  "is_srcPort_le_50690"; "is_srcPort_ge_50690";
  "is_srcNAT_le_20479"; "is_srcNAT_ge_20479";
  "is_srcPort_le_55597"; "is_srcPort_ge_55597";
  "is_srcNAT_le_45448"; "is_srcNAT_ge_45448";
  "is_srcPort_le_49164"; "is_srcPort_ge_49164";
  "is_srcNAT_le_45916"; "is_srcNAT_ge_45916";
  "is_srcPort_le_36887"; "is_srcPort_ge_36887";
  "is_srcNAT_le_63451"; "is_srcNAT_ge_63451";
  "is_srcPort_le_1939"; "is_srcPort_ge_1939";
  "is_srcNAT_le_33288"; "is_srcNAT_ge_33288";
  "is_srcPort_le_50281"; "is_srcPort_ge_50281";
  "is_srcNAT_le_33175"; "is_srcNAT_ge_33175";
  "is_srcNAT_le_51448"; "is_srcNAT_ge_51448";
  "is_srcPort_le_56710"; "is_srcPort_ge_56710";
  "is_srcNAT_le_57885"; "is_srcNAT_ge_57885";
  "is_srcPort_le_48488"; "is_srcPort_ge_48488";
  "is_srcNAT_le_26104"; "is_srcNAT_ge_26104";
  "is_srcPort_le_50691"; "is_srcPort_ge_50691";
  "is_srcNAT_le_62082"; "is_srcNAT_ge_62082";
  "is_srcPort_le_50693"; "is_srcPort_ge_50693";
  "is_srcNAT_le_54649"; "is_srcNAT_ge_54649";
  "is_srcPort_le_1940"; "is_srcPort_ge_1940";
  "is_srcNAT_le_23603"; "is_srcNAT_ge_23603";
  "is_srcPort_le_50172"; "is_srcPort_ge_50172";
  "is_srcNAT_le_37056"; "is_srcNAT_ge_37056"
]``;

val policy_full_order = ``[
  ("zj",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("0o15" ,["is_dstPort_le_53";"is_dstPort_ge_53"]);
  ("hms",["is_srcNAT_le_54587";"is_srcNAT_ge_54587"]);
  ("xg8d" ,["is_dstNAT_le_53";"is_dstNAT_ge_53"]);
  ("13",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("86" ,["is_dstPort_le_3389";"is_dstPort_ge_3389"]);
  ("shb",["is_srcNAT_le_56258";"is_srcNAT_ge_56258"]);
  ("jyl5" ,["is_dstNAT_le_3389";"is_dstNAT_ge_3389"]);
  ("o3wh",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("k845" ,["is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("zpwq",["is_srcNAT_le_43265";"is_srcNAT_ge_43265"]);
  ("yp" ,["is_dstNAT_le_50321";"is_dstNAT_ge_50321"]);
  ("yk5z",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("75" ,["is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
  ("4j",["is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("ifb" ,["is_dstPort_le_443";"is_dstPort_ge_443"]);
  ("71q",["is_srcNAT_le_45848";"is_srcNAT_ge_45848"]);
  ("ks7" ,["is_dstNAT_le_443";"is_dstNAT_ge_443"]);
  ("cly4",["is_srcPort_le_51465";"is_srcPort_ge_51465"]);
  ("e6" ,["is_srcNAT_le_39975";"is_srcNAT_ge_39975"]);
  ("cz",["is_srcPort_le_60513";"is_srcPort_ge_60513"]);
  ("tr2" ,["is_dstPort_le_47094";"is_dstPort_ge_47094"]);
  ("5gm",["is_srcNAT_le_45469";"is_srcNAT_ge_45469"]);
  ("mjr" ,["is_dstNAT_le_47094";"is_dstNAT_ge_47094"]);
  ("2sg4",["is_srcPort_le_50049";"is_srcPort_ge_50049"]);
  ("n2o" ,["is_srcNAT_le_21285";"is_srcNAT_ge_21285"]);
  ("ob8",["is_srcPort_le_52244";"is_srcPort_ge_52244"]);
  ("nh7" ,["is_dstPort_le_58774";"is_dstPort_ge_58774"]);
  ("5i",["is_srcNAT_le_2211";"is_srcNAT_ge_2211"]);
  ("2nh9" ,["is_dstNAT_le_58774";"is_dstNAT_ge_58774"]);
  ("1mgd",["is_srcPort_le_50627";"is_srcPort_ge_50627"]);
  ("wii2" ,["is_srcNAT_le_16215";"is_srcNAT_ge_16215"]);
  ("5v",["is_srcPort_le_43676";"is_srcPort_ge_43676"]);
  ("7cac" ,["is_dstPort_le_80";"is_dstPort_ge_80"]);
  ("y0xi",["is_srcNAT_le_45378";"is_srcNAT_ge_45378"]);
  ("ax" ,["is_dstNAT_le_80";"is_dstNAT_ge_80"]);
  ("8zvp",["is_srcPort_le_52190";"is_srcPort_ge_52190"]);
  ("pwdf" ,["is_srcNAT_le_16680";"is_srcNAT_ge_16680"]);
  ("i7v",["is_srcPort_le_50690";"is_srcPort_ge_50690"]);
  ("d7" ,["is_srcNAT_le_20479";"is_srcNAT_ge_20479"]);
  ("i3",["is_srcPort_le_55597";"is_srcPort_ge_55597"]);
  ("2cqt" ,["is_srcNAT_le_45448";"is_srcNAT_ge_45448"]);
  ("k15",["is_srcPort_le_49164";"is_srcPort_ge_49164"]);
  ("g2u" ,["is_srcNAT_le_45916";"is_srcNAT_ge_45916"]);
  ("x2p",["is_srcPort_le_36887";"is_srcPort_ge_36887"]);
  ("z9yc" ,["is_srcNAT_le_63451";"is_srcNAT_ge_63451"]);
  ("56",["is_srcPort_le_1939";"is_srcPort_ge_1939"]);
  ("di1" ,["is_srcNAT_le_33288";"is_srcNAT_ge_33288"]);
  ("3w30",["is_srcPort_le_50281";"is_srcPort_ge_50281"]);
  ("6q" ,["is_srcNAT_le_33175";"is_srcNAT_ge_33175"]);
  ("bbj4",["is_srcNAT_le_51448";"is_srcNAT_ge_51448"]);
  ("0g6" ,["is_srcPort_le_56710";"is_srcPort_ge_56710"]);
  ("0o9v",["is_srcNAT_le_57885";"is_srcNAT_ge_57885"]);
  ("to61" ,["is_srcPort_le_48488";"is_srcPort_ge_48488"]);
  ("9wii",["is_srcNAT_le_26104";"is_srcNAT_ge_26104"]);
  ("eqq" ,["is_srcPort_le_50691";"is_srcPort_ge_50691"]);
  ("vk",["is_srcNAT_le_62082";"is_srcNAT_ge_62082"]);
  ("v6io" ,["is_srcPort_le_50693";"is_srcPort_ge_50693"]);
  ("wm",["is_srcNAT_le_54649";"is_srcNAT_ge_54649"]);
  ("3l" ,["is_srcPort_le_1940";"is_srcPort_ge_1940"]);
  ("gn",["is_srcNAT_le_23603";"is_srcNAT_ge_23603"]);
  ("i2u" ,["is_srcPort_le_50172";"is_srcPort_ge_50172"]);
  ("4h",["is_srcNAT_le_37056";"is_srcNAT_ge_37056"])
]``;












(****************************************)


(********************)
(*  Testing scripts *)
(********************)

(* BDD alists + EVAL *)

(* 
val final_thm_res_eval =
fwd_proofLib.convert_arith_policy_to_interval_tables (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order); 
*)


(* BDD alists + Cakeml w parser, just bin *)
val final_thm_res_cake = fwd_proof_cakeLib.convert_arith_policy_to_interval_tables_cake (arith_policy, policy_me, test_pd_type, policy_full_order, policy_order, 
"internet_firewall_25");



                      
val _ = export_theory ();
