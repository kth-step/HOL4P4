open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib; 


val _ = new_theory "internet_firewall_20";

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
]”;


(*
(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002";"is_srcPort_le_51465";"is_srcPort_ge_51465";"is_srcPort_le_60513";"is_srcPort_ge_60513";"is_srcPort_le_50049";"is_srcPort_ge_50049";"is_srcPort_le_52244";"is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627";"is_srcPort_le_43676";"is_srcPort_ge_43676";"is_srcPort_le_52190";"is_srcPort_ge_52190";"is_srcPort_le_50690";"is_srcPort_ge_50690";"is_srcPort_le_55597";"is_srcPort_ge_55597";"is_srcPort_le_49164";"is_srcPort_ge_49164";"is_srcPort_le_36887";"is_srcPort_ge_36887";"is_srcPort_le_1939";"is_srcPort_ge_1939";"is_srcPort_le_50281";"is_srcPort_ge_50281";"is_srcPort_le_56710";"is_srcPort_ge_56710"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321";"is_dstPort_le_443";"is_dstPort_ge_443";"is_dstPort_le_47094";"is_dstPort_ge_47094";"is_dstPort_le_58774";"is_dstPort_ge_58774";"is_dstPort_le_80";"is_dstPort_ge_80"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553";"is_srcNAT_le_45848";"is_srcNAT_ge_45848";"is_srcNAT_le_39975";"is_srcNAT_ge_39975";"is_srcNAT_le_45469";"is_srcNAT_ge_45469";"is_srcNAT_le_21285";"is_srcNAT_ge_21285";"is_srcNAT_le_2211";"is_srcNAT_ge_2211";"is_srcNAT_le_16215";"is_srcNAT_ge_16215";"is_srcNAT_le_45378";"is_srcNAT_ge_45378";"is_srcNAT_le_16680";"is_srcNAT_ge_16680";"is_srcNAT_le_20479";"is_srcNAT_ge_20479";"is_srcNAT_le_45448";"is_srcNAT_ge_45448";"is_srcNAT_le_45916";"is_srcNAT_ge_45916";"is_srcNAT_le_63451";"is_srcNAT_ge_63451";"is_srcNAT_le_33288";"is_srcNAT_ge_33288";"is_srcNAT_le_33175";"is_srcNAT_ge_33175";"is_srcNAT_le_51448";"is_srcNAT_ge_51448";"is_srcNAT_le_57885";"is_srcNAT_ge_57885"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321";"is_dstNAT_le_443";"is_dstNAT_ge_443";"is_dstNAT_le_47094";"is_dstNAT_ge_47094";"is_dstNAT_le_58774";"is_dstNAT_ge_58774";"is_dstNAT_le_80";"is_dstNAT_ge_80"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002"; "is_srcPort_ge_50002"; "is_srcPort_le_51465"; "is_srcPort_ge_51465"; "is_srcPort_le_60513"; "is_srcPort_ge_60513"; "is_srcPort_le_50049"; "is_srcPort_ge_50049"; "is_srcPort_le_52244"; "is_srcPort_ge_52244"; "is_srcPort_le_50627"; "is_srcPort_ge_50627"; "is_srcPort_le_43676"; "is_srcPort_ge_43676"; "is_srcPort_le_52190"; "is_srcPort_ge_52190"; "is_srcPort_le_50690"; "is_srcPort_ge_50690"; "is_srcPort_le_55597"; "is_srcPort_ge_55597"; "is_srcPort_le_49164"; "is_srcPort_ge_49164"; "is_srcPort_le_36887"; "is_srcPort_ge_36887"; "is_srcPort_le_1939"; "is_srcPort_ge_1939"; "is_srcPort_le_50281"; "is_srcPort_ge_50281"; "is_srcPort_le_56710"; "is_srcPort_ge_56710"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_dstPort_le_443"; "is_dstPort_ge_443"; "is_dstPort_le_47094"; "is_dstPort_ge_47094"; "is_dstPort_le_58774"; "is_dstPort_ge_58774"; "is_dstPort_le_80"; "is_dstPort_ge_80"; "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; "is_srcNAT_le_45848"; "is_srcNAT_ge_45848"; "is_srcNAT_le_39975"; "is_srcNAT_ge_39975"; "is_srcNAT_le_45469"; "is_srcNAT_ge_45469"; "is_srcNAT_le_21285"; "is_srcNAT_ge_21285"; "is_srcNAT_le_2211"; "is_srcNAT_ge_2211"; "is_srcNAT_le_16215"; "is_srcNAT_ge_16215"; "is_srcNAT_le_45378"; "is_srcNAT_ge_45378"; "is_srcNAT_le_16680"; "is_srcNAT_ge_16680"; "is_srcNAT_le_20479"; "is_srcNAT_ge_20479"; "is_srcNAT_le_45448"; "is_srcNAT_ge_45448"; "is_srcNAT_le_45916"; "is_srcNAT_ge_45916"; "is_srcNAT_le_63451"; "is_srcNAT_ge_63451"; "is_srcNAT_le_33288"; "is_srcNAT_ge_33288"; "is_srcNAT_le_33175"; "is_srcNAT_ge_33175"; "is_srcNAT_le_51448"; "is_srcNAT_ge_51448"; "is_srcNAT_le_57885"; "is_srcNAT_ge_57885"; "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321"; "is_dstNAT_le_443"; "is_dstNAT_ge_443"; "is_dstNAT_le_47094"; "is_dstNAT_ge_47094"; "is_dstNAT_le_58774"; "is_dstNAT_ge_58774"; "is_dstNAT_le_80"; "is_dstNAT_ge_80"]”;
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
  "is_srcNAT_le_57885"; "is_srcNAT_ge_57885"
]``;

val policy_full_order = ``[
  ("r8zh",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("hs" ,["is_dstPort_le_53";"is_dstPort_ge_53"]);
  ("efz",["is_srcNAT_le_54587";"is_srcNAT_ge_54587"]);
  ("eh" ,["is_dstNAT_le_53";"is_dstNAT_ge_53"]);
  ("ec",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("j14" ,["is_dstPort_le_3389";"is_dstPort_ge_3389"]);
  ("o5",["is_srcNAT_le_56258";"is_srcNAT_ge_56258"]);
  ("fq8c" ,["is_dstNAT_le_3389";"is_dstNAT_ge_3389"]);
  ("hr",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("2ce" ,["is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("4ypo",["is_srcNAT_le_43265";"is_srcNAT_ge_43265"]);
  ("z4" ,["is_dstNAT_le_50321";"is_dstNAT_ge_50321"]);
  ("ff0l",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("ko" ,["is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
  ("bfn",["is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("pt" ,["is_dstPort_le_443";"is_dstPort_ge_443"]);
  ("rjc4",["is_srcNAT_le_45848";"is_srcNAT_ge_45848"]);
  ("k0rz" ,["is_dstNAT_le_443";"is_dstNAT_ge_443"]);
  ("gkcv",["is_srcPort_le_51465";"is_srcPort_ge_51465"]);
  ("rr" ,["is_srcNAT_le_39975";"is_srcNAT_ge_39975"]);
  ("dso",["is_srcPort_le_60513";"is_srcPort_ge_60513"]);
  ("b6k" ,["is_dstPort_le_47094";"is_dstPort_ge_47094"]);
  ("js",["is_srcNAT_le_45469";"is_srcNAT_ge_45469"]);
  ("wezw" ,["is_dstNAT_le_47094";"is_dstNAT_ge_47094"]);
  ("lw",["is_srcPort_le_50049";"is_srcPort_ge_50049"]);
  ("qbz" ,["is_srcNAT_le_21285";"is_srcNAT_ge_21285"]);
  ("to7",["is_srcPort_le_52244";"is_srcPort_ge_52244"]);
  ("ioq" ,["is_dstPort_le_58774";"is_dstPort_ge_58774"]);
  ("3y96",["is_srcNAT_le_2211";"is_srcNAT_ge_2211"]);
  ("07z" ,["is_dstNAT_le_58774";"is_dstNAT_ge_58774"]);
  ("n13r",["is_srcPort_le_50627";"is_srcPort_ge_50627"]);
  ("e7" ,["is_srcNAT_le_16215";"is_srcNAT_ge_16215"]);
  ("peu",["is_srcPort_le_43676";"is_srcPort_ge_43676"]);
  ("ox7" ,["is_dstPort_le_80";"is_dstPort_ge_80"]);
  ("xn8",["is_srcNAT_le_45378";"is_srcNAT_ge_45378"]);
  ("cwa" ,["is_dstNAT_le_80";"is_dstNAT_ge_80"]);
  ("fd8",["is_srcPort_le_52190";"is_srcPort_ge_52190"]);
  ("715" ,["is_srcNAT_le_16680";"is_srcNAT_ge_16680"]);
  ("9hjb",["is_srcPort_le_50690";"is_srcPort_ge_50690"]);
  ("zx77" ,["is_srcNAT_le_20479";"is_srcNAT_ge_20479"]);
  ("t00z",["is_srcPort_le_55597";"is_srcPort_ge_55597"]);
  ("0a2" ,["is_srcNAT_le_45448";"is_srcNAT_ge_45448"]);
  ("fv",["is_srcPort_le_49164";"is_srcPort_ge_49164"]);
  ("7y" ,["is_srcNAT_le_45916";"is_srcNAT_ge_45916"]);
  ("71s",["is_srcPort_le_36887";"is_srcPort_ge_36887"]);
  ("8h" ,["is_srcNAT_le_63451";"is_srcNAT_ge_63451"]);
  ("0jf",["is_srcPort_le_1939";"is_srcPort_ge_1939"]);
  ("r2v9" ,["is_srcNAT_le_33288";"is_srcNAT_ge_33288"]);
  ("7ui",["is_srcPort_le_50281";"is_srcPort_ge_50281"]);
  ("h5g" ,["is_srcNAT_le_33175";"is_srcNAT_ge_33175"]);
  ("7a",["is_srcNAT_le_51448";"is_srcNAT_ge_51448"]);
  ("2ch1" ,["is_srcPort_le_56710";"is_srcPort_ge_56710"]);
  ("05",["is_srcNAT_le_57885";"is_srcNAT_ge_57885"])
]``;


(************************************************)


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
"internet_firewall_20");



                      
val _ = export_theory ();
