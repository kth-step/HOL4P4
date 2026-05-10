open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "internet_firewall_50";

Type single_rule = “:((string# num list) action_expr) arith_rule”;

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

(* rule 26 *)

val is_srcPort_le_38802 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 38802 16))”;
val is_srcPort_ge_38802 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 38802 16))”;

val is_srcNAT_le_38802 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 38802 16))”;
val is_srcNAT_ge_38802 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 38802 16))”;


val arith_policy_rule26 = “((arith_and (arith_a ^is_srcPort_le_38802)
                          (arith_and (arith_a ^is_srcPort_ge_38802)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_38802)
                          (arith_and (arith_a ^is_srcNAT_ge_38802)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 27 *)

val is_srcNAT_le_8038 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 8038 16))”;
val is_srcNAT_ge_8038 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 8038 16))”;


val arith_policy_rule27 = “((arith_and (arith_a ^is_srcPort_le_50281)
                          (arith_and (arith_a ^is_srcPort_ge_50281)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_8038)
                          (arith_and (arith_a ^is_srcNAT_ge_8038)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 28 *)

val is_srcPort_le_50051 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50051 16))”;
val is_srcPort_ge_50051 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50051 16))”;

val is_srcNAT_le_1683 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 1683 16))”;
val is_srcNAT_ge_1683 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 1683 16))”;


val arith_policy_rule28 = “((arith_and (arith_a ^is_srcPort_le_50051)
                          (arith_and (arith_a ^is_srcPort_ge_50051)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_1683)
                          (arith_and (arith_a ^is_srcNAT_ge_1683)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 29 *)

val is_srcPort_le_52192 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52192 16))”;
val is_srcPort_ge_52192 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52192 16))”;

val is_srcNAT_le_41129 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 41129 16))”;
val is_srcNAT_ge_41129 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 41129 16))”;


val arith_policy_rule29 = “((arith_and (arith_a ^is_srcPort_le_52192)
                          (arith_and (arith_a ^is_srcPort_ge_52192)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_41129)
                          (arith_and (arith_a ^is_srcNAT_ge_41129)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 30 *)

val is_srcPort_le_57886 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57886 16))”;
val is_srcPort_ge_57886 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57886 16))”;

val is_srcNAT_le_10717 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 10717 16))”;
val is_srcNAT_ge_10717 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 10717 16))”;


val arith_policy_rule30 = “((arith_and (arith_a ^is_srcPort_le_57886)
                          (arith_and (arith_a ^is_srcPort_ge_57886)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_10717)
                          (arith_and (arith_a ^is_srcNAT_ge_10717)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 31 *)

val is_srcPort_le_50289 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50289 16))”;
val is_srcPort_ge_50289 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50289 16))”;

val is_srcNAT_le_7131 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 7131 16))”;
val is_srcNAT_ge_7131 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 7131 16))”;


val arith_policy_rule31 = “((arith_and (arith_a ^is_srcPort_le_50289)
                          (arith_and (arith_a ^is_srcPort_ge_50289)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_7131)
                          (arith_and (arith_a ^is_srcNAT_ge_7131)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 32 *)

val is_srcPort_le_58615 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 58615 16))”;
val is_srcPort_ge_58615 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 58615 16))”;

val is_srcNAT_le_30095 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 30095 16))”;
val is_srcNAT_ge_30095 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 30095 16))”;


val arith_policy_rule32 = “((arith_and (arith_a ^is_srcPort_le_58615)
                          (arith_and (arith_a ^is_srcPort_ge_58615)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_30095)
                          (arith_and (arith_a ^is_srcNAT_ge_30095)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 33 *)

val is_srcPort_le_38551 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 38551 16))”;
val is_srcPort_ge_38551 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 38551 16))”;

val is_srcNAT_le_14191 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 14191 16))”;
val is_srcNAT_ge_14191 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 14191 16))”;


val arith_policy_rule33 = “((arith_and (arith_a ^is_srcPort_le_38551)
                          (arith_and (arith_a ^is_srcPort_ge_38551)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_14191)
                          (arith_and (arith_a ^is_srcNAT_ge_14191)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 34 *)

val is_srcPort_le_64787 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 64787 16))”;
val is_srcPort_ge_64787 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 64787 16))”;

val is_srcNAT_le_29856 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 29856 16))”;
val is_srcNAT_ge_29856 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 29856 16))”;


val arith_policy_rule34 = “((arith_and (arith_a ^is_srcPort_le_64787)
                          (arith_and (arith_a ^is_srcPort_ge_64787)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_29856)
                          (arith_and (arith_a ^is_srcNAT_ge_29856)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 35 *)

val is_srcPort_le_34529 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 34529 16))”;
val is_srcPort_ge_34529 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 34529 16))”;

val is_srcNAT_le_30445 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 30445 16))”;
val is_srcNAT_ge_30445 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 30445 16))”;


val arith_policy_rule35 = “((arith_and (arith_a ^is_srcPort_le_34529)
                          (arith_and (arith_a ^is_srcPort_ge_34529)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_30445)
                          (arith_and (arith_a ^is_srcNAT_ge_30445)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 36 *)

val is_srcPort_le_52184 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52184 16))”;
val is_srcPort_ge_52184 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52184 16))”;

val is_srcNAT_le_13267 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 13267 16))”;
val is_srcNAT_ge_13267 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 13267 16))”;


val arith_policy_rule36 = “((arith_and (arith_a ^is_srcPort_le_52184)
                          (arith_and (arith_a ^is_srcPort_ge_52184)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_13267)
                          (arith_and (arith_a ^is_srcNAT_ge_13267)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 37 *)

val is_srcPort_le_60377 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60377 16))”;
val is_srcPort_ge_60377 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60377 16))”;

val is_srcNAT_le_34261 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 34261 16))”;
val is_srcNAT_ge_34261 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 34261 16))”;


val arith_policy_rule37 = “((arith_and (arith_a ^is_srcPort_le_60377)
                          (arith_and (arith_a ^is_srcPort_ge_60377)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_34261)
                          (arith_and (arith_a ^is_srcNAT_ge_34261)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 38 *)

val is_srcPort_le_59347 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 59347 16))”;
val is_srcPort_ge_59347 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 59347 16))”;

val is_srcNAT_le_59347 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 59347 16))”;
val is_srcNAT_ge_59347 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 59347 16))”;


val arith_policy_rule38 = “((arith_and (arith_a ^is_srcPort_le_59347)
                          (arith_and (arith_a ^is_srcPort_ge_59347)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_59347)
                          (arith_and (arith_a ^is_srcNAT_ge_59347)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 39 *)

val is_srcPort_le_50077 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50077 16))”;
val is_srcPort_ge_50077 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50077 16))”;

val is_srcNAT_le_40548 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 40548 16))”;
val is_srcNAT_ge_40548 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 40548 16))”;


val arith_policy_rule39 = “((arith_and (arith_a ^is_srcPort_le_50077)
                          (arith_and (arith_a ^is_srcPort_ge_50077)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_40548)
                          (arith_and (arith_a ^is_srcNAT_ge_40548)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 40 *)

val is_srcPort_le_50149 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50149 16))”;
val is_srcPort_ge_50149 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50149 16))”;

val is_srcNAT_le_2917 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2917 16))”;
val is_srcNAT_ge_2917 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2917 16))”;


val arith_policy_rule40 = “((arith_and (arith_a ^is_srcPort_le_50149)
                          (arith_and (arith_a ^is_srcPort_ge_50149)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_2917)
                          (arith_and (arith_a ^is_srcNAT_ge_2917)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 41 *)

val is_srcPort_le_50004 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50004 16))”;
val is_srcPort_ge_50004 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50004 16))”;

val is_srcNAT_le_10108 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 10108 16))”;
val is_srcNAT_ge_10108 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 10108 16))”;


val arith_policy_rule41 = “((arith_and (arith_a ^is_srcPort_le_50004)
                          (arith_and (arith_a ^is_srcPort_ge_50004)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_10108)
                          (arith_and (arith_a ^is_srcNAT_ge_10108)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 42 *)

val is_srcPort_le_60411 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60411 16))”;
val is_srcPort_ge_60411 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60411 16))”;

val is_srcNAT_le_48309 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 48309 16))”;
val is_srcNAT_ge_48309 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 48309 16))”;


val arith_policy_rule42 = “((arith_and (arith_a ^is_srcPort_le_60411)
                          (arith_and (arith_a ^is_srcPort_ge_60411)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_48309)
                          (arith_and (arith_a ^is_srcNAT_ge_48309)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 43 *)

val is_srcPort_le_60354 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60354 16))”;
val is_srcPort_ge_60354 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60354 16))”;

val is_srcNAT_le_7611 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 7611 16))”;
val is_srcNAT_ge_7611 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 7611 16))”;


val arith_policy_rule43 = “((arith_and (arith_a ^is_srcPort_le_60354)
                          (arith_and (arith_a ^is_srcPort_ge_60354)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_7611)
                          (arith_and (arith_a ^is_srcNAT_ge_7611)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 44 *)

val is_srcPort_le_60399 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60399 16))”;
val is_srcPort_ge_60399 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60399 16))”;

val is_srcNAT_le_36861 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 36861 16))”;
val is_srcNAT_ge_36861 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 36861 16))”;


val arith_policy_rule44 = “((arith_and (arith_a ^is_srcPort_le_60399)
                          (arith_and (arith_a ^is_srcPort_ge_60399)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_36861)
                          (arith_and (arith_a ^is_srcNAT_ge_36861)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 45 *)

val is_srcPort_le_60348 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60348 16))”;
val is_srcPort_ge_60348 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60348 16))”;

val is_srcNAT_le_15161 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 15161 16))”;
val is_srcNAT_ge_15161 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 15161 16))”;


val arith_policy_rule45 = “((arith_and (arith_a ^is_srcPort_le_60348)
                          (arith_and (arith_a ^is_srcPort_ge_60348)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_15161)
                          (arith_and (arith_a ^is_srcNAT_ge_15161)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 46 *)

val is_srcPort_le_60420 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60420 16))”;
val is_srcPort_ge_60420 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60420 16))”;

val is_srcNAT_le_1065 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 1065 16))”;
val is_srcNAT_ge_1065 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 1065 16))”;


val arith_policy_rule46 = “((arith_and (arith_a ^is_srcPort_le_60420)
                          (arith_and (arith_a ^is_srcPort_ge_60420)
                          (arith_and (arith_a ^is_dstPort_le_80)
                          (arith_and (arith_a ^is_dstPort_ge_80)
                          (arith_and (arith_a ^is_srcNAT_le_1065)
                          (arith_and (arith_a ^is_srcNAT_ge_1065)
                          (arith_and (arith_a ^is_dstNAT_le_80)
                                   (arith_a ^is_dstNAT_ge_80)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 47 *)

val is_srcPort_le_60423 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60423 16))”;
val is_srcPort_ge_60423 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60423 16))”;

val is_srcNAT_le_61729 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 61729 16))”;
val is_srcNAT_ge_61729 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 61729 16))”;


val arith_policy_rule47 = “((arith_and (arith_a ^is_srcPort_le_60423)
                          (arith_and (arith_a ^is_srcPort_ge_60423)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_61729)
                          (arith_and (arith_a ^is_srcNAT_ge_61729)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 48 *)

val is_srcPort_le_60360 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60360 16))”;
val is_srcPort_ge_60360 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60360 16))”;

val is_srcNAT_le_62556 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 62556 16))”;
val is_srcNAT_ge_62556 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 62556 16))”;


val arith_policy_rule48 = “((arith_and (arith_a ^is_srcPort_le_60360)
                          (arith_and (arith_a ^is_srcPort_ge_60360)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_62556)
                          (arith_and (arith_a ^is_srcNAT_ge_62556)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 49 *)

val is_srcPort_le_60363 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60363 16))”;
val is_srcPort_ge_60363 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60363 16))”;

val is_srcNAT_le_28558 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 28558 16))”;
val is_srcNAT_ge_28558 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 28558 16))”;


val arith_policy_rule49 = “((arith_and (arith_a ^is_srcPort_le_60363)
                          (arith_and (arith_a ^is_srcPort_ge_60363)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_28558)
                          (arith_and (arith_a ^is_srcNAT_ge_28558)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
                           action ("allow",[])):single_rule”;

(* rule 50 *)

val is_srcPort_le_9523 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 9523 16))”;
val is_srcPort_ge_9523 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 9523 16))”;

val is_srcNAT_le_27776 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 27776 16))”;
val is_srcNAT_ge_27776 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 27776 16))”;


val arith_policy_rule50 = “((arith_and (arith_a ^is_srcPort_le_9523)
                          (arith_and (arith_a ^is_srcPort_ge_9523)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_27776)
                          (arith_and (arith_a ^is_srcNAT_ge_27776)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))) ,
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
    ^arith_policy_rule26;
    ^arith_policy_rule27;
    ^arith_policy_rule28;
    ^arith_policy_rule29;
    ^arith_policy_rule30;
    ^arith_policy_rule31;
    ^arith_policy_rule32;
    ^arith_policy_rule33;
    ^arith_policy_rule34;
    ^arith_policy_rule35;
    ^arith_policy_rule36;
    ^arith_policy_rule37;
    ^arith_policy_rule38;
    ^arith_policy_rule39;
    ^arith_policy_rule40;
    ^arith_policy_rule41;
    ^arith_policy_rule42;
    ^arith_policy_rule43;
    ^arith_policy_rule44;
    ^arith_policy_rule45;
    ^arith_policy_rule46;
    ^arith_policy_rule47;
    ^arith_policy_rule48;
    ^arith_policy_rule49;
    ^arith_policy_rule50;
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
    ("is_srcPort_le_38802", ^is_srcPort_le_38802);
    ("is_srcPort_ge_38802", ^is_srcPort_ge_38802);
    ("is_srcNAT_le_38802", ^is_srcNAT_le_38802);
    ("is_srcNAT_ge_38802", ^is_srcNAT_ge_38802);
    ("is_srcNAT_le_8038", ^is_srcNAT_le_8038);
    ("is_srcNAT_ge_8038", ^is_srcNAT_ge_8038);
    ("is_srcPort_le_50051", ^is_srcPort_le_50051);
    ("is_srcPort_ge_50051", ^is_srcPort_ge_50051);
    ("is_srcNAT_le_1683", ^is_srcNAT_le_1683);
    ("is_srcNAT_ge_1683", ^is_srcNAT_ge_1683);
    ("is_srcPort_le_52192", ^is_srcPort_le_52192);
    ("is_srcPort_ge_52192", ^is_srcPort_ge_52192);
    ("is_srcNAT_le_41129", ^is_srcNAT_le_41129);
    ("is_srcNAT_ge_41129", ^is_srcNAT_ge_41129);
    ("is_srcPort_le_57886", ^is_srcPort_le_57886);
    ("is_srcPort_ge_57886", ^is_srcPort_ge_57886);
    ("is_srcNAT_le_10717", ^is_srcNAT_le_10717);
    ("is_srcNAT_ge_10717", ^is_srcNAT_ge_10717);
    ("is_srcPort_le_50289", ^is_srcPort_le_50289);
    ("is_srcPort_ge_50289", ^is_srcPort_ge_50289);
    ("is_srcNAT_le_7131", ^is_srcNAT_le_7131);
    ("is_srcNAT_ge_7131", ^is_srcNAT_ge_7131);
    ("is_srcPort_le_58615", ^is_srcPort_le_58615);
    ("is_srcPort_ge_58615", ^is_srcPort_ge_58615);
    ("is_srcNAT_le_30095", ^is_srcNAT_le_30095);
    ("is_srcNAT_ge_30095", ^is_srcNAT_ge_30095);
    ("is_srcPort_le_38551", ^is_srcPort_le_38551);
    ("is_srcPort_ge_38551", ^is_srcPort_ge_38551);
    ("is_srcNAT_le_14191", ^is_srcNAT_le_14191);
    ("is_srcNAT_ge_14191", ^is_srcNAT_ge_14191);
    ("is_srcPort_le_64787", ^is_srcPort_le_64787);
    ("is_srcPort_ge_64787", ^is_srcPort_ge_64787);
    ("is_srcNAT_le_29856", ^is_srcNAT_le_29856);
    ("is_srcNAT_ge_29856", ^is_srcNAT_ge_29856);
    ("is_srcPort_le_34529", ^is_srcPort_le_34529);
    ("is_srcPort_ge_34529", ^is_srcPort_ge_34529);
    ("is_srcNAT_le_30445", ^is_srcNAT_le_30445);
    ("is_srcNAT_ge_30445", ^is_srcNAT_ge_30445);
    ("is_srcPort_le_52184", ^is_srcPort_le_52184);
    ("is_srcPort_ge_52184", ^is_srcPort_ge_52184);
    ("is_srcNAT_le_13267", ^is_srcNAT_le_13267);
    ("is_srcNAT_ge_13267", ^is_srcNAT_ge_13267);
    ("is_srcPort_le_60377", ^is_srcPort_le_60377);
    ("is_srcPort_ge_60377", ^is_srcPort_ge_60377);
    ("is_srcNAT_le_34261", ^is_srcNAT_le_34261);
    ("is_srcNAT_ge_34261", ^is_srcNAT_ge_34261);
    ("is_srcPort_le_59347", ^is_srcPort_le_59347);
    ("is_srcPort_ge_59347", ^is_srcPort_ge_59347);
    ("is_srcNAT_le_59347", ^is_srcNAT_le_59347);
    ("is_srcNAT_ge_59347", ^is_srcNAT_ge_59347);
    ("is_srcPort_le_50077", ^is_srcPort_le_50077);
    ("is_srcPort_ge_50077", ^is_srcPort_ge_50077);
    ("is_srcNAT_le_40548", ^is_srcNAT_le_40548);
    ("is_srcNAT_ge_40548", ^is_srcNAT_ge_40548);
    ("is_srcPort_le_50149", ^is_srcPort_le_50149);
    ("is_srcPort_ge_50149", ^is_srcPort_ge_50149);
    ("is_srcNAT_le_2917", ^is_srcNAT_le_2917);
    ("is_srcNAT_ge_2917", ^is_srcNAT_ge_2917);
    ("is_srcPort_le_50004", ^is_srcPort_le_50004);
    ("is_srcPort_ge_50004", ^is_srcPort_ge_50004);
    ("is_srcNAT_le_10108", ^is_srcNAT_le_10108);
    ("is_srcNAT_ge_10108", ^is_srcNAT_ge_10108);
    ("is_srcPort_le_60411", ^is_srcPort_le_60411);
    ("is_srcPort_ge_60411", ^is_srcPort_ge_60411);
    ("is_srcNAT_le_48309", ^is_srcNAT_le_48309);
    ("is_srcNAT_ge_48309", ^is_srcNAT_ge_48309);
    ("is_srcPort_le_60354", ^is_srcPort_le_60354);
    ("is_srcPort_ge_60354", ^is_srcPort_ge_60354);
    ("is_srcNAT_le_7611", ^is_srcNAT_le_7611);
    ("is_srcNAT_ge_7611", ^is_srcNAT_ge_7611);
    ("is_srcPort_le_60399", ^is_srcPort_le_60399);
    ("is_srcPort_ge_60399", ^is_srcPort_ge_60399);
    ("is_srcNAT_le_36861", ^is_srcNAT_le_36861);
    ("is_srcNAT_ge_36861", ^is_srcNAT_ge_36861);
    ("is_srcPort_le_60348", ^is_srcPort_le_60348);
    ("is_srcPort_ge_60348", ^is_srcPort_ge_60348);
    ("is_srcNAT_le_15161", ^is_srcNAT_le_15161);
    ("is_srcNAT_ge_15161", ^is_srcNAT_ge_15161);
    ("is_srcPort_le_60420", ^is_srcPort_le_60420);
    ("is_srcPort_ge_60420", ^is_srcPort_ge_60420);
    ("is_srcNAT_le_1065", ^is_srcNAT_le_1065);
    ("is_srcNAT_ge_1065", ^is_srcNAT_ge_1065);
    ("is_srcPort_le_60423", ^is_srcPort_le_60423);
    ("is_srcPort_ge_60423", ^is_srcPort_ge_60423);
    ("is_srcNAT_le_61729", ^is_srcNAT_le_61729);
    ("is_srcNAT_ge_61729", ^is_srcNAT_ge_61729);
    ("is_srcPort_le_60360", ^is_srcPort_le_60360);
    ("is_srcPort_ge_60360", ^is_srcPort_ge_60360);
    ("is_srcNAT_le_62556", ^is_srcNAT_le_62556);
    ("is_srcNAT_ge_62556", ^is_srcNAT_ge_62556);
    ("is_srcPort_le_60363", ^is_srcPort_le_60363);
    ("is_srcPort_ge_60363", ^is_srcPort_ge_60363);
    ("is_srcNAT_le_28558", ^is_srcNAT_le_28558);
    ("is_srcNAT_ge_28558", ^is_srcNAT_ge_28558);
    ("is_srcPort_le_9523", ^is_srcPort_le_9523);
    ("is_srcPort_ge_9523", ^is_srcPort_ge_9523);
    ("is_srcNAT_le_27776", ^is_srcNAT_le_27776);
    ("is_srcNAT_ge_27776", ^is_srcNAT_ge_27776);
]”;



val policy_order = “[
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
  "is_srcNAT_le_37056"; "is_srcNAT_ge_37056";
  "is_srcPort_le_38802"; "is_srcPort_ge_38802";
  "is_srcNAT_le_38802"; "is_srcNAT_ge_38802";
  "is_srcNAT_le_8038"; "is_srcNAT_ge_8038";
  "is_srcPort_le_50051"; "is_srcPort_ge_50051";
  "is_srcNAT_le_1683"; "is_srcNAT_ge_1683";
  "is_srcPort_le_52192"; "is_srcPort_ge_52192";
  "is_srcNAT_le_41129"; "is_srcNAT_ge_41129";
  "is_srcPort_le_57886"; "is_srcPort_ge_57886";
  "is_srcNAT_le_10717"; "is_srcNAT_ge_10717";
  "is_srcPort_le_50289"; "is_srcPort_ge_50289";
  "is_srcNAT_le_7131"; "is_srcNAT_ge_7131";
  "is_srcPort_le_58615"; "is_srcPort_ge_58615";
  "is_srcNAT_le_30095"; "is_srcNAT_ge_30095";
  "is_srcPort_le_38551"; "is_srcPort_ge_38551";
  "is_srcNAT_le_14191"; "is_srcNAT_ge_14191";
  "is_srcPort_le_64787"; "is_srcPort_ge_64787";
  "is_srcNAT_le_29856"; "is_srcNAT_ge_29856";
  "is_srcPort_le_34529"; "is_srcPort_ge_34529";
  "is_srcNAT_le_30445"; "is_srcNAT_ge_30445";
  "is_srcPort_le_52184"; "is_srcPort_ge_52184";
  "is_srcNAT_le_13267"; "is_srcNAT_ge_13267";
  "is_srcPort_le_60377"; "is_srcPort_ge_60377";
  "is_srcNAT_le_34261"; "is_srcNAT_ge_34261";
  "is_srcPort_le_59347"; "is_srcPort_ge_59347";
  "is_srcNAT_le_59347"; "is_srcNAT_ge_59347";
  "is_srcPort_le_50077"; "is_srcPort_ge_50077";
  "is_srcNAT_le_40548"; "is_srcNAT_ge_40548";
  "is_srcPort_le_50149"; "is_srcPort_ge_50149";
  "is_srcNAT_le_2917"; "is_srcNAT_ge_2917";
  "is_srcPort_le_50004"; "is_srcPort_ge_50004";
  "is_srcNAT_le_10108"; "is_srcNAT_ge_10108";
  "is_srcPort_le_60411"; "is_srcPort_ge_60411";
  "is_srcNAT_le_48309"; "is_srcNAT_ge_48309";
  "is_srcPort_le_60354"; "is_srcPort_ge_60354";
  "is_srcNAT_le_7611"; "is_srcNAT_ge_7611";
  "is_srcPort_le_60399"; "is_srcPort_ge_60399";
  "is_srcNAT_le_36861"; "is_srcNAT_ge_36861";
  "is_srcPort_le_60348"; "is_srcPort_ge_60348";
  "is_srcNAT_le_15161"; "is_srcNAT_ge_15161";
  "is_srcPort_le_60420"; "is_srcPort_ge_60420";
  "is_srcNAT_le_1065"; "is_srcNAT_ge_1065";
  "is_srcPort_le_60423"; "is_srcPort_ge_60423";
  "is_srcNAT_le_61729"; "is_srcNAT_ge_61729";
  "is_srcPort_le_60360"; "is_srcPort_ge_60360";
  "is_srcNAT_le_62556"; "is_srcNAT_ge_62556";
  "is_srcPort_le_60363"; "is_srcPort_ge_60363";
  "is_srcNAT_le_28558"; "is_srcNAT_ge_28558";
  "is_srcPort_le_9523"; "is_srcPort_ge_9523";
  "is_srcNAT_le_27776"; "is_srcNAT_ge_27776"
]”;

(************************************************)


(********************)
(*  Testing scripts *)
(********************)


(* create an MTBDD using CakeML bin *)
val final_bdd = bdd_policy_cakeLib.convert_arith_policy_to_bdd (arith_policy, policy_me, test_pd_type, policy_order,
"internet_firewall_50");



val _ = export_theory ();