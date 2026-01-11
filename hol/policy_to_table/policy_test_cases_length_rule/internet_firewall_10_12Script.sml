open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;  


val _ = new_theory "internet_firewall_10_12";

val _ = type_abbrev("single_rule", “:((string# num list) action_expr) arith_rule”);
 
val test_pd_type = “[("h", type_record [("srcPort", type_length 16);
                                        ("dstPort", type_length 16);
                                        ("srcNAT", type_length 16);
                                        ("dstNAT", type_length 16);
                                        ("ttl", type_length 8);
                                        ("length", type_length 8)
                                        ])]”;

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

val is_ttl_le_10 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 10 8))”;
val is_ttl_ge_10 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 10 8))”;

val is_length_le_10 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 10 8))”;
val is_length_ge_10 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 10 8))”;

val arith_policy_rule1 = “(
                          (arith_and (arith_a ^is_length_le_10)
                          (arith_and (arith_a ^is_length_ge_10)
                          (arith_and (arith_a ^is_ttl_le_10)
                          (arith_and (arith_a ^is_ttl_ge_10)
                          (arith_and (arith_a ^is_srcPort_le_57222)
                          (arith_and (arith_a ^is_srcPort_ge_57222)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          (arith_and (arith_a ^is_dstPort_ge_53)
                          (arith_and (arith_a ^is_srcNAT_le_54587)
                          (arith_and (arith_a ^is_srcNAT_ge_54587)
                          (arith_and (arith_a ^is_dstNAT_le_53)
                                   (arith_a ^is_dstNAT_ge_53)))))))))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 2 *)

val is_srcPort_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcPort_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstPort_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstPort_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;

val is_srcNAT_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcNAT_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstNAT_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstNAT_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 3389 16))”;

val is_ttl_le_11 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 11 8))”;
val is_ttl_ge_11 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 11 8))”;

val is_length_le_11 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 11 8))”;
val is_length_ge_11 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 11 8))”;

val arith_policy_rule2 = “(
                          (arith_and (arith_a ^is_length_le_11)
                          (arith_and (arith_a ^is_length_ge_11)
                          (arith_and (arith_a ^is_ttl_le_11)
                          (arith_and (arith_a ^is_ttl_ge_11)
                          (arith_and (arith_a ^is_srcPort_le_56258)
                          (arith_and (arith_a ^is_srcPort_ge_56258)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_56258)
                          (arith_and (arith_a ^is_srcNAT_ge_56258)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))))))) ,
                           action ("allow",[2])):single_rule”;

(* rule 3 *)

val is_srcPort_le_6881 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;
val is_srcPort_ge_6881 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;

val is_dstPort_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstPort_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;

val is_srcNAT_le_43265 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;
val is_srcNAT_ge_43265 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 43265 16))”;

val is_dstNAT_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstNAT_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 50321 16))”;

val is_ttl_le_12 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 12 8))”;
val is_ttl_ge_12 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 12 8))”;

val is_length_le_12 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 12 8))”;
val is_length_ge_12 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 12 8))”;


val arith_policy_rule3 = “(
                          (arith_and (arith_a ^is_length_le_12)
                          (arith_and (arith_a ^is_length_ge_12)
                          (arith_and (arith_a ^is_ttl_le_12)
                          (arith_and (arith_a ^is_ttl_ge_12)
                          (arith_and (arith_a ^is_srcPort_le_6881)
                          (arith_and (arith_a ^is_srcPort_ge_6881)
                          (arith_and (arith_a ^is_dstPort_le_50321)
                          (arith_and (arith_a ^is_dstPort_ge_50321)
                          (arith_and (arith_a ^is_srcNAT_le_43265)
                          (arith_and (arith_a ^is_srcNAT_ge_43265)
                          (arith_and (arith_a ^is_dstNAT_le_50321)
                                   (arith_a ^is_dstNAT_ge_50321)))))))))))) ,
                           action ("allow",[3])):single_rule”;

(* rule 4 *)

val is_srcPort_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcPort_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;

val is_srcNAT_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcNAT_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 50553 16))”;

val is_ttl_le_13 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 13 8))”;
val is_ttl_ge_13 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 13 8))”;

val is_length_le_13 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 13 8))”;
val is_length_ge_13 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 13 8))”;

val arith_policy_rule4 = “(
                          (arith_and (arith_a ^is_length_le_13)
                          (arith_and (arith_a ^is_length_ge_13)
                          (arith_and (arith_a ^is_ttl_le_13)
                          (arith_and (arith_a ^is_ttl_ge_13)
                          (arith_and (arith_a ^is_srcPort_le_50553)
                          (arith_and (arith_a ^is_srcPort_ge_50553)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_50553)
                          (arith_and (arith_a ^is_srcNAT_ge_50553)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))))))) ,
                           action ("allow",[4])):single_rule”;

(* rule 5 *)

val is_srcPort_le_50002 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;
val is_srcPort_ge_50002 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;

val is_dstPort_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstPort_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;

val is_srcNAT_le_45848 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;
val is_srcNAT_ge_45848 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45848 16))”;

val is_dstNAT_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstNAT_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 443 16))”;


val arith_policy_rule5 = “(
                          (arith_and (arith_a ^is_length_le_11)
                          (arith_and (arith_a ^is_length_ge_11)
                          (arith_and (arith_a ^is_ttl_le_11)
                          (arith_and (arith_a ^is_ttl_ge_11)
                          (arith_and (arith_a ^is_srcPort_le_50002)
                          (arith_and (arith_a ^is_srcPort_ge_50002)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_45848)
                          (arith_and (arith_a ^is_srcNAT_ge_45848)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))))))) ,
                           action ("allow",[5])):single_rule”;

(* rule 6 *)

val is_srcPort_le_51465 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;
val is_srcPort_ge_51465 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;

val is_srcNAT_le_39975 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 39975 16))”;
val is_srcNAT_ge_39975 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 39975 16))”;

val is_ttl_le_14 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 14 8))”;
val is_ttl_ge_14 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 14 8))”;

val is_length_le_14 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 14 8))”;
val is_length_ge_14 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 14 8))”;

val arith_policy_rule6 = “(
                          (arith_and (arith_a ^is_length_le_14)
                          (arith_and (arith_a ^is_length_ge_14)
                          (arith_and (arith_a ^is_ttl_le_14)
                          (arith_and (arith_a ^is_ttl_ge_14)
                          (arith_and (arith_a ^is_srcPort_le_51465)
                          (arith_and (arith_a ^is_srcPort_ge_51465)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_39975)
                          (arith_and (arith_a ^is_srcNAT_ge_39975)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))))))) ,
                           action ("allow",[6])):single_rule”;

(* rule 7 *)

val is_srcPort_le_60513 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;
val is_srcPort_ge_60513 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;

val is_dstPort_le_47094 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;
val is_dstPort_ge_47094 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;

val is_srcNAT_le_45469 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45469 16))”;
val is_srcNAT_ge_45469 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 45469 16))”;

val is_dstNAT_le_47094 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 47094 16))”;
val is_dstNAT_ge_47094 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 47094 16))”;

val is_ttl_le_15 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 15 8))”;
val is_ttl_ge_15 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 15 8))”;

val is_length_le_15 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 15 8))”;
val is_length_ge_15 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 15 8))”;

val arith_policy_rule7 = “(
                          (arith_and (arith_a ^is_length_le_15)
                          (arith_and (arith_a ^is_length_ge_15)
                          (arith_and (arith_a ^is_ttl_le_15)
                          (arith_and (arith_a ^is_ttl_ge_15)
                          (arith_and (arith_a ^is_srcPort_le_60513)
                          (arith_and (arith_a ^is_srcPort_ge_60513)
                          (arith_and (arith_a ^is_dstPort_le_47094)
                          (arith_and (arith_a ^is_dstPort_ge_47094)
                          (arith_and (arith_a ^is_srcNAT_le_45469)
                          (arith_and (arith_a ^is_srcNAT_ge_45469)
                          (arith_and (arith_a ^is_dstNAT_le_47094)
                                   (arith_a ^is_dstNAT_ge_47094)))))))))))) ,
                           action ("allow",[7])):single_rule”;

(* rule 8 *)

val is_srcPort_le_50049 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;
val is_srcPort_ge_50049 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;

val is_srcNAT_le_21285 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 21285 16))”;
val is_srcNAT_ge_21285 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 21285 16))”;

val is_ttl_le_16 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 16 8))”;
val is_ttl_ge_16 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 16 8))”;

val is_length_le_16 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 16 8))”;
val is_length_ge_16 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 16 8))”;

val arith_policy_rule8 = “(
                          (arith_and (arith_a ^is_length_le_16)
                          (arith_and (arith_a ^is_length_ge_16)
                          (arith_and (arith_a ^is_ttl_le_16)
                          (arith_and (arith_a ^is_ttl_ge_16)
                          (arith_and (arith_a ^is_srcPort_le_50049)
                          (arith_and (arith_a ^is_srcPort_ge_50049)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_21285)
                          (arith_and (arith_a ^is_srcNAT_ge_21285)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))))))) ,
                           action ("allow",[8])):single_rule”;

(* rule 9 *)

val is_srcPort_le_52244 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;
val is_srcPort_ge_52244 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;

val is_dstPort_le_58774 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;
val is_dstPort_ge_58774 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;

val is_srcNAT_le_2211 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2211 16))”;
val is_srcNAT_ge_2211 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 2211 16))”;

val is_dstNAT_le_58774 = “(arithm_le (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 58774 16))”;
val is_dstNAT_ge_58774 = “(arithm_ge (lv_acc (lv_x "h") "dstNAT") ^(bdd_utilsLib.make_bv 58774 16))”;

val is_ttl_le_17 = “(arithm_le (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 17 8))”;
val is_ttl_ge_17 = “(arithm_ge (lv_acc (lv_x "h") "ttl") ^(bdd_utilsLib.make_bv 17 8))”;

val is_length_le_17 = “(arithm_le (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 17 8))”;
val is_length_ge_17 = “(arithm_ge (lv_acc (lv_x "h") "length") ^(bdd_utilsLib.make_bv 17 8))”;

val arith_policy_rule9 = “(
                          (arith_and (arith_a ^is_length_le_17)
                          (arith_and (arith_a ^is_length_ge_17)
                          (arith_and (arith_a ^is_ttl_le_17)
                          (arith_and (arith_a ^is_ttl_ge_17)
                          (arith_and (arith_a ^is_srcPort_le_52244)
                          (arith_and (arith_a ^is_srcPort_ge_52244)
                          (arith_and (arith_a ^is_dstPort_le_58774)
                          (arith_and (arith_a ^is_dstPort_ge_58774)
                          (arith_and (arith_a ^is_srcNAT_le_2211)
                          (arith_and (arith_a ^is_srcNAT_ge_2211)
                          (arith_and (arith_a ^is_dstNAT_le_58774)
                                   (arith_a ^is_dstNAT_ge_58774)))))))))))) ,
                           action ("allow",[9])):single_rule”;

(* rule 10 *)

val is_srcPort_le_50627 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;
val is_srcPort_ge_50627 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;

val is_srcNAT_le_16215 = “(arithm_le (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16215 16))”;
val is_srcNAT_ge_16215 = “(arithm_ge (lv_acc (lv_x "h") "srcNAT") ^(bdd_utilsLib.make_bv 16215 16))”;


val arith_policy_rule10 = “(
                          (arith_and (arith_a ^is_length_le_11)
                          (arith_and (arith_a ^is_length_ge_11)
                          (arith_and (arith_a ^is_ttl_le_11)
                          (arith_and (arith_a ^is_ttl_ge_11)
                          (arith_and (arith_a ^is_srcPort_le_50627)
                          (arith_and (arith_a ^is_srcPort_ge_50627)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          (arith_and (arith_a ^is_dstPort_ge_443)
                          (arith_and (arith_a ^is_srcNAT_le_16215)
                          (arith_and (arith_a ^is_srcNAT_ge_16215)
                          (arith_and (arith_a ^is_dstNAT_le_443)
                                   (arith_a ^is_dstNAT_ge_443)))))))))))) ,
                           action ("allow",[10])):single_rule”;

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
    ^arith_policy_rule_default
]:single_rule list”;



(* Combined policy mapping *)
val policy_me =   “[
    ("is_length_le_10", ^is_length_le_10);
    ("is_length_ge_10", ^is_length_ge_10);
    ("is_ttl_le_10", ^is_ttl_le_10);
    ("is_ttl_ge_10", ^is_ttl_ge_10);
    ("is_srcPort_le_57222", ^is_srcPort_le_57222);
    ("is_srcPort_ge_57222", ^is_srcPort_ge_57222);
    ("is_dstPort_le_53", ^is_dstPort_le_53);
    ("is_dstPort_ge_53", ^is_dstPort_ge_53);
    ("is_srcNAT_le_54587", ^is_srcNAT_le_54587);
    ("is_srcNAT_ge_54587", ^is_srcNAT_ge_54587);
    ("is_dstNAT_le_53", ^is_dstNAT_le_53);
    ("is_dstNAT_ge_53", ^is_dstNAT_ge_53);
    ("is_length_le_11", ^is_length_le_11);
    ("is_length_ge_11", ^is_length_ge_11);
    ("is_ttl_le_11", ^is_ttl_le_11);
    ("is_ttl_ge_11", ^is_ttl_ge_11);
    ("is_srcPort_le_56258", ^is_srcPort_le_56258);
    ("is_srcPort_ge_56258", ^is_srcPort_ge_56258);
    ("is_dstPort_le_3389", ^is_dstPort_le_3389);
    ("is_dstPort_ge_3389", ^is_dstPort_ge_3389);
    ("is_srcNAT_le_56258", ^is_srcNAT_le_56258);
    ("is_srcNAT_ge_56258", ^is_srcNAT_ge_56258);
    ("is_dstNAT_le_3389", ^is_dstNAT_le_3389);
    ("is_dstNAT_ge_3389", ^is_dstNAT_ge_3389);
    ("is_length_le_12", ^is_length_le_12);
    ("is_length_ge_12", ^is_length_ge_12);
    ("is_ttl_le_12", ^is_ttl_le_12);
    ("is_ttl_ge_12", ^is_ttl_ge_12);
    ("is_srcPort_le_6881", ^is_srcPort_le_6881);
    ("is_srcPort_ge_6881", ^is_srcPort_ge_6881);
    ("is_dstPort_le_50321", ^is_dstPort_le_50321);
    ("is_dstPort_ge_50321", ^is_dstPort_ge_50321);
    ("is_srcNAT_le_43265", ^is_srcNAT_le_43265);
    ("is_srcNAT_ge_43265", ^is_srcNAT_ge_43265);
    ("is_dstNAT_le_50321", ^is_dstNAT_le_50321);
    ("is_dstNAT_ge_50321", ^is_dstNAT_ge_50321);
    ("is_length_le_13", ^is_length_le_13);
    ("is_length_ge_13", ^is_length_ge_13);  
    ("is_ttl_le_13", ^is_ttl_le_13);
    ("is_ttl_ge_13", ^is_ttl_ge_13);
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
    ("is_length_le_14", ^is_length_le_14);
    ("is_length_ge_14", ^is_length_ge_14);
    ("is_ttl_le_14", ^is_ttl_le_14);
    ("is_ttl_ge_14", ^is_ttl_ge_14);
    ("is_srcPort_le_51465", ^is_srcPort_le_51465);
    ("is_srcPort_ge_51465", ^is_srcPort_ge_51465);
    ("is_srcNAT_le_39975", ^is_srcNAT_le_39975);
    ("is_srcNAT_ge_39975", ^is_srcNAT_ge_39975);
    ("is_length_le_15", ^is_length_le_15);
    ("is_length_ge_15", ^is_length_ge_15);
    ("is_ttl_le_15", ^is_ttl_le_15);
    ("is_ttl_ge_15", ^is_ttl_ge_15);
    ("is_srcPort_le_60513", ^is_srcPort_le_60513);
    ("is_srcPort_ge_60513", ^is_srcPort_ge_60513);
    ("is_dstPort_le_47094", ^is_dstPort_le_47094);
    ("is_dstPort_ge_47094", ^is_dstPort_ge_47094);
    ("is_srcNAT_le_45469", ^is_srcNAT_le_45469);
    ("is_srcNAT_ge_45469", ^is_srcNAT_ge_45469);
    ("is_dstNAT_le_47094", ^is_dstNAT_le_47094);
    ("is_dstNAT_ge_47094", ^is_dstNAT_ge_47094);
    ("is_length_le_16", ^is_length_le_16);
    ("is_length_ge_16", ^is_length_ge_16);
    ("is_ttl_le_16", ^is_ttl_le_16);
    ("is_ttl_ge_16", ^is_ttl_ge_16);
    ("is_srcPort_le_50049", ^is_srcPort_le_50049);
    ("is_srcPort_ge_50049", ^is_srcPort_ge_50049);
    ("is_srcNAT_le_21285", ^is_srcNAT_le_21285);
    ("is_srcNAT_ge_21285", ^is_srcNAT_ge_21285);
    ("is_length_le_17", ^is_length_le_17);
    ("is_length_ge_17", ^is_length_ge_17);
    ("is_ttl_le_17", ^is_ttl_le_17);
    ("is_ttl_ge_17", ^is_ttl_ge_17);
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
]”;



(****************************)
(* worst output table order *)
(*    but better for BDD    *)
(****************************)

val policy_order = ``[
  "is_length_le_10"; "is_length_ge_10";
  "is_ttl_le_10"; "is_ttl_ge_10";
  "is_srcPort_le_57222"; "is_srcPort_ge_57222";
  "is_dstPort_le_53"; "is_dstPort_ge_53";
  "is_srcNAT_le_54587"; "is_srcNAT_ge_54587";
  "is_dstNAT_le_53"; "is_dstNAT_ge_53";
  "is_length_le_11"; "is_length_ge_11";
  "is_ttl_le_11"; "is_ttl_ge_11";
  "is_srcPort_le_56258"; "is_srcPort_ge_56258";
  "is_dstPort_le_3389"; "is_dstPort_ge_3389";
  "is_srcNAT_le_56258"; "is_srcNAT_ge_56258";
  "is_dstNAT_le_3389"; "is_dstNAT_ge_3389";
  "is_length_le_12"; "is_length_ge_12";
  "is_ttl_le_12"; "is_ttl_ge_12";
  "is_srcPort_le_6881"; "is_srcPort_ge_6881";
  "is_dstPort_le_50321"; "is_dstPort_ge_50321";
  "is_srcNAT_le_43265"; "is_srcNAT_ge_43265";
  "is_dstNAT_le_50321"; "is_dstNAT_ge_50321";
  "is_length_le_13"; "is_length_ge_13";
  "is_ttl_le_13"; "is_ttl_ge_13";
  "is_srcPort_le_50553"; "is_srcPort_ge_50553";
  "is_srcNAT_le_50553"; "is_srcNAT_ge_50553";
  "is_srcPort_le_50002"; "is_srcPort_ge_50002";
  "is_dstPort_le_443"; "is_dstPort_ge_443";
  "is_srcNAT_le_45848"; "is_srcNAT_ge_45848";
  "is_dstNAT_le_443"; "is_dstNAT_ge_443";
  "is_ttl_le_14"; "is_ttl_ge_14";
  "is_srcPort_le_51465"; "is_srcPort_ge_51465";
  "is_srcNAT_le_39975"; "is_srcNAT_ge_39975";
  "is_length_le_15"; "is_length_ge_15";
  "is_ttl_le_15"; "is_ttl_ge_15";
  "is_srcPort_le_60513"; "is_srcPort_ge_60513";
  "is_dstPort_le_47094"; "is_dstPort_ge_47094";
  "is_srcNAT_le_45469"; "is_srcNAT_ge_45469";
  "is_dstNAT_le_47094"; "is_dstNAT_ge_47094";
  "is_length_le_16"; "is_length_ge_16";
  "is_ttl_le_16"; "is_ttl_ge_16";
  "is_srcPort_le_50049"; "is_srcPort_ge_50049";
  "is_srcNAT_le_21285"; "is_srcNAT_ge_21285";
  "is_length_le_17"; "is_length_ge_17";
  "is_ttl_le_17"; "is_ttl_ge_17";
  "is_srcPort_le_52244"; "is_srcPort_ge_52244";
  "is_dstPort_le_58774"; "is_dstPort_ge_58774";
  "is_srcNAT_le_2211"; "is_srcNAT_ge_2211";
  "is_dstNAT_le_58774"; "is_dstNAT_ge_58774";
  "is_srcPort_le_50627"; "is_srcPort_ge_50627";
  "is_srcNAT_le_16215"; "is_srcNAT_ge_16215"
]``;

val policy_full_order = ``[
  ("310s",["is_length_le_10";"is_length_ge_10"]);
  ("u7a" ,["is_ttl_le_10";"is_ttl_ge_10"]);
  ("aa5",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("13" ,["is_dstPort_le_53";"is_dstPort_ge_53"]);
  ("wqso",["is_srcNAT_le_54587";"is_srcNAT_ge_54587"]);
  ("ei" ,["is_dstNAT_le_53";"is_dstNAT_ge_53"]);
  ("um",["is_length_le_11";"is_length_ge_11"]);
  ("1b" ,["is_ttl_le_11";"is_ttl_ge_11"]);
  ("gu58",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("zrmz" ,["is_dstPort_le_3389";"is_dstPort_ge_3389"]);
  ("gm",["is_srcNAT_le_56258";"is_srcNAT_ge_56258"]);
  ("xp82" ,["is_dstNAT_le_3389";"is_dstNAT_ge_3389"]);
  ("3bp",["is_length_le_12";"is_length_ge_12"]);
  ("i6uu" ,["is_ttl_le_12";"is_ttl_ge_12"]);
  ("7nd",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("ouzt" ,["is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("41d",["is_srcNAT_le_43265";"is_srcNAT_ge_43265"]);
  ("82" ,["is_dstNAT_le_50321";"is_dstNAT_ge_50321"]);
  ("1h4q",["is_length_le_13";"is_length_ge_13"]);
  ("xm68" ,["is_ttl_le_13";"is_ttl_ge_13"]);
  ("xn",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("tc" ,["is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
  ("o9e4",["is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("pk" ,["is_dstPort_le_443";"is_dstPort_ge_443"]);
  ("9pj",["is_srcNAT_le_45848";"is_srcNAT_ge_45848"]);
  ("lnk" ,["is_dstNAT_le_443";"is_dstNAT_ge_443"]);
  ("mzt",["is_ttl_le_14";"is_ttl_ge_14"]);
  ("h3zy" ,["is_srcPort_le_51465";"is_srcPort_ge_51465"]);
  ("wte",["is_srcNAT_le_39975";"is_srcNAT_ge_39975"]);
  ("8t" ,["is_length_le_15";"is_length_ge_15"]);
  ("069",["is_ttl_le_15";"is_ttl_ge_15"]);
  ("jv" ,["is_srcPort_le_60513";"is_srcPort_ge_60513"]);
  ("qj",["is_dstPort_le_47094";"is_dstPort_ge_47094"]);
  ("fvw5" ,["is_srcNAT_le_45469";"is_srcNAT_ge_45469"]);
  ("t3hx",["is_dstNAT_le_47094";"is_dstNAT_ge_47094"]);
  ("xoa6" ,["is_length_le_16";"is_length_ge_16"]);
  ("plb",["is_ttl_le_16";"is_ttl_ge_16"]);
  ("zdt" ,["is_srcPort_le_50049";"is_srcPort_ge_50049"]);
  ("p4o",["is_srcNAT_le_21285";"is_srcNAT_ge_21285"]);
  ("f1t" ,["is_length_le_17";"is_length_ge_17"]);
  ("bk",["is_ttl_le_17";"is_ttl_ge_17"]);
  ("m9" ,["is_srcPort_le_52244";"is_srcPort_ge_52244"]);
  ("5o",["is_dstPort_le_58774";"is_dstPort_ge_58774"]);
  ("j7p" ,["is_srcNAT_le_2211";"is_srcNAT_ge_2211"]);
  ("v8ax",["is_dstNAT_le_58774";"is_dstNAT_ge_58774"]);
  ("txr6" ,["is_srcPort_le_50627";"is_srcPort_ge_50627"]);
  ("obv",["is_srcNAT_le_16215";"is_srcNAT_ge_16215"])
]``;


(********************************)


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
"internet_firewall_10_12");


                      
val _ = export_theory ();
