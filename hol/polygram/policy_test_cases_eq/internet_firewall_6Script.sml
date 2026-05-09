open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "internet_firewall_6";

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


val arith_policy_rule2 = “((arith_and (arith_a ^is_srcPort_le_56258)
                          (arith_and (arith_a ^is_srcPort_ge_56258)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          (arith_and (arith_a ^is_dstPort_ge_3389)
                          (arith_and (arith_a ^is_srcNAT_le_56258)
                          (arith_and (arith_a ^is_srcNAT_ge_56258)
                          (arith_and (arith_a ^is_dstNAT_le_3389)
                                   (arith_a ^is_dstNAT_ge_3389)))))))) ,
                           action ("allow",[1])):single_rule”;

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
                           action ("allow",[1])):single_rule”;

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
                           action ("allow",[1])):single_rule”;

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
                           action ("allow",[1])):single_rule”;

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
                           action ("allow",[1])):single_rule”;

(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;

(* Combined arith policy list *)
val arith_policy1 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule5;
    ^arith_policy_rule6;
    ^arith_policy_rule_default
]:single_rule list”;


val arith_policy2 = “[
    ^arith_policy_rule3;
    ^arith_policy_rule1;
    ^arith_policy_rule6;
    ^arith_policy_rule2;
    ^arith_policy_rule4;
    ^arith_policy_rule5;
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
]”;


(* order *)
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
  "is_srcNAT_le_39975"; "is_srcNAT_ge_39975"
]”;


(***********************************************)

val policy_eq_thm = fwd_proof_polcies_cakeLib.check_two_polcies_eq (arith_policy1, arith_policy2, policy_me, test_pd_type, policy_order, "internet_firewall_6");

val _ = export_theory ();