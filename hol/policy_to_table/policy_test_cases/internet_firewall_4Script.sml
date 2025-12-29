open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


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


(******************************)
(*   Best output table order  *)
(******************************)

(* 
(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321"])
]”;

(* Flat policy order (grouped) *)

val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321"]”;
 *)


(**************************************)
(* hand crafted possible better order *)
(**************************************)


(* 
val policy_full_order = “[
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("dstNATGrp" ,["is_dstNAT_le_53";"is_dstNAT_ge_53";"is_dstNAT_le_3389";"is_dstNAT_ge_3389";"is_dstNAT_le_50321";"is_dstNAT_ge_50321"]);
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("srcNATGrp" ,["is_srcNAT_le_54587";"is_srcNAT_ge_54587";"is_srcNAT_le_56258";"is_srcNAT_ge_56258";"is_srcNAT_le_43265";"is_srcNAT_ge_43265";"is_srcNAT_le_50553";"is_srcNAT_ge_50553"]);
]”;

val policy_order = “[
  "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321";
   "is_dstNAT_le_53"; "is_dstNAT_ge_53"; "is_dstNAT_le_3389"; "is_dstNAT_ge_3389"; "is_dstNAT_le_50321"; "is_dstNAT_ge_50321";
   "is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; 
   "is_srcNAT_le_54587"; "is_srcNAT_ge_54587"; "is_srcNAT_le_56258"; "is_srcNAT_ge_56258"; "is_srcNAT_le_43265"; "is_srcNAT_ge_43265"; "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"; 
 ]”;
 *)



(****************************)
(* worst output table order *)
(*    but better for BDD    *)
(****************************)


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
  "is_srcNAT_le_50553"; "is_srcNAT_ge_50553"
]``;

val policy_full_order = ``[
  ("e5",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("jwg" ,["is_dstPort_le_53";"is_dstPort_ge_53"]);
  ("7w5",["is_srcNAT_le_54587";"is_srcNAT_ge_54587"]);
  ("i4w" ,["is_dstNAT_le_53";"is_dstNAT_ge_53"]);
  ("2z6f",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("79y" ,["is_dstPort_le_3389";"is_dstPort_ge_3389"]);
  ("7wu",["is_srcNAT_le_56258";"is_srcNAT_ge_56258"]);
  ("d1" ,["is_dstNAT_le_3389";"is_dstNAT_ge_3389"]);
  ("vl94",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("gs" ,["is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("4a",["is_srcNAT_le_43265";"is_srcNAT_ge_43265"]);
  ("lb" ,["is_dstNAT_le_50321";"is_dstNAT_ge_50321"]);
  ("7eii",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("g5" ,["is_srcNAT_le_50553";"is_srcNAT_ge_50553"])
]``; 





(***********************************************)


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
"internet_firewall_4");



val _ = export_theory ();
