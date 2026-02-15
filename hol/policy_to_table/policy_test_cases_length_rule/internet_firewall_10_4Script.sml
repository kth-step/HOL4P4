open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "internet_firewall_10_4";

Type single_rule = “:((string# num list) action_expr) arith_rule”;

val test_pd_type = “[("h", type_record [("srcPort", type_length 16);
                                        ("dstPort", type_length 16)])]”;

(************************************************)
(* rule 1 *)

val is_srcPort_le_57222 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;
val is_srcPort_ge_57222 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;

val is_dstPort_le_53 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;
val is_dstPort_ge_53 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 53 16))”;


val arith_policy_rule1 = “((arith_and (arith_a ^is_srcPort_le_57222)
                          (arith_and (arith_a ^is_srcPort_ge_57222)
                          (arith_and (arith_a ^is_dstPort_le_53)
                          ( (arith_a ^is_dstPort_ge_53))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 2 *)

val is_srcPort_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcPort_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;

val is_dstPort_le_3389 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;
val is_dstPort_ge_3389 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 3389 16))”;


val arith_policy_rule2 = “((arith_and (arith_a ^is_srcPort_le_56258)
                          (arith_and (arith_a ^is_srcPort_ge_56258)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          ((arith_a ^is_dstPort_ge_3389))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 3 *)

val is_srcPort_le_6881 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;
val is_srcPort_ge_6881 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;

val is_dstPort_le_50321 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;
val is_dstPort_ge_50321 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 50321 16))”;


val arith_policy_rule3 = “((arith_and (arith_a ^is_srcPort_le_6881)
                          (arith_and (arith_a ^is_srcPort_ge_6881)
                          (arith_and (arith_a ^is_dstPort_le_50321)
                          ((arith_a ^is_dstPort_ge_50321))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 4 *)

val is_srcPort_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcPort_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;


val arith_policy_rule4 = “((arith_and (arith_a ^is_srcPort_le_50553)
                          (arith_and (arith_a ^is_srcPort_ge_50553)
                          (arith_and (arith_a ^is_dstPort_le_3389)
                          ((arith_a ^is_dstPort_ge_3389))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 5 *)

val is_srcPort_le_50002 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;
val is_srcPort_ge_50002 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;

val is_dstPort_le_443 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;
val is_dstPort_ge_443 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 443 16))”;



val arith_policy_rule5 = “((arith_and (arith_a ^is_srcPort_le_50002)
                          (arith_and (arith_a ^is_srcPort_ge_50002)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          ( (arith_a ^is_dstPort_ge_443))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 6 *)

val is_srcPort_le_51465 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;
val is_srcPort_ge_51465 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;


val arith_policy_rule6 = “((arith_and (arith_a ^is_srcPort_le_51465)
                          (arith_and (arith_a ^is_srcPort_ge_51465)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          ( (arith_a ^is_dstPort_ge_443))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 7 *)

val is_srcPort_le_60513 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;
val is_srcPort_ge_60513 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;

val is_dstPort_le_47094 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;
val is_dstPort_ge_47094 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 47094 16))”;


val arith_policy_rule7 = “((arith_and (arith_a ^is_srcPort_le_60513)
                          (arith_and (arith_a ^is_srcPort_ge_60513)
                          (arith_and (arith_a ^is_dstPort_le_47094)
                          ( (arith_a ^is_dstPort_ge_47094))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 8 *)

val is_srcPort_le_50049 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;
val is_srcPort_ge_50049 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;


val arith_policy_rule8 = “((arith_and (arith_a ^is_srcPort_le_50049)
                          (arith_and (arith_a ^is_srcPort_ge_50049)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          ( (arith_a ^is_dstPort_ge_443))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 9 *)

val is_srcPort_le_52244 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;
val is_srcPort_ge_52244 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;

val is_dstPort_le_58774 = “(arithm_le (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;
val is_dstPort_ge_58774 = “(arithm_ge (lv_acc (lv_x "h") "dstPort") ^(bdd_utilsLib.make_bv 58774 16))”;


val arith_policy_rule9 = “((arith_and (arith_a ^is_srcPort_le_52244)
                          (arith_and (arith_a ^is_srcPort_ge_52244)
                          (arith_and (arith_a ^is_dstPort_le_58774)
                          ( (arith_a ^is_dstPort_ge_58774))))) ,
                           action ("allow",[1])):single_rule”;

(* rule 10 *)

val is_srcPort_le_50627 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;
val is_srcPort_ge_50627 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;



val arith_policy_rule10 = “((arith_and (arith_a ^is_srcPort_le_50627)
                          (arith_and (arith_a ^is_srcPort_ge_50627)
                          (arith_and (arith_a ^is_dstPort_le_443)
                          ( (arith_a ^is_dstPort_ge_443))))) ,
                           action ("allow",[1])):single_rule”;

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
    ("is_srcPort_le_57222", ^is_srcPort_le_57222);
    ("is_srcPort_ge_57222", ^is_srcPort_ge_57222);
    ("is_dstPort_le_53", ^is_dstPort_le_53);
    ("is_dstPort_ge_53", ^is_dstPort_ge_53);
    ("is_srcPort_le_56258", ^is_srcPort_le_56258);
    ("is_srcPort_ge_56258", ^is_srcPort_ge_56258);
    ("is_dstPort_le_3389", ^is_dstPort_le_3389);
    ("is_dstPort_ge_3389", ^is_dstPort_ge_3389);
    ("is_srcPort_le_6881", ^is_srcPort_le_6881);
    ("is_srcPort_ge_6881", ^is_srcPort_ge_6881);
    ("is_dstPort_le_50321", ^is_dstPort_le_50321);
    ("is_dstPort_ge_50321", ^is_dstPort_ge_50321);
    ("is_srcPort_le_50553", ^is_srcPort_le_50553);
    ("is_srcPort_ge_50553", ^is_srcPort_ge_50553);
    ("is_srcPort_le_50002", ^is_srcPort_le_50002);
    ("is_srcPort_ge_50002", ^is_srcPort_ge_50002);
    ("is_dstPort_le_443", ^is_dstPort_le_443);
    ("is_dstPort_ge_443", ^is_dstPort_ge_443);
    ("is_srcPort_le_51465", ^is_srcPort_le_51465);
    ("is_srcPort_ge_51465", ^is_srcPort_ge_51465);
    ("is_srcPort_le_60513", ^is_srcPort_le_60513);
    ("is_srcPort_ge_60513", ^is_srcPort_ge_60513);
    ("is_dstPort_le_47094", ^is_dstPort_le_47094);
    ("is_dstPort_ge_47094", ^is_dstPort_ge_47094);
    ("is_srcPort_le_50049", ^is_srcPort_le_50049);
    ("is_srcPort_ge_50049", ^is_srcPort_ge_50049);
    ("is_srcPort_le_52244", ^is_srcPort_le_52244);
    ("is_srcPort_ge_52244", ^is_srcPort_ge_52244);
    ("is_dstPort_le_58774", ^is_dstPort_le_58774);
    ("is_dstPort_ge_58774", ^is_dstPort_ge_58774);
    ("is_srcPort_le_50627", ^is_srcPort_le_50627);
    ("is_srcPort_ge_50627", ^is_srcPort_ge_50627)
]”;

(***********************************************)


(******************************)
(*   Best output table order  *)
(******************************)


(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002";"is_srcPort_le_51465";"is_srcPort_ge_51465";"is_srcPort_le_60513";"is_srcPort_ge_60513";"is_srcPort_le_50049";"is_srcPort_ge_50049";"is_srcPort_le_52244";"is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627"]);
  ("dstPortGrp",["is_dstPort_le_53";"is_dstPort_ge_53";"is_dstPort_le_3389";"is_dstPort_ge_3389";"is_dstPort_le_50321";"is_dstPort_ge_50321";"is_dstPort_le_443";"is_dstPort_ge_443";"is_dstPort_le_47094";"is_dstPort_ge_47094";"is_dstPort_le_58774";"is_dstPort_ge_58774"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002"; "is_srcPort_ge_50002"; "is_srcPort_le_51465"; "is_srcPort_ge_51465"; "is_srcPort_le_60513"; "is_srcPort_ge_60513"; "is_srcPort_le_50049"; "is_srcPort_ge_50049"; "is_srcPort_le_52244"; "is_srcPort_ge_52244"; "is_srcPort_le_50627"; "is_srcPort_ge_50627"; "is_dstPort_le_53"; "is_dstPort_ge_53"; "is_dstPort_le_3389"; "is_dstPort_ge_3389"; "is_dstPort_le_50321"; "is_dstPort_ge_50321"; "is_dstPort_le_443"; "is_dstPort_ge_443"; "is_dstPort_le_47094"; "is_dstPort_ge_47094"; "is_dstPort_le_58774"; "is_dstPort_ge_58774"]”;






(****************************)
(* worst output table order *)
(*    but better for BDD    *)
(****************************)
(*
val policy_order = “[
  "is_srcPort_le_57222"; "is_srcPort_ge_57222";
  "is_dstPort_le_53"; "is_dstPort_ge_53";
  "is_srcPort_le_56258"; "is_srcPort_ge_56258";
  "is_dstPort_le_3389"; "is_dstPort_ge_3389";
  "is_srcPort_le_6881"; "is_srcPort_ge_6881";
  "is_dstPort_le_50321"; "is_dstPort_ge_50321";
  "is_srcPort_le_50553"; "is_srcPort_ge_50553";
  "is_srcPort_le_50002"; "is_srcPort_ge_50002";
  "is_dstPort_le_443"; "is_dstPort_ge_443";
  "is_srcPort_le_51465"; "is_srcPort_ge_51465";
  "is_srcPort_le_60513"; "is_srcPort_ge_60513";
  "is_dstPort_le_47094"; "is_dstPort_ge_47094";
  "is_srcPort_le_50049"; "is_srcPort_ge_50049";
  "is_srcPort_le_52244"; "is_srcPort_ge_52244";
  "is_dstPort_le_58774"; "is_dstPort_ge_58774";
  "is_srcPort_le_50627"; "is_srcPort_ge_50627";
]”;

val policy_full_order = “[
  ("igfm",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("f5x" ,["is_dstPort_le_53";"is_dstPort_ge_53"]);
  ("gm",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("9g5" ,["is_dstPort_le_3389";"is_dstPort_ge_3389"]);
  ("qou",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("pa" ,["is_dstPort_le_50321";"is_dstPort_ge_50321"]);
  ("ebq",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("ti",["is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("lc" ,["is_dstPort_le_443";"is_dstPort_ge_443"]);
  ("5nby",["is_srcPort_le_51465";"is_srcPort_ge_51465"]);
  ("kjz",["is_srcPort_le_60513";"is_srcPort_ge_60513"]);
  ("2fo" ,["is_dstPort_le_47094";"is_dstPort_ge_47094"]);
  ("j06",["is_srcPort_le_50049";"is_srcPort_ge_50049"]);
  ("hjl",["is_srcPort_le_52244";"is_srcPort_ge_52244"]);
  ("8cb0" ,["is_dstPort_le_58774";"is_dstPort_ge_58774"]);
  ("8ug",["is_srcPort_le_50627";"is_srcPort_ge_50627"]);
]”;  *)


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
"internet_firewall_10_4");



val _ = export_theory ();
