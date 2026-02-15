open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "internet_firewall_10_2";

Type single_rule = “:((string# num list) action_expr) arith_rule”;

val test_pd_type = “[("h", type_record [("srcPort", type_length 16)])]”;

(************************************************)
(* rule 1 *)

val is_srcPort_le_57222 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;
val is_srcPort_ge_57222 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 57222 16))”;


val arith_policy_rule1 = “((arith_and (arith_a ^is_srcPort_le_57222)
                          ( (arith_a ^is_srcPort_ge_57222)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 2 *)

val is_srcPort_le_56258 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;
val is_srcPort_ge_56258 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 56258 16))”;


val arith_policy_rule2 = “((arith_and (arith_a ^is_srcPort_le_56258)
                          ( (arith_a ^is_srcPort_ge_56258)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 3 *)

val is_srcPort_le_6881 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;
val is_srcPort_ge_6881 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 6881 16))”;

val arith_policy_rule3 = “((arith_and (arith_a ^is_srcPort_le_6881)
                          ( (arith_a ^is_srcPort_ge_6881)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 4 *)

val is_srcPort_le_50553 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;
val is_srcPort_ge_50553 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50553 16))”;


val arith_policy_rule4 = “((arith_and (arith_a ^is_srcPort_le_50553)
                          ( (arith_a ^is_srcPort_ge_50553)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 5 *)

val is_srcPort_le_50002 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;
val is_srcPort_ge_50002 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50002 16))”;




val arith_policy_rule5 = “((arith_and (arith_a ^is_srcPort_le_50002)
                          ( (arith_a ^is_srcPort_ge_50002)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 6 *)

val is_srcPort_le_51465 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;
val is_srcPort_ge_51465 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 51465 16))”;


val arith_policy_rule6 = “((arith_and (arith_a ^is_srcPort_le_51465)
                          ( (arith_a ^is_srcPort_ge_51465))) ,
                           action ("allow",[1])):single_rule”;

(* rule 7 *)

val is_srcPort_le_60513 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;
val is_srcPort_ge_60513 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 60513 16))”;

val arith_policy_rule7 = “((arith_and (arith_a ^is_srcPort_le_60513)
                          ( (arith_a ^is_srcPort_ge_60513))) ,
                           action ("allow",[1])):single_rule”;

(* rule 8 *)

val is_srcPort_le_50049 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;
val is_srcPort_ge_50049 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50049 16))”;


val arith_policy_rule8 = “((arith_and (arith_a ^is_srcPort_le_50049)
                          ( (arith_a ^is_srcPort_ge_50049))) ,
                           action ("allow",[1])):single_rule”;

(* rule 9 *)

val is_srcPort_le_52244 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;
val is_srcPort_ge_52244 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 52244 16))”;

val arith_policy_rule9 = “((arith_and (arith_a ^is_srcPort_le_52244)
                          ( (arith_a ^is_srcPort_ge_52244)
                          )) ,
                           action ("allow",[1])):single_rule”;

(* rule 10 *)
val is_srcPort_le_50627 = “(arithm_le (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;
val is_srcPort_ge_50627 = “(arithm_ge (lv_acc (lv_x "h") "srcPort") ^(bdd_utilsLib.make_bv 50627 16))”;

val arith_policy_rule10 = “((arith_and (arith_a ^is_srcPort_le_50627)
                          ( (arith_a ^is_srcPort_ge_50627)
                          )) ,
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
    ("is_srcPort_le_56258", ^is_srcPort_le_56258);
    ("is_srcPort_ge_56258", ^is_srcPort_ge_56258);
    ("is_srcPort_le_6881", ^is_srcPort_le_6881);
    ("is_srcPort_ge_6881", ^is_srcPort_ge_6881);
    ("is_srcPort_le_50553", ^is_srcPort_le_50553);
    ("is_srcPort_ge_50553", ^is_srcPort_ge_50553);
    ("is_srcPort_le_50002", ^is_srcPort_le_50002);
    ("is_srcPort_ge_50002", ^is_srcPort_ge_50002);
    ("is_srcPort_le_51465", ^is_srcPort_le_51465);
    ("is_srcPort_ge_51465", ^is_srcPort_ge_51465);
    ("is_srcPort_le_60513", ^is_srcPort_le_60513);
    ("is_srcPort_ge_60513", ^is_srcPort_ge_60513);
    ("is_srcPort_le_50049", ^is_srcPort_le_50049);
    ("is_srcPort_ge_50049", ^is_srcPort_ge_50049);
    ("is_srcPort_le_52244", ^is_srcPort_le_52244);
    ("is_srcPort_ge_52244", ^is_srcPort_ge_52244);
    ("is_srcPort_le_50627", ^is_srcPort_le_50627);
    ("is_srcPort_ge_50627", ^is_srcPort_ge_50627)
]”;



(***********************************************)



(******************************)
(*   Best output table order  *)
(******************************)


(* Grouped policy ordering *)
val policy_full_order = “[
  ("srcPortGrp",["is_srcPort_le_57222";"is_srcPort_ge_57222";"is_srcPort_le_56258";"is_srcPort_ge_56258";"is_srcPort_le_6881";"is_srcPort_ge_6881";"is_srcPort_le_50553";"is_srcPort_ge_50553";"is_srcPort_le_50002";"is_srcPort_ge_50002";"is_srcPort_le_51465";"is_srcPort_ge_51465";"is_srcPort_le_60513";"is_srcPort_ge_60513";"is_srcPort_le_50049";"is_srcPort_ge_50049";"is_srcPort_le_52244";"is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627"])
]”;

(* Flat policy order (grouped) *)
val policy_order = “["is_srcPort_le_57222"; "is_srcPort_ge_57222"; "is_srcPort_le_56258"; "is_srcPort_ge_56258"; "is_srcPort_le_6881"; "is_srcPort_ge_6881"; "is_srcPort_le_50553"; "is_srcPort_ge_50553"; "is_srcPort_le_50002"; "is_srcPort_ge_50002"; "is_srcPort_le_51465"; "is_srcPort_ge_51465"; "is_srcPort_le_60513"; "is_srcPort_ge_60513"; "is_srcPort_le_50049"; "is_srcPort_ge_50049"; "is_srcPort_le_52244"; "is_srcPort_ge_52244";"is_srcPort_le_50627";"is_srcPort_ge_50627"]”;






(****************************)
(* worst output table order *)
(*    but better for BDD    *)
(****************************)
(*
val policy_order = “[
  "is_srcPort_le_57222"; "is_srcPort_ge_57222";
  "is_srcPort_le_56258"; "is_srcPort_ge_56258";
  "is_srcPort_le_6881"; "is_srcPort_ge_6881";
  "is_srcPort_le_50553"; "is_srcPort_ge_50553";
  "is_srcPort_le_50002"; "is_srcPort_ge_50002";
  "is_srcPort_le_51465"; "is_srcPort_ge_51465";
  "is_srcPort_le_60513"; "is_srcPort_ge_60513";
  "is_srcPort_le_50049"; "is_srcPort_ge_50049";
  "is_srcPort_le_52244"; "is_srcPort_ge_52244";
  "is_srcPort_le_50627"; "is_srcPort_ge_50627";
]”;

val policy_full_order = “[
  ("igfm",["is_srcPort_le_57222";"is_srcPort_ge_57222"]);
  ("gm",["is_srcPort_le_56258";"is_srcPort_ge_56258"]);
  ("qou",["is_srcPort_le_6881";"is_srcPort_ge_6881"]);
  ("ebq",["is_srcPort_le_50553";"is_srcPort_ge_50553"]);
  ("ti",["is_srcPort_le_50002";"is_srcPort_ge_50002"]);
  ("5nby",["is_srcPort_le_51465";"is_srcPort_ge_51465"]);
  ("kjz",["is_srcPort_le_60513";"is_srcPort_ge_60513"]);
  ("j06",["is_srcPort_le_50049";"is_srcPort_ge_50049"]);
  ("hjl",["is_srcPort_le_52244";"is_srcPort_ge_52244"]);
  ("8ug",["is_srcPort_le_50627";"is_srcPort_ge_50627"]);
]”; *)


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
"internet_firewall_10_2");



val _ = export_theory ();


(*

    Type action_table_type = :((string# num list) var_table_list # num)



val tbl = “([[([Var "is_srcPort_le_57222"; Var "is_srcPort_ge_57222"],0,state 3);
              ([Var "is_srcPort_le_56258"; Var "is_srcPort_ge_56258"],0,state 9);
              ([Var "is_srcPort_le_6881"; Var "is_srcPort_ge_6881"],0,state 15);
              ([Var "is_srcPort_le_50553"; Var "is_srcPort_ge_50553"],0,state 21);
              ([Var "is_srcPort_le_50002"; Var "is_srcPort_ge_50002"],0,state 27);
              ([Var "is_srcPort_le_51465"; Var "is_srcPort_ge_51465"],0,state 33);
              ([Var "is_srcPort_le_60513"; Var "is_srcPort_ge_60513"],0,state 39);
              ([Var "is_srcPort_le_50049"; Var "is_srcPort_ge_50049"],0,state 45);
              ([Var "is_srcPort_le_52244"; Var "is_srcPort_ge_52244"],0,state 51);
              ([Var "is_srcPort_le_50627"; Var "is_srcPort_ge_50627"],0,state 57);
             ];

             [([True],3,action ("allow",[1])); ([True],9,action ("allow",[2]));
              ([True],15,action ("allow",[3])); ([True],21,action ("allow",[4]));
              ([True],27,action ("allow",[5])); ([True],33,action ("allow",[6]));
              ([True],39,action ("allow",[7])); ([True],45,action ("allow",[8]));
              ([True],51,action ("allow",[9])); ([True],56,action ("drop",[]));
              ([True],57,action ("allow",[10]))]


            ],0):action_table_type”
*)
