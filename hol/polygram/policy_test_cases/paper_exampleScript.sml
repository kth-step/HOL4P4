open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "paper_example";

Type single_rule = “:((string# num list) action_expr) arith_rule”;

val test_pd_type = “["h", type_record [("ip", type_record [("dst", type_length 32);
                                                           ("ttl", type_length 8);]);
                                       ("tcp", type_record [("dstPort", type_length 16)])]]”;


(* between 10.0.0.0 and 10.0.0.255*)
val x1 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 167772160 32))”;
val x2 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 167772415 32))”;

(* between 192.168.0.0 and 192.168.255.255 *)
val x3 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 3232235520 32))”;
val x4 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 3232301055 32))”;

val y1 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 1023 16))”;
val y2 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 49152 16))”;

val z = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^(bdd_utilsLib.make_bv 2 8))”;



val a_x1 = “arith_a ^x1”;
val a_x2 = “arith_a ^x2”;

val a_x3 = “arith_a ^x2”;
val a_x4 = “arith_a ^x4”;

val a_y1 = “arith_a ^y1”;
val a_y2 = “arith_a ^y2”;

val a_z = “arith_a ^z”;





(* rule 1 *)
val arith_policy_rule1 = “(arith_and ^a_y1 (arith_and  ^a_x1  ^a_x2) ,
                           action ("fwd",[1])):single_rule”;


(* rule 2 *)
val arith_policy_rule2 = “(arith_and ^a_y2 (arith_or (arith_and ^a_x1 ^a_x2) (arith_and ^a_x3 ^a_x4)) ,
                           action ("fwd",[2])):single_rule”;


(* rule 3 *)
val arith_policy_rule3 = “(arith_and
                           (arith_and ^a_y2 (arith_not
                                             (arith_or (arith_and ^a_x1 ^a_x2)
                                                       (arith_and ^a_x3 ^a_x4))))
                           ^a_z ,
                           action ("fwd",[3])):single_rule”;

(* rule 4 *)
val arith_policy_rule4 =  “(arith_and ^a_y1 (arith_or (arith_and ^a_x1 ^a_x2)
                                                      (arith_and ^a_x3 ^a_x4)) ,
                            action ("fwd",[4])):single_rule”;




(* Default policy rule *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;


(* Combined arith policy list *)
val arith_policy_figure1 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule_default
]:single_rule list”;


(* Combined policy mapping *)
val atoms_map =   “[
    ("x1", ^x1);
    ("x2", ^x2);
    ("x3", ^x3);
    ("x4", ^x4);
    ("y1", ^y1);
    ("y2", ^y2);
    ("z", ^z);
]”;


(****************************************)
(*   Best output table but worst order  *)
(****************************************)


(* Flat policy order *)
val policy_order = “["x1";"x2";"x3";"x4";"y1";"y2";"z"]”;

(* Grouped policy ordering *)
val policy_full_order = “[
  ("ip_dst",["x1";"x2";"x3";"x4"]);
  ("tcp_dst",["y1";"y2"]);
  ("ip_ttl" ,["z"])
]”;

(****************************)
(* worst output table order *)
(*    but better for MTBDD    *)
(****************************)

(*
val policy_order = “["y1";"x1";"x2";"x3";"x4";"y2";"z"]”;

(* Grouped policy ordering *)
val policy_full_order = “[
  ("tcp_dst1" ,["y1"]);
  ("ip_dst",["x1";"x2";"x3";"x4"]);
  ("tcp_dst2" ,["y2"]);
  ("ip_ttl" ,["z"])
]”;
*)



(********************)
(*  Testing scripts *)
(********************)
(* 
(* BDD alists + EVAL *)
val final_thm_res_eval =
fwd_proofLib.convert_arith_policy_to_interval_tables (arith_policy_figure1, atoms_map, test_pd_type, policy_full_order, policy_order);  *)



(* BDD alists + Cakeml w parser, just bin *)
val final_thm_res_cake = fwd_proof_cakeLib.convert_arith_policy_to_interval_tables_cake
                                          (arith_policy_figure1, atoms_map, test_pd_type, policy_full_order, policy_order,
"paper_example"); 


val _ = export_theory ();
