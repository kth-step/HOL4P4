open HolKernel boolLib liteLib simpLib Parse bossLib;
open policy_arith_to_varTheory;
open bdd_utilsLib;


val _ = new_theory "paper_example_cakeml_best";

(* ---------------------------------------------------------------------------
   Paper running example (Figures 1, 4, and 5).
 
   This script encodes the forwarding policy from Figure 1 of the paper.
   It runs the POLYGRAM pipeline on it, and produces a certified proof of
   semantic equivalence between the high-level policy and the generated
   P4 interval tables using cakeml MTBDD construction
 
   The policy governs a switch connected to two internal networks:
     LAN1: 10.0.0.*       (ip.dst in [10.0.0.0,   10.0.0.255])
     LAN2: 192.168.*.*    (ip.dst in [192.168.0.0, 192.168.255.255])
 
   Rules (Figure 1):
     Rule 1: tcp.dstport <= 1023 /\ ip.dst in 10.0.0.* : fwd(1)
     Rule 2: tcp.dstport >= 49152 /\ ip.dst in 10.0.0.* or 192.168.*.* : fwd(2)
     Rule 3: tcp.dstport >= 49152 /\ ip.dst not in 10.0.0.* or 192.168.*.* /\ ip.ttl >= 2  : fwd(3)
     Rule 4: tcp.dstport <= 1023 /\ ip.dst in 10.0.0.* or 192.168.*.*  : fwd(4)
     Default: T : drop()
 
   Atomic predicates and variable mapping m (Figure 4):
     x1 -> ip.dst >= 10.0.0.0
     x2 -> ip.dst <= 10.0.0.255
     x3 -> ip.dst >= 192.168.0.0
     x4 -> ip.dst <= 192.168.255.255
     y1 -> tcp.dstport <= 1023
     y2 -> tcp.dstport >= 49152
     z  -> ip.ttl >= 2
   --------------------------------------------------------------------------- *)
 


Type single_rule = “:((string# num list) action_expr) arith_rule”;



(* Packet type descriptor: encodes the bit-vector width of each header field
   Used by trans-back to compute interval complements (Section IV-D) *)
val test_pd_type = “["h", type_record [("ip", type_record [("dst", type_length 32);
                                                           ("ttl", type_length 8);]);
                                       ("tcp", type_record [("dstPort", type_length 16)])]]”;



(* Atomic predicates over packet header fields (Figure 4, atoms map m),
   subnet membership is expressed as a pair of bounds using >= and <=,
   make_bv converts a decimal value to a bit-vector of the given width *)

(* ip.dst  between 10.0.0.0 and 10.0.0.255*)
val x1 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 167772160 32))”;
val x2 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 167772415 32))”;

(* ip.dst  between 192.168.0.0 and 192.168.255.255 *)
val x3 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 3232235520 32))”;
val x4 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "ip") "dst") ^(bdd_utilsLib.make_bv 3232301055 32))”;

(* tcp.dstport <= 1023  (standard-service traffic) *)
val y1 = “(arithm_le (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 1023 16))”;

(* tcp.dstport >= 49152 (dynamic-port traffic) *)
val y2 = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "tcp") "dstPort") ^(bdd_utilsLib.make_bv 49152 16))”;

(* ip.ttl >= 2 *)
val z = “(arithm_ge (lv_acc (lv_acc (lv_x "h") "ip") "ttl") ^(bdd_utilsLib.make_bv 2 8))”;


(* Lift atomic predicates to the arith_a constructor of the policy language *)

val a_x1 = “arith_a ^x1”;
val a_x2 = “arith_a ^x2”;

val a_x3 = “arith_a ^x3”;
val a_x4 = “arith_a ^x4”;

val a_y1 = “arith_a ^y1”;
val a_y2 = “arith_a ^y2”;

val a_z = “arith_a ^z”;


(* Mapping m from variable names to atomic predicates (Figure 4, atoms map).
   Used by trans-fwd (Stage 1) and trans-back (Stage 3). *)
val atoms_map =   “[
    ("x1", ^x1);
    ("x2", ^x2);
    ("x3", ^x3);
    ("x4", ^x4);
    ("y1", ^y1);
    ("y2", ^y2);
    ("z", ^z);
]”;


(* Policy rules (Figure 1).
   each rule is a pair (predicate, action) of type single_rule.
   rules are evaluated in order; the first matching rule applies. *)

(* Rule 1: tcp.dstport <= 1023 /\ ip.dst in 10.0.0.* : fwd(1) *)
val arith_policy_rule1 = “(arith_and ^a_y1 (arith_and  ^a_x1  ^a_x2) ,
                           action ("fwd",[1])):single_rule”;



(* Rule 2: tcp.dstport >= 49152 /\ ip.dst in 10.0.0.* or 192.168.*.* : fwd(2) *)
val arith_policy_rule2 = “(arith_and ^a_y2 (arith_or (arith_and ^a_x1 ^a_x2) (arith_and ^a_x3 ^a_x4)) ,
                           action ("fwd",[2])):single_rule”;



(* Rule 3: tcp.dstport >= 49152 /\ ip.dst not in 10.0.0.* or 192.168.*.* /\ ip.ttl >= 2  : fwd(3) *)
val arith_policy_rule3 = “(arith_and
                           (arith_and ^a_y2 (arith_not
                                             (arith_or (arith_and ^a_x1 ^a_x2)
                                                       (arith_and ^a_x3 ^a_x4))))
                           ^a_z ,
                           action ("fwd",[3])):single_rule”;


(* Rule 4: tcp.dstport <= 1023 /\ ip.dst in 10.0.0.* or 192.168.*.*  : fwd(4) *)
val arith_policy_rule4 =  “(arith_and ^a_y1 (arith_or (arith_and ^a_x1 ^a_x2)
                                                      (arith_and ^a_x3 ^a_x4)) ,
                            action ("fwd",[4])):single_rule”;


(* Default: T : drop() *)
val arith_policy_rule_default = “(arith_a a_True, action ("drop", [])):single_rule”;


(* Complete policy: ordered list of rules as in Figure 1 *)
val arith_policy_figure1 = “[
    ^arith_policy_rule1;
    ^arith_policy_rule2;
    ^arith_policy_rule3;
    ^arith_policy_rule4;
    ^arith_policy_rule_default
]:single_rule list”;





(* ----------------------------------------------------------------------- *)
(*                  Variable orders for MTBDD construction                 *)
(*                                                                         *)
(*  The variable order affects MTBDD size but not correctness (Section V). *)
(* ----------------------------------------------------------------------- *)


(****************************************)
(*          best  order                 *)
(****************************************)


val policy_order = “["y1";"x1";"x2";"x3";"x4";"y2";"z"]”;

(* Grouped policy ordering *)
val variables_grouping = “[
  ("tcp_dst1" ,["y1"]);
  ("ip_dst",["x1";"x2";"x3";"x4"]);
  ("tcp_dst2" ,["y2"]);
  ("ip_ttl" ,["z"])
]”;





(** ----------------------------------------------------------------------- *)
(*  Pipeline invocation                                                     *)
(*                                                                          *)
(*  Two pipeline variants are available (Section VI):                      *)
(*       fwd_proof_cakeLib -- delegates MTBDD construction to verified     *)
(*                           CakeML binaries; I/O serialization is TCB     *)
(*                           (faster; see Table II CakeML columns)         *)
(* ----------------------------------------------------------------------- *)



(* BDD alists + Cakeml w parser, just bin *)
val final_thm_res_cake = fwd_proof_cakeLib.convert_arith_policy_to_interval_tables_cake
                                          (arith_policy_figure1, atoms_map, test_pd_type, variables_grouping, policy_order,
"paper_example_cakeml_best"); 


val _ = export_theory ();
