open HolKernel boolLib liteLib simpLib Parse bossLib;
open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_coreTheory;


open bitstringTheory;
open wordsTheory;
open optionTheory;
open sumTheory;
open stringTheory;
open ottTheory;
open pairTheory;
open rich_listTheory;
open arithmeticTheory;
open alistTheory;
open numeralTheory;




val _ = new_theory "p4_policy";



val _ = Hol_datatype `
h =  (* expression *)
   h_v of x  (* value *)
 | h_acc of h => h (* access *)
`;





(* create a mapping instead of this, from the start! *)
Definition map_of_h_names_def:
  map_of_h_names (tau_xtl st_ty []) st_op = [] ∧
  map_of_h_names (tau_xtl st_ty ((x,t)::xtl)) st_op =
  case st_op of
  | NONE =>
      (case t of
       | (tau_bit n) => (h_v x)::(map_of_h_names (tau_xtl st_ty xtl) NONE)
       | (tau_xtl st_ty xtl') => (map_of_h_names (tau_xtl st_ty xtl') (SOME (h_v x)))++(map_of_h_names (tau_xtl st_ty xtl) NONE)
      )
  | SOME x'  =>
      (case t of
       | (tau_bit n) => (h_acc (x') (h_v x))::(map_of_h_names (tau_xtl st_ty xtl) (SOME x'))
       | (tau_xtl st_ty xtl') => (map_of_h_names (tau_xtl st_ty xtl') (SOME (h_acc x' (h_v x))))++(map_of_h_names (tau_xtl st_ty xtl) (SOME x'))
      )
End






EVAL “map_of_h_names  (tau_xtl st_ty [("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                ("internal", tau_xtl st_ty [("a'",tau_bit 1);("b'",tau_bit 1);("c'",tau_bit 1)]);
                                ("blah", tau_xtl st_ty [("a''",tau_bit 1);("b''",tau_bit 1);("c''",tau_bit 1)])]) NONE ”;


EVAL “map_of_h_names  (tau_xtl st_ty [("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                ("internal", tau_xtl st_ty [("a'",tau_bit 1);("b'",tau_bit 1);
                                                            ("blah", tau_xtl st_ty [("a''",tau_bit 1);("b''",tau_bit 1);("c''",tau_bit 1)])])
                                ]) NONE ”;


EVAL “map_of_h_names  (tau_xtl st_ty [("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                ("internal", tau_xtl st_ty [("a'",tau_bit 1);("b'",tau_bit 1);
                                                            ("blah", tau_xtl st_ty [("a''",tau_bit 1);("b''",tau_bit 1);("c''",tau_bit 1)])]);
                                ("a",tau_bit 1)
                                ]) NONE ”;






Definition size_xtl_def:
 (size_xtl (tau_bit n) =  n) /\
 (size_xtl (tau_xtl st_ty []) =  0) /\
 (size_xtl (tau_xtl st_ty (h::t)) = size_xtl (SND h) + size_xtl (tau_xtl st_ty  t))
End




EVAL “size_xtl  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)])]))”;



EVAL “size_xtl  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)]);
                                 ("internal2", tau_xtl st_ty [("g",tau_bit 7)])]))”;







Definition map_of_h_index_def:
  map_of_h_index (tau_xtl st_ty []) acc = [] ∧
  map_of_h_index (tau_xtl st_ty ((x,t)::xtl)) acc =
  case (t) of
  | (tau_bit n) => (acc, (acc + n - 1 ))::(map_of_h_index (tau_xtl st_ty (xtl)) (acc+n))
  | (tau_xtl st_ty xtl') => (map_of_h_index (tau_xtl st_ty (xtl')) (acc))++(map_of_h_index (tau_xtl st_ty (xtl)) (acc + size_xtl (tau_xtl st_ty xtl')))
End








EVAL “map_of_h_index  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)])])) 0”;



EVAL “map_of_h_index  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)]);
                                 ("internal2", tau_xtl st_ty [("g",tau_bit 7)])])) 0”;





(*
Definition mk_h_map_def:
  mk_map_acc_idx hdr =
        ZIP(map_of_h_names hdr,map_of_h_index hdr)
End
*)



val _ = Hol_datatype `
e =  (* expression *)
e_larger of h  =>  num_exp
| e_less   of h =>  num_exp
| e_eq   of h => num_exp
`;


val _ = Hol_datatype `
c =  (* expression *)
c_and of c => c
| c_or   of c => c
| c_neg   of c
| c_e   of e
`;



Definition pos_acc_e_def:
  pos_acc_e (e_larger e1 e2) = [e1] ∧
  pos_acc_e (e_less e1 e2) = [e1] ∧
  pos_acc_e (e_eq e1 e2) = [e1]
End


Definition pos_acc_c_def:
  pos_acc_c (c_e e) = pos_acc_e (e) ∧
  pos_acc_c (c_neg c) = pos_acc_c (c) ∧
  pos_acc_c (c_and c1 c2) = pos_acc_c (c1)++ pos_acc_c (c2) ∧
  pos_acc_c (c_or c1 c2) = pos_acc_c (c1)++ pos_acc_c (c2)
End


(* we need to make pos_acc_c distinct*)
Definition mk_distinct_def:
  mk_distinct [] = [] ∧
  mk_distinct (x::l) =
  case MEM x l of
  | T => (mk_distinct l)
  | F => x::(mk_distinct l)
End

(*
val h_a = “h_v "a" ”;
val h_b = “h_v "b" ”;
val h_c = “h_v "c" ”;
val h_internal_f = “h_acc (h_v "internal") (h_v "f") ”;
val h_internal_g = “h_acc (h_v "internal") (h_v "g") ”;
val e_larger1 = “e_larger ^h_a 3”;
val e_less1   = “e_less ^h_b 3”;
val e_less2   = “e_less ^h_internal_f 3”;
val e_eq1     = “e_eq ^h_internal_g 7 ”;
val c1     = “c_or (c_e ^e_less1) (c_e ^e_less2)”;




EVAL “ pos_acc_c  (c_or ^c1 ^c1)  ”;
EVAL “ mk_distinct (pos_acc_c  (c_or ^c1 ^c1) ) ”;
*)



(*
Definition mk_distinct_h_def:
  mk_distinct_h [] = [] ∧
  mk_distinct x::l =
  case x of
  | (h_v _) => mk_distinct l
  | (h_acc a b) =>


End
*)

















val _ = export_theory ();
