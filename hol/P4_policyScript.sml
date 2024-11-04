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


    
(* this must be fixed that the second element of access is just a (h_v x)*)
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





(*
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



EVAL “map_of_h_names  (tau_xtl st_ty [("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                ("internal", tau_xtl st_ty [("a'",tau_bit 1);("b'",tau_bit 1);
                                                            ("blah", tau_xtl st_ty [("blah2", tau_xtl st_ty [("a''",tau_bit 1);("b''",tau_bit 1);("c''",tau_bit 1)]);("b''",tau_bit 1);("c''",tau_bit 1)])]);
                                ("a",tau_bit 1)
                                ]) NONE ”;

*)


Definition size_xtl_def:
 (size_xtl (tau_bit n) =  n) /\
 (size_xtl (tau_xtl st_ty []) =  0) /\
 (size_xtl (tau_xtl st_ty (h::t)) = size_xtl (SND h) + size_xtl (tau_xtl st_ty  t))
End



(*
EVAL “size_xtl  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)])]))”;



EVAL “size_xtl  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)]);
                                 ("internal2", tau_xtl st_ty [("g",tau_bit 7)])]))”;

*)





Definition map_of_h_index_def:
  map_of_h_index (tau_xtl st_ty []) acc = [] ∧
  map_of_h_index (tau_xtl st_ty ((x,t)::xtl)) acc =
  case (t) of
  | (tau_bit n) => (acc, (acc + n - 1 ))::(map_of_h_index (tau_xtl st_ty (xtl)) (acc+n))
  | (tau_xtl st_ty xtl') => (map_of_h_index (tau_xtl st_ty (xtl')) (acc))++(map_of_h_index (tau_xtl st_ty (xtl)) (acc + size_xtl (tau_xtl st_ty xtl')))
End






(*

EVAL “map_of_h_index  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)])])) 0”;



EVAL “map_of_h_index  (tau_xtl st_ty ([("a",tau_bit 1);("b",tau_bit 1);("c",tau_bit 1);
                                 ("internal", tau_xtl st_ty [("g",tau_bit 1)]);
                                 ("internal2", tau_xtl st_ty [("g",tau_bit 7)])])) 0”;


*)



Definition mk_mem_def:
  mk_map_acc_idx hdr =
       let xl = (map_of_h_names hdr NONE) in
       let il =  (map_of_h_index hdr 0) in
        ZIP (xl,il)
End




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


(* we need to make pos_acc_c distinct, this is polymorph. so can be used on teh flattened list directlt*)
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



        

(* flattens the header access into a list of strings*)
(* NOTE this should be use eariler as well!*)
Definition flatten_acc_def:
  flatten_acc (h_v a) = [a] ∧
  flatten_acc (h_acc h1 h2) = (flatten_acc h1)++(flatten_acc h2)
End

        
(*
EVAL “flatten_acc  (h_acc (h_acc (h_v "internal") (h_v "f1")) (h_v "f2"))”;
*)


(*flattens a full list*)        
Definition flatten_acc_l_def:
  flatten_acc_l [] = [] ∧
  flatten_acc_l (x::l) = (flatten_acc x)::(flatten_acc_l l)
End


(*
EVAL “flatten_acc_l  [(h_acc (h_acc (h_v "internal") (h_v "f1")) (h_v "f1"));
                      (h_acc (h_acc (h_v "internal") (h_v "f1")) (h_v "f2"));          
                      (h_v "f2")]”;
*)

(*
Definition gcd_members_def:
  gcd_members [] [] = ([],[]) ∧
  gcd_members (x1::l2) (x2::l2) =
  case (x1 = x2) of
  | T => (x1::(gcd_members l1 l2))
  | F => (x1::(gcd_members l1 l2))
End



        
(* checks a single access with respect a list if it is part of it*)
Definition mk_smallest_distinct_h_def:
  mk_smallest_distinct_h [[]] = [[]] ∧
  mk_smallest_distinct_h x::l =  
End

*)
















val _ = export_theory ();
