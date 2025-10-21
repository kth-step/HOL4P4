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
open alistTheory;
open set_relationTheory;
open pred_setTheory;
open pred_setLib;

open bdd_genTheory;     
open pred_specTheory;     
open policy_specTheory;     
open tables_spec_oldTheory;

open table_bs_propertiesTheory;
     
open policy_arith_to_varTheory;


val _ = new_theory "table_var_to_arith";


    

(* todo :
 every_is_some_in_l change to all_is_some 
*)

    
(*===============================*)
(*      Types of arith tables    *)
(*===============================*)


Type arith_row = “:(arithm_atom list # num # 'a action_expr)”;
Type arith_table = “: ('a arith_row) list”
Type arith_table_list = “: ('a arith_table) list”


val _ = Hol_datatype `
  pd_type = 
     type_length of num   
   | type_record of (string # pd_type) list  (* [f1:bs; ...; fn:bs_n] *)
`;

Type pd_type_struct = “: (string # pd_type) list”; 



(*============================*)
(*    Auxiliary definitions   *)
(*============================*)

(*
        
Definition check_widths_interval_def:
  check_widths_interval (v1,w1) (v2,w2) (v3,w3) (v4,w4) = 
  (w1 = w2 ∧ w2 = w3 ∧ w3 = w4 ∧
   LENGTH v1 = w1 ∧
   LENGTH v2 = w1 ∧
   LENGTH v3 = w1 ∧
   LENGTH v4 = w1  
  )
End



Definition check_widths_bs_def:
  check_widths_bs (v1,w1) (v2,w2) = 
  (w1 = w2 ∧
   LENGTH v1 = w1 ∧
   LENGTH v2 = w1 
  )
End
*)


        
Definition get_lval_def:
  get_lval (a_True) = NONE ∧
  get_lval (a_False) = NONE ∧
  get_lval (arithm_ge lv _) = SOME lv ∧
  get_lval (arithm_le lv _) = SOME lv
End

        
(* given a struct type and lval, this retrives the field type
 or bs width *)
Definition resolve_lval_type_def:
  resolve_lval_type pd_type lval =
  case lval of
  | lv_x var => ALOOKUP pd_type var
  | lv_acc lval var => 
      case resolve_lval_type pd_type lval of
      | SOME (type_record fields) => ALOOKUP fields var
      | _ => NONE
End

        

(*
Definition resolve_pd_min_max_def:
  resolve_pd_min_max pd_type lval =
    case resolve_lval_type pd_type lval of
      | SOME (type_length n) => SOME ((fixwidth n (n2v 0), n), ( fixwidth n (n2v (max_from_type n)), n)  )
      | _ => NONE
End
  *)      

Definition bv_ge_than_def:
  bv_ge_than bv bv' =
  bitv_binpred binop_ge bv bv'
End


Definition bv_le_than_def:
  bv_le_than bv bv' =
  bitv_binpred binop_le bv bv'
End

(*
Definition bv_gt_than_def:
  bv_gt_than bv bv' =
  bitv_binpred binop_gt bv bv'
End


Definition bv_lt_than_def:
  bv_lt_than bv bv' =
  bitv_binpred binop_lt bv bv'
End
  *)      
        
Definition add_one_to_bv_def:
  add_one_to_bv bv=
  let (b,v) = bv in
    case bitv_binpred binop_ge (b,v) (n2v (max_from_type v), v) of
    | SOME F =>  bitv_binop binop_add (b,v) (n2v 1, v)
    | _ => NONE
End
     

Definition sub_one_of_bv_def:
  sub_one_of_bv bv=
  let (b,v) = bv in
    if ((fixwidth v b,v) ≠ (fixwidth v (n2v 0) , v)) then
      bitv_binop binop_sub (b,v) (n2v 1, v) 
    else
      NONE
End

        
(*==========================================*)
(*    var atoms to arith atom conversion    *)
(*==========================================*)

    
(* Convert atom_var to arithm_atom using me
   i.e. each cell in the line of var table will be converted
   directly to an aritmetic atom via this def. *)
   
Definition var_atom_to_arith_def:
  var_atom_to_arith me g =
  case g of
  | True => SOME a_True
  | False => SOME a_False
  | NotTrue => SOME a_False
  | NotFalse=> SOME a_True
  | Var x => ALOOKUP me x
  | Not x => 
      (case ALOOKUP me x of
       | SOME a_True => SOME a_False
       | SOME a_False => SOME a_True
       | SOME (arithm_ge lv (bl, len)) =>                 
           (
           if (fixwidth len bl, len) = (fixwidth len (n2v 0), len) then
             SOME a_False                                 (* ¬(a ≥ 0) is a_False *)
                                                          
           else
             (case sub_one_of_bv (bl, len) of
              | NONE => NONE
              | SOME bv' => SOME (arithm_le lv bv'))      (* ¬(a ≥ b) is (a ≤ b-1) *)
           )


      | SOME (arithm_le lv (bl, len)) =>                 
           (
           if (bl, len) = (n2v (max_from_type len), len) then
             SOME a_False                                 (* ¬(a ≤ max) is a_False *)
           else
             (case add_one_to_bv (bl, len) of
              | NONE => NONE
              | SOME bv' => SOME (arithm_ge lv bv'))      (* ¬(a ≤ b) is (a ≥ b+1) *)
           )
      | NONE => NONE
      )
End

                                            
(*

EVAL ``var_atom_to_arith [("x", arithm_ge (lv_x "y") (fixwidth 3 (n2v 0),3))] (Not (Var "x"))``; (*false*)
EVAL ``var_atom_to_arith [("x", arithm_ge (lv_x "y") (fixwidth 3 (n2v 7),3))] (Not (Var "x"))``; (*x < 6*)
EVAL ``var_atom_to_arith [("x", arithm_le (lv_x "y") (fixwidth 3 (n2v 7),3))] (Not (Var "x"))``; (*False*)
EVAL ``var_atom_to_arith [("x", arithm_le (lv_x "y") (fixwidth 3 (n2v 0),3))] (Not (Var "x"))``; (*x>1*)

EVAL ``var_atom_to_arith [("x", arithm_le (lv_x "y") (fixwidth 3 (n2v 8),3))] (Not (Var "x"))``; 

EVAL “bitv_binpred binop_ge (fixwidth 3 (n2v 8)      ,3)
                            (n2v (max_from_type 3)   ,3)”


     
*)
        

Definition convert_var_list_to_arith_def:
  convert_var_list_to_arith var_guards me =
      MAP (λg. var_atom_to_arith me g) var_guards
End


Definition every_is_some_in_l_def:
  every_is_some_in_l var_tbl_opt =
  EVERY (λ(opt_guards,_,_). EVERY IS_SOME opt_guards) var_tbl_opt
End


Definition rm_optl_def:
  rm_optl var_tbl_opt =
  MAP (λ(arithl_opt, st, res). MAP (\g. THE g) arithl_opt , st, res) var_tbl_opt
End

        
Definition convert_var_rows_to_arith_def:
  convert_var_rows_to_arith var_table me =
      MAP (λ(var_guards,st,res). convert_var_list_to_arith var_guards me, st, res) var_table
End


        
Definition convert_var_to_arith_table_def:
  convert_var_to_arith_table var_table me =
    let converted = convert_var_rows_to_arith var_table me in
    if every_is_some_in_l converted ∧ var_table ≠ [] then
      SOME (rm_optl converted)
    else
      NONE
End


(*============================*)
(*    arith table semantics   *)
(*============================*)

        
        
Definition is_arith_guards_true_def:
  is_arith_guards_true arith_guards pd= 
  EVERY (λ arith_atom. eval_arithm_atom pd arith_atom = SOME T ) arith_guards
End      

         
Definition is_arith_match_row_def:
  is_arith_match_row st_in st_num artih_atoml pd = 
    ((st_in = st_num) ∧ is_arith_guards_true artih_atoml pd ∧ artih_atoml ≠ [])
End

        
Definition check_arith_table_sem_def:
  check_arith_table_sem st_in (arith_table: 'a arith_table) pd =                     
  MAP (\(arith_guards,st,res). (is_arith_match_row st_in st arith_guards pd, res) )  arith_table
End


Definition match_arith_table_def:
  match_arith_table (arith_table:'a arith_table) pd st_in =
    let res = check_arith_table_sem st_in arith_table pd in
      case min_idx_till res T of
        SOME (idx, line) => SOME (SND line)
      | NONE => NONE
End

        
(*
val test_pd = ``[("ttl", val_bs (fixwidth 8 (n2v 0), 8));
                 ("src", val_bs (fixwidth 8 (n2v 0), 8))]``;
                 
val test_me = ``[("x1", arithm_ge (lv_x "ttl") (fixwidth 8 (n2v 5), 8));
                ("x2",  arithm_le (lv_x "src") (fixwidth 8 (n2v 3), 8))]``;


val test_var_table = ``[
  ([True; Var "x1"; Var "x2"], 1n, action "fwd1");
  ([False; Var "x1"; Not "x2"], 1n, action "fwd2");
  ([Var "x2"; Not "x2"], 1n, action "fwd3");
  ([True], 1n, action "drop")
]``;

                        
val test_arith_table = 
  EVAL ``convert_var_to_arith_table ^test_var_table ^test_me``;

val arith_table = optionSyntax.dest_some (rhs (concl test_arith_table));

EVAL ``match_arith_table  ^arith_table  ^test_pd (1:num)``
                                    
*)



(*===============================================*)
(*  Proof of : sem var_table = sem arith_table   *)
(*===============================================*)


                          
val bitv_normalize_imp1_tac =
(gvs[sub_one_of_bv_def, add_one_to_bv_def] >>

 imp_res_tac bitv_binpred_same_length >>
 imp_res_tac bitv_binpred_range_length >>
 imp_res_tac all_bs_larger_than_zero >>
 imp_res_tac all_bs_larger_than_zero2 
);

                
        
Theorem sem_var_arith_atom_imp1:
  ∀ var_atom me mv packet_input arith_atom b.
    (∀var arith_atom'.
       ALOOKUP me var = SOME arith_atom' ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input arith_atom') ∧
    sem_var_atom var_atom mv = SOME b ∧
    var_atom_to_arith me var_atom = SOME arith_atom ⇒
    eval_arithm_atom packet_input arith_atom = SOME b
Proof

  Cases_on ‘var_atom’ >> rpt strip_tac >> gvs[]  >|[
            
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def] >>    
    res_tac >>
    gvs[] 
    ,

    gvs[sem_var_atom_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
   
    rgs[Once var_atom_to_arith_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    res_tac >>

    fs[] >>
         
    (* this portion resolves goals 1 and 2 of not True and not False *)
    rgs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]  >>      
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[sem_var_atom_def] >>
    gvs[Once eval_arithm_atom_def] >|[
             
        (* goal 3 of ¬(a ≥ 0) converted to a_False*)
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[] 
        ,
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[]    
        ,
        (* goal 5 interesting case of not ge *)
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[] >>
        
        rename1 ‘bitv_binpred binop_ge (lval_bl, len) (n,len) = SOME bool’ >>
        rename1 ‘bitv_binop binop_sub (n,len) (n2v 1,len) = SOME n_plus_1’ >>
        
        imp_res_tac bitv_binpred_ge_bool_conv1 
        ,
        (*goal 6 *)
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[] >>

        imp_res_tac every_bs_is_less_than_max >>
        gvs[]                                                                       
        ,
        (*goal 7 *)
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[] >>
              
        imp_res_tac every_bs_is_less_than_max >>
        gvs[]
        ,
    
        bitv_normalize_imp1_tac >>
        PairCases_on ‘p’ >>
        gvs[] >>
    
        gvs[add_one_to_bv_def] >>
        BasicProvers.FULL_CASE_TAC >> gvs[] >>
    
        rename1 ‘bitv_binpred binop_le (lval_bs,len) (n,len) = SOME bool’ >>
        rename1 ‘bitv_binop binop_add (n,len) (n2v 1,len) = SOME n'’ >>
        imp_res_tac bitv_binpred_le_bool_conv1
        ]
  ]
QED




Theorem var_atom_to_arith_not_never_none_mv:
  ∀ mv me packet_input arith_atom b s.
    
    (∀var . lookup_is_some mv var = lookup_is_some me var) ∧
    (∀var arith_atom'.
       ALOOKUP me var = SOME arith_atom' ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input arith_atom') ∧
       
    eval_arithm_atom packet_input arith_atom = SOME b ∧
    var_atom_to_arith me (Not s) = SOME arith_atom  ⇒
    ALOOKUP mv s ≠ NONE
Proof

  rpt strip_tac >>
  rgs[Once var_atom_to_arith_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  res_tac >>
  fs[eval_arithm_atom_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[lookup_is_some_def] >>
  res_tac >> gvs[]
QED

        
     
Theorem sem_var_arith_atom_imp2:
  ∀ var_atom me mv packet_input arith_atom b.
    (∀var. lookup_is_some mv var ⇔ lookup_is_some me var) ∧
    (∀var arith_atom'.
       ALOOKUP me var = SOME arith_atom' ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input arith_atom') ∧
    eval_arithm_atom packet_input arith_atom = SOME b ∧
    var_atom_to_arith me var_atom = SOME arith_atom ⇒
    sem_var_atom var_atom mv = SOME b 
Proof
  Cases_on ‘var_atom’ >> rpt strip_tac >> gvs[]  >|[
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,       
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]       
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def]
    ,
    gvs[Once var_atom_to_arith_def, Once eval_arithm_atom_def, sem_var_atom_def] >>    
    res_tac >>
    fs[] 
    ,
    gvs[sem_var_atom_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    imp_res_tac var_atom_to_arith_not_never_none_mv >>
    
    rgs[Once var_atom_to_arith_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    
    (fs[Once eval_arithm_atom_def]  >>
     fs[sub_one_of_bv_def] >>
     
     res_tac >>
     fs[Once eval_arithm_atom_def]  >>
     rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
     
     imp_res_tac bitv_binpred_same_length >>
     imp_res_tac bitv_binpred_range_length >>
     
     Cases_on ‘p’ >> gvs[] >>
     
     imp_res_tac all_bs_larger_than_zero2 >>
     gvs[]) >|[
        
        imp_res_tac bitv_binpred_ge_bool_conv1 >>
        gvs[]
        ,
        imp_res_tac every_bs_is_less_than_max >>
        gvs[]
        ,
        imp_res_tac every_bs_is_less_than_max >>
        gvs[]
        ,
        
        gvs[add_one_to_bv_def] >>
        BasicProvers.FULL_CASE_TAC >> gvs[] >>
        imp_res_tac bitv_binpred_le_bool_conv1 >>
        gvs[]     
      ]
  ]
QED



                                                  
Theorem atoml_var_arith_correct:
  ∀var_guards me packet_input mv x var_table arith_st arith_res.
    (∀var. lookup_is_some mv var ⇔ lookup_is_some me var) ∧
    (∀var arith_atom'.
       ALOOKUP me var = SOME arith_atom' ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input arith_atom') ∧
    
    (∀n. n < LENGTH var_guards ⇒
         IS_SOME (var_atom_to_arith me (EL n var_guards)))  ⇒
    is_atoml_true var_guards mv =
    is_arith_guards_true (MAP (λg. THE (var_atom_to_arith me g)) var_guards)  packet_input 
Proof
  rw[is_atoml_true_def, is_arith_guards_true_def] >>
  gvs[] >>
  EQ_TAC >> strip_tac  >>
  
  (gvs[EVERY_EL] >>
   rpt strip_tac >>
   gvs[] >>
   res_tac >>
   
   gvs[EL_MAP] >>
   res_tac >>
   Cases_on ‘var_atom_to_arith me (EL n var_guards)’ >> rgs[] >>
   res_tac) >>
   
  imp_res_tac sem_var_arith_atom_imp1 >>
  imp_res_tac sem_var_arith_atom_imp2
QED



Triviality every_is_some_in_l_rest_of_list:
  ∀ var_table h me.
    every_is_some_in_l (convert_var_rows_to_arith (h::var_table) me) ⇒
    every_is_some_in_l (convert_var_rows_to_arith var_table me)
Proof
  gvs[every_is_some_in_l_def, convert_var_to_arith_table_def, convert_var_rows_to_arith_def]
QED




                                                  
        
Theorem convert_var_to_arith_table_length:
  ∀ var_table arith_table me.
    convert_var_to_arith_table var_table me = SOME arith_table ⇒
    LENGTH arith_table = LENGTH var_table
Proof
  Induct >>
  rpt strip_tac >>
  gvs[convert_var_to_arith_table_def] >>
  imp_res_tac every_is_some_in_l_rest_of_list >>
  res_tac  >>
  Cases_on ‘var_table = []’ >> gvs[] >|[
    PairCases_on ‘h’ >>
    gvs[convert_var_rows_to_arith_def,
        convert_var_list_to_arith_def,
        rm_optl_def]
    ,
                 
    simp[convert_var_rows_to_arith_def] >>
    simp[Once rm_optl_def]
  ]
QED

        


                                


Theorem all_rows_var_arith_correct:
  ∀var_table arith_table me packet_input mv st_in.
    (∀var. lookup_is_some mv var ⇔ lookup_is_some me var) ∧
    (∀var atom. 
       ALOOKUP me var = SOME atom ⇒ 
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    (convert_var_to_arith_table var_table me = SOME arith_table) ⇒
    check_all_rows_match st_in var_table mv = check_arith_table_sem st_in arith_table packet_input
Proof                                                                      
  rw[check_all_rows_match_def, check_arith_table_sem_def] >>
  simp[LIST_EQ_REWRITE] >>
  ‘LENGTH arith_table = LENGTH var_table’ by metis_tac[convert_var_to_arith_table_length] >>
  gvs[] >> rpt strip_tac >>
  gvs[EL_MAP] >>
  Cases_on ‘EL x var_table’ >> Cases_on ‘r’ >>
  Cases_on ‘EL x arith_table’ >> Cases_on ‘r’ >>
  
  rename1 ‘EL x var_table = (var_guards,var_st,var_res)’ >>
  rename1 ‘EL x arith_table = (arith_guards,arith_st,arith_res)’ >>
  
  gvs[convert_var_to_arith_table_def] >>
  gvs[every_is_some_in_l_def] >>
  
  gvs[rm_optl_def] >>
  gvs[EL_MAP] >>
  
  Cases_on ‘EL x (convert_var_rows_to_arith var_table me)’ >> Cases_on ‘r’ >>
  rename1 ‘EL x (convert_var_rows_to_arith var_table me) = (op_var_guards,op_var_st,op_var_res)’ >>
  gvs[] >>
  
  gvs[convert_var_rows_to_arith_def] >>
  gvs[EL_MAP] >>
  gvs[MEM_MAP] >>
  
  gvs[convert_var_list_to_arith_def] >>
  gvs[is_match_row_def, is_arith_match_row_def] >>
  
  gvs[MAP_MAP_o] >>
  rw[combinTheory.o_DEF] >>
  
  gvs[EVERY_EL] >>
  res_tac >>
  gvs[EL_MAP]  >>

  
  ‘is_atoml_true var_guards mv =
   is_arith_guards_true (MAP (λg. THE (var_atom_to_arith me g)) var_guards)  packet_input’ by metis_tac[atoml_var_arith_correct] >>

  metis_tac[]
QED
                                                                                                    
             

                      
Theorem table_var_arith_correct:       
  ∀var_table arith_table me packet_input mv st_in.
    (∀var. lookup_is_some mv var ⇔ lookup_is_some me var) ∧
    (∀var atom. 
       ALOOKUP me var = SOME atom ⇒ 
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    (convert_var_to_arith_table var_table me = SOME arith_table) ⇒
    match_tbl var_table mv st_in = match_arith_table arith_table packet_input st_in
Proof
  rw[match_tbl_def, match_arith_table_def] >>
  ‘check_all_rows_match st_in var_table mv =
   check_arith_table_sem st_in arith_table packet_input’ by metis_tac[all_rows_var_arith_correct] >>
  gvs[]
QED



val _ = export_theory ();







