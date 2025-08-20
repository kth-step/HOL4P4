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
open tables_specTheory;

open table_bs_propertiesTheory;
     
open policy_arith_to_varTheory;
open table_var_to_arithTheory;

val _ = new_theory "table_arith_to_interval";


(*==========================================*)
(*         Types of interval tables         *)
(*==========================================*)       
val _ = Hol_datatype ` 
  interval = Empty | Single of bitv => bitv
`;

val _ = Hol_datatype ` 
  interval_key = key_val of arith_lv | key_const of bitv
`;

        
Type intvl_row        = “:(interval list # num # 'a action_expr)”;
Type intvl_table      = “:(interval_key # 'a intvl_row list)”;
Type intvl_table_list = “:('a intvl_table ) list”;



Definition wf_bit_def:
  wf_bit (bl,len) =
         (LENGTH bl = len)
End


Definition mk_max_bv_def:
  mk_max_bv bit_len =
  (fixwidth bit_len (n2v (max_from_type bit_len)),bit_len)
End
           
Definition mk_min_bv_def:
  mk_min_bv bit_len =
  (fixwidth bit_len (n2v 0),bit_len)
End        



(*===============================================*)
(*       convert arith table to interval table   *)
(*===============================================*)

           
Definition arith_to_interval_def:
  arith_to_interval a bit_len =
    case a of
    | a_True => SOME (Single (mk_min_bv bit_len) (mk_max_bv bit_len))
    | a_False => SOME Empty
    | arithm_ge _ n =>
        (let (bl,len) = n in
          if (bit_len = len) ∧ wf_bit n  then
             SOME (Single n (mk_max_bv bit_len))
           else
             NONE)
          
    | arithm_le _ n =>
        (let (bl,len) = n in
           if (bit_len = len) ∧ wf_bit n then
              SOME (Single (mk_min_bv bit_len) n)
            else
              NONE)
End



Definition convert_arith_list_to_interval_def:
  convert_arith_list_to_interval arith_guards bit_len =
      MAP (λg. arith_to_interval g bit_len) arith_guards 
End

        
Definition convert_arith_rows_to_arith_def:
  convert_arith_rows_to_arith arith_table bit_len =
      MAP (λ(arith_guards,st,res). convert_arith_list_to_interval arith_guards bit_len, st, res) arith_table
End




(*
still incorrect cause this table blends ttl and src
EVAL “convert_arith_rows_to_arith
      [([a_True;
         arithm_ge (lv_x "ttl") (fixwidth 8 (n2v 1),8);
         arithm_le (lv_x "src") (fixwidth 8 (n2v 3),8)],1, action "fwd1");
        
       ([arithm_ge (lv_x "src") (fixwidth 8 (n2v 4),8)],1,action "fwd2");
       
        ([a_True],1,action "drop")] 8”


        
*)





Definition valid_line_def:
  valid_line (guards, s, res) = (guards ≠ [])
End


Definition valid_table_def:
  valid_table table = 
    ((table ≠ []) ∧ EVERY valid_line table)
End

(*
Definition valid_tables_def:
  valid_tables tables = EVERY valid_table tables
End
*)

        

val _ = Hol_datatype ` 
  ret_arth_indic = isTrue | isFalse | is_lval of arith_lv
`;
      




Definition arth_indic_in_lval_def:
  arth_indic_in_lval isTrue = F ∧
  arth_indic_in_lval isFalse = F ∧
  arth_indic_in_lval (is_lval _) = T           
End


      
Definition get_lval_from_arith:
  get_lval_from_arith a_True = isTrue ∧
  get_lval_from_arith a_False = isFalse ∧
  get_lval_from_arith (arithm_ge lv _) = is_lval lv ∧
  get_lval_from_arith (arithm_le lv _) = is_lval lv
End
           


Definition get_lval_of_ret_arith_list_def:
  get_lval_of_ret_arith_list ret_arith_guards =
  let filtered = FILTER (λx. arth_indic_in_lval x) ret_arith_guards in
    (case nub filtered of
    | [is_lval lv] => SOME (is_lval lv)
    | _ => NONE)                           (* if no lval at all after filtering,
                                              or more than one, then NONE*)
End
           

(* this should be for the whole table*)        
Definition get_lval_of_arith_list_def:
  get_lval_of_arith_list arith_guards =
  let lvals = MAP (λarith_g. get_lval_from_arith arith_g) arith_guards in
        ( case EVERY (λx. ¬ arth_indic_in_lval x) lvals of                (* case all True *)
          | T => SOME isTrue
          | F =>
              ( case get_lval_of_ret_arith_list lvals of     
                | SOME lv => SOME lv                           (* case blend, return single lval*)
                | NONE => NONE                                 (* faluty case, shouldn't be reached*)
              )
        )
        
End
           





(* checks if arithmetic table is convertable to interval table,
 we do not need to do this as a first step for vars anymore *) 
Definition analyze_arith_table_type_def:
  analyze_arith_table_type pd_type arith_table =
  if valid_table arith_table then
    let all_guards = FLAT (MAP FST arith_table) in
      (case get_lval_of_arith_list all_guards of
       | SOME isFalse => NONE
       | SOME isTrue => SOME (key_const (n2v 1, 1), 1)
       | SOME (is_lval lval) =>
           (case resolve_lval_type pd_type lval of
            | SOME (type_length n) => SOME (key_val lval, n)
            | _ => NONE
           )
       | NONE => NONE
      )
  else
    NONE
End

        
        
Definition convert_arith_to_interval_table_def:
  convert_arith_to_interval_table arith_table pd_type =
  case analyze_arith_table_type pd_type arith_table of
  | NONE => NONE 
  | SOME (key, bit_len) =>    
    (let converted = convert_arith_rows_to_arith arith_table bit_len in
    if every_is_some_in_l converted ∧ arith_table ≠ [] then
      SOME ((key, rm_optl converted): 'a intvl_table)
    else
      NONE
    )
End



(*
still incorrect cause this table blends ttl and src


val test_pd_type = ``[("h" , type_record [("ttl", type_length 8);
                                          ("src", type_length 8)])]``;
                               

                                  
EVAL “convert_arith_to_interval_table
      [([   a_True;
         arithm_ge (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 1),8);
         arithm_le (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 3),8)],1, action "fwd1");
        
       ([arithm_ge (lv_acc (lv_x "h") "ttl") (fixwidth 8 (n2v 4),8)],1,action "fwd2");

       ([a_False],1,action "drop");

        ([a_True],1,action "drop")]

       ^test_pd_type”



      
EVAL “convert_arith_to_interval_table
      [([a_False],1, action "fwd1");
        
       ([a_True],1,action "fwd2");

       ([a_False],1,action "drop");

        ([a_False],1,action "drop")]

       ^test_pd_type”

       

        
*)



        


(*===============================================*)
(*       sem arith_table = sem interval_table    *)
(*===============================================*)

(*
Definition eval_interval_atom_def:
  (eval_interval_atom arith_lv pd Empty = SOME F) ∧
  (eval_interval_atom arith_lv pd (Single a b) =
   (case resolve_lval pd arith_lv of
    | SOME (val_bs bv) => (
      case (bv_ge_than bv a, bv_le_than bv b) of
      | (SOME T, SOME T) => SOME T
      | (SOME F, SOME _) => SOME F
      | (SOME _, SOME F) => SOME F
      | (_,_) => NONE
      )
    | _ => NONE
   )
  ) 
End
*)



(* bv here could be from the lval in pd or from const*)
Definition eval_interval_atom_def:
  (eval_interval_atom bv pd Empty = SOME F) ∧
  (eval_interval_atom bv pd (Single a b) =
   case (bv_ge_than bv a, bv_le_than bv b) of
   | (SOME T, SOME T) => SOME T
   | (SOME F, SOME _) => SOME F
   | (SOME _, SOME F) => SOME F
   | (_,_) => NONE
  )
End        

   
Definition is_interval_guards_true_def:
  is_interval_guards_true interval_guards bv pd =
  EVERY (λ interval_atom. eval_interval_atom bv pd interval_atom = SOME T ) interval_guards
End      

         
Definition extract_bv_from_key_def:
  (extract_bv_from_key (key_val lval) pd =
   case resolve_lval pd lval of
   | SOME (val_bs bv) => SOME bv
   | _ => NONE
  )∧
  (extract_bv_from_key (key_const bv) pd = SOME bv)
End
         
         
Definition is_interval_match_row_def:
  is_interval_match_row st_in st_num artih_atoml bv pd = 
   ((st_in = st_num) ∧ is_interval_guards_true artih_atoml bv pd ∧ artih_atoml ≠ [])
End

        
Definition check_interval_table_sem_def:
  check_interval_table_sem st_in (interval_table: 'a intvl_table) pd =
  (let (key, intvl_lines) = interval_table in
     case (extract_bv_from_key key pd) of
     | SOME bv =>
       SOME (MAP (\(interval_guards, st, res).
         (is_interval_match_row st_in st interval_guards bv pd, res))  intvl_lines)
     | NONE => NONE
  )
End



Definition match_interval_table_def:
  match_interval_table st_in (interval_table:'a intvl_table) pd =
  case check_interval_table_sem st_in interval_table pd of
    | SOME res =>
      (case min_idx_till res T of
        SOME (idx, line) => SOME (SND line)
       | NONE => NONE
      )
    | NONE => NONE
End


(*



val example_pd =  
 “([ ("h", val_record [
            ("ttl", val_bs (fixwidth 8 (n2v 1), (8:num)))
     ])]): pd”;


val example_interval_table=
 “(key_val (lv_acc (lv_x "h") "ttl"),
        [([Single ([F; F; F; F; F; F; F; F],8) ([T; T; T; T; T; T; T; T],8);
           Single ([F; F; F; F; F; F; F; T],8) ([T; T; T; T; T; T; T; T],8);
           Single ([F; F; F; F; F; F; F; F],8) ([F; F; F; F; F; F; T; T],8)],
          1,action "fwd1");
         ([Single ([F; F; F; F; F; T; F; F],8) ([T; T; T; T; T; T; T; T],8)],
          1,action "fwd2"); ([Empty],1,action "drop");
         ([Single ([F; F; F; F; F; F; F; F],8) ([T; T; T; T; T; T; T; T],8)],
          1,action "drop")]): string intvl_table”;
        
EVAL “match_interval_table (1:num)
      ^example_interval_table
      ^example_pd ”;

*)






        
(* questions:
   1. is this correct or is it way too strong∃
   2. should it be = instead of implication
   3. should this to be for all fields of packet or the fields that appear in the policy only?
 *)

Definition wf_packet_def:
  wf_packet packet_type packet_input =
  ∀ lval n.  resolve_lval_type packet_type lval = SOME (type_length n) ⇒
             ∃ bs. (resolve_lval packet_input lval = SOME (val_bs bs) ∧
                    wf_bit bs ∧ SND bs = n)
End




Theorem extract_bv_from_key_not_none:
  ∀ arith_table packet_type packet_input key rows.        
    wf_packet packet_type packet_input ∧
    convert_arith_to_interval_table arith_table packet_type = SOME (key,rows) ⇒
    extract_bv_from_key key packet_input ≠ NONE
Proof
  rw[convert_arith_to_interval_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[analyze_arith_table_type_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[extract_bv_from_key_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  
  gvs[wf_packet_def] >>
  res_tac >> fs[] >>
  Cases_on ‘resolve_lval packet_input a’ >> gvs[]
QED



(*)




        

∀ arith_table interval_table packet_type st_in packet_input.
wf_packet packet_type packet_input ∧
convert_arith_to_interval_table arith_table packet_type =
        SOME interval_table ⇒
check_interval_table_sem st_in interval_table packet_input = 
        SOME (check_arith_table_sem st_in arith_table packet_input)

                                    
rw[check_interval_table_sem_def, check_arith_table_sem_def] >>

Cases_on ‘interval_table’ >> 
gvs[] >>

Cases_on ‘extract_bv_from_key q packet_input’ >> gvs[] >| [
    ‘extract_bv_from_key q packet_input ≠ NONE’ by metis_tac[extract_bv_from_key_not_none]
    ,
        
    simp[LIST_EQ_REWRITE] >>
    ‘LENGTH r = LENGTH arith_table’ by cheat >>
    gvs[] >>

    rpt strip_tac >>
    gvs[EL_MAP] >>

    Cases_on ‘EL x' r’ >> Cases_on ‘r'’ >>
    Cases_on ‘EL x' arith_table’ >> Cases_on ‘r'’ >>


    rename1 ‘EL x' r = (interval_guards,interval_st,interval_res)’ >>
    rename1 ‘EL x' arith_table = (arith_guards,arith_st,arith_res)’ >>
    gvs[] >>


        
    gvs[convert_arith_to_interval_table_def] >>
    Cases_on ‘analyze_arith_table_type packet_type arith_table’ >> gvs[] >>
    Cases_on ‘x''’ >> gvs[] >>

    rename1 ‘i < LENGTH arith_table’ >>
    rename1 ‘extract_bv_from_key key packet_input = SOME k_val’ >>

    
            

    
             



                                             
  gvs[every_is_some_in_l_def] >>



        


  ]


*)
                                                        

      



                                    


Theorem table_arith_interval_correct:
  ∀ arith_table interval_table packet_input packet_type st_in.
    wf_packet packet_type packet_input ∧
    (convert_arith_to_interval_table arith_table packet_type = SOME interval_table) ⇒
    (match_interval_table st_in interval_table packet_input =
    match_arith_table st_in arith_table packet_input)
Proof
  rw[match_interval_table_def, match_arith_table_def] >>

  ‘check_interval_table_sem st_in interval_table packet_input  =
   SOME (check_arith_table_sem st_in arith_table packet_input) ’ by cheat >>
  gvs[] 
QED

        



(*


pd = ["ttl", ([T;T;T], 3)]

ttl >= ([T;F;F;F], 4)

ttl >= ([T;F;F;F], 3)
   


        

        
OLD STUFF 


   


        
Definition intersect_single_def:
  (intersect_single (SOME (Single bv1 bv2)) (SOME (Single bv3 bv4)) =
   (if check_widths bv1 bv2 bv3 bv4 then
     (case (bv_gt_than bv1 bv3, bv_gt_than bv2 bv4) of
      | (SOME a1_gt_a2, SOME b1_gt_b2) =>
          (let lower = if a1_gt_a2 then bv1 else bv3 in
            let upper = if b1_gt_b2 then bv4 else bv2 in
              (case bv_gt_than lower upper of
               | SOME F => SOME (Single lower upper)
               | _ => NONE                (* Shouldn't happen per bv_gt_than spec *)
              ))
      | _ => NONE)                        (* Invalid comparison *)
   else NONE)) ∧                         (* Width/length mismatch *)

        
  (intersect_single NONE _ = NONE) ∧
  (intersect_single _ NONE = NONE) ∧
  (intersect_single (SOME Empty) _ = NONE) ∧
  (intersect_single _ (SOME Empty) = NONE)
End

  
Definition is_True_or_False_def:
  is_True_or_False g =
  ((g = True) ∨ (g = False))
End

     
Definition process_var_to_arith_def:
  process_var_to_arith me min max g (SOME curr_int) =
   case var_atom_to_arith me g of
   | NONE => NONE                            (* Invalid guard becomes NONE *)
   | SOME a_True => SOME curr_int            (* True uses full range of the input *)
   | SOME a_False => NONE                    (* False becomes NONE *)
   | SOME a => intersect_single (SOME curr_int) (arith_to_interval a min max)
End


(*==================================*)
(*     line coversion definitions   *)
(*==================================*)


        
Definition process_guards_rec_def:
  (process_guards_rec me min max [] init_int = init_int) ∧
  (process_guards_rec me min max (g::gs) init_int =
    case init_int of
    | NONE => NONE
    | SOME intvl =>
        case process_var_to_arith me min max g (SOME intvl) of
        | NONE => NONE
        | SOME new_intvl => process_guards_rec me min max gs (SOME new_intvl))
End

        
Definition convert_line_with_key_def:
  (convert_line_with_key me min max ([], s, res) = NONE) ∧
  (convert_line_with_key me min max (var_guards, s, res) =
    case process_guards_rec me min max var_guards (SOME (Single min max)) of
    | NONE => SOME (NONE, s, res)  
    | SOME interval => SOME (SOME interval, s, res))
End

        
Definition convert_lines_map_with_key_def:
  convert_lines_map_with_key me min max lines =
   MAP (\line.case convert_line_with_key me min max line of
     | NONE => NONE  (* This is for completely invalid lines *)
     | SOME x => SOME x   (* Preserve the (interval option, state, action) structure *)) lines
End





(*==================================*)
(*  WFness conditions for var tbl   *)
(*==================================*)




Definition all_vars_defined_abstract_def:
  (all_vars_defined_abstract me [] = T) ∧
  (all_vars_defined_abstract me (True::rest) = all_vars_defined_abstract me rest) ∧
  (all_vars_defined_abstract me (False::rest) = all_vars_defined_abstract me rest) ∧
  (all_vars_defined_abstract me ((Var x)::rest) = 
   (case ALOOKUP me x of
     | SOME _ => all_vars_defined_abstract me rest
     | NONE => F)) ∧
  (all_vars_defined_abstract me ((Not g)::rest) = 
   (all_vars_defined_abstract me [g] ∧ all_vars_defined_abstract me rest))
End






Definition get_lval_of_guard_in_me_def:
  get_lval_of_guard_in_me me var_g = 
    case var_g of
      | Var x => (case ALOOKUP me x of
                  | SOME a => get_lval a
                  | NONE => NONE)
      | Not (Var x) => (case ALOOKUP me x of
                        | SOME a => get_lval a
                        | NONE => NONE)
      | _ => NONE
End


Definition get_guard_lvals_def:
  get_guard_lvals me guards = 
    FILTER (λ x . IS_SOME x ) (MAP (get_lval_of_guard_in_me me) guards)
End


Definition ALL_SAME_def:
  (ALL_SAME [] = T) ∧
  (ALL_SAME [x] = T) ∧
  (ALL_SAME (x::y::rest) = ((x = y) ∧ ALL_SAME (y::rest)))
End


Definition one_unique_lval_in_guards_def:
  one_unique_lval_in_guards me all_guards =
    let lvals = get_guard_lvals me all_guards in
    case lvals of
      | [] => NONE   (* No lvals found *)
      | h::t => if ALL_SAME (h::t) 
                then h  (* Returns SOME lv if all same *)
                else NONE
End      

       
Definition valid_line_def:
  valid_line (guards, s, res) = (guards ≠ [])
End


Definition valid_table_def:
  valid_table table = 
    ((table ≠ []) ∧ EVERY valid_line table)
End


Definition valid_tables_def:
  valid_tables tables = EVERY valid_table tables
End

  

(* Add this new function to analyze the entire table first *)
Definition analyze_table_type_def:
  analyze_table_type me pd_type table =
   if table = [] then NONE else 
     let all_guards = FLAT (MAP FST table) in
       case all_vars_defined_abstract me all_guards  of
       | T => ( case EVERY (λx. x = (False:atom_var)) all_guards of
                | T => NONE
                | F =>  (case EVERY (λx. x = True) all_guards of
                         | T => SOME (T, key_const (n2v 1, 1), (n2v 0,1), (n2v 1,1))
                         | F => ( case one_unique_lval_in_guards me all_guards of
                                  (* All non-boolean guards use same lval *)
                                  | SOME lv => (
                                    case resolve_pd_min_max pd_type lv of
                                    | SOME (min,max) => SOME (T, key_val lv, min, max)
                                    | NONE => NONE
                                    )
                                  | NONE => NONE
                                )
                        )
              )
       | F => NONE 
End


(*==================================*)
(*         Tables conversion        *)
(*==================================*)

Definition convert_single_table_def: 
  (convert_single_table [] me pd_type = NONE) ∧
  (convert_single_table lines me pd_type =                
   case analyze_table_type me pd_type lines of
   | SOME (T, key_type, min, max) =>       
       let converted_lines = convert_lines_map_with_key me min max lines in
         if EVERY IS_SOME converted_lines then
           SOME (key_type, MAP THE converted_lines)  (* All lines valid *)
         else
           NONE  (* At least one line was completely invalid (NONE) *)
   | _ => NONE  (* Inconsistent table *)
  )
End

        
Definition convert_tables_def:
  (convert_tables [] _ _ = SOME []) ∧
  (convert_tables (tbl::tbls) me pd_type =
    if ¬(valid_tables (tbl::tbls)) then NONE
      else
        (case convert_single_table tbl me pd_type of
        | NONE => NONE  (* Fail immediately if any table fails *)
        | SOME converted_tbl =>
            (case convert_tables tbls me pd_type of
            | NONE => NONE
            | SOME converted_tbls => SOME (converted_tbl :: converted_tbls))
        )
      )
End



(*
val policy1_var = “[[([(Var "x" :atom_var); (Var "y" :atom_var)],(0 :num), (state (3 :num) :(string # num list) action_expr));
       ([(Var "x" :atom_var); Not (Var "y" :atom_var)],(0 :num), (state (4 :num) :(string # num list) action_expr));
       ([Not (Var "x" :atom_var)],(0 :num),                      (state (4 :num) :(string # num list) action_expr))];
       
      [([(Var "z" :atom_var)],(4 :num),                          (state (7 :num) :(string # num list) action_expr));
       ([Not (Var "z" :atom_var)],(4 :num),                      (state (8 :num) :(string # num list) action_expr));
       ([True],(3 :num),                                         (state (3 :num) :(string # num list) action_expr))];
       
      [([True],(3 :num),action ("fwd",[(1 :num)]));
       ([True],(7 :num),action ("fwd",[(2 :num)]));
       ([True],(8 :num),action ("drop",([] :num list)))]]”;


val test_pd_nested = ``[
  ("h", type_record [
    ("len", type_length 5); 
    ("flags", type_length 5); 
    ("ttl", type_length 5)
  ])
]``;


val test_lval1 = ``lv_acc (lv_x "h") "ttl"``;
val test_lval2 = ``lv_acc (lv_x "h") "flags"``;
val test_lval3 = ``lv_x "z"``;


val test_atom1 = ``arithm_gt ^test_lval1 (n2v 0,5)``;  (* h.ttl > 0 *)
val test_atom2 = ``arithm_lt ^test_lval1 (n2v 10,5)``; (* h.ttl < 10 *)
val test_atom3 = ``arithm_lt ^test_lval2 (n2v 3,5)``;  (* h.flags < 3 *)

    
val test_me = ``[
  ("x", ^test_atom1); 
  ("y", ^test_atom2); 
  ("z", ^test_atom3)
]``;

EVAL ``convert_tables (^policy1_var) ^test_me ^test_pd_nested``;
        
*)



                  

(*==================================*)
(*    interval table semantics      *)
(*==================================*)




Definition is_intvl_match_row_def:
  is_intvl_match_row key (s_in:num) (packet_input:pd) (row:('a intvl_row)) =
  case (key, row) of
  | (key_val lval, (SOME (Single a b), s, res)) =>
      (let (a_v,a_w) = a in
        let (b_v,b_w) = b in
          (case resolve_lval packet_input lval of
           | SOME (val_bs (v,v_w)) => 
               (if (a_w = b_w) ∧ (b_w = v_w) then
                  (case (bv_lt_than (v,v_w) (a_v,a_w), bv_lt_than (b_v,b_w) (v,v_w)) of
                   | (SOME F, SOME F) => (s_in = s)  (* a ≤ v ≤ b *)
                   | _ => F)
                else F
               )
           | SOME _ => F  (* non-numeric value *)
           | NONE => F))   (* lval not found *)
  | (key_val lval, (NONE, s, res)) => F  (* Empty interval never matches *)             
  | (key_const (c,c_w), (_, s, _)) => (s_in = s)  (* Constant key matches state only *)
End

      
        

(* Process all rows in an interval table *)
Definition check_all_intvl_rows_match_def:
  check_all_intvl_rows_match key st_in rows packet_input =
  MAP (λ(interval,s,res). is_intvl_match_row key (st_in:num) (packet_input:pd) (interval,s,res), res) rows
End



(* Find first matching line in a converted table *)
Definition match_intvl_tbl_def:
  match_intvl_tbl (intvl_tbl: 'a intvl_table) packet_input st_in =
  let (key, rows) = intvl_tbl in
    let lines_res = check_all_intvl_rows_match key st_in rows packet_input in
      case min_idx_till lines_res T of
      | SOME (idx, line) => SOME (SND line)
      | NONE => NONE
End


(* Process list of interval tables with state propagation *)
Definition match_intvl_tbll_def:
  (match_intvl_tbll ([]: 'a intvl_table_list) packet_input st_in = NONE) ∧
  (match_intvl_tbll [intvl_tbl] packet_input st_in =
    case match_intvl_tbl intvl_tbl packet_input st_in of
      | SOME (action a) => SOME (action a)
      | _ => NONE) ∧
  (match_intvl_tbll (intvl_tbl::intvl_tbls) packet_input st_in =
    case match_intvl_tbl intvl_tbl packet_input st_in of
      | SOME (state n) => match_intvl_tbll intvl_tbls packet_input n
      | _ => NONE)
End



(* Top-level interval table semantics *)
Definition sem_intvl_tables_def:
  sem_intvl_tables ((intvl_tbll: (('a intvl_table ) list)), st_in) (packet_input:pd) =
  match_intvl_tbll intvl_tbll packet_input st_in
End

(* IMPORTANT well formdness every var in me is indeed defined in pd*)




        

(*==================================*)
(*            P R O O F             *)
(*==================================*)





Theorem convert_tables_never_empty:
  ∀ h' t me packet_type.
    convert_tables (h'::t) me packet_type ≠ SOME []
Proof
  rw[convert_tables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) 
QED
   

Theorem append_defined_implies_first_defined:
  ∀me l l'. all_vars_defined_abstract me (l ++ l') ⇒
              (all_vars_defined_abstract me l' ∧  all_vars_defined_abstract me l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
  res_tac
QED



Theorem check_all_rows_match_length:
  ∀ tbl mv st_in.
    LENGTH (check_all_rows_match st_in tbl mv) = LENGTH (tbl)
Proof
  Induct >>
  gvs[check_all_rows_match_def]
QED


Theorem convert_lines_map_with_key_length:
  ∀ tbl me min max.
    LENGTH (convert_lines_map_with_key me min max tbl) = LENGTH tbl
Proof
  Induct >>
  gvs[convert_lines_map_with_key_def]
QED


Theorem check_all_intvl_rows_match_comb_length:
  ∀ tbl me min max key st_in packet_input.
    LENGTH (check_all_intvl_rows_match key st_in (MAP THE (convert_lines_map_with_key me min max tbl)) packet_input) =
    LENGTH tbl
Proof
  Induct >>
  gvs[check_all_intvl_rows_match_def, convert_lines_map_with_key_def]
QED




Theorem guards_in_tbl_not_empty:
  ∀ tbl x guards st_row res_row.
  valid_table tbl ∧
  x < LENGTH tbl ∧
  EL x tbl = (guards,st_row,res_row) ⇒
  guards ≠ []      
Proof
  rw[valid_table_def, EVERY_EL, valid_line_def] >>
  res_tac >>
  metis_tac[valid_line_def]           
QED
        



Theorem all_rows_true_then_lval_none_thm:
  ∀ rows snlist me.
    EVERY (λx. x = True) rows ∧
    FILTER (λx. IS_SOME x) (MAP (get_lval_of_guard_in_me me) rows) = snlist ⇒
    EVERY IS_NONE  snlist
Proof
  Induct >>
  rpt strip_tac >>
  gvs[] >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  gvs[get_lval_of_guard_in_me_def]
QED
    
        
        
Theorem every_true_then_in_mv_true_l_thm:
  ∀ row st res mv x tbl.
    x < LENGTH tbl ∧
    EL x tbl = (row,st,res) ∧
    EVERY (λx. x = True) (FLAT (MAP FST tbl)) ⇒
    is_atoml_true row mv
Proof
  rw[is_atoml_true_def] >>
  imp_res_tac EL_MEM >>           
  gvs[EVERY_MEM] >>
  rpt strip_tac >>
  imp_res_tac mem_fst_snd >>
  gvs[MEM_FLAT] >>
  res_tac >>
  gvs[sem_var_atom_def]
QED

        
Theorem all_rows_true_then_no_unique:
  ∀ rows me.
    EVERY (λx. x = True) rows ⇒             
    one_unique_lval_in_guards me rows = NONE
Proof
  
  gvs[one_unique_lval_in_guards_def] >>                            
  gvs[get_guard_lvals_def, get_lval_of_guard_in_me_def] >>
  rpt strip_tac >>
  rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
  imp_res_tac all_rows_true_then_lval_none_thm >>
  gvs[]
QED
  


        
        
Theorem  all_vars_defined_abstract_on_individual:       
  ∀ me  l.    
    (all_vars_defined_abstract me) (FLAT l) ⇒
    (EVERY (\x. all_vars_defined_abstract me x) l)
Proof
  Induct_on `l` >> simp[all_vars_defined_abstract_def] >>
  Cases >> simp[all_vars_defined_abstract_def] >>
  rpt strip_tac >> res_tac >>
  `h'::(t ++ FLAT l) = [h'] ++ t ++ FLAT l` by simp[] >> 
  `(h':: t) = [h'] ++ t ` by simp[] >> 
  metis_tac[append_defined_implies_first_defined]
QED






        
Definition norm_match_tbl_def:
  (norm_match_tbl [] mv st_in = NONE) ∧
  (norm_match_tbl (h::t) mv st_in =
   let (guards,st,res) = h in
    if is_match_row st_in st guards mv then
      SOME res
    else
      norm_match_tbl t mv st_in)
End


Theorem norm_match_tbl_equiv:
  ∀tbl mv st_in.
    norm_match_tbl tbl mv st_in = match_tbl tbl mv st_in
Proof
  Induct >> rw[] >-
  (
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def, min_idx_till_def, INDEX_FIND_def]
  ) >>
  PairCases_on ‘h’ >>
  fs[norm_match_tbl_def, match_tbl_def, check_all_rows_match_def] >>
  Cases_on `is_match_row st_in h1 h0 mv` >> fs[] >>
  gvs[min_idx_till_def, INDEX_FIND_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  

  imp_res_tac INDEX_FIND_NONE_EXISTS >>
  imp_res_tac exists_index_some >>
  gvs[EXISTS_MAP] >>
  gvs[MAP_MAP_o] >>          
  imp_res_tac P_implies_next >>
  gvs[]     
QED





Theorem all_vars_defined_abstract_normalize:
  ∀ h guards me.
    all_vars_defined_abstract me (h::guards) ⇒
    all_vars_defined_abstract me [h] ∧
    all_vars_defined_abstract me guards
Proof
  Cases_on ‘h’ >>                          
  rw[all_vars_defined_abstract_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
QED

Theorem check_intvl_rows_elementwise_correct:
  ∀l key st_in packet_input x x'.
    x < LENGTH l ∧
    EL x l = SOME x' ⇒
    (EL x (check_all_intvl_rows_match key st_in (MAP THE l) packet_input) =
     HD (check_all_intvl_rows_match key st_in [x'] packet_input))
Proof
  rpt gen_tac >> strip_tac >>
  (* Expand both sides *)
  simp[check_all_intvl_rows_match_def] >>
  gvs[EL_MAP]                              
QED


Triviality unique_lval_gt_same_triv1:
  ∀ var guards lval lval' me p.
    one_unique_lval_in_guards me (Var var::guards) = SOME lval ∧
    ALOOKUP me var = SOME (arithm_gt lval' p) ⇒
    lval = lval'
Proof
  rw[one_unique_lval_in_guards_def] >>
  gvs[get_guard_lvals_def] >>
  gvs[get_lval_of_guard_in_me_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[get_lval_def]
QED




Triviality unique_lval_lt_same_triv1:
  ∀ var guards lval lval' me p.
    one_unique_lval_in_guards me (Var var::guards) = SOME lval ∧
    ALOOKUP me var = SOME (arithm_lt lval' p) ⇒
    lval = lval'
Proof
  rw[one_unique_lval_in_guards_def] >>
  gvs[get_guard_lvals_def] >>
  gvs[get_lval_of_guard_in_me_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  gvs[get_lval_def]
QED








        



  
        
        
(*******************************************************)












        

        
Theorem el_rows_match_check_thm:
  ∀me mv packet_input packet_type  st_in tbl x interval st res key min max.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table tbl ∧
    (∀var atom.
       ALOOKUP me var = SOME atom ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    analyze_table_type me packet_type tbl = SOME (T,key,min,max) ∧ 
    LENGTH (convert_lines_map_with_key me min max tbl) =
    LENGTH (check_all_rows_match st_in tbl mv) ∧
    EL x (convert_lines_map_with_key me min max tbl) =
    SOME (interval,st,res) ∧
    x < LENGTH (check_all_rows_match st_in tbl mv)
    ⇒
    EL x (check_all_rows_match st_in tbl mv) =
    (is_intvl_match_row key st_in packet_input (interval,st,res),res)
Proof

  rpt gen_tac >> strip_tac >>
  fs[convert_lines_map_with_key_def, check_all_rows_match_def] >>
  gvs[] >>
  
  Cases_on ‘EL x tbl’ >>   Cases_on ‘r’ >>
  rename1 ‘EL x tbl = (guards, st_row, res_row)’ >>
  
  gvs[EL_MAP] >>
  
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

  ‘guards ≠ []’ by metis_tac[guards_in_tbl_not_empty] >>

  Cases_on ‘key’ >|[
    (* Case 1: key_val *)
    rgs[analyze_table_type_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>  
    gvs[] >>
    
    (* we check if the row contains at least one lval or not *)
    Cases_on ‘one_unique_lval_in_guards me guards’ >> gvs[] >|[
      (* if not, trivial,  all values are true and false or not defined (by contrdiction)*)
      cheat
      ,
      
      (* else this lval will be the same for the whole table *)
      ‘a=x'’ by cheat >>
      Cases_on ‘guards’ >> gvs[] >>
      
      gvs[convert_line_with_key_def] >>
      Cases_on ‘process_guards_rec me min max (h::t) (SOME (Single min max))’ >> gvs[] >|[
          
          simp[is_match_row_def, is_intvl_match_row_def] >>
          strip_tac >>
          ‘all_vars_defined_abstract me (h::t)’ by cheat >>  (* trivial from condition *)
          irule none_interval_implies_false_guard >>
          qexistsl_tac [‘a’, ‘max’, ‘me’, ‘min’, ‘packet_input’, ‘packet_type’] >>
          gvs[]
          ,
          (*process retunrs some*)
          
          
        ]
    ,
    (* Case 2: key_const *)
    rgs[analyze_table_type_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> rgs[]) >>
    imp_res_tac all_rows_true_then_no_unique >>
    gvs[] >>
    
    Cases_on ‘guards’ >> gvs[convert_line_with_key_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  
    
    gvs[is_match_row_def, is_intvl_match_row_def] >>
    ‘is_atoml_true (h::t) mv’ by metis_tac[every_true_then_in_mv_true_l_thm] >> gvs[]
                                                                                   
  ]

QED




Theorem interval_all_rows_converstion_correctness:
  ∀ tbl me packet_input mv packet_type st_in key min max.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table tbl ∧
    (∀var atom.
       ALOOKUP me var = SOME atom ⇒
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    EVERY IS_SOME (convert_lines_map_with_key me min max (tbl)) ∧
    analyze_table_type me packet_type tbl = SOME (T,key,min,max) ⇒
    ((check_all_rows_match st_in tbl mv) =
     (check_all_intvl_rows_match key st_in (MAP THE (convert_lines_map_with_key me min max tbl)) packet_input))
Proof
  rw[LIST_EQ_REWRITE] >|[
    
    ‘LENGTH (check_all_rows_match st_in tbl mv) = LENGTH (tbl)’ by gvs[check_all_rows_match_length] >>
    ‘LENGTH (convert_lines_map_with_key me min max tbl) = LENGTH tbl’ by gvs[convert_lines_map_with_key_length] >>
    gvs[check_all_intvl_rows_match_comb_length]
    ,


    ‘LENGTH (convert_lines_map_with_key me min max tbl) =
     LENGTH (check_all_rows_match st_in tbl mv)’ by gvs[check_all_rows_match_length, convert_lines_map_with_key_length] >>
    gvs[EVERY_EL] >>
    
    first_x_assum (strip_assume_tac o (Q.SPECL [‘x’])) >>
    res_tac >>

    Cases_on ‘EL x (convert_lines_map_with_key me min max tbl)’ >> rw[IS_SOME_DEF] >> gvs[] >>

    imp_res_tac check_intvl_rows_elementwise_correct >>
    ‘x < LENGTH (convert_lines_map_with_key me min max tbl)’ by gvs[] >>
    res_tac >>
                                                                                          
    first_x_assum (strip_assume_tac o (Q.SPECL [‘st_in’, ‘packet_input’, ‘key’])) >>
    res_tac >>
                                        
    gvs[] >>

    gvs[check_all_intvl_rows_match_def] >>
    PairCases_on ‘x'’ >>
    gvs[] >>

    rename1 ‘EL x (convert_lines_map_with_key me min max tbl) = SOME (interval,st,res)’ >>
    imp_res_tac  el_rows_match_check_thm (* theorem here*)
  ]
QED


      
Theorem interval_single_table_converstion_correctness:
  ∀var_table me packet_input mv interval_table packet_type st_in.
    ALL_DISTINCT (MAP FST me) ∧
    valid_table var_table  ∧
    (∀var atom.  ALOOKUP me var = SOME atom ⇒
                 ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    convert_single_table var_table me packet_type = SOME interval_table ⇒
    match_tbl var_table mv st_in = match_intvl_tbl interval_table packet_input st_in
Proof
  
  Cases_on ‘var_table’ >>
  rpt strip_tac >-
   gvs[valid_table_def] >>
  
  gvs[convert_single_table_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>  
  
  rename1 ‘analyze_table_type me packet_type (row::tbl) = SOME (T,key,min,max)’ >>
  gvs[match_tbl_def, match_intvl_tbl_def] >>
  
  ‘(check_all_rows_match st_in (row::tbl) mv) = (check_all_intvl_rows_match key st_in
               (MAP THE (convert_lines_map_with_key me min max (row::tbl)))
               packet_input)’ by metis_tac[interval_all_rows_converstion_correctness] >>    (* thm here *)
  
  gvs[]
QED

        

        
Theorem interval_tables_conversion_correctness:
  ∀var_tables me packet_input mv interval_tables packet_type st_in.
    ALL_DISTINCT (MAP FST me) ∧
    (∀var atom. 
       ALOOKUP me var = SOME atom ⇒ 
       ALOOKUP mv var = eval_arithm_atom packet_input atom) ∧
    (convert_tables var_tables me packet_type = SOME interval_tables) ⇒
    sem_tables (var_tables, st_in) mv = 
    sem_intvl_tables (interval_tables, st_in) packet_input
Proof
  Induct >> rpt strip_tac >-
   
   (fs[convert_tables_def, sem_tables_def, sem_intvl_tables_def] >>
    gvs[sem_tables_def, match_tbll_def, sem_intvl_tables_def, match_intvl_tbll_def]) >> 
  
  fs[convert_tables_def] >>     
  Cases_on ‘convert_single_table h me packet_type’ >> fs[] >>
  Cases_on ‘convert_tables var_tables me packet_type’ >> fs[] >>
  
  last_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >>
  

  ‘valid_table h’ by gvs[valid_tables_def] >>
        
  subgoal ‘match_tbl h mv st_in = match_intvl_tbl x packet_input st_in’ >-
   ( metis_tac[interval_single_table_converstion_correctness] ) >>                 (*thm here*)
  
  simp[sem_tables_def, sem_intvl_tables_def] >>
  
  Cases_on ‘var_tables’ >>
  Cases_on ‘x'’ >>
  gvs[] >|[
    (* both are last tables*)
    fs[match_tbll_def, match_intvl_tbll_def] 
    ,
    fs[convert_tables_def]
    ,
    gvs[convert_tables_never_empty]
    ,
    fs[match_tbll_def, match_intvl_tbll_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    fs[sem_tables_def, sem_intvl_tables_def] 
  ]   
QED








*)
        
   


                                                                

val _ = export_theory ();







