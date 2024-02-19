open HolKernel boolLib liteLib simpLib Parse bossLib;

val _ = new_theory "p4_tc";

open arithmeticTheory stringTheory containerTheory pred_setTheory
     listTheory finite_mapTheory;

open p4Lib;
open blastLib bitstringLib;
open p4Theory;
open p4_auxTheory;
open p4_deterTheory;
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
open sumTheory;
open optionTheory;



(*

TODO:
1. extend the type system to include 128 bit
2. remove the basic definition because it is not really executable outside, make it total def 
3. refactor the proofs
*)


val vt_size_def = Define `
 (vt_size (v,t,b) = v_size v)
`;

Theorem v1_size_mem:
 !x_v x_v_l. MEM x_v x_v_l ==> v_size (SND x_v) < v1_size x_v_l
Proof
 REPEAT STRIP_TAC >>
 Cases_on ‘x_v’ >>
 fs [listTheory.MEM_SPLIT, v1_size_append, v_size_def]
QED

Theorem vxl_size_mem:
 !xvl v. MEM v (MAP (λ(x,v). v) xvl) ==> v_size v < v1_size xvl
Proof
Induct >> gvs[] >> REPEAT STRIP_TAC >-
(PairCases_on ‘h’  >>  fs [v_size_def]) >>
RES_TAC >> fs [v_size_def] 
QED
     
        

Theorem vt_size_mem:
 !e l. MEM e l ==> e_size e < e3_size l
Proof
 REPEAT STRIP_TAC >>
 fs [listTheory.MEM_SPLIT, e3_size_append, e_size_def]
QED

Theorem xel_size_mem:
 !xel e. MEM e (MAP (λ(x,e). e) xel) ==> e_size e < e1_size xel + 1
Proof
Induct >> gvs[] >> REPEAT STRIP_TAC >-
(PairCases_on ‘h’  >>  fs [e_size_def]) >>
RES_TAC >> fs [e_size_def]
QED










        
                
Definition map_is_true_def:
 map_is_true l =
  ~ MEM F l                           
End




        

Theorem map_is_true_is_T:
∀l. map_is_true l = (∀ b. MEM b l ⇒ b = T  )
Proof
Induct >> gvs[map_is_true_def] >>
STRIP_TAC >>                
Cases_on ‘h’ >> gvs[] >>       
EQ_TAC >> REPEAT STRIP_TAC >>
METIS_TAC[]               
QED


        

Theorem map_is_true_imp_EL:
∀l. map_is_true l ⇒ ∀i. i < LENGTH l ⇒ EL i l
Proof
Induct >> gvs[map_is_true_def] >>
STRIP_TAC >>                
Induct >>        
gvs[map_is_true_def]
QED



Theorem EL_imp_map_is_true:
∀ l . (∀i. i < LENGTH l ⇒ EL i l) ⇒ map_is_true l
Proof
Induct >> gvs[map_is_true_def] >>
REPEAT STRIP_TAC >>
(
subgoal ‘(∀i. i < LENGTH l ⇒ EL i l)’ >- (
REPEAT STRIP_TAC >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘SUC i ’])) >> gvs[]
  )) >| [
Cases_on ‘h’ >> gvs[] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘0’])) >> gvs[]
,
RES_TAC
]          
QED


Theorem EL_map_true:
∀ l . map_is_true l ⇔ ∀ i .( i < LENGTH l ⇒ EL i l)
Proof
STRIP_TAC >>
EQ_TAC >> gvs[map_is_true_imp_EL, EL_imp_map_is_true]
QED

        

Theorem f_maps_mem:
  ∀ l . ~ MEM F l ⇒
        ∀ i . i < LENGTH l ⇒ EL i l = T
Proof
  Induct >> gvs[] >> STRIP_TAC >>
  Induct >> gvs[]
QED
               

Definition all_some_def:
 all_some l =
  ~ MEM NONE l                           
End

        
Definition rm_some_def:
 rm_some l =
  MAP (\x. THE x ) l                      
End

Definition rm_t_def:
 rm_t (t_tau tau ) = tau
End
              
Definition is_tau_def: 
 is_tau (t_tau (tau : tau) ) = T ∧
 is_tau _ = F
End

        
Theorem all_some_imp_EL:
∀l. all_some l ⇒ (∀i. i < LENGTH l ⇒ ∃x. EL i l = SOME x)
Proof
  Induct >> gvs[all_some_def] >> NTAC 2 STRIP_TAC >>
  Induct >> gvs[] >> Cases_on ‘h’ >> gvs[]
QED

                  

(*This is not a total function,
  Because headers and structs feilds are typed with a base type.
  is the type is a literal, then it returns NONE.
  We do not type the structs and headers with literals because it means that struct can have many possible types.
  NOTE: type of literal is basically checking that literal st is in any possible set that contains it
*)

val typeOf_v_def = TotalDefn.tDefine "typeOf_v" `
(typeOf_v (v_bool boolv) = SOME (t_tau tau_bool)) /\
(typeOf_v (v_bit (bl, n)) = SOME (t_tau (tau_bit n))) /\
(typeOf_v (v_bot) = SOME (t_tau tau_bot)) /\
(typeOf_v (v_str x) = SOME (t_string_names_a [x]) ) /\
(typeOf_v (v_ext_ref n) = SOME (t_tau tau_ext) ) /\

          (* add MAP ... from type system to here = xvl and so *)
(typeOf_v (v_struct xvl) =
 let vl = (MAP (\(x,v). v) xvl ) in
  let xl = (MAP (\(x,v). x) xvl) in
    let tl_some = (MAP (\(v). typeOf_v v ) vl ) in
       (case (all_some tl_some) of 
        | T =>      
            ( let tl = (MAP (\x. THE x ) tl_some) in
             (case (map_is_true (MAP (\t. is_tau t) tl)) of
               | T => let tl_t_removed = MAP (\t. rm_t t) tl in
                        let xvtl = (ZIP( xl, ZIP(vl , tl_t_removed ) ))  in
                      SOME (t_tau (tau_xtl struct_ty_struct ( MAP (\ (x,v,t). (x,t) ) xvtl)))
               | F => NONE
             ))
       | F => NONE
))  ∧

(typeOf_v (v_header boolv xvl) =
 let vl = (MAP (\(x,v). v) xvl ) in
  let xl = (MAP (\(x,v). x) xvl) in     
    let tl_some = (MAP (\(v). typeOf_v v ) vl ) in
       (case (all_some tl_some) of 
        | T =>      
            ( let tl = (MAP (\x. THE x ) tl_some) in
             (case (map_is_true (MAP (\t. is_tau t) tl)) of
               | T => let tl_t_removed = MAP (\t. rm_t t) tl in
                        let xvtl = (ZIP( xl, ZIP(vl , tl_t_removed ) ))  in
                      SOME (t_tau (tau_xtl struct_ty_header ( MAP (\ (x,v,t). (x,t) ) xvtl)))
               | F => NONE
             ))
       | F => NONE
))
`
(WF_REL_TAC `measure v_size` >>
 fs[v_size_def] >>
 REPEAT STRIP_TAC >>
 IMP_RES_TAC v1_size_mem >>
 IMP_RES_TAC vxl_size_mem >>
 gvs[]                                
);




        
(*
EVAL “ typeOf_v (v_struct [])   ”; 
EVAL “ typeOf_v (v_struct [(y,v_bool F);(x,v_bool F)])   ”;
EVAL “ typeOf_v (v_struct [(y,v_bool F);(x,v_str "x")])   ”; (*NONE*)
EVAL “ typeOf_v (v_struct [(y,v_bool F);(ip, v_struct [(y,v_bool F);(x,v_str "x")])])   ”; (*NONE*)
EVAL “ typeOf_v (v_header T [(y,v_bool F);(ip, v_struct [(y,v_bool F);(x,v_str "x")])])   ”; (*NONE*)
EVAL “ typeOf_v (v_header T [(y,v_bool F);(ip, v_struct [(y,v_bool F)])])   ”; (* some struct type*)

     
*)
        

Definition v_tc:
  (* value bool *)          
 ( ( v_tc (v_bool boolv) (t_tau tau)  F  ) =
 case (typeOf_v (v_bool boolv) ) of
 | SOME (t_tau t) => (t = tau)
 | SOME (t_string_names_a  t) => F                        
 | NONE => F               
) ∧


  (* value bitstring *)
( ( v_tc (v_bit bitv) (t_tau tau)  F  ) =
 case (typeOf_v (v_bit bitv )) of
 | SOME (t_tau t) => (t = tau)
 | SOME (t_string_names_a  t) => F                        
 | NONE => F               
 )∧      


  (* value bot *)
(( v_tc v_bot (t_tau tau)  F  ) =
 case (typeOf_v (v_bot )) of
 | SOME (t_tau t) => (t = tau)
 | SOME (t_string_names_a  t) => F                        
 | NONE => F  
) ∧


  (* value parser state name - I do not use the typeOf_v here because from there i get a singleton list
     and check MEM x [x] and here is can be any possible list
   *)
  (( v_tc (v_str x) (t_string_names_a  (x_list))  F  ) = MEM x x_list) ∧



  (* structs *)       
  ( ( v_tc (v_struct (xvl)) (t_tau tau)  F  ) =
    case (typeOf_v (v_struct (xvl))) of
    | SOME (t_tau t) => (t = tau)
    | SOME (t_string_names_a  t) => F                        
    | NONE => F
  ) ∧


  (* headers *)   
  ( ( v_tc (v_header b (xvl)) (t_tau tau)  F  ) =
    case (typeOf_v (v_header b (xvl))) of
    | SOME (t_tau t) =>
        ( case (typeOf_v (v_bool b)) of
         | SOME (t_tau t') => (t = tau ∧ t' = tau_bool)
         | SOME (t_string_names_a  t) => F                        
         | NONE => F  
        )
    | SOME (t_string_names_a  t) => F                        
    | NONE => F
  ) ∧


  (* ext_ref *) 
  ( ( v_tc (v_ext_ref i) (t_tau tau)  F  ) =
    case (typeOf_v (v_ext_ref i)) of
    | SOME (t_tau t) => (t = tau)
    | SOME (t_string_names_a  t) => F                        
    | NONE => F
  ) ∧  
    
  (* otherwise cases *)   
  (( v_tc (_) (_)  _  ) = F)
End

        
val v_tc = save_thm("v_tc", v_tc);
val v_tc_ind = tryfind (uncurry DB.fetch) [("scratch", "v_tc_ind"),
                                             ("p4_tc", "v_tc_ind")];
val _ = save_thm("v_tc_ind", v_tc_ind);



 (*       
EVAL “ (  v_tc (v_bool F) (t_tau tau_bool)  F  ) ”;
EVAL “ (  v_tc (v_bit ([T;F;F],3)) (t_tau (tau_bit  3 ))  F  ) ”;
EVAL “ (  v_tc v_bot (t_tau tau_bot)  F   ) ”;
EVAL “ (  v_tc (v_str "a") (t_string_names_a  (["a"]))  F  ) ”;
EVAL “ (  v_tc (v_struct []) (t_tau (tau_xtl struct_ty_struct []))  F  ) ”;
EVAL “ (  v_tc (v_struct [(x,v_bool F)]) (t_tau (tau_xtl struct_ty_struct [(x,tau_bool)]))  F  ) ”;
EVAL “ (  v_tc (v_struct [(x,v_bool F)]) (t_tau (tau_xtl struct_ty_struct [(x,tau_bot)]))  F  ) ”; (*false*)
EVAL “ (  v_tc (v_struct [(y,v_bool F);(x,v_bool F)]) (t_tau (tau_xtl struct_ty_struct [(x,tau_bot);(x,tau_bool)]))  F  ) ”;

*)







Theorem type_is_not_xl:        
∀ v tau.        
typeOf_v v = SOME (t_tau tau) ⇒
 ∀ xl . ( typeOf_v v ≠ SOME(t_string_names_a xl))            
Proof
Induct >> 
gvs[typeOf_v_def]
QED

         

Theorem all_some_normalize:
∀ a l .
all_some (a::l) ⇒
(∃ x . a = SOME x ∧ all_some l) 
Proof
gvs[all_some_def] >>
REPEAT STRIP_TAC >>
Cases_on ‘a’ >> gvs[]
QED   

Theorem map_is_true_normalize:
∀ a l .
map_is_true (a::l) ⇒
( a = T∧ map_is_true l) 
Proof
gvs[map_is_true_def] 
QED

Theorem is_tau_exists:
∀ x .
is_tau x ⇒
∃ tau . x = t_tau tau
Proof                  
Induct >>                     
gvs[is_tau_def]
QED


Theorem t_rm_lemma:
∀ tau . t_tau (rm_t (t_tau tau)) = t_tau tau
Proof
gvs[rm_t_def]
QED
                            

val zip_map_lemma = prove(
“∀ l1 l2 f1 f2.
ZIP (MAP f1 l1, MAP f2 l1) = l2 ⇒
 LENGTH l1 = LENGTH l2”,

Induct >> gvs[]
);



Theorem MAP_MAP_MAP_o:
∀ l f g c.
  MAP f (MAP g (MAP c l)) = MAP (f o g o c ) l 
Proof
Induct >> gvs[]
QED



Theorem struct_map_is_true_rw:
∀l.
map_is_true (MAP (\t. is_tau t) (MAP (λx. THE x) (MAP (λ(x,v). typeOf_v v) l))) = 
map_is_true (MAP (λx. is_tau (THE ((λ(x,v). typeOf_v v) x))) l)
Proof           
gvs[MAP_MAP_MAP_o] >>
gvs[combinTheory.o_DEF]
QED



val struct_tc_lemma = prove (
“
∀ n t t'.
  n < LENGTH t ∧
  n < LENGTH t' ∧
ZIP (MAP (λ(x,v). x) t,  MAP (λt. rm_t t) (MAP (λx. THE x) (MAP (λ(x,v). typeOf_v v) t))) = t' ∧
all_some (MAP (λ(x,v). typeOf_v v) t) ∧
map_is_true (MAP (λx. is_tau (THE ((λ(x,v). typeOf_v v) x))) t) ⇒
typeOf_v (SND (EL n t)) = SOME (t_tau (SND (EL n t')))” ,

Induct >> gvs[] >>
REPEAT STRIP_TAC >>
rfs[MAP_MAP_MAP_o] >>
rfs[combinTheory.o_DEF]>> 

Cases_on ‘t’ >> gvs[] >>
PairCases_on ‘h’ >> gvs[] >>
IMP_RES_TAC map_is_true_normalize >>
IMP_RES_TAC all_some_normalize >|[

    gvs[is_tau_def, rm_t_def] >>                         
    Cases_on ‘x’ >> gvs[is_tau_def, rm_t_def]  
    
    ,                             
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘t'’])) >>
    gvs[]
]                               
);



val struct_s_ty_lemma = prove (
“∀ xvl xtl s.
v_tc (v_struct xvl) (t_tau (tau_xtl s xtl)) F ⇒
 (s = struct_ty_struct)”,

REPEAT STRIP_TAC >>    
Cases_on ‘xvl’ >>
Cases_on ‘xtl’ >>
Cases_on ‘s’ >>    
gvs[v_tc] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[typeOf_v_def])
);








Theorem typeOf_state_name_imp_v_tc:               
∀ v xl.
typeOf_v v = SOME (t_string_names_a xl) ⇒
v_tc v (t_string_names_a xl) F
Proof
REPEAT STRIP_TAC >>
Cases_on ‘v’ >>
gvs[v_tc] >>
gvs[typeOf_v_def]>>
PairCases_on ‘p’ >> gvs[typeOf_v_def]
QED        





        
        
Definition typeOf_v_tc_def:
  typeOf_v_tc v =
   (∀ tau . (  typeOf_v v = SOME (t_tau tau) ==>         
  v_tc v (t_tau tau) F ))
End


Definition typeOf_xv_tc_def:
  typeOf_xv_tc (xv:(string#v)) =
  typeOf_v_tc (SND xv)
End


Definition typeOf_xvl_tc_def:
  typeOf_xvl_tc (xvl: (string#v) list) =
  ∀ (v:v) . MEM v (MAP (\(x,v). v) xvl) ==> typeOf_v_tc v
End

        
               
fun OPEN_TO_V val_term =
(Q.PAT_X_ASSUM `typeOf_v (^val_term) = SOME d` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [typeOf_v_def] thm)))


              
                                              
Theorem v_tc_correct:
(∀ v . typeOf_v_tc v) ∧
(∀ xv . typeOf_xv_tc xv) ∧
(∀ xvl . typeOf_xvl_tc xvl)
Proof           
  Induct >>
  gvs[typeOf_v_tc_def, typeOf_xvl_tc_def]>>
  REPEAT STRIP_TAC  >| [
    (*bool*)
    gvs[v_tc, typeOf_v_def]                                  
    ,   
    (*values*)                 
    gvs[v_tc, typeOf_v_def]                                      
    ,
    (* str *)
    gvs[v_tc, typeOf_v_def]                         
    ,    
    (* struct *)    
    Cases_on ‘xvl’ >-
    ( gvs[typeOf_v_def, v_tc]) >>
      
    Cases_on ‘tau’ >> rfs[typeOf_v_def] >>
    Cases_on ‘l’ >> rfs[v_tc] >>
    Cases_on ‘h’ >> Cases_on ‘h'’ >> rfs[] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[typeOf_v_def])
    ,
 
    (* headers*)
    Cases_on ‘xvl’ >-
     ( gvs[typeOf_v_def, v_tc, map_is_true_def, all_some_def]) >>
      
    Cases_on ‘tau’ >> rfs[typeOf_v_def] >>
    Cases_on ‘l’ >> rfs[v_tc] >>
    Cases_on ‘h’ >> Cases_on ‘h'’ >> rfs[] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[typeOf_v_def])
    ,
        
    (*v_bot*)
    gvs[v_tc, typeOf_v_def]                         
    ,   
    (*v_bot*)
    gvs[v_tc, typeOf_v_def]                         
    ,
    (* Induction steps for string value pairs *)
    PairCases_on ‘xv’ >>
    gvs[typeOf_xv_tc_def, typeOf_v_tc_def]
    ,
    PairCases_on ‘xv’ >>
    gvs[typeOf_xv_tc_def, typeOf_v_tc_def]
    ,
    gvs[typeOf_xv_tc_def, typeOf_v_tc_def]    
  ] 
QED    


          

(* -------------------------------------------------------------------------- *)
(*                     SOUNDNESS PROOF FOR VALUES                             *)
(* -------------------------------------------------------------------------- *)
   


Definition v_tc_sound_def:
v_tc_sound v =
 ∀ t b . (v_tc v t b  ⇒ v_typ v t  b)
End


Definition xvl_tc_sound_def:
xvl_tc_sound (xvl : (string#v) list) =
 ∀  (v:v) . MEM v (MAP SND xvl) ==> v_tc_sound v
End

        
Definition xv_tc_sound_def:
 xv_tc_sound (xv : (string#v)) =
  v_tc_sound (SND xv)
End
        

val TC_V_SOUND_TAC =
Cases_on ‘b’>> 
Cases_on ‘t’ >>  gvs[Once v_typ_cases, clause_name_def, v_tc] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[typeOf_v_def])

val MAP_DOUB_SIMP_TAC =     gvs[map_distrub] >>
    gvs[map_tri_zip12, map_rw1]>>
    gvs[ZIP_MAP_FST_SND]>>
    rfs[MAP_MAP_MAP_o, combinTheory.o_DEF]

val EL_TO_INSIDE_TAC =  gvs[EL_MAP] >> gvs[EL_ZIP]                   


val MAP_QUAD_SIMP_TAC =  gvs[map_quad_zip112] >>
gvs[map_rw2] >>
gvs[map_rw_quad] >>
gvs[UNZIP_rw]
    
Theorem TC_v_sound:
(∀v. v_tc_sound v) /\
(∀(xvl : (string#v) list). xvl_tc_sound xvl) /\
( ∀(xv : (string#v))       .xv_tc_sound xv)
Proof
       
Induct>>
gvs[v_tc_sound_def] >>
REPEAT STRIP_TAC >|[
    Cases_on ‘b'’>>
    TC_V_SOUND_TAC             
    ,
    TC_V_SOUND_TAC >>
    PairCases_on ‘p’ >>
    gvs[typeOf_v_def, bs_width_def]
    ,
    TC_V_SOUND_TAC   
    ,
    TC_V_SOUND_TAC >>
    MAP_DOUB_SIMP_TAC >>
        
    Q.EXISTS_TAC ‘(ZIP (MAP (\(a,b). a) xvl,ZIP(MAP (\(a,b). b) xvl,
                       MAP (λx. rm_t (THE (typeOf_v x))) (MAP (λ(x,v). v) xvl))))’ >>


    MAP_DOUB_SIMP_TAC >>
                                                                               
    CONJ_TAC >-
       (METIS_TAC[GSYM ZIP_MAP_FST_SND, ELIM_UNCURRY, lambda_FST, lambda_SND]) >>

    REPEAT STRIP_TAC >>
    gvs[xvl_tc_sound_def, GSYM lambda_SND] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(EL i (MAP (λ(a_,b_). b_) (xvl : (string # v) list)))’])) >> gvs[] >>
    gvs[EL_MEM, LENGTH_MAP]>>
                                                    
    gvs[v_tc_sound_def] >>
                           
    gvs[EL_map_true] >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘THE (typeOf_v ((λ(x,v). v) (EL i (xvl : (string # v) list))))’, ‘F’])) >> gvs[] >>
    IMP_RES_TAC is_tau_exists >>
    IMP_RES_TAC all_some_imp_EL >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    ASSUME_TAC v_tc_correct >>
    gvs[typeOf_v_tc_def] >>          

    gvs[is_tau_def, rm_t_def]   
    ,


    (**************)
    (** header   **)

    Cases_on ‘b'’ >>  gvs[Once v_typ_cases, clause_name_def, v_tc] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[v_tc]) >-
    TC_V_SOUND_TAC >>

    MAP_DOUB_SIMP_TAC >>
        
    Q.EXISTS_TAC ‘(ZIP (MAP (\(a,b). a) xvl,ZIP(MAP (\(a,b). b) xvl,
                       MAP (λx. rm_t (THE (typeOf_v x))) (MAP (λ(x,v). v) xvl))))’ >>


    MAP_DOUB_SIMP_TAC >>
                                                                               
    (CONJ_TAC >-
      (METIS_TAC[GSYM ZIP_MAP_FST_SND, ELIM_UNCURRY, lambda_FST, lambda_SND])) >>


    Cases_on ‘t’ >>  gvs[Once v_typ_cases, clause_name_def, v_tc] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[typeOf_v_def])>>


                                                                                        

    REPEAT STRIP_TAC >>
    gvs[xvl_tc_sound_def, GSYM lambda_SND] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(EL i (MAP (λ(a_,b_). b_) (xvl : (string # v) list)))’])) >> gvs[] >>
    gvs[EL_MEM, LENGTH_MAP]>>                                                                                         
    MAP_DOUB_SIMP_TAC >>
                                                    
    gvs[v_tc_sound_def] >>
                           
    gvs[EL_map_true] >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘THE (typeOf_v ((λ(x,v). v) (EL i (xvl : (string # v) list))))’, ‘F’])) >> gvs[] >>
    IMP_RES_TAC is_tau_exists >>
    IMP_RES_TAC all_some_imp_EL >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    ASSUME_TAC v_tc_correct >>
    gvs[typeOf_v_tc_def] >>          

    gvs[is_tau_def, rm_t_def]                            

 ,
        
 TC_V_SOUND_TAC 
 ,
 
 TC_V_SOUND_TAC 
 ,
 
 gvs[xvl_tc_sound_def]
 ,
 gvs[xvl_tc_sound_def, xv_tc_sound_def, v_tc_sound_def] >> METIS_TAC[]
 ,
 gvs[xv_tc_sound_def, v_tc_sound_def] >> METIS_TAC[]                                                
]

QED     







(****************** EXPRESSIONS ********************)





val et_struct_size_def = Define `
 (et_struct_size (a,b,c,d) = e_size a)
 `;

val find_tau_in_xtl_def = Define `
  find_tau_in_xtl (xtl:(x#tau) list) (x:x) =
     case (FIND (λ(xm,tm). xm = x) xtl) of
     | SOME (xm,tm) => SOME (tm)
     | NONE => NONE
 `;        


                


        
 (* note that the calulatur for lvalues is not here, and this is because :
    1. it complicates the definition even more especially for cases like structs
    2. I will need to extend with two constructs: one for the expresstion itself, and otherones for the subexpressions
 *)
(* Must return the type, not just the base one *)
(* TODO: finish all cases *)
val typeOf_e = TotalDefn.tDefine "typeOf_e" `
                          
(* values *)              
(typeOf_e (e_v v) tslg tsl (T_e:T_e) = 
  case (typeOf_v v) of
   | SOME t =>  SOME (t, F)
   | NONE => NONE 
)

        
∧

(* variable names *)        
(typeOf_e (e_var (varn_star f')) tslg tsl (ord,f,(d_g,d_b,d_x,d_t)) =  
 (case (t_lookup_funn f' d_g d_b d_x) of
  | SOME (txdl , t ) =>
      (case (find_star_in_globals tslg (varn_star f')) of
       | SOME t' => (case (t = t') of
                     | T => SOME (t_tau t , T)
                     | F => NONE
                    )     
       | NONE => NONE
      )
  | NONE => NONE
 )
)

∧

(typeOf_e (e_var varn) tslg tsl (T_e:T_e) =
  case (lookup_tau tsl tslg varn) of
  | SOME t => SOME (t_tau t , T)
  | NONE   => NONE               
)



        
∧
(* structs *)
(typeOf_e (e_struct xel) tslg tsl T_e =
 (
 let el = ( MAP (\(x,e).e) xel) in
  let xl = ( MAP (\(x,e).x) xel) in
  let (tl_bl_some: (t#bool)option list ) = ( MAP (\e. (typeOf_e e  tslg tsl T_e)) el) in
    (case (all_some tl_bl_some) of         
     | T =>
         ( let (tl_bl: (t#bool)list ) = (MAP (\x. THE x ) tl_bl_some) in
             let (tl:t list) = MAP (\(t,b). t) tl_bl in
             let (bl:bool list) = MAP (\(t,b).b) tl_bl in
       
                (case (map_is_true (MAP (\t. is_tau t) tl)) of
                 | T =>
                     let  tl_t_removed = MAP (\t. rm_t t) tl in
                       let  xtl = ZIP(xl,tl_t_removed) in         
                           SOME (t_tau (tau_xtl struct_ty_struct (xtl)), F)
                 | F => NONE
                )
          )
     | F => NONE    
    )
 )
)



∧
(* header *)
(typeOf_e (e_header boolv xel) tslg tsl T_e =
 (
 let el = ( MAP (\(x,e).e) xel) in
  let xl = ( MAP (\(x,e).x) xel) in
  let (tl_bl_some: (t#bool)option list ) = ( MAP (\e. (typeOf_e e  tslg tsl T_e)) el) in
    (case (all_some tl_bl_some) of         
     | T =>
         ( let (tl_bl: (t#bool)list ) = (MAP (\x. THE x ) tl_bl_some) in
             let (tl:t list) = MAP (\(t,b). t) tl_bl in
             let (bl:bool list) = MAP (\(t,b).b) tl_bl in
       
                (case (map_is_true (MAP (\t. is_tau t) tl)) of
                 | T =>
                     let  tl_t_removed = MAP (\t. rm_t t) tl in
                       let  xtl = ZIP(xl,tl_t_removed) in         
                           SOME (t_tau (tau_xtl struct_ty_header (xtl)), F)
                 | F => NONE
                )
          )
     | F => NONE    
    )
 )
)



        

∧
(* TODO: PROBLEM HERE? *)
(* access fld *) (* TODO: our rule can never make access an lval, in the type system should be b' not teh same b*)
( typeOf_e (e_acc e f) tslg tsl T_e =
  case (typeOf_e e tslg tsl T_e) of
  | SOME (t_tau (tau_xtl struct_ty xtl), b) =>
      ( case (find_tau_in_xtl xtl f ) of
        | SOME t => (case (correct_field_type xtl f t) of
                     | T => SOME (t_tau t, b)
                     | F => NONE
                    )
        | NONE => NONE
      )
  | _ => NONE
        
)

       
∧

(* note that we actually care about the overall lval boolean of teh whole expression, not sub exp here, this is why it is F*)
(typeOf_e (e_unop unop e) tslg tsl T_e =
 case (unop  =  unop_neg) of
 | T => (case (typeOf_e e tslg tsl T_e) of
         | SOME (t_tau tau_bool, b) =>  SOME (t_tau tau_bool, F)
         | SOME _ => NONE
         | NONE => NONE ) 
 | F => (case (typeOf_e e tslg tsl T_e) of
         | SOME (t_tau (tau_bit  w), b) =>
                ( case (w  > 0 /\  w  <= 64) of
                  | T => SOME (t_tau (tau_bit  w) ,F)
                  | F => NONE                        
                )
         | SOME _ => NONE
         | NONE => NONE ) 
)

∧




(*binop*)
        
(typeOf_e (e_binop e binop e') tslg tsl T_e =
(case (typeOf_e e tslg tsl T_e) of
 | SOME (t_tau tau_bool, b) =>
     ( case (typeOf_e e' tslg tsl T_e) of
       | SOME (t_tau tau_bool, b') =>
           ( case (is_bool_op  binop) of
                  | T => SOME (t_tau tau_bool, F)
                  | F => NONE
                        
                )
       | _ => NONE
     )       
 | SOME (t_tau (tau_bit w) , b) =>
     ( case (typeOf_e e' tslg tsl T_e) of
       | SOME (t_tau (tau_bit w') , b') =>
           ( case ( w= w' ∧ w  > 0 /\  w  <= 64 ) of
             | T=> ( case (is_bv_op binop) of
                     | T => SOME (t_tau (tau_bit w), F)
                     | F =>
                         ( case (is_bv_bool_op binop) of
                           | T => SOME (t_tau tau_bool, F)
                           | F => NONE
                         ) 
                   )
             | F => NONE
           )
       | _ => NONE
     )
 | _ => NONE ) 
)

∧









        

(*concat*)

(typeOf_e (e_concat e e') tslg tsl T_e =
 case (typeOf_e e tslg tsl T_e) of
 | SOME (t_tau (tau_bit  w) , b) =>
     ( case (typeOf_e e' tslg tsl T_e) of
       | SOME (t_tau (tau_bit w') , b') => SOME (t_tau (tau_bit (w+w')) , F)
       | _ => NONE
        )
 | _ => NONE
)

∧



        
(*cast*)
(typeOf_e ( e_cast (cast_unsigned n) e) tslg tsl T_e =
 case (typeOf_e e tslg tsl T_e) of
 | SOME (t_tau (tau_bit n') , b ) =>
        (case ( n  > 0 /\  n  <= 64 ) of
        | T => SOME (t_tau (tau_bit n),F)
        | F => NONE
        )                                        
 | SOME (t_tau (tau_bool) , b) =>  
         (case ( n  > 0 /\  n  <= 64 ) of
          | T => SOME (t_tau (tau_bit n),F)
          | F => NONE
         )   
                                         
 | _ => NONE    
)
∧




        
(*slice*)
(typeOf_e ( e_slice e e' e'') tslg tsl T_e =
case e' of
| (e_v (v_bit bitv)) =>
  ( case e'' of              
    | (e_v (v_bit bitv'))  =>
           (let w1 = vec_to_const bitv in
              let w2 = vec_to_const bitv' in
                case (typeOf_e e tslg tsl T_e ) of
                | SOME (t_tau (tau_bit  w ) , b) =>
                    ( case (bits_length_check  w w1 w2) of
                      | T => SOME (t_tau (tau_bit (w1 − w2 + 1)),b)
                      | F => NONE 
                    )
                | _ => NONE)
    | _ => NONE)      
| _ => NONE
)
∧

    


(* select *)
(typeOf_e (e_select e (vxl) x) tslg tsl T_e =
 let xl = MAP (\(v,x).x) vxl in
  let vl = MAP (\(v,x).v) vxl in
  case (typeOf_e e tslg tsl T_e) of    
   | SOME (t_tau tau, b) => 
       (let tl_some = MAP (\v. typeOf_v v) vl in
         (case (all_some tl_some) of
          | T => ( case (map_is_true (MAP (\t. is_tau (THE t) ∧ THE t = t_tau tau) tl_some)) of
                   | T => SOME (t_string_names_a (xl ++ [x]) , F)
                   | F => NONE
                 )
          | F => NONE
         ))
   | SOME _ => NONE
   | NONE => NONE 
)

∧


        



(*function call*)
(typeOf_e (e_call f el) tslg tsl ((ord,f',(d_g,d_b,d_x,d_t)):T_e) =
 case (t_lookup_funn f d_g d_b d_x ) of
 | SOME ( txdl , tau ) => (
   let tl = MAP (\(t,x,d).t) txdl in
    let dl = MAP (\(t,x,d).d) txdl in
     let (tl'_bl_some: (t#bool)option list ) = ( MAP (\e. (typeOf_e e  tslg tsl (ord,f',(d_g,d_b,d_x,d_t)))) el) in
       (case (all_some tl'_bl_some) of         
        | T => (
          let (tl'_bl: (t#bool)list ) = (MAP (\x. THE x ) tl'_bl_some) in
            let (tl':t list) = MAP (\(t,b). t) tl'_bl in
             let (bl:bool list) = MAP (\(t,b).b) tl'_bl in
  
                (case (map_is_true (MAP (\t. is_tau t) tl')) of
                 | T =>
                     let  tl'_t_removed = MAP (\t. rm_t t) tl' in
                       ( case (tl'_t_removed = tl) of
                         | T => (
                             case ( map_is_true ( MAP (\(d,b). is_d_out d ⇒ b ) (ZIP(dl,bl)))) of
                         | T => (case (ord (order_elem_f f) (order_elem_f f')) of
                                 | T => SOME (t_tau tau , F)
                                 | F => NONE
                                ) 
                                
                              | F => NONE
                           )
                         | F => NONE
                        )
                | F => NONE
                )


          )
          | F => NONE    
       )

   )
 | NONE => NONE
        
)∧






 typeOf_e _ _ _ _ = NONE
                        
`
(
WF_REL_TAC `measure et_struct_size` >>
gvs[et_struct_size_def] >>
 REPEAT STRIP_TAC >>
 IMP_RES_TAC xel_size_mem >>
gvs[e_size_def] >>
IMP_RES_TAC e1_size_mem >>
fs [e_size_def] >>
IMP_RES_TAC e3_size_mem >>
fs [e_size_def] 
);



        

        

val T_e0 = “ (ord,f,(d_g,[("z", (txdl, (tau_bot)))],d_x,d_t)) : T_e”;

val tslg0  = “[(varn_name "y", tau_bot, (NONE:lval option));
              (varn_star (funn_name "z"), tau_bot, (NONE: lval option))]”;
val tsl0 = “[(varn_name "x", tau_bool, (NONE: lval option));
              (varn_name "y", tau_bool, (NONE: lval option))]”;
val tsl0_slice = “[(varn_name "x", (tau_bit 4), (NONE: lval option));
                   (varn_name "y", tau_bool, (NONE: lval option))]”;
             
EVAL “typeOf_e (e_var (varn_name "y")) [^tslg0] [^tsl0] ^T_e0”; (*bool*)
EVAL “typeOf_e (e_var (varn_name "x")) [^tslg0] [^tsl0] ^T_e0”; (*bool*)
EVAL “typeOf_e (e_var (varn_name "z")) [^tslg0] [^tsl0] ^T_e0”; (*NONE*)
EVAL “typeOf_e (e_var (varn_star (funn_name "z"))) [^tslg0] [^tsl0] ^T_e0”; (*bot*)
EVAL “typeOf_e (e_var (varn_star (funn_name "z"))) [^tslg0] [^tsl0] ^T_e0”; (*bot*)
EVAL “typeOf_e (e_unop  unop_neg (e_v (v_bool T))) [] [] ^T_e0”; (*tau_bool*)
EVAL “typeOf_e (e_unop  unop_neg (e_var (varn_name "x"))) [^tslg0] [^tsl0] ^T_e0”; (*tau_bool*)

        

val T_efun0 = “ (ord,f,(d_g,[("z", ([(tau_bit 1, "o", d_in )], (tau_bot)))],d_x,d_t)) : T_e”;
EVAL “typeOf_e (e_call  (funn_name "z") [(e_v (v_bit([F],1)))]) [^tslg0] [^tsl0] ^T_efun0”; (*bot*)

val T_efun1 = “ (ord,f,(d_g,[("z", ([(tau_bit 2, "o", d_in )], (tau_bot)))],d_x,d_t)) : T_e”;
EVAL “typeOf_e (e_call  (funn_name "z") [(e_v (v_bit([F],1)))]) [^tslg0] [^tsl0] ^T_efun1”; (*NONE-- type of arg different*)


val T_efun2 = “ (ord,f,(d_g,[("z", ([(tau_bit 2, "o", d_in )], (tau_bot)))],d_x,d_t)) : T_e”;
EVAL “typeOf_e (e_call  (funn_name "z") [(e_v (v_bit([F],1))); (e_v v_bot)]) [^tslg0] [^tsl0] ^T_efun2”; (*NONE-- num of args different*)

     
val T_efun2 = “ (ord,f,(d_g,[("z", ([(tau_bit 1, "o", d_inout )], (tau_bot)))],d_x,d_t)) : T_e”;
EVAL “typeOf_e (e_call  (funn_name "z") [(e_v (v_bit([F],1)))]) [^tslg0] [^tsl0] ^T_efun2”; (*direction inout, but not lval passed*)


EVAL “typeOf_e (e_select (e_v v_bot) [((v_bool F), "a")] "b" ) [^tslg0] [^tsl0] ^T_e0”; (*NONE*)
EVAL “typeOf_e (e_select (e_v (v_bool F)) [((v_bool F), "a")] "b" ) [^tslg0] [^tsl0] ^T_e0”; (*[a,b]*)

EVAL “typeOf_e (e_slice (e_v(v_bit ([T;F;F],3))) (e_v (v_bit ([T],1))) (e_v (v_bit ([F],1)))) [] [] T_e”; (* 2, F*)
EVAL “typeOf_e (e_slice (e_var (varn_name "x"))  (e_v (v_bit ([T],1))) (e_v (v_bit ([F],1)))) [] [^tsl0_slice] ^T_e0”; (* 2 ,T*)

(*    
EVAL “typeOf_e  (e_acc ^e_struct0 "x" ) [] [^tsl0_slice] ^T_e0” (* 4 ,F because the expression is directly a struct*)

val e_struct0 = “e_struct [("x" ,e_v (v_bit ([T;F;F;F],4)))]”;
val t_struct0 = “ (tau_xtl struct_ty_struct [("x", tau_bit  4)])” ;
val tsl0_struct = “[(varn_name "a", ^t_struct0, (NONE: lval option))]”;

EVAL “typeOf_e  (e_acc (e_var (varn_name "a")) "x" ) [] [^tsl0_struct] ^T_e0”; (* 4 ,T because accessing it in the state, not directly a struct exp*)
*)








                            
Definition e_tc:
(* val *)  
  ( ( e_tc t_scopes_tup (T_e:T_e) (e_v v) t  F  ) = (v_tc v t  F )) ∧

(( e_tc  (tslg,tsl) ((ord,f,(d_g,d_b,d_x,d_t)):T_e)  (e_var (varn_star f')) (t_tau tau)  b) =  
 (
 case (typeOf_e  (e_var (varn_star f'))  tslg tsl (ord,f,(d_g,d_b,d_x,d_t)) ) of
 | SOME (t_tau t, b') => (t = tau ∧ b = b')
 | SOME (t_string_names_a  t,b') => F                        
 | NONE => F               
 )

) ∧
   
(* var name *)   (* TODO why in the example it must be a proper T_e tuples not just T_e*)      
(( e_tc  (tslg,tsl)  (T_e:T_e) (e_var varn) (t_tau tau)  b  ) =
 (
 case (typeOf_e  (e_var varn)  tslg tsl T_e ) of
 | SOME (t_tau t, b') => (t = tau ∧ b = b')
 | SOME (t_string_names_a  t,b) => F                        
 | NONE => F                  
 )
)
 ∧



(* struct *)

((e_tc  (tslg,tsl) (T_e:T_e) (e_struct (xel)) (t_tau tau) b)   =
 (
 (case (typeOf_e (e_struct (xel)) tslg tsl T_e) of
  | SOME (t_tau t, b') => (t = tau ∧ b = b')
  | SOME (t_string_names_a  t,b') => F                        
  | NONE => F              
))) ∧




(* header *)

((e_tc  (tslg,tsl) (T_e:T_e) (e_header boolv (xel)) (t_tau tau) b)   =
 (
 (case (typeOf_e (e_header boolv (xel)) tslg tsl T_e) of
  | SOME (t_tau t, b') => (t = tau ∧ b = b')
  | SOME (t_string_names_a  t,b') => F                        
  | NONE => F              
))) ∧

    

(* access fld *)

((e_tc  (tslg,tsl) (T_e:T_e) (e_acc e f) (t_tau tau) b)   =
 (
 (case (typeOf_e (e_acc e f) tslg tsl T_e) of
  | SOME (t_tau t, b') => (t = tau ∧ b = b')
  | SOME (t_string_names_a  t,b') => F                        
  | NONE => F              
))) ∧

    
(* unop *)

 ((e_tc  (tslg,tsl) (T_e:T_e) (e_unop unop e) (t_tau tau) b)   = (
   case (typeOf_e  (e_unop unop e) tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ (b = b'))
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧


(* binop *)

 ((e_tc  (tslg,tsl) (T_e:T_e) (e_binop e binop e') (t_tau tau) b)   = (
   case (typeOf_e  (e_binop e binop e') tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ (b = b'))
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧



   

(* concat *)

 ((e_tc  (tslg,tsl) (T_e:T_e) ( e_concat e e') (t_tau tau) b)   = (
   case (typeOf_e  ( e_concat e e') tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ (b = b') ∧ (b=F))
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧




   
(* slice *)

 ((e_tc  (tslg,tsl) (T_e:T_e) ( e_slice e e' e'') (t_tau tau) b)   = (
   case (typeOf_e  ( e_slice e e' e'') tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ (b = b'))
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧



   
(* cast *)

 ((e_tc  (tslg,tsl) (T_e:T_e) (e_cast (cast_unsigned n) e) (t_tau tau) b)   = (
   case (typeOf_e  ( e_cast (cast_unsigned n) e) tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ (b = b') ∧ (b=F))
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧
   

   
(* select *)

 ((e_tc  (tslg,tsl) (T_e:T_e) (e_select e (vxl) x) (t_string_names_a xl) b)   = (
   case (typeOf_e  (e_select e (vxl) x) tslg tsl T_e) of
   | SOME (t_tau t, b') => F
   | SOME (t_string_names_a  t ,b') => (t = xl ∧ b = b' ∧ b = F)                      
   | NONE => F               
   ))∧


   


(* f call *)

 ((e_tc  (tslg,tsl) (T_e:T_e) (e_call funn' el) (t_tau tau) b)   = (
   case (typeOf_e  (e_call funn' el) tslg tsl T_e) of
   | SOME (t_tau t, b') => (t = tau ∧ b = b' ∧ b = F)
   | SOME (t_string_names_a  t,b') => F                        
   | NONE => F               
   )) ∧


   
(e_tc _ _ _ _  _ = F)
   
End
           

val e_tc = save_thm("e_tc", e_tc);
val e_tc_ind = tryfind (uncurry DB.fetch) [("scratch", "e_tc_ind"),
                                             ("p4_tc", "e_tc_ind")];
val _ = save_thm("e_tc_ind", e_tc_ind);

                         



(******************************************************************************)
(*                Test cases ; TODO: add more                                 *)
(******************************************************************************)

      
           
val tslg1 = “[(varn_name "x", tau_bool, (NONE: lval option))]”;
val tsl1  = “[(varn_name "y", tau_bot, (NONE:lval option))]”;
val T_e1 = “ (ord,f,([],[("x", (txdl, (tau_bot)))],[],d_t)) : T_e”;

EVAL “e_tc ([^tslg1],[^tsl1]) ^T_e1 (e_v (v_bit ([T;F;F],3))) (t_tau (tau_bit  3 )) F ”;(*True*)
EVAL “e_tc ([^tslg1],[^tsl1]) ^T_e1 (e_v (v_bit ([T;F;F;T],4))) (t_tau (tau_bit  3 )) F ”;(*False*)

EVAL “e_tc ([^tslg1],[^tsl1]) ^T_e1 (e_var (varn_name "x")) (t_tau (tau_bool)) T ”; (*True*)
EVAL “e_tc ([^tslg1],[^tsl1]) ^T_e1 (e_var (varn_name "y")) (t_tau (tau_bot)) T ”; (*True*)
EVAL “e_tc ([^tslg1],[^tsl1]) ^T_e1 (e_var (varn_star (funn_name "y"))) (t_tau (tau_bot)) T ”; (*False*)

(*                                                                                                        
EVAL “e_typ ([^tslg1],[^tsl1]) (^T_e1:T_e) (e_var (varn_name "x")) (t_tau (tau_bool)) T ”;
rw[Once e_typ_cases] >> EVAL_TAC>> FULL_SIMP_TAC std_ss []*)

val tslg2 = “[(varn_star (funn_name "x"), tau_bool, (NONE: lval option))]”;
val tsl2  = “[(varn_name "y", tau_bot, (NONE:lval option))]”;
EVAL “e_tc ([^tslg2],[^tsl2]) ^T_e1 (e_var (varn_star (funn_name "x"))) (t_tau (tau_bot)) T ”;  (*False*)    
EVAL “e_tc ([^tslg2],[^tsl2]) ^T_e1 (e_var (varn_star (funn_name "x"))) (t_tau (tau_bool)) T ”; (*False, because the type doesnt match in global's star and return *)    


val tslg3 = “[(varn_star (funn_name "x"), tau_bot, (NONE: lval option))]”;
EVAL “e_tc ([^tslg3],[^tsl2]) ^T_e1 (e_var (varn_star (funn_name "x"))) (t_tau (tau_bot)) T ”; (*True*)   


(*     
EVAL “e_typ ([^tslg2],[^tsl2]) ^T_e (e_var (varn_star (funn_name "x"))) (t_tau (tau_bot)) T”;
rw[Once e_typ_cases] >> fs[]>> FULL_SIMP_TAC std_ss []*)

val e_struct0 = “e_struct [("x" ,e_v (v_bit ([T;F;F;F],4)))]”;
val t_struct0 = “ t_tau (tau_xtl struct_ty_struct [("x", tau_bit  4)])” ;

EVAL “e_tc ([^tslg3],[^tsl2]) ^T_e1 ^e_struct0 ^t_struct0 F ”; (*True*)   

    
val e_struct1 = “e_struct [("x" ,e_var (varn_name "x"))]”;
val t_struct1 = “ t_tau (tau_xtl struct_ty_struct [("x", tau_bool)])” ;        

EVAL “e_tc ([^tslg1],[^tsl2]) ^T_e1 ^e_struct1 ^t_struct1 F ”; (*True*)   



val e_struct01 = “e_struct [("x" ,e_var (varn_name "x"));("y" ,e_v (v_bit ([T;F;F;F],4)))]”;
val t_struct01 = “ t_tau (tau_xtl struct_ty_struct [("x", tau_bool);("y", tau_bit  4)])” ;        

EVAL “e_tc ([^tslg1],[^tsl2]) ^T_e1 ^e_struct01 ^t_struct01 F ”; (*True*)   
EVAL “e_tc ([^tslg1],[^tsl2]) ^T_e1 ^e_struct01 ^t_struct01 F ”; (*True*)   
EVAL “e_tc ([^tslg1],[^tsl2]) ^T_e1 ^e_struct01 ^t_struct01 F ”; (*True*)   
EVAL “e_tc ([^tslg1],[^tsl2]) ^T_e1 ^e_struct01 ^t_struct01 F ”; (*True*)   


EVAL “e_tc ([],[^tsl0]) ^T_e0 (e_unop  unop_neg (e_var (varn_name "x"))) (t_tau tau_bool) F” ; (*true*)
EVAL “e_tc ([],[])      ^T_e0 (e_unop  unop_neg (e_v (v_bool T))) (t_tau tau_bool) F” ; (*true*)
EVAL “e_tc ([],[])      ^T_e0 (e_unop  unop_neg (e_v (v_bit ([T],1)))) (t_tau tau_bool) F” ; (*false*)
(*
EVAL “e_tc ([],[^tsl0_struct]) ^T_e0 (e_acc (e_var (varn_name "a")) "x" ) (t_tau (tau_bit 4)) T  ”;  (*true*)
EVAL “e_tc ([],[^tsl0_struct]) ^T_e0 (e_acc (e_var (varn_name "a")) "x" ) (t_tau (tau_bit 4)) F  ” ; (*false*)
*)

     

(******************************************************************************)
(*                    EXPRISSIONS soundness proof                             *)
(******************************************************************************)
     






Definition e_tc_sound_def:
e_tc_sound e =
∀ T_e t_scopes_tup t b . (e_tc  t_scopes_tup  T_e e t  b ⇒
          e_typ t_scopes_tup T_e e t  b   )
End

Definition xel_tc_sound_def:
   xel_tc_sound (xel : (string#e) list)
      = !  (e:e) . MEM e (MAP (\(x,e). e) xel) ⇒ e_tc_sound e
End


                                                   
Definition el_tc_sound_def:
  el_tc_sound (el : e list)  =
    !(e : e). MEM e el ==> e_tc_sound e
End

        
Definition xe_tc_sound_def:
 xe_tc_sound (xe : (string#e))=
          e_tc_sound (SND xe)
End



                 
   

        

Theorem typeOf_e_imp_e_tc:               
∀ e tslg tsl T_e tau b.
typeOf_e e tslg tsl T_e = SOME (t_tau tau , b) ⇒
e_tc (tslg,tsl) T_e e (t_tau tau) b
Proof

Induct >>
REPEAT STRIP_TAC >>

TRY (PairCases_on ‘T_e’ >>        
     rename1 `(ord,f,d_g,d_b,d_x,d_t)`) >>
TRY(gvs[e_tc, typeOf_e] )
>| [
    (* values *)
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    ASSUME_TAC v_tc_correct >>
    fs[typeOf_v_tc_def, e_tc]
    ,

    (* variable names *)
    Cases_on ‘v’ >>
    SIMP_TAC list_ss [e_tc] >>
    gvs[]
    ,
    (*cast*)
    Cases_on ‘b’ >>
    Cases_on ‘c’ >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[e_tc, typeOf_e] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])                
    ,
    (* concat *)
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
    ,
        
    (* function call *) 
    Cases_on ‘b’ >>
    PairCases_on ‘T_e’ >>         
    gvs[e_tc, typeOf_e] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
    
    ,    
    (* select *)
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
]      
QED
         






Theorem typeOf_state_name_imp_e_tc:               
∀ e tslg tsl T_e tau b xl.
typeOf_e e tslg tsl T_e = SOME (t_string_names_a xl , b) ⇒
e_tc (tslg,tsl) T_e e (t_string_names_a xl) b
Proof

Induct >>
REPEAT STRIP_TAC >>

TRY (PairCases_on ‘T_e’ >>        
rename1 `(ord,f,d_g,d_b,d_x,d_t)`) >>
TRY(gvs[e_tc] ) >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
TRY(gvs[typeOf_e]) >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >| [
    gvs[e_tc] >>
    IMP_RES_TAC typeOf_state_name_imp_v_tc
    ,
    Cases_on ‘v’ >> gvs[typeOf_e] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
    ,
     Cases_on ‘c’ >> gvs[typeOf_e] >>
     REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
    ,
    PairCases_on ‘T_e’ >> gvs[typeOf_e] >>
     REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])       
  ]
QED






         

val zip_doub_eq_lemma = prove (
“∀ a b c d.
  LENGTH a = LENGTH b∧
  LENGTH b = LENGTH d∧
  LENGTH c = LENGTH a∧         
ZIP (a,b) = ZIP (c,d) ⇒
(a=c ∧ b=d) ”,

Induct_on ‘a’ >> gvs[] >>
Induct_on ‘b’ >> gvs[] >>
Induct_on ‘c’ >> gvs[] >>
Induct_on ‘d’ >> gvs[] >>
REPEAT STRIP_TAC >> RES_TAC       
);











        



        

Theorem e_struct_soundness:
∀ xel t tslg tsl T_e b boolv.
  (xel_tc_sound xel ∧
   typeOf_e (e_struct xel) tslg tsl T_e = SOME (t_tau t,b) ⇒
 e_typ (tslg,tsl) T_e (e_struct xel) (t_tau t) b) ∧
  (xel_tc_sound xel ∧
   typeOf_e (e_header boolv xel) tslg tsl T_e = SOME (t_tau t,b) ⇒
e_typ (tslg,tsl) T_e (e_header boolv xel) (t_tau t) b)
Proof

 
REPEAT STRIP_TAC >>
PairCases_on ‘T_e’ >>        
rename1 `(ord,f,(d_g,d_b,d_x,d_t))` >>
Cases_on ‘t’ >> 
Cases_on ‘b’ >>

         
TRY (fs [Once e_typ_cases, typeOf_e, clause_name_def] ) >>

MAP_DOUB_SIMP_TAC >>

Q.EXISTS_TAC ‘ZIP( (MAP (λ(x,e). x) xel),
                   ZIP ( (MAP (λ(x,e). e) xel),
                         ZIP (MAP (λx. rm_t ((λ(t,b). t) (THE (typeOf_e ((λ(x,e). e) x) tslg tsl (ord,f,d_g,d_b,d_x,d_t))))) xel,
                              MAP (λx. ((λ(t,b). b) (THE (typeOf_e ((λ(x,e). e) x) tslg tsl (ord,f,d_g,d_b,d_x,d_t))))) xel )))’>>
       
                

NTAC 2 (   
EL_TO_INSIDE_TAC >> 
MAP_DOUB_SIMP_TAC >>
MAP_QUAD_SIMP_TAC) >>

(CONJ_TAC >-
 (METIS_TAC[GSYM ZIP_MAP_FST_SND, ELIM_UNCURRY, lambda_FST, lambda_SND])) >>

REPEAT STRIP_TAC >>

gvs[xel_tc_sound_def, GSYM lambda_SND] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘((λ(x,e). e) (EL i (xel : (string # e) list)))’])) >> gvs[] >>

SIMP_TAC list_ss [Once v_typ_cases] >> gvs[clause_name_def] >>


              
(subgoal ‘MEM ((λ(x,e). e) (EL i xel)) (MAP (λ(x,e). e) xel)’ >-
   (gvs[MEM_EL] >>
   Q.EXISTS_TAC ‘i’ >> gvs[] >>
   EL_TO_INSIDE_TAC
   ) ) >>
gvs[] >>

        
gvs[e_tc_sound_def] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(ord,f,d_g,d_b,d_x,d_t)’, ‘(tslg,tsl)’, ‘(t_tau
             (rm_t
                ((λ(t,b). t)
                   (THE
                      (typeOf_e ((λ(x,e). e) (EL i (xel : (string # e) list))) tslg tsl
                       (ord,f,d_g,d_b,d_x,d_t))))))’,
                                           ‘((λ(t,b). b)
             (THE
                (typeOf_e ((λ(x,e). e) (EL i (xel : (string # e) list))) tslg tsl
                   (ord,f,d_g,d_b,d_x,d_t))))’])) >> gvs[] >>
MAP_DOUB_SIMP_TAC >>


                    
    gvs[EL_map_true] >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>
    
    IMP_RES_TAC is_tau_exists >>
    IMP_RES_TAC all_some_imp_EL >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>
    PairCases_on ‘x’ >> gvs[] >>
    IMP_RES_TAC typeOf_e_imp_e_tc >> gvs[] >>        

    gvs[is_tau_def, rm_t_def]   
              
QED











Theorem f_call_soundness:
∀ el f tslg tsl ord f' d_g d_b d_x d_t t .
   el_tc_sound el ∧
   typeOf_e (e_call f el) tslg tsl (ord,f',(d_g,d_b,d_x,d_t))=
        SOME (t_tau t,F) ⇒
        e_typ (tslg,tsl) (ord,f',(d_g,d_b,d_x,d_t)) (e_call f el)
          (t_tau t) F
Proof



REPEAT STRIP_TAC >>
fs [Once e_typ_cases, typeOf_e, clause_name_def] >>

NTAC 3 (   
MAP_DOUB_SIMP_TAC >>
MAP_QUAD_SIMP_TAC) >>

REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>



Q.EXISTS_TAC ‘ ZIP (el,
                    ZIP(MAP (λ(t,x,d). t) q,
                        ZIP(MAP (λ(t,x,d). x) q,
                            ZIP (MAP (λ(t,x,d). d) q
                                        ,MAP (λx. (λ(t,b). b) (THE (typeOf_e x tslg tsl (ord,f',d_g,d_b,d_x,d_t)))) el))))’ >>
    
‘LENGTH el = LENGTH q ’ by gvs[MAP_EQ_EVERY2] >>
    
rfs[map_distrub_penta] >>

NTAC 2 (   
EL_TO_INSIDE_TAC >> 
MAP_DOUB_SIMP_TAC >>
MAP_QUAD_SIMP_TAC) >>


(* list simplification for txdl*)                   
CONJ_TAC >-
(rw[lambda_unzip_tri]) >>
rw[] >|[
       
  (* for the expressions arguments subcase *)

gvs[el_tc_sound_def] >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘EL i el’])) >> gvs[] >>
gvs[EL_MEM] >>
  
gvs[e_tc_sound_def] >>
LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(ord,f',d_g,d_b,d_x,d_t)’, ‘(tslg,tsl)’])) >> gvs[] >>

gvs[EL_map_true] >>
NTAC 2 (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’]))) >> gvs[] >>
EL_TO_INSIDE_TAC >>
MAP_DOUB_SIMP_TAC >>

LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘(t_tau ((λ(t,x,d). t) (EL i (q : (tau # string # d) list))))’,
                                           ‘((λ(t,b). b)
             (THE (typeOf_e (EL i el) tslg tsl (ord,f',d_g,d_b,d_x,d_t))))’])) >> gvs[] >>



             
IMP_RES_TAC all_some_imp_EL >>
FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
EL_TO_INSIDE_TAC >>

gvs[MAP_EQ_EVERY2] >>
gvs[LIST_REL_EL_EQN] >>

FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
EL_TO_INSIDE_TAC >>
PairCases_on ‘x’ >> gvs[] >>
Cases_on ‘x0’ >> gvs[is_tau_def, rm_t_def]>>         
IMP_RES_TAC typeOf_e_imp_e_tc >> gvs[]

,
(* out is lval case *)
gvs[out_is_lval_def] >>
REPEAT STRIP_TAC >>

EL_TO_INSIDE_TAC >> 
MAP_DOUB_SIMP_TAC >>
MAP_QUAD_SIMP_TAC >>

gvs[EL_map_true] >>
NTAC 2 (LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’]))) >> gvs[] >>       
NTAC 2 EL_TO_INSIDE_TAC
]
QED

         







val E_TC_EXTRACT_AND_RENAME =     fs[e_tc_sound_def] >>
    REPEAT STRIP_TAC >>
    PairCases_on ‘t_scopes_tup’ >>
    rename1 `(tslg,tsl)` >>
    PairCases_on ‘T_e’ >>        
    rename1 `(ord,f,(d_g,d_b,d_x,d_t))` 


fun OPEN_EXP_TC_TAC exp_term =
(Q.PAT_X_ASSUM `e_tc (a1,a2) (t1,t2,t3,t4,t5,t6) ^exp_term h l` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [e_tc] thm)))




               


Theorem binop_soudness:
∀ e e' b. e_tc_sound e ∧  e_tc_sound e' ⇒
         e_tc_sound (e_binop e b e')
Proof

 E_TC_EXTRACT_AND_RENAME >>
           
 SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
 gvs[typeOf_e] >>

 Cases_on ‘b’ >>
 Cases_on ‘t’ >>
 fs[e_tc, is_bv_bool_op_def, is_bv_op_def, is_bool_op_def] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[is_bv_bool_op_def, is_bv_op_def, is_bool_op_def ]) >> 
 gvs[typeOf_e] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[is_bv_bool_op_def, is_bv_op_def, is_bool_op_def ]) >> 
 IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >> gvs[] >>
 TRY ( qexistsl_tac [‘r'’,‘r’] >> gvs[]) >>
 TRY ( qexistsl_tac [‘n’,‘r'’,‘r’] >> gvs[]) >| [
    DISJ1_TAC >> qexistsl_tac [‘r'’,‘r’] >> gvs[]
    ,
    DISJ2_TAC >> qexistsl_tac [‘n’, ‘r'’,‘r’] >> gvs[]
    ,
    DISJ1_TAC >> qexistsl_tac [‘r'’,‘r’] >> gvs[]
    ,
    DISJ2_TAC >> qexistsl_tac [‘n’, ‘r'’,‘r’] >> gvs[]
]
QED












        





         
Theorem TC_e_sound:
  (∀(e:e). e_tc_sound e) /\
  (∀(el : e list). el_tc_sound el) /\
  (∀(xel : (string#e) list). xel_tc_sound xel) /\
  ( ∀(xe : (string#e)). xe_tc_sound xe)
Proof
  Induct >>     
  REPEAT STRIP_TAC >| [
         
    (* values *)     
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    gvs[e_tc, Once e_typ_cases, clause_name_def] >>
              
    ASSUME_TAC TC_v_sound >>
    gvs[v_tc_sound_def]
        
    ,
        
    (* variable names *)
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘v’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >>
    fs[Once e_typ_cases, clause_name_def ] >>
    (*var name tc soundness *)
    gvs[typeOf_e] >>      
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
                                       
    ,
        
    (* e_list *)    
    E_TC_EXTRACT_AND_RENAME >>
    gvs[el_tc_sound_def]  >>
    gvs[e_tc]
        
    ,
        
    (* feild access *)
    E_TC_EXTRACT_AND_RENAME >>
    gvs[el_tc_sound_def]  >>
    gvs[e_tc] >>
              
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >>                        
  
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
             
    SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
    gvs[typeOf_e] >>
     (*var name tc soundness *)
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>   
    qexistsl_tac [‘l’,‘s'’] >> gvs[]

        
    ,
    (* unary operations *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >>                        
  
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
             
    SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
    gvs[typeOf_e] >>
     (*var name tc soundness *)
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>   
    Q.EXISTS_TAC ‘r’ >> gvs[]                       
    ,
       
    (* e cast *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    Cases_on ‘c’ >>
    fs[e_tc] >> 
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 

    SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
    gvs[typeOf_e] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>  
    gvs[] >>
    RES_TAC >> gvs[] >| [
    qexistsl_tac [‘r’,‘t_tau tau_bool’] >> gvs[]
    ,
    qexistsl_tac [‘r’,‘t_tau (tau_bit n')’] >> gvs[]
    ]                 
    ,
        
    (* e binop *)    
      gvs[binop_soudness]

    ,
        
    (* e concat *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >> 
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
    gvs[typeOf_e] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>   
    qexistsl_tac [‘n'’,‘n’,‘r'’,‘r’] >> gvs[]


        
    ,
        
    (* e slice *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    gvs[e_tc] >>                        
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[typeOf_e] >>                        
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    SIMP_TAC list_ss [Once e_typ_cases] >> gvs[clause_name_def]>>
    Q.EXISTS_TAC ‘n’ >> gvs[] >> gvs[] >>                       
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC                                         
             
    ,
        
    (* e call *)    

    fs[e_tc_sound_def] >>
    REPEAT STRIP_TAC >>
    PairCases_on ‘t_scopes_tup’ >>
    rename1 `(tslg,tsl)` >>
    PairCases_on ‘T_e’ >> 


    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >>                        
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[f_call_soundness]  

    ,
        
    (* e select *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘b’ >>
    Cases_on ‘t’ >>
    fs[e_tc] >>      
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    SIMP_TAC list_ss [Once e_typ_cases, clause_name_def] >>
    gvs[typeOf_e] >>

    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >> 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>   
    qexistsl_tac [‘t’,‘r’, ‘F’]>> gvs[] >>
    REPEAT STRIP_TAC >>

    gvs[EL_map_true] >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>
                    
    IMP_RES_TAC all_some_imp_EL >>
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    ASSUME_TAC v_tc_correct >> gvs[typeOf_v_tc_def, ELIM_UNCURRY] >>
    RES_TAC >> gvs[] >>
    ASSUME_TAC TC_v_sound >> gvs[v_tc_sound_def]


    ,
        
    (* e struct *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘t’ >>
    fs[e_tc] >>      
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[e_struct_soundness]
    ,

    (* e header *)    
    E_TC_EXTRACT_AND_RENAME >>
    Cases_on ‘t’ >>
    fs[e_tc] >>      
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    gvs[e_struct_soundness]
        
    ,
    (* xel = [] soundness *)
    gvs[xel_tc_sound_def]    
    ,
    (* xel ≠ [] soundness *)    
    gvs[xel_tc_sound_def, xe_tc_sound_def]>>
    REPEAT STRIP_TAC >>                      
    PairCases_on ‘xe’ >>
    gvs[e_tc_sound_def]
    ,
    (* xe  soundness *)    
    gvs[e_tc_sound_def, xe_tc_sound_def]
    ,
    (* el = []  soundness *)    
    gvs[el_tc_sound_def]
    ,
    (* el ≠ []  soundness *)    
    gvs[el_tc_sound_def] >>
    REPEAT STRIP_TAC >>
    gvs[]
  ]

QED        
     




(* ========================================================================== *)
(*                                                                            *)
(*                         l--values  TYPE CHECKER                            *)
(*                                                                            *)
(* ========================================================================== *)




Definition typeOf_lval:                                  
(* variable names *)        
(typeOf_lval (lval_varname (varn_star f')) tslg tsl (ord,f,(d_g,d_b,d_x,d_t)) =  
 (case (t_lookup_funn f' d_g d_b d_x) of
  | SOME (txdl , t ) =>
      (case (find_star_in_globals tslg (varn_star f')) of
       | SOME t' => (case (t = t') of
                     | T => SOME (t_tau t , T)
                     | F => NONE
                    )     
       | NONE => NONE
      )
  | NONE => NONE
 )
)

∧


   
(typeOf_lval (lval_varname varn) tslg tsl (T_e:T_e) =
  case (lookup_tau tsl tslg varn) of
  | SOME t => SOME (t_tau t , T)
  | NONE   => NONE               
) ∧


(* access fld *) 
( typeOf_lval (lval_field lval f) tslg tsl T_e =
  case (typeOf_lval lval tslg tsl T_e) of
  | SOME (t_tau (tau_xtl struct_ty xtl), T) =>
      ( case (find_tau_in_xtl xtl f ) of
        | SOME t => (case (correct_field_type xtl f t) of
                     | T => SOME (t_tau t, T)
                     | F => NONE
                    )
        | NONE => NONE
      )
  | _ => NONE
        
) ∧



(*slice*)
        
(typeOf_lval ( lval_slice lval e' e'') tslg tsl T_e =
 case e' of
 | (e_v (v_bit bitv)) =>
     ( case e'' of              
       | (e_v (v_bit bitv'))  =>
           (let w1 = vec_to_const bitv in
              let w2 = vec_to_const bitv' in
                case (typeOf_lval lval tslg tsl T_e ) of
                | SOME (t_tau (tau_bit  w ) , T) =>
                    ( case (bits_length_check  w w1 w2) of
                      | T => SOME (t_tau (tau_bit (w1 − w2 + 1)),T)
                      | F => NONE 
                    )
                | _ => NONE)
    | _ => NONE)      
| _ => NONE
)
∧

typeOf_lval _ _ _ _ = NONE

                        
End

  

        



                        




Definition lval_tc:

   
(* var name *)   (* TODO why in the example it must be a proper T_e tuples not just T_e*)      
(( lval_tc  (tslg,tsl)  (T_e:T_e) (lval_varname varn) (t_tau tau) ) =
 (
 case (typeOf_e  (e_var varn)  tslg tsl T_e) of
 | SOME (t_tau t, T) => (t = tau)
 | SOME (t_tau t, F) => F
 | SOME (t_string_names_a  t,b) => F                            
 | NONE => F                  
 )
)
 ∧


(* access fld *)

((lval_tc  (tslg,tsl) T_e (lval_field lval f) (t_tau tau))   =
 (
 (case (typeOf_lval (lval_field lval f) tslg tsl T_e) of
 | SOME (t_tau t, T) => (t = tau)
 | SOME (t_tau t, F) => F
 | SOME (t_string_names_a  t,b) => F                            
 | NONE => F             
))) ∧

    
   
(* slice *)

 ((lval_tc  (tslg,tsl) (T_e:T_e) ( lval_slice lval e e') (t_tau tau))   = (
   case (typeOf_lval  ( lval_slice lval e e') tslg tsl T_e) of
 | SOME (t_tau t, T) => (t = tau)
 | SOME (t_tau t, F) => F
 | SOME (t_string_names_a  t,b) => F                            
 | NONE => F            
   )) ∧


   
(lval_tc _ _ _ _  = F)
   
End
           

val lval_tc = save_thm("lval_tc", lval_tc);
val lval_tc_ind = tryfind (uncurry DB.fetch) [("scratch", "lval_tc_ind"),
                                             ("p4_tc", "lval_tc_ind")];
val _ = save_thm("lval_tc_ind", lval_tc_ind);






Theorem typeOf_lval_imp_tc:
∀ lval T_e tslg tsl t.
typeOf_lval lval tslg tsl T_e = SOME (t_tau t,T) ⇒
lval_tc (tslg,tsl) T_e lval (t_tau t)
Proof
Induct >>
REPEAT STRIP_TAC >>

TRY (PairCases_on ‘T_e’ >>        
rename1 `(ord,f,d_g,d_b,d_x,d_t)`) >>
TRY(gvs[lval_tc] ) >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
TRY(gvs[typeOf_lval]) >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

Cases_on ‘v’ >> gvs[typeOf_lval, typeOf_e] >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
QED





Definition lval_tc_sound_def:
lval_tc_sound lval =
∀ T_e t_scopes_tup t. (lval_tc  t_scopes_tup  T_e  lval t ⇒
          lval_typ t_scopes_tup T_e lval t)
End


Theorem TC_lval_sound:
∀ lval . lval_tc_sound lval 
Proof
Induct >> gvs[lval_tc_sound_def] >>
SIMP_TAC list_ss [Once lval_typ_cases, clause_name_def] >>
gvs[lval_tc] >>
REPEAT STRIP_TAC >| [

 E_TC_EXTRACT_AND_RENAME >>
 Cases_on ‘v’ >>
 Cases_on ‘t’ >>
 fs[lval_tc] >>
 fs[Once e_typ_cases, clause_name_def ] >>
 (*var name tc soundness *)
 gvs[typeOf_e] >>      
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
 ,
 E_TC_EXTRACT_AND_RENAME >>
 Cases_on ‘t’ >>
 gvs[lval_tc]
 ,
 E_TC_EXTRACT_AND_RENAME >>
 Cases_on ‘t’ >>       
 fs[lval_tc] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
                      
 fs[clause_name_def ] >>
 (*var name tc soundness *)
 gvs[typeOf_lval] >>      
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 IMP_RES_TAC typeOf_lval_imp_tc >>
 METIS_TAC []      
 ,
        
 E_TC_EXTRACT_AND_RENAME >>        
 Cases_on ‘t’ >>       
 fs[lval_tc] >>
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
                      
 fs[clause_name_def ] >>
 (*var name tc soundness *)
 gvs[typeOf_lval] >>      
 REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
 IMP_RES_TAC typeOf_lval_imp_tc >>
 METIS_TAC []   
 ,
 E_TC_EXTRACT_AND_RENAME >>        
 Cases_on ‘t’ >>       
 fs[lval_tc]
]
QED
   






(* ========================================================================== *)
(*                                                                            *)
(*                         STATEMENTS TYPE CHECKER                            *)
(*                                                                            *)
(* ========================================================================== *)





Definition star_not_in_ts_exec_def:
(star_not_in_ts_exec ([]:t_scope) = T) ∧
(star_not_in_ts_exec (s::sl) =
 case (FST s) of
   | varn_star f => F
   | varn_name x => star_not_in_ts_exec sl   
)                    
End


        
EVAL “ star_not_in_ts_exec [(varn_star f,a,b)]”;
EVAL “ star_not_in_ts_exec [(varn_name f,a,b)]”;



Theorem star_not_in_ts_eq:
∀l . star_not_in_ts l = star_not_in_ts_exec l
Proof
Induct >>
REPEAT STRIP_TAC >>
EQ_TAC >>
gvs[star_not_in_ts_def, star_not_in_ts_exec_def] >>
REPEAT STRIP_TAC >>

PairCases_on ‘h’ >> gvs[] >>
BasicProvers.FULL_CASE_TAC >> gvs[] >| [
    FIRST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘f’])) >>
    BasicProvers.FULL_CASE_TAC >> gvs[]
    ,
    BasicProvers.FULL_CASE_TAC >> gvs[]
  ]
QED




Definition typeOf_el_def:
typeOf_el (el:e list) tslg tsl T_e =
 MAP (\ e . typeOf_e e tslg tsl T_e ) el
End
             








        

Definition ext_is_defined_exec_def:
  ext_is_defined_exec delta_x funn = 
  case funn of
  | funn_name f => (ALOOKUP delta_x f = NONE)
  | funn_inst x => (
    case (ALOOKUP delta_x x) of
      | SOME (a1,ext_MoE) => T
      | NONE => F                       
    )
  | funn_ext x x' =>        
    (case (ALOOKUP delta_x x) of
     | SOME (a1,ext_MoE) =>
         (case (ALOOKUP ext_MoE x') of
          | SOME (txdl, t) => T
          | NONE => F                       
         )
     | NONE => F                       
    )
End    



       

       
Theorem ext_is_defined_eq:
  ∀ funn d_x . ext_is_defined_exec d_x funn ⇔ (ext_is_defined d_x funn)
Proof
gvs[ext_is_defined_def, ext_is_defined_exec_def] >>  
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
                           
PairCases_on ‘x’ >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
gvs[]             
QED
             



Definition ext_not_defined_exec_def:
ext_not_defined_exec delta_g delta_b funn = 
  case funn of
  | funn_name f => (ALOOKUP delta_g f = NONE ∧ ALOOKUP delta_b f = NONE)
  | funn_inst x => (ALOOKUP delta_g x = NONE ∧ ALOOKUP delta_b x = NONE)
  | funn_ext x x' => (ALOOKUP delta_g x = NONE ∧ ALOOKUP delta_b x = NONE)       
End


Theorem ext_not_defined_eq:
∀ d_g d_b funn. ext_not_defined_exec d_g d_b funn = ext_not_defined d_g d_b funn
Proof
gvs[ext_not_defined_exec_def, ext_not_defined_def] >>  
REPEAT STRIP_TAC >>
REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[])
QED




             
 (*Definition stmt_tc:*)       
val stmt_tc = Define `                 

  (*empty stmt*)
  ( stmt_tc t_scopes_tup (T_e:T_e) (P:Prs_n) stmt_empty  = T ) ∧

  (* assignment *)
  ( stmt_tc (tslg,tsl) T_e P (stmt_ass lval_null e)   =
    ( case (typeOf_e e tslg tsl T_e) of
      | SOME (t_tau tau, b) => T
      | _ => F                                      
    )
  )∧




     
  ( stmt_tc (tslg,tsl) T_e P (stmt_ass lval e)   =
    ( case (typeOf_lval lval tslg tsl T_e) of
      | SOME (t_tau tau, T) =>
          ( case (typeOf_e e tslg tsl T_e) of
            | SOME (t_tau tau', b) => (tau = tau')
            | _ => F                                      
          )
      | _ => F                                      
    )
  )∧





     
  (* if statment *)             
  ( stmt_tc (tslg,tsl) T_e P (stmt_cond e stmt1 stmt2)  =
    ( case (typeOf_e e tslg tsl T_e) of
      | SOME (t_tau tau_bool, b) => (stmt_tc (tslg,tsl) T_e P stmt1 ∧ stmt_tc (tslg,tsl) T_e P stmt2)
      | _ => F                                      
  )  )∧


 (*stmt blk*)

  ( stmt_tc (tslg,tsl) T_e P (stmt_block t_scope stmt)  =
    (case (lvalop_not_none  t_scope ∧ star_not_in_ts_exec t_scope ) of
     | T => ( stmt_tc (tslg,[t_scope]++tsl) T_e  P stmt)
    | F => F    
    ) 
  ) ∧
        


 (*stmt seq*)

  ( stmt_tc t_scopes_tup T_e P (stmt_seq stmt1 stmt2)  =
    (stmt_tc t_scopes_tup T_e P stmt1∧
     stmt_tc t_scopes_tup T_e P stmt2)
  ) ∧


 (*stmt trans*)

  ( stmt_tc (tslg,tsl) T_e P (stmt_trans e)  =
    case (typeOf_e e tslg tsl T_e) of
    | SOME (t_string_names_a xl, b) => (literials_in_P_state  xl (P++["accept";"reject"]))
    | _ => F
  ) ∧

 (*stmt return*)

  ( stmt_tc (tslg,tsl) (ord,f,(d_g,d_b,d_x,d_t)) P (stmt_ret e)  =
    case (t_lookup_funn f d_g d_b []) of
    | SOME (txdl,tau) => (
      case (typeOf_e e tslg tsl (ord,f,(d_g,d_b,d_x,d_t))) of
      | SOME (t_tau t, b) => (t=tau)
      | _ => F
      )
    | NONE => F
  ) ∧


 (*stmt apply*)

  ( stmt_tc (tslg,tsl) (ord,f,(d_g,d_b,d_x,d_t)) P (stmt_app tbl el)  =
    case ( ord  (order_elem_t  tbl ) (order_elem_f  f )) of
    | T => ( case (ALOOKUP d_t tbl) of
             | SOME (tl) =>
                 (case (LENGTH tl = LENGTH el) of
                  | T => ( let tl_bl_some = (typeOf_el el tslg tsl (ord,f,(d_g,d_b,d_x,d_t)) ) in
                             let tl' = (MAP (\x. (FST (THE x)) ) tl_bl_some)    in      
                             case (all_some tl_bl_some ∧ map_is_true (MAP (\t. is_tau t) tl') ) of
                             | T => (tl = MAP (\t. rm_t t) tl')
                             | F => F        
                         )
                  | F => F
                  )
             | NONE => F
        )
    | F => F
  )   ∧

 (*stmt ext*)

  ( stmt_tc (tslg,tsl) (ord,f,(d_g,d_b,d_x,d_t)) P (stmt_ext)  =
     (ext_not_defined_exec d_g d_b f ∧ ext_is_defined_exec d_x f)
  ) 
`;
           

val stmt_tc = save_thm("stmt_tc", stmt_tc);
val stmt_tc_ind = tryfind (uncurry DB.fetch) [("scratch", "stmt_tc_ind"),
                                             ("p4_tc", "stmt_tc_ind")];
val _ = save_thm("stmt_tc_ind", stmt_tc_ind);

                         


(* Test


EVAL “stmt_tc (tslg,tsl) T_e P (stmt_cond (e_binop (e_v (v_bool T)) binop_eq (e_v (v_bool T))) stmt_empty stmt_empty)”; (*true*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_trans (e_v(v_str "st")))”; (*true*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_seq (stmt_trans (e_v(v_str "st")))  stmt_empty )”; (*true*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_seq (stmt_trans (e_v(v_str "st")))  (stmt_block [] stmt_empty  ) )”; (*true*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_seq (stmt_trans (e_v(v_str "st")))  (stmt_block [(varn_name "x",a,NONE)] stmt_empty  ) )”; (*true*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_seq (stmt_trans (e_v(v_str "st")))  (stmt_block [(varn_star (funn_name "x"),a,NONE)] stmt_empty  ) )”; (*false*)
EVAL “stmt_tc (tslg,tsl) T_e ["st"] (stmt_seq (stmt_trans (e_v(v_str "st")))  (stmt_block [(varn_star (funn_name "x"),a,SOME f)] stmt_empty  ) )”; (*false*)

val T_efun6 = “ (ord,funn_name "z",([],[("z", ([], (tau_bool)))],[],[])) : T_e”;     
EVAL “stmt_tc ([],[]) ^T_efun6 [] (stmt_ret (e_v v_bot) )”; (*false*)
EVAL “stmt_tc ([],[]) ^T_efun6 [] (stmt_ret (e_v (v_bool T)) )”; (*true*)



     

val ord = 
“ord1 (order_elem_t  "tbl" ) (order_elem_f  (funn_name "z")) ∧
 ord1 (order_elem_t  "tbl" ) (order_elem_f  (funn_name "a")) ∧
 ~ ord1 (order_elem_t  "tbl" ) (order_elem_f  (_))
 ”;

      
val T_efun7 = “ (ord1,funn_name "z",([],[],[],[("tbl",[tau_bool])])) : T_e”;     
EVAL “stmt_tc ([],[]) ^T_efun7 [] (stmt_app "tbl" [])”; (*false*)
EVAL “stmt_tc ([],[]) ^T_efun7 [] (stmt_app "tbl" [e_v (v_bool T)])”; (*true*)
*)



                         


Definition stmt_tc_sound_def:
stmt_tc_sound stmt =
∀ T_e t_scopes_tup P. (stmt_tc  t_scopes_tup  T_e P  stmt ⇒
          stmt_typ t_scopes_tup T_e P stmt  )
End





val STMT_TC_EXTRACT_AND_RENAME =  
    REPEAT STRIP_TAC >>
    PairCases_on ‘t_scopes_tup’ >>
    rename1 `(tslg,tsl)` >>
    PairCases_on ‘T_e’ >>        
    rename1 `(ord,f,(d_g,d_b,d_x,d_t))` 



fun OPEN_STMT_TC_TAC stmt_term =
(Q.PAT_X_ASSUM `stmt_tc (a1,a2) (t1,t2,t3,t4,t5,t6) c ^stmt_term` (fn thm => ASSUME_TAC (SIMP_RULE (srw_ss()) [stmt_tc] thm)))





Theorem TC_stmt_sound:
∀ stmt . stmt_tc_sound stmt
Proof
Induct >>
gvs[stmt_tc_sound_def] >>
REPEAT STRIP_TAC >| [
    (*empty*)
    gvs[Once stmt_typ_cases, clause_name_def]
    ,
        
    (*assignment*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>



    Cases_on ‘l’ >>                       
    OPEN_STMT_TC_TAC “stmt_ass l e”>>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>                                         
    ASSUME_TAC TC_e_sound >> gvs[e_tc_sound_def] >>       
    RES_TAC >>

    IMP_RES_TAC typeOf_lval_imp_tc >> RES_TAC >>                                                     
    ASSUME_TAC TC_lval_sound >> gvs[lval_tc_sound_def] >>


    METIS_TAC[]
    ,
        
    (*if statement*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “stmt_cond e stmt stmt'”>>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>                                         
    ASSUME_TAC TC_e_sound >> gvs[e_tc_sound_def] >>       
    RES_TAC >> METIS_TAC[]
    ,

    (*stmt block*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “(stmt_block l stmt)”>>
    gvs[star_not_in_ts_eq]            
    ,
        
    (*return*)    
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “(stmt_ret e)”>>
    gvs[] >>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>                                         
    ASSUME_TAC TC_e_sound >> gvs[e_tc_sound_def] >>       
    RES_TAC >> METIS_TAC[]
    ,
    (*seq*)
    
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “(stmt_seq stmt stmt')”>>

    gvs[]                 
    ,

    (*transition*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “stmt_trans e”>>
    REPEAT (BasicProvers.FULL_CASE_TAC >> gvs[]) >>

    ASSUME_TAC typeOf_state_name_imp_e_tc >> RES_TAC >>                                         
    ASSUME_TAC TC_e_sound >> gvs[e_tc_sound_def] >>       
    RES_TAC >> METIS_TAC[]
    ,
        
    (*apply*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >> gvs[] >>     
    OPEN_STMT_TC_TAC “stmt_app s l”>>
    REPEAT (BasicProvers.FULL_CASE_TAC >> rfs[]) >>

    Q.EXISTS_TAC ‘ZIP(l,
                      ZIP(x,
                          MAP (λx. (SND (THE x))) (typeOf_el l tslg tsl (ord,f,d_g,d_b,d_x,d_t))
                         ))’ >>


    NTAC 2 (
    EL_TO_INSIDE_TAC >> 
    MAP_DOUB_SIMP_TAC >>
    MAP_QUAD_SIMP_TAC) >>
    
    REPEAT STRIP_TAC >>

    IMP_RES_TAC all_some_imp_EL >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>

    gvs[typeOf_el_def] >>           
    EL_TO_INSIDE_TAC >>

    PairCases_on ‘x’ >> gvs[] >>

    gvs[EL_map_true] >>
    LAST_X_ASSUM (STRIP_ASSUME_TAC o (Q.SPECL [‘i’])) >> gvs[] >>
    EL_TO_INSIDE_TAC >>
    Cases_on ‘x0’ >> gvs[is_tau_def] >>
               
                 
    IMP_RES_TAC typeOf_e_imp_e_tc >> RES_TAC >>                                         
    ASSUME_TAC TC_e_sound >> gvs[e_tc_sound_def, rm_t_def]
    ,

    (*extern*)
    SIMP_TAC list_ss [Once stmt_typ_cases, clause_name_def] >>
    gvs[] >>
          
    STMT_TC_EXTRACT_AND_RENAME >>      
    OPEN_STMT_TC_TAC “stmt_ext”>>
    gvs[ext_is_defined_eq,ext_not_defined_eq]
  ]

QED

                         

(* last thing is to define the order relation *)

Definition order_check_def:              
  order_check l a b =
    ((THE(INDEX_OF a l )) <  (THE(INDEX_OF b l )))   
End
    
     
val _ = export_theory ();
