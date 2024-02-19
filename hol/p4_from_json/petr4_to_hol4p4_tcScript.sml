open HolKernel boolLib liteLib simpLib Parse bossLib;
open listSyntax;

open stringTheory listTheory alistTheory ASCIInumbersTheory;
open parse_jsonTheory;
open p4Theory p4_auxTheory;
open petr4_to_hol4p4Theory;
(* For EVAL *)
open ASCIInumbersLib;
open pairSyntax;

val _ = new_theory "petr4_to_hol4p4_tc";

     

(* extract block local info: name of pbl, functions declared inside with their input type and return type*)
Definition extract_fmap_def:
  extract_fmap json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => fmap
 | NONE_msg msg => ([]: (string#stmt#(string#d)list)list)      
End


(* extract block local info: name of pbl, functions declared inside with their input type and return type*)
Definition extract_blftymap_def:
  extract_blftymap json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => blftymap
 | NONE_msg msg => ([]:(string # (funn # p_tau list # p_tau) list) list)       
End



Definition extract_ftymap_def:
  extract_ftymap json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => ftymap
 | NONE_msg msg => []      
End

        
(* extract prog block map contains: name, kind of block, body and signature name and dir *)
Definition extract_pblock_map_def:
  extract_pblock json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => pblock_map
 | NONE_msg msg => ([]:(string # pblock)list)       
End

(* extract tables types *)
Definition extract_dt_def:
  extract_dt json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => ttymap
 | NONE_msg msg => ([]: (string # tau list) list )   
End

Definition extract_arch_pkg_opt_def:
  extract_arch_pkg_opt json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt1, ab_list, ttymap) => arch_pkg_opt1
 | NONE_msg msg => NONE
End

Definition extract_vtymap_def:
extract_vtymap json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => vtymap
 | NONE_msg msg => []
End


Definition extract_ab_list_def:
extract_ab_list json_parse_result arch_pkg_opt =
 case (p4_from_json json_parse_result arch_pkg_opt) of
 | SOME_msg (tyenv, enummap, vtymap, ftymap, blftymap, fmap, bltymap, ptymap, gscope, pblock_map,vab_list, arch_pkg_opt, ab_list, ttymap) => ab_list
 | NONE_msg msg => []
End
        
(* ========================================================================== *)
(*                                                                            *)
(*                         Types here                                         *)
(*                                                                            *)
(* ========================================================================== *)
   

 (* TODO TODO: so much overhead on the let exract function, I should extract only once and just work with it all along *)  

        
Definition remove_duplicates:
  remove_duplicates [] = [] ∧
  remove_duplicates (x::xl) =
  case (MEM x xl) of
  | T => (remove_duplicates xl)
  | F => (x::(remove_duplicates xl))            
End

        
Definition el_blftymap_switch_type_def:
el_blftymap_switch_type (blftymap_el: (string # (funn # p_tau list # p_tau) list)) =
remove_duplicates (MAP (\(f,pt,t). (f,THE (deparameterise_taus pt), deparameterise_tau t))  (SND blftymap_el))
End


Definition blftymap_switch_type_def:
blftymap_switch_type (blftymap: (string # (funn # p_tau list # p_tau) list) list) =
   ZIP ( MAP FST blftymap   ,MAP (\l. el_blftymap_switch_type l)  blftymap)
End        











        
(***************************************)

Definition extract_1st_tri_def:
extract_1st_tri (l: ('a # 'b # 'c) list) =
 MAP (\(a,b,c).a) l
End

Definition extract_2nd_tri_def:
extract_2nd_tri (l: ('a # 'b # 'c) list) =
 MAP (\(a,b,c).b) l
End
                    
Definition extract_3rd_tri_def:
extract_3rd_tri (l: ('a # 'b # 'c) list) =
 MAP (\(a,b,c).c) l
End



Definition extract_bfuncmap_from_pblock_def:
extract_bfuncmap_from_pblock ((pblock_regular pbl_type b_func_map t_scope pars_map tbl_map):pblock) =
b_func_map
End

        
     
        
           
(* exracts local functions signature from each block *)
Definition extract_sig_of_xpblockl_def:
extract_tuples_of_xpblockl (xpblockl: (string # pblock) list) =
let (xl,pbl) = UNZIP xpblockl in
let bfuncmapl = MAP extract_bfuncmap_from_pblock pbl in
    MAP (\(x,sigl). (x,   ZIP(extract_1st_tri sigl ,   extract_3rd_tri sigl)   ) ) (ZIP(xl,bfuncmapl))
End  

        




           
           

Definition keep_funn_name:
 keep_funn_name (ftlt :(funn # tau list # tau option)) = 
 case FST ftlt of
 | funn_name x => SOME (x , SND ftlt)
 | _ => NONE
End 



        
Definition keep_funn_name_in_list_def:
 (keep_funn_name_in_list ([] :(funn # tau list # tau option) list) = [] ) ∧
  (keep_funn_name_in_list (ftlt::ftltl :(funn # tau list # tau option) list) = 
  case (keep_funn_name ftlt) of
  | SOME (x , tl, rt_type) => ((x , tl, rt_type)::keep_funn_name_in_list ftltl)
  | NONE => (keep_funn_name_in_list ftltl))                              
End 




    
Definition init_hit_miss_with_def:
  (init_hit_miss_with  [] [] = []) ∧
  (init_hit_miss_with  [] xdl = [(tau_bool,"from_table",d_in);(tau_bool,"hit",d_in)] ) ∧
(init_hit_miss_with  ((t::tl): tau list) ((xd::xdl): (string#d) list ) = 
case (FST xd) of
| "from_table" => (tau_bool,"from_table",d_in)::init_hit_miss_with (t::tl) xdl
| "hit" =>   (tau_bool,"hit",d_in)::init_hit_miss_with (t::tl) xdl  
| _ => (t,FST xd, SND xd)::init_hit_miss_with tl xdl)
End
    


Definition search_sig_db:
  search_sig_db (ftlt:(x # tau list # tau option) )
  (fxdl : (string # (string # d) list) list) =
    let (x, tl , rt_type) = (FST ftlt, (FST (SND ftlt)), THE (SND (SND ftlt)) ) in    
  case (ALOOKUP fxdl x) of
  | SOME xdl =>
      ( case (LENGTH xdl = LENGTH tl) of
        | T => [(x, ZIP (tl,xdl) , rt_type)]
        | F =>  [(x, init_hit_miss_with  tl xdl , rt_type)]      
      )
   | NONE => [] (* it means either defined in the global envirounment or not even defined at all*)    
End 




Definition search_sigl_db:
  (search_sigl_db [] fxdl = [] ) ∧
  ( search_sigl_db (ftlt::ftltl_filtered:(string # tau list # tau option) list )
                (fxdl : (string # (string # d) list) list) =
      (search_sig_db ftlt fxdl)::(search_sigl_db ftltl_filtered fxdl) )
End   

    
        
Definition mk_sig_db:
  mk_sig_db (fxdl : (string # (string # d) list) list)
         (ftltl :(funn # tau list # tau option) list) = 
  (* filter list and keep only func name*)
     (* then search for the xdl for that*)
     FLAT (search_sigl_db (keep_funn_name_in_list ftltl) fxdl)
End           
        

Definition mk_db_def:
  mk_db (l: ((string # (string # (string # d) list) list) #
                               string # (funn # tau list # tau option) list)
                              list) =
   MAP  (\ (fxdl, x, ftlt).  (x,  mk_sig_db (SND fxdl) ftlt))    l
End





(*                                
        
(* so much info about teh pbl and ext in them, this is to initialize everything*)
Definition mk_db_init_def:
  mk_db_init json_parse_result arch_pkg_opt =
  let pbl_fmaps = (extract_tuples_of_xpblockl (extract_pblock json_parse_result arch_pkg_opt)) in
    let f_tl_rt = remove_duplicates((blftymap_switch_type (extract_blftymap json_parse_result arch_pkg_opt))) in
     (*mk_db*) (ZIP(pbl_fmaps,f_tl_rt))  
End
*)

(* we need to keep track of teh order the arch has the programmable blocks, important to
   a later task (creating the block local copied in scope of pb, the only way to connect them is via the order,
   which entails all the constructs in the output tuple should follow that order )*)

Definition extract_x_from_ab_arch_block_def:
extract_x_from_ab_arch_block ((arch_block_pbl x el ):arch_block) = x
End


Definition extract_pbl_order_def:
extract_pbl_order (ab_list:arch_block list) = 
  MAP (\ arch_block_pbl. extract_x_from_ab_arch_block arch_block_pbl ) ab_list
End




        
Definition reorder_arch_constructs_def:
reorder_arch_constructs [] pbl_sigl = [] ∧
reorder_arch_constructs (x::pbl_order) pbl_sigl  =
case ALOOKUP pbl_sigl x of
| SOME y => (x,y)::(reorder_arch_constructs pbl_order pbl_sigl)
| NONE =>  (reorder_arch_constructs pbl_order pbl_sigl)
End    





        
(* so much info about teh pbl and ext in them, this is to initialize everything*)
Definition mk_db_init_def:
  mk_db_init json_parse_result arch_pkg_opt =
  let pbl_fmaps = (extract_tuples_of_xpblockl (extract_pblock json_parse_result arch_pkg_opt)) in
    let f_tl_rt = remove_duplicates((blftymap_switch_type (extract_blftymap json_parse_result arch_pkg_opt))) in


      let ab_list = extract_ab_list json_parse_result arch_pkg_opt in
        let pbl_order = extract_pbl_order ab_list in
              
            let db = mk_db (ZIP(pbl_fmaps,f_tl_rt)) in
             reorder_arch_constructs pbl_order  db
End



        

(*******************************************)








Definition search_sig_dg:
  search_sig_dg (ftlt:(x # tau list # tau option) list )
                (fxdl : (x # (string # d) list)) =
  let (x, xdl) = (FST fxdl, SND fxdl ) in
     
  case (ALOOKUP ftlt x) of
  | SOME (tl,SOME rt_type) =>
      ( case (LENGTH xdl = LENGTH tl) of
        | T => [(x, ZIP (tl,xdl) ,  rt_type)]
        | F =>  [(x, init_hit_miss_with  tl xdl ,  rt_type)]      
      )
  | NONE => [] (* it means not used at all and it doesn't have any stmt or signature in fmap,
                  so from that i do not know type of it from didrik's output*)    
End 
  

        
Definition ftymap_switch_type_def:
ftymap_switch_type [] = [] ∧
ftymap_switch_type ((f,tl,t)::ftymap) =
case f of
| funn_name x => (x, THE (deparameterise_taus tl), deparameterise_tau t)::ftymap_switch_type ftymap
| funn_inst x => ftymap_switch_type ftymap
| funn_ext x x' => ftymap_switch_type ftymap
End  


Definition mk_dg_from_fmap_def:
mk_dg_from_fmap f_tl_rtl fsxdl = 
  MAP (\(f,stmt,xdl). search_sig_dg  f_tl_rtl (f,xdl) ) fsxdl
End

     
  
Definition mk_dg_init_def:
  mk_dg_init json_parse_result arch_pkg_opt =
    let f_tl_rtl = (ftymap_switch_type (extract_ftymap json_parse_result arch_pkg_opt)) in   (* might contain local functions, it is filtered below *)
    let fsxdl = extract_fmap json_parse_result arch_pkg_opt in
     ( FLAT (mk_dg_from_fmap f_tl_rtl fsxdl) ) : delta_g
End




(*********************)
(* externs *)



(* fetched and fixed from P4_v1modelLib.sml *)        
Definition init_arch_v1model_ext:
  init_arch_v1model_ext =
  [("header",(NONE: Ftau option),
    [("isValid",[(tau_ext,"this",d_in)],tau_bool);
     ("setValid",[(tau_ext,"this",d_inout)],tau_ext);
     ("setInvalid",[(tau_ext,"this",d_inout)],tau_ext)])] :   delta_x
End



Definition init_arch_ebpf_ext:
  init_arch_ebpf_ext =
  [("header",(NONE: Ftau option),
    [("isValid",[(tau_ext,"this",d_in)],tau_bool);
     ("setValid",[(tau_ext,"this",d_inout)],tau_ext);
     ("setInvalid",[(tau_ext,"this",d_inout)],tau_ext)]);
     
   ("", (NONE: Ftau option),
    [("verify", [(tau_bool,"condition",d_in); (tau_bit 32,"err",d_in)], tau_bot)]);

   ("packet_in", (NONE: Ftau option),
    [("length", [(tau_ext,"this",d_in)], tau_bit 32);
     ("extract", [(tau_ext,"this",d_in); (tau_ext,"headerLvalue",d_out)], tau_bot)]);   
  ] :   delta_x
End


        
           
(*



(* fetched and fixed from P4_v1modelLib.sml *)        
Definition init_arch_v1model_ext:
init_arch_v1model_ext =
 [("header",NONE,
   [("isValid",[("this",tau_ext,d_in)]);
    ("setValid",[("this",tau_ext,d_inout)]);
    ("setInvalid",[("this",tau_ext,d_inout)])]);
  ("",NONE,
   [("mark_to_drop",[("standard_metadata", tau_ext, d_inout)]);
    ("verify",["verify",[("condition", tau_bool, d_in); ("err",tau_bit 32, d_in)]]);
    ("verify_checksum", ([("condition", tau_bool, d_in); ("data",  d_in); ("checksum", tau_ext, d_in); ("algo", tau_ext, d_none)]));
    ("update_checksum", ([("condition", tau_bool, d_in); ("data", d_in); ("checksum", tau_ext, d_inout); ("algo", tau_ext, d_none)]))
    ]);
  ("packet_in",NONE,
   [("extract",[("this", tau_ext, d_in); ("headerLvalue", tau_ext, d_out)]);
    ("lookahead",[("this", tau_ext, d_in); ("targ1", tau_ext, d_in)]);
    ("advance",[("this", tau_ext, d_in); ("bits", tau_bit 32, d_in)])]);
  ("packet_out",NONE,
   [("emit",[("this", tau_ext, d_in); ("data", tau_ext, d_in)])]);
  ("register",
   SOME
     ([("this",tau_ext, d_out); ("size", tau_bit n, d_none); ("targ1", tau_ext, d_in)]),
   [("read",[("this", tau_ext, d_in); ("result", tau_ext, d_out); ("index", tau_bit 32, d_in)]);
    ("write",[("this", tau_ext, d_in); ("index", tau_bit 32, d_in); ("value",tau_ext, d_in)])])
  (* ;("Checksum16", SOME ([("this", d_out)]),
   ([("clear", ([("this", d_in)]));
    ("update", ([("this", d_in); ("data", d_in)]));
    ("get", ([("this", d_in)]))])) *)
    ]
End
*)


(* TODO: update teh archs after finishing*)        
Definition arch_extern_gen_def:
arch_extern_gen (arch_opt_tm : arch_t option) =
case arch_opt_tm of
  | SOME (arch_v1model (opty)) => init_arch_v1model_ext
  | SOME (arch_vss (opty)) => init_arch_v1model_ext
  | SOME (arch_ebpf (opty)) =>  init_arch_v1model_ext         
  | NONE =>  init_arch_v1model_ext
End



Definition mk_dx_init_def:
  mk_dx_init arch_pkg_opt =
    (arch_extern_gen (arch_pkg_opt)) : delta_x
End


        





(**************** tables dt **************)



Definition extract_table_from_pblock_def:
extract_table_from_pblock ((pblock_regular pbl_type b_func_map t_scope pars_map tbl_map):pblock) =
MAP FST tbl_map
End


        
(* exracts tables functions signature from each block *)
Definition extract_tables_of_xpblockl_def:
extract_tables_of_xpblockl (xpblockl: (string # pblock) list) =
   MAP (\(pb_name,pb). (pb_name, extract_table_from_pblock  pb)  ) xpblockl
End  

Definition match_tbl_type_def:
  match_tbl_type [] tbl_typel = [] ∧

  match_tbl_type (tbl::tbls) tbl_typel =
  case ALOOKUP tbl_typel tbl of
  | SOME tl => (tbl,tl)::(match_tbl_type tbls tbl_typel)
  | NONE=> match_tbl_type tbls tbl_typel
End

        
Definition mk_dt_def:
mk_dt (pbl_tbl: (string # string list) list)   (tbl_typel: (string#tau list) list) =
   MAP (\(pb_name, tbls). (pb_name , match_tbl_type tbls tbl_typel) ) pbl_tbl 
End
           
                  
Definition mk_dt_init_def:
  mk_dt_init json_parse_result arch_pkg_opt =
  let pbl_tbl = (extract_tables_of_xpblockl (extract_pblock json_parse_result arch_pkg_opt)) in
    let tbl_typel = extract_dt json_parse_result arch_pkg_opt in

      let ab_list = extract_ab_list json_parse_result arch_pkg_opt in
        let pbl_order = extract_pbl_order ab_list in
              
          let (dt:(string#delta_t) list) = mk_dt pbl_tbl tbl_typel  in

              
             reorder_arch_constructs pbl_order  dt
End













        


(****************** make global variable typing map ***)
(* tyenv  - EL 1 list contains the type map of things that can be typedef
   vtymap - EL 3 list has the global variables *)

(* TODO: double check teh results, and add the missing initil values*)


val typeOf_gen_apply_result = “tau_xtl struct_ty_struct
                                       [("hit",tau_bool);
                                        ("miss",tau_bool);
                                        ("action_run",tau_bit 32)]”;



    
   
(* gen_apply_result always exsists in the global scope, it's type is tau bot*)
Definition init_g_tscope_def:
init_g_tscope =
[(varn_name "gen_apply_result", ^typeOf_gen_apply_result,NONE); (* TODO: what is teh difference between this one and the EL 9 res_list v_boy*)
 (varn_name "from_table",tau_bool,NONE);
 (varn_name "hit",tau_bool,NONE)]: t_scope
End




        



(* add variables that are globally defined in p4 programs *)        
Definition mk_g_tscope_with_gvar_def:
 mk_g_tscope_with_gvar l = 
  (MAP (\(var,ty). (var, THE (deparameterise_tau ty) ,(NONE:lval option) )) l ) 
End

(* now add the var stars for all functions defined in the  global functions and externs
   NOTE THAT THIS ALSO DEPENDS ON THE ARCH. !!
   globally defined functions can mbe found in  el 6 : fmap :
   so lazy to do it, just take the new delta_g and extract the names and types from there  *)

Definition  mk_g_tscope_with_global_stars_def:
 mk_g_tscope_with_global_stars l = 
   MAP (\(f,sig,t). varn_star (funn_name f ) , t , (NONE:lval option)) l
End


Definition extract_type_extrn_def:
  extract_type_extrn (ftau_op:Ftau option) =
  case ftau_op of
  | SOME (txdl, t) => SOME t
  | NONE => NONE
End                

        
(* same for inst of ext obj, just take the mk_dx_init *)
Definition  mk_g_tscope_with_ext_inst_stars_def:
 (mk_g_tscope_with_ext_inst_stars ([]:delta_x) = []) ∧
 (mk_g_tscope_with_ext_inst_stars ((inst_name, ftau_op, maps_sig)::l) =
  case ftau_op of
  | SOME (txdl, t) => (varn_star  (funn_inst inst_name) ,t , (NONE:lval option) )::mk_g_tscope_with_ext_inst_stars l
  | NONE => mk_g_tscope_with_ext_inst_stars l
  )                     
End




        
(* same for ext method call *)

Definition extract_type_method_def:
  extract_type_method inst_name (maps_sig : (string # Ftau ) list) =
   MAP (\(x, txdl , t ). (varn_star (funn_ext inst_name x) , t , (NONE:lval option))) maps_sig
End


   
Definition  mk_g_tscope_with_ext_methods_stars_def:
 (mk_g_tscope_with_ext_methods_stars ([]:delta_x) = []) ∧
 (mk_g_tscope_with_ext_methods_stars ((inst_name, ftau_op, maps_sig)::l) =
  ( extract_type_method  inst_name  maps_sig)::mk_g_tscope_with_ext_methods_stars l
  )                      
End



   

Definition mk_gtsc_def:
  mk_gtsc json_parse_result arch_pkg_opt =
  let gvars = (extract_vtymap json_parse_result arch_pkg_opt) in
    let (dg = mk_dg_init json_parse_result arch_pkg_opt) in
      let (dx = mk_dx_init arch_pkg_opt) in
      (
          FLAT (mk_g_tscope_with_ext_methods_stars dx) ++
          mk_g_tscope_with_ext_inst_stars dx ++
          mk_g_tscope_with_global_stars dg ++
          mk_g_tscope_with_gvar gvars ++
          init_g_tscope
      )
End



















        

(****************** make block local variable map (copied in not teh actual locals defined there) variable typing map ***)
(* for each programmable block, we first need to get the copied in types of the programmable blocks:*)
(* to do so, first infer the type variable <H> <M> that you can find
   and based on teh arch definitions, those are most likely headers and structs, and for each archtecure this number differs based on:
   https://github.com/p4lang/p4c/blob/main/p4include/core.p4
   https://github.com/p4lang/p4c/blob/main/backends/ebpf/p4include/ebpf_model.p4
   https://github.com/p4lang/p4c/blob/main/p4include/v1model.p4
   https://github.com/jafingerhut/p4-guide/blob/master/specifying-p4-architectures/vss-try1/very_simple_switch_model.p4
   
*)

(* now carefully match those types with teh programmable blocks based on the type of teh programmable block
   in el 10 of res_list :pblock_map
   i.e. for each arch, the expected type that is static should be defined first
   then for each actual programmable block that we parse, match those with the types variable *)
 

val standard_metadata_t = “ 
(tau_xtl struct_ty_struct
    [("ingress_port",tau_bit 9); ("egress_spec",tau_bit 9);
     ("egress_port",tau_bit 9); ("instance_type",tau_bit 32);
     ("packet_length",tau_bit 32); ("enq_timestamp",tau_bit 32);
     ("enq_qdepth",tau_bit 19); ("deq_timedelta",tau_bit 32);
     ("deq_qdepth",tau_bit 19); ("ingress_global_timestamp",tau_bit 48);
     ("egress_global_timestamp",tau_bit 48); ("mcast_grp",tau_bit 16);
     ("egress_rid",tau_bit 16); ("checksum_error",tau_bit 1);
     ("parser_error",tau_bit 32); ("priority",tau_bit 3)]) : tau”;




(* from: https://github.com/jafingerhut/p4-guide/blob/master/multipackage/example-arch.p4 *)     
val InControl = “ 
tau_xtl struct_ty_struct
    [("inputPort",tau_bit 4)]”;


val OutControl = “ 
tau_xtl struct_ty_struct
    [("outputPort",tau_bit 4)]”;

    
 
Definition arch_ebpf_type_of_pb_copied_args_def:
arch_ebpf_type_of_pb_copied_args arch_pkg_opt =
  case arch_pkg_opt of
  | SOME (arch_ebpf (SOME (ebpf_pkg_ebpfFilter h))) => [[tau_ext;h]; [h;tau_bool]]
  | SOME (arch_v1model (SOME (v1model_pkg_V1Switch h m ))) => [[tau_ext; h; m; ^standard_metadata_t];
                                                               [h;m];
                                                               [h;m;^standard_metadata_t];
                                                               [h;m;^standard_metadata_t];
                                                               [h;m];
                                                               [tau_ext;h]]
  | SOME (arch_vss (SOME (vss_pkg_VSS h ))) =>  [[tau_ext;h]; [h;tau_bit 32; ^InControl ; ^OutControl]; [h;tau_ext]]
  | _ => [[tau_bot]] (* TODO: leave it to debug, remove later and make []*)
End





        
        
(* now to continoue with teh next step is to fetch the arch programmable blocks from el 10*)
Definition match_pb_name_to_its_def:
  match_pb_name_to_its (pb_name:string) (pb:pblock) =
  let b_func_map = extract_bfuncmap_from_pblock pb  in
    case ALOOKUP b_func_map pb_name of
    | SOME (stmt, xdl) => xdl
    | NONE => [("x", d_in)]  (* TODO: leave it to debug, remove later and make []*)     
End

   

Definition extract_pipeline_and_sig_def:
extract_pipeline_and_sig (pbl: (string#pblock) list) =
   MAP (\ (pb_name, pb). (pb_name, match_pb_name_to_its pb_name pb) ) pbl
End


Definition map_sig_to_arch_def:
map_sig_to_arch (pb_sig: (string#(string # d)list)) (arch_based_sig: tau list) =
let (pb_name,xdl) = (FST pb_sig, SND pb_sig)  in
 ( pb_name , MAP2 (\(x,d) t. (varn_name x, t , (NONE:lval option))) xdl arch_based_sig)
    
End

Definition map_sigl_to_archl_def:
map_sigl_to_archl (pbl_sigl: (string#(string # d)list) list ) (arch_based_sigl: tau list list) =
   MAP2 (\pb_sig arch_based_sig . map_sig_to_arch pb_sig arch_based_sig ) pbl_sigl arch_based_sigl
End
        
    
(* do not forget that there is a t_scope for teh programmable block tuple should be taken into account *)


Definition extract_tscope_from_pblock_def:
extract_tscope_from_pblock ((pblock_regular pbl_type b_func_map t_scope pars_map tbl_map):pblock) =
t_scope
End

Definition extract_tscopel_from_pblockl_def:
 extract_tscopel_from_pblockl (pbl: (string#pblock) list) =
   MAP (\ (pb_name, pb). (pb_name, extract_tscope_from_pblock pb) ) pbl
End


   

           
Definition mk_copied_in_blk_local:
  mk_copied_in_blk_local json_parse_result arch_pkg_opt =
  let arch_pkg_opt_selected = extract_arch_pkg_opt json_parse_result arch_pkg_opt in
      
    let pbl  = extract_pblock json_parse_result arch_pkg_opt  in
        let pbl_sigl =  extract_pipeline_and_sig pbl in
          let arch_based_sigl =  arch_ebpf_type_of_pb_copied_args arch_pkg_opt_selected  in

let t_scopel = extract_tscopel_from_pblockl pbl in

              
          (* first use the order in ab_list *)
          let ab_list = extract_ab_list json_parse_result arch_pkg_opt in
            let pbl_order = extract_pbl_order ab_list in


                

              let correct_pbl_order = reorder_arch_constructs pbl_order  pbl_sigl in                
                let correct_t_scopel_order = reorder_arch_constructs pbl_order  t_scopel in

                    
                  let db_copied_in_arch = map_sigl_to_archl correct_pbl_order arch_based_sigl in

                      MAP2 (\(x,y1) (x,y2). (x, y1 ++ y2)  ) db_copied_in_arch correct_t_scopel_order
End







(*********************************************)

(* now create the order of teh functions in the code...
   for each programmable block, you need to find the names of the order of the actions and which one calls teh other one.
   *)
 (* The steps:
    1, within the same programmable block, get the actions and create an order for them
    2, order each action you find with anything in teh global functions or externs.
       use ord action _
    3, Now the global functions, let's just hope that they are nicely ordered and not to do so much work
    4, after finishing collenting those
*)


(*for step 1, TODO DEBUG: the easiest way to do it, is just to take the output of the delta_b, and reverse the order of the function that happens there
 step 2, for each programmable block, each local function or action is ordered with respect to it
 i.e. ∀ f in F_{action or local function} defined before F_programmable block name
 *)

(*pb_name can call and function defined in it*)       
Definition ord_d_def:
ord_d delta = 
  MAP (\(fb_name, sig). (order_elem_f (funn_name fb_name) )) delta
End
                                                                          
Definition ord_dt_def:
  ord_dt (dt: (string#delta_t)list) pb_name =
  case ALOOKUP dt pb_name of
  | SOME l => MAP (\(tname,sig). order_elem_t tname ) l
  | NONE => []
End



                                                        
Definition ord_fxx_helper_def:
ord_fxx_helper fx (fxxl)  = 
  MAP (\(fxx,sig). (order_elem_f (funn_ext fx fxx))) fxxl
End

Definition ord_fxx_def:
ord_fxx (dx: delta_x)  = 
  MAP (\(fx,l).  ord_fxx_helper fx (SND l)  ) dx
End

                                              
                                                                        
Definition ord_fx_def:
ord_fx (dx: delta_x)  = 
  MAP (\(fx,l). (order_elem_f(funn_inst fx))) dx
End
        

 



        

                                                                                        
Definition mk_ord_tup_def:
mk_ord_tup (pb_name:string) (db:delta_b)  (dg: delta_g) (dx: delta_x) (dt: (string#delta_t)list) =
FLAT (ord_fxx dx) ++
ord_fx dx ++
ord_d dg ++
REVERSE(ord_d db) ++
ord_dt dt pb_name ++
[order_elem_f (funn_name pb_name)]
End       
        

(*
val relation_name = "ord55" 
val anoud_list_test = 
“[((order_elem_t  "tbl") , (order_elem_t  "z") );  ((order_elem_t  "tbl") , (order_elem_t  "a"))]”;         
val result_t = ASSUME “abc = ^anoud_list_test”;
(*concl result_t*)
def_order_of_pblocals "ord56" result_t

        
val anoud_list = snd (dest_eq (concl result_t));


    
open pairSyntax;

     
val anoud_semi_ready = map dest_pair (fst (dest_list anoud_list))
     
  
val rel_ord_tm = mk_var (relation_name, “:order_elem -> order_elem -> bool”); 

(* works only for one line*)    
(*val line_tm = “^rel_ord_tm ^(fst (hd anoud_semi_ready)) ^(snd (hd anoud_semi_ready)) = T”; *)

fun line_tm_fun (a,b) = “^rel_ord_tm ^a ^b = T”;

val all_lines_tms = map line_tm_fun anoud_semi_ready;
val last_line_tm = “^rel_ord_tm (_) (_) = F”;

val really_all_lines_tms = all_lines_tms @ [last_line_tm];

(*
val rel_def_tm  = “^line_tm ∧  ^final_line_tm”;
mk_conj (line_tm , final_line_tm)
*)
                                           
val rel_def_tm  = list_mk_conj really_all_lines_tms;
val ord_x = Define ‘^rel_def_tm’
*)





(*
fun def_order_of_pblocals rel_nm tupl_thm =
let
val relation_name = rel_nm
val result_t = tupl_thm                         
val anoud_list = snd (dest_eq (concl result_t));
val anoud_semi_ready = map dest_pair (fst (dest_list anoud_list))
val rel_ord_tm = mk_var (relation_name, “:order_elem -> order_elem -> bool”); 
fun line_tm_fun (a,b) = “^rel_ord_tm ^a ^b = T”;
val all_lines_tms = map line_tm_fun anoud_semi_ready;
val last_line_tm = “^rel_ord_tm (_) (_) = F”;
val really_all_lines_tms = all_lines_tms @ [last_line_tm];                             
val rel_def_tm  = list_mk_conj really_all_lines_tms;
val ord_x = Define ‘^rel_def_tm’
in
  ord_x
end




def_order_of_pblocals "ord56" result_t
*)

                      
(*
val new_ord = EVAL “EVERY (UNCURRY ord1) [((order_elem_t  "tbl" ), (order_elem_f  (funn_name "z")));((order_elem_t  "tbl" ), (order_elem_f  (funn_name "a")))]”;



                 
val ord1_def = Define
‘ord1 (order_elem_t  "tbl" ) (order_elem_f  (funn_name "z")) = T ∧
 ord1 (order_elem_t  "tbl" ) (order_elem_f  (funn_name "a")) = T ∧
 ord1 (_) (_) = F     
’;


val T_efun7a = “ (ord55, funn_name "z",([],[],[],[("tbl",[tau_bool])])) : T_e”;    
EVAL “stmt_tc ([],[]) ^T_efun7a [] (stmt_app "tbl" [e_v (v_bool T)])”; (*true*)

val T_efun7b = “ (ord1,funn_name "g",([],[],[],[("tbl",[tau_bool])])) : T_e”;       
EVAL “stmt_tc ([],[]) ^T_efun7b [] (stmt_app "tbl" [e_v (v_bool T)])”; (*false*)
*)





     

(**********************************)





(*        
Definition tup_to_ord_def:
tup_to_ord (l: (order_elem # order_elem) list) = 
  AND_EL (MAP (\(el1,el2). ORD1 T el1 el2) l)
End


EVAL “ tup_to_ord [(order_elem_t "tbl1", order_elem_t  "tbl2");(order_elem_t  "tbl2", order_elem_t  "tbl3")]”
      

Definition tup_to_ord_def:
tup_to_ord (l: (order_elem # order_elem) list) = 
  AND_EL (MAP (\(el1,el2). ord1 T el1 el2) l)
End
*)


        
          
Definition for_each_pbl_mk_ord_tup_def:
for_each_pbl_mk_ord_tup (xdbl:(string # delta_b) list) (dg: delta_g) (dx: delta_x) (dt: (string#delta_t)list) =
 MAP (\(pb_name, db). (pb_name,  (mk_ord_tup pb_name db dg dx dt))  ) xdbl           
End




   
 


(******************** collect parser states names ***************)







Definition extract_pars_map_from_pblock_def:
extract_pars_map_from_pblock ((pblock_regular pbl_type b_func_map t_scope pars_map tbl_map):pblock) =
case (MAP FST pars_map) of
| [] => []
| l => l ++ ["accept";"reject"]
End

Definition extract_prs_map_of_xpblockl_def:
extract_prs_map_of_xpblockl (xpblockl: (string # pblock) list) =
   MAP (\(pb_name,pb). (pb_name, extract_pars_map_from_pblock  pb)  ) xpblockl
End  





Definition mk_P_init_def:
  mk_P_init json_parse_result arch_pkg_opt =
  let pbl_pmap = (extract_prs_map_of_xpblockl (extract_pblock json_parse_result arch_pkg_opt)) in

      let ab_list = extract_ab_list json_parse_result arch_pkg_opt in
        let pbl_order = extract_pbl_order ab_list in
             
             reorder_arch_constructs pbl_order  pbl_pmap
End




(******************** statements ***************)

(* exatract stmts
for control, one only, for prs exatrct a list of them*)




Definition extract_pars_stmt_from_pblock_def:
extract_pars_stmt_from_pblock ((pblock_regular pbl_type b_func_map t_scope pars_map tbl_map):pblock) =
MAP SND pars_map
End

(* extarct it for all blocks, because it it was a pb control then it will be empty *)        
Definition extract_prs_stmt_from_xpblockl_def:
extract_prs_stmt_from_xpblockl (xpblockl: (string # pblock) list) =
   MAP (\(pb_name,pb). (pb_name, extract_pars_stmt_from_pblock  pb)  ) xpblockl
End 


(* the body to type is teh same one that has the name of pb block, the rest are actions and
   functions defined in the same scope*)
Definition match_pb_name_to_its_stmt_def:
  match_pb_name_to_its_stmt (pb_name:string) (pb:pblock) =
  let b_func_map = extract_bfuncmap_from_pblock pb  in
    case ALOOKUP b_func_map pb_name of
    | SOME (stmt, xdl) => stmt
    | NONE => stmt_empty    
End

                                                                        
Definition extract_stmt_of_xpblockl_def:
extract_stmt_of_xpblockl (xpblockl: (string # pblock) list) =
   MAP (\(pb_name,pb). (pb_name, match_pb_name_to_its_stmt  pb_name pb)  ) xpblockl
End 


Definition merge_stmtl_def:
merge_stmtl (pbl_og_stmtl: (string#stmt)list) (pbl_prs_stmtl:(string#stmt list) list) = 
MAP2 (\(x,stmt1) (y,stmt2) . (x, stmt1::stmt2  ) ) pbl_og_stmtl pbl_prs_stmtl
End
           

Definition mk_stmt_init_def:
  mk_stmt_init json_parse_result arch_pkg_opt =
  let pbl_prs_stmtl = (extract_prs_stmt_from_xpblockl  (extract_pblock json_parse_result arch_pkg_opt)) in
    let pbl_og_stmtl = (extract_stmt_of_xpblockl  (extract_pblock json_parse_result arch_pkg_opt)) in
    let pbl_stmtl = merge_stmtl pbl_og_stmtl pbl_prs_stmtl in
      
        let ab_list = extract_ab_list json_parse_result arch_pkg_opt in
        let pbl_order = extract_pbl_order ab_list in
             
             reorder_arch_constructs pbl_order  pbl_stmtl 
End

                      
        
(* ========================================================================== *)
(*                                                                            *)
(*                  Finally all tuples here                                   *)
(*                                                                            *)
(* ========================================================================== *)









   

(* to print the output and debug, this is the easiest to observe*)

Definition typing_maps_def:
  typing_maps json_parse_result arch_pkg_opt =
  ( mk_dg_init json_parse_result arch_pkg_opt,
    mk_db_init json_parse_result arch_pkg_opt,
    mk_dx_init arch_pkg_opt,
    mk_dt_init json_parse_result arch_pkg_opt,
    mk_gtsc json_parse_result arch_pkg_opt,
    mk_copied_in_blk_local json_parse_result arch_pkg_opt,
    mk_P_init json_parse_result arch_pkg_opt,       
  (for_each_pbl_mk_ord_tup (mk_db_init json_parse_result arch_pkg_opt)
                            (mk_dg_init json_parse_result arch_pkg_opt)
                            (mk_dx_init arch_pkg_opt)
                            (mk_dt_init json_parse_result arch_pkg_opt)),
  mk_stmt_init json_parse_result arch_pkg_opt
  )
End


Definition order_check_def:              
  order_check l a b =
    ((THE(INDEX_OF a l )) <  (THE(INDEX_OF b l )))   
End


        

Definition mk_typing_lists_def:
mk_typing_lists json_parse_result arch_pkg_opt = 
 let (dg, dbl, dx, dtl, gtc, blklstl, pl, ordl, stmtl) =   typing_maps json_parse_result arch_pkg_opt in     
   MAP (\ ((x1,tscl) , (x2,ord) ,  (x3,db) , (x4,dt) , (x5,p) , (x,stmt)).
    (stmt, ([gtc]++[tscl], ([]:t_scope list)), (order_check ord, funn_name x1, (dg,db,dx,dt)): T_e, p)        
       )
        (ZIP(blklstl,ZIP(ordl,ZIP(dbl,ZIP(dtl,ZIP(pl,stmtl))))))  
End


Definition mk_final_tc_maps_helper_def:
mk_final_tc_maps_helper [] = [] ∧
mk_final_tc_maps_helper ((ftm)::ftml) =
 let (stmt,rest) = (FST ftm, SND ftm ) in
   case stmt of
| [] =>  (mk_final_tc_maps_helper ftml)  
| [s] => ((s,rest)::(mk_final_tc_maps_helper ftml))
| (s::sl) => ((s,rest)::(mk_final_tc_maps_helper ((sl,rest)::ftml)))
End

(*
EVAL “mk_final_tc_maps_helper [([s1;s2], a,b);([s3;s4], x,y)]”
EVAL “mk_final_tc_maps_helper [[s1], a]”
EVAL “mk_final_tc_maps_helper [[], a]”
*)


        
      

Definition mk_final_tc_maps_def:
mk_final_tc_maps json_parse_result arch_pkg_opt =
let ftml = mk_typing_lists json_parse_result arch_pkg_opt in
 mk_final_tc_maps_helper ftml
End



        

val _ = export_theory ();



(*
val typing_lists = ``[(stmt_seq stmt_empty (stmt_trans (e_v (v_str "start"))),
  ([[(varn_star (funn_ext "header" "isValid"),tau_bool,NONE);
     (varn_star (funn_ext "header" "setValid"),tau_ext,NONE);
     (varn_star (funn_ext "header" "setInvalid"),tau_ext,NONE);
     (varn_star (funn_name "NoAction"),tau_bot,NONE);
     (varn_star (funn_name "do_function1"),tau_bit 16,NONE);
     (varn_star (funn_name "do_function2"),tau_bit 16,NONE);
     (varn_name "gen_apply_result",
      tau_xtl struct_ty_struct
        [("hit",tau_bool); ("miss",tau_bool); ("action_run",tau_bit 32)],NONE);
     (varn_name "from_table",tau_bool,NONE); (varn_name "hit",tau_bool,NONE)];
    [(varn_name "p",tau_ext,NONE);
     (varn_name "headers",tau_xtl struct_ty_struct [],NONE)]],[]),
  (order_check
     [order_elem_f (funn_ext "header" "isValid");
      order_elem_f (funn_ext "header" "setValid");
      order_elem_f (funn_ext "header" "setInvalid");
      order_elem_f (funn_inst "header"); order_elem_f (funn_name "NoAction");
      order_elem_f (funn_name "do_function1");
      order_elem_f (funn_name "do_function2");
      order_elem_f (funn_name "prs")],funn_name "prs",
   [("NoAction",[(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in)],tau_bot);
    ("do_function1",[(tau_bit 48,"val",d_inout)],tau_bit 16);
    ("do_function2",[(tau_bit 48,"val",d_inout)],tau_bit 16)],[],
   [("header",NONE,
     [("isValid",[(tau_ext,"this",d_in)],tau_bool);
      ("setValid",[(tau_ext,"this",d_inout)],tau_ext);
      ("setInvalid",[(tau_ext,"this",d_inout)],tau_ext)])],[]),
  ["start"; "accept"; "reject"]);
 (stmt_seq stmt_empty (stmt_trans (e_v (v_str "accept"))),
  ([[(varn_star (funn_ext "header" "isValid"),tau_bool,NONE);
     (varn_star (funn_ext "header" "setValid"),tau_ext,NONE);
     (varn_star (funn_ext "header" "setInvalid"),tau_ext,NONE);
     (varn_star (funn_name "NoAction"),tau_bot,NONE);
     (varn_star (funn_name "do_function1"),tau_bit 16,NONE);
     (varn_star (funn_name "do_function2"),tau_bit 16,NONE);
     (varn_name "gen_apply_result",
      tau_xtl struct_ty_struct
        [("hit",tau_bool); ("miss",tau_bool); ("action_run",tau_bit 32)],NONE);
     (varn_name "from_table",tau_bool,NONE); (varn_name "hit",tau_bool,NONE)];
    [(varn_name "p",tau_ext,NONE);
     (varn_name "headers",tau_xtl struct_ty_struct [],NONE)]],[]),
  (order_check
     [order_elem_f (funn_ext "header" "isValid");
      order_elem_f (funn_ext "header" "setValid");
      order_elem_f (funn_ext "header" "setInvalid");
      order_elem_f (funn_inst "header"); order_elem_f (funn_name "NoAction");
      order_elem_f (funn_name "do_function1");
      order_elem_f (funn_name "do_function2");
      order_elem_f (funn_name "prs")],funn_name "prs",
   [("NoAction",[(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in)],tau_bot);
    ("do_function1",[(tau_bit 48,"val",d_inout)],tau_bit 16);
    ("do_function2",[(tau_bit 48,"val",d_inout)],tau_bit 16)],[],
   [("header",NONE,
     [("isValid",[(tau_ext,"this",d_in)],tau_bool);
      ("setValid",[(tau_ext,"this",d_inout)],tau_ext);
      ("setInvalid",[(tau_ext,"this",d_inout)],tau_ext)])],[]),
  ["start"; "accept"; "reject"]);
 (stmt_seq stmt_empty
    (stmt_block [(varn_name "x",tau_bool,NONE)]
       (stmt_seq (stmt_ass (lval_varname (varn_name "x")) (e_v (v_bool T)))
          (stmt_ass lval_null
             (e_call (funn_name "Reject2")
                [e_v (v_bool F); e_v (v_bool ARB); e_var (varn_name "x")])))),
  ([[(varn_star (funn_ext "header" "isValid"),tau_bool,NONE);
     (varn_star (funn_ext "header" "setValid"),tau_ext,NONE);
     (varn_star (funn_ext "header" "setInvalid"),tau_ext,NONE);
     (varn_star (funn_name "NoAction"),tau_bot,NONE);
     (varn_star (funn_name "do_function1"),tau_bit 16,NONE);
     (varn_star (funn_name "do_function2"),tau_bit 16,NONE);
     (varn_name "gen_apply_result",
      tau_xtl struct_ty_struct
        [("hit",tau_bool); ("miss",tau_bool); ("action_run",tau_bit 32)],NONE);
     (varn_name "from_table",tau_bool,NONE); (varn_name "hit",tau_bool,NONE)];
    [(varn_name "headers",tau_xtl struct_ty_struct [],NONE);
     (varn_name "pass",tau_bool,NONE)]],[]),
  (order_check
     [order_elem_f (funn_ext "header" "isValid");
      order_elem_f (funn_ext "header" "setValid");
      order_elem_f (funn_ext "header" "setInvalid");
      order_elem_f (funn_inst "header"); order_elem_f (funn_name "NoAction");
      order_elem_f (funn_name "do_function1");
      order_elem_f (funn_name "do_function2");
      order_elem_f (funn_name "Reject1"); order_elem_f (funn_name "Reject2");
      order_elem_f (funn_name "Reject3"); order_elem_f (funn_name "pipe")],
   funn_name "pipe",
   [("NoAction",[(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in)],tau_bot);
    ("do_function1",[(tau_bit 48,"val",d_inout)],tau_bit 16);
    ("do_function2",[(tau_bit 48,"val",d_inout)],tau_bit 16)],
   [("Reject3",
     [(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in);
      (tau_bool,"rej",d_none)],tau_bot);
    ("Reject2",
     [(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in);
      (tau_bool,"rej",d_none)],tau_bot);
    ("Reject1",
     [(tau_bool,"from_table",d_in); (tau_bool,"hit",d_in);
      (tau_bool,"rej",d_none)],tau_bot)],
   [("header",NONE,
     [("isValid",[(tau_ext,"this",d_in)],tau_bool);
      ("setValid",[(tau_ext,"this",d_inout)],tau_ext);
      ("setInvalid",[(tau_ext,"this",d_inout)],tau_ext)])],[]),[])]``;
 
    

fun arrange_tup_el ([t1, t2, t3, t4, t5, t6, t7, t8, t9, t10]:term list) = 
 ((t2, t3), list_mk_pair [t4, t5, t6, t7, t8, t9],t10, t1);

fun line_tm_fun ((t1, t2), T_e , p, stmt) =
 “stmt_tc (^t1, ^t2) ^T_e ^p ^stmt ”;



fun gen_tc_of_prog typing_lists =
let 
val l1  = map (inst [“:'a ”|-> “:lval”,
                     “:'b” |-> “:(varn # tau # lval option) list”,
                     “:'c ”|-> “:((tau # string # d) list # tau)”,
                     “:'d ”|-> “:(string # tau list)”]) (fst (dest_list typing_lists));
val l2 = map strip_pair l1; 
val l3 =  map arrange_tup_el l2;
in
map line_tm_fun l3
end
*)



