open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_exec_arch_v1model";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_retrofit_auxLib p4_exec_semTheory p4_exec_archTheory;
open p4_coreTheory p4_v1modelTheory;

val CONTROL_PLANE_API = 0;

(*
(* TODO: Retrofitted this *)
Definition v1model_input_f_def:
 (v1model_input_f (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((byte_list,p)::t) =>
   (* TODO: Implement persistence between packets when you fully model persistent extern objects *)
   let ext_obj_map' = AUPDATE_LIST [] [(0, INL (core_v_ext_packet byte_list));
                                       (1, INL (core_v_ext_packet []))] in
   let counter' = 2 in
   (* TODO: Currently, no garbage collection in v_map is needed *)
   let v_map' = AUPDATE_LIST v_map [(^(get_id "b"), v_ext_ref 0);
                                    (^(get_id "b_temp"), v_ext_ref 1);
                                    (^(get_id "standard_metadata"), v_struct (p4$AUPDATE (^v1model_standard_metadata_zeroed) (^(get_id "ingress_port"), (v_bit (fixwidth 9 $ n2v p, 9) ) )));
                                    (^(get_id "parsedHdr"), tau1_uninit_v);
                                    (^(get_id "hdr"), tau1_uninit_v);
                                    (^(get_id "meta"), tau2_uninit_v);
                                    (^(get_id "checksum_error"), v_bit ([F], 1))] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope))
End
*)

(* TODO: Regular version hacked to use init_out_v_cake
(* TODO: Uninit? *)
Definition v1model_reduce_nonout_def:
 (v1model_reduce_nonout ([], elist:e list, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout (dlist, elist, v_map))
  else
   (case e of
    | (e_var (varn_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e_v v, v1model_reduce_nonout (dlist, elist, v_map))
       else oCONS (e_v (init_out_v_cake v), v1model_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout (_, _, v_map) = NONE)
End
*)

(* TODO: Regular version hacked to use copyin_exec
(* Uses the above and copyin *)
Definition v1model_copyin_pbl_def:
 v1model_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case v1model_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin_exec xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End
*)
(* TODO: Just forget about registers, for now...
Definition register_construct_def:
 (register_construct ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "size"))) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "targ1"))) of
    | SOME (v_bit (bl', n')) =>
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_register (v1model_register_construct_inner bl n'))) in
     (case assign_exec scope_list (v_ext_ref counter) (lval_varname (varn_name ^(get_id "this"))) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition register_read_def:
 (register_read ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "index"))) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "this"))) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (* TODO: HACK, looking up the result variable to get the result width. *)
       (case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "result"))) of
        | SOME (v_bit (bl'', n'')) =>      
         let (bl', n') = v1model_register_read_inner n'' bl array in
           (case assign_exec scope_list (v_bit (bl', n')) (lval_varname (varn_name ^(get_id "result"))) of
            | SOME scope_list' =>
             SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)
            | NONE => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition register_write_def:
 (register_write ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "index"))) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "value"))) of
    | SOME (v_bit (bl', n')) =>
     (case lookup_lval_exec scope_list (lval_varname (varn_name ^(get_id "this"))) of
      | SOME (v_ext_ref i) =>
       (case ALOOKUP ext_obj_map i of
        | SOME (INR (v1model_v_ext_register array)) =>
         let array' = v1model_register_write_inner (bl', n') bl array in
         let ext_obj_map' = AUPDATE ext_obj_map (i, INR (v1model_v_ext_register array')) in
          SOME ((counter, ext_obj_map', v_map, ctrl), scope_list, status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End
*)
val _ = export_theory ();
