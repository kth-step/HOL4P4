open HolKernel boolLib Parse bossLib;

val _ = new_theory "p4_arch_cake";

open p4Syntax;
open bitstringSyntax numSyntax pairSyntax;
open p4Theory p4_auxTheory p4_exec_sem_cakeTheory;
open p4_coreTheory;
open p4_v1modelTheory;

(* Note that the below have been manually translated using the dictionary mapping strings to words64
 * created using p4_transform_cakeLib *)

(*********************)
(* Core architecture *)

Definition header_entries2v'_def:
 (header_entries2v' (INL []) = SOME []) /\
 (header_entries2v' (INL (h::t)) =
  case header_entries2v' (INR h) of
  | SOME bl =>
  (case header_entries2v' (INL t) of
   | SOME bl2 => SOME (bl++bl2)
   | NONE => NONE)
  | NONE => NONE
 ) /\
 (header_entries2v' (INR (x:word64, v)) =
  case v of
  | (v'_bit (bl, n)) => SOME bl
  | (v'_struct x_v_l) => header_entries2v' (INL x_v_l)
  | (v'_header validity x_v_l) => header_entries2v' (INL x_v_l)
  | _ => NONE
 )
Termination
WF_REL_TAC `measure ( \ t. case t of | (INL x_v_l) => v'1_size x_v_l | (INR (x,v)) => v'_size v)`
End

Definition get_checksum_incr''_def:
 (get_checksum_incr'' (scope_list:scope_list') ext_data_name =
   (case lookup_lval' scope_list ext_data_name of
    | SOME (v'_bit (bl, n)) =>
     if n MOD 16 = 0 then (v2w16s''' bl) else NONE
    | SOME (v'_header vbit f_list) =>
     (case header_entries2v' (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | SOME (v'_struct f_list) =>
     (case header_entries2v' (INL f_list) of
      | SOME bl => v2w16s'' bl
      | NONE => NONE)
    | _ => NONE)
 )
End

(** Some new architectural functions **)

Definition v_map_to_scope'_def:
 (v_map_to_scope' [] = []) /\
 (v_map_to_scope' (((k, v)::t):(word64, v') alist) =
  ((varn'_name k, (v, NONE:lval' option))::v_map_to_scope' t)
 )
End

Definition scope_to_vmap'_def:
 (scope_to_vmap' [] = SOME []) /\
 (scope_to_vmap' ((vn, (v:v', lval_opt:lval' option))::t) =
  case vn of
   | (varn'_name k) => oCONS ((k, v), scope_to_vmap' t)
   | _ => NONE
 )
End

Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope' v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End

(** Generic implementations **)

Definition verify_gen'_def:
 (verify_gen' ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 2w)) of
  | SOME (v'_bool T) =>
   SOME (ascope, scope_list, status'_returnv v'_bot)
  | SOME (v'_bool F) =>
   (case lookup_lval' scope_list (lval'_varname (varn'_name 1w)) of
    | SOME (v'_bit bitv) =>
     SOME (ascope_update_v_map ascope (0w:word64) (v'_bit bitv), scope_list, status'_trans "reject")
    | _ => NONE)
  | _ => NONE
 )
End

Definition lookup_lval_header'_def:
 (lookup_lval_header' ss header_lval =
  case p4_exec_sem_cake$lookup_lval' ss header_lval of
   | SOME (v'_header valid_bit x_v_l) => SOME (valid_bit, x_v_l)
   | _ => NONE
 )
End

Definition size_in_bits'_def:
 (size_in_bits' (v'_bool b) = SOME 1) /\
 (size_in_bits' (v'_bit (bl, n)) = SOME n) /\
 (size_in_bits' (v'_header valid_bit []) = SOME 0) /\
 (size_in_bits' (v'_struct []) = SOME 0) /\
 (size_in_bits' (v'_header valid_bit (h::t)) =
  case SND h of
  | (v'_bit (bl, num)) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v'_bool _) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | (v'_struct fields) =>
   (case size_in_bits' (v'_header valid_bit t) of
    | SOME num' =>
     (case size_in_bits' (v'_struct fields) of
      | SOME num'' =>
       SOME (num'' + num')
      | NONE => NONE
     )
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits' (v'_struct (h::t)) =
  case SND h of
  | (v'_bit (bl, num)) => 
   (case size_in_bits' (v'_struct t) of
    | SOME num' => SOME (num + num')
    | NONE => NONE
   )
  | (v'_bool _) =>
   (case size_in_bits' (v'_struct t) of
    | SOME num' => SOME (1 + num')
    | NONE => NONE
   )
  | _ => NONE
 ) /\
 (size_in_bits' _ = NONE)
End

Definition set_bool'_def:
 (set_bool' [] = NONE) /\
 (set_bool' packet_in = SOME (v'_bool (HD packet_in), TL packet_in))
End
Definition set_bit'_def:
 (set_bit' n packet_in =
  case oTAKE n packet_in of
  | SOME res => SOME (v'_bit (res, n), DROP n packet_in)
  | NONE => NONE)
End

Definition set_fields'_def:
 (set_fields' []     acc _ = SOME acc) /\
 (set_fields' (h::t) acc packet_in =
  case h of
  | (x:word64, (v'_bool b)) =>
   (case set_bool' packet_in of
    | SOME (res, t') => set_fields' t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v'_bit (bv, l))) =>
   (case set_bit' l packet_in of
    | SOME (res, t') => set_fields' t (acc++[(x, res)]) t'
    | NONE => NONE)
  | (x, (v'_struct x_v_l)) =>
   (case size_in_bits' (v'_struct x_v_l) of
    | SOME n =>
     (case oTAKE_DROP n packet_in of
      | SOME (res, t') =>
       (case set_fields' x_v_l [] res of
        | SOME acc' =>
         set_fields' t (acc++[(x, v'_struct acc')]) t'
        | NONE => NONE)
      | NONE => NONE)
    | NONE => NONE)
  | _ => NONE)
Termination
WF_REL_TAC `measure ( \ (t, acc, packet_in). v'1_size t)`
End

Definition set_header'_def:
 (set_header' x_v_l packet_in =
  case set_fields' x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v'_header T x_v_l')
  | NONE => NONE)
End

Definition set_struct'_def:
 (set_struct' x_v_l packet_in =
  case set_fields' x_v_l [] packet_in of
  | SOME x_v_l' => SOME (v'_struct x_v_l')
  | NONE => NONE)
End

Definition set_v'_def:
 (set_v' (v'_bit (bitv, n)) packet_in =
  case set_bit' n packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v' (v'_bool b)        packet_in =
  case set_bool' packet_in of
  | SOME (res, t') => SOME res
  | NONE => NONE) /\
 (set_v' (v'_struct x_v_l) packet_in = (set_struct' x_v_l packet_in)) /\
 (set_v' (v'_header validity x_v_l) packet_in = (set_header' x_v_l packet_in)) /\
 (set_v' _ packet_in = NONE)
End

Definition packet_in_extract_gen'_def:
 (packet_in_extract_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case p4_exec_sem_cake$lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case lookup_lval_header' scope_list (lval'_varname (varn'_name 4w)) of
    | SOME (valid_bit, x_v_l) =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits' (v'_header valid_bit x_v_l) of
        | SOME size =>
         if size <= LENGTH packet_in_bl
         then
          (case set_header' x_v_l packet_in_bl of
           | SOME header =>
            (case assign' scope_list header (lval'_varname (varn'_name 4w)) of
             | SOME scope_list' =>
              SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP size packet_in_bl))):(core_v_ext, 'b) sum), scope_list', status'_returnv v'_bot)
             | NONE => NONE)
           | NONE => NONE)
         else
          (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet [])):(core_v_ext, 'b) sum)) (0w:word64) (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans "reject")
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition packet_in_lookahead_gen'_def:
 (packet_in_lookahead_gen' ascope_lookup ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case lookup_lval' scope_list (lval'_varname (varn'_name 5w)) of
    | SOME dummy_v =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       (case size_in_bits' dummy_v of
        | SOME size =>
         if size <= LENGTH packet_in_bl
         then
          (case set_v' dummy_v packet_in_bl of
           | SOME v =>
            SOME (ascope, scope_list, status'_returnv v)
           | NONE => NONE)
         else
          (* NOTE: Specific serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
          SOME (ascope_update_v_map ascope (0w:word64) (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans "reject")
        | NONE => NONE)
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition lookup_lval_bit32'_def:
 (lookup_lval_bit32' ss bit32_lval =
  case p4_exec_sem_cake$lookup_lval' ss bit32_lval of
   | SOME (v'_bit (bitv, 32)) => SOME (v2n bitv)
   | _ => NONE
 )
End

Definition packet_in_advance_gen'_def:
 (packet_in_advance_gen' ascope_lookup ascope_update ascope_update_v_map (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case lookup_lval_bit32' scope_list (lval'_varname (varn'_name 6w)) of
    | SOME n_bits =>
     (case lookup_ascope_gen ascope_lookup ascope i of
      | SOME ((INL (core_v_ext_packet packet_in_bl)):(core_v_ext, 'b) sum) =>
       if n_bits <= LENGTH packet_in_bl
       then
        SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (DROP n_bits packet_in_bl))):(core_v_ext, 'b) sum), scope_list, status'_returnv v'_bot)
       else
        (* NOTE: Serialisation of errors is assumed here - "PacketTooShort" -> 1 *)
        SOME (ascope_update_v_map ascope (0w:word64) (v'_bit (fixwidth 32 (n2v 1), 32)), scope_list, status'_trans "reject")
       | _ => NONE)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition flatten_v_l'_def:
 (flatten_v_l' [] = SOME []) /\
 (flatten_v_l' (h::t) =
  case h of
  | v'_struct [] =>
   (case flatten_v_l' t of
    | SOME l => SOME l
    | NONE => NONE)
  | v'_struct (h'::t') =>
   (case flatten_v_l' [SND h'] of
    | SOME l =>
     (case flatten_v_l' ((v'_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v'_header validity [] =>
   (case flatten_v_l' t of
    | SOME l => SOME l
    | NONE => NONE)
  | v'_header validity (h'::t') =>
   (case flatten_v_l' [SND h'] of
    | SOME l =>
     (case flatten_v_l' ((v'_struct t')::t) of
      | SOME l' => SOME (l++l')
      | NONE => NONE)
    | NONE => NONE)
  | v'_bit (bl, n) =>
   (case flatten_v_l' t of
    | SOME l => SOME (bl++l)
    | NONE => NONE)
  | v'_bool b =>
   (case flatten_v_l' t of
    | SOME l => SOME (b::l)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition packet_out_emit_gen'_def:
 (packet_out_emit_gen' (ascope_lookup:'a -> num -> (core_v_ext + 'b) option) ascope_update (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_ext_ref i) =>
   (case lookup_ascope_gen ascope_lookup ascope i of
    | SOME (INL (core_v_ext_packet packet_out_bl)) =>
     (case lookup_lval' scope_list (lval'_varname (varn'_name 7w)) of
      | SOME (v'_header F x_v_l) => SOME (ascope, scope_list, status'_returnv v'_bot)
      | SOME (v'_header T x_v_l) =>
       (case flatten_v_l' (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status'_returnv v'_bot)
        | NONE => NONE)
      | SOME (v'_struct x_v_l) =>
       (case flatten_v_l' (MAP SND x_v_l) of
        | SOME bl =>
         SOME (update_ascope_gen ascope_update ascope i ((INL (core_v_ext_packet (packet_out_bl++bl))):(core_v_ext, 'b) sum), scope_list, status'_returnv v'_bot)
        | NONE => NONE)
      | SOME _ => NONE
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End


(** Implementations **)

Definition header_is_valid'_def:
 (header_is_valid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_header valid_bit x_v_l) =>
   SOME (ascope, scope_list, status'_returnv (v'_bool valid_bit))
  | _ => NONE
 )
End

Definition header_set_valid'_def:
 (header_set_valid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_header valid_bit x_v_l) =>
   (case assign' scope_list (v'_header T x_v_l) (lval'_varname (varn'_name 3w)) of
    | SOME scope_list' =>
     SOME (ascope, scope_list', status'_returnv v'_bot)
    | NONE => NONE)
  | _ => NONE
 )
End

Definition header_set_invalid'_def:
 (header_set_invalid' (ascope:'a, g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
  | SOME (v'_header valid_bit x_v_l) =>
   (case assign' scope_list (v'_header F x_v_l) (lval'_varname (varn'_name 3w)) of
    | SOME scope_list' =>             
     SOME (ascope, scope_list', status'_returnv v'_bot)
    | NONE => NONE)
  | _ => NONE
 )
End


(***********)
(* V1Model *)

val CONTROL_PLANE_API = 0;

Type v1model_ctrl' = “:(word64, (((e_list' -> bool) # num), string # e_list') alist) alist”;

Type v1model_ascope' = “:(num # ((num, v1model_sum_v_ext) alist) # ((word64, v') alist) # v1model_ctrl')”;

Definition v1model_ascope_lookup'_def:
 v1model_ascope_lookup' (ascope:v1model_ascope') ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition v1model_ascope_update'_def:
 v1model_ascope_update' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition v1model_ascope_update_v_map'_def:
 v1model_ascope_update_v_map' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition v1model_ascope_of_conc_state'_def:
 v1model_ascope_of_conc_state' (io1,io2,(ascope:v1model_ascope')) =
  ascope
End

Definition v1model_ascope_read_ext_obj'_def:
 v1model_ascope_read_ext_obj' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') vname =
  case ALOOKUP v_map vname of
  | SOME (v'_ext_ref n) =>
   ALOOKUP ext_obj_map n
  | _ => NONE
End

Definition v1model_postparser'_def:
 v1model_postparser' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  (case ALOOKUP v_map 8w of
   | SOME (v'_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map 9w of
       | SOME (v'_ext_ref i') =>
        (case ALOOKUP v_map 11w of
         | SOME v =>
          let v_map' = p4$AUPDATE v_map (12w, v) in
           (case ALOOKUP v_map 0w of
            | SOME v' =>
             (case assign' [v_map_to_scope' v_map'] v' (lval'_field (lval'_varname (varn'_name 10w)) 36w) of
              | SOME [v_map_scope] =>
               (case scope_to_vmap' v_map_scope of
                | SOME v_map'' =>
                 let v_map''' = p4$AUPDATE v_map'' (7w, v'_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl') = (v1model_ascope_update' (counter, ext_obj_map, v_map''', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (v1model_ascope_update' (counter', ext_obj_map', v_map'''', ctrl') i (INL (core_v_ext_packet [])))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

val (v'_bit_tm, mk_v'_bit, dest_v'_bit, is_v'_bit) =
  syntax_fns1 "p4_exec_sem_cake" "v'_bit";

fun mk_v_bitii' (num, width) =
 let
  val width_tm = term_of_int width
 in
  mk_v'_bit $ mk_pair (mk_fixwidth (width_tm, mk_n2v $ term_of_int num), width_tm)
 end
;

val v1model_standard_metadata_zeroed' =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(“22w:word64”, mk_v_bitii' (0, 9)),
    (“23w:word64”, mk_v_bitii' (0, 9)),
    (“24w:word64”, mk_v_bitii' (0, 9)),
    (“25w:word64”, mk_v_bitii' (0, 32)),
    (“26w:word64”, mk_v_bitii' (0, 32)),
    (“27w:word64”, mk_v_bitii' (0, 32)),
    (“28w:word64”, mk_v_bitii' (0, 19)),
    (“29w:word64”, mk_v_bitii' (0, 32)),
    (“30w:word64”, mk_v_bitii' (0, 19)),
    (“31w:word64”, mk_v_bitii' (0, 48)),
    (“32w:word64”, mk_v_bitii' (0, 48)),
    (“33w:word64”, mk_v_bitii' (0, 16)),
    (“34w:word64”, mk_v_bitii' (0, 16)),
    (“35w:word64”, mk_v_bitii' (0, 1)),
    (“36w:word64”, mk_v_bitii' (0, 32)),
    (“37w:word64”, mk_v_bitii' (0, 3))],
   “:(word64 # v')”);
   
(*
Redblackmap.find (v1model_dict, “"meta"”)
*)
Definition v1model_input_f'_def:
 (v1model_input_f' (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   (* let counter' = ^v1model_init_counter in *)
   let ext_obj_map' = AUPDATE_LIST ext_obj_map [(counter, INL (core_v_ext_packet bl));
                                                (counter+1, INL (core_v_ext_packet []))] in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [(8w, v'_ext_ref counter);
                                    (9w, v'_ext_ref (counter+1));
                                    (10w, v'_struct (p4$AUPDATE (^v1model_standard_metadata_zeroed') (22w, (v'_bit (fixwidth 9 $ n2v p, 9) ) )));
                                    (11w, tau1_uninit_v);
                                    (12w, tau1_uninit_v);
                                    (13w, tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope'))
End

Definition v1model_reduce_nonout'_def:
 (v1model_reduce_nonout' ([], elist:e' list, v_map) =
  SOME []
 ) /\
 (v1model_reduce_nonout' (d::dlist, e::elist, v_map) =
  if is_d_out d
  then oCONS (e, v1model_reduce_nonout' (dlist, elist, v_map))
  else
   (case e of
    | (e'_var (varn'_name x)) =>
     (case ALOOKUP v_map x of
      | SOME v =>
       if is_d_in d
       then oCONS (e'_v v, v1model_reduce_nonout' (dlist, elist, v_map))
       else oCONS (e'_v (init_out_v_cake v), v1model_reduce_nonout' (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout' (_, _, v_map) = NONE)
End

Definition v1model_lookup_obj'_def:
 v1model_lookup_obj' ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v'_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

Definition v1model_output_f'_def:
 v1model_output_f' (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  (case v1model_lookup_obj' ext_obj_map v_map 8w of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case v1model_lookup_obj' ext_obj_map v_map 9w of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map 10w of
       | SOME (v'_struct struct) =>
        (case ALOOKUP struct 23w of
         | SOME (v'_bit (port_bl, n)) =>
          SOME (in_out_list++(if v1model_is_drop_port port_bl then [] else [(bl++bl', v2n port_bl)]), (counter, ext_obj_map, v_map, ctrl))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End  



(* Uses the above and copyin' *)
Definition v1model_copyin_pbl'_def:
 v1model_copyin_pbl' (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
  case v1model_reduce_nonout' (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin' xlist dlist elist' [v_map_to_scope' v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End
(*
(* Uses update_return_frame' *)
Definition copyout_pbl_gen'_def:
 copyout_pbl_gen' xlist dlist g_scope_list v_map =
  let v_map_scope = v_map_to_scope' v_map in
   update_return_frame' xlist dlist [v_map_scope] g_scope_list
End
*)
(* Uses the above *)
Definition v1model_copyout_pbl'_def:
 v1model_copyout_pbl' (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope', dlist, xlist, (status:status')) =
  case copyout_pbl_gen' xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap' v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):v1model_ascope')
    | NONE => NONE)
  | _ => NONE
End

val v1model_apply_table_f'_def =
 if CONTROL_PLANE_API = 0
 then xDefine "v1model_apply_table_f'"
  ‘v1model_apply_table_f' (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      if (MEM mk_lpm mk_list)
      then
       (* Largest priority wins (like for P4Runtime API - should be equivalent to TDI
        * for tables that contain at most one LPM key, with others exact) *)
       SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
      else
       (* Smallest priority wins (like for TDI) *)
       SOME (FST $ FOLDL_MATCH_alt e_l ((x', e_l'), NONE) (1:num) table)
     | NONE => NONE’
 else xDefine "v1model_apply_table_f'"
  ‘v1model_apply_table_f' (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):v1model_ascope') =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      (* Largest priority wins *)
      SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
     | NONE => NONE’;

(** Implementations **)

Definition v1model_packet_in_extract'_def:
 v1model_packet_in_extract' = packet_in_extract_gen' v1model_ascope_lookup' v1model_ascope_update' v1model_ascope_update_v_map'
End

Definition v1model_packet_in_lookahead'_def:
 v1model_packet_in_lookahead' = packet_in_lookahead_gen' v1model_ascope_lookup' v1model_ascope_update_v_map'
End

Definition v1model_packet_in_advance'_def:
 v1model_packet_in_advance' = packet_in_advance_gen' v1model_ascope_lookup' v1model_ascope_update' v1model_ascope_update_v_map'
End

Definition v1model_packet_out_emit'_def:
 v1model_packet_out_emit' = packet_out_emit_gen' v1model_ascope_lookup' v1model_ascope_update'
End

Definition v1model_verify'_def:
 (v1model_verify' (ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  verify_gen' v1model_ascope_update_v_map' (ascope, g_scope_list, scope_list))
End

Definition v1model_mark_to_drop'_def:
 v1model_mark_to_drop' (v1model_ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case assign' scope_list (v'_bit (fixwidth 9 (n2v 511), 9)) (lval'_field (lval'_varname (varn'_name 10w)) 23w) of
   | SOME scope_list' =>
    (case assign' scope_list' (v'_bit (fixwidth 16 (n2v 0), 16)) (lval'_field (lval'_varname (varn'_name 10w)) 33w) of
     | SOME scope_list'' =>
      SOME (v1model_ascope, scope_list'', status'_returnv v'_bot)
     | NONE => NONE)
   | NONE => NONE
End

Definition v1model_assert'_def:
 v1model_assert' (v1model_ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 14w)) of
   | SOME $ v'_bool b =>
    (if b
     then SOME (v1model_ascope, scope_list, status'_returnv v'_bot)
     else NONE)
   | _ => NONE
End

Definition v1model_assume'_def:
 v1model_assume' (v1model_ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 14w)) of
   | SOME $ v'_bool b =>
    (if b
     then SOME (v1model_ascope, scope_list, status'_returnv v'_bot)
     else NONE)
   | _ => NONE
End

Definition v1model_direct_counter_construct'_def:
 v1model_direct_counter_construct' (v1model_ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list:scope_list') =
  SOME (v1model_ascope, scope_list, status'_returnv v'_bot)
End

(* TODO: This is currently a noop - note the resulting data is not accessible from the data plane anyway. Counting should
 * use the apply_table_f instead. *)
Definition v1model_direct_counter_count'_def:
 v1model_direct_counter_count' (v1model_ascope:v1model_ascope', g_scope_list:g_scope_list', scope_list:scope_list') =
  SOME (v1model_ascope, scope_list, status'_returnv v'_bot)
End

Definition v1model_verify_checksum'_def:
 (v1model_verify_checksum' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  (case lookup_lval' scope_list (lval'_varname (varn'_name 2w)) of
   | SOME $ v'_bool b =>
    if b
    then
     (case lookup_lval' scope_list (lval'_varname (varn'_name 16w)) of
      | SOME $ v'_bit (bl, n) =>
       if v2n bl = 6
       then
        (case get_checksum_incr'' scope_list (lval'_varname (varn'_name 7w)) of
         | SOME checksum_incr =>
          (case lookup_lval' scope_list (lval'_varname (varn'_name 15w)) of
           | SOME $ v'_bit (bl', n') =>
            if n' = 16
            then
             (case compute_checksum16 checksum_incr of
              | SOME bl'' =>
               (if bl' = bl''
                then SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status'_returnv v'_bot)
                else
                 (case assign' [v_map_to_scope' v_map] (v'_bit ([T], 1)) (lval'_field (lval'_varname (varn'_name 10w)) 35w) of
                  | SOME [v_map_scope] =>
                   (case scope_to_vmap' v_map_scope of
                    | SOME v_map' =>
                     SOME ((counter, ext_obj_map, v_map', ctrl), scope_list, status'_returnv v'_bot)
                    | NONE => NONE)
                  | _ => NONE))
              | _ => NONE)
            else NONE
           | _ => NONE)
         | NONE => NONE)
       (* TODO: Others not implemented yet *)
       else NONE
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status'_returnv v'_bot)
   | _ => NONE)
 )
End

Definition v1model_update_checksum'_def:
 (v1model_update_checksum' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  (case lookup_lval' scope_list (lval'_varname (varn'_name 2w)) of
   | SOME $ v'_bool b =>
    if b
    then
     (case lookup_lval' scope_list (lval'_varname (varn'_name 16w)) of
      | SOME $ v'_bit (bl, n) =>
       if v2n bl = 6
       then
        (case get_checksum_incr'' scope_list (lval'_varname (varn'_name 7w)) of
         | SOME checksum_incr =>
          (case lookup_lval' scope_list (lval'_varname (varn'_name 15w)) of
           | SOME $ v'_bit (bl', n') =>
            if n' = 16
            then
             (case compute_checksum16 checksum_incr of
              | SOME res =>
               (case assign' scope_list (v'_bit (res, 16)) (lval'_varname (varn'_name 15w)) of
                | SOME scope_list' =>
                 SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status'_returnv v'_bot)
                | NONE => NONE)
              | NONE => NONE)
            else NONE
           | _ => NONE)
         | NONE => NONE)
       (* TODO: Others not implemented yet *)
       else NONE
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status'_returnv v'_bot)
   | _ => NONE)
 )
End

Definition register_construct'_def:
 (register_construct' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 17w)) of
  | SOME (v'_bit (bl, n)) =>
   (case lookup_lval' scope_list (lval'_varname (varn'_name 5w)) of
    | SOME (v'_bit (bl', n')) =>
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_register (v1model_register_construct_inner bl n'))) in
     (case assign' scope_list (v'_ext_ref counter) (lval'_varname (varn'_name 3w)) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status'_returnv v'_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition register_read'_def:
 (register_read' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 19w)) of
  | SOME (v'_bit (bl, n)) =>
   (case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
    | SOME (v'_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (* TODO: HACK, looking up the result variable to get the result width. *)
       (case lookup_lval' scope_list (lval'_varname (varn'_name 18w)) of
        | SOME (v'_bit (bl'', n'')) =>      
         let (bl', n') = v1model_register_read_inner n'' bl array in
           (case assign' scope_list (v'_bit (bl', n')) (lval'_varname (varn'_name 18w)) of
            | SOME scope_list' =>
             SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status'_returnv v'_bot)
            | NONE => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

Definition register_write'_def:
 (register_write' ((counter, ext_obj_map, v_map, ctrl):v1model_ascope', g_scope_list:g_scope_list', scope_list) =
  case lookup_lval' scope_list (lval'_varname (varn'_name 19w)) of
  | SOME (v'_bit (bl, n)) =>
   (case lookup_lval' scope_list (lval'_varname (varn'_name 20w)) of
    | SOME (v'_bit (bl', n')) =>
     (case lookup_lval' scope_list (lval'_varname (varn'_name 3w)) of
      | SOME (v'_ext_ref i) =>
       (case ALOOKUP ext_obj_map i of
        | SOME (INR (v1model_v_ext_register array)) =>
         let array' = v1model_register_write_inner (bl', n') bl array in
         let ext_obj_map' = AUPDATE ext_obj_map (i, INR (v1model_v_ext_register array')) in
          SOME ((counter, ext_obj_map', v_map, ctrl), scope_list, status'_returnv v'_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

val _ = export_theory ();
