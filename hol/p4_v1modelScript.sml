open HolKernel boolLib Parse bossLib ottLib;

open p4Theory p4Syntax p4_auxTheory p4_coreTheory p4_coreLib;

val _ = new_theory "p4_v1model";

(* Useful documentation and reference links:
   https://github.com/p4lang/behavioral-model/blob/main/docs/simple_switch.md
   https://github.com/p4lang/behavioral-model/blob/main/targets/simple_switch/simple_switch.cpp
*)

(* NOTE ON CONTROL PLANE APIS
 * By default, this model is set up to work with TDI-style tables, where priority annotation
 * leads to smallest priority winning out in case of multiple matches (for ternary match kinds).
 * Change this by setting the value of CONTROL_PLANE_API to correspond with the control plane
 * API you want to model.
 *
 * TDI (default): 0
 * P4Runtime API: 1
 *
 * *)

val CONTROL_PLANE_API = 0;

(* TODO: v1model uses a checksum in the verify_checksum and update_checksum externs *)
Datatype:
 v1model_v_ext =
   v1model_v_ext_ipv4_checksum (word16 list)
 | v1model_v_ext_counter
 | v1model_v_ext_direct_counter
 | v1model_v_ext_meter
 | v1model_v_ext_direct_meter
 | v1model_v_ext_register ((bool list # num) list)
 (* From IPSec example *)
 | v1model_v_ext_ipsec_crypt
End
val _ = type_abbrev("v1model_sum_v_ext", ``:(core_v_ext, v1model_v_ext) sum``);

(* The control plane representation:

   (* the table name *)
   (string, 
     (* the key of a table entry: first element is a predicate for matching, second is priority *)
    ((e_list -> bool, num),
     (* the action of a table entry: string is action name, e_list is arguments *)
     string # e_list) alist) alist``)
*)
val _ = type_abbrev("v1model_ctrl", ``:(string, (((e_list -> bool) # num), string # e_list) alist) alist``);

(* The architectural state type of the V1Model architecture model *)
val _ = type_abbrev("v1model_ascope", ``:(num # ((num, v1model_sum_v_ext) alist) # ((string, v) alist) # v1model_ctrl)``);

(**********************************************************)
(*               SPECIALISED CORE METHODS                 *)
(**********************************************************)

Definition v1model_ascope_lookup_def:
 v1model_ascope_lookup (ascope:v1model_ascope) ext_ref = 
  let ext_obj_map = FST $ SND ascope in
   ALOOKUP ext_obj_map ext_ref
End

Definition v1model_ascope_update_def:
 v1model_ascope_update ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) ext_ref v_ext =
   (counter, AUPDATE ext_obj_map (ext_ref, v_ext), v_map, ctrl)
End

Definition v1model_ascope_update_v_map_def:
 v1model_ascope_update_v_map ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) str v =
   (counter, ext_obj_map, AUPDATE v_map (str, v), ctrl)
End

Definition v1model_packet_in_extract_def:
 v1model_packet_in_extract = packet_in_extract_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_in_lookahead_def:
 v1model_packet_in_lookahead = packet_in_lookahead_gen v1model_ascope_lookup v1model_ascope_update_v_map
End

Definition v1model_packet_in_advance_def:
 v1model_packet_in_advance = packet_in_advance_gen v1model_ascope_lookup v1model_ascope_update v1model_ascope_update_v_map
End

Definition v1model_packet_out_emit_def:
 v1model_packet_out_emit = packet_out_emit_gen v1model_ascope_lookup v1model_ascope_update
End

Definition v1model_verify_def:
 (v1model_verify (ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  verify_gen v1model_ascope_update_v_map (ascope, g_scope_list, scope_list))
End

(**********************************************)
(*             HELPER FUNCTIONS               *)
(**********************************************)

Definition v1model_ascope_read_ext_obj_def:
 v1model_ascope_read_ext_obj ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) vname =
  case ALOOKUP v_map vname of
  | SOME (v_ext_ref n) =>
   ALOOKUP ext_obj_map n
  | _ => NONE
End

Definition v1model_ascope_of_conc_state_def:
 v1model_ascope_of_conc_state (io1,io2,(ascope:v1model_ascope)) =
  ascope
End
    
(**********************************************************)
(*             EXTERN OBJECTS AND FUNCTIONS               *)
(**********************************************************)

(* NOTE: 511 is the default drop port *)
Definition v1model_mark_to_drop_def:
 v1model_mark_to_drop (v1model_ascope:v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case assign scope_list (v_bit (fixwidth 9 (n2v 511), 9)) (lval_field (lval_varname (varn_name "standard_metadata")) "egress_spec") of
   | SOME scope_list' =>
    (case assign scope_list' (v_bit (fixwidth 16 (n2v 0), 16)) (lval_field (lval_varname (varn_name "standard_metadata")) "mcast_grp") of
     | SOME scope_list'' =>
      SOME (v1model_ascope, scope_list'', status_returnv v_bot)
     | NONE => NONE)
   | NONE => NONE
End

(**********************)
(* Checksum methods   *)
(**********************)

Definition reflect16'_def:
 (reflect16' data reflection 0 = reflection) /\
 (reflect16' data reflection (SUC bit) =
  if ~((word_and data (1w:word16)) = (0w:word16))
  then reflect16' (word_lsl data 1) (word_or reflection (word_lsl (1w:word16) bit)) bit
  else reflect16' (word_lsl data 1) reflection bit)
End
Definition reflect16_def:
 (reflect16 data nBits = reflect16' data (0w:word16) nBits)
End

(* CRC16:

https://github.com/p4lang/behavioral-model/blob/5f1c590c7bdb32ababb6d6fe18977cf13ae3b043/src/bm_sim/calculations.cpp

*)
(* https://barrgroup.com/blog/crc-series-part-3-crc-implementation-code-cc *)

val table_crc16 = 
 “[0w; 32773w; 32783w; 10w; 32795w; 30w; 20w; 32785w; 32819w; 54w; 60w;
   32825w; 40w; 32813w; 32807w; 34w; 32867w; 102w; 108w; 32873w; 120w;
   32893w; 32887w; 114w; 80w; 32853w; 32863w; 90w; 32843w; 78w; 68w;
   32833w; 32963w; 198w; 204w; 32969w; 216w; 32989w; 32983w; 210w; 240w;
   33013w; 33023w; 250w; 33003w; 238w; 228w; 32993w; 160w; 32933w; 32943w;
   170w; 32955w; 190w; 180w; 32945w; 32915w; 150w; 156w; 32921w; 136w;
   32909w; 32903w; 130w; 33155w; 390w; 396w; 33161w; 408w; 33181w; 33175w;
   402w; 432w; 33205w; 33215w; 442w; 33195w; 430w; 420w; 33185w; 480w;
   33253w; 33263w; 490w; 33275w; 510w; 500w; 33265w; 33235w; 470w; 476w;
   33241w; 456w; 33229w; 33223w; 450w; 320w; 33093w; 33103w; 330w; 33115w;
   350w; 340w; 33105w; 33139w; 374w; 380w; 33145w; 360w; 33133w; 33127w;
   354w; 33059w; 294w; 300w; 33065w; 312w; 33085w; 33079w; 306w; 272w;
   33045w; 33055w; 282w; 33035w; 270w; 260w; 33025w; 33539w; 774w; 780w;
   33545w; 792w; 33565w; 33559w; 786w; 816w; 33589w; 33599w; 826w; 33579w;
   814w; 804w; 33569w; 864w; 33637w; 33647w; 874w; 33659w; 894w; 884w;
   33649w; 33619w; 854w; 860w; 33625w; 840w; 33613w; 33607w; 834w; 960w;
   33733w; 33743w; 970w; 33755w; 990w; 980w; 33745w; 33779w; 1014w; 1020w;
   33785w; 1000w; 33773w; 33767w; 994w; 33699w; 934w; 940w; 33705w; 952w;
   33725w; 33719w; 946w; 912w; 33685w; 33695w; 922w; 33675w; 910w; 900w;
   33665w; 640w; 33413w; 33423w; 650w; 33435w; 670w; 660w; 33425w; 33459w;
   694w; 700w; 33465w; 680w; 33453w; 33447w; 674w; 33507w; 742w; 748w;
   33513w; 760w; 33533w; 33527w; 754w; 720w; 33493w; 33503w; 730w; 33483w;
   718w; 708w; 33473w; 33347w; 582w; 588w; 33353w; 600w; 33373w; 33367w;
   594w; 624w; 33397w; 33407w; 634w; 33387w; 622w; 612w; 33377w; 544w;
   33317w; 33327w; 554w; 33339w; 574w; 564w; 33329w; 33299w; 534w; 540w;
   33305w; 520w; 33293w; 33287w; 514w]:word16 list”;

Definition compute_crc16'_def:
 (compute_crc16' buf 0 (remainder:word16) = remainder) /\
 (compute_crc16' buf (SUC byte) remainder =
  let data = w2n $ word_and (reflect16 (EL byte buf) 8) (word_lsr remainder 8) in
  let remainder' = word_and (EL data ^table_crc16) (word_lsl remainder 8) in
  compute_crc16' buf byte remainder')
End

(* This uses a word8 list to imitate v1model, even though it immediately gets
 * cast to a word16 *)
Definition compute_crc16_def:
 compute_crc16 (buf:word8 list) =
  (* These constants chosen for CRC-16, replace for other algorithms *)
  let remainder = (0w:word16) in
  let final_xor_value = (0w:word16) in
  let remainder' = compute_crc16' (MAP w2w buf) (LENGTH buf) remainder in
  word_and (reflect16 remainder' 16) final_xor_value
End


(*******************)
(* verify_checksum *)

Definition v1model_verify_checksum_def:
 (v1model_verify_checksum ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  (case lookup_lval scope_list (lval_varname (varn_name "condition")) of
   | SOME $ v_bool b =>
    if b
    then
     (case lookup_lval scope_list (lval_varname (varn_name "algo")) of
      | SOME $ v_bit (bl, n) =>
       if v2n bl = 6
       then
        (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
         | SOME checksum_incr =>
          (case lookup_lval scope_list (lval_varname (varn_name "checksum")) of
           | SOME $ v_bit (bl', n') =>
            if n' = 16
            then
             (if (v_bit (bl', n')) = (v_bit $ w16 $ compute_checksum16 checksum_incr)
              then SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status_returnv v_bot)
              else
               (case assign [v_map_to_scope v_map] (v_bit ([T], 1)) (lval_field (lval_varname (varn_name "standard_metadata")) "checksum_error") of
                | SOME [v_map_scope] =>
                 (case scope_to_vmap v_map_scope of
                  | SOME v_map' =>
                   SOME ((counter, ext_obj_map, v_map', ctrl), scope_list, status_returnv v_bot)
                  | NONE => NONE)
                | _ => NONE))
            else NONE
           | _ => NONE)
         | NONE => NONE)
       (* TODO: Others not implemented yet *)
       else NONE
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status_returnv v_bot)
   | _ => NONE)
 )
End

(*************************)
(* update_checksum *)

Definition v1model_update_checksum_def:
 (v1model_update_checksum ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  (case lookup_lval scope_list (lval_varname (varn_name "condition")) of
   | SOME $ v_bool b =>
    if b
    then
     (case lookup_lval scope_list (lval_varname (varn_name "algo")) of
      | SOME $ v_bit (bl, n) =>
       if v2n bl = 6
       then
        (case get_checksum_incr scope_list (lval_varname (varn_name "data")) of
         | SOME checksum_incr =>
          (case lookup_lval scope_list (lval_varname (varn_name "checksum")) of
           | SOME $ v_bit (bl', n') =>
            if n' = 16
            then
             (case assign scope_list (v_bit $ w16 $ compute_checksum16 checksum_incr) (lval_varname (varn_name "checksum")) of
              | SOME scope_list' =>
               SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)             | NONE => NONE)
            else NONE
           | _ => NONE)
         | NONE => NONE)
       (* TODO: Others not implemented yet *)
       else NONE
      | _ => NONE)
    else SOME ((counter, ext_obj_map, v_map, ctrl), scope_list, status_returnv v_bot)
   | _ => NONE)
 )
End

(**************)
(* Register   *)
(**************)

Definition replicate_arb_def:
 replicate_arb length width =
  REPLICATE length ((REPLICATE width (ARB:bool)), width)
End

Definition v1model_register_construct_inner_def:
 (v1model_register_construct_inner length_bl width =
  replicate_arb (v2n length_bl) width
 )
End

Definition register_construct_def:
 (register_construct ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "size")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "targ1")) of
    | SOME (v_bit (bl', n')) =>
     let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_register (v1model_register_construct_inner bl n'))) in
     (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
      | SOME scope_list' =>
       SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
      | NONE => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* OLD:
Definition register_read_def:
 (register_read ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (case oEL (v2n bl) array of
        | SOME (bl', n') =>
         (case assign scope_list (v_bit (bl', n')) (lval_varname (varn_name "result")) of
          | SOME scope_list' =>
           SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)
          | NONE => NONE)
        | NONE => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End
*)

(* Simply replaces the oEL of a v2n index *)
Definition v1model_register_read_inner_def:
 (v1model_register_read_inner n'' array_index_v array =
  case oEL (v2n array_index_v) array of
  | SOME res => res
  | NONE => (REPLICATE n'' (ARB:bool), n'')
 )
End

(* Note that register_read always has a result, according to v1model.p4. *)
Definition register_read_def:
 (register_read ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "this")) of
    | SOME (v_ext_ref i) =>
     (case ALOOKUP ext_obj_map i of
      | SOME (INR (v1model_v_ext_register array)) =>
       (* TODO: HACK, looking up the result variable to get the result width. *)
       (case lookup_lval scope_list (lval_varname (varn_name "result")) of
        | SOME (v_bit (bl'', n'')) =>      
         let (bl', n') = v1model_register_read_inner n'' bl array in
           (case assign scope_list (v_bit (bl', n')) (lval_varname (varn_name "result")) of
            | SOME scope_list' =>
             SOME ((counter, ext_obj_map, v_map, ctrl), scope_list', status_returnv v_bot)
            | NONE => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End
        
Definition v1model_register_write_inner_def:
 (v1model_register_write_inner update array_index_v (array:(bool list # num) list) =
  LUPDATE update (v2n array_index_v) array
 )
End
        
Definition register_write_def:
 (register_write ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "index")) of
  | SOME (v_bit (bl, n)) =>
   (case lookup_lval scope_list (lval_varname (varn_name "value")) of
    | SOME (v_bit (bl', n')) =>
     (case lookup_lval scope_list (lval_varname (varn_name "this")) of
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

(*******************)
(* IPSec methods   *)
(*******************)

(* TODO: Initialises nothing, for now... *)
Definition ipsec_crypt_construct_def:
 (ipsec_crypt_construct ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
   let ext_obj_map' = AUPDATE ext_obj_map (counter, INR (v1model_v_ext_ipsec_crypt)) in
   (case assign scope_list (v_ext_ref counter) (lval_varname (varn_name "this")) of
    | SOME scope_list' =>
     SOME ((counter + 1, ext_obj_map', v_map, ctrl), scope_list', status_returnv v_bot)
    | NONE => NONE)
 )
End

Definition set_validity_def:
  (set_validity validity (v_struct ((x,v)::t)) = v_struct (((x, set_validity validity v))::(MAP (\(x',v'). (x', set_validity validity v')) t))) /\
  (set_validity validity (v_struct []) = v_struct []) /\
  (set_validity validity (v_header boolv ((x,v)::t)) =
    v_header validity (( (x, set_validity validity v) )::(MAP (\(x',v'). (x', set_validity validity v')) t))) /\
  (set_validity validity (v_header boolv []) = v_header validity []) /\
  (set_validity _ (v:v) = v)
Termination
 WF_REL_TAC `measure (\ (validity,v). v_size v)` >>
 fs [v_size_def] >>
 REPEAT STRIP_TAC >>
 `v_size v' < v1_size t` suffices_by (
  fs []
 ) >>
 METIS_TAC [v1_size_mem]
End

(* TODO: This is currently a placeholder implementation.
 * For symbolic execution. This should be rewritten by adding an assumption that introduces fresh free variables *)
Definition ipsec_crypt_decrypt_aes_ctr_def:
 (ipsec_crypt_decrypt_aes_ctr ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case lookup_lval scope_list (lval_varname (varn_name "standard_metadata")) of
      | SOME standard_metadata =>
       (case assign scope_list (set_validity T $ init_out_v ipv4_header) (lval_varname (varn_name "ipv4")) of
        | SOME scope_list' =>
         (case assign scope_list' (set_validity T $ init_out_v esp_header) (lval_varname (varn_name "esp")) of
          | SOME scope_list'' =>
           (case assign scope_list'' (set_validity T $ init_out_v standard_metadata) (lval_varname (varn_name "standard_metadata")) of
            | SOME scope_list''' =>
             SOME ((counter, ext_obj_map, v_map, ctrl), scope_list''', status_returnv v_bot)
            | _ => NONE)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* TODO: This is currently a placeholder implementation.
 * For symbolic execution. This should be rewritten by adding an assumption that introduces fresh free variables *)
Definition ipsec_crypt_encrypt_aes_ctr_def:
 (ipsec_crypt_encrypt_aes_ctr ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case assign scope_list (set_validity T $ init_out_v ipv4_header) (lval_varname (varn_name "ipv4")) of
      | SOME scope_list' =>
       (case assign scope_list' (set_validity T $ init_out_v esp_header) (lval_varname (varn_name "esp")) of
        | SOME scope_list'' =>
         SOME ((counter, ext_obj_map, v_map, ctrl), scope_list'', status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* TODO: This is currently a placeholder implementation.
 * For symbolic execution. This should be rewritten by adding an assumption that introduces fresh free variables *)
Definition ipsec_crypt_encrypt_null_def:
 (ipsec_crypt_encrypt_null ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case assign scope_list (set_validity T $ init_out_v ipv4_header) (lval_varname (varn_name "ipv4")) of
      | SOME scope_list' =>
       (case assign scope_list' (set_validity T $ init_out_v esp_header) (lval_varname (varn_name "esp")) of
        | SOME scope_list'' =>
         SOME ((counter, ext_obj_map, v_map, ctrl), scope_list'', status_returnv v_bot)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(* TODO: This is currently a placeholder implementation.
 * For symbolic execution. This should be rewritten by adding an assumption that introduces fresh free variables *)
Definition ipsec_crypt_decrypt_null_def:
 (ipsec_crypt_decrypt_null ((counter, ext_obj_map, v_map, ctrl):v1model_ascope, g_scope_list:g_scope_list, scope_list) =
  case lookup_lval scope_list (lval_varname (varn_name "ipv4")) of
  | SOME ipv4_header =>
   (case lookup_lval scope_list (lval_varname (varn_name "esp")) of
    | SOME esp_header =>
     (case lookup_lval scope_list (lval_varname (varn_name "standard_metadata")) of
      | SOME standard_metadata =>
       (case assign scope_list (set_validity T $ init_out_v ipv4_header) (lval_varname (varn_name "ipv4")) of
        | SOME scope_list' =>
         (case assign scope_list' (set_validity T $ init_out_v esp_header) (lval_varname (varn_name "esp")) of
          | SOME scope_list'' =>
           (case assign scope_list'' (set_validity T $ init_out_v standard_metadata) (lval_varname (varn_name "standard_metadata")) of
            | SOME scope_list''' =>
             SOME ((counter, ext_obj_map, v_map, ctrl), scope_list''', status_returnv v_bot)
            | _ => NONE)
          | _ => NONE)
        | _ => NONE)
      | _ => NONE)
    | _ => NONE)
  | _ => NONE
 )
End

(**********************************************************)
(*                     MODEL-SPECIFIC                     *)
(**********************************************************)

(* TODO: The reset values of standard metadata *)
val v1model_standard_metadata_zeroed =
 listSyntax.mk_list
  (map pairSyntax.mk_pair
   [(``"ingress_port"``, mk_v_bitii (0, 9)),
    (``"egress_spec"``, mk_v_bitii (0, 9)),
    (``"egress_port"``, mk_v_bitii (0, 9)),
    (``"instance_type"``, mk_v_bitii (0, 32)),
    (``"packet_length"``, mk_v_bitii (0, 32)),
    (``"enq_timestamp"``, mk_v_bitii (0, 32)),
    (``"enq_qdepth"``, mk_v_bitii (0, 19)),
    (``"deq_timedelta"``, mk_v_bitii (0, 32)),
    (``"deq_qdepth"``, mk_v_bitii (0, 19)),
    (``"ingress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"egress_global_timestamp"``, mk_v_bitii (0, 48)),
    (``"mcast_grp"``, mk_v_bitii (0, 16)),
    (``"egress_rid"``, mk_v_bitii (0, 16)),
    (``"checksum_error"``, mk_v_bitii (0, 1)),
    (``"parser_error"``, mk_v_bitii (0, 32)),
    (``"priority"``, mk_v_bitii (0, 3))],
   “:(string # v)”);

(*
val v1model_standard_metadata_uninit =
 mk_v_struct_list [(``"ingress_port"``, mk_v_biti_arb 9),
                   (``"egress_spec"``, mk_v_biti_arb 9),
                   (``"egress_port"``, mk_v_biti_arb 9),
                   (``"instance_type"``, mk_v_biti_arb 32),
                   (``"packet_length"``, mk_v_biti_arb 32),
                   (``"enq_timestamp"``, mk_v_biti_arb 32),
                   (``"enq_qdepth"``, mk_v_biti_arb 19),
                   (``"deq_timedelta"``, mk_v_biti_arb 32),
                   (``"deq_qdepth"``, mk_v_biti_arb 19),
                   (``"ingress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"egress_global_timestamp"``, mk_v_biti_arb 48),
                   (``"mcast_grp"``, mk_v_biti_arb 16),
                   (``"egress_rid"``, mk_v_biti_arb 16),
                   (``"checksum_error"``, mk_v_biti_arb 1),
                   (``"parser_error"``, mk_v_biti_arb 32),
                   (``"priority"``, mk_v_biti_arb 3)];
*)
(*
val v1model_meta_uninit =
 mk_v_struct_list [];

val v1model_row_uninit =
 mk_v_struct_list [(``"e"``, mk_v_biti_arb 8),
                   (``"t"``, mk_v_biti_arb 16),
                   (``"l"``, mk_v_biti_arb 8),
                   (``"r"``, mk_v_biti_arb 8),
                   (``"v"``, mk_v_biti_arb 8)];

val v1model_hdr_uninit =
 mk_v_header_list F [(``"row"``, v1model_row_uninit)];

val v1model_header_uninit =
 mk_v_struct_list [(``"h"``, v1model_hdr_uninit)];
*)

(* TODO: This should also arbitrate between different ports, taking a list of lists of input *)
Definition v1model_input_f_def:
 (v1model_input_f (tau1_uninit_v,tau2_uninit_v) (io_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case io_list of
  | [] => NONE
  | ((bl,p)::t) =>
   (* TODO: Currently, no garbage collection in ext_obj_map is done *)
   (* let counter' = ^v1model_init_counter in *)
   let ext_obj_map' = AUPDATE ext_obj_map (counter, INL (core_v_ext_packet bl)) in
   let counter' = counter + 2 in
   (* TODO: Currently, no garbage collection in v_map is done *)
   let v_map' = AUPDATE_LIST v_map [("b", v_ext_ref counter);
                                    ("b_temp", v_ext_ref (counter+1));
                                    ("standard_metadata", v_struct (AUPDATE (^v1model_standard_metadata_zeroed) ("ingress_port", v_bit (w9 (n2w p)))));
                                    ("parsedHdr", tau1_uninit_v);
                                    ("hdr", tau1_uninit_v);
                                    ("meta", tau2_uninit_v)] in
    SOME (t, (counter', ext_obj_map', v_map', ctrl):v1model_ascope))
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition v1model_reduce_nonout_def:
 (v1model_reduce_nonout ([], elist, v_map) =
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
       else oCONS (e_v (init_out_v v), v1model_reduce_nonout (dlist, elist, v_map))       
      | _ => NONE)
    | _ => NONE)) /\
 (v1model_reduce_nonout (_, _, v_map) = NONE)
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
(* TODO: Remove these and keep "v_map" as just a regular scope? *)
Definition v_map_to_scope_def:
 (v_map_to_scope [] = []) /\
 (v_map_to_scope (((k, v)::t):(string, v) alist) =
  ((varn_name k, (v, NONE:lval option))::v_map_to_scope t)
 )
End

(* TODO: Generalise and move to core? Duplicated in all three architectures... *)
Definition scope_to_vmap_def:
 (scope_to_vmap [] = SOME []) /\
 (scope_to_vmap ((vn, (v:v, lval_opt:lval option))::t) =
  case vn of
   | (varn_name k) => oCONS ((k, v), scope_to_vmap t)
   | _ => NONE
 )
End

(* TODO: Since the same thing should be initialised
 *       for all known architectures, maybe it should be made a
 *       architecture-generic (core) function? *)
(* TODO: Don't reduce all arguments at once? *)
Definition v1model_copyin_pbl_def:
 v1model_copyin_pbl (xlist, dlist, elist, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  case v1model_reduce_nonout (dlist, elist, v_map) of
  | SOME elist' =>
   (case copyin xlist dlist elist' [v_map_to_scope v_map] [ [] ] of
    | SOME scope =>
     SOME scope
    | NONE => NONE)
  | NONE => NONE
End

(* Note that this re-uses the copyout function intended for P4 functions *)
Definition v1model_copyout_pbl_def:
 v1model_copyout_pbl (g_scope_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope, dlist, xlist, (status:status)) =
  case copyout_pbl_gen xlist dlist g_scope_list v_map of
  | SOME [v_map_scope] =>
   (case scope_to_vmap v_map_scope of
    | SOME v_map' => SOME ((counter, ext_obj_map, v_map', ctrl):v1model_ascope)
    | NONE => NONE)
  | _ => NONE
End

(* TODO: Make generic *)
Definition v1model_lookup_obj_def:
 v1model_lookup_obj ext_obj_map v_map k =
  case ALOOKUP v_map k of
  | SOME (v_ext_ref i) =>
   ALOOKUP ext_obj_map i
  | _ => NONE
End

(* Transfers the value of parsedHdr to hdr and the parserError value to standard_metadata,
 * then resets the shared packet "b" (TODO: Fix that hack) and saves its content in "b_temp" *)
(* TODO: Note that this also resets parseError to 0 *)
Definition v1model_postparser_def:
 v1model_postparser ((counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case ALOOKUP v_map "b" of
   | SOME (v_ext_ref i) =>
    (case ALOOKUP ext_obj_map i of
     | SOME (INL (core_v_ext_packet bl)) =>
      (case ALOOKUP v_map "b_temp" of
       | SOME (v_ext_ref i') =>
        (case ALOOKUP v_map "parsedHdr" of
         | SOME v =>
          let v_map' = AUPDATE v_map ("hdr", v) in
           (case ALOOKUP v_map "parseError" of
            | SOME v' =>
             (case assign [v_map_to_scope v_map'] v' (lval_field (lval_varname (varn_name "standard_metadata")) "parser_error") of
              | SOME [v_map_scope] =>
               (case scope_to_vmap v_map_scope of
                | SOME v_map'' =>
                 let v_map''' = AUPDATE v_map'' ("parseError", v_bit (fixwidth 32 (n2v 0), 32)) in
                 let (counter', ext_obj_map', v_map'''', ctrl') = (v1model_ascope_update (counter, ext_obj_map, v_map''', ctrl) i' (INL (core_v_ext_packet bl))) in
   SOME (v1model_ascope_update (counter', ext_obj_map', v_map'''', ctrl') i (INL (core_v_ext_packet [])))
                | NONE => NONE)
              | _ => NONE)
            | NONE => NONE)
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End

(* Note that this split-up of functions is so that the symbolic execution
 * can handle symbolic branch on output port.
 * TODO: Use the v directly (and not the port_bl) in order to
 * make sense to also use as a control plane assumption, specifically on
 * the argument of an action. *)
Definition v1model_is_drop_port_def:
 v1model_is_drop_port port_bl =
  if v2n port_bl = 511
  then T
  else F
End

(* TODO: Outsource obtaining the output port to an external function? *)
(* NOTE: "b" renamed to "b_out" *)
(* A little clumsy with the double v2n, but that makes things easier *)
Definition v1model_output_f_def:
 v1model_output_f (in_out_list:in_out_list, (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
  (case v1model_lookup_obj ext_obj_map v_map "b" of
   | SOME (INL (core_v_ext_packet bl)) =>
    (case v1model_lookup_obj ext_obj_map v_map "b_temp" of
     | SOME (INL (core_v_ext_packet bl')) =>
      (case ALOOKUP v_map "standard_metadata" of
       | SOME (v_struct struct) =>
        (case ALOOKUP struct "egress_spec" of
         | SOME (v_bit (port_bl, n)) =>
          SOME (in_out_list++(if v1model_is_drop_port port_bl then [] else [(bl++bl', v2n port_bl)]), (counter, ext_obj_map, v_map, ctrl))
         | _ => NONE)
       | _ => NONE)
     | _ => NONE)
   | _ => NONE)
End  

(* This assumes that tables contains at most one LPM key,
 * with other keys being exact if one LPM key is present.
 * Note that table priority is runtime-dependent, with only partial P4 language
 * support. *)
val v1model_apply_table_f_def =
 if CONTROL_PLANE_API = 0
 then xDefine "v1model_apply_table_f"
  ‘v1model_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
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
 else xDefine "v1model_apply_table_f"
  ‘v1model_apply_table_f (x, e_l, mk_list:mk_list, (x', e_l'), (counter, ext_obj_map, v_map, ctrl):v1model_ascope) =
    (* TODO: Note that this function could do other stuff here depending on table name.
     *       Ideally, one could make a general, not hard-coded, solution for this *)
    case ALOOKUP ctrl x of
     | SOME table =>
      (* Largest priority wins *)
      SOME (FST $ FOLDL_MATCH e_l ((x', e_l'), NONE) table)
     | NONE => NONE’;

val _ = export_theory ();
