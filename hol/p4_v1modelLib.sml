structure p4_v1modelLib :> p4_v1modelLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax numSyntax pairSyntax;

open p4Syntax p4_coreLib;

open p4Theory p4_coreTheory p4_v1modelTheory;

fun dest_quinop c e tm =
   case with_exn strip_comb tm e of
      (t, [t1, t2, t3, t4, t5]) =>
         if same_const t c then (t1, t2, t3, t4, t5) else raise e
    | _ => raise e;
fun list_of_quintuple (a, b, c, d, e) = [a, b, c, d, e];
fun mk_quinop tm = HolKernel.list_mk_icomb tm o list_of_quintuple;
val syntax_fns5 = HolKernel.syntax_fns {n = 5, dest = dest_quinop, make = mk_quinop};

val v1model_arch_ty = ``:v1model_ascope``;

(* Architectural constants *)
(* TODO: Nothing other than enumeration types? *)
val v1model_init_global_scope = ``[]:scope``;

val v1model_init_ext_obj_map = “[]:(num, v1model_sum_v_ext) alist”;

val v1model_init_counter = rhs $ concl $ EVAL “LENGTH ^v1model_init_ext_obj_map”;

val v1model_init_v_map = ``^core_init_v_map:(string, v) alist``;

(*******************************************)
(* Architectural context (generic externs) *)

val v1model_objectless_map =
 ``[("mark_to_drop", ([("standard_metadata", d_inout)], v1model_mark_to_drop));
    ("verify", ([("condition", d_in); ("err", d_in)], v1model_verify));
    ("verify_checksum", ([("condition", d_in); ("data", d_in); ("checksum", d_in); ("algo", d_none)], v1model_verify_checksum));
    ("update_checksum", ([("condition", d_in); ("data", d_in); ("checksum", d_inout); ("algo", d_none)], v1model_update_checksum))]``;

val v1model_packet_in_map =
 ``[("extract", ([("this", d_in); ("headerLvalue", d_out)], v1model_packet_in_extract));
    ("lookahead", ([("this", d_in); ("targ1", d_in)], v1model_packet_in_lookahead));
    ("advance", ([("this", d_in); ("bits", d_in)], v1model_packet_in_advance))]``;

val v1model_packet_out_map =
 ``[("emit", ([("this", d_in); ("data", d_in)], v1model_packet_out_emit))]``;

(*************************)
(* Architectural context *)

(* Input function term *)
val v1model_input_f = ``v1model_input_f``;

(* Output function term *)
val v1model_output_f = ``v1model_output_f``;
val v1model_is_drop_port = ``v1model_is_drop_port``;

(* Programmable block input function term *)
val v1model_copyin_pbl = ``v1model_copyin_pbl``;

(* Programmable block output function term *)
val v1model_copyout_pbl = ``v1model_copyout_pbl``;

(* Programmable block output function term *)
val v1model_apply_table_f = ``v1model_apply_table_f``;

(* Fixed-function block map *)
val v1model_ffblock_map = ``[("postparser", ffblock_ff v1model_postparser)]``;

val v1model_register_map =
 ``[("read", ([("this", d_in); ("result", d_out); ("index", d_in)], register_read random_oracle));
    ("write", ([("this", d_in); ("index", d_in); ("value", d_in)], register_write))]``;

val v1model_ipsec_crypt_map =
 ``[("decrypt_aes_ctr", ([("this", d_in); ("ipv4", d_inout); ("esp", d_inout); ("standard_metadata", d_inout); ("key", d_in); ("key_hmac", d_in)], ipsec_crypt_decrypt_aes_ctr random_oracle));
    ("encrypt_aes_ctr", ([("this", d_in); ("ipv4", d_inout); ("esp", d_inout); ("key", d_in); ("key_hmac", d_in)], ipsec_crypt_encrypt_aes_ctr random_oracle));
    ("encrypt_null", ([("this", d_in); ("ipv4", d_inout); ("esp", d_inout)], ipsec_crypt_encrypt_null random_oracle));
    ("decrypt_null", ([("this", d_in); ("ipv4", d_inout); ("esp", d_inout); ("standard_metadata", d_inout)], ipsec_crypt_decrypt_null random_oracle))]``;

(* Extern (object) function map *)
val v1model_ext_map =
 ``((^(inst [``:'a`` |-> v1model_arch_ty] core_ext_map))
    ++ [("", (NONE, (^v1model_objectless_map)));
        ("packet_in", (NONE, (^v1model_packet_in_map)));
        ("packet_out", (NONE, (^v1model_packet_out_map)));
        ("register", SOME ([("this", d_out); ("size", d_none); ("targ1", d_in)], register_construct random_oracle), (^v1model_register_map));
        ("ipsec_crypt", SOME ([("this", d_out)], ipsec_crypt_construct), (^v1model_ipsec_crypt_map))])``;

(* Function map *)
val v1model_func_map = core_func_map;

(*****************)
(* Miscellaneous *)

fun dest_v1model_ascope v1model_ascope =
 let
  val (ext_counter, v1model_ascope') = dest_pair v1model_ascope
  val (ext_obj_map, v1model_ascope'') = dest_pair v1model_ascope'
  val (v_map, v1model_ascope''') = dest_pair v1model_ascope''
  val (ctrl, oracle_index) = dest_pair v1model_ascope'''
 in
  (ext_counter, ext_obj_map, v_map, ctrl, oracle_index)
 end
;

val (v1model_register_construct_inner_tm,  mk_v1model_register_construct_inner, dest_v1model_register_construct_inner, is_v1model_register_construct_inner) =
  syntax_fns4 "p4_v1model" "v1model_register_construct_inner";

val (v1model_register_read_inner_tm,  mk_v1model_register_read_inner, dest_v1model_register_read_inner, is_v1model_register_read_inner) =
  syntax_fns5 "p4_v1model" "v1model_register_read_inner";

val (v1model_register_write_inner_tm,  mk_v1model_register_write_inner, dest_v1model_register_write_inner, is_v1model_register_write_inner) =
  syntax_fns3 "p4_v1model" "v1model_register_write_inner";

val (v1model_update_checksum_inner_tm,  mk_v1model_update_checksum_inner, dest_v1model_update_checksum_inner, is_v1model_update_checksum_inner) =
  syntax_fns1 "p4_v1model" "v1model_update_checksum_inner";

end
