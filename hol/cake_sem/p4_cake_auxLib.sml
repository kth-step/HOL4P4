structure p4_cake_auxLib :> p4_cake_auxLib = struct

open HolKernel boolLib liteLib simpLib Parse bossLib;

open listSyntax bitstringSyntax numSyntax pairSyntax;

open p4Theory;
open p4_cake_auxTheory;
open p4Syntax;

(* Some extra tricks for CakeML export *)

fun to_fixwidth_n2v_CONV tm =
 let
  val elems = fst $ dest_list tm
  val len = length elems
  val n = rhs $ concl $ EVAL $ mk_v2n $ mk_list (elems, bool)
  val rewrite = GSYM $ EVAL $ mk_fixwidth (term_of_int len, mk_n2v n)
 in
  REWRITE_CONV [rewrite] tm
 end
;

(* This simpset fragment takes bool lists and converts them to a less verbose format
 * involving fewer constants *)
val BOOL_LIST_ss =
 SSFRAG {name = SOME "BOOL_LIST_ss",
	 convs = [{conv = K $ K to_fixwidth_n2v_CONV,
		   key= SOME ([], mk_var ("bool_list", mk_list_type bool)),
		   name = "to_fixwidth_n2v_CONV",
		   trace = 2}],
	 rewrs = [],
         ac = [],
	 filter = NONE,
	 dprocs = [],
	 congs = []
 };

val (word_tm, mk_word, dest_word, is_word) =
  syntax_fns2 "p4_aux" "word";

fun to_word_CONV tm =
 let
  val (list, width) = dest_pair tm
  val elems = fst $ dest_list list
  (* TODO: Check agreement *)
  val n = rhs $ concl $ EVAL $ mk_v2n $ mk_list (elems, bool)
  val rewrite = GSYM $ EVAL $ mk_word (n, width)
 in
  REWRITE_CONV [rewrite] tm
 end
;

val BOOL_LIST_ss' =
 SSFRAG {name = SOME "BOOL_LIST_ss'",
	 convs = [{conv = K $ K to_word_CONV,
		   key= SOME ([], mk_pair (mk_var ("bool_list", mk_list_type bool), mk_var ("width", num))),
		   name = "to_word_CONV",
		   trace = 2}],
	 rewrs = [],
         ac = [],
	 filter = NONE,
	 dprocs = [],
	 congs = []
 };


(******************)
(* Creating input *)

val (tau_in_bit_rand_tm, mk_tau_in_bit_rand, dest_tau_in_bit_rand, is_tau_in_bit_rand) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_rand";
val (tau_in_bit_fix_tm, mk_tau_in_bit_fix, dest_tau_in_bit_fix, is_tau_in_bit_fix) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_fix";

fun n_coin_flips 0 = []
  | n_coin_flips n =
   mlibUseful.coin_flip () :: (n_coin_flips (n-1))
;

fun bitstring_of_tau_in_list' [] = “[]:bool list”
  | bitstring_of_tau_in_list' (h::t) =
   if is_tau_in_bit_rand h
   then
    let
     val width = int_of_term $ dest_tau_in_bit_rand h
    in
     mk_append (mk_list (map (lift_bool bool) $ n_coin_flips width, bool),  bitstring_of_tau_in_list' t)
    end
   else if is_tau_in_bit_fix h
   then
    let
     val (value, width) = dest_pair $ dest_tau_in_bit_fix h
     val bitlist_tm = rhs $ concl $ EVAL “fixwidth ^width $ n2v ^value”
    in
     mk_append (bitlist_tm,  bitstring_of_tau_in_list' t)
    end
   else raise Fail "Subtype not supported"
;
fun bitstring_of_tau_in_list l =
 rhs $ concl $ EVAL $ bitstring_of_tau_in_list' (fst $ dest_list l)
;

val (tau_in_bit_fix_tm, mk_tau_in_bit_fix, dest_tau_in_bit_fix, is_tau_in_bit_fix) =
  syntax_fns1 "p4_cake_aux" "tau_in_bit_fix";

val (acc_fld_tm, mk_acc_fld, dest_acc_fld, is_acc_fld) =
  syntax_fns1 "p4_cake_aux" "acc_fld";
val (acc_struct_tm, mk_acc_struct, dest_acc_struct, is_acc_struct) =
  syntax_fns2 "p4_cake_aux" "acc_struct";

fun mk_acc []      = raise Fail "Can't make a field access with no string names"
  | mk_acc (h::[]) = mk_acc_fld (stringLib.fromMLstring h)
  | mk_acc (h::t)  = mk_acc_struct (stringLib.fromMLstring h, mk_acc t)
;

fun update_entries [] tau_in = tau_in
  | update_entries ((acc, new_val)::t) tau_in =
 let
  val acc_tm = mk_acc $ mlibUseful.split "." acc
  val tau_in' = optionSyntax.dest_some $ rhs $ concl $ EVAL “update_tau_in ^acc_tm ^(term_of_int new_val) ^tau_in”
 in
  update_entries t tau_in'
 end
;

(* TODO: This simply generates an input packet based on the shape of the "H" type parameter in V1Model,
 * and names of sub-structs and fields *)
fun v1model_get_input actx fixed_fields components =
 let
  val input_f_tm = #4 $ dest_actx actx
  val hdr_tm = fst $ dest_pair $ snd $ dest_comb input_f_tm
  val tau_in = rhs $ concl $ EVAL “tau_to_tau_in $ THE $ tau_of_type $ type_of_v ^hdr_tm”
(* Length check:
val tau_in_sum = rhs $ concl $ EVAL “tau_in_sum ^tau_in”
*)
  val tau_in' = update_entries fixed_fields tau_in
  val tau_in'' = rhs $ concl $ EVAL “filter_tau_in ^tau_in' ^(mk_list (map stringLib.fromMLstring components, stringLib.string_ty))”
  val tau_in_list = rhs $ concl $ EVAL “tau_in_to_list ^tau_in''”
(* Length checks:
val tau_in_sum = rhs $ concl $ EVAL “tau_in_sum ^tau_in'”
val tau_in_sum = rhs $ concl $ EVAL “FOLDL (\a b. (a:num) + (b:num) ) 0 $ MAP tau_in_sum ^tau_in_list”
*)
 in
  bitstring_of_tau_in_list tau_in_list
 end
;

end
