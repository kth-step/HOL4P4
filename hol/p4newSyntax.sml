structure p4newSyntax :> p4newSyntax =
struct

open HolKernel boolLib Parse bossLib ottLib;

open p4newTheory;

fun syntax_fns n d m = HolKernel.syntax_fns {n = n, dest = d, make = m} "p4new"
fun syntax_fns0 s = let val (tm, _, _, is_f) = syntax_fns 0
   (fn tm1 => fn e => fn tm2 =>
       if Term.same_const tm1 tm2 then () else raise e)
   (fn tm => fn () => tm) s in (tm, is_f) end;

(* Variable contexts *)
(* TODO
val stack_frame_ty = mk_type ("stack_frame", []);
val env_stack_ty = mk_type ("env_stack", []);
val temp_stack_ty = mk_type ("temp_stack", []);
*)

val status_ty = mk_type ("status", []);

val (status_running_tm, is_status_running) =
  syntax_fns0 "status_running";
val (status_type_error_tm, is_status_type_error) =
  syntax_fns0 "status_type_error";

(* State *)

val state_ty = mk_type ("state", []);

val (state_ct_tm, mk_state_ct, dest_state_ct, is_state_ct) =
  syntax_fns3 "p4new"  "state_ct";

(* Expressions *)

val exp_ty = mk_type ("exp", []);

val (exp_bool_const_tm, mk_exp_bool_const, dest_exp_bool_const, is_exp_bool_const) =
  syntax_fns1 "p4new"  "exp_bool_const";
val (exp_int_const_tm, mk_exp_int_const, dest_exp_int_const, is_exp_int_const) =
  syntax_fns1 "p4new"  "exp_int_const";
val (exp_var_tm, mk_exp_var, dest_exp_var, is_exp_var) =
  syntax_fns1 "p4new"  "exp_var";
val (exp_eq_tm, mk_exp_eq, dest_exp_eq, is_exp_eq) =
  syntax_fns2 "p4new"  "exp_eq";
val (exp_sub_tm, mk_exp_sub, dest_exp_sub, is_exp_sub) =
  syntax_fns2 "p4new"  "exp_sub";

(* Expression reductions *)

val (exp_red_tm, mk_exp_red, dest_exp_red, is_exp_red) =
  syntax_fns4 "p4new"  "exp_red";

end
