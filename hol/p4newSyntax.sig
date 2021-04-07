signature p4newSyntax =
sig
   include Abbrev

   (**********)
   (* Status *)
   (**********)

   val status_ty : hol_type
   
   val status_running_tm   : term
   val is_status_running   : term -> bool

   val status_type_error_tm   : term
   val is_status_type_error   : term -> bool


   (*********)
   (* State *)
   (*********)

   val state_ty : hol_type
   
   val state_ct_tm   : term
   val dest_state_ct : term -> term * term * term
   val is_state_ct   : term -> bool
   val mk_state_ct   : term * term * term -> term


   (***************)
   (* Expressions *)
   (***************)

   val exp_ty : hol_type

   val exp_bool_const_tm   : term
   val dest_exp_bool_const : term -> term
   val is_exp_bool_const   : term -> bool
   val mk_exp_bool_const   : term -> term

   val exp_int_const_tm   : term
   val dest_exp_int_const : term -> term
   val is_exp_int_const   : term -> bool
   val mk_exp_int_const   : term -> term

   val exp_var_tm   : term
   val dest_exp_var : term -> term
   val is_exp_var   : term -> bool
   val mk_exp_var   : term -> term

   val exp_eq_tm   : term
   val dest_exp_eq : term -> term * term
   val is_exp_eq   : term -> bool
   val mk_exp_eq   : term * term -> term

   val exp_sub_tm   : term
   val dest_exp_sub : term -> term * term
   val is_exp_sub   : term -> bool
   val mk_exp_sub   : term * term -> term


   (************************)
   (* Expression reduction *)
   (************************)

   val exp_red_tm   : term
   val dest_exp_red : term -> term * term * term * term
   val is_exp_red   : term -> bool
   val mk_exp_red   : term * term * term * term -> term

end
