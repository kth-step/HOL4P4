signature p4_cake_validationLib =
sig
  include Abbrev

val p4_eval_test_tac' : hol_type -> term -> term -> (goal, thm) gentactic

end
