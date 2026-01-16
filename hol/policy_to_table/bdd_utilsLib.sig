signature bdd_utilsLib =
sig
  include Abbrev

        val make_bv :int -> int -> term
        val pairBDDs   : term * term -> term

        val bdd_to_tables_iterative   : term -> term -> term
        val bdd_to_tables_iterative_old   : term -> term -> term

        val mtbdd_to_rules_all_paths   : term -> term 
        val mtbdd_to_rules_grouped_by_action_simple   : term -> term 
        val mtbdd_to_rules   : term -> term 

end