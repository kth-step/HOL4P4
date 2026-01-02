signature bdd_utilsLib =
sig
  include Abbrev

        val make_bv :int -> int -> term
        val pairBDDs   : term * term -> term
        val bdd_to_tables_iterative   : term -> term -> term
        val mtbdd_to_rules1   : term -> term 
        val mtbdd_to_rules2   : term -> term 
        
end