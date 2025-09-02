signature bdd_utilsLib =
sig
  include Abbrev

        val make_bv :int -> int -> term
        val pairBDDs   : term * term -> term
        val bdd_to_tables_iterative   : term -> term -> term


end