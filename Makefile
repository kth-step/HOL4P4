hol:
	cd hol/ && Holmake

polygram: hol
	Holmake -r -I hol -I hol/polygram

cake: polygram
	cd hol/polygram/bdd_cake_trans && Holmake	


test: cake
	cd hol/polygram/policy_test_cases_mtbdd && ./prepp.sh
	cd hol/polygram/policy_test_cases_eq && ./prepp.sh
	cd hol/polygram/policy_test_cases_gen_policy && ./prepp.sh
	cd hol/polygram/policy_test_cases && ./prepp.sh


clean:
	cd hol && Holmake clean
	cd hol/polygram && Holmake clean
	cd hol/polygram/policy_test_cases && Holmake clean && rm -f *.txt
	cd hol/polygram/policy_test_cases_eq && Holmake clean && rm -f *.txt
	cd hol/polygram/policy_test_cases_gen_policy && Holmake clean && rm -f *.txt
	cd hol/polygram/bdd_cake_trans && Holmake clean
	cd hol/polygram/bdd_cake_test && Holmake clean && rm -f internet_firewall_* && rm -f test_bdd_*

.PHONY: default clean hol