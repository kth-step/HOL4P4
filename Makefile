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
	cd hol/polygram/policy_test_cases_cakeml_best && ./prepp.sh
	cd hol/polygram/policy_test_cases_cakeml_worst && ./prepp.sh
	cd hol/polygram/policy_test_cases_hol4_best && ./prepp.sh
	cd hol/polygram/policy_test_cases_hol4_worst && ./prepp.sh

clean:
#	cd hol && Holmake clean
#	cd hol/polygram && Holmake clean
	cd hol/polygram/policy_test_cases_cakeml_best && Holmake clean
	cd hol/polygram/policy_test_cases_cakeml_worst && Holmake clean
	cd hol/polygram/policy_test_cases_hol4_best && Holmake clean
	cd hol/polygram/policy_test_cases_hol4_worst && Holmake clean
	cd hol/polygram/policy_test_cases_eq && Holmake clean
	cd hol/polygram/policy_test_cases_gen_policy && Holmake clean
	cd hol/polygram/policy_test_cases_mtbdd && Holmake clean
# 	cd hol/polygram/bdd_cake_trans && Holmake clean
# 	cd hol/polygram/bdd_cake_test && Holmake clean && rm -f internet_firewall_* && rm -f test_bdd_*

.PHONY: default clean hol