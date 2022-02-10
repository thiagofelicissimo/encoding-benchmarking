

typecheck-traditional-dk:
	cd arith_fermat/traditional/dk && rm -f *.dko && time dkcheck -e sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-traditional-kontroli:
	cd arith_fermat/traditional/ko && time kocheck sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-traditional-lp:
	cd arith_fermat/traditional/lp && rm -f *.lpo && time lambdapi check -c fermat.lp

typecheck-traditional-lp-no-obj:
	cd arith_fermat/traditional/lp && rm -f *.lpo && time lambdapi check fermat.lp

typecheck-adequate-dk:
	cd arith_fermat/adequate/dk && rm -f *.dko && time dkcheck -e fermatlib_sttfa.dk fermatlib_connectives.dk fermatlib_leibniz.dk fermatlib_logic.dk fermatlib_relations.dk fermatlib_bool.dk fermatlib_nat.dk fermatlib_exp.dk fermatlib_div_mod.dk fermatlib_primes.dk fermatlib_cong.dk fermatlib_gcd.dk fermatlib_bigops.dk fermatlib_sigma_pi.dk fermatlib_fact.dk fermatlib_permutation.dk fermatlib_fermat.dk

typecheck-adequate-kontroli:
	cd arith_fermat/adequate/ko && time kocheck fermatlib_sttfa.dk fermatlib_connectives.dk fermatlib_leibniz.dk fermatlib_logic.dk fermatlib_relations.dk fermatlib_bool.dk fermatlib_nat.dk fermatlib_exp.dk fermatlib_div_mod.dk fermatlib_primes.dk fermatlib_cong.dk fermatlib_gcd.dk fermatlib_bigops.dk fermatlib_sigma_pi.dk fermatlib_fact.dk fermatlib_permutation.dk fermatlib_fermat.dk

typecheck-adequate-lp:
	cd arith_fermat/adequate/lp && rm -f *.lpo && time lambdapi check -c fermat.lp

typecheck-adequate-lp-no-obj:
	cd arith_fermat/adequate/lp && rm -f *.lpo && time lambdapi check fermat.lp



