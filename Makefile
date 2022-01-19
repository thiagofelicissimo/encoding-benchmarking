

typecheck-traditional-dk:
	cd arith_fermat/traditional && rm -f *.dko && time dkcheck -e sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-adequate-dk:
	cd arith_fermat/adequate/dk && rm -f *.dko && time dkcheck -e sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-adequate-lp:
	cd arith_fermat/adequate/lp && rm -f *.lpo && time lambdapi check -c fermat.lp
