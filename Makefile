

typecheck-traditional-dk:
	cd arith_fermat/traditional/dk && rm -f *.dko && time dkcheck -e sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-traditional-kontroli:
	cd arith_fermat/traditional/ko && time kocheck sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-traditional-lp:
	cd arith_fermat/traditional/lp && rm -f *.lpo && time lambdapi check -c fermat.lp

typecheck-traditional-lp-no-obj:
	cd arith_fermat/traditional/lp && rm -f *.lpo && time lambdapi check fermat.lp

typecheck-adequate-dk:
	cd arith_fermat/adequate/dk && rm -f *.dko && time dkcheck -e sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk

typecheck-adequate-kontroli:
	cd arith_fermat/adequate/ko && time kocheck sttfa.dk connectives.dk logic.dk leibniz.dk relations.dk bool.dk nat.dk fact.dk div_mod.dk exp.dk bigops.dk sigma_pi.dk primes.dk gcd.dk cong.dk permutation.dk fermat.dk 

typecheck-adequate-lp:
	cd arith_fermat/adequate/lp && rm -f *.lpo && time lambdapi check -c fermat.lp

typecheck-adequate-lp-no-obj:
	cd arith_fermat/adequate/lp && rm -f *.lpo && time lambdapi check fermat.lp



