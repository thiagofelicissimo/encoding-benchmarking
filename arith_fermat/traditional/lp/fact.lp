require tests.connectives as connectives;
require tests.leibniz as leibniz;
require tests.nat as nat;
require tests.sttfa as sttfa;
constant symbol fact : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat));
constant symbol fact_body
  : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat));
constant symbol axiom_fact
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal nat.nat (fact n)
        (nat.filter_nat_type nat.nat fact_body n)));
symbol eq_fact
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat (fact n)
        (nat.filter_nat_type nat.nat fact_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal_leibniz nat.nat (fact n)
        (nat.filter_nat_type nat.nat fact_body n) (axiom_fact n);
symbol sym_eq_fact
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat
        (nat.filter_nat_type nat.nat fact_body n) (fact n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.sym_leibniz nat.nat (fact n)
        (nat.filter_nat_type nat.nat fact_body n) (eq_fact n);
constant symbol axiom_fact_body_O
  : sttfa.eps
    (connectives.equal nat.nat (fact_body nat.O) (nat.S nat.O));
symbol eq_fact_body_O
  : sttfa.eps (leibniz.leibniz nat.nat (fact_body nat.O) (nat.S nat.O))
  ≔ connectives.equal_leibniz nat.nat (fact_body nat.O) (nat.S nat.O)
      axiom_fact_body_O;
symbol sym_eq_fact_body_O
  : sttfa.eps (leibniz.leibniz nat.nat (nat.S nat.O) (fact_body nat.O))
  ≔ leibniz.sym_leibniz nat.nat (fact_body nat.O) (nat.S nat.O)
      eq_fact_body_O;
constant symbol axiom_fact_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal nat.nat (fact_body (nat.S n))
        (nat.times (fact n) (nat.S n))));
symbol eq_fact_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat (fact_body (nat.S n))
        (nat.times (fact n) (nat.S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal_leibniz nat.nat (fact_body (nat.S n))
        (nat.times (fact n) (nat.S n)) (axiom_fact_body_S n);
symbol sym_eq_fact_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat (nat.times (fact n) (nat.S n))
        (fact_body (nat.S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.sym_leibniz nat.nat (fact_body (nat.S n))
        (nat.times (fact n) (nat.S n)) (eq_fact_body_S n);
