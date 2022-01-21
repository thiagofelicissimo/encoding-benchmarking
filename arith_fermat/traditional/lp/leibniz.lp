require tests.sttfa as sttfa;
require tests.connectives as connectives;
symbol leibniz
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.eta A),
          λ (y : sttfa.eta A),
            sttfa.forall (sttfa.arrow A sttfa.bool)
            (λ (P : sttfa.eta (sttfa.arrow A sttfa.bool)),
               sttfa.impl (P x) (P y));
symbol refl_leibniz
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A (λ (x : sttfa.eta A), leibniz A x x)))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.eta A),
          λ (P : sttfa.eta (sttfa.arrow A sttfa.bool)),
            λ (H : sttfa.eps (P x)), H;
symbol sym_leibniz
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.eta A),
           sttfa.forall A
           (λ (y : sttfa.eta A), sttfa.impl (leibniz A x y) (leibniz A y x)))));
