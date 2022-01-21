require tests.sttfa as sttfa;
constant symbol True : sttfa.etap (sttfa.p sttfa.bool);
constant symbol False : sttfa.etap (sttfa.p sttfa.bool);
constant symbol Not
  : sttfa.etap (sttfa.p (sttfa.arrow sttfa.bool sttfa.bool));
constant symbol And
  : sttfa.etap
    (sttfa.p (sttfa.arrow sttfa.bool (sttfa.arrow sttfa.bool sttfa.bool)));
constant symbol Or
  : sttfa.etap
    (sttfa.p (sttfa.arrow sttfa.bool (sttfa.arrow sttfa.bool sttfa.bool)));
constant symbol ex
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow (sttfa.arrow A sttfa.bool) sttfa.bool)));
constant symbol equal
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool))));
constant symbol I : sttfa.eps True;
constant symbol falsity
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (t : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.impl False t));
constant symbol nmk
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.impl (sttfa.impl A False) (Not A)));
constant symbol Not_ind
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (Q : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl (sttfa.impl (sttfa.impl A False) Q)
           (sttfa.impl (Not A) Q))));
constant symbol conj
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl A (sttfa.impl B (And A B)))));
constant symbol match_And_prop
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.forall sttfa.bool
           (λ (return : sttfa.etap (sttfa.p sttfa.bool)),
              sttfa.impl (sttfa.impl A (sttfa.impl B return))
              (sttfa.impl (And A B) return)))));
constant symbol or_introl
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl A (Or A B))));
constant symbol or_intror
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl B (Or A B))));
constant symbol match_Or_prop
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.forall sttfa.bool
           (λ (return : sttfa.etap (sttfa.p sttfa.bool)),
              sttfa.impl (sttfa.impl A return)
              (sttfa.impl (sttfa.impl B return)
               (sttfa.impl (Or A B) return))))));
constant symbol ex_intro
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow A sttfa.bool)
        (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
           sttfa.forall A
           (λ (x : sttfa.etap (sttfa.p A)), sttfa.impl (P x) (ex A P)))));
constant symbol match_ex_prop
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow A sttfa.bool)
        (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
           sttfa.forall sttfa.bool
           (λ (return : sttfa.etap (sttfa.p sttfa.bool)),
              sttfa.impl
              (sttfa.forall A
               (λ (x : sttfa.etap (sttfa.p A)), sttfa.impl (P x) return))
              (sttfa.impl (ex A P) return)))));
constant symbol refl_equal
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A (λ (x : sttfa.eta A), equal A x x)));
constant symbol equal_leibniz
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.eta A),
           sttfa.forall A
           (λ (y : sttfa.eta A),
              sttfa.impl (equal A x y)
              (sttfa.forall (sttfa.arrow A sttfa.bool)
               (λ (P : sttfa.eta (sttfa.arrow A sttfa.bool)),
                  sttfa.impl (P x) (P y)))))));
