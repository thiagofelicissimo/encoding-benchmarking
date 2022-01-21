require tests.sttfa as sttfa;
require tests.connectives as connectives;
require tests.logic as logic;
symbol reflexive
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow A (sttfa.arrow A sttfa.bool)) sttfa.bool)))
  ≔ λ (A : sttfa.{|type|}),
        λ
          (
          R : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
          ), sttfa.forall A (λ (x : sttfa.etap (sttfa.p A)), R x x);
symbol transitive
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow A (sttfa.arrow A sttfa.bool)) sttfa.bool)))
  ≔ λ (A : sttfa.{|type|}),
        λ
          (
          R : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
          ),
          sttfa.forall A
          (λ (x : sttfa.etap (sttfa.p A)),
             sttfa.forall A
             (λ (y : sttfa.etap (sttfa.p A)),
                sttfa.forall A
                (λ (z : sttfa.etap (sttfa.p A)),
                   sttfa.impl (R x y) (sttfa.impl (R y z) (R x z)))));
symbol RC
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow A (sttfa.arrow A sttfa.bool))
         (sttfa.arrow A (sttfa.arrow A sttfa.bool)))))
  ≔ λ (A : sttfa.{|type|}),
        λ
          (
          R : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
          ),
          λ (x : sttfa.etap (sttfa.p A)),
            λ (y : sttfa.etap (sttfa.p A)),
              connectives.Or (R x y) (logic.eq A x y);
symbol RC_reflexive
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow A (sttfa.arrow A sttfa.bool))
        (λ
           (
           R : sttfa.etap
               (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
           ), reflexive A (RC A R))))
  ≔ λ (A : sttfa.{|type|}),
        λ
          (
          R : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
          ),
          λ (x : sttfa.etap (sttfa.p A)),
            connectives.or_intror (R x x) (logic.eq A x x) (logic.refl A x);
symbol injective_
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.forallK
        (λ (B : sttfa.{|type|}),
           sttfa.p (sttfa.arrow (sttfa.arrow A B) sttfa.bool))))
  ≔ λ (A : sttfa.{|type|}),
        λ (B : sttfa.{|type|}),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow A B))),
            sttfa.forall A
            (λ (x : sttfa.etap (sttfa.p A)),
               sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.impl (logic.eq B (f x) (f y)) (logic.eq A x y)));
symbol {|commutative|}
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow (sttfa.arrow A (sttfa.arrow A A)) sttfa.bool)))
  ≔ λ (A : sttfa.{|type|}),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
          sttfa.forall A
          (λ (x : sttfa.etap (sttfa.p A)),
             sttfa.forall A
             (λ (y : sttfa.etap (sttfa.p A)), logic.eq A (f x y) (f y x)));
symbol {|associative|}
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow (sttfa.arrow A (sttfa.arrow A A)) sttfa.bool)))
  ≔ λ (A : sttfa.{|type|}),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
          sttfa.forall A
          (λ (x : sttfa.etap (sttfa.p A)),
             sttfa.forall A
             (λ (y : sttfa.etap (sttfa.p A)),
                sttfa.forall A
                (λ (z : sttfa.etap (sttfa.p A)),
                   logic.eq A (f (f x y) z) (f x (f y z)))));
symbol monotonic
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow A (sttfa.arrow A sttfa.bool))
         (sttfa.arrow (sttfa.arrow A A) sttfa.bool))))
  ≔ λ (A : sttfa.{|type|}),
        λ
          (
          R : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool)))
          ),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow A A))),
            sttfa.forall A
            (λ (x : sttfa.etap (sttfa.p A)),
               sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.impl (R x y) (R (f x) (f y))));
symbol distributive
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow A (sttfa.arrow A A))
         (sttfa.arrow (sttfa.arrow A (sttfa.arrow A A)) sttfa.bool))))
  ≔ λ (A : sttfa.{|type|}),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
          λ (g : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
            sttfa.forall A
            (λ (x : sttfa.etap (sttfa.p A)),
               sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.forall A
                  (λ (z : sttfa.etap (sttfa.p A)),
                     logic.eq A (f x (g y z)) (g (f x y) (f x z)))));
