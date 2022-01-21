require tests.sttfa as sttfa;
require tests.connectives as connectives;
constant symbol eq
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p (sttfa.arrow A (sttfa.arrow A sttfa.bool))));
constant symbol refl
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A (λ (x : sttfa.etap (sttfa.p A)), eq A x x)));
constant symbol eq_ind
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
              sttfa.impl (P x)
              (sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.impl (eq A x y) (P y)))))));
symbol eq_rect_r
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (a : sttfa.etap (sttfa.p A)),
           sttfa.forall A
           (λ (x : sttfa.etap (sttfa.p A)),
              sttfa.impl (eq A x a)
              (sttfa.forall (sttfa.arrow A sttfa.bool)
               (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
                  sttfa.impl (P a) (P x)))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (a : sttfa.etap (sttfa.p A)),
          λ (x : sttfa.etap (sttfa.p A)),
            λ (p : sttfa.eps (eq A x a)),
              eq_ind A x
              (λ (__ : sttfa.etap (sttfa.p A)),
                 sttfa.forall (sttfa.arrow A sttfa.bool)
                 (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
                    sttfa.impl (P __) (P x)))
              (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
                 λ (auto : sttfa.eps (P x)), auto)
              a p;
symbol eq_ind_r
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (a : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
              sttfa.impl (P a)
              (sttfa.forall A
               (λ (x : sttfa.etap (sttfa.p A)),
                  sttfa.impl (eq A x a) (P x)))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (a : sttfa.etap (sttfa.p A)),
          λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
            λ (p : sttfa.eps (P a)),
              λ (x0' : sttfa.etap (sttfa.p A)),
                λ (p0 : sttfa.eps (eq A x0' a)),
                  eq_rect_r A a x0' p0
                  (λ (x01' : sttfa.etap (sttfa.p A)), P x01') p;
symbol rewrite_l
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
              sttfa.impl (P x)
              (sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.impl (eq A x y) (P y)))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.etap (sttfa.p A)),
          λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
            λ (Hx : sttfa.eps (P x)),
              λ (y : sttfa.etap (sttfa.p A)),
                λ (Heq : sttfa.eps (eq A x y)),
                  eq_ind A x (λ (__ : sttfa.etap (sttfa.p A)), P __)
                  Hx y Heq;
symbol sym_eq
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall A
           (λ (y : sttfa.etap (sttfa.p A)),
              sttfa.impl (eq A x y) (eq A y x)))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.etap (sttfa.p A)),
          λ (y : sttfa.etap (sttfa.p A)),
            λ (Heq : sttfa.eps (eq A x y)),
              rewrite_l A x
              (λ (__ : sttfa.etap (sttfa.p A)), eq A __ x)
              (refl A x) y
              (rewrite_l A x
               (λ (__ : sttfa.etap (sttfa.p A)), eq A x __)
               (refl A x) y Heq);
symbol rewrite_r
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
              sttfa.impl (P x)
              (sttfa.forall A
               (λ (y : sttfa.etap (sttfa.p A)),
                  sttfa.impl (eq A y x) (P y)))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.etap (sttfa.p A)),
          λ (P : sttfa.etap (sttfa.p (sttfa.arrow A sttfa.bool))),
            λ (Hx : sttfa.eps (P x)),
              λ (y : sttfa.etap (sttfa.p A)),
                λ (Heq : sttfa.eps (eq A y x)),
                  eq_ind A x (λ (__ : sttfa.etap (sttfa.p A)), P __)
                  Hx y (sym_eq A y x Heq);
symbol eq_coerc
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl A (sttfa.impl (eq sttfa.bool A B) B))))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        λ (B : sttfa.etap (sttfa.p sttfa.bool)),
          λ (Ha : sttfa.eps A),
            λ (Heq : sttfa.eps (eq sttfa.bool A B)),
              eq_ind sttfa.bool A
              (λ (x_19 : sttfa.etap (sttfa.p sttfa.bool)), x_19) Ha B Heq;
symbol trans_eq
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall A
           (λ (y : sttfa.etap (sttfa.p A)),
              sttfa.forall A
              (λ (z : sttfa.etap (sttfa.p A)),
                 sttfa.impl (eq A x y)
                 (sttfa.impl (eq A y z) (eq A x z)))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.etap (sttfa.p A)),
          λ (y : sttfa.etap (sttfa.p A)),
            λ (z : sttfa.etap (sttfa.p A)),
              λ (H1 : sttfa.eps (eq A x y)),
                λ (H2 : sttfa.eps (eq A y z)),
                  eq_ind_r A y
                  (λ (x0 : sttfa.etap (sttfa.p A)), eq A x0 z)
                  (rewrite_l A x
                   (λ (__ : sttfa.etap (sttfa.p A)), eq A __ z)
                   (rewrite_l A x
                    (λ (__ : sttfa.etap (sttfa.p A)), eq A x __)
                    (refl A x) z
                    (rewrite_r A y
                     (λ (__ : sttfa.etap (sttfa.p A)), eq A __ z) H2 x
                     H1))
                   y H1)
                  x H1;
symbol eq_f
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forallP
        (λ (B : sttfa.{|type|}),
           sttfa.forall (sttfa.arrow A B)
           (λ (f : sttfa.etap (sttfa.p (sttfa.arrow A B))),
              sttfa.forall A
              (λ (x : sttfa.etap (sttfa.p A)),
                 sttfa.forall A
                 (λ (y : sttfa.etap (sttfa.p A)),
                    sttfa.impl (eq A x y) (eq B (f x) (f y))))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (B : sttfa.{|type|}),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow A B))),
            λ (x : sttfa.etap (sttfa.p A)),
              λ (y : sttfa.etap (sttfa.p A)),
                λ (H : sttfa.eps (eq A x y)),
                  eq_ind_r A y
                  (λ (x0 : sttfa.etap (sttfa.p A)), eq B (f x0) (f y))
                  (rewrite_l A x
                   (λ (__ : sttfa.etap (sttfa.p A)), eq B (f __) (f y))
                   (rewrite_l A x
                    (λ (__ : sttfa.etap (sttfa.p A)),
                       eq B (f x) (f __))
                    (refl B (f x)) y H)
                   y H)
                  x H;
symbol eq_f2
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forallP
        (λ (B : sttfa.{|type|}),
           sttfa.forallP
           (λ (C : sttfa.{|type|}),
              sttfa.forall (sttfa.arrow A (sttfa.arrow B C))
              (λ
                 (f : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow B C)))),
                 sttfa.forall A
                 (λ (x1 : sttfa.etap (sttfa.p A)),
                    sttfa.forall A
                    (λ (x2 : sttfa.etap (sttfa.p A)),
                       sttfa.forall B
                       (λ (y1 : sttfa.etap (sttfa.p B)),
                          sttfa.forall B
                          (λ (y2 : sttfa.etap (sttfa.p B)),
                             sttfa.impl (eq A x1 x2)
                             (sttfa.impl (eq B y1 y2)
                              (eq C (f x1 y1) (f x2 y2))))))))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (B : sttfa.{|type|}),
          λ (C : sttfa.{|type|}),
            λ (f : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow B C)))),
              λ (x1 : sttfa.etap (sttfa.p A)),
                λ (x2 : sttfa.etap (sttfa.p A)),
                  λ (y1 : sttfa.etap (sttfa.p B)),
                    λ (y2 : sttfa.etap (sttfa.p B)),
                      λ (E1 : sttfa.eps (eq A x1 x2)),
                        λ (E2 : sttfa.eps (eq B y1 y2)),
                          eq_ind_r A x2
                          (λ (x : sttfa.etap (sttfa.p A)),
                             eq C (f x y1) (f x2 y2))
                          (eq_ind_r B y2
                           (λ (x : sttfa.etap (sttfa.p B)),
                              eq C (f x2 x) (f x2 y2))
                           (rewrite_l A x1
                            (λ (__ : sttfa.etap (sttfa.p A)),
                               eq C (f __ y2) (f x2 y2))
                            (rewrite_l B y1
                             (λ (__ : sttfa.etap (sttfa.p B)),
                                eq C (f x1 __) (f x2 y2))
                             (rewrite_l A x1
                              (λ (__ : sttfa.etap (sttfa.p A)),
                                 eq C (f x1 y1) (f __ y2))
                              (rewrite_l B y1
                               (λ (__ : sttfa.etap (sttfa.p B)),
                                  eq C (f x1 y1) (f x1 __))
                               (refl C (f x1 y1)) y2 E2)
                              x2 E1)
                             y2 E2)
                            x2 E1)
                           y1 E2)
                          x1 E1;
symbol absurd
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.impl A (sttfa.impl (connectives.Not A) connectives.False)))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        λ (H : sttfa.eps A),
          λ (Hn : sttfa.eps (connectives.Not A)),
            connectives.Not_ind A connectives.False
            (λ (_x_80 : sttfa.eps (sttfa.impl A connectives.False)), _x_80 H)
            Hn;
symbol not_to_not
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl (sttfa.impl A B)
           (sttfa.impl (connectives.Not B) (connectives.Not A)))))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        λ (B : sttfa.etap (sttfa.p sttfa.bool)),
          λ (auto : sttfa.eps (sttfa.impl A B)),
            λ (auto' : sttfa.eps (connectives.Not B)),
              connectives.nmk A
              (λ (auto'' : sttfa.eps A), absurd B (auto auto'') auto');
symbol sym_not_eq
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (x : sttfa.etap (sttfa.p A)),
           sttfa.forall A
           (λ (y : sttfa.etap (sttfa.p A)),
              sttfa.impl (connectives.Not (eq A x y))
              (connectives.Not (eq A y x))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (x : sttfa.etap (sttfa.p A)),
          λ (y : sttfa.etap (sttfa.p A)),
            λ (auto : sttfa.eps (connectives.Not (eq A x y))),
              connectives.nmk (eq A y x)
              (λ (auto' : sttfa.eps (eq A y x)),
                 absurd (eq A x y)
                 (rewrite_r A x
                  (λ (__ : sttfa.etap (sttfa.p A)), eq A x __)
                  (refl A x) y auto')
                 auto);
symbol proj1
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl (connectives.And A B) A)))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        λ (B : sttfa.etap (sttfa.p sttfa.bool)),
          λ (AB : sttfa.eps (connectives.And A B)),
            connectives.match_And_prop A B A
            (λ (_x_120 : sttfa.eps A), λ (_x_119 : sttfa.eps B), _x_120) AB;
symbol proj2
  : sttfa.eps
    (sttfa.forall sttfa.bool
     (λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        sttfa.forall sttfa.bool
        (λ (B : sttfa.etap (sttfa.p sttfa.bool)),
           sttfa.impl (connectives.And A B) B)))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        λ (B : sttfa.etap (sttfa.p sttfa.bool)),
          λ (AB : sttfa.eps (connectives.And A B)),
            connectives.match_And_prop A B B
            (λ (_x_120 : sttfa.eps A), λ (_x_119 : sttfa.eps B), _x_119) AB;
symbol decidable : sttfa.etap (sttfa.p (sttfa.arrow sttfa.bool sttfa.bool))
  ≔ λ (A : sttfa.etap (sttfa.p sttfa.bool)),
        connectives.Or A (connectives.Not A);
