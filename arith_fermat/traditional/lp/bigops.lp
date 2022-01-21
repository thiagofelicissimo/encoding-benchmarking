require tests.sttfa as sttfa;
require tests.connectives as connectives;
require tests.bool as bool;
require tests.div_mod as div_mod;
require tests.leibniz as leibniz;
require tests.logic as logic;
require tests.nat as nat;
symbol sameF_upto
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow nat.nat
         (sttfa.arrow (sttfa.arrow nat.nat A)
          (sttfa.arrow (sttfa.arrow nat.nat A) sttfa.bool)))))
  ≔ λ (A : sttfa.{|type|}),
        λ (k : sttfa.etap (sttfa.p nat.nat)),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
            λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
              sttfa.forall nat.nat
              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.lt i k) (logic.eq A (f i) (g i)));
symbol sameF_p
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow nat.nat
         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
          (sttfa.arrow (sttfa.arrow nat.nat A)
           (sttfa.arrow (sttfa.arrow nat.nat A) sttfa.bool))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (k : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
              λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
                sttfa.forall nat.nat
                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                   sttfa.impl (nat.lt i k)
                   (sttfa.impl (logic.eq bool.bool (p i) bool.true)
                    (logic.eq A (f i) (g i))));
symbol sameF_upto_le
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat.nat A)
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
           sttfa.forall (sttfa.arrow nat.nat A)
           (λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
              sttfa.forall nat.nat
              (λ (n : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.forall nat.nat
                 (λ (m : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.impl (nat.le n m)
                    (sttfa.impl (sameF_upto A m f g)
                     (sameF_upto A n f g))))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
          λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
            λ (n : sttfa.etap (sttfa.p nat.nat)),
              λ (m : sttfa.etap (sttfa.p nat.nat)),
                λ (lenm : sttfa.eps (nat.le n m)),
                  λ (samef : sttfa.eps (sameF_upto A m f g)),
                    λ (i : sttfa.etap (sttfa.p nat.nat)),
                      λ (ltin : sttfa.eps (nat.lt i n)),
                        samef i (nat.lt_to_le_to_lt i n m ltin lenm);
symbol sameF_p_le
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat.nat bool.bool)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           sttfa.forall (sttfa.arrow nat.nat A)
           (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
              sttfa.forall (sttfa.arrow nat.nat A)
              (λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
                 sttfa.forall nat.nat
                 (λ (n : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.forall nat.nat
                    (λ (m : sttfa.etap (sttfa.p nat.nat)),
                       sttfa.impl (nat.le n m)
                       (sttfa.impl (sameF_p A m p f g)
                        (sameF_p A n p f g)))))))))
  ≔ λ (A : sttfa.{|type|}),
        λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
            λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat A))),
              λ (n : sttfa.etap (sttfa.p nat.nat)),
                λ (m : sttfa.etap (sttfa.p nat.nat)),
                  λ (lenm : sttfa.eps (nat.le n m)),
                    λ (samef : sttfa.eps (sameF_p A m p f g)),
                      λ (i : sttfa.etap (sttfa.p nat.nat)),
                        λ (ltin : sttfa.eps (nat.lt i n)),
                          λ
                            (
                            pi : sttfa.eps
                                 (logic.eq bool.bool (p i) bool.true)
                            ),
                            samef i (nat.lt_to_le_to_lt i n m ltin lenm)
                            (logic.rewrite_r bool.bool bool.true
                             (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                logic.eq bool.bool __ bool.true)
                             (logic.refl bool.bool bool.true) (p i) pi);
constant symbol bigop
  : sttfa.etap
    (sttfa.forallK
     (λ (H : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow nat.nat
         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
          (sttfa.arrow H
           (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
            (sttfa.arrow (sttfa.arrow nat.nat H) H)))))));
constant symbol bigop_body
  : sttfa.etap
    (sttfa.forallK
     (λ (H : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow nat.nat
         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
          (sttfa.arrow H
           (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
            (sttfa.arrow (sttfa.arrow nat.nat H) H)))))));
constant symbol axiom_bigop_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        connectives.equal
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop H nat.O) (bigop_body H nat.O)));
symbol eq_bigop_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop H nat.O) (bigop_body H nat.O)))
  ≔ λ (H : sttfa.{|type|}),
        connectives.equal_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop H nat.O) (bigop_body H nat.O) (axiom_bigop_O H);
symbol sym_eq_bigop_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop_body H nat.O) (bigop H nat.O)))
  ≔ λ (H : sttfa.{|type|}),
        leibniz.sym_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop H nat.O) (bigop_body H nat.O)
        (eq_bigop_O H);
constant symbol axiom_bigop_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           connectives.equal
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (bigop H (nat.S n)) (bigop_body H (nat.S n)))));
symbol eq_bigop_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (bigop H (nat.S n)) (bigop_body H (nat.S n)))))
  ≔ λ (H : sttfa.{|type|}),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          connectives.equal_leibniz
          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
           (sttfa.arrow H
            (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
             (sttfa.arrow (sttfa.arrow nat.nat H) H))))
          (bigop H (nat.S n)) (bigop_body H (nat.S n))
          (axiom_bigop_S H n);
symbol sym_eq_bigop_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (bigop_body H (nat.S n)) (bigop H (nat.S n)))))
  ≔ λ (H : sttfa.{|type|}),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          leibniz.sym_leibniz
          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
           (sttfa.arrow H
            (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
             (sttfa.arrow (sttfa.arrow nat.nat H) H))))
          (bigop H (nat.S n)) (bigop_body H (nat.S n))
          (eq_bigop_S H n);
constant symbol axiom_bigop_body_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        connectives.equal
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop_body H nat.O)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           λ (nil : sttfa.etap (sttfa.p H)),
             λ
               (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))),
               λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))), nil)));
symbol eq_bigop_body_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop_body H nat.O)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           λ (nil : sttfa.etap (sttfa.p H)),
             λ
               (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))),
               λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))), nil)))
  ≔ λ (H : sttfa.{|type|}),
        connectives.equal_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop_body H nat.O)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           λ (nil : sttfa.etap (sttfa.p H)),
             λ
               (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))),
               λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))), nil)
        (axiom_bigop_body_O H);
symbol sym_eq_bigop_body_O
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           λ (nil : sttfa.etap (sttfa.p H)),
             λ
               (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))),
               λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))), nil)
        (bigop_body H nat.O)))
  ≔ λ (H : sttfa.{|type|}),
        leibniz.sym_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow H
          (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
           (sttfa.arrow (sttfa.arrow nat.nat H) H))))
        (bigop_body H nat.O)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           λ (nil : sttfa.etap (sttfa.p H)),
             λ
               (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))),
               λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))), nil)
        (eq_bigop_body_O H);
constant symbol axiom_bigop_body_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           connectives.equal
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (bigop_body H (nat.S n))
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (nil : sttfa.etap (sttfa.p H)),
                λ
                  (
                  op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))
                  ),
                  λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))),
                    bool.match_bool_type H
                    (op (f n) (bigop H n p nil op f))
                    (bigop H n p nil op f) (p n)))));
symbol eq_bigop_body_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (bigop_body H (nat.S n))
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (nil : sttfa.etap (sttfa.p H)),
                λ
                  (
                  op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))
                  ),
                  λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))),
                    bool.match_bool_type H
                    (op (f n) (bigop H n p nil op f))
                    (bigop H n p nil op f) (p n)))))
  ≔ λ (H : sttfa.{|type|}),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          connectives.equal_leibniz
          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
           (sttfa.arrow H
            (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
             (sttfa.arrow (sttfa.arrow nat.nat H) H))))
          (bigop_body H (nat.S n))
          (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
             λ (nil : sttfa.etap (sttfa.p H)),
               λ
                 (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))
                 ),
                 λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))),
                   bool.match_bool_type H
                   (op (f n) (bigop H n p nil op f))
                   (bigop H n p nil op f) (p n))
          (axiom_bigop_body_S H n);
symbol sym_eq_bigop_body_S
  : sttfa.eps
    (sttfa.forallP
     (λ (H : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz
           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
            (sttfa.arrow H
             (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
              (sttfa.arrow (sttfa.arrow nat.nat H) H))))
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (nil : sttfa.etap (sttfa.p H)),
                λ
                  (
                  op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))
                  ),
                  λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))),
                    bool.match_bool_type H
                    (op (f n) (bigop H n p nil op f))
                    (bigop H n p nil op f) (p n))
           (bigop_body H (nat.S n)))))
  ≔ λ (H : sttfa.{|type|}),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          leibniz.sym_leibniz
          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
           (sttfa.arrow H
            (sttfa.arrow (sttfa.arrow H (sttfa.arrow H H))
             (sttfa.arrow (sttfa.arrow nat.nat H) H))))
          (bigop_body H (nat.S n))
          (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
             λ (nil : sttfa.etap (sttfa.p H)),
               λ
                 (op : sttfa.etap (sttfa.p (sttfa.arrow H (sttfa.arrow H H)))
                 ),
                 λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat H))),
                   bool.match_bool_type H
                   (op (f n) (bigop H n p nil op f))
                   (bigop H n p nil op f) (p n))
          (eq_bigop_body_S H n);
symbol bigop_Strue
  : sttfa.eps
    (sttfa.forallP
     (λ (B : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (k : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall B
              (λ (nil : sttfa.etap (sttfa.p B)),
                 sttfa.forall (sttfa.arrow B (sttfa.arrow B B))
                 (λ
                    (
                    op : sttfa.etap
                         (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))
                    ),
                    sttfa.forall (sttfa.arrow nat.nat B)
                    (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                       sttfa.impl (logic.eq bool.bool (p k) bool.true)
                       (logic.eq B
                        (bigop B (nat.S k)
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                        (op (f k)
                         (bigop B k
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))))))))
  ≔ λ (B : sttfa.{|type|}),
        λ (k : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (nil : sttfa.etap (sttfa.p B)),
              λ
                (op : sttfa.etap (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))),
                λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                  sym_eq_bigop_S B k
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                           (sttfa.arrow B
                            (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                             (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                     ),
                     sttfa.impl (logic.eq bool.bool (p k) bool.true)
                     (logic.eq B
                      (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                      (op (f k)
                       (bigop B k
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))
                  (sym_eq_bigop_body_S B k
                   (λ
                      (
                      y : sttfa.etap
                          (sttfa.p
                           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                            (sttfa.arrow B
                             (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                              (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                      ),
                      sttfa.impl (logic.eq bool.bool (p k) bool.true)
                      (logic.eq B
                       (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                       (op (f k)
                        (bigop B k
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))
                   (λ (H : sttfa.eps (logic.eq bool.bool (p k) bool.true)),
                      logic.eq_ind_r bool.bool bool.true
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq B
                         (bool.match_bool_type B
                          (op (f k)
                           (bigop B k
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                          (bigop B k
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                           op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                          x)
                         (op (f k)
                          (bigop B k
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                           op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                      (bool.eq_match_bool_type_true B
                       (op (f k)
                        (bigop B k
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                       (bigop B k
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                       (λ (y : sttfa.etap (sttfa.p B)),
                          logic.eq B
                          (bool.match_bool_type B
                           (op (f k)
                            (bigop B k
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                             op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                           (bigop B k
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           bool.true)
                          y)
                       (logic.refl B
                        (bool.match_bool_type B
                         (op (f k)
                          (bigop B k
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                           op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                         (bigop B k
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                         bool.true)))
                      (p k) H));
symbol bigop_Sfalse
  : sttfa.eps
    (sttfa.forallP
     (λ (B : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (k : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall B
              (λ (nil : sttfa.etap (sttfa.p B)),
                 sttfa.forall (sttfa.arrow B (sttfa.arrow B B))
                 (λ
                    (
                    op : sttfa.etap
                         (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))
                    ),
                    sttfa.forall (sttfa.arrow nat.nat B)
                    (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                       sttfa.impl (logic.eq bool.bool (p k) bool.false)
                       (logic.eq B
                        (bigop B (nat.S k)
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                        (bigop B k
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))))))))
  ≔ λ (B : sttfa.{|type|}),
        λ (k : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (nil : sttfa.etap (sttfa.p B)),
              λ
                (op : sttfa.etap (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))),
                λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                  sym_eq_bigop_S B k
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                           (sttfa.arrow B
                            (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                             (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                     ),
                     sttfa.impl (logic.eq bool.bool (p k) bool.false)
                     (logic.eq B
                      (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                      (bigop B k
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                  (sym_eq_bigop_body_S B k
                   (λ
                      (
                      y : sttfa.etap
                          (sttfa.p
                           (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                            (sttfa.arrow B
                             (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                              (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                      ),
                      sttfa.impl (logic.eq bool.bool (p k) bool.false)
                      (logic.eq B
                       (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                       (bigop B k
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                   (λ (H : sttfa.eps (logic.eq bool.bool (p k) bool.false)),
                      logic.eq_ind_r bool.bool bool.false
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq B
                         (bool.match_bool_type B
                          (op (f k)
                           (bigop B k
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                          (bigop B k
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                           op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                          x)
                         (bigop B k
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                      (bool.eq_match_bool_type_false B
                       (op (f k)
                        (bigop B k
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                       (bigop B k
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                       (λ (y : sttfa.etap (sttfa.p B)),
                          logic.eq B
                          (bool.match_bool_type B
                           (op (f k)
                            (bigop B k
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                             op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                           (bigop B k
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           bool.false)
                          y)
                       (logic.refl B
                        (bool.match_bool_type B
                         (op (f k)
                          (bigop B k
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil
                           op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                         (bigop B k
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), p i) nil op
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                         bool.false)))
                      (p k) H));
symbol same_bigop
  : sttfa.eps
    (sttfa.forallP
     (λ (B : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (k : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall (sttfa.arrow nat.nat bool.bool)
              (λ
                 (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                 sttfa.forall B
                 (λ (nil : sttfa.etap (sttfa.p B)),
                    sttfa.forall (sttfa.arrow B (sttfa.arrow B B))
                    (λ
                       (
                       op : sttfa.etap
                            (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))
                       ),
                       sttfa.forall (sttfa.arrow nat.nat B)
                       (λ
                          (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                          sttfa.forall (sttfa.arrow nat.nat B)
                          (λ
                             (
                             g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))
                             ),
                             sttfa.impl (sameF_upto bool.bool k p1 p2)
                             (sttfa.impl (sameF_p B k p1 f g)
                              (logic.eq B
                               (bigop B k
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                               (bigop B k
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))))))))))
  ≔ λ (B : sttfa.{|type|}),
        λ (k : sttfa.etap (sttfa.p nat.nat)),
          λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (nil : sttfa.etap (sttfa.p B)),
                λ
                  (
                  op : sttfa.etap (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))
                  ),
                  λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                    λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                      nat.nat_ind
                      (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
                         sttfa.impl
                         (sameF_upto bool.bool _x_365 p1 p2)
                         (sttfa.impl (sameF_p B _x_365 p1 f g)
                          (logic.eq B
                           (bigop B _x_365
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           (bigop B _x_365
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i) nil
                            op (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                      (sym_eq_bigop_O B
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p
                               (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                                (sttfa.arrow B
                                 (sttfa.arrow
                                  (sttfa.arrow B (sttfa.arrow B B))
                                  (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                          ),
                          sttfa.impl
                          (sameF_upto bool.bool nat.O p1 p2)
                          (sttfa.impl (sameF_p B nat.O p1 f g)
                           (logic.eq B
                            (bigop B nat.O
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                             nil op
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                            (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                             nil op
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                       (sym_eq_bigop_body_O B
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p
                                (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                                 (sttfa.arrow B
                                  (sttfa.arrow
                                   (sttfa.arrow B (sttfa.arrow B B))
                                   (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                           ),
                           sttfa.impl
                           (sameF_upto bool.bool nat.O p1 p2)
                           (sttfa.impl (sameF_p B nat.O p1 f g)
                            (logic.eq B
                             (bigop B nat.O
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                              nil op
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                             (y (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                              nil op
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                        (eq_bigop_body_O B
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p
                                 (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                                  (sttfa.arrow B
                                   (sttfa.arrow
                                    (sttfa.arrow B (sttfa.arrow B B))
                                    (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                            ),
                            sttfa.impl
                            (sameF_upto bool.bool nat.O p1 p2)
                            (sttfa.impl (sameF_p B nat.O p1 f g)
                             (logic.eq B
                              (bigop B nat.O
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                               nil op
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                              (y
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                               nil op
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))
                         (eq_bigop_O B
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p
                                  (sttfa.arrow
                                   (sttfa.arrow nat.nat bool.bool)
                                   (sttfa.arrow B
                                    (sttfa.arrow
                                     (sttfa.arrow B (sttfa.arrow B B))
                                     (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                             ),
                             sttfa.impl
                             (sameF_upto bool.bool nat.O p1 p2)
                             (sttfa.impl (sameF_p B nat.O p1 f g)
                              (logic.eq B
                               (bigop B nat.O
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                               (y
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))
                          (λ
                             (
                             auto : sttfa.eps
                                    (sameF_upto bool.bool nat.O p1 p2)
                             ),
                             λ
                               (
                               auto' : sttfa.eps
                                       (sameF_p B nat.O p1 f g)
                               ),
                               logic.refl B
                               (bigop B nat.O
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))))
                      (λ (n : sttfa.etap (sttfa.p nat.nat)),
                         sym_eq_bigop_S B n
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p
                                 (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                                  (sttfa.arrow B
                                   (sttfa.arrow
                                    (sttfa.arrow B (sttfa.arrow B B))
                                    (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                            ),
                            sttfa.impl
                            (sttfa.impl (sameF_upto bool.bool n p1 p2)
                             (sttfa.impl (sameF_p B n p1 f g)
                              (logic.eq B
                               (bigop B n
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                               (bigop B n
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                            (sttfa.impl
                             (sameF_upto bool.bool (nat.S n) p1 p2)
                             (sttfa.impl (sameF_p B (nat.S n) p1 f g)
                              (logic.eq B
                               (bigop B (nat.S n)
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                               (y
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                nil op
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), g i))))))
                         (sym_eq_bigop_S B n
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p
                                  (sttfa.arrow
                                   (sttfa.arrow nat.nat bool.bool)
                                   (sttfa.arrow B
                                    (sttfa.arrow
                                     (sttfa.arrow B (sttfa.arrow B B))
                                     (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                             ),
                             sttfa.impl
                             (sttfa.impl
                              (sameF_upto bool.bool n p1 p2)
                              (sttfa.impl (sameF_p B n p1 f g)
                               (logic.eq B
                                (bigop B n
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                 nil op
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                                (bigop B n
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                 nil op
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                             (sttfa.impl
                              (sameF_upto bool.bool (nat.S n) p1 p2)
                              (sttfa.impl (sameF_p B (nat.S n) p1 f g)
                               (logic.eq B
                                (y
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                 nil op
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                                (bigop_body B (nat.S n)
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                 nil op
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), g i))))))
                          (sym_eq_bigop_body_S B n
                           (λ
                              (
                              y : sttfa.etap
                                  (sttfa.p
                                   (sttfa.arrow
                                    (sttfa.arrow nat.nat bool.bool)
                                    (sttfa.arrow B
                                     (sttfa.arrow
                                      (sttfa.arrow B (sttfa.arrow B B))
                                      (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                              ),
                              sttfa.impl
                              (sttfa.impl
                               (sameF_upto bool.bool n p1 p2)
                               (sttfa.impl (sameF_p B n p1 f g)
                                (logic.eq B
                                 (bigop B n
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     p1 i)
                                  nil op
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                                 (bigop B n
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     p2 i)
                                  nil op
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), g i)))))
                              (sttfa.impl
                               (sameF_upto bool.bool (nat.S n) p1 p2)
                               (sttfa.impl
                                (sameF_p B (nat.S n) p1 f g)
                                (logic.eq B
                                 (y
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     p1 i)
                                  nil op
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                                 (bigop_body B (nat.S n)
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     p2 i)
                                  nil op
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), g i))))))
                           (sym_eq_bigop_body_S B n
                            (λ
                               (
                               y : sttfa.etap
                                   (sttfa.p
                                    (sttfa.arrow
                                     (sttfa.arrow nat.nat bool.bool)
                                     (sttfa.arrow B
                                      (sttfa.arrow
                                       (sttfa.arrow B (sttfa.arrow B B))
                                       (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                               ),
                               sttfa.impl
                               (sttfa.impl
                                (sameF_upto bool.bool n p1 p2)
                                (sttfa.impl (sameF_p B n p1 f g)
                                 (logic.eq B
                                  (bigop B n
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      p1 i)
                                   nil op
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      f i))
                                  (bigop B n
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      p2 i)
                                   nil op
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      g i)))))
                               (sttfa.impl
                                (sameF_upto bool.bool (nat.S n) p1 p2)
                                (sttfa.impl
                                 (sameF_p B (nat.S n) p1 f g)
                                 (logic.eq B
                                  ((λ
                                      (
                                      p : sttfa.etap
                                          (sttfa.p
                                           (sttfa.arrow nat.nat bool.bool))
                                      ),
                                      λ (nil0 : sttfa.etap (sttfa.p B)),
                                        λ
                                          (
                                          op0 : sttfa.etap
                                                (sttfa.p
                                                 (sttfa.arrow B
                                                  (sttfa.arrow B B)))
                                          ),
                                          λ
                                            (
                                            f0 : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat B))
                                            ),
                                            bool.match_bool_type B
                                            (op0 (f0 n)
                                             (bigop B n p nil0 op0 f0))
                                            (bigop B n p nil0 op0 f0)
                                            (p n))
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      p1 i)
                                   nil op
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      f i))
                                  (y
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      p2 i)
                                   nil op
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      g i))))))
                            (λ
                               (
                               Hind : sttfa.eps
                                      (sttfa.impl
                                       (sameF_upto bool.bool n p1 p2)
                                       (sttfa.impl
                                        (sameF_p B n p1 f g)
                                        (logic.eq B
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p1 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), f i))
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), g i)))))
                               ),
                               λ
                                 (
                                 samep : sttfa.eps
                                         (sameF_upto bool.bool
                                          (nat.S n) p1 p2)
                                 ),
                                 λ
                                   (
                                   samef : sttfa.eps
                                           (sameF_p B (nat.S n) p1 f g)
                                   ),
                                   logic.eq_ind_r B
                                   (bigop B n
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       p2 i)
                                    nil op
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       g i))
                                   (λ (x : sttfa.etap (sttfa.p B)),
                                      logic.eq B
                                      (bool.match_bool_type B (op (f n) x) x
                                       (p1 n))
                                      (bool.match_bool_type B
                                       (op (g n)
                                        (bigop B n
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), p2 i)
                                         nil op
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), g i)))
                                       (bigop B n
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           p2 i)
                                        nil op
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           g i))
                                       (p2 n)))
                                   (logic.eq_ind bool.bool (p1 n)
                                    (λ
                                       (x_1 : sttfa.etap (sttfa.p bool.bool)),
                                       logic.eq B
                                       (bool.match_bool_type B
                                        (op (f n)
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), g i)))
                                        (bigop B n
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), p2 i)
                                         nil op
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), g i))
                                        (p1 n))
                                       (bool.match_bool_type B
                                        (op (g n)
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), g i)))
                                        (bigop B n
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), p2 i)
                                         nil op
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), g i))
                                        x_1))
                                    (connectives.match_Or_prop
                                     (logic.eq bool.bool (p1 n) bool.true)
                                     (logic.eq bool.bool (p1 n) bool.false)
                                     (logic.eq B
                                      (bool.match_bool_type B
                                       (op (f n)
                                        (bigop B n
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), p2 i)
                                         nil op
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), g i)))
                                       (bigop B n
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           p2 i)
                                        nil op
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           g i))
                                       (p1 n))
                                      (bool.match_bool_type B
                                       (op (g n)
                                        (bigop B n
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), p2 i)
                                         nil op
                                         (λ
                                            (i : sttfa.etap (sttfa.p nat.nat)
                                            ), g i)))
                                       (bigop B n
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           p2 i)
                                        nil op
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           g i))
                                       (p1 n)))
                                     (λ
                                        (
                                        H1 : sttfa.eps
                                             (logic.eq bool.bool (p1 n)
                                              bool.true)
                                        ),
                                        logic.eq_ind_r bool.bool bool.true
                                        (λ
                                           (
                                           x : sttfa.etap (sttfa.p bool.bool)
                                           ),
                                           logic.eq B
                                           (bool.match_bool_type B
                                            (op (f n)
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i)))
                                            (bigop B n
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), p2 i)
                                             nil op
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), g i))
                                            x)
                                           (bool.match_bool_type B
                                            (op (g n)
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i)))
                                            (bigop B n
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), p2 i)
                                             nil op
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), g i))
                                            x))
                                        (bool.sym_eq_match_bool_type_true B
                                         (op (f n)
                                          (bigop B n
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), p2 i)
                                           nil op
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), g i)))
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), g i))
                                         (λ (y : sttfa.etap (sttfa.p B)),
                                            logic.eq B y
                                            (bool.match_bool_type B
                                             (op (g n)
                                              (bigop B n
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), p2 i)
                                               nil op
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), g i)))
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i))
                                             bool.true))
                                         (bool.sym_eq_match_bool_type_true B
                                          (op (g n)
                                           (bigop B n
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), p2 i)
                                            nil op
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), g i)))
                                          (bigop B n
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), p2 i)
                                           nil op
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), g i))
                                          (λ (y : sttfa.etap (sttfa.p B)),
                                             logic.eq B
                                             (op (f n)
                                              (bigop B n
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), p2 i)
                                               nil op
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), g i)))
                                             y)
                                          (logic.eq_ind B (f n)
                                           (λ
                                              (x_1 : sttfa.etap (sttfa.p B)),
                                              logic.eq B
                                              (op (f n)
                                               (bigop B n
                                                (λ
                                                   (
                                                   i : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                   ), p2 i)
                                                nil op
                                                (λ
                                                   (
                                                   i : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                   ), g i)))
                                              (op x_1
                                               (bigop B n
                                                (λ
                                                   (
                                                   i : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                   ), p2 i)
                                                nil op
                                                (λ
                                                   (
                                                   i : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                   ), g i))))
                                           (logic.refl B
                                            (op (f n)
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i))))
                                           (g n)
                                           (samef n (nat.le_n (nat.S n)) H1))))
                                        (p1 n) H1)
                                     (λ
                                        (
                                        H1 : sttfa.eps
                                             (logic.eq bool.bool (p1 n)
                                              bool.false)
                                        ),
                                        logic.eq_ind_r bool.bool bool.false
                                        (λ
                                           (
                                           x : sttfa.etap (sttfa.p bool.bool)
                                           ),
                                           logic.eq B
                                           (bool.match_bool_type B
                                            (op (f n)
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i)))
                                            (bigop B n
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), p2 i)
                                             nil op
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), g i))
                                            x)
                                           (bool.match_bool_type B
                                            (op (g n)
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i)))
                                            (bigop B n
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), p2 i)
                                             nil op
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ), g i))
                                            x))
                                        (bool.sym_eq_match_bool_type_false B
                                         (op (f n)
                                          (bigop B n
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), p2 i)
                                           nil op
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), g i)))
                                         (bigop B n
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          nil op
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), g i))
                                         (λ (y : sttfa.etap (sttfa.p B)),
                                            logic.eq B y
                                            (bool.match_bool_type B
                                             (op (g n)
                                              (bigop B n
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), p2 i)
                                               nil op
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ), g i)))
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i))
                                             bool.false))
                                         (bool.sym_eq_match_bool_type_false B
                                          (op (g n)
                                           (bigop B n
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), p2 i)
                                            nil op
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), g i)))
                                          (bigop B n
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), p2 i)
                                           nil op
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ), g i))
                                          (λ (y : sttfa.etap (sttfa.p B)),
                                             logic.eq B
                                             (bigop B n
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), p2 i)
                                              nil op
                                              (λ
                                                 (
                                                 i : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), g i))
                                             y)
                                          (logic.refl B
                                           (bigop B n
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), p2 i)
                                            nil op
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ), g i)))))
                                        (p1 n) H1)
                                     (bool.true_or_false (p1 n)))
                                    (p2 n) (samep n (nat.le_n (nat.S n))))
                                   (bigop B n
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       p1 i)
                                    nil op
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       f i))
                                   (Hind
                                    (sameF_upto_le bool.bool p1 p2 n
                                     (nat.S n)
                                     (logic.eq_coerc
                                      (nat.le (nat.pred (nat.S n)) (nat.S n))
                                      (nat.le n (nat.S n))
                                      (nat.le_pred_n (nat.S n))
                                      (logic.rewrite_l nat.nat n
                                       (λ
                                          (__ : sttfa.etap (sttfa.p nat.nat)),
                                          logic.eq sttfa.bool
                                          (nat.le __ (nat.S n))
                                          (nat.le n (nat.S n)))
                                       (logic.refl sttfa.bool
                                        (nat.le n (nat.S n)))
                                       (nat.pred (nat.S n)) (nat.pred_Sn n)))
                                     samep)
                                    (sameF_p_le B p1 f g n (nat.S n)
                                     (logic.eq_coerc
                                      (nat.le (nat.pred (nat.S n)) (nat.S n))
                                      (nat.le n (nat.S n))
                                      (nat.le_pred_n (nat.S n))
                                      (logic.rewrite_l nat.nat n
                                       (λ
                                          (__ : sttfa.etap (sttfa.p nat.nat)),
                                          logic.eq sttfa.bool
                                          (nat.le __ (nat.S n))
                                          (nat.le n (nat.S n)))
                                       (logic.refl sttfa.bool
                                        (nat.le n (nat.S n)))
                                       (nat.pred (nat.S n)) (nat.pred_Sn n)))
                                     samef)))))))
                      k;
symbol bigop_false
  : sttfa.eps
    (sttfa.forallP
     (λ (B : sttfa.{|type|}),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall B
           (λ (nil : sttfa.etap (sttfa.p B)),
              sttfa.forall (sttfa.arrow B (sttfa.arrow B B))
              (λ
                 (op : sttfa.etap (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))
                 ),
                 sttfa.forall (sttfa.arrow nat.nat B)
                 (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                    logic.eq B
                    (bigop B n
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                     op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                    nil))))))
  ≔ λ (B : sttfa.{|type|}),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (nil : sttfa.etap (sttfa.p B)),
            λ (op : sttfa.etap (sttfa.p (sttfa.arrow B (sttfa.arrow B B)))),
              λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat B))),
                nat.nat_ind
                (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq B
                   (bigop B _x_365
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                    op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                   nil)
                (eq_bigop_body_O B
                 (λ
                    (
                    y : sttfa.etap
                        (sttfa.p
                         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                          (sttfa.arrow B
                           (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                            (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                    ),
                    logic.eq B
                    (bigop B nat.O
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                     op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                    (y (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false)
                     nil op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                 (eq_bigop_O B
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                           (sttfa.arrow B
                            (sttfa.arrow (sttfa.arrow B (sttfa.arrow B B))
                             (sttfa.arrow (sttfa.arrow nat.nat B) B)))))
                     ),
                     logic.eq B
                     (bigop B nat.O
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                      op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                     (y (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false)
                      nil op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                  (logic.refl B
                   (bigop B nat.O
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                    op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))))
                (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
                   λ
                     (
                     Hind : sttfa.eps
                            (logic.eq B
                             (bigop B n1
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 bool.false)
                              nil op
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                             nil)
                     ),
                     logic.eq_ind_r B
                     (bigop B n1
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                      op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                     (λ (x : sttfa.etap (sttfa.p B)), logic.eq B x nil)
                     (logic.rewrite_r B nil
                      (λ (__ : sttfa.etap (sttfa.p B)), logic.eq B __ nil)
                      (logic.refl B nil)
                      (bigop B n1
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false)
                       nil op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                      Hind)
                     (bigop B (nat.S n1)
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.false) nil
                      op (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                     (bigop_Sfalse B n1
                      (λ (__ : sttfa.etap (sttfa.p nat.nat)), bool.false)
                      nil op f (logic.refl bool.bool bool.false)))
                n;
constant symbol Aop
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}), sttfa.p (sttfa.arrow A sttfa.bool)));
constant symbol mk_Aop
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (nil : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A (sttfa.arrow A A))
           (λ (op : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
              sttfa.impl
              (sttfa.forall A
               (λ (a : sttfa.etap (sttfa.p A)), logic.eq A (op nil a) a))
              (sttfa.impl
               (sttfa.forall A
                (λ (a : sttfa.etap (sttfa.p A)), logic.eq A (op a nil) a))
               (sttfa.impl
                (sttfa.forall A
                 (λ (a : sttfa.etap (sttfa.p A)),
                    sttfa.forall A
                    (λ (b : sttfa.etap (sttfa.p A)),
                       sttfa.forall A
                       (λ (c : sttfa.etap (sttfa.p A)),
                          logic.eq A (op a (op b c)) (op (op a b) c)))))
                (Aop A nil)))))));
symbol assoc
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (a : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (b : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (c : sttfa.etap (sttfa.p nat.nat)),
              logic.eq nat.nat (nat.times a (nat.times b c))
              (nat.times (nat.times a b) c)))))
  ≔ λ (a : sttfa.etap (sttfa.p nat.nat)),
        λ (b : sttfa.etap (sttfa.p nat.nat)),
          λ (c : sttfa.etap (sttfa.p nat.nat)),
            logic.sym_eq nat.nat (nat.times (nat.times a b) c)
            (nat.times a (nat.times b c)) (nat.associative_times a b c);
symbol timesA : sttfa.eps (Aop nat.nat (nat.S nat.O))
  ≔ mk_Aop nat.nat (nat.S nat.O) nat.times
      (λ (a : sttfa.etap (sttfa.p nat.nat)),
         nat.sym_eq_times (nat.S nat.O)
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
            logic.eq nat.nat (y a) a)
         (nat.sym_eq_filter_nat_type_S (sttfa.arrow nat.nat nat.nat)
          nat.times_body nat.O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
             logic.eq nat.nat (y a) a)
          (nat.sym_eq_times_body_S nat.O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              logic.eq nat.nat (y a) a)
           (nat.sym_eq_times nat.O
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
               logic.eq nat.nat (nat.plus a (y a)) a)
            (nat.sym_eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
             nat.times_body
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                logic.eq nat.nat (nat.plus a (y a)) a)
             (nat.sym_eq_times_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                 logic.eq nat.nat (nat.plus a (y a)) a)
              (logic.sym_eq nat.nat a (nat.plus a nat.O) (nat.plus_n_O a))))))))
      (λ (n : sttfa.etap (sttfa.p nat.nat)),
         logic.sym_eq nat.nat n (nat.times n (nat.S nat.O)) (nat.times_n_1 n))
      (λ (a : sttfa.etap (sttfa.p nat.nat)),
         λ (b : sttfa.etap (sttfa.p nat.nat)),
           λ (c : sttfa.etap (sttfa.p nat.nat)),
             logic.sym_eq nat.nat (nat.times (nat.times a b) c)
             (nat.times a (nat.times b c)) (nat.associative_times a b c));
symbol bigop_I_gen
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (a : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (b : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall (sttfa.arrow nat.nat nat.nat)
              (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                 sttfa.impl (nat.le a b)
                 (logic.eq nat.nat
                  (bigop nat.nat (nat.minus b a)
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), p (nat.plus i a))
                   (nat.S nat.O) nat.times
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), f (nat.plus i a)))
                  (bigop nat.nat b
                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                      bool.andb (nat.leb a i) (p i))
                   (nat.S nat.O) nat.times
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat.nat)),
        λ (b : sttfa.etap (sttfa.p nat.nat)),
          nat.nat_ind
          (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
             sttfa.forall (sttfa.arrow nat.nat bool.bool)
             (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                sttfa.forall (sttfa.arrow nat.nat nat.nat)
                (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                   sttfa.impl (nat.le a _x_365)
                   (logic.eq nat.nat
                    (bigop nat.nat (nat.minus _x_365 a)
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), p (nat.plus i a))
                     (nat.S nat.O) nat.times
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), f (nat.plus i a)))
                    (bigop nat.nat _x_365
                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                        bool.andb (nat.leb a i) (p i))
                     (nat.S nat.O) nat.times
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))))
          (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
             λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
               sym_eq_bigop_O nat.nat
               (λ
                  (
                  y : sttfa.etap
                      (sttfa.p
                       (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                        (sttfa.arrow nat.nat
                         (sttfa.arrow
                          (sttfa.arrow nat.nat (sttfa.arrow nat.nat nat.nat))
                          (sttfa.arrow (sttfa.arrow nat.nat nat.nat) nat.nat)))))
                  ),
                  sttfa.impl (nat.le a nat.O)
                  (logic.eq nat.nat
                   (bigop nat.nat (nat.minus nat.O a)
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), p (nat.plus i a))
                    (nat.S nat.O) nat.times
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), f (nat.plus i a)))
                   (y
                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                       bool.andb (nat.leb a i) (p i))
                    (nat.S nat.O) nat.times
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
               (sym_eq_bigop_body_O nat.nat
                (λ
                   (
                   y : sttfa.etap
                       (sttfa.p
                        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                         (sttfa.arrow nat.nat
                          (sttfa.arrow
                           (sttfa.arrow nat.nat (sttfa.arrow nat.nat nat.nat))
                           (sttfa.arrow (sttfa.arrow nat.nat nat.nat) nat.nat)))))
                   ),
                   sttfa.impl (nat.le a nat.O)
                   (logic.eq nat.nat
                    (bigop nat.nat (nat.minus nat.O a)
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), p (nat.plus i a))
                     (nat.S nat.O) nat.times
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), f (nat.plus i a)))
                    (y
                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                        bool.andb (nat.leb a i) (p i))
                     (nat.S nat.O) nat.times
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                (eq_bigop_body_O nat.nat
                 (λ
                    (
                    y : sttfa.etap
                        (sttfa.p
                         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                          (sttfa.arrow nat.nat
                           (sttfa.arrow
                            (sttfa.arrow nat.nat
                             (sttfa.arrow nat.nat nat.nat))
                            (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                             nat.nat)))))
                    ),
                    sttfa.impl (nat.le a nat.O)
                    (logic.eq nat.nat
                     (bigop nat.nat (nat.minus nat.O a)
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         p (nat.plus i a))
                      (nat.S nat.O) nat.times
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         f (nat.plus i a)))
                     (y
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         p (nat.plus i a))
                      (nat.S nat.O) nat.times
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         f (nat.plus i a)))))
                 (eq_bigop_O nat.nat
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
                           (sttfa.arrow nat.nat
                            (sttfa.arrow
                             (sttfa.arrow nat.nat
                              (sttfa.arrow nat.nat nat.nat))
                             (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                              nat.nat)))))
                     ),
                     sttfa.impl (nat.le a nat.O)
                     (logic.eq nat.nat
                      (bigop nat.nat (nat.minus nat.O a)
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          p (nat.plus i a))
                       (nat.S nat.O) nat.times
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          f (nat.plus i a)))
                      (y
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          p (nat.plus i a))
                       (nat.S nat.O) nat.times
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          f (nat.plus i a)))))
                  (nat.eq_minus_body_O
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      sttfa.impl (nat.le a nat.O)
                      (logic.eq nat.nat
                       (bigop nat.nat (nat.minus nat.O a)
                        (λ (i : sttfa.etap (sttfa.p nat.nat)),
                           p (nat.plus i a))
                        (nat.S nat.O) nat.times
                        (λ (i : sttfa.etap (sttfa.p nat.nat)),
                           f (nat.plus i a)))
                       (bigop nat.nat (y a)
                        (λ (i : sttfa.etap (sttfa.p nat.nat)),
                           p (nat.plus i a))
                        (nat.S nat.O) nat.times
                        (λ (i : sttfa.etap (sttfa.p nat.nat)),
                           f (nat.plus i a)))))
                   (nat.eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
                    nat.minus_body
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       sttfa.impl (nat.le a nat.O)
                       (logic.eq nat.nat
                        (bigop nat.nat (nat.minus nat.O a)
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            p (nat.plus i a))
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            f (nat.plus i a)))
                        (bigop nat.nat (y a)
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            p (nat.plus i a))
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            f (nat.plus i a)))))
                    (nat.eq_minus nat.O
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                        ),
                        sttfa.impl (nat.le a nat.O)
                        (logic.eq nat.nat
                         (bigop nat.nat (nat.minus nat.O a)
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             p (nat.plus i a))
                          (nat.S nat.O) nat.times
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             f (nat.plus i a)))
                         (bigop nat.nat (y a)
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             p (nat.plus i a))
                          (nat.S nat.O) nat.times
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             f (nat.plus i a)))))
                     (λ (auto : sttfa.eps (nat.le a nat.O)),
                        logic.refl nat.nat
                        (bigop nat.nat (nat.minus nat.O a)
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            p (nat.plus i a))
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            f (nat.plus i a)))))))))))
          (λ (b0 : sttfa.etap (sttfa.p nat.nat)),
             λ
               (
               Hind : sttfa.eps
                      (sttfa.forall (sttfa.arrow nat.nat bool.bool)
                       (λ
                          (
                          p : sttfa.etap
                              (sttfa.p (sttfa.arrow nat.nat bool.bool))
                          ),
                          sttfa.forall (sttfa.arrow nat.nat nat.nat)
                          (λ
                             (
                             f : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat.nat nat.nat))
                             ),
                             sttfa.impl (nat.le a b0)
                             (logic.eq nat.nat
                              (bigop nat.nat (nat.minus b0 a)
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a)))
                              (bigop nat.nat b0
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (nat.leb a i) (p i))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))))
               ),
               λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                 λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                   λ (lea : sttfa.eps (nat.le a (nat.S b0))),
                     connectives.match_Or_prop (nat.lt a (nat.S b0))
                     (logic.eq nat.nat a (nat.S b0))
                     (logic.eq nat.nat
                      (bigop nat.nat (nat.minus (nat.S b0) a)
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          p (nat.plus i a))
                       (nat.S nat.O) nat.times
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          f (nat.plus i a)))
                      (bigop nat.nat (nat.S b0)
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          bool.andb (nat.leb a i) (p i))
                       (nat.S nat.O) nat.times
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                     (λ (Ha : sttfa.eps (nat.lt a (nat.S b0))),
                        connectives.match_Or_prop
                        (logic.eq bool.bool (p b0) bool.true)
                        (logic.eq bool.bool (p b0) bool.false)
                        (logic.eq nat.nat
                         (bigop nat.nat (nat.minus (nat.S b0) a)
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             p (nat.plus i a))
                          (nat.S nat.O) nat.times
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             f (nat.plus i a)))
                         (bigop nat.nat (nat.S b0)
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             bool.andb (nat.leb a i) (p i))
                          (nat.S nat.O) nat.times
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                        (λ
                           (
                           Hcase : sttfa.eps
                                   (logic.eq bool.bool (p b0) bool.true)
                           ),
                           logic.eq_ind_r nat.nat
                           (nat.times (f b0)
                            (bigop nat.nat b0
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                bool.andb (nat.leb a i) (p i))
                             (nat.S nat.O) nat.times
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                           (λ (x : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat
                              (bigop nat.nat (nat.minus (nat.S b0) a)
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a)))
                              x)
                           (logic.eq_ind_r nat.nat (nat.S (nat.minus b0 a))
                            (λ (x : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat
                               (bigop nat.nat x
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   p (nat.plus i a))
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   f (nat.plus i a)))
                               (nat.times (f b0)
                                (bigop nat.nat b0
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    bool.andb (nat.leb a i) (p i))
                                 (nat.S nat.O) nat.times
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                            (logic.eq_ind_r nat.nat
                             (nat.times (f (nat.plus (nat.minus b0 a) a))
                              (bigop nat.nat (nat.minus b0 a)
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a))))
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat x
                                (nat.times (f b0)
                                 (bigop nat.nat b0
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     bool.andb (nat.leb a i) (p i))
                                  (nat.S nat.O) nat.times
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))))
                             (logic.eq_f2 nat.nat nat.nat nat.nat nat.times
                              (f (nat.plus (nat.minus b0 a) a)) (f b0)
                              (bigop nat.nat (nat.minus b0 a)
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a)))
                              (bigop nat.nat b0
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (nat.leb a i) (p i))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                              (logic.eq_f nat.nat nat.nat f
                               (nat.plus (nat.minus b0 a) a) b0
                               (logic.eq_ind nat.nat b0
                                (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat x_1 b0)
                                (logic.refl nat.nat b0)
                                (nat.plus (nat.minus b0 a) a)
                                (nat.plus_minus_m_m b0 a
                                 (nat.le_S_S_to_le a b0 Ha))))
                              (Hind p f (nat.le_S_S_to_le a b0 Ha)))
                             (bigop nat.nat (nat.S (nat.minus b0 a))
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus i a))
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus i a)))
                             (bigop_Strue nat.nat (nat.minus b0 a)
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus __ a))
                              (nat.S nat.O) nat.times
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus __ a))
                              (logic.eq_ind nat.nat b0
                               (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq bool.bool (p x_1) bool.true)
                               (logic.rewrite_r bool.bool bool.true
                                (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                   logic.eq bool.bool __ bool.true)
                                (logic.refl bool.bool bool.true) (p b0) Hcase)
                               (nat.plus (nat.minus b0 a) a)
                               (nat.plus_minus_m_m b0 a
                                (nat.le_S_S_to_le a b0 Ha)))))
                            (nat.minus (nat.S b0) a)
                            (nat.match_nat_prop
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                sttfa.impl (nat.le __ b0)
                                (logic.eq nat.nat (nat.minus (nat.S b0) __)
                                 (nat.S (nat.minus b0 __))))
                             (λ (auto : sttfa.eps (nat.le nat.O b0)),
                                logic.rewrite_l nat.nat (nat.S b0)
                                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat __
                                   (nat.S (nat.minus b0 nat.O)))
                                (logic.rewrite_l nat.nat b0
                                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat (nat.S b0) (nat.S __))
                                 (logic.refl nat.nat (nat.S b0))
                                 (nat.minus b0 nat.O) (nat.minus_n_O b0))
                                (nat.minus (nat.S b0) nat.O)
                                (nat.minus_n_O (nat.S b0)))
                             (nat.sym_eq_minus (nat.S b0)
                              (λ
                                 (
                                 y : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                 ),
                                 sttfa.forall nat.nat
                                 (λ (n : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.le (nat.S n) b0)
                                    (logic.eq nat.nat (y (nat.S n))
                                     (nat.S (nat.minus b0 (nat.S n))))))
                              (nat.sym_eq_filter_nat_type_S
                               (sttfa.arrow nat.nat nat.nat) nat.minus_body
                               b0
                               (λ
                                  (
                                  y : sttfa.etap
                                      (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                  ),
                                  sttfa.forall nat.nat
                                  (λ (n : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.le (nat.S n) b0)
                                     (logic.eq nat.nat (y (nat.S n))
                                      (nat.S (nat.minus b0 (nat.S n))))))
                               (λ (a1 : sttfa.etap (sttfa.p nat.nat)),
                                  nat.sym_eq_minus_body_S b0
                                  (λ
                                     (
                                     y : sttfa.etap
                                         (sttfa.p
                                          (sttfa.arrow nat.nat nat.nat))
                                     ),
                                     sttfa.impl (nat.le (nat.S a1) b0)
                                     (logic.eq nat.nat (y (nat.S a1))
                                      (nat.S (nat.minus b0 (nat.S a1)))))
                                  (nat.sym_eq_match_nat_type_S nat.nat
                                   (nat.S b0)
                                   (λ (q : sttfa.etap (sttfa.p nat.nat)),
                                      nat.minus b0 q)
                                   a1
                                   (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                      sttfa.impl (nat.le (nat.S a1) b0)
                                      (logic.eq nat.nat y
                                       (nat.S (nat.minus b0 (nat.S a1)))))
                                   (λ
                                      (
                                      lta1 : sttfa.eps (nat.le (nat.S a1) b0)
                                      ),
                                      logic.eq_ind_r nat.nat
                                      (nat.pred (nat.minus b0 a1))
                                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                         logic.eq nat.nat (nat.minus b0 a1)
                                         (nat.S x))
                                      (logic.eq_ind_r nat.nat
                                       (nat.minus b0 a1)
                                       (λ
                                          (x : sttfa.etap (sttfa.p nat.nat)),
                                          logic.eq nat.nat (nat.minus b0 a1)
                                          x)
                                       (logic.refl nat.nat (nat.minus b0 a1))
                                       (nat.S (nat.pred (nat.minus b0 a1)))
                                       (nat.S_pred (nat.minus b0 a1)
                                        (nat.lt_plus_to_minus_r nat.O a1 b0
                                         (nat.sym_eq_plus nat.O
                                          (λ
                                             (
                                             y : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat
                                                   nat.nat))
                                             ), nat.le (nat.S (y a1)) b0)
                                          (nat.sym_eq_filter_nat_type_O
                                           (sttfa.arrow nat.nat nat.nat)
                                           nat.plus_body
                                           (λ
                                              (
                                              y : sttfa.etap
                                                  (sttfa.p
                                                   (sttfa.arrow nat.nat
                                                    nat.nat))
                                              ), nat.le (nat.S (y a1)) b0)
                                           (nat.sym_eq_plus_body_O
                                            (λ
                                               (
                                               y : sttfa.etap
                                                   (sttfa.p
                                                    (sttfa.arrow nat.nat
                                                     nat.nat))
                                               ), nat.le (nat.S (y a1)) b0)
                                            lta1))))))
                                      (nat.minus b0 (nat.S a1))
                                      (nat.eq_minus_S_pred b0 a1))))))
                             a (nat.le_S_S_to_le a b0 Ha)))
                           (bigop nat.nat (nat.S b0)
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a i) (p i))
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           (bigop_Strue nat.nat b0
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a __) (p __))
                            (nat.S nat.O) nat.times f
                            (logic.eq_ind_r bool.bool bool.true
                             (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                logic.eq bool.bool
                                (bool.andb (nat.leb a b0) x) bool.true)
                             (logic.eq_ind_r bool.bool bool.true
                              (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                 logic.eq bool.bool (bool.andb x bool.true)
                                 bool.true)
                              (bool.eq_match_bool_type_true bool.bool
                               bool.true bool.false
                               (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool
                                  (bool.match_bool_type bool.bool bool.true
                                   bool.false bool.true)
                                  y)
                               (logic.refl bool.bool
                                (bool.andb bool.true bool.true)))
                              (nat.leb a b0)
                              (nat.le_to_leb_true a b0
                               (nat.le_S_S_to_le a b0 Ha)))
                             (p b0) Hcase)))
                        (λ
                           (
                           Hcase : sttfa.eps
                                   (logic.eq bool.bool (p b0) bool.false)
                           ),
                           logic.eq_ind_r nat.nat
                           (bigop nat.nat b0
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a i) (p i))
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           (λ (x : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat
                              (bigop nat.nat (nat.minus (nat.S b0) a)
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a)))
                              x)
                           (logic.eq_ind_r nat.nat (nat.S (nat.minus b0 a))
                            (λ (x : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat
                               (bigop nat.nat x
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   p (nat.plus i a))
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   f (nat.plus i a)))
                               (bigop nat.nat b0
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   bool.andb (nat.leb a i) (p i))
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                            (logic.eq_ind_r nat.nat
                             (bigop nat.nat (nat.minus b0 a)
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus i a))
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus i a)))
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat x
                                (bigop nat.nat b0
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    bool.andb (nat.leb a i) (p i))
                                 (nat.S nat.O) nat.times
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                             (Hind p f (nat.le_S_S_to_le a b0 Ha))
                             (bigop nat.nat (nat.S (nat.minus b0 a))
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus i a))
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus i a)))
                             (bigop_Sfalse nat.nat (nat.minus b0 a)
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus __ a))
                              (nat.S nat.O) nat.times
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus __ a))
                              (logic.eq_ind nat.nat b0
                               (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq bool.bool (p x_1) bool.false)
                               (logic.rewrite_r bool.bool bool.false
                                (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                   logic.eq bool.bool __ bool.false)
                                (logic.refl bool.bool bool.false) (p b0)
                                Hcase)
                               (nat.plus (nat.minus b0 a) a)
                               (nat.plus_minus_m_m b0 a
                                (nat.le_S_S_to_le a b0 Ha)))))
                            (nat.minus (nat.S b0) a)
                            (nat.match_nat_prop
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                sttfa.impl (nat.le __ b0)
                                (logic.eq nat.nat (nat.minus (nat.S b0) __)
                                 (nat.S (nat.minus b0 __))))
                             (λ (auto : sttfa.eps (nat.le nat.O b0)),
                                logic.rewrite_l nat.nat (nat.S b0)
                                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat __
                                   (nat.S (nat.minus b0 nat.O)))
                                (logic.rewrite_l nat.nat b0
                                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat (nat.S b0) (nat.S __))
                                 (logic.refl nat.nat (nat.S b0))
                                 (nat.minus b0 nat.O) (nat.minus_n_O b0))
                                (nat.minus (nat.S b0) nat.O)
                                (nat.minus_n_O (nat.S b0)))
                             (nat.sym_eq_minus (nat.S b0)
                              (λ
                                 (
                                 y : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                 ),
                                 sttfa.forall nat.nat
                                 (λ (n : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.le (nat.S n) b0)
                                    (logic.eq nat.nat (y (nat.S n))
                                     (nat.S (nat.minus b0 (nat.S n))))))
                              (nat.sym_eq_filter_nat_type_S
                               (sttfa.arrow nat.nat nat.nat) nat.minus_body
                               b0
                               (λ
                                  (
                                  y : sttfa.etap
                                      (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                  ),
                                  sttfa.forall nat.nat
                                  (λ (n : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.le (nat.S n) b0)
                                     (logic.eq nat.nat (y (nat.S n))
                                      (nat.S (nat.minus b0 (nat.S n))))))
                               (λ (a1 : sttfa.etap (sttfa.p nat.nat)),
                                  nat.sym_eq_minus_body_S b0
                                  (λ
                                     (
                                     y : sttfa.etap
                                         (sttfa.p
                                          (sttfa.arrow nat.nat nat.nat))
                                     ),
                                     sttfa.impl (nat.le (nat.S a1) b0)
                                     (logic.eq nat.nat (y (nat.S a1))
                                      (nat.S (nat.minus b0 (nat.S a1)))))
                                  (nat.sym_eq_match_nat_type_S nat.nat
                                   (nat.S b0)
                                   (λ (q : sttfa.etap (sttfa.p nat.nat)),
                                      nat.minus b0 q)
                                   a1
                                   (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                      sttfa.impl (nat.le (nat.S a1) b0)
                                      (logic.eq nat.nat y
                                       (nat.S (nat.minus b0 (nat.S a1)))))
                                   (λ
                                      (
                                      lta1 : sttfa.eps (nat.le (nat.S a1) b0)
                                      ),
                                      logic.eq_ind_r nat.nat
                                      (nat.pred (nat.minus b0 a1))
                                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                         logic.eq nat.nat (nat.minus b0 a1)
                                         (nat.S x))
                                      (logic.eq_ind_r nat.nat
                                       (nat.minus b0 a1)
                                       (λ
                                          (x : sttfa.etap (sttfa.p nat.nat)),
                                          logic.eq nat.nat (nat.minus b0 a1)
                                          x)
                                       (logic.refl nat.nat (nat.minus b0 a1))
                                       (nat.S (nat.pred (nat.minus b0 a1)))
                                       (nat.S_pred (nat.minus b0 a1)
                                        (nat.lt_plus_to_minus_r nat.O a1 b0
                                         (nat.sym_eq_plus nat.O
                                          (λ
                                             (
                                             y : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat
                                                   nat.nat))
                                             ), nat.le (nat.S (y a1)) b0)
                                          (nat.sym_eq_filter_nat_type_O
                                           (sttfa.arrow nat.nat nat.nat)
                                           nat.plus_body
                                           (λ
                                              (
                                              y : sttfa.etap
                                                  (sttfa.p
                                                   (sttfa.arrow nat.nat
                                                    nat.nat))
                                              ), nat.le (nat.S (y a1)) b0)
                                           (nat.sym_eq_plus_body_O
                                            (λ
                                               (
                                               y : sttfa.etap
                                                   (sttfa.p
                                                    (sttfa.arrow nat.nat
                                                     nat.nat))
                                               ), nat.le (nat.S (y a1)) b0)
                                            lta1))))))
                                      (nat.minus b0 (nat.S a1))
                                      (nat.eq_minus_S_pred b0 a1))))))
                             a (nat.le_S_S_to_le a b0 Ha)))
                           (bigop nat.nat (nat.S b0)
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a i) (p i))
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                           (bigop_Sfalse nat.nat b0
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a __) (p __))
                            (nat.S nat.O) nat.times f
                            (logic.eq_ind_r bool.bool bool.false
                             (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                logic.eq bool.bool
                                (bool.andb (nat.leb a b0) x) bool.false)
                             (bool.match_bool_prop
                              (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                 logic.eq bool.bool (bool.andb __ bool.false)
                                 bool.false)
                              (bool.eq_match_bool_type_true bool.bool
                               bool.false bool.false
                               (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool
                                  (bool.match_bool_type bool.bool bool.false
                                   bool.false bool.true)
                                  y)
                               (logic.refl bool.bool
                                (bool.andb bool.true bool.false)))
                              (bool.eq_match_bool_type_false bool.bool
                               bool.false bool.false
                               (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool
                                  (bool.match_bool_type bool.bool bool.false
                                   bool.false bool.false)
                                  y)
                               (logic.refl bool.bool
                                (bool.andb bool.false bool.false)))
                              (nat.leb a b0))
                             (p b0) Hcase)))
                        (bool.true_or_false (p b0)))
                     (λ (Ha : sttfa.eps (logic.eq nat.nat a (nat.S b0))),
                        logic.eq_ind nat.nat a
                        (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (bigop nat.nat (nat.minus x_1 a)
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               p (nat.plus i a))
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               f (nat.plus i a)))
                           (bigop nat.nat x_1
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               bool.andb (nat.leb a i) (p i))
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                        (logic.eq_ind nat.nat nat.O
                         (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat
                            (bigop nat.nat x_1
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                p (nat.plus i a))
                             (nat.S nat.O) nat.times
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                f (nat.plus i a)))
                            (bigop nat.nat a
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                bool.andb (nat.leb a i) (p i))
                             (nat.S nat.O) nat.times
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                         (sym_eq_bigop_O nat.nat
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p
                                  (sttfa.arrow
                                   (sttfa.arrow nat.nat bool.bool)
                                   (sttfa.arrow nat.nat
                                    (sttfa.arrow
                                     (sttfa.arrow nat.nat
                                      (sttfa.arrow nat.nat nat.nat))
                                     (sttfa.arrow
                                      (sttfa.arrow nat.nat nat.nat) nat.nat)))))
                             ),
                             logic.eq nat.nat
                             (y
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 p (nat.plus i a))
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 f (nat.plus i a)))
                             (bigop nat.nat a
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 bool.andb (nat.leb a i) (p i))
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                          (sym_eq_bigop_body_O nat.nat
                           (λ
                              (
                              y : sttfa.etap
                                  (sttfa.p
                                   (sttfa.arrow
                                    (sttfa.arrow nat.nat bool.bool)
                                    (sttfa.arrow nat.nat
                                     (sttfa.arrow
                                      (sttfa.arrow nat.nat
                                       (sttfa.arrow nat.nat nat.nat))
                                      (sttfa.arrow
                                       (sttfa.arrow nat.nat nat.nat) nat.nat)))))
                              ),
                              logic.eq nat.nat
                              (y
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  p (nat.plus i a))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  f (nat.plus i a)))
                              (bigop nat.nat a
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (nat.leb a i) (p i))
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                           (logic.eq_ind nat.nat
                            (bigop nat.nat a
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                bool.false)
                             (nat.S nat.O) nat.times
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), f i))
                            (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat x_1
                               (bigop nat.nat a
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   bool.andb (nat.leb a i) (p i))
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                            (same_bigop nat.nat a
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                bool.false)
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                bool.andb (nat.leb a __) (p __))
                             (nat.S nat.O) nat.times f f
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                λ (ltia : sttfa.eps (nat.lt i a)),
                                  logic.eq_ind_r bool.bool bool.false
                                  (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                     logic.eq bool.bool bool.false
                                     (bool.andb x (p i)))
                                  (bool.sym_eq_match_bool_type_false
                                   bool.bool (p i) bool.false
                                   (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                      logic.eq bool.bool bool.false y)
                                   (logic.refl bool.bool bool.false))
                                  (nat.leb a i)
                                  (nat.not_le_to_leb_false a i
                                   (nat.lt_to_not_le i a ltia)))
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                λ (auto : sttfa.eps (nat.lt i a)),
                                  λ
                                    (
                                    auto' : sttfa.eps
                                            (logic.eq bool.bool bool.false
                                             bool.true)
                                    ), logic.refl nat.nat (f i)))
                            (nat.S nat.O)
                            (bigop_false nat.nat a (nat.S nat.O)
                             nat.times f))))
                         (nat.minus a a) (nat.minus_n_n a))
                        (nat.S b0) Ha)
                     (nat.le_to_or_lt_eq a (nat.S b0) lea))
          b;
constant symbol ACop
  : sttfa.etap
    (sttfa.forallK
     (λ (A : sttfa.{|type|}), sttfa.p (sttfa.arrow A sttfa.bool)));
constant symbol mk_ACop
  : sttfa.eps
    (sttfa.forallP
     (λ (A : sttfa.{|type|}),
        sttfa.forall A
        (λ (nil : sttfa.etap (sttfa.p A)),
           sttfa.forall (sttfa.arrow A (sttfa.arrow A A))
           (λ (op : sttfa.etap (sttfa.p (sttfa.arrow A (sttfa.arrow A A)))),
              sttfa.impl
              (sttfa.forall A
               (λ (a : sttfa.etap (sttfa.p A)), logic.eq A (op nil a) a))
              (sttfa.impl
               (sttfa.forall A
                (λ (a : sttfa.etap (sttfa.p A)), logic.eq A (op a nil) a))
               (sttfa.impl
                (sttfa.forall A
                 (λ (a : sttfa.etap (sttfa.p A)),
                    sttfa.forall A
                    (λ (b : sttfa.etap (sttfa.p A)),
                       sttfa.forall A
                       (λ (c : sttfa.etap (sttfa.p A)),
                          logic.eq A (op a (op b c)) (op (op a b) c)))))
                (sttfa.impl
                 (sttfa.forall A
                  (λ (a : sttfa.etap (sttfa.p A)),
                     sttfa.forall A
                     (λ (b : sttfa.etap (sttfa.p A)),
                        logic.eq A (op a b) (op b a))))
                 (ACop A nil))))))));
symbol timesAC : sttfa.eps (ACop nat.nat (nat.S nat.O))
  ≔ mk_ACop nat.nat (nat.S nat.O) nat.times
      (λ (a : sttfa.etap (sttfa.p nat.nat)),
         nat.sym_eq_times (nat.S nat.O)
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
            logic.eq nat.nat (y a) a)
         (nat.sym_eq_filter_nat_type_S (sttfa.arrow nat.nat nat.nat)
          nat.times_body nat.O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
             logic.eq nat.nat (y a) a)
          (nat.sym_eq_times_body_S nat.O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              logic.eq nat.nat (y a) a)
           (nat.sym_eq_times nat.O
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
               logic.eq nat.nat (nat.plus a (y a)) a)
            (nat.sym_eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
             nat.times_body
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                logic.eq nat.nat (nat.plus a (y a)) a)
             (nat.sym_eq_times_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                 logic.eq nat.nat (nat.plus a (y a)) a)
              (logic.sym_eq nat.nat a (nat.plus a nat.O) (nat.plus_n_O a))))))))
      (λ (n : sttfa.etap (sttfa.p nat.nat)),
         logic.sym_eq nat.nat n (nat.times n (nat.S nat.O)) (nat.times_n_1 n))
      (λ (a : sttfa.etap (sttfa.p nat.nat)),
         λ (b : sttfa.etap (sttfa.p nat.nat)),
           λ (c : sttfa.etap (sttfa.p nat.nat)),
             logic.sym_eq nat.nat (nat.times (nat.times a b) c)
             (nat.times a (nat.times b c)) (nat.associative_times a b c))
      nat.commutative_times;
symbol bigop_diff
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat bool.bool)
     (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall nat.nat
           (λ (i : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (n : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.lt i n)
                 (sttfa.impl (logic.eq bool.bool (p i) bool.true)
                  (logic.eq nat.nat
                   (bigop nat.nat n
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                    (nat.S nat.O) nat.times
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                   (nat.times (f i)
                    (bigop nat.nat n
                     (λ (x : sttfa.etap (sttfa.p nat.nat)),
                        bool.andb (bool.notb (nat.eqb i x)) (p x))
                     (nat.S nat.O) nat.times
                     (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))))))))
  ≔ λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (i : sttfa.etap (sttfa.p nat.nat)),
            λ (n : sttfa.etap (sttfa.p nat.nat)),
              nat.nat_ind
              (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.lt i _x_365)
                 (sttfa.impl (logic.eq bool.bool (p i) bool.true)
                  (logic.eq nat.nat
                   (bigop nat.nat _x_365
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                    (nat.S nat.O) nat.times
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                   (nat.times (f i)
                    (bigop nat.nat _x_365
                     (λ (x : sttfa.etap (sttfa.p nat.nat)),
                        bool.andb (bool.notb (nat.eqb i x)) (p x))
                     (nat.S nat.O) nat.times
                     (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))))
              (λ (ltO : sttfa.eps (nat.lt i nat.O)),
                 connectives.falsity
                 (sttfa.impl (logic.eq bool.bool (p i) bool.true)
                  (logic.eq nat.nat
                   (bigop nat.nat nat.O
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                    (nat.S nat.O) nat.times
                    (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                   (nat.times (f i)
                    (bigop nat.nat nat.O
                     (λ (x : sttfa.etap (sttfa.p nat.nat)),
                        bool.andb (bool.notb (nat.eqb i x)) (p x))
                     (nat.S nat.O) nat.times
                     (λ (x : sttfa.etap (sttfa.p nat.nat)), f x)))))
                 (logic.absurd (nat.le (nat.S i) nat.O) ltO
                  (nat.not_le_Sn_O i)))
              (λ (n0 : sttfa.etap (sttfa.p nat.nat)),
                 λ
                   (
                   Hind : sttfa.eps
                          (sttfa.impl (nat.lt i n0)
                           (sttfa.impl (logic.eq bool.bool (p i) bool.true)
                            (logic.eq nat.nat
                             (bigop nat.nat n0
                              (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                              (nat.S nat.O) nat.times
                              (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                             (nat.times (f i)
                              (bigop nat.nat n0
                               (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i x)) (p x))
                               (nat.S nat.O) nat.times
                               (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))))
                   ),
                   λ (lein : sttfa.eps (nat.lt i (nat.S n0))),
                     λ
                       (pi : sttfa.eps (logic.eq bool.bool (p i) bool.true)),
                       connectives.match_Or_prop (nat.lt i n0)
                       (logic.eq nat.nat i n0)
                       (logic.eq nat.nat
                        (bigop nat.nat (nat.S n0)
                         (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                         (nat.S nat.O) nat.times
                         (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                        (nat.times (f i)
                         (bigop nat.nat (nat.S n0)
                          (λ (x : sttfa.etap (sttfa.p nat.nat)),
                             bool.andb (bool.notb (nat.eqb i x)) (p x))
                          (nat.S nat.O) nat.times
                          (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))
                       (λ (Hi : sttfa.eps (nat.lt i n0)),
                          connectives.match_Or_prop
                          (logic.eq bool.bool (p n0) bool.true)
                          (logic.eq bool.bool (p n0) bool.false)
                          (logic.eq nat.nat
                           (bigop nat.nat (nat.S n0)
                            (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                            (nat.S nat.O) nat.times
                            (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                           (nat.times (f i)
                            (bigop nat.nat (nat.S n0)
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                bool.andb (bool.notb (nat.eqb i x)) (p x))
                             (nat.S nat.O) nat.times
                             (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))
                          (λ
                             (
                             pn : sttfa.eps
                                  (logic.eq bool.bool (p n0) bool.true)
                             ),
                             logic.eq_ind_r nat.nat
                             (nat.times (f n0)
                              (bigop nat.nat n0
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                               (nat.S nat.O) nat.times
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat x
                                (nat.times (f i)
                                 (bigop nat.nat (nat.S n0)
                                  (λ (x0 : sttfa.etap (sttfa.p nat.nat)),
                                     bool.andb (bool.notb (nat.eqb i x0))
                                     (p x0))
                                  (nat.S nat.O) nat.times
                                  (λ (x0 : sttfa.etap (sttfa.p nat.nat)),
                                     f x0))))
                             (logic.eq_ind_r nat.nat
                              (nat.times (f n0)
                               (bigop nat.nat n0
                                (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                   bool.andb (bool.notb (nat.eqb i i0))
                                   (p i0))
                                (nat.S nat.O) nat.times
                                (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                              (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (nat.times (f n0)
                                  (bigop nat.nat n0
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      p i0)
                                   (nat.S nat.O) nat.times
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      f i0)))
                                 (nat.times (f i) x))
                              (logic.eq_ind_r nat.nat
                               (nat.times (nat.times (f i) (f n0))
                                (bigop nat.nat n0
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    bool.match_bool_type bool.bool (p i0)
                                    bool.false
                                    (bool.match_bool_type bool.bool
                                     bool.false bool.true (nat.eqb i i0)))
                                 (nat.S nat.O) nat.times
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    f i0)))
                               (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat
                                  (nat.times (f n0)
                                   (bigop nat.nat n0
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       p i0)
                                    (nat.S nat.O) nat.times
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       f i0)))
                                  x)
                               (logic.eq_ind_r nat.nat
                                (nat.times (f n0) (f i))
                                (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat
                                   (nat.times (f n0)
                                    (bigop nat.nat n0
                                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                        p i0)
                                     (nat.S nat.O) nat.times
                                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                        f i0)))
                                   (nat.times x
                                    (bigop nat.nat n0
                                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                        bool.match_bool_type bool.bool (p i0)
                                        bool.false
                                        (bool.match_bool_type bool.bool
                                         bool.false bool.true (nat.eqb i i0)))
                                     (nat.S nat.O) nat.times
                                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                        f i0))))
                                (logic.eq_ind nat.nat
                                 (nat.times (f n0)
                                  (nat.times (f i)
                                   (bigop nat.nat n0
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       bool.match_bool_type bool.bool (p i0)
                                       bool.false
                                       (bool.match_bool_type bool.bool
                                        bool.false bool.true (nat.eqb i i0)))
                                    (nat.S nat.O) nat.times
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       f i0))))
                                 (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat
                                    (nat.times (f n0)
                                     (bigop nat.nat n0
                                      (λ
                                         (i0 : sttfa.etap (sttfa.p nat.nat)),
                                         p i0)
                                      (nat.S nat.O) nat.times
                                      (λ
                                         (i0 : sttfa.etap (sttfa.p nat.nat)),
                                         f i0)))
                                    x_1)
                                 (logic.eq_ind_r nat.nat
                                  (nat.times (f i)
                                   (bigop nat.nat n0
                                    (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                       bool.andb (bool.notb (nat.eqb i x))
                                       (p x))
                                    (nat.S nat.O) nat.times
                                    (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                       f x)))
                                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                     logic.eq nat.nat (nat.times (f n0) x)
                                     (nat.times (f n0)
                                      (nat.times (f i)
                                       (bigop nat.nat n0
                                        (λ
                                           (i0 : sttfa.etap (sttfa.p nat.nat)
                                           ),
                                           bool.match_bool_type bool.bool
                                           (p i0) bool.false
                                           (bool.match_bool_type bool.bool
                                            bool.false bool.true
                                            (nat.eqb i i0)))
                                        (nat.S nat.O) nat.times
                                        (λ
                                           (i0 : sttfa.etap (sttfa.p nat.nat)
                                           ), f i0)))))
                                  (logic.refl nat.nat
                                   (nat.times (f n0)
                                    (nat.times (f i)
                                     (bigop nat.nat n0
                                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                         bool.andb (bool.notb (nat.eqb i x))
                                         (p x))
                                      (nat.S nat.O) nat.times
                                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                         f x)))))
                                  (bigop nat.nat n0
                                   (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                      p x)
                                   (nat.S nat.O) nat.times
                                   (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                      f x))
                                  (Hind Hi
                                   (logic.rewrite_r bool.bool bool.true
                                    (λ
                                       (__ : sttfa.etap (sttfa.p bool.bool)),
                                       logic.eq bool.bool __ bool.true)
                                    (logic.refl bool.bool bool.true) (
                                    p i) pi)))
                                 (nat.times (nat.times (f n0) (f i))
                                  (bigop nat.nat n0
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      bool.match_bool_type bool.bool (p i0)
                                      bool.false
                                      (bool.match_bool_type bool.bool
                                       bool.false bool.true (nat.eqb i i0)))
                                   (nat.S nat.O) nat.times
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      f i0)))
                                 (assoc (f n0) (f i)
                                  (bigop nat.nat n0
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      bool.match_bool_type bool.bool (p i0)
                                      bool.false
                                      (bool.match_bool_type bool.bool
                                       bool.false bool.true (nat.eqb i i0)))
                                   (nat.S nat.O) nat.times
                                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                      f i0))))
                                (nat.times (f i) (f n0))
                                (nat.commutative_times (f i) (f n0)))
                               (nat.times (f i)
                                (nat.times (f n0)
                                 (bigop nat.nat n0
                                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                     bool.match_bool_type bool.bool (p i0)
                                     bool.false
                                     (bool.match_bool_type bool.bool
                                      bool.false bool.true (nat.eqb i i0)))
                                  (nat.S nat.O) nat.times
                                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                     f i0))))
                               (assoc (f i) (f n0)
                                (bigop nat.nat n0
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    bool.match_bool_type bool.bool (p i0)
                                    bool.false
                                    (bool.match_bool_type bool.bool
                                     bool.false bool.true (nat.eqb i i0)))
                                 (nat.S nat.O) nat.times
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    f i0))))
                              (bigop nat.nat (nat.S n0)
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i i0)) (p i0))
                               (nat.S nat.O) nat.times
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                              (bigop_Strue nat.nat n0
                               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i __)) (p __))
                               (nat.S nat.O) nat.times f
                               (logic.rewrite_r bool.bool bool.true
                                (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                   logic.eq bool.bool
                                   (bool.andb (bool.notb (nat.eqb i n0)) __)
                                   bool.true)
                                (logic.rewrite_r bool.bool bool.true
                                 (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                    logic.eq bool.bool __ bool.true)
                                 (logic.refl bool.bool bool.true)
                                 (bool.andb (bool.notb (nat.eqb i n0))
                                  bool.true)
                                 (logic.rewrite_l bool.bool (p n0)
                                  (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                     logic.eq bool.bool
                                     (bool.andb (bool.notb (nat.eqb i n0))
                                      bool.true)
                                     __)
                                  (logic.rewrite_l bool.bool (p n0)
                                   (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                      logic.eq bool.bool
                                      (bool.andb (bool.notb (nat.eqb i n0))
                                       __)
                                      (p n0))
                                   (logic.eq_ind_r bool.bool bool.false
                                    (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                       logic.eq bool.bool
                                       (bool.andb (bool.notb x) (p n0))
                                       (p n0))
                                    (bool.sym_eq_match_bool_type_false
                                     bool.bool bool.false bool.true
                                     (λ
                                        (y : sttfa.etap (sttfa.p bool.bool)),
                                        logic.eq bool.bool
                                        (bool.match_bool_type bool.bool
                                         (p n0) bool.false y)
                                        (p n0))
                                     (bool.eq_match_bool_type_true bool.bool
                                      (p n0) bool.false
                                      (λ
                                         (y : sttfa.etap (sttfa.p bool.bool)),
                                         logic.eq bool.bool
                                         (bool.match_bool_type bool.bool
                                          (p n0) bool.false bool.true)
                                         y)
                                      (bool.eq_match_bool_type_false
                                       bool.bool bool.false bool.true
                                       (λ
                                          (y : sttfa.etap (sttfa.p bool.bool)
                                          ),
                                          logic.eq bool.bool
                                          (bool.match_bool_type bool.bool
                                           (p n0) bool.false bool.true)
                                          (bool.match_bool_type bool.bool
                                           (p n0) bool.false y))
                                       (bool.eq_match_bool_type_false
                                        bool.bool bool.false bool.true
                                        (λ
                                           (
                                           y : sttfa.etap (sttfa.p bool.bool)
                                           ),
                                           logic.eq bool.bool
                                           (bool.match_bool_type bool.bool
                                            (p n0) bool.false y)
                                           (bool.match_bool_type bool.bool
                                            (p n0) bool.false
                                            (bool.match_bool_type bool.bool
                                             bool.false bool.true bool.false)))
                                        (logic.refl bool.bool
                                         (bool.andb (bool.notb bool.false)
                                          (p n0)))))))
                                    (nat.eqb i n0)
                                    (nat.not_eq_to_eqb_false i n0
                                     (nat.lt_to_not_eq i n0 Hi)))
                                   bool.true pn)
                                  bool.true pn))
                                (p n0) pn)))
                             (bigop nat.nat (nat.S n0)
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                              (nat.S nat.O) nat.times
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                             (bigop_Strue nat.nat n0 p (nat.S nat.O)
                              nat.times f
                              (logic.rewrite_r bool.bool bool.true
                               (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool __ bool.true)
                               (logic.refl bool.bool bool.true) (p n0) pn)))
                          (λ
                             (
                             pn : sttfa.eps
                                  (logic.eq bool.bool (p n0) bool.false)
                             ),
                             logic.eq_ind_r nat.nat
                             (bigop nat.nat n0
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                              (nat.S nat.O) nat.times
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat x
                                (nat.times (f i)
                                 (bigop nat.nat (nat.S n0)
                                  (λ (x0 : sttfa.etap (sttfa.p nat.nat)),
                                     bool.andb (bool.notb (nat.eqb i x0))
                                     (p x0))
                                  (nat.S nat.O) nat.times
                                  (λ (x0 : sttfa.etap (sttfa.p nat.nat)),
                                     f x0))))
                             (logic.eq_ind_r nat.nat
                              (bigop nat.nat n0
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i i0)) (p i0))
                               (nat.S nat.O) nat.times
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                              (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (bigop nat.nat n0
                                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                     p i0)
                                  (nat.S nat.O) nat.times
                                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                     f i0))
                                 (nat.times (f i) x))
                              (logic.eq_ind_r nat.nat
                               (nat.times (f i)
                                (bigop nat.nat n0
                                 (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                    bool.andb (bool.notb (nat.eqb i x)) (p x))
                                 (nat.S nat.O) nat.times
                                 (λ (x : sttfa.etap (sttfa.p nat.nat)), f x)))
                               (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat x
                                  (nat.times (f i)
                                   (bigop nat.nat n0
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       bool.andb (bool.notb (nat.eqb i i0))
                                       (p i0))
                                    (nat.S nat.O) nat.times
                                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                       f i0))))
                               (logic.refl nat.nat
                                (nat.times (f i)
                                 (bigop nat.nat n0
                                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                     bool.andb (bool.notb (nat.eqb i x))
                                     (p x))
                                  (nat.S nat.O) nat.times
                                  (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))
                               (bigop nat.nat n0
                                (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                                (nat.S nat.O) nat.times
                                (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                               (Hind Hi
                                (logic.rewrite_r bool.bool bool.true
                                 (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                    logic.eq bool.bool __ bool.true)
                                 (logic.refl bool.bool bool.true) (p i) pi)))
                              (bigop nat.nat (nat.S n0)
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i i0)) (p i0))
                               (nat.S nat.O) nat.times
                               (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                              (bigop_Sfalse nat.nat n0
                               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i __)) (p __))
                               (nat.S nat.O) nat.times f
                               (logic.rewrite_r bool.bool bool.false
                                (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                   logic.eq bool.bool
                                   (bool.andb (bool.notb (nat.eqb i n0)) __)
                                   bool.false)
                                (logic.rewrite_r bool.bool bool.false
                                 (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                    logic.eq bool.bool __ bool.false)
                                 (logic.refl bool.bool bool.false)
                                 (bool.andb (bool.notb (nat.eqb i n0))
                                  bool.false)
                                 (logic.rewrite_l bool.bool (p n0)
                                  (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                     logic.eq bool.bool
                                     (bool.andb (bool.notb (nat.eqb i n0))
                                      bool.false)
                                     __)
                                  (logic.rewrite_l bool.bool (p n0)
                                   (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                      logic.eq bool.bool
                                      (bool.andb (bool.notb (nat.eqb i n0))
                                       __)
                                      (p n0))
                                   (logic.eq_ind_r bool.bool bool.false
                                    (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                       logic.eq bool.bool
                                       (bool.andb (bool.notb x) (p n0))
                                       (p n0))
                                    (bool.sym_eq_match_bool_type_false
                                     bool.bool bool.false bool.true
                                     (λ
                                        (y : sttfa.etap (sttfa.p bool.bool)),
                                        logic.eq bool.bool
                                        (bool.match_bool_type bool.bool
                                         (p n0) bool.false y)
                                        (p n0))
                                     (bool.eq_match_bool_type_true bool.bool
                                      (p n0) bool.false
                                      (λ
                                         (y : sttfa.etap (sttfa.p bool.bool)),
                                         logic.eq bool.bool
                                         (bool.match_bool_type bool.bool
                                          (p n0) bool.false bool.true)
                                         y)
                                      (bool.eq_match_bool_type_false
                                       bool.bool bool.false bool.true
                                       (λ
                                          (y : sttfa.etap (sttfa.p bool.bool)
                                          ),
                                          logic.eq bool.bool
                                          (bool.match_bool_type bool.bool
                                           (p n0) bool.false bool.true)
                                          (bool.match_bool_type bool.bool
                                           (p n0) bool.false y))
                                       (bool.eq_match_bool_type_false
                                        bool.bool bool.false bool.true
                                        (λ
                                           (
                                           y : sttfa.etap (sttfa.p bool.bool)
                                           ),
                                           logic.eq bool.bool
                                           (bool.match_bool_type bool.bool
                                            (p n0) bool.false y)
                                           (bool.match_bool_type bool.bool
                                            (p n0) bool.false
                                            (bool.match_bool_type bool.bool
                                             bool.false bool.true bool.false)))
                                        (logic.refl bool.bool
                                         (bool.andb (bool.notb bool.false)
                                          (p n0)))))))
                                    (nat.eqb i n0)
                                    (nat.not_eq_to_eqb_false i n0
                                     (nat.lt_to_not_eq i n0 Hi)))
                                   bool.false pn)
                                  bool.false pn))
                                (p n0) pn)))
                             (bigop nat.nat (nat.S n0)
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                              (nat.S nat.O) nat.times
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                             (bigop_Sfalse nat.nat n0 p (nat.S nat.O)
                              nat.times f
                              (logic.rewrite_r bool.bool bool.false
                               (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool __ bool.false)
                               (logic.refl bool.bool bool.false) (p n0) pn)))
                          (bool.true_or_false (p n0)))
                       (λ (Hi : sttfa.eps (logic.eq nat.nat i n0)),
                          logic.eq_ind nat.nat i
                          (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat
                             (bigop nat.nat (nat.S x_1)
                              (λ (x : sttfa.etap (sttfa.p nat.nat)), p x)
                              (nat.S nat.O) nat.times
                              (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                             (nat.times (f i)
                              (bigop nat.nat (nat.S x_1)
                               (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                  bool.andb (bool.notb (nat.eqb i x)) (p x))
                               (nat.S nat.O) nat.times
                               (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))))
                          (logic.eq_ind_r nat.nat
                           (nat.times (f i)
                            (bigop nat.nat i
                             (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                             (nat.S nat.O) nat.times
                             (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                           (λ (x : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat x
                              (nat.times (f i)
                               (bigop nat.nat (nat.S i)
                                (λ (x0 : sttfa.etap (sttfa.p nat.nat)),
                                   bool.andb (bool.notb (nat.eqb i x0))
                                   (p x0))
                                (nat.S nat.O) nat.times
                                (λ (x0 : sttfa.etap (sttfa.p nat.nat)), f x0))))
                           (logic.eq_f nat.nat nat.nat (nat.times (f i))
                            (bigop nat.nat i
                             (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                             (nat.S nat.O) nat.times
                             (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                            (bigop nat.nat (nat.S i)
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                bool.andb (bool.notb (nat.eqb i x)) (p x))
                             (nat.S nat.O) nat.times
                             (λ (x : sttfa.etap (sttfa.p nat.nat)), f x))
                            (logic.eq_ind_r nat.nat
                             (bigop nat.nat i
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                 bool.andb (bool.notb (nat.eqb i i0)) (p i0))
                              (nat.S nat.O) nat.times
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (bigop nat.nat i
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    p i0)
                                 (nat.S nat.O) nat.times
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    f i0))
                                x)
                             (same_bigop nat.nat i p
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 bool.andb (bool.notb (nat.eqb i __)) (p __))
                              (nat.S nat.O) nat.times f f
                              (λ (k : sttfa.etap (sttfa.p nat.nat)),
                                 λ (ltki : sttfa.eps (nat.lt k i)),
                                   logic.eq_ind_r bool.bool bool.false
                                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                      logic.eq bool.bool (p k)
                                      (bool.andb (bool.notb x) (p k)))
                                   (bool.sym_eq_match_bool_type_false
                                    bool.bool bool.false bool.true
                                    (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                       logic.eq bool.bool (p k)
                                       (bool.match_bool_type bool.bool (p k)
                                        bool.false y))
                                    (bool.sym_eq_match_bool_type_true
                                     bool.bool (p k) bool.false
                                     (λ
                                        (y : sttfa.etap (sttfa.p bool.bool)),
                                        logic.eq bool.bool (p k) y)
                                     (logic.refl bool.bool (p k))))
                                   (nat.eqb i k)
                                   (nat.not_eq_to_eqb_false i k
                                    (logic.not_to_not (logic.eq nat.nat i k)
                                     (nat.le (nat.S i) i)
                                     (λ
                                        (
                                        auto : sttfa.eps
                                               (logic.eq nat.nat i k)
                                        ),
                                        logic.eq_coerc (nat.le (nat.S k) i)
                                        (nat.le (nat.S i) i) ltki
                                        (logic.rewrite_l nat.nat i
                                         (λ
                                            (
                                            __ : sttfa.etap (sttfa.p nat.nat)
                                            ),
                                            logic.eq sttfa.bool
                                            (nat.le (nat.S __) i)
                                            (nat.le (nat.S i) i))
                                         (logic.refl sttfa.bool
                                          (nat.le (nat.S i) i))
                                         k auto))
                                     (nat.not_le_Sn_n i))))
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                 λ (auto : sttfa.eps (nat.lt i0 i)),
                                   λ
                                     (
                                     auto' : sttfa.eps
                                             (logic.eq bool.bool (p i0)
                                              bool.true)
                                     ), logic.refl nat.nat (f i0)))
                             (bigop nat.nat (nat.S i)
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                 bool.andb (bool.notb (nat.eqb i i0)) (p i0))
                              (nat.S nat.O) nat.times
                              (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                             (bigop_Sfalse nat.nat i
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 bool.andb (bool.notb (nat.eqb i __)) (p __))
                              (nat.S nat.O) nat.times f
                              (logic.eq_ind_r bool.bool bool.true
                               (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                  logic.eq bool.bool
                                  (bool.andb (bool.notb x) (p i)) bool.false)
                               (bool.eq_match_bool_type_false bool.bool (p i)
                                bool.false
                                (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                   logic.eq bool.bool
                                   (bool.match_bool_type bool.bool (p i)
                                    bool.false
                                    (bool.match_bool_type bool.bool
                                     bool.false bool.true bool.true))
                                   y)
                                (bool.eq_match_bool_type_true bool.bool
                                 bool.false bool.true
                                 (λ (y : sttfa.etap (sttfa.p bool.bool)),
                                    logic.eq bool.bool
                                    (bool.match_bool_type bool.bool (p i)
                                     bool.false
                                     (bool.match_bool_type bool.bool
                                      bool.false bool.true bool.true))
                                    (bool.match_bool_type bool.bool (p i)
                                     bool.false y))
                                 (logic.refl bool.bool
                                  (bool.andb (bool.notb bool.true) (p i)))))
                               (nat.eqb i i)
                               (nat.eq_to_eqb_true i i (logic.refl nat.nat i))))))
                           (bigop nat.nat (nat.S i)
                            (λ (i0 : sttfa.etap (sttfa.p nat.nat)), p i0)
                            (nat.S nat.O) nat.times
                            (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                           (bigop_Strue nat.nat i p (nat.S nat.O)
                            nat.times f
                            (logic.rewrite_r bool.bool bool.true
                             (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                logic.eq bool.bool __ bool.true)
                             (logic.refl bool.bool bool.true) (p i) pi)))
                          n0 Hi)
                       (nat.le_to_or_lt_eq i n0 (nat.le_S_S_to_le i n0 lein)))
              n;
symbol sub_hk
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
      (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
       (sttfa.arrow nat.nat
        (sttfa.arrow nat.nat
         (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
          (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
           (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
            (sttfa.arrow (sttfa.arrow nat.nat nat.nat) sttfa.bool)))))))))
  ≔ λ (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (k : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (n1 : sttfa.etap (sttfa.p nat.nat)),
            λ (n2 : sttfa.etap (sttfa.p nat.nat)),
              λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                λ
                  (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                  λ
                    (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    λ
                      (
                      f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      sttfa.forall nat.nat
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         sttfa.impl (nat.lt i n1)
                         (sttfa.impl (logic.eq bool.bool (p1 i) bool.true)
                          (connectives.And
                           (connectives.And (nat.lt (h i) n2)
                            (logic.eq bool.bool (p2 (h i)) bool.true))
                           (logic.eq nat.nat (k (h i)) i))));
symbol iso
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow nat.nat
      (sttfa.arrow nat.nat
       (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
        (sttfa.arrow (sttfa.arrow nat.nat bool.bool)
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow (sttfa.arrow nat.nat nat.nat) sttfa.bool)))))))
  ≔ λ (n1 : sttfa.etap (sttfa.p nat.nat)),
        λ (n2 : sttfa.etap (sttfa.p nat.nat)),
          λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                λ (f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                  connectives.ex (sttfa.arrow nat.nat nat.nat)
                  (λ
                     (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                     connectives.ex (sttfa.arrow nat.nat nat.nat)
                     (λ
                        (
                        k : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                        ),
                        connectives.And
                        (connectives.And
                         (sttfa.forall nat.nat
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl (nat.lt i n1)
                             (sttfa.impl
                              (logic.eq bool.bool (p1 i) bool.true)
                              (logic.eq nat.nat (f1 i) (f2 (h i))))))
                         (sub_hk h k n1 n2 p1 p2 f1 f2))
                        (sub_hk k h n2 n1 p2 p1 f2 f1)));
symbol sub_hkO
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (k : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall nat.nat
           (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (n2 : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.forall (sttfa.arrow nat.nat bool.bool)
                 (λ
                    (
                    p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))
                    ),
                    sttfa.forall (sttfa.arrow nat.nat bool.bool)
                    (λ
                       (
                       p2 : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat bool.bool))
                       ),
                       sttfa.forall (sttfa.arrow nat.nat nat.nat)
                       (λ
                          (
                          f1 : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          sttfa.forall (sttfa.arrow nat.nat nat.nat)
                          (λ
                             (
                             f2 : sttfa.etap
                                  (sttfa.p (sttfa.arrow nat.nat nat.nat))
                             ),
                             sttfa.impl (logic.eq nat.nat n1 nat.O)
                             (sub_hk h k n1 n2 p1 p2 f1 f2))))))))))
  ≔ λ (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (k : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (n1 : sttfa.etap (sttfa.p nat.nat)),
            λ (n2 : sttfa.etap (sttfa.p nat.nat)),
              λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                λ
                  (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                  λ
                    (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    λ
                      (
                      f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      λ (up0 : sttfa.eps (logic.eq nat.nat n1 nat.O)),
                        λ (i : sttfa.etap (sttfa.p nat.nat)),
                          λ (lti : sttfa.eps (nat.lt i n1)),
                            logic.eq_ind_r nat.nat nat.O
                            (λ (x : sttfa.etap (sttfa.p nat.nat)),
                               sttfa.impl
                               (logic.eq bool.bool (p1 i) bool.true)
                               (connectives.And
                                (connectives.And (nat.lt (h i) n2)
                                 (logic.eq bool.bool (p2 (h i)) bool.true))
                                (logic.eq nat.nat (k (h i)) i)))
                            (connectives.falsity
                             (sttfa.impl
                              (logic.eq bool.bool (p1 i) bool.true)
                              (connectives.And
                               (connectives.And (nat.lt (h i) n2)
                                (logic.eq bool.bool (p2 (h i)) bool.true))
                               (logic.eq nat.nat (k (h i)) i)))
                             (logic.absurd (nat.le (nat.S i) nat.O)
                              (logic.eq_coerc (nat.le (nat.S i) n1)
                               (nat.le (nat.S i) nat.O) lti
                               (logic.rewrite_r nat.nat nat.O
                                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq sttfa.bool (nat.le (nat.S i) __)
                                   (nat.le (nat.S i) nat.O))
                                (logic.refl sttfa.bool
                                 (nat.le (nat.S i) nat.O))
                                n1 up0))
                              (nat.not_le_Sn_O i)))
                            n1 up0;
symbol sub0_to_false
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (k : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall nat.nat
           (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (n2 : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.forall (sttfa.arrow nat.nat bool.bool)
                 (λ
                    (
                    p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))
                    ),
                    sttfa.forall (sttfa.arrow nat.nat bool.bool)
                    (λ
                       (
                       p2 : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat bool.bool))
                       ),
                       sttfa.forall (sttfa.arrow nat.nat nat.nat)
                       (λ
                          (
                          f1 : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          sttfa.forall (sttfa.arrow nat.nat nat.nat)
                          (λ
                             (
                             f2 : sttfa.etap
                                  (sttfa.p (sttfa.arrow nat.nat nat.nat))
                             ),
                             sttfa.impl (logic.eq nat.nat n1 nat.O)
                             (sttfa.impl
                              (sub_hk h k n2 n1 p2 p1 f2 f1)
                              (sttfa.forall nat.nat
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  sttfa.impl (nat.lt i n2)
                                  (logic.eq bool.bool (p2 i) bool.false)))))))))))))
  ≔ λ (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (k : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (n1 : sttfa.etap (sttfa.p nat.nat)),
            λ (n2 : sttfa.etap (sttfa.p nat.nat)),
              λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                λ
                  (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                  λ
                    (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    λ
                      (
                      f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      λ (up0 : sttfa.eps (logic.eq nat.nat n1 nat.O)),
                        λ
                          (
                          sub : sttfa.eps
                                (sub_hk h k n2 n1 p2 p1 f2 f1)
                          ),
                          λ (i : sttfa.etap (sttfa.p nat.nat)),
                            λ (lti : sttfa.eps (nat.lt i n2)),
                              connectives.match_Or_prop
                              (logic.eq bool.bool (p2 i) bool.true)
                              (logic.eq bool.bool (p2 i) bool.false)
                              (logic.eq bool.bool (p2 i) bool.false)
                              (λ
                                 (
                                 ptrue : sttfa.eps
                                         (logic.eq bool.bool (p2 i) bool.true)
                                 ),
                                 connectives.match_And_prop
                                 (connectives.And (nat.lt (h i) n1)
                                  (logic.eq bool.bool (p1 (h i)) bool.true))
                                 (logic.eq nat.nat (k (h i)) i)
                                 (logic.eq bool.bool (p2 i) bool.false)
                                 (λ
                                    (
                                    _clearme : sttfa.eps
                                               (connectives.And
                                                (nat.lt (h i) n1)
                                                (logic.eq bool.bool
                                                 (p1 (h i)) bool.true))
                                    ),
                                    connectives.match_And_prop
                                    (nat.lt (h i) n1)
                                    (logic.eq bool.bool (p1 (h i)) bool.true)
                                    (sttfa.impl
                                     (logic.eq nat.nat (k (h i)) i)
                                     (logic.eq bool.bool (p2 i) bool.false))
                                    (λ (hi : sttfa.eps (nat.lt (h i) n1)),
                                       connectives.falsity
                                       (sttfa.impl
                                        (logic.eq bool.bool (p1 (h i))
                                         bool.true)
                                        (sttfa.impl
                                         (logic.eq nat.nat (k (h i)) i)
                                         (logic.eq bool.bool (p2 i)
                                          bool.false)))
                                       (logic.absurd
                                        (nat.le (nat.S (h i)) nat.O)
                                        (logic.eq_coerc
                                         (nat.le (nat.S (h i)) n1)
                                         (nat.le (nat.S (h i)) nat.O) hi
                                         (logic.rewrite_r nat.nat nat.O
                                          (λ
                                             (
                                             __ : sttfa.etap
                                                  (sttfa.p nat.nat)
                                             ),
                                             logic.eq sttfa.bool
                                             (nat.le (nat.S (h i)) __)
                                             (nat.le (nat.S (h i)) nat.O))
                                          (logic.refl sttfa.bool
                                           (nat.le (nat.S (h i)) nat.O))
                                          n1 up0))
                                        (nat.not_le_Sn_O (h i))))
                                    _clearme)
                                 (sub i lti ptrue))
                              (λ
                                 (
                                 auto : sttfa.eps
                                        (logic.eq bool.bool (p2 i) bool.false)
                                 ),
                                 logic.rewrite_r bool.bool bool.false
                                 (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                                    logic.eq bool.bool __ bool.false)
                                 (logic.refl bool.bool bool.false) (p2 i)
                                 auto)
                              (bool.true_or_false (p2 i));
symbol sub_lt
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (e : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat bool.bool)
        (λ (p : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
           sttfa.forall nat.nat
           (λ (n : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (m : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.le n m)
                 (sub_hk (λ (x : sttfa.etap (sttfa.p nat.nat)), x)
                  (λ (x : sttfa.etap (sttfa.p nat.nat)), x) n m p p e e))))))
  ≔ λ (e : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            λ (m : sttfa.etap (sttfa.p nat.nat)),
              λ (lenm : sttfa.eps (nat.le n m)),
                λ (i : sttfa.etap (sttfa.p nat.nat)),
                  λ (lti : sttfa.eps (nat.lt i n)),
                    λ (fi : sttfa.eps (logic.eq bool.bool (f i) bool.true)),
                      connectives.conj
                      (connectives.And (nat.lt i m)
                       (logic.eq bool.bool (f i) bool.true))
                      (logic.eq nat.nat i i)
                      (connectives.conj (nat.lt i m)
                       (logic.eq bool.bool (f i) bool.true)
                       (nat.lt_to_le_to_lt i n m lti lenm)
                       (logic.rewrite_r bool.bool bool.true
                        (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                           logic.eq bool.bool __ bool.true)
                        (logic.refl bool.bool bool.true) (f i) fi))
                      (logic.refl nat.nat i);
symbol transitive_sub
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (h1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (k1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall (sttfa.arrow nat.nat nat.nat)
           (λ (h2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              sttfa.forall (sttfa.arrow nat.nat nat.nat)
              (λ (k2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                 sttfa.forall nat.nat
                 (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.forall nat.nat
                    (λ (n2 : sttfa.etap (sttfa.p nat.nat)),
                       sttfa.forall nat.nat
                       (λ (n3 : sttfa.etap (sttfa.p nat.nat)),
                          sttfa.forall (sttfa.arrow nat.nat bool.bool)
                          (λ
                             (
                             p1 : sttfa.etap
                                  (sttfa.p (sttfa.arrow nat.nat bool.bool))
                             ),
                             sttfa.forall (sttfa.arrow nat.nat bool.bool)
                             (λ
                                (
                                p2 : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat.nat bool.bool))
                                ),
                                sttfa.forall (sttfa.arrow nat.nat bool.bool)
                                (λ
                                   (
                                   p3 : sttfa.etap
                                        (sttfa.p
                                         (sttfa.arrow nat.nat bool.bool))
                                   ),
                                   sttfa.forall (sttfa.arrow nat.nat nat.nat)
                                   (λ
                                      (
                                      f1 : sttfa.etap
                                           (sttfa.p
                                            (sttfa.arrow nat.nat nat.nat))
                                      ),
                                      sttfa.forall
                                      (sttfa.arrow nat.nat nat.nat)
                                      (λ
                                         (
                                         f2 : sttfa.etap
                                              (sttfa.p
                                               (sttfa.arrow nat.nat nat.nat))
                                         ),
                                         sttfa.forall
                                         (sttfa.arrow nat.nat nat.nat)
                                         (λ
                                            (
                                            f3 : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat
                                                   nat.nat))
                                            ),
                                            sttfa.impl
                                            (sub_hk h1 k1 n1 n2 p1 p2
                                             f1 f2)
                                            (sttfa.impl
                                             (sub_hk h2 k2 n2 n3 p2 p3
                                              f2 f3)
                                             (sub_hk
                                              (λ
                                                 (
                                                 x : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), h2 (h1 x))
                                              (λ
                                                 (
                                                 x : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                 ), k1 (k2 x))
                                              n1 n3 p1 p3 f1 f3))))))))))))))))
  ≔ λ (h1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (k1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (h2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
            λ (k2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              λ (n1 : sttfa.etap (sttfa.p nat.nat)),
                λ (n2 : sttfa.etap (sttfa.p nat.nat)),
                  λ (n3 : sttfa.etap (sttfa.p nat.nat)),
                    λ
                      (
                      p1 : sttfa.etap
                           (sttfa.p (sttfa.arrow nat.nat bool.bool))
                      ),
                      λ
                        (
                        p2 : sttfa.etap
                             (sttfa.p (sttfa.arrow nat.nat bool.bool))
                        ),
                        λ
                          (
                          p3 : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat bool.bool))
                          ),
                          λ
                            (
                            f1 : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat.nat nat.nat))
                            ),
                            λ
                              (
                              f2 : sttfa.etap
                                   (sttfa.p (sttfa.arrow nat.nat nat.nat))
                              ),
                              λ
                                (
                                f3 : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                ),
                                λ
                                  (
                                  sub1 : sttfa.eps
                                         (sub_hk h1 k1 n1 n2 p1 p2 f1
                                          f2)
                                  ),
                                  λ
                                    (
                                    sub2 : sttfa.eps
                                           (sub_hk h2 k2 n2 n3 p2 p3
                                            f2 f3)
                                    ),
                                    λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      λ (lti : sttfa.eps (nat.lt i n1)),
                                        λ
                                          (
                                          fi : sttfa.eps
                                               (logic.eq bool.bool (p1 i)
                                                bool.true)
                                          ),
                                          connectives.match_And_prop
                                          (connectives.And (nat.lt (h1 i) n2)
                                           (logic.eq bool.bool (p2 (h1 i))
                                            bool.true))
                                          (logic.eq nat.nat (k1 (h1 i)) i)
                                          (connectives.And
                                           (connectives.And
                                            (nat.lt (h2 (h1 i)) n3)
                                            (logic.eq bool.bool
                                             (p3 (h2 (h1 i))) bool.true))
                                           (logic.eq nat.nat
                                            (k1 (k2 (h2 (h1 i)))) i))
                                          (λ
                                             (
                                             _clearme : sttfa.eps
                                                        (connectives.And
                                                         (nat.lt (h1 i) n2)
                                                         (logic.eq bool.bool
                                                          (p2 (h1 i))
                                                          bool.true))
                                             ),
                                             connectives.match_And_prop
                                             (nat.lt (h1 i) n2)
                                             (logic.eq bool.bool (p2 (h1 i))
                                              bool.true)
                                             (sttfa.impl
                                              (logic.eq nat.nat (k1 (h1 i)) i)
                                              (connectives.And
                                               (connectives.And
                                                (nat.lt (h2 (h1 i)) n3)
                                                (logic.eq bool.bool
                                                 (p3 (h2 (h1 i))) bool.true))
                                               (logic.eq nat.nat
                                                (k1 (k2 (h2 (h1 i)))) i)))
                                             (λ
                                                (
                                                lth1i : sttfa.eps
                                                        (nat.lt (h1 i) n2)
                                                ),
                                                λ
                                                  (
                                                  fh1i : sttfa.eps
                                                         (logic.eq bool.bool
                                                          (p2 (h1 i))
                                                          bool.true)
                                                  ),
                                                  λ
                                                    (
                                                    ei : sttfa.eps
                                                         (logic.eq nat.nat
                                                          (k1 (h1 i)) i)
                                                    ),
                                                    connectives.match_And_prop
                                                    (connectives.And
                                                     (nat.lt (h2 (h1 i)) n3)
                                                     (logic.eq bool.bool
                                                      (p3 (h2 (h1 i)))
                                                      bool.true))
                                                    (logic.eq nat.nat
                                                     (k2 (h2 (h1 i))) (
                                                     h1 i))
                                                    (connectives.And
                                                     (connectives.And
                                                      (nat.lt (h2 (h1 i)) n3)
                                                      (logic.eq bool.bool
                                                       (p3 (h2 (h1 i)))
                                                       bool.true))
                                                     (logic.eq nat.nat
                                                      (k1 (k2 (h2 (h1 i)))) i))
                                                    (λ
                                                       (
                                                       _clearme0 : sttfa.eps
                                                                   (connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h2 (h1 i))
                                                                    n3)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p3
                                                                    (
                                                                    h2 (h1 i)))
                                                                    bool.true))
                                                       ),
                                                       connectives.match_And_prop
                                                       (nat.lt (h2 (h1 i)) n3)
                                                       (logic.eq bool.bool
                                                        (p3 (h2 (h1 i)))
                                                        bool.true)
                                                       (sttfa.impl
                                                        (logic.eq nat.nat
                                                         (k2 (h2 (h1 i)))
                                                         (h1 i))
                                                        (connectives.And
                                                         (connectives.And
                                                          (nat.lt (h2 (h1 i))
                                                           n3)
                                                          (logic.eq bool.bool
                                                           (p3 (h2 (h1 i)))
                                                           bool.true))
                                                         (logic.eq nat.nat
                                                          (k1
                                                           (k2 (h2 (h1 i))))
                                                          i)))
                                                       (λ
                                                          (
                                                          H1 : sttfa.eps
                                                               (nat.lt
                                                                (h2 (h1 i))
                                                                n3)
                                                          ),
                                                          λ
                                                            (
                                                            H2 : sttfa.eps
                                                                 (logic.eq
                                                                  bool.bool
                                                                  (p3
                                                                   (h2 (h1 i)))
                                                                  bool.true)
                                                            ),
                                                            λ
                                                              (
                                                              H3 : sttfa.eps
                                                                   (logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k2
                                                                    (
                                                                    h2 (h1 i)))
                                                                    (
                                                                    h1 i))
                                                              ),
                                                              connectives.conj
                                                              (connectives.And
                                                               (nat.lt
                                                                (h2 (h1 i))
                                                                n3)
                                                               (logic.eq
                                                                bool.bool
                                                                (p3
                                                                 (h2 (h1 i)))
                                                                bool.true))
                                                              (logic.eq
                                                               nat.nat
                                                               (k1
                                                                (k2
                                                                 (h2 (h1 i))))
                                                               i)
                                                              (connectives.conj
                                                               (nat.lt
                                                                (h2 (h1 i))
                                                                n3)
                                                               (logic.eq
                                                                bool.bool
                                                                (p3
                                                                 (h2 (h1 i)))
                                                                bool.true)
                                                               H1
                                                               (logic.rewrite_r
                                                                bool.bool
                                                                bool.true
                                                                (λ
                                                                   (
                                                                   __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                   ),
                                                                   logic.eq
                                                                   bool.bool
                                                                   __
                                                                   bool.true)
                                                                (logic.refl
                                                                 bool.bool
                                                                 bool.true)
                                                                (p3
                                                                 (h2 (h1 i)))
                                                                H2))
                                                              (logic.rewrite_r
                                                               nat.nat (
                                                               h1 i)
                                                               (λ
                                                                  (
                                                                  __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                                  ),
                                                                  logic.eq
                                                                  nat.nat
                                                                  (k1 __) i)
                                                               (logic.rewrite_r
                                                                nat.nat i
                                                                (λ
                                                                   (
                                                                   __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                                   ),
                                                                   logic.eq
                                                                   nat.nat __
                                                                   i)
                                                                (logic.refl
                                                                 nat.nat i)
                                                                (k1 (h1 i))
                                                                ei)
                                                               (k2
                                                                (h2 (h1 i)))
                                                               H3))
                                                       _clearme0)
                                                    (sub2 (h1 i) lth1i fh1i))
                                             _clearme)
                                          (sub1 i lti fi);
symbol let_clause_10471
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (n2 : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall (sttfa.arrow nat.nat bool.bool)
              (λ
                 (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                 sttfa.forall (sttfa.arrow nat.nat nat.nat)
                 (λ
                    (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    sttfa.forall (sttfa.arrow nat.nat nat.nat)
                    (λ
                       (
                       f2 : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       sttfa.impl (iso n1 n2 p1 p2 f1 f2)
                       (sttfa.forall (sttfa.arrow nat.nat nat.nat)
                        (λ
                           (
                           h : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat nat.nat))
                           ),
                           sttfa.impl
                           (connectives.ex (sttfa.arrow nat.nat nat.nat)
                            (λ
                               (
                               k : sttfa.etap
                                   (sttfa.p (sttfa.arrow nat.nat nat.nat))
                               ),
                               connectives.And
                               (connectives.And
                                (sttfa.forall nat.nat
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.lt i n1)
                                    (sttfa.impl
                                     (logic.eq bool.bool (p1 i) bool.true)
                                     (logic.eq nat.nat (f1 i) (f2 (h i))))))
                                (sub_hk h k n1 n2 p1 p2 f1 f2))
                               (sub_hk k h n2 n1 p2 p1 f2 f1)))
                           (sttfa.forall (sttfa.arrow nat.nat nat.nat)
                            (λ
                               (
                               k : sttfa.etap
                                   (sttfa.p (sttfa.arrow nat.nat nat.nat))
                               ),
                               sttfa.impl
                               (connectives.And
                                (connectives.And
                                 (sttfa.forall nat.nat
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.lt i n1)
                                     (sttfa.impl
                                      (logic.eq bool.bool (p1 i) bool.true)
                                      (logic.eq nat.nat (f1 i) (f2 (h i))))))
                                 (sub_hk h k n1 n2 p1 p2 f1 f2))
                                (sub_hk k h n2 n1 p2 p1 f2 f1))
                               (sttfa.impl
                                (connectives.And
                                 (sttfa.forall nat.nat
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.lt i n1)
                                     (sttfa.impl
                                      (logic.eq bool.bool (p1 i) bool.true)
                                      (logic.eq nat.nat (f1 i) (f2 (h i))))))
                                 (sub_hk h k n1 n2 p1 p2 f1 f2))
                                (sttfa.impl
                                 (sttfa.forall nat.nat
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.lt i n1)
                                     (sttfa.impl
                                      (logic.eq bool.bool (p1 i) bool.true)
                                      (logic.eq nat.nat (f1 i) (f2 (h i))))))
                                 (sttfa.forall nat.nat
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.forall nat.nat
                                     (λ (m : sttfa.etap (sttfa.p nat.nat)),
                                        sttfa.impl
                                        (sttfa.forall
                                         (sttfa.arrow nat.nat bool.bool)
                                         (λ
                                            (
                                            f : sttfa.etap
                                                (sttfa.p
                                                 (sttfa.arrow nat.nat
                                                  bool.bool))
                                            ),
                                            sttfa.impl (nat.le nat.O n1)
                                            (sttfa.impl
                                             (sub_hk h k nat.O m p1 f
                                              f1 f2)
                                             (sttfa.impl
                                              (sub_hk k h m nat.O f p1
                                               f2 f1)
                                              (logic.eq nat.nat
                                               (bigop nat.nat nat.O
                                                (λ
                                                   (
                                                   i0 : sttfa.etap
                                                        (sttfa.p nat.nat)
                                                   ), p1 i0)
                                                (nat.S nat.O) nat.times
                                                (λ
                                                   (
                                                   i0 : sttfa.etap
                                                        (sttfa.p nat.nat)
                                                   ), f1 i0))
                                               (bigop nat.nat m
                                                (λ
                                                   (
                                                   i0 : sttfa.etap
                                                        (sttfa.p nat.nat)
                                                   ), f i0)
                                                (nat.S nat.O) nat.times
                                                (λ
                                                   (
                                                   i0 : sttfa.etap
                                                        (sttfa.p nat.nat)
                                                   ), f2 i0)))))))
                                        (sttfa.forall
                                         (sttfa.arrow nat.nat bool.bool)
                                         (λ
                                            (
                                            p20 : sttfa.etap
                                                  (sttfa.p
                                                   (sttfa.arrow nat.nat
                                                    bool.bool))
                                            ),
                                            sttfa.impl (nat.le nat.O n1)
                                            (sttfa.impl
                                             (sub_hk h k nat.O
                                              (nat.S m) p1 p20 f1 f2)
                                             (sttfa.impl
                                              (sub_hk k h (nat.S m)
                                               nat.O p20 p1 f2 f1)
                                              (sttfa.forall nat.nat
                                               (λ
                                                  (
                                                  x2571 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                  ),
                                                  sttfa.forall nat.nat
                                                  (λ
                                                     (
                                                     x2572 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                     ),
                                                     logic.eq nat.nat x2571
                                                     (nat.plus
                                                      (nat.times x2572
                                                       (div_mod.div x2571
                                                        x2572))
                                                      (div_mod.mod x2571
                                                       x2572)))))))))))))))))))))))))
  ≔ λ (n1 : sttfa.etap (sttfa.p nat.nat)),
        λ (n2 : sttfa.etap (sttfa.p nat.nat)),
          λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                λ (f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                  λ (_clearme : sttfa.eps (iso n1 n2 p1 p2 f1 f2)),
                    λ
                      (h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      λ
                        (
                        _clearme0 : sttfa.eps
                                    (connectives.ex
                                     (sttfa.arrow nat.nat nat.nat)
                                     (λ
                                        (
                                        k : sttfa.etap
                                            (sttfa.p
                                             (sttfa.arrow nat.nat nat.nat))
                                        ),
                                        connectives.And
                                        (connectives.And
                                         (sttfa.forall nat.nat
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ),
                                             sttfa.impl (nat.lt i n1)
                                             (sttfa.impl
                                              (logic.eq bool.bool (p1 i)
                                               bool.true)
                                              (logic.eq nat.nat (f1 i)
                                               (f2 (h i))))))
                                         (sub_hk h k n1 n2 p1 p2 f1 f2))
                                        (sub_hk k h n2 n1 p2 p1 f2 f1)))
                        ),
                        λ
                          (
                          k : sttfa.etap
                              (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          λ
                            (
                            _clearme1 : sttfa.eps
                                        (connectives.And
                                         (connectives.And
                                          (sttfa.forall nat.nat
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ),
                                              sttfa.impl (nat.lt i n1)
                                              (sttfa.impl
                                               (logic.eq bool.bool (p1 i)
                                                bool.true)
                                               (logic.eq nat.nat (f1 i)
                                                (f2 (h i))))))
                                          (sub_hk h k n1 n2 p1 p2 f1
                                           f2))
                                         (sub_hk k h n2 n1 p2 p1 f2 f1))
                            ),
                            λ
                              (
                              _clearme2 : sttfa.eps
                                          (connectives.And
                                           (sttfa.forall nat.nat
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ),
                                               sttfa.impl (nat.lt i n1)
                                               (sttfa.impl
                                                (logic.eq bool.bool (p1 i)
                                                 bool.true)
                                                (logic.eq nat.nat (f1 i)
                                                 (f2 (h i))))))
                                           (sub_hk h k n1 n2 p1 p2 f1
                                            f2))
                              ),
                              λ
                                (
                                same : sttfa.eps
                                       (sttfa.forall nat.nat
                                        (λ
                                           (i : sttfa.etap (sttfa.p nat.nat)),
                                           sttfa.impl (nat.lt i n1)
                                           (sttfa.impl
                                            (logic.eq bool.bool (p1 i)
                                             bool.true)
                                            (logic.eq nat.nat (f1 i)
                                             (f2 (h i))))))
                                ),
                                λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  λ (m : sttfa.etap (sttfa.p nat.nat)),
                                    λ
                                      (
                                      Hind : sttfa.eps
                                             (sttfa.forall
                                              (sttfa.arrow nat.nat bool.bool)
                                              (λ
                                                 (
                                                 f : sttfa.etap
                                                     (sttfa.p
                                                      (sttfa.arrow nat.nat
                                                       bool.bool))
                                                 ),
                                                 sttfa.impl (nat.le nat.O n1)
                                                 (sttfa.impl
                                                  (sub_hk h k nat.O m
                                                   p1 f f1 f2)
                                                  (sttfa.impl
                                                   (sub_hk k h m nat.O
                                                    f p1 f2 f1)
                                                   (logic.eq nat.nat
                                                    (bigop nat.nat
                                                     nat.O
                                                     (λ
                                                        (
                                                        i0 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), p1 i0)
                                                     (nat.S nat.O) nat.times
                                                     (λ
                                                        (
                                                        i0 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), f1 i0))
                                                    (bigop nat.nat m
                                                     (λ
                                                        (
                                                        i0 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), f i0)
                                                     (nat.S nat.O) nat.times
                                                     (λ
                                                        (
                                                        i0 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), f2 i0)))))))
                                      ),
                                      λ
                                        (
                                        p20 : sttfa.etap
                                              (sttfa.p
                                               (sttfa.arrow nat.nat bool.bool))
                                        ),
                                        λ
                                          (__ : sttfa.eps (nat.le nat.O n1)),
                                          λ
                                            (
                                            sub1 : sttfa.eps
                                                   (sub_hk h k nat.O
                                                    (nat.S m) p1 p20 f1 f2)
                                            ),
                                            λ
                                              (
                                              sub2 : sttfa.eps
                                                     (sub_hk k h
                                                      (nat.S m) nat.O p20 p1
                                                      f2 f1)
                                              ),
                                              λ
                                                (
                                                x2571 : sttfa.etap
                                                        (sttfa.p nat.nat)
                                                ),
                                                λ
                                                  (
                                                  x2572 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                  ),
                                                  logic.rewrite_l nat.nat
                                                  (nat.times
                                                   (div_mod.div x2571 x2572)
                                                   x2572)
                                                  (λ
                                                     (
                                                     __1 : sttfa.etap
                                                           (sttfa.p nat.nat)
                                                     ),
                                                     logic.eq nat.nat x2571
                                                     (nat.plus __1
                                                      (div_mod.mod x2571
                                                       x2572)))
                                                  (div_mod.div_mod x2571
                                                   x2572)
                                                  (nat.times x2572
                                                   (div_mod.div x2571 x2572))
                                                  (nat.commutative_times
                                                   (div_mod.div x2571 x2572)
                                                   x2572);
symbol bigop_iso
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (n2 : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat bool.bool)
           (λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              sttfa.forall (sttfa.arrow nat.nat bool.bool)
              (λ
                 (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
                 sttfa.forall (sttfa.arrow nat.nat nat.nat)
                 (λ
                    (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    sttfa.forall (sttfa.arrow nat.nat nat.nat)
                    (λ
                       (
                       f2 : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       sttfa.impl (iso n1 n2 p1 p2 f1 f2)
                       (logic.eq nat.nat
                        (bigop nat.nat n1
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f1 i))
                        (bigop nat.nat n2
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f2 i))))))))))
  ≔ λ (n1 : sttfa.etap (sttfa.p nat.nat)),
        λ (n2 : sttfa.etap (sttfa.p nat.nat)),
          λ (p1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
            λ (p2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat bool.bool))),
              λ (f1 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                λ (f2 : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                  λ (_clearme : sttfa.eps (iso n1 n2 p1 p2 f1 f2)),
                    connectives.match_ex_prop (sttfa.arrow nat.nat nat.nat)
                    (λ
                       (
                       h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       connectives.ex (sttfa.arrow nat.nat nat.nat)
                       (λ
                          (
                          k : sttfa.etap
                              (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          connectives.And
                          (connectives.And
                           (sttfa.forall nat.nat
                            (λ (i : sttfa.etap (sttfa.p nat.nat)),
                               sttfa.impl (nat.lt i n1)
                               (sttfa.impl
                                (logic.eq bool.bool (p1 i) bool.true)
                                (logic.eq nat.nat (f1 i) (f2 (h i))))))
                           (sub_hk h k n1 n2 p1 p2 f1 f2))
                          (sub_hk k h n2 n1 p2 p1 f2 f1)))
                    (logic.eq nat.nat
                     (bigop nat.nat n1
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                      (nat.S nat.O) nat.times
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), f1 i))
                     (bigop nat.nat n2
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                      (nat.S nat.O) nat.times
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), f2 i)))
                    (λ
                       (
                       h : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       λ
                         (
                         _clearme0 : sttfa.eps
                                     (connectives.ex
                                      (sttfa.arrow nat.nat nat.nat)
                                      (λ
                                         (
                                         k : sttfa.etap
                                             (sttfa.p
                                              (sttfa.arrow nat.nat nat.nat))
                                         ),
                                         connectives.And
                                         (connectives.And
                                          (sttfa.forall nat.nat
                                           (λ
                                              (
                                              i : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ),
                                              sttfa.impl (nat.lt i n1)
                                              (sttfa.impl
                                               (logic.eq bool.bool (p1 i)
                                                bool.true)
                                               (logic.eq nat.nat (f1 i)
                                                (f2 (h i))))))
                                          (sub_hk h k n1 n2 p1 p2 f1
                                           f2))
                                         (sub_hk k h n2 n1 p2 p1 f2 f1)))
                         ),
                         connectives.match_ex_prop
                         (sttfa.arrow nat.nat nat.nat)
                         (λ
                            (
                            k : sttfa.etap
                                (sttfa.p (sttfa.arrow nat.nat nat.nat))
                            ),
                            connectives.And
                            (connectives.And
                             (sttfa.forall nat.nat
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 sttfa.impl (nat.lt i n1)
                                 (sttfa.impl
                                  (logic.eq bool.bool (p1 i) bool.true)
                                  (logic.eq nat.nat (f1 i) (f2 (h i))))))
                             (sub_hk h k n1 n2 p1 p2 f1 f2))
                            (sub_hk k h n2 n1 p2 p1 f2 f1))
                         (logic.eq nat.nat
                          (bigop nat.nat n1
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                           (nat.S nat.O) nat.times
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), f1 i))
                          (bigop nat.nat n2
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                           (nat.S nat.O) nat.times
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), f2 i)))
                         (λ
                            (
                            k : sttfa.etap
                                (sttfa.p (sttfa.arrow nat.nat nat.nat))
                            ),
                            λ
                              (
                              _clearme1 : sttfa.eps
                                          (connectives.And
                                           (connectives.And
                                            (sttfa.forall nat.nat
                                             (λ
                                                (
                                                i : sttfa.etap
                                                    (sttfa.p nat.nat)
                                                ),
                                                sttfa.impl (nat.lt i n1)
                                                (sttfa.impl
                                                 (logic.eq bool.bool (p1 i)
                                                  bool.true)
                                                 (logic.eq nat.nat (f1 i)
                                                  (f2 (h i))))))
                                            (sub_hk h k n1 n2 p1 p2 f1
                                             f2))
                                           (sub_hk k h n2 n1 p2 p1 f2
                                            f1))
                              ),
                              connectives.match_And_prop
                              (connectives.And
                               (sttfa.forall nat.nat
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   sttfa.impl (nat.lt i n1)
                                   (sttfa.impl
                                    (logic.eq bool.bool (p1 i) bool.true)
                                    (logic.eq nat.nat (f1 i) (f2 (h i))))))
                               (sub_hk h k n1 n2 p1 p2 f1 f2))
                              (sub_hk k h n2 n1 p2 p1 f2 f1)
                              (logic.eq nat.nat
                               (bigop nat.nat n1
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p1 i)
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f1 i))
                               (bigop nat.nat n2
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), p2 i)
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f2 i)))
                              (λ
                                 (
                                 _clearme2 : sttfa.eps
                                             (connectives.And
                                              (sttfa.forall nat.nat
                                               (λ
                                                  (
                                                  i : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ),
                                                  sttfa.impl (nat.lt i n1)
                                                  (sttfa.impl
                                                   (logic.eq bool.bool (p1 i)
                                                    bool.true)
                                                   (logic.eq nat.nat (f1 i)
                                                    (f2 (h i))))))
                                              (sub_hk h k n1 n2 p1 p2
                                               f1 f2))
                                 ),
                                 connectives.match_And_prop
                                 (sttfa.forall nat.nat
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     sttfa.impl (nat.lt i n1)
                                     (sttfa.impl
                                      (logic.eq bool.bool (p1 i) bool.true)
                                      (logic.eq nat.nat (f1 i) (f2 (h i))))))
                                 (sub_hk h k n1 n2 p1 p2 f1 f2)
                                 (sttfa.impl
                                  (sub_hk k h n2 n1 p2 p1 f2 f1)
                                  (logic.eq nat.nat
                                   (bigop nat.nat n1
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       p1 i)
                                    (nat.S nat.O) nat.times
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       f1 i))
                                   (bigop nat.nat n2
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       p2 i)
                                    (nat.S nat.O) nat.times
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       f2 i))))
                                 (λ
                                    (
                                    same : sttfa.eps
                                           (sttfa.forall nat.nat
                                            (λ
                                               (
                                               i : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ),
                                               sttfa.impl (nat.lt i n1)
                                               (sttfa.impl
                                                (logic.eq bool.bool (p1 i)
                                                 bool.true)
                                                (logic.eq nat.nat (f1 i)
                                                 (f2 (h i))))))
                                    ),
                                    nat.le_gen
                                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                       sttfa.impl
                                       (sub_hk h k __ n2 p1 p2 f1 f2)
                                       (sttfa.impl
                                        (sub_hk k h n2 __ p2 p1 f2 f1)
                                        (logic.eq nat.nat
                                         (bigop nat.nat __
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p1 i)
                                          (nat.S nat.O) nat.times
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), f1 i))
                                         (bigop nat.nat n2
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), p2 i)
                                          (nat.S nat.O) nat.times
                                          (λ
                                             (
                                             i : sttfa.etap (sttfa.p nat.nat)
                                             ), f2 i)))))
                                    n1
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       nat.nat_ind
                                       (λ
                                          (
                                          _x_365 : sttfa.etap
                                                   (sttfa.p nat.nat)
                                          ),
                                          sttfa.forall
                                          (sttfa.arrow nat.nat bool.bool)
                                          (λ
                                             (
                                             f : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat
                                                   bool.bool))
                                             ),
                                             sttfa.impl (nat.le _x_365 n1)
                                             (sttfa.impl
                                              (sub_hk h k _x_365 n2 p1
                                               f f1 f2)
                                              (sttfa.impl
                                               (sub_hk k h n2 _x_365 f
                                                p1 f2 f1)
                                               (logic.eq nat.nat
                                                (bigop nat.nat _x_365
                                                 (λ
                                                    (
                                                    i0 : sttfa.etap
                                                         (sttfa.p nat.nat)
                                                    ), p1 i0)
                                                 (nat.S nat.O) nat.times
                                                 (λ
                                                    (
                                                    i0 : sttfa.etap
                                                         (sttfa.p nat.nat)
                                                    ), f1 i0))
                                                (bigop nat.nat n2
                                                 (λ
                                                    (
                                                    i0 : sttfa.etap
                                                         (sttfa.p nat.nat)
                                                    ), f i0)
                                                 (nat.S nat.O) nat.times
                                                 (λ
                                                    (
                                                    i0 : sttfa.etap
                                                         (sttfa.p nat.nat)
                                                    ), f2 i0)))))))
                                       (nat.nat_ind
                                        (λ
                                           (
                                           _x_365 : sttfa.etap
                                                    (sttfa.p nat.nat)
                                           ),
                                           sttfa.forall
                                           (sttfa.arrow nat.nat bool.bool)
                                           (λ
                                              (
                                              f : sttfa.etap
                                                  (sttfa.p
                                                   (sttfa.arrow nat.nat
                                                    bool.bool))
                                              ),
                                              sttfa.impl (nat.le nat.O n1)
                                              (sttfa.impl
                                               (sub_hk h k nat.O
                                                _x_365 p1 f f1 f2)
                                               (sttfa.impl
                                                (sub_hk k h _x_365
                                                 nat.O f p1 f2 f1)
                                                (logic.eq nat.nat
                                                 (bigop nat.nat nat.O
                                                  (λ
                                                     (
                                                     i0 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), p1 i0)
                                                  (nat.S nat.O) nat.times
                                                  (λ
                                                     (
                                                     i0 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f1 i0))
                                                 (bigop nat.nat _x_365
                                                  (λ
                                                     (
                                                     i0 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f i0)
                                                  (nat.S nat.O) nat.times
                                                  (λ
                                                     (
                                                     i0 : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f2 i0)))))))
                                        (λ
                                           (
                                           f : sttfa.etap
                                               (sttfa.p
                                                (sttfa.arrow nat.nat
                                                 bool.bool))
                                           ),
                                           sym_eq_bigop_O nat.nat
                                           (λ
                                              (
                                              y : sttfa.etap
                                                  (sttfa.p
                                                   (sttfa.arrow
                                                    (sttfa.arrow nat.nat
                                                     bool.bool)
                                                    (sttfa.arrow nat.nat
                                                     (sttfa.arrow
                                                      (sttfa.arrow nat.nat
                                                       (sttfa.arrow nat.nat
                                                        nat.nat))
                                                      (sttfa.arrow
                                                       (sttfa.arrow nat.nat
                                                        nat.nat)
                                                       nat.nat)))))
                                              ),
                                              sttfa.impl (nat.le nat.O n1)
                                              (sttfa.impl
                                               (sub_hk h k nat.O nat.O
                                                p1 f f1 f2)
                                               (sttfa.impl
                                                (sub_hk k h nat.O
                                                 nat.O f p1 f2 f1)
                                                (logic.eq nat.nat
                                                 (bigop nat.nat nat.O
                                                  (λ
                                                     (
                                                     iO : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), p1 iO)
                                                  (nat.S nat.O) nat.times
                                                  (λ
                                                     (
                                                     iO : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f1 iO))
                                                 (y
                                                  (λ
                                                     (
                                                     iO : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f iO)
                                                  (nat.S nat.O) nat.times
                                                  (λ
                                                     (
                                                     iO : sttfa.etap
                                                          (sttfa.p nat.nat)
                                                     ), f2 iO))))))
                                           (sym_eq_bigop_body_O
                                            nat.nat
                                            (λ
                                               (
                                               y : sttfa.etap
                                                   (sttfa.p
                                                    (sttfa.arrow
                                                     (sttfa.arrow nat.nat
                                                      bool.bool)
                                                     (sttfa.arrow nat.nat
                                                      (sttfa.arrow
                                                       (sttfa.arrow nat.nat
                                                        (sttfa.arrow nat.nat
                                                         nat.nat))
                                                       (sttfa.arrow
                                                        (sttfa.arrow nat.nat
                                                         nat.nat)
                                                        nat.nat)))))
                                               ),
                                               sttfa.impl (nat.le nat.O n1)
                                               (sttfa.impl
                                                (sub_hk h k nat.O
                                                 nat.O p1 f f1 f2)
                                                (sttfa.impl
                                                 (sub_hk k h nat.O
                                                  nat.O f p1 f2 f1)
                                                 (logic.eq nat.nat
                                                  (bigop nat.nat nat.O
                                                   (λ
                                                      (
                                                      iO : sttfa.etap
                                                           (sttfa.p nat.nat)
                                                      ), p1 iO)
                                                   (nat.S nat.O) nat.times
                                                   (λ
                                                      (
                                                      iO : sttfa.etap
                                                           (sttfa.p nat.nat)
                                                      ), f1 iO))
                                                  (y
                                                   (λ
                                                      (
                                                      iO : sttfa.etap
                                                           (sttfa.p nat.nat)
                                                      ), f iO)
                                                   (nat.S nat.O) nat.times
                                                   (λ
                                                      (
                                                      iO : sttfa.etap
                                                           (sttfa.p nat.nat)
                                                      ), f2 iO))))))
                                            (eq_bigop_body_O nat.nat
                                             (λ
                                                (
                                                y : sttfa.etap
                                                    (sttfa.p
                                                     (sttfa.arrow
                                                      (sttfa.arrow nat.nat
                                                       bool.bool)
                                                      (sttfa.arrow nat.nat
                                                       (sttfa.arrow
                                                        (sttfa.arrow nat.nat
                                                         (sttfa.arrow nat.nat
                                                          nat.nat))
                                                        (sttfa.arrow
                                                         (sttfa.arrow nat.nat
                                                          nat.nat)
                                                         nat.nat)))))
                                                ),
                                                sttfa.impl (nat.le nat.O n1)
                                                (sttfa.impl
                                                 (sub_hk h k nat.O
                                                  nat.O p1 f f1 f2)
                                                 (sttfa.impl
                                                  (sub_hk k h nat.O
                                                   nat.O f p1 f2 f1)
                                                  (logic.eq nat.nat
                                                   (bigop nat.nat
                                                    nat.O
                                                    (λ
                                                       (
                                                       iO : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                       ), p1 iO)
                                                    (nat.S nat.O) nat.times
                                                    (λ
                                                       (
                                                       iO : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                       ), f1 iO))
                                                   (y
                                                    (λ
                                                       (
                                                       iO : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                       ), p1 iO)
                                                    (nat.S nat.O) nat.times
                                                    (λ
                                                       (
                                                       iO : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                       ), f1 iO))))))
                                             (eq_bigop_O nat.nat
                                              (λ
                                                 (
                                                 y : sttfa.etap
                                                     (sttfa.p
                                                      (sttfa.arrow
                                                       (sttfa.arrow nat.nat
                                                        bool.bool)
                                                       (sttfa.arrow nat.nat
                                                        (sttfa.arrow
                                                         (sttfa.arrow nat.nat
                                                          (sttfa.arrow
                                                           nat.nat nat.nat))
                                                         (sttfa.arrow
                                                          (sttfa.arrow
                                                           nat.nat nat.nat)
                                                          nat.nat)))))
                                                 ),
                                                 sttfa.impl (nat.le nat.O n1)
                                                 (sttfa.impl
                                                  (sub_hk h k nat.O
                                                   nat.O p1 f f1 f2)
                                                  (sttfa.impl
                                                   (sub_hk k h nat.O
                                                    nat.O f p1 f2 f1)
                                                   (logic.eq nat.nat
                                                    (bigop nat.nat
                                                     nat.O
                                                     (λ
                                                        (
                                                        iO : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), p1 iO)
                                                     (nat.S nat.O) nat.times
                                                     (λ
                                                        (
                                                        iO : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), f1 iO))
                                                    (y
                                                     (λ
                                                        (
                                                        iO : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), p1 iO)
                                                     (nat.S nat.O) nat.times
                                                     (λ
                                                        (
                                                        iO : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                        ), f1 iO))))))
                                              (λ
                                                 (
                                                 auto : sttfa.eps
                                                        (nat.le nat.O n1)
                                                 ),
                                                 λ
                                                   (
                                                   auto' : sttfa.eps
                                                           (sub_hk h k
                                                            nat.O nat.O p1 f
                                                            f1 f2)
                                                   ),
                                                   λ
                                                     (
                                                     auto'' : sttfa.eps
                                                              (sub_hk
                                                               k h nat.O
                                                               nat.O f p1 f2
                                                               f1)
                                                     ),
                                                     logic.refl nat.nat
                                                     (bigop nat.nat
                                                      nat.O
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), p1 i0)
                                                      (nat.S nat.O) nat.times
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), f1 i0)))))))
                                        (λ
                                           (m : sttfa.etap (sttfa.p nat.nat)),
                                           λ
                                             (
                                             Hind : sttfa.eps
                                                    (sttfa.forall
                                                     (sttfa.arrow nat.nat
                                                      bool.bool)
                                                     (λ
                                                        (
                                                        f : sttfa.etap
                                                            (sttfa.p
                                                             (sttfa.arrow
                                                              nat.nat
                                                              bool.bool))
                                                        ),
                                                        sttfa.impl
                                                        (nat.le nat.O n1)
                                                        (sttfa.impl
                                                         (sub_hk h k
                                                          nat.O m p1 f f1 f2)
                                                         (sttfa.impl
                                                          (sub_hk k h
                                                           m nat.O f p1 f2 f1)
                                                          (logic.eq nat.nat
                                                           (bigop
                                                            nat.nat nat.O
                                                            (λ
                                                               (
                                                               i0 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                               ), p1 i0)
                                                            (nat.S nat.O)
                                                            nat.times
                                                            (λ
                                                               (
                                                               i0 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                               ), f1 i0))
                                                           (bigop
                                                            nat.nat m
                                                            (λ
                                                               (
                                                               i0 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                               ), f i0)
                                                            (nat.S nat.O)
                                                            nat.times
                                                            (λ
                                                               (
                                                               i0 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                               ), f2 i0)))))))
                                             ),
                                             λ
                                               (
                                               p20 : sttfa.etap
                                                     (sttfa.p
                                                      (sttfa.arrow nat.nat
                                                       bool.bool))
                                               ),
                                               λ
                                                 (
                                                 __ : sttfa.eps
                                                      (nat.le nat.O n1)
                                                 ),
                                                 λ
                                                   (
                                                   sub1 : sttfa.eps
                                                          (sub_hk h k
                                                           nat.O (nat.S m) p1
                                                           p20 f1 f2)
                                                   ),
                                                   λ
                                                     (
                                                     sub2 : sttfa.eps
                                                            (sub_hk k
                                                             h (nat.S m)
                                                             nat.O p20 p1 f2
                                                             f1)
                                                     ),
                                                     logic.eq_ind_r nat.nat
                                                     (bigop nat.nat m
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), p20 i0)
                                                      (nat.S nat.O) nat.times
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), f2 i0))
                                                     (λ
                                                        (
                                                        x : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                        ),
                                                        logic.eq nat.nat
                                                        (bigop nat.nat
                                                         nat.O
                                                         (λ
                                                            (
                                                            i0 : sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                            ), p1 i0)
                                                         (nat.S nat.O)
                                                         nat.times
                                                         (λ
                                                            (
                                                            i0 : sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                            ), f1 i0))
                                                        x)
                                                     (Hind p20
                                                      (nat.le_O_n n1)
                                                      (sub_hkO h k
                                                       nat.O m p1 p20 f1 f2
                                                       (logic.refl nat.nat
                                                        nat.O))
                                                      (transitive_sub
                                                       (λ
                                                          (
                                                          x : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                          ), x)
                                                       (λ
                                                          (
                                                          x : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                          ), x)
                                                       k h m (nat.S m) nat.O
                                                       p20 p20 p1 f2 f2 f1
                                                       (sub_lt f2 p20
                                                        m (nat.S m)
                                                        (nat.le_n_Sn m))
                                                       sub2))
                                                     (bigop nat.nat
                                                      (nat.S m)
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), p20 i0)
                                                      (nat.S nat.O) nat.times
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), f2 i0))
                                                     (bigop_Sfalse
                                                      nat.nat m p20
                                                      (nat.S nat.O) nat.times
                                                      f2
                                                      (sub0_to_false k
                                                       h nat.O (nat.S m) p1
                                                       p20 f1 f2
                                                       (logic.refl nat.nat
                                                        nat.O)
                                                       sub2 m
                                                       (logic.eq_coerc
                                                        (nat.lt
                                                         (div_mod.mod m nat.O)
                                                         (nat.plus
                                                          (nat.plus
                                                           (div_mod.mod m
                                                            nat.O)
                                                           (nat.times nat.O
                                                            (div_mod.div m
                                                             nat.O)))
                                                          (nat.S nat.O)))
                                                        (nat.lt m (nat.S m))
                                                        (nat.lt_plus_Sn_r
                                                         (div_mod.mod m nat.O)
                                                         (nat.times nat.O
                                                          (div_mod.div m
                                                           nat.O))
                                                         nat.O)
                                                        (logic.rewrite_l
                                                         nat.nat m
                                                         (λ
                                                            (
                                                            __1 : sttfa.etap
                                                                  (sttfa.p
                                                                   nat.nat)
                                                            ),
                                                            logic.eq
                                                            sttfa.bool
                                                            (nat.lt
                                                             (div_mod.mod m
                                                              nat.O)
                                                             (nat.plus __1
                                                              (nat.S nat.O)))
                                                            (nat.lt m
                                                             (nat.S m)))
                                                         (logic.rewrite_l
                                                          nat.nat m
                                                          (λ
                                                             (
                                                             __1 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                             ),
                                                             logic.eq
                                                             sttfa.bool
                                                             (nat.lt __1
                                                              (nat.plus m
                                                               (nat.S nat.O)))
                                                             (nat.lt m
                                                              (nat.S m)))
                                                          (logic.rewrite_l
                                                           nat.nat (nat.S m)
                                                           (λ
                                                              (
                                                              __1 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                              ),
                                                              logic.eq
                                                              sttfa.bool
                                                              (nat.lt m __1)
                                                              (nat.lt m
                                                               (nat.S m)))
                                                           (logic.refl
                                                            sttfa.bool
                                                            (nat.lt m
                                                             (nat.S m)))
                                                           (nat.plus m
                                                            (nat.S nat.O))
                                                           (logic.rewrite_r
                                                            nat.nat
                                                            (nat.plus m nat.O)
                                                            (λ
                                                               (
                                                               __1 : 
                                                                 sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                               ),
                                                               logic.eq
                                                               nat.nat
                                                               (nat.S __1)
                                                               (nat.plus m
                                                                (nat.S nat.O)))
                                                            (nat.plus_n_Sm m
                                                             nat.O)
                                                            m
                                                            (nat.plus_n_O m)))
                                                          (div_mod.mod m
                                                           nat.O)
                                                          (logic.rewrite_r
                                                           nat.nat
                                                           (nat.plus nat.O
                                                            (div_mod.mod m
                                                             nat.O))
                                                           (λ
                                                              (
                                                              __1 : sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                              ),
                                                              logic.eq
                                                              nat.nat m __1)
                                                           (logic.rewrite_l
                                                            nat.nat
                                                            (nat.plus
                                                             (div_mod.mod m
                                                              nat.O)
                                                             nat.O)
                                                            (λ
                                                               (
                                                               __1 : 
                                                                 sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                               ),
                                                               logic.eq
                                                               nat.nat m __1)
                                                            (logic.rewrite_r
                                                             nat.nat
                                                             (nat.times nat.O
                                                              (div_mod.div m
                                                               nat.O))
                                                             (λ
                                                                (
                                                                __1 : 
                                                                  sttfa.etap
                                                                  (sttfa.p
                                                                   nat.nat)
                                                                ),
                                                                logic.eq
                                                                nat.nat m
                                                                (nat.plus
                                                                 (div_mod.mod
                                                                  m nat.O)
                                                                 __1))
                                                             (logic.rewrite_l
                                                              nat.nat
                                                              (nat.plus
                                                               (nat.times
                                                                nat.O
                                                                (div_mod.div
                                                                 m nat.O))
                                                               (div_mod.mod m
                                                                nat.O))
                                                              (λ
                                                                 (
                                                                 __1 : 
                                                                   sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                                 ),
                                                                 logic.eq
                                                                 nat.nat m
                                                                 __1)
                                                              (let_clause_10471
                                                               n1 n2 p1 p2 f1
                                                               f2 _clearme h
                                                               _clearme0 k
                                                               _clearme1
                                                               _clearme2 same
                                                               i m Hind p20
                                                               __ sub1 sub2 m
                                                               nat.O)
                                                              (nat.plus
                                                               (div_mod.mod m
                                                                nat.O)
                                                               (nat.times
                                                                nat.O
                                                                (div_mod.div
                                                                 m nat.O)))
                                                              (nat.commutative_plus
                                                               (nat.times
                                                                nat.O
                                                                (div_mod.div
                                                                 m nat.O))
                                                               (div_mod.mod m
                                                                nat.O)))
                                                             nat.O
                                                             (nat.times_O_n
                                                              (div_mod.div m
                                                               nat.O)))
                                                            (nat.plus nat.O
                                                             (div_mod.mod m
                                                              nat.O))
                                                            (nat.commutative_plus
                                                             (div_mod.mod m
                                                              nat.O)
                                                             nat.O))
                                                           (div_mod.mod m
                                                            nat.O)
                                                           (nat.plus_O_n
                                                            (div_mod.mod m
                                                             nat.O))))
                                                         (nat.plus
                                                          (div_mod.mod m
                                                           nat.O)
                                                          (nat.times nat.O
                                                           (div_mod.div m
                                                            nat.O)))
                                                         (logic.rewrite_l
                                                          nat.nat
                                                          (nat.plus
                                                           (nat.times nat.O
                                                            (div_mod.div m
                                                             nat.O))
                                                           (div_mod.mod m
                                                            nat.O))
                                                          (λ
                                                             (
                                                             __1 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                             ),
                                                             logic.eq nat.nat
                                                             m __1)
                                                          (let_clause_10471
                                                           n1 n2 p1 p2 f1 f2
                                                           _clearme h
                                                           _clearme0 k
                                                           _clearme1
                                                           _clearme2 same i m
                                                           Hind p20 __ sub1
                                                           sub2 m nat.O)
                                                          (nat.plus
                                                           (div_mod.mod m
                                                            nat.O)
                                                           (nat.times nat.O
                                                            (div_mod.div m
                                                             nat.O)))
                                                          (nat.commutative_plus
                                                           (nat.times nat.O
                                                            (div_mod.div m
                                                             nat.O))
                                                           (div_mod.mod m
                                                            nat.O))))))))
                                        n2)
                                       (λ
                                          (n : sttfa.etap (sttfa.p nat.nat)),
                                          λ
                                            (
                                            Hind : sttfa.eps
                                                   (sttfa.forall
                                                    (sttfa.arrow nat.nat
                                                     bool.bool)
                                                    (λ
                                                       (
                                                       f : sttfa.etap
                                                           (sttfa.p
                                                            (sttfa.arrow
                                                             nat.nat
                                                             bool.bool))
                                                       ),
                                                       sttfa.impl
                                                       (nat.le n n1)
                                                       (sttfa.impl
                                                        (sub_hk h k n
                                                         n2 p1 f f1 f2)
                                                        (sttfa.impl
                                                         (sub_hk k h
                                                          n2 n f p1 f2 f1)
                                                         (logic.eq nat.nat
                                                          (bigop
                                                           nat.nat n
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), p1 i0)
                                                           (nat.S nat.O)
                                                           nat.times
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f1 i0))
                                                          (bigop
                                                           nat.nat n2
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f i0)
                                                           (nat.S nat.O)
                                                           nat.times
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f2 i0)))))))
                                            ),
                                            λ
                                              (
                                              p20 : sttfa.etap
                                                    (sttfa.p
                                                     (sttfa.arrow nat.nat
                                                      bool.bool))
                                              ),
                                              λ
                                                (
                                                ltn : sttfa.eps
                                                      (nat.le (nat.S n) n1)
                                                ),
                                                λ
                                                  (
                                                  sub1 : sttfa.eps
                                                         (sub_hk h k
                                                          (nat.S n) n2 p1 p20
                                                          f1 f2)
                                                  ),
                                                  λ
                                                    (
                                                    sub2 : sttfa.eps
                                                           (sub_hk k h
                                                            n2 (nat.S n) p20
                                                            p1 f2 f1)
                                                    ),
                                                    connectives.match_Or_prop
                                                    (logic.eq bool.bool
                                                     (p1 n) bool.true)
                                                    (logic.eq bool.bool
                                                     (p1 n) bool.false)
                                                    (logic.eq nat.nat
                                                     (bigop nat.nat
                                                      (nat.S n)
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), p1 i0)
                                                      (nat.S nat.O) nat.times
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), f1 i0))
                                                     (bigop nat.nat n2
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), p20 i0)
                                                      (nat.S nat.O) nat.times
                                                      (λ
                                                         (
                                                         i0 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                         ), f2 i0)))
                                                    (λ
                                                       (
                                                       p1n : sttfa.eps
                                                             (logic.eq
                                                              bool.bool
                                                              (p1 n)
                                                              bool.true)
                                                       ),
                                                       logic.eq_ind_r nat.nat
                                                       (nat.times (f1 n)
                                                        (bigop nat.nat
                                                         n
                                                         (λ
                                                            (
                                                            i0 : sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                            ), p1 i0)
                                                         (nat.S nat.O)
                                                         nat.times
                                                         (λ
                                                            (
                                                            i0 : sttfa.etap
                                                                 (sttfa.p
                                                                  nat.nat)
                                                            ), f1 i0)))
                                                       (λ
                                                          (
                                                          x : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                          ),
                                                          logic.eq nat.nat x
                                                          (bigop
                                                           nat.nat n2
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), p20 i0)
                                                           (nat.S nat.O)
                                                           nat.times
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f2 i0)))
                                                       (connectives.match_And_prop
                                                        (connectives.And
                                                         (nat.lt (h n) n2)
                                                         (logic.eq bool.bool
                                                          (p20 (h n))
                                                          bool.true))
                                                        (logic.eq nat.nat
                                                         (k (h n)) n)
                                                        (logic.eq nat.nat
                                                         (nat.times (f1 n)
                                                          (bigop
                                                           nat.nat n
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), p1 i0)
                                                           (nat.S nat.O)
                                                           nat.times
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f1 i0)))
                                                         (bigop
                                                          nat.nat n2
                                                          (λ
                                                             (
                                                             i0 : sttfa.etap
                                                                  (sttfa.p
                                                                   nat.nat)
                                                             ), p20 i0)
                                                          (nat.S nat.O)
                                                          nat.times
                                                          (λ
                                                             (
                                                             i0 : sttfa.etap
                                                                  (sttfa.p
                                                                   nat.nat)
                                                             ), f2 i0)))
                                                        (λ
                                                           (
                                                           _clearme3 : 
                                                             sttfa.eps
                                                             (connectives.And
                                                              (nat.lt (h n)
                                                               n2)
                                                              (logic.eq
                                                               bool.bool
                                                               (p20 (h n))
                                                               bool.true))
                                                           ),
                                                           connectives.match_And_prop
                                                           (nat.lt (h n) n2)
                                                           (logic.eq
                                                            bool.bool
                                                            (p20 (h n))
                                                            bool.true)
                                                           (sttfa.impl
                                                            (logic.eq nat.nat
                                                             (k (h n)) n)
                                                            (logic.eq nat.nat
                                                             (nat.times
                                                              (f1 n)
                                                              (bigop
                                                               nat.nat n
                                                               (λ
                                                                  (
                                                                  i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                                  ), 
                                                                  p1 i0)
                                                               (nat.S nat.O)
                                                               nat.times
                                                               (λ
                                                                  (
                                                                  i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)
                                                                  ), 
                                                                  f1 i0)))
                                                             (bigop
                                                              nat.nat n2
                                                              (λ
                                                                 (
                                                                 i0 : 
                                                                   sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                                 ), p20 i0)
                                                              (nat.S nat.O)
                                                              nat.times
                                                              (λ
                                                                 (
                                                                 i0 : 
                                                                   sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                                 ), f2 i0))))
                                                           (λ
                                                              (
                                                              hn : sttfa.eps
                                                                   (nat.lt
                                                                    (
                                                                    h n) n2)
                                                              ),
                                                              λ
                                                                (
                                                                p2hn : 
                                                                  sttfa.eps
                                                                  (logic.eq
                                                                   bool.bool
                                                                   (p20 (h n))
                                                                   bool.true)
                                                                ),
                                                                λ
                                                                  (
                                                                  eqn : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h n))
                                                                    n)
                                                                  ),
                                                                  logic.eq_ind_r
                                                                  nat.nat
                                                                  (nat.times
                                                                   (f2 (h n))
                                                                   (bigop
                                                                    nat.nat
                                                                    n2
                                                                    (
                                                                    λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) x))
                                                                    (
                                                                    p20 x))
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f2 x)))
                                                                  (λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    nat.times
                                                                    (
                                                                    f1 n)
                                                                    (
                                                                    bigop
                                                                    nat.nat n
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    p1 i0)
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f1 i0)))
                                                                    x)
                                                                  (logic.eq_ind_r
                                                                   nat.nat
                                                                   (f2 (h n))
                                                                   (λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    nat.times
                                                                    x
                                                                    (
                                                                    bigop
                                                                    nat.nat n
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    p1 i0)
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f1 i0)))
                                                                    (
                                                                    nat.times
                                                                    (
                                                                    f2 (h n))
                                                                    (
                                                                    bigop
                                                                    nat.nat
                                                                    n2
                                                                    (
                                                                    λ
                                                                    (
                                                                    x0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) x0))
                                                                    (
                                                                    p20 x0))
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    x0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f2 x0))))
                                                                   (logic.eq_f
                                                                    nat.nat
                                                                    nat.nat
                                                                    (
                                                                    nat.times
                                                                    (
                                                                    f2 (h n)))
                                                                    (
                                                                    bigop
                                                                    nat.nat n
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    p1 i0)
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f1 i0))
                                                                    (
                                                                    bigop
                                                                    nat.nat
                                                                    n2
                                                                    (
                                                                    λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) x))
                                                                    (
                                                                    p20 x))
                                                                    (
                                                                    nat.S
                                                                    nat.O)
                                                                    nat.times
                                                                    (
                                                                    λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f2 x))
                                                                    (
                                                                    Hind
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) __))
                                                                    (
                                                                    p20 __))
                                                                    (
                                                                    nat.lt_to_le
                                                                    n n1 ltn)
                                                                    (
                                                                    λ
                                                                    (
                                                                    i0 : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    λ
                                                                    (
                                                                    ltin : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt i0
                                                                    n)),
                                                                    λ
                                                                    (
                                                                    p1i : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 i0)
                                                                    bool.true)
                                                                    ),
                                                                    connectives.match_And_prop
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0)
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0)))
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0)))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0))
                                                                    (
                                                                    λ
                                                                    (
                                                                    _clearme4 : 
                                                                    sttfa.eps
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.true))
                                                                    ),
                                                                    connectives.match_And_prop
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.true)
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0)
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0)))
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0)))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0)))
                                                                    (
                                                                    λ
                                                                    (
                                                                    h1i : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    ),
                                                                    λ
                                                                    (
                                                                    p2h1i : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.true)
                                                                    ),
                                                                    λ
                                                                    (
                                                                    eqi : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0)),
                                                                    connectives.conj
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0)))
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0)))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k (h i0))
                                                                    i0)
                                                                    (
                                                                    connectives.conj
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    h i0) n2)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0)))
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0)))
                                                                    bool.true)
                                                                    h1i
                                                                    (
                                                                    logic.eq_ind_r
                                                                    bool.bool
                                                                    bool.false
                                                                    (
                                                                    λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    x)
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0)))
                                                                    bool.true)
                                                                    (
                                                                    bool.sym_eq_match_bool_type_false
                                                                    bool.bool
                                                                    bool.false
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.match_bool_type
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.false
                                                                    y)
                                                                    bool.true)
                                                                    (
                                                                    bool.sym_eq_match_bool_type_true
                                                                    bool.bool
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    bool.false
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    y
                                                                    bool.true)
                                                                    (
                                                                    logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.true)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    (
                                                                    p20
                                                                    (
                                                                    h i0))
                                                                    p2h1i)))
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0))
                                                                    (
                                                                    nat.not_eq_to_eqb_false
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0)
                                                                    (
                                                                    logic.not_to_not
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    i0 n)
                                                                    (
                                                                    λ
                                                                    (
                                                                    auto : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n)
                                                                    (
                                                                    h i0))),
                                                                    logic.rewrite_r
                                                                    nat.nat n
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ n)
                                                                    (
                                                                    logic.refl
                                                                    nat.nat n)
                                                                    i0
                                                                    (
                                                                    logic.rewrite_l
                                                                    nat.nat
                                                                    (
                                                                    k (h n))
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ n) eqn
                                                                    i0
                                                                    (
                                                                    logic.rewrite_r
                                                                    nat.nat
                                                                    (
                                                                    h i0)
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k __) i0)
                                                                    eqi (
                                                                    h n) auto)))
                                                                    (
                                                                    nat.lt_to_not_eq
                                                                    i0 n ltin)))))
                                                                    (
                                                                    logic.rewrite_r
                                                                    nat.nat
                                                                    i0
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ i0)
                                                                    (
                                                                    logic.refl
                                                                    nat.nat
                                                                    i0)
                                                                    (
                                                                    k (h i0))
                                                                    eqi))
                                                                    _clearme4)
                                                                    (
                                                                    sub1 i0
                                                                    (
                                                                    nat.le_S
                                                                    (
                                                                    nat.S i0)
                                                                    n ltin)
                                                                    p1i))
                                                                    (
                                                                    λ
                                                                    (
                                                                    j : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    λ
                                                                    (
                                                                    ltj : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt j
                                                                    n2)),
                                                                    λ
                                                                    (
                                                                    p2j : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) j))
                                                                    (
                                                                    p20 j))
                                                                    bool.true)
                                                                    ),
                                                                    connectives.match_And_prop
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j)
                                                                    (
                                                                    nat.S n))
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j)
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j))
                                                                    (
                                                                    λ
                                                                    (
                                                                    _clearme4 : 
                                                                    sttfa.eps
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j)
                                                                    (
                                                                    nat.S n))
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true))
                                                                    ),
                                                                    connectives.match_And_prop
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j)
                                                                    (
                                                                    nat.S n))
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true)
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j)
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j)))
                                                                    (
                                                                    λ
                                                                    (
                                                                    ltkj : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j)
                                                                    (
                                                                    nat.S n))
                                                                    ),
                                                                    λ
                                                                    (
                                                                    p1kj : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true)
                                                                    ),
                                                                    λ
                                                                    (
                                                                    eqj : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j)),
                                                                    connectives.conj
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k j))
                                                                    j)
                                                                    (
                                                                    connectives.conj
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k j))
                                                                    bool.true)
                                                                    (
                                                                    connectives.match_Or_prop
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    λ
                                                                    (
                                                                    auto : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)),
                                                                    auto)
                                                                    (
                                                                    λ
                                                                    (
                                                                    eqkj : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k j) n)),
                                                                    connectives.falsity
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k j) n)
                                                                    (
                                                                    nat.eqb_elim
                                                                    (
                                                                    h n) j
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.andb
                                                                    (
                                                                    bool.notb
                                                                    __)
                                                                    (
                                                                    p20 j))
                                                                    bool.true)
                                                                    connectives.False)
                                                                    (
                                                                    bool.sym_eq_match_bool_type_true
                                                                    bool.bool
                                                                    bool.false
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j)
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.match_bool_type
                                                                    bool.bool
                                                                    (
                                                                    p20 j)
                                                                    bool.false
                                                                    y)
                                                                    bool.true)
                                                                    connectives.False))
                                                                    (
                                                                    bool.sym_eq_match_bool_type_false
                                                                    bool.bool
                                                                    (
                                                                    p20 j)
                                                                    bool.false
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j)
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    y
                                                                    bool.true)
                                                                    connectives.False))
                                                                    (
                                                                    λ
                                                                    (
                                                                    auto : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j)),
                                                                    λ
                                                                    (
                                                                    auto' : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    bool.false
                                                                    bool.true)
                                                                    ),
                                                                    logic.absurd
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    bool.true
                                                                    bool.false)
                                                                    (
                                                                    logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    bool.true
                                                                    __)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    bool.false
                                                                    auto')
                                                                    bool.not_eq_true_false)))
                                                                    (
                                                                    bool.sym_eq_match_bool_type_false
                                                                    bool.bool
                                                                    bool.false
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    sttfa.impl
                                                                    (
                                                                    connectives.Not
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j))
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    bool.match_bool_type
                                                                    bool.bool
                                                                    (
                                                                    p20 j)
                                                                    bool.false
                                                                    y)
                                                                    bool.true)
                                                                    connectives.False))
                                                                    (
                                                                    bool.sym_eq_match_bool_type_true
                                                                    bool.bool
                                                                    (
                                                                    p20 j)
                                                                    bool.false
                                                                    (
                                                                    λ
                                                                    (
                                                                    y : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    sttfa.impl
                                                                    (
                                                                    connectives.Not
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j))
                                                                    (
                                                                    sttfa.impl
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    y
                                                                    bool.true)
                                                                    connectives.False))
                                                                    (
                                                                    λ
                                                                    (
                                                                    auto : 
                                                                    sttfa.eps
                                                                    (
                                                                    connectives.Not
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j))),
                                                                    λ
                                                                    (
                                                                    auto' : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p20 j)
                                                                    bool.true)
                                                                    ),
                                                                    logic.absurd
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h n) j)
                                                                    (
                                                                    logic.rewrite_r
                                                                    nat.nat j
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ j)
                                                                    (
                                                                    logic.refl
                                                                    nat.nat j)
                                                                    (
                                                                    h n)
                                                                    (
                                                                    logic.rewrite_l
                                                                    nat.nat
                                                                    (
                                                                    k j)
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h __) j)
                                                                    eqj n
                                                                    eqkj))
                                                                    auto)))
                                                                    p2j))
                                                                    (
                                                                    nat.le_to_or_lt_eq
                                                                    (
                                                                    k j) n
                                                                    (
                                                                    nat.le_S_S_to_le
                                                                    (
                                                                    k j) n
                                                                    ltkj)))
                                                                    (
                                                                    logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.true)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    (
                                                                    p1 (k j))
                                                                    p1kj))
                                                                    (
                                                                    logic.rewrite_r
                                                                    nat.nat j
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ j)
                                                                    (
                                                                    logic.refl
                                                                    nat.nat j)
                                                                    (
                                                                    h (k j))
                                                                    eqj))
                                                                    _clearme4)
                                                                    (
                                                                    sub2 j
                                                                    ltj
                                                                    (
                                                                    bool.andb_true_r
                                                                    (
                                                                    bool.notb
                                                                    (
                                                                    nat.eqb
                                                                    (
                                                                    h n) j))
                                                                    (
                                                                    p20 j)
                                                                    p2j)))))
                                                                   (f1 n)
                                                                   (same n
                                                                    ltn
                                                                    (
                                                                    logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.true)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    (
                                                                    p1 n) p1n)))
                                                                  (bigop
                                                                   nat.nat n2
                                                                   (λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    p20 x)
                                                                   (nat.S
                                                                    nat.O)
                                                                   nat.times
                                                                   (λ
                                                                    (
                                                                    x : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    f2 x))
                                                                  (bigop_diff
                                                                   p20 f2
                                                                   (h n) n2
                                                                   hn
                                                                   (logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.true)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    (
                                                                    p20 (h n))
                                                                    p2hn)))
                                                           _clearme3)
                                                        (sub1 n
                                                         (nat.le_n (nat.S n))
                                                         p1n))
                                                       (bigop nat.nat
                                                        (nat.S n)
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), p1 i0)
                                                        (nat.S nat.O)
                                                        nat.times
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), f1 i0))
                                                       (bigop_Strue
                                                        nat.nat n p1
                                                        (nat.S nat.O)
                                                        nat.times f1
                                                        (logic.rewrite_r
                                                         bool.bool bool.true
                                                         (λ
                                                            (
                                                            __ : sttfa.etap
                                                                 (sttfa.p
                                                                  bool.bool)
                                                            ),
                                                            logic.eq
                                                            bool.bool __
                                                            bool.true)
                                                         (logic.refl
                                                          bool.bool bool.true)
                                                         (p1 n) p1n)))
                                                    (λ
                                                       (
                                                       p1n : sttfa.eps
                                                             (logic.eq
                                                              bool.bool
                                                              (p1 n)
                                                              bool.false)
                                                       ),
                                                       logic.eq_ind_r nat.nat
                                                       (bigop nat.nat
                                                        n
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), p1 i0)
                                                        (nat.S nat.O)
                                                        nat.times
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), f1 i0))
                                                       (λ
                                                          (
                                                          x : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                          ),
                                                          logic.eq nat.nat x
                                                          (bigop
                                                           nat.nat n2
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), p20 i0)
                                                           (nat.S nat.O)
                                                           nat.times
                                                           (λ
                                                              (
                                                              i0 : sttfa.etap
                                                                   (sttfa.p
                                                                    nat.nat)
                                                              ), f2 i0)))
                                                       (Hind p20
                                                        (nat.lt_to_le n n1
                                                         ltn)
                                                        (transitive_sub
                                                         (λ
                                                            (
                                                            x : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                            ), x)
                                                         (λ
                                                            (
                                                            x : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                            ), x)
                                                         h k n (nat.S n) n2
                                                         p1 p1 p20 f1 f1 f2
                                                         (sub_lt f1 p1
                                                          n (nat.S n)
                                                          (nat.le_n_Sn n))
                                                         sub1)
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ),
                                                           λ
                                                             (
                                                             lti : sttfa.eps
                                                                   (nat.lt i0
                                                                    n2)
                                                             ),
                                                             λ
                                                               (
                                                               p2i : 
                                                                 sttfa.eps
                                                                 (logic.eq
                                                                  bool.bool
                                                                  (p20 i0)
                                                                  bool.true)
                                                               ),
                                                               connectives.match_And_prop
                                                               (connectives.And
                                                                (nat.lt
                                                                 (k i0)
                                                                 (nat.S n))
                                                                (logic.eq
                                                                 bool.bool
                                                                 (p1 (k i0))
                                                                 bool.true))
                                                               (logic.eq
                                                                nat.nat
                                                                (h (k i0)) i0)
                                                               (connectives.And
                                                                (connectives.And
                                                                 (nat.lt
                                                                  (k i0) n)
                                                                 (logic.eq
                                                                  bool.bool
                                                                  (p1 (k i0))
                                                                  bool.true))
                                                                (logic.eq
                                                                 nat.nat
                                                                 (h (k i0))
                                                                 i0))
                                                               (λ
                                                                  (
                                                                  _clearme3 : 
                                                                    sttfa.eps
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0)
                                                                    (
                                                                    nat.S n))
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k i0))
                                                                    bool.true))
                                                                  ),
                                                                  connectives.match_And_prop
                                                                  (nat.lt
                                                                   (k i0)
                                                                   (nat.S n))
                                                                  (logic.eq
                                                                   bool.bool
                                                                   (p1 (k i0))
                                                                   bool.true)
                                                                  (sttfa.impl
                                                                   (logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k i0))
                                                                    i0)
                                                                   (connectives.And
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k i0))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k i0))
                                                                    i0)))
                                                                  (λ
                                                                    (
                                                                    ltki : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0)
                                                                    (
                                                                    nat.S n))
                                                                    ),
                                                                    λ
                                                                    (
                                                                    p1ki : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k i0))
                                                                    bool.true)
                                                                    ),
                                                                    λ
                                                                    (
                                                                    eqi : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k i0))
                                                                    i0)),
                                                                    connectives.conj
                                                                    (
                                                                    connectives.And
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k i0))
                                                                    bool.true))
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    h (k i0))
                                                                    i0)
                                                                    (
                                                                    connectives.conj
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 (k i0))
                                                                    bool.true)
                                                                    (
                                                                    connectives.match_Or_prop
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    λ
                                                                    (
                                                                    auto : 
                                                                    sttfa.eps
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)),
                                                                    auto)
                                                                    (
                                                                    λ
                                                                    (
                                                                    eqki : 
                                                                    sttfa.eps
                                                                    (
                                                                    logic.eq
                                                                    nat.nat
                                                                    (
                                                                    k i0) n)),
                                                                    connectives.falsity
                                                                    (
                                                                    nat.lt
                                                                    (
                                                                    k i0) n)
                                                                    (
                                                                    logic.absurd
                                                                    (
                                                                    logic.eq
                                                                    bool.bool
                                                                    bool.true
                                                                    bool.false)
                                                                    (
                                                                    logic.rewrite_l
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    bool.true
                                                                    __)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    bool.false
                                                                    (
                                                                    logic.rewrite_l
                                                                    bool.bool
                                                                    (
                                                                    p1 n)
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.false)
                                                                    p1n
                                                                    bool.true
                                                                    (
                                                                    logic.rewrite_l
                                                                    nat.nat
                                                                    (
                                                                    k i0)
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    bool.bool
                                                                    (
                                                                    p1 __)
                                                                    bool.true)
                                                                    p1ki n
                                                                    eqki)))
                                                                    bool.not_eq_true_false))
                                                                    (
                                                                    nat.le_to_or_lt_eq
                                                                    (
                                                                    k i0) n
                                                                    (
                                                                    nat.le_S_S_to_le
                                                                    (
                                                                    k i0) n
                                                                    ltki)))
                                                                    (
                                                                    logic.rewrite_r
                                                                    bool.bool
                                                                    bool.true
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    bool.bool)
                                                                    ),
                                                                    logic.eq
                                                                    bool.bool
                                                                    __
                                                                    bool.true)
                                                                    (
                                                                    logic.refl
                                                                    bool.bool
                                                                    bool.true)
                                                                    (
                                                                    p1 (k i0))
                                                                    p1ki))
                                                                    (
                                                                    logic.rewrite_r
                                                                    nat.nat
                                                                    i0
                                                                    (
                                                                    λ
                                                                    (
                                                                    __ : 
                                                                    sttfa.etap
                                                                    (
                                                                    sttfa.p
                                                                    nat.nat)),
                                                                    logic.eq
                                                                    nat.nat
                                                                    __ i0)
                                                                    (
                                                                    logic.refl
                                                                    nat.nat
                                                                    i0)
                                                                    (
                                                                    h (k i0))
                                                                    eqi))
                                                                  _clearme3)
                                                               (sub2 i0 lti
                                                                p2i)))
                                                       (bigop nat.nat
                                                        (nat.S n)
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), p1 i0)
                                                        (nat.S nat.O)
                                                        nat.times
                                                        (λ
                                                           (
                                                           i0 : sttfa.etap
                                                                (sttfa.p
                                                                 nat.nat)
                                                           ), f1 i0))
                                                       (bigop_Sfalse
                                                        nat.nat n p1
                                                        (nat.S nat.O)
                                                        nat.times f1
                                                        (logic.rewrite_r
                                                         bool.bool bool.false
                                                         (λ
                                                            (
                                                            __ : sttfa.etap
                                                                 (sttfa.p
                                                                  bool.bool)
                                                            ),
                                                            logic.eq
                                                            bool.bool __
                                                            bool.false)
                                                         (logic.refl
                                                          bool.bool
                                                          bool.false)
                                                         (p1 n) p1n)))
                                                    (bool.true_or_false
                                                     (p1 n)))
                                       i p2))
                                 _clearme2)
                              _clearme1)
                         _clearme0)
                    _clearme;
