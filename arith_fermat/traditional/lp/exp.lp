require tests.connectives as connectives;
require tests.leibniz as leibniz;
require tests.nat as nat;
require tests.sttfa as sttfa;
constant symbol exp
  : sttfa.etap (sttfa.p (sttfa.arrow nat.nat (sttfa.arrow nat.nat nat.nat)));
constant symbol exp_body
  : sttfa.etap (sttfa.p (sttfa.arrow nat.nat (sttfa.arrow nat.nat nat.nat)));
constant symbol axiom_exp
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           connectives.equal nat.nat (exp n m)
           (nat.filter_nat_type nat.nat (exp_body n) m))));
symbol eq_exp
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz nat.nat (exp n m)
           (nat.filter_nat_type nat.nat (exp_body n) m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          connectives.equal_leibniz nat.nat (exp n m)
          (nat.filter_nat_type nat.nat (exp_body n) m) (axiom_exp n m);
symbol sym_eq_exp
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz nat.nat
           (nat.filter_nat_type nat.nat (exp_body n) m) (exp n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          leibniz.sym_leibniz nat.nat (exp n m)
          (nat.filter_nat_type nat.nat (exp_body n) m) (eq_exp n m);
constant symbol axiom_exp_body_O
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal nat.nat (exp_body n nat.O) (nat.S nat.O)));
symbol eq_exp_body_O
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat (exp_body n nat.O) (nat.S nat.O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal_leibniz nat.nat (exp_body n nat.O)
        (nat.S nat.O) (axiom_exp_body_O n);
symbol sym_eq_exp_body_O
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz nat.nat (nat.S nat.O) (exp_body n nat.O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.sym_leibniz nat.nat (exp_body n nat.O) (nat.S nat.O)
        (eq_exp_body_O n);
constant symbol axiom_exp_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           connectives.equal nat.nat (exp_body n (nat.S m))
           (nat.times (exp n m) n))));
symbol eq_exp_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz nat.nat (exp_body n (nat.S m))
           (nat.times (exp n m) n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          connectives.equal_leibniz nat.nat (exp_body n (nat.S m))
          (nat.times (exp n m) n) (axiom_exp_body_S n m);
symbol sym_eq_exp_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           leibniz.leibniz nat.nat (nat.times (exp n m) n)
           (exp_body n (nat.S m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          leibniz.sym_leibniz nat.nat (exp_body n (nat.S m))
          (nat.times (exp n m) n) (eq_exp_body_S n m);
symbol lt_O_exp
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (nat.lt nat.O n) (nat.lt nat.O (exp n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          nat.nat_ind
          (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
             sttfa.impl (nat.lt nat.O n) (nat.lt nat.O (exp n _x_365)))
          (sym_eq_exp n nat.O
           (λ (y : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y))
           (nat.sym_eq_filter_nat_type_O nat.nat (exp_body n)
            (λ (y : sttfa.etap (sttfa.p nat.nat)),
               sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y))
            (sym_eq_exp_body_O n
             (λ (y : sttfa.etap (sttfa.p nat.nat)),
                sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y))
             (λ (auto : sttfa.eps (nat.le (nat.S nat.O) n)),
                nat.lt_O_S nat.O))))
          (λ (a : sttfa.etap (sttfa.p nat.nat)),
             sym_eq_exp n (nat.S a)
             (λ (y : sttfa.etap (sttfa.p nat.nat)),
                sttfa.impl
                (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O (exp n a)))
                (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y)))
             (nat.sym_eq_filter_nat_type_S nat.nat (exp_body n) a
              (λ (y : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl
                 (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O (exp n a)))
                 (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y)))
              (sym_eq_exp_body_S n a
               (λ (y : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.impl
                  (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O (exp n a)))
                  (sttfa.impl (nat.lt nat.O n) (nat.lt nat.O y)))
               (λ
                  (
                  Hind : sttfa.eps
                         (sttfa.impl (nat.le (nat.S nat.O) n)
                          (nat.le (nat.S nat.O) (exp n a)))
                  ),
                  λ (posn : sttfa.eps (nat.le (nat.S nat.O) n)),
                    nat.eq_times_body_O
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       nat.le (nat.S (y (nat.S nat.O)))
                       (nat.times (exp n a) n))
                    (nat.eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
                     nat.times_body
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                        ),
                        nat.le (nat.S (y (nat.S nat.O)))
                        (nat.times (exp n a) n))
                     (nat.eq_times nat.O
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat.nat nat.nat))
                         ),
                         nat.le (nat.S (y (nat.S nat.O)))
                         (nat.times (exp n a) n))
                      (nat.eq_plus_body_O
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          nat.le (nat.S (y (nat.times nat.O (nat.S nat.O))))
                          (nat.times (exp n a) n))
                       (nat.eq_filter_nat_type_O
                        (sttfa.arrow nat.nat nat.nat) nat.plus_body
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat nat.nat))
                           ),
                           nat.le (nat.S (y (nat.times nat.O (nat.S nat.O))))
                           (nat.times (exp n a) n))
                        (nat.eq_plus nat.O
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p (sttfa.arrow nat.nat nat.nat))
                            ),
                            nat.le
                            (nat.S (y (nat.times nat.O (nat.S nat.O))))
                            (nat.times (exp n a) n))
                         (nat.eq_plus_body_S nat.O
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat.nat nat.nat))
                             ),
                             nat.le (y (nat.times nat.O (nat.S nat.O)))
                             (nat.times (exp n a) n))
                          (nat.eq_filter_nat_type_S
                           (sttfa.arrow nat.nat nat.nat) nat.plus_body nat.O
                           (λ
                              (
                              y : sttfa.etap
                                  (sttfa.p (sttfa.arrow nat.nat nat.nat))
                              ),
                              nat.le (y (nat.times nat.O (nat.S nat.O)))
                              (nat.times (exp n a) n))
                           (nat.eq_plus (nat.S nat.O)
                            (λ
                               (
                               y : sttfa.etap
                                   (sttfa.p (sttfa.arrow nat.nat nat.nat))
                               ),
                               nat.le (y (nat.times nat.O (nat.S nat.O)))
                               (nat.times (exp n a) n))
                            (nat.eq_times_body_S nat.O
                             (λ
                                (
                                y : sttfa.etap
                                    (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                ),
                                nat.le (y (nat.S nat.O))
                                (nat.times (exp n a) n))
                             (nat.eq_filter_nat_type_S
                              (sttfa.arrow nat.nat nat.nat) nat.times_body
                              nat.O
                              (λ
                                 (
                                 y : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                 ),
                                 nat.le (y (nat.S nat.O))
                                 (nat.times (exp n a) n))
                              (nat.eq_times (nat.S nat.O)
                               (λ
                                  (
                                  y : sttfa.etap
                                      (sttfa.p (sttfa.arrow nat.nat nat.nat))
                                  ),
                                  nat.le (y (nat.S nat.O))
                                  (nat.times (exp n a) n))
                               (nat.le_times (nat.S nat.O) (exp n a)
                                (nat.S nat.O) n (Hind posn) posn))))))))))))))))
          m;
