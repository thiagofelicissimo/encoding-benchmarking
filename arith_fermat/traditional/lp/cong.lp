require tests.div_mod as div_mod;
require tests.logic as logic;
require tests.nat as nat;
require tests.primes as primes;
require tests.relations as relations;
require tests.sttfa as sttfa;
symbol congruent
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow nat.nat
      (sttfa.arrow nat.nat (sttfa.arrow nat.nat sttfa.bool))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            logic.eq nat.nat (div_mod.mod n p) (div_mod.mod m p);
symbol congruent_n_n
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (p : sttfa.etap (sttfa.p nat.nat)), congruent n n p)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (p : sttfa.etap (sttfa.p nat.nat)),
          logic.refl nat.nat (div_mod.mod n p);
symbol transitive_congruent
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (p : sttfa.etap (sttfa.p nat.nat)),
        relations.transitive nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           λ (m : sttfa.etap (sttfa.p nat.nat)), congruent n m p)))
  ≔ λ (p : sttfa.etap (sttfa.p nat.nat)),
        λ (x : sttfa.etap (sttfa.p nat.nat)),
          λ (y : sttfa.etap (sttfa.p nat.nat)),
            λ (z : sttfa.etap (sttfa.p nat.nat)),
              λ (auto : sttfa.eps (congruent x y p)),
                λ (auto' : sttfa.eps (congruent y z p)),
                  logic.rewrite_l nat.nat (div_mod.mod x p)
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat (div_mod.mod x p) __)
                  (logic.refl nat.nat (div_mod.mod x p)) (div_mod.mod z p)
                  (logic.rewrite_r nat.nat (div_mod.mod y p)
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat __ (div_mod.mod z p))
                   auto' (div_mod.mod x p) auto);
symbol mod_mod
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (p : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (nat.lt nat.O p)
           (logic.eq nat.nat (div_mod.mod n p)
            (div_mod.mod (div_mod.mod n p) p)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (p : sttfa.etap (sttfa.p nat.nat)),
          λ (posp : sttfa.eps (nat.lt nat.O p)),
            logic.eq_ind_r nat.nat
            (nat.plus (nat.times (div_mod.div (div_mod.mod n p) p) p)
             (div_mod.mod (div_mod.mod n p) p))
            (λ (x : sttfa.etap (sttfa.p nat.nat)),
               logic.eq nat.nat x (div_mod.mod (div_mod.mod n p) p))
            (logic.eq_ind_r nat.nat nat.O
             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                logic.eq nat.nat
                (nat.plus (nat.times x p) (div_mod.mod (div_mod.mod n p) p))
                (div_mod.mod (div_mod.mod n p) p))
             (logic.rewrite_r nat.nat (nat.times p nat.O)
              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                 logic.eq nat.nat
                 (nat.plus __ (div_mod.mod (div_mod.mod n p) p))
                 (div_mod.mod (div_mod.mod n p) p))
              (logic.rewrite_l nat.nat nat.O
               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                  logic.eq nat.nat
                  (nat.plus __ (div_mod.mod (div_mod.mod n p) p))
                  (div_mod.mod (div_mod.mod n p) p))
               (logic.rewrite_l nat.nat (div_mod.mod (div_mod.mod n p) p)
                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat __ (div_mod.mod (div_mod.mod n p) p))
                (logic.refl nat.nat (div_mod.mod (div_mod.mod n p) p))
                (nat.plus nat.O (div_mod.mod (div_mod.mod n p) p))
                (nat.plus_O_n (div_mod.mod (div_mod.mod n p) p)))
               (nat.times p nat.O) (nat.times_n_O p))
              (nat.times nat.O p) (nat.commutative_times nat.O p))
             (div_mod.div (div_mod.mod n p) p)
             (div_mod.eq_div_O (div_mod.mod n p) p
              (div_mod.lt_mod_m_m n p posp)))
            (div_mod.mod n p) (div_mod.div_mod (div_mod.mod n p) p);
symbol congruent_n_mod_n
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (p : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (nat.lt nat.O p) (congruent n (div_mod.mod n p) p))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (p : sttfa.etap (sttfa.p nat.nat)),
          λ (posp : sttfa.eps (nat.lt nat.O p)), mod_mod n p posp;
symbol eq_times_plus_to_congruent
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (r : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.lt nat.O p)
                 (sttfa.impl
                  (logic.eq nat.nat n (nat.plus (nat.times r p) m))
                  (congruent n m p)))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (r : sttfa.etap (sttfa.p nat.nat)),
              λ (posp : sttfa.eps (nat.lt nat.O p)),
                λ
                  (
                  Hn : sttfa.eps
                       (logic.eq nat.nat n (nat.plus (nat.times r p) m))
                  ),
                  div_mod.div_mod_spec_to_eq2 n p (div_mod.div n p)
                  (div_mod.mod n p) (nat.plus r (div_mod.div m p))
                  (div_mod.mod m p) (div_mod.div_mod_spec_div_mod n p posp)
                  (div_mod.div_mod_spec_intro n p
                   (nat.plus r (div_mod.div m p)) (div_mod.mod m p)
                   (div_mod.lt_mod_m_m m p posp)
                   (logic.eq_ind_r nat.nat
                    (nat.times p (nat.plus r (div_mod.div m p)))
                    (λ (x : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat n (nat.plus x (div_mod.mod m p)))
                    (logic.eq_ind_r nat.nat
                     (nat.plus (nat.times p r)
                      (nat.times p (div_mod.div m p)))
                     (λ (x : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat n (nat.plus x (div_mod.mod m p)))
                     (logic.eq_ind_r nat.nat (nat.times r p)
                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat n
                         (nat.plus
                          (nat.plus x (nat.times p (div_mod.div m p)))
                          (div_mod.mod m p)))
                      (logic.eq_ind_r nat.nat (nat.times (div_mod.div m p) p)
                       (λ (x : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat n
                          (nat.plus (nat.plus (nat.times r p) x)
                           (div_mod.mod m p)))
                       (logic.eq_ind_r nat.nat
                        (nat.plus (nat.times r p)
                         (nat.plus (nat.times (div_mod.div m p) p)
                          (div_mod.mod m p)))
                        (λ (x : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat n x)
                        (logic.rewrite_r nat.nat (nat.times p r)
                         (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat n
                            (nat.plus __
                             (nat.plus (nat.times (div_mod.div m p) p)
                              (div_mod.mod m p))))
                         (logic.rewrite_r nat.nat
                          (nat.times p (div_mod.div m p))
                          (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat n
                             (nat.plus (nat.times p r)
                              (nat.plus __ (div_mod.mod m p))))
                          (logic.rewrite_r nat.nat
                           (nat.plus (div_mod.mod m p)
                            (nat.times p (div_mod.div m p)))
                           (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat n
                              (nat.plus (nat.times p r) __))
                           (logic.rewrite_l nat.nat m
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat n
                               (nat.plus (nat.times p r) __))
                            (logic.rewrite_r nat.nat
                             (nat.plus m (nat.times p r))
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat n __)
                             (logic.rewrite_l nat.nat n
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat n __)
                              (logic.refl nat.nat n)
                              (nat.plus m (nat.times p r))
                              (logic.rewrite_l nat.nat
                               (nat.plus (nat.times p r) m)
                               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat n __)
                               (logic.rewrite_l nat.nat (nat.times r p)
                                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat n (nat.plus __ m))
                                Hn (nat.times p r)
                                (nat.commutative_times r p))
                               (nat.plus m (nat.times p r))
                               (nat.commutative_plus (nat.times p r) m)))
                             (nat.plus (nat.times p r) m)
                             (nat.commutative_plus (nat.times p r) m))
                            (nat.plus (div_mod.mod m p)
                             (nat.times p (div_mod.div m p)))
                            (logic.rewrite_l nat.nat
                             (nat.plus (nat.times p (div_mod.div m p))
                              (div_mod.mod m p))
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat m __)
                             (logic.rewrite_l nat.nat
                              (nat.times (div_mod.div m p) p)
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat m
                                 (nat.plus __ (div_mod.mod m p)))
                              (div_mod.div_mod m p)
                              (nat.times p (div_mod.div m p))
                              (nat.commutative_times (div_mod.div m p) p))
                             (nat.plus (div_mod.mod m p)
                              (nat.times p (div_mod.div m p)))
                             (nat.commutative_plus
                              (nat.times p (div_mod.div m p))
                              (div_mod.mod m p))))
                           (nat.plus (nat.times p (div_mod.div m p))
                            (div_mod.mod m p))
                           (nat.commutative_plus
                            (nat.times p (div_mod.div m p)) (div_mod.mod m p)))
                          (nat.times (div_mod.div m p) p)
                          (nat.commutative_times (div_mod.div m p) p))
                         (nat.times r p) (nat.commutative_times r p))
                        (nat.plus
                         (nat.plus (nat.times r p)
                          (nat.times (div_mod.div m p) p))
                         (div_mod.mod m p))
                        (nat.associative_plus (nat.times r p)
                         (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
                       (nat.times p (div_mod.div m p))
                       (nat.commutative_times p (div_mod.div m p)))
                      (nat.times p r) (nat.commutative_times p r))
                     (nat.times p (nat.plus r (div_mod.div m p)))
                     (nat.distributive_times_plus p r (div_mod.div m p)))
                    (nat.times (nat.plus r (div_mod.div m p)) p)
                    (nat.commutative_times (nat.plus r (div_mod.div m p)) p)));
symbol divides_to_congruent
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O p)
              (sttfa.impl (nat.le m n)
               (sttfa.impl (primes.divides p (nat.minus n m))
                (congruent n m p)))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (posp : sttfa.eps (nat.lt nat.O p)),
              λ (lemn : sttfa.eps (nat.le m n)),
                λ (_clearme : sttfa.eps (primes.divides p (nat.minus n m))),
                  primes.match_divides_prop p (nat.minus n m)
                  (congruent n m p)
                  (λ (q : sttfa.etap (sttfa.p nat.nat)),
                     λ
                       (
                       Hdiv : sttfa.eps
                              (logic.eq nat.nat (nat.minus n m)
                               (nat.times p q))
                       ),
                       eq_times_plus_to_congruent n m p q posp
                       (logic.eq_ind_r nat.nat (nat.plus m (nat.times q p))
                        (λ (x : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat n x)
                        (nat.minus_to_plus n m (nat.times q p) lemn
                         (logic.rewrite_r nat.nat (nat.times p q)
                          (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat __ (nat.times q p))
                          (logic.rewrite_r nat.nat (nat.times p q)
                           (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat (nat.times p q) __)
                           (logic.refl nat.nat (nat.times p q))
                           (nat.times q p) (nat.commutative_times q p))
                          (nat.minus n m) Hdiv))
                        (nat.plus (nat.times q p) m)
                        (nat.commutative_plus (nat.times q p) m)))
                  _clearme;
symbol congruent_to_divides
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O p)
              (sttfa.impl (congruent n m p)
               (primes.divides p (nat.minus n m)))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (posp : sttfa.eps (nat.lt nat.O p)),
              λ (Hcong : sttfa.eps (congruent n m p)),
                primes.quotient p (nat.minus n m)
                (nat.minus (div_mod.div n p) (div_mod.div m p))
                (logic.eq_ind_r nat.nat
                 (nat.times (nat.minus (div_mod.div n p) (div_mod.div m p)) p)
                 (λ (x : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat (nat.minus n m) x)
                 (logic.eq_ind_r nat.nat
                  (nat.plus (nat.times (div_mod.div n p) p) (div_mod.mod n p))
                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat (nat.minus x m)
                     (nat.times
                      (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                  (logic.eq_ind_r nat.nat
                   (nat.plus (nat.times (div_mod.div m p) p)
                    (div_mod.mod m p))
                   (λ (x : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat
                      (nat.minus
                       (nat.plus (nat.times (div_mod.div n p) p)
                        (div_mod.mod n p))
                       x)
                      (nat.times
                       (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                   (logic.rewrite_r nat.nat (nat.times p (div_mod.div n p))
                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat
                       (nat.minus (nat.plus __ (div_mod.mod n p))
                        (nat.plus (nat.times (div_mod.div m p) p)
                         (div_mod.mod m p)))
                       (nat.times
                        (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                    (logic.rewrite_r nat.nat
                     (nat.plus (div_mod.mod n p)
                      (nat.times p (div_mod.div n p)))
                     (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (nat.minus __
                         (nat.plus (nat.times (div_mod.div m p) p)
                          (div_mod.mod m p)))
                        (nat.times
                         (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                     (logic.rewrite_l nat.nat n
                      (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat
                         (nat.minus __
                          (nat.plus (nat.times (div_mod.div m p) p)
                           (div_mod.mod m p)))
                         (nat.times
                          (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                      (logic.rewrite_r nat.nat
                       (nat.times p (div_mod.div m p))
                       (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat
                          (nat.minus n (nat.plus __ (div_mod.mod m p)))
                          (nat.times
                           (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                       (logic.rewrite_l nat.nat (div_mod.mod n p)
                        (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (nat.minus n
                            (nat.plus (nat.times p (div_mod.div m p)) __))
                           (nat.times
                            (nat.minus (div_mod.div n p) (div_mod.div m p)) p))
                        (logic.rewrite_r nat.nat
                         (nat.plus (div_mod.mod n p)
                          (nat.times p (div_mod.div m p)))
                         (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat (nat.minus n __)
                            (nat.times
                             (nat.minus (div_mod.div n p) (div_mod.div m p))
                             p))
                         (logic.rewrite_l nat.nat
                          (nat.minus (nat.minus n (div_mod.mod n p))
                           (nat.times p (div_mod.div m p)))
                          (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat __
                             (nat.times
                              (nat.minus (div_mod.div n p) (div_mod.div m p))
                              p))
                          (logic.rewrite_l nat.nat
                           (nat.times p (div_mod.div n p))
                           (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat
                              (nat.minus __ (nat.times p (div_mod.div m p)))
                              (nat.times
                               (nat.minus (div_mod.div n p) (div_mod.div m p))
                               p))
                           (logic.rewrite_l nat.nat
                            (nat.times p
                             (nat.minus (div_mod.div n p) (div_mod.div m p)))
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat __
                               (nat.times
                                (nat.minus (div_mod.div n p)
                                 (div_mod.div m p))
                                p))
                            (logic.rewrite_r nat.nat
                             (nat.times p
                              (nat.minus (div_mod.div n p) (div_mod.div m p)))
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (nat.times p
                                 (nat.minus (div_mod.div n p)
                                  (div_mod.div m p)))
                                __)
                             (logic.refl nat.nat
                              (nat.times p
                               (nat.minus (div_mod.div n p) (div_mod.div m p))))
                             (nat.times
                              (nat.minus (div_mod.div n p) (div_mod.div m p))
                              p)
                             (nat.commutative_times
                              (nat.minus (div_mod.div n p) (div_mod.div m p))
                              p))
                            (nat.minus (nat.times p (div_mod.div n p))
                             (nat.times p (div_mod.div m p)))
                            (nat.distributive_times_minus p (div_mod.div n p)
                             (div_mod.div m p)))
                           (nat.minus n (div_mod.mod n p))
                           (logic.rewrite_l nat.nat
                            (nat.times (div_mod.div n p) p)
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat __
                               (nat.minus n (div_mod.mod n p)))
                            (div_mod.eq_times_div_minus_mod n p)
                            (nat.times p (div_mod.div n p))
                            (nat.commutative_times (div_mod.div n p) p)))
                          (nat.minus n
                           (nat.plus (div_mod.mod n p)
                            (nat.times p (div_mod.div m p))))
                          (nat.minus_plus n (div_mod.mod n p)
                           (nat.times p (div_mod.div m p))))
                         (nat.plus (nat.times p (div_mod.div m p))
                          (div_mod.mod n p))
                         (nat.commutative_plus
                          (nat.times p (div_mod.div m p)) (div_mod.mod n p)))
                        (div_mod.mod m p) Hcong)
                       (nat.times (div_mod.div m p) p)
                       (nat.commutative_times (div_mod.div m p) p))
                      (nat.plus (div_mod.mod n p)
                       (nat.times p (div_mod.div n p)))
                      (logic.rewrite_l nat.nat
                       (nat.plus (nat.times p (div_mod.div n p))
                        (div_mod.mod n p))
                       (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat n __)
                       (logic.rewrite_l nat.nat
                        (nat.times (div_mod.div n p) p)
                        (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat n (nat.plus __ (div_mod.mod n p)))
                        (div_mod.div_mod n p) (nat.times p (div_mod.div n p))
                        (nat.commutative_times (div_mod.div n p) p))
                       (nat.plus (div_mod.mod n p)
                        (nat.times p (div_mod.div n p)))
                       (nat.commutative_plus (nat.times p (div_mod.div n p))
                        (div_mod.mod n p))))
                     (nat.plus (nat.times p (div_mod.div n p))
                      (div_mod.mod n p))
                     (nat.commutative_plus (nat.times p (div_mod.div n p))
                      (div_mod.mod n p)))
                    (nat.times (div_mod.div n p) p)
                    (nat.commutative_times (div_mod.div n p) p))
                   m (div_mod.div_mod m p))
                  n (div_mod.div_mod n p))
                 (nat.times p (nat.minus (div_mod.div n p) (div_mod.div m p)))
                 (nat.commutative_times p
                  (nat.minus (div_mod.div n p) (div_mod.div m p))));
symbol let_clause_1034
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O p)
              (sttfa.forall nat.nat
               (λ (x2515 : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.forall nat.nat
                  (λ (x2516 : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat x2515
                     (nat.plus (div_mod.mod x2515 x2516)
                      (nat.times x2516 (div_mod.div x2515 x2516))))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (posp : sttfa.eps (nat.lt nat.O p)),
              λ (x2515 : sttfa.etap (sttfa.p nat.nat)),
                λ (x2516 : sttfa.etap (sttfa.p nat.nat)),
                  logic.rewrite_l nat.nat
                  (nat.plus (nat.times x2516 (div_mod.div x2515 x2516))
                   (div_mod.mod x2515 x2516))
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat x2515 __)
                  (logic.rewrite_l nat.nat
                   (nat.times (div_mod.div x2515 x2516) x2516)
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat x2515
                      (nat.plus __ (div_mod.mod x2515 x2516)))
                   (div_mod.div_mod x2515 x2516)
                   (nat.times x2516 (div_mod.div x2515 x2516))
                   (nat.commutative_times (div_mod.div x2515 x2516) x2516))
                  (nat.plus (div_mod.mod x2515 x2516)
                   (nat.times x2516 (div_mod.div x2515 x2516)))
                  (nat.commutative_plus
                   (nat.times x2516 (div_mod.div x2515 x2516))
                   (div_mod.mod x2515 x2516));
symbol let_clause_73
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O p)
              (sttfa.forall nat.nat
               (λ (x134 : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.forall nat.nat
                  (λ (x135 : sttfa.etap (sttfa.p nat.nat)),
                     sttfa.forall nat.nat
                     (λ (x136 : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat (nat.plus x134 (nat.plus x135 x136))
                        (nat.plus x135 (nat.plus x134 x136))))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (posp : sttfa.eps (nat.lt nat.O p)),
              λ (x134 : sttfa.etap (sttfa.p nat.nat)),
                λ (x135 : sttfa.etap (sttfa.p nat.nat)),
                  λ (x136 : sttfa.etap (sttfa.p nat.nat)),
                    logic.rewrite_l nat.nat
                    (nat.plus (nat.plus x135 x134) x136)
                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat (nat.plus x134 (nat.plus x135 x136))
                       __)
                    (nat.assoc_plus1 x136 x135 x134)
                    (nat.plus x135 (nat.plus x134 x136))
                    (nat.associative_plus x135 x134 x136);
symbol mod_times
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (p : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.lt nat.O p)
              (logic.eq nat.nat (div_mod.mod (nat.times n m) p)
               (div_mod.mod (nat.times (div_mod.mod n p) (div_mod.mod m p)) p))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (p : sttfa.etap (sttfa.p nat.nat)),
            λ (posp : sttfa.eps (nat.lt nat.O p)),
              eq_times_plus_to_congruent (nat.times n m)
              (nat.times (div_mod.mod n p) (div_mod.mod m p)) p
              (nat.plus
               (nat.plus
                (nat.times (nat.times (div_mod.div n p) p) (div_mod.div m p))
                (nat.times (div_mod.div n p) (div_mod.mod m p)))
               (nat.times (div_mod.mod n p) (div_mod.div m p)))
              posp
              (logic.trans_eq nat.nat (nat.times n m)
               (nat.times
                (nat.plus (nat.times (div_mod.div n p) p) (div_mod.mod n p))
                (nat.plus (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
               (nat.plus
                (nat.times
                 (nat.plus
                  (nat.plus
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.div m p))
                   (nat.times (div_mod.div n p) (div_mod.mod m p)))
                  (nat.times (div_mod.mod n p) (div_mod.div m p)))
                 p)
                (nat.times (div_mod.mod n p) (div_mod.mod m p)))
               (logic.rewrite_r nat.nat (nat.times p (div_mod.div n p))
                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat (nat.times n m)
                   (nat.times (nat.plus __ (div_mod.mod n p))
                    (nat.plus (nat.times (div_mod.div m p) p)
                     (div_mod.mod m p))))
                (logic.rewrite_r nat.nat
                 (nat.plus (div_mod.mod n p) (nat.times p (div_mod.div n p)))
                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat (nat.times n m)
                    (nat.times __
                     (nat.plus (nat.times (div_mod.div m p) p)
                      (div_mod.mod m p))))
                 (logic.rewrite_l nat.nat n
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat (nat.times n m)
                     (nat.times __
                      (nat.plus (nat.times (div_mod.div m p) p)
                       (div_mod.mod m p))))
                  (logic.rewrite_r nat.nat (nat.times p (div_mod.div m p))
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat (nat.times n m)
                      (nat.times n (nat.plus __ (div_mod.mod m p))))
                   (logic.rewrite_r nat.nat
                    (nat.plus (div_mod.mod m p)
                     (nat.times p (div_mod.div m p)))
                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat (nat.times n m) (nat.times n __))
                    (logic.rewrite_l nat.nat m
                     (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat (nat.times n m) (nat.times n __))
                     (logic.refl nat.nat (nat.times n m))
                     (nat.plus (div_mod.mod m p)
                      (nat.times p (div_mod.div m p)))
                     (let_clause_1034 n m p posp m p))
                    (nat.plus (nat.times p (div_mod.div m p))
                     (div_mod.mod m p))
                    (nat.commutative_plus (nat.times p (div_mod.div m p))
                     (div_mod.mod m p)))
                   (nat.times (div_mod.div m p) p)
                   (nat.commutative_times (div_mod.div m p) p))
                  (nat.plus (div_mod.mod n p) (nat.times p (div_mod.div n p)))
                  (let_clause_1034 n m p posp n p))
                 (nat.plus (nat.times p (div_mod.div n p)) (div_mod.mod n p))
                 (nat.commutative_plus (nat.times p (div_mod.div n p))
                  (div_mod.mod n p)))
                (nat.times (div_mod.div n p) p)
                (nat.commutative_times (div_mod.div n p) p))
               (logic.trans_eq nat.nat
                (nat.times
                 (nat.plus (nat.times (div_mod.div n p) p) (div_mod.mod n p))
                 (nat.plus (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
                (nat.plus
                 (nat.plus
                  (nat.plus
                   (nat.times (nat.times (div_mod.div n p) p)
                    (nat.times (div_mod.div m p) p))
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.mod m p)))
                  (nat.times (div_mod.mod n p)
                   (nat.times (div_mod.div m p) p)))
                 (nat.times (div_mod.mod n p) (div_mod.mod m p)))
                (nat.plus
                 (nat.times
                  (nat.plus
                   (nat.plus
                    (nat.times (nat.times (div_mod.div n p) p)
                     (div_mod.div m p))
                    (nat.times (div_mod.div n p) (div_mod.mod m p)))
                   (nat.times (div_mod.mod n p) (div_mod.div m p)))
                  p)
                 (nat.times (div_mod.mod n p) (div_mod.mod m p)))
                (logic.eq_ind_r nat.nat
                 (nat.plus
                  (nat.times (nat.times (div_mod.div n p) p)
                   (nat.plus (nat.times (div_mod.div m p) p)
                    (div_mod.mod m p)))
                  (nat.times (div_mod.mod n p)
                   (nat.plus (nat.times (div_mod.div m p) p)
                    (div_mod.mod m p))))
                 (λ (x : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat x
                    (nat.plus
                     (nat.plus
                      (nat.plus
                       (nat.times (nat.times (div_mod.div n p) p)
                        (nat.times (div_mod.div m p) p))
                       (nat.times (nat.times (div_mod.div n p) p)
                        (div_mod.mod m p)))
                      (nat.times (div_mod.mod n p)
                       (nat.times (div_mod.div m p) p)))
                     (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                 (logic.eq_ind_r nat.nat
                  (nat.plus
                   (nat.times (nat.times (div_mod.div n p) p)
                    (nat.times (div_mod.div m p) p))
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.mod m p)))
                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat
                     (nat.plus x
                      (nat.times (div_mod.mod n p)
                       (nat.plus (nat.times (div_mod.div m p) p)
                        (div_mod.mod m p))))
                     (nat.plus
                      (nat.plus
                       (nat.plus
                        (nat.times (nat.times (div_mod.div n p) p)
                         (nat.times (div_mod.div m p) p))
                        (nat.times (nat.times (div_mod.div n p) p)
                         (div_mod.mod m p)))
                       (nat.times (div_mod.mod n p)
                        (nat.times (div_mod.div m p) p)))
                      (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                  (logic.eq_ind_r nat.nat
                   (nat.plus
                    (nat.times (div_mod.mod n p)
                     (nat.times (div_mod.div m p) p))
                    (nat.times (div_mod.mod n p) (div_mod.mod m p)))
                   (λ (x : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat
                      (nat.plus
                       (nat.plus
                        (nat.times (nat.times (div_mod.div n p) p)
                         (nat.times (div_mod.div m p) p))
                        (nat.times (nat.times (div_mod.div n p) p)
                         (div_mod.mod m p)))
                       x)
                      (nat.plus
                       (nat.plus
                        (nat.plus
                         (nat.times (nat.times (div_mod.div n p) p)
                          (nat.times (div_mod.div m p) p))
                         (nat.times (nat.times (div_mod.div n p) p)
                          (div_mod.mod m p)))
                        (nat.times (div_mod.mod n p)
                         (nat.times (div_mod.div m p) p)))
                       (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                   (logic.rewrite_l nat.nat
                    (nat.plus
                     (nat.plus
                      (nat.plus
                       (nat.times (nat.times (div_mod.div n p) p)
                        (nat.times (div_mod.div m p) p))
                       (nat.times (nat.times (div_mod.div n p) p)
                        (div_mod.mod m p)))
                      (nat.times (div_mod.mod n p)
                       (nat.times (div_mod.div m p) p)))
                     (nat.times (div_mod.mod n p) (div_mod.mod m p)))
                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat __
                       (nat.plus
                        (nat.plus
                         (nat.plus
                          (nat.times (nat.times (div_mod.div n p) p)
                           (nat.times (div_mod.div m p) p))
                          (nat.times (nat.times (div_mod.div n p) p)
                           (div_mod.mod m p)))
                         (nat.times (div_mod.mod n p)
                          (nat.times (div_mod.div m p) p)))
                        (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                    (logic.refl nat.nat
                     (nat.plus
                      (nat.plus
                       (nat.plus
                        (nat.times (nat.times (div_mod.div n p) p)
                         (nat.times (div_mod.div m p) p))
                        (nat.times (nat.times (div_mod.div n p) p)
                         (div_mod.mod m p)))
                       (nat.times (div_mod.mod n p)
                        (nat.times (div_mod.div m p) p)))
                      (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                    (nat.plus
                     (nat.plus
                      (nat.times (nat.times (div_mod.div n p) p)
                       (nat.times (div_mod.div m p) p))
                      (nat.times (nat.times (div_mod.div n p) p)
                       (div_mod.mod m p)))
                     (nat.plus
                      (nat.times (div_mod.mod n p)
                       (nat.times (div_mod.div m p) p))
                      (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                    (nat.associative_plus
                     (nat.plus
                      (nat.times (nat.times (div_mod.div n p) p)
                       (nat.times (div_mod.div m p) p))
                      (nat.times (nat.times (div_mod.div n p) p)
                       (div_mod.mod m p)))
                     (nat.times (div_mod.mod n p)
                      (nat.times (div_mod.div m p) p))
                     (nat.times (div_mod.mod n p) (div_mod.mod m p))))
                   (nat.times (div_mod.mod n p)
                    (nat.plus (nat.times (div_mod.div m p) p)
                     (div_mod.mod m p)))
                   (nat.distributive_times_plus (div_mod.mod n p)
                    (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
                  (nat.times (nat.times (div_mod.div n p) p)
                   (nat.plus (nat.times (div_mod.div m p) p)
                    (div_mod.mod m p)))
                  (nat.distributive_times_plus
                   (nat.times (div_mod.div n p) p)
                   (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
                 (nat.times
                  (nat.plus (nat.times (div_mod.div n p) p) (div_mod.mod n p))
                  (nat.plus (nat.times (div_mod.div m p) p) (div_mod.mod m p)))
                 (nat.distributive_times_plus_r
                  (nat.plus (nat.times (div_mod.div m p) p) (div_mod.mod m p))
                  (nat.times (div_mod.div n p) p) (div_mod.mod n p)))
                (logic.eq_f2 nat.nat nat.nat nat.nat nat.plus
                 (nat.plus
                  (nat.plus
                   (nat.times (nat.times (div_mod.div n p) p)
                    (nat.times (div_mod.div m p) p))
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.mod m p)))
                  (nat.times (div_mod.mod n p)
                   (nat.times (div_mod.div m p) p)))
                 (nat.times
                  (nat.plus
                   (nat.plus
                    (nat.times (nat.times (div_mod.div n p) p)
                     (div_mod.div m p))
                    (nat.times (div_mod.div n p) (div_mod.mod m p)))
                   (nat.times (div_mod.mod n p) (div_mod.div m p)))
                  p)
                 (nat.times (div_mod.mod n p) (div_mod.mod m p))
                 (nat.times (div_mod.mod n p) (div_mod.mod m p))
                 (logic.eq_ind nat.nat
                  (nat.times
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.div m p))
                   p)
                  (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat
                     (nat.plus
                      (nat.plus x_1
                       (nat.times (nat.times (div_mod.div n p) p)
                        (div_mod.mod m p)))
                      (nat.times (div_mod.mod n p)
                       (nat.times (div_mod.div m p) p)))
                     (nat.times
                      (nat.plus
                       (nat.plus
                        (nat.times (nat.times (div_mod.div n p) p)
                         (div_mod.div m p))
                        (nat.times (div_mod.div n p) (div_mod.mod m p)))
                       (nat.times (div_mod.mod n p) (div_mod.div m p)))
                      p))
                  (logic.eq_ind_r nat.nat
                   (nat.times (div_mod.div n p)
                    (nat.times p (div_mod.mod m p)))
                   (λ (x : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat
                      (nat.plus
                       (nat.plus
                        (nat.times
                         (nat.times (nat.times (div_mod.div n p) p)
                          (div_mod.div m p))
                         p)
                        x)
                       (nat.times (div_mod.mod n p)
                        (nat.times (div_mod.div m p) p)))
                      (nat.times
                       (nat.plus
                        (nat.plus
                         (nat.times (nat.times (div_mod.div n p) p)
                          (div_mod.div m p))
                         (nat.times (div_mod.div n p) (div_mod.mod m p)))
                        (nat.times (div_mod.mod n p) (div_mod.div m p)))
                       p))
                   (logic.eq_ind_r nat.nat (nat.times (div_mod.mod m p) p)
                    (λ (x : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat
                       (nat.plus
                        (nat.plus
                         (nat.times
                          (nat.times (nat.times (div_mod.div n p) p)
                           (div_mod.div m p))
                          p)
                         (nat.times (div_mod.div n p) x))
                        (nat.times (div_mod.mod n p)
                         (nat.times (div_mod.div m p) p)))
                       (nat.times
                        (nat.plus
                         (nat.plus
                          (nat.times (nat.times (div_mod.div n p) p)
                           (div_mod.div m p))
                          (nat.times (div_mod.div n p) (div_mod.mod m p)))
                         (nat.times (div_mod.mod n p) (div_mod.div m p)))
                        p))
                    (logic.eq_ind nat.nat
                     (nat.times
                      (nat.times (div_mod.div n p) (div_mod.mod m p)) p)
                     (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (nat.plus
                         (nat.plus
                          (nat.times
                           (nat.times (nat.times (div_mod.div n p) p)
                            (div_mod.div m p))
                           p)
                          x_1)
                         (nat.times (div_mod.mod n p)
                          (nat.times (div_mod.div m p) p)))
                        (nat.times
                         (nat.plus
                          (nat.plus
                           (nat.times (nat.times (div_mod.div n p) p)
                            (div_mod.div m p))
                           (nat.times (div_mod.div n p) (div_mod.mod m p)))
                          (nat.times (div_mod.mod n p) (div_mod.div m p)))
                         p))
                     (logic.eq_ind_r nat.nat
                      (nat.plus
                       (nat.times
                        (nat.plus
                         (nat.times (nat.times (div_mod.div n p) p)
                          (div_mod.div m p))
                         (nat.times (div_mod.div n p) (div_mod.mod m p)))
                        p)
                       (nat.times
                        (nat.times (div_mod.mod n p) (div_mod.div m p)) p))
                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat
                         (nat.plus
                          (nat.plus
                           (nat.times
                            (nat.times (nat.times (div_mod.div n p) p)
                             (div_mod.div m p))
                            p)
                           (nat.times
                            (nat.times (div_mod.div n p) (div_mod.mod m p)) p))
                          (nat.times (div_mod.mod n p)
                           (nat.times (div_mod.div m p) p)))
                         x)
                      (logic.rewrite_r nat.nat
                       (nat.times p (div_mod.div n p))
                       (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat
                          (nat.plus
                           (nat.plus
                            (nat.times (nat.times __ (div_mod.div m p)) p)
                            (nat.times
                             (nat.times (div_mod.div n p) (div_mod.mod m p))
                             p))
                           (nat.times (div_mod.mod n p)
                            (nat.times (div_mod.div m p) p)))
                          (nat.plus
                           (nat.times
                            (nat.plus
                             (nat.times (nat.times (div_mod.div n p) p)
                              (div_mod.div m p))
                             (nat.times (div_mod.div n p) (div_mod.mod m p)))
                            p)
                           (nat.times
                            (nat.times (div_mod.mod n p) (div_mod.div m p)) p)))
                       (logic.rewrite_r nat.nat
                        (nat.times (div_mod.div m p)
                         (nat.times p (div_mod.div n p)))
                        (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (nat.plus
                            (nat.plus (nat.times __ p)
                             (nat.times
                              (nat.times (div_mod.div n p) (div_mod.mod m p))
                              p))
                            (nat.times (div_mod.mod n p)
                             (nat.times (div_mod.div m p) p)))
                           (nat.plus
                            (nat.times
                             (nat.plus
                              (nat.times (nat.times (div_mod.div n p) p)
                               (div_mod.div m p))
                              (nat.times (div_mod.div n p) (div_mod.mod m p)))
                             p)
                            (nat.times
                             (nat.times (div_mod.mod n p) (div_mod.div m p))
                             p)))
                        (logic.rewrite_r nat.nat
                         (nat.times p
                          (nat.times (div_mod.div m p) (div_mod.div n p)))
                         (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat
                            (nat.plus
                             (nat.plus (nat.times __ p)
                              (nat.times
                               (nat.times (div_mod.div n p) (div_mod.mod m p))
                               p))
                             (nat.times (div_mod.mod n p)
                              (nat.times (div_mod.div m p) p)))
                            (nat.plus
                             (nat.times
                              (nat.plus
                               (nat.times (nat.times (div_mod.div n p) p)
                                (div_mod.div m p))
                               (nat.times (div_mod.div n p) (div_mod.mod m p)))
                              p)
                             (nat.times
                              (nat.times (div_mod.mod n p) (div_mod.div m p))
                              p)))
                         (logic.rewrite_r nat.nat
                          (nat.times (div_mod.div n p) (div_mod.div m p))
                          (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat
                             (nat.plus
                              (nat.plus (nat.times (nat.times p __) p)
                               (nat.times
                                (nat.times (div_mod.div n p)
                                 (div_mod.mod m p))
                                p))
                              (nat.times (div_mod.mod n p)
                               (nat.times (div_mod.div m p) p)))
                             (nat.plus
                              (nat.times
                               (nat.plus
                                (nat.times (nat.times (div_mod.div n p) p)
                                 (div_mod.div m p))
                                (nat.times (div_mod.div n p)
                                 (div_mod.mod m p)))
                               p)
                              (nat.times
                               (nat.times (div_mod.mod n p) (div_mod.div m p))
                               p)))
                          (logic.rewrite_r nat.nat
                           (nat.times p
                            (nat.times p
                             (nat.times (div_mod.div n p) (div_mod.div m p))))
                           (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat
                              (nat.plus
                               (nat.plus __
                                (nat.times
                                 (nat.times (div_mod.div n p)
                                  (div_mod.mod m p))
                                 p))
                               (nat.times (div_mod.mod n p)
                                (nat.times (div_mod.div m p) p)))
                              (nat.plus
                               (nat.times
                                (nat.plus
                                 (nat.times (nat.times (div_mod.div n p) p)
                                  (div_mod.div m p))
                                 (nat.times (div_mod.div n p)
                                  (div_mod.mod m p)))
                                p)
                               (nat.times
                                (nat.times (div_mod.mod n p)
                                 (div_mod.div m p))
                                p)))
                           (logic.rewrite_r nat.nat
                            (nat.times p
                             (nat.times (div_mod.div n p) (div_mod.mod m p)))
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat
                               (nat.plus
                                (nat.plus
                                 (nat.times p
                                  (nat.times p
                                   (nat.times (div_mod.div n p)
                                    (div_mod.div m p))))
                                 __)
                                (nat.times (div_mod.mod n p)
                                 (nat.times (div_mod.div m p) p)))
                               (nat.plus
                                (nat.times
                                 (nat.plus
                                  (nat.times (nat.times (div_mod.div n p) p)
                                   (div_mod.div m p))
                                  (nat.times (div_mod.div n p)
                                   (div_mod.mod m p)))
                                 p)
                                (nat.times
                                 (nat.times (div_mod.mod n p)
                                  (div_mod.div m p))
                                 p)))
                            (logic.rewrite_l nat.nat
                             (nat.times p
                              (nat.plus
                               (nat.times p
                                (nat.times (div_mod.div n p)
                                 (div_mod.div m p)))
                               (nat.times (div_mod.div n p) (div_mod.mod m p))))
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (nat.plus __
                                 (nat.times (div_mod.mod n p)
                                  (nat.times (div_mod.div m p) p)))
                                (nat.plus
                                 (nat.times
                                  (nat.plus
                                   (nat.times (nat.times (div_mod.div n p) p)
                                    (div_mod.div m p))
                                   (nat.times (div_mod.div n p)
                                    (div_mod.mod m p)))
                                  p)
                                 (nat.times
                                  (nat.times (div_mod.mod n p)
                                   (div_mod.div m p))
                                  p)))
                             (logic.rewrite_r nat.nat
                              (nat.times p (div_mod.div m p))
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (nat.plus
                                  (nat.times p
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p))))
                                  (nat.times (div_mod.mod n p) __))
                                 (nat.plus
                                  (nat.times
                                   (nat.plus
                                    (nat.times
                                     (nat.times (div_mod.div n p) p)
                                     (div_mod.div m p))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p)))
                                   p)
                                  (nat.times
                                   (nat.times (div_mod.mod n p)
                                    (div_mod.div m p))
                                   p)))
                              (logic.rewrite_r nat.nat
                               (nat.times p
                                (nat.times (div_mod.mod n p)
                                 (div_mod.div m p)))
                               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat
                                  (nat.plus
                                   (nat.times p
                                    (nat.plus
                                     (nat.times p
                                      (nat.times (div_mod.div n p)
                                       (div_mod.div m p)))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p))))
                                   __)
                                  (nat.plus
                                   (nat.times
                                    (nat.plus
                                     (nat.times
                                      (nat.times (div_mod.div n p) p)
                                      (div_mod.div m p))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p)))
                                    p)
                                   (nat.times
                                    (nat.times (div_mod.mod n p)
                                     (div_mod.div m p))
                                    p)))
                               (logic.rewrite_r nat.nat
                                (nat.times (div_mod.div m p)
                                 (div_mod.mod n p))
                                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat
                                   (nat.plus
                                    (nat.times p
                                     (nat.plus
                                      (nat.times p
                                       (nat.times (div_mod.div n p)
                                        (div_mod.div m p)))
                                      (nat.times (div_mod.div n p)
                                       (div_mod.mod m p))))
                                    (nat.times p __))
                                   (nat.plus
                                    (nat.times
                                     (nat.plus
                                      (nat.times
                                       (nat.times (div_mod.div n p) p)
                                       (div_mod.div m p))
                                      (nat.times (div_mod.div n p)
                                       (div_mod.mod m p)))
                                     p)
                                    (nat.times
                                     (nat.times (div_mod.mod n p)
                                      (div_mod.div m p))
                                     p)))
                                (logic.rewrite_r nat.nat
                                 (nat.plus
                                  (nat.times p
                                   (nat.times (div_mod.div m p)
                                    (div_mod.mod n p)))
                                  (nat.times p
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p)))))
                                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat __
                                    (nat.plus
                                     (nat.times
                                      (nat.plus
                                       (nat.times
                                        (nat.times (div_mod.div n p) p)
                                        (div_mod.div m p))
                                       (nat.times (div_mod.div n p)
                                        (div_mod.mod m p)))
                                      p)
                                     (nat.times
                                      (nat.times (div_mod.mod n p)
                                       (div_mod.div m p))
                                      p)))
                                 (logic.rewrite_l nat.nat
                                  (nat.times p
                                   (nat.plus
                                    (nat.times (div_mod.div m p)
                                     (div_mod.mod n p))
                                    (nat.plus
                                     (nat.times p
                                      (nat.times (div_mod.div n p)
                                       (div_mod.div m p)))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p)))))
                                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                     logic.eq nat.nat __
                                     (nat.plus
                                      (nat.times
                                       (nat.plus
                                        (nat.times
                                         (nat.times (div_mod.div n p) p)
                                         (div_mod.div m p))
                                        (nat.times (div_mod.div n p)
                                         (div_mod.mod m p)))
                                       p)
                                      (nat.times
                                       (nat.times (div_mod.mod n p)
                                        (div_mod.div m p))
                                       p)))
                                  (logic.rewrite_r nat.nat
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.plus
                                     (nat.times (div_mod.div m p)
                                      (div_mod.mod n p))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p))))
                                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                      logic.eq nat.nat (nat.times p __)
                                      (nat.plus
                                       (nat.times
                                        (nat.plus
                                         (nat.times
                                          (nat.times (div_mod.div n p) p)
                                          (div_mod.div m p))
                                         (nat.times (div_mod.div n p)
                                          (div_mod.mod m p)))
                                        p)
                                       (nat.times
                                        (nat.times (div_mod.mod n p)
                                         (div_mod.div m p))
                                        p)))
                                   (logic.rewrite_r nat.nat
                                    (nat.plus
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p))
                                     (nat.times (div_mod.div m p)
                                      (div_mod.mod n p)))
                                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                       logic.eq nat.nat
                                       (nat.times p
                                        (nat.plus
                                         (nat.times p
                                          (nat.times (div_mod.div n p)
                                           (div_mod.div m p)))
                                         __))
                                       (nat.plus
                                        (nat.times
                                         (nat.plus
                                          (nat.times
                                           (nat.times (div_mod.div n p) p)
                                           (div_mod.div m p))
                                          (nat.times (div_mod.div n p)
                                           (div_mod.mod m p)))
                                         p)
                                        (nat.times
                                         (nat.times (div_mod.mod n p)
                                          (div_mod.div m p))
                                         p)))
                                    (logic.rewrite_r nat.nat
                                     (nat.times p (div_mod.div n p))
                                     (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                        logic.eq nat.nat
                                        (nat.times p
                                         (nat.plus
                                          (nat.times p
                                           (nat.times (div_mod.div n p)
                                            (div_mod.div m p)))
                                          (nat.plus
                                           (nat.times (div_mod.div n p)
                                            (div_mod.mod m p))
                                           (nat.times (div_mod.div m p)
                                            (div_mod.mod n p)))))
                                        (nat.plus
                                         (nat.times
                                          (nat.plus
                                           (nat.times __ (div_mod.div m p))
                                           (nat.times (div_mod.div n p)
                                            (div_mod.mod m p)))
                                          p)
                                         (nat.times
                                          (nat.times (div_mod.mod n p)
                                           (div_mod.div m p))
                                          p)))
                                     (logic.rewrite_r nat.nat
                                      (nat.times (div_mod.div m p)
                                       (nat.times p (div_mod.div n p)))
                                      (λ
                                         (__ : sttfa.etap (sttfa.p nat.nat)),
                                         logic.eq nat.nat
                                         (nat.times p
                                          (nat.plus
                                           (nat.times p
                                            (nat.times (div_mod.div n p)
                                             (div_mod.div m p)))
                                           (nat.plus
                                            (nat.times (div_mod.div n p)
                                             (div_mod.mod m p))
                                            (nat.times (div_mod.div m p)
                                             (div_mod.mod n p)))))
                                         (nat.plus
                                          (nat.times
                                           (nat.plus __
                                            (nat.times (div_mod.div n p)
                                             (div_mod.mod m p)))
                                           p)
                                          (nat.times
                                           (nat.times (div_mod.mod n p)
                                            (div_mod.div m p))
                                           p)))
                                      (logic.rewrite_r nat.nat
                                       (nat.times p
                                        (nat.times (div_mod.div m p)
                                         (div_mod.div n p)))
                                       (λ
                                          (__ : sttfa.etap (sttfa.p nat.nat)),
                                          logic.eq nat.nat
                                          (nat.times p
                                           (nat.plus
                                            (nat.times p
                                             (nat.times (div_mod.div n p)
                                              (div_mod.div m p)))
                                            (nat.plus
                                             (nat.times (div_mod.div n p)
                                              (div_mod.mod m p))
                                             (nat.times (div_mod.div m p)
                                              (div_mod.mod n p)))))
                                          (nat.plus
                                           (nat.times
                                            (nat.plus __
                                             (nat.times (div_mod.div n p)
                                              (div_mod.mod m p)))
                                            p)
                                           (nat.times
                                            (nat.times (div_mod.mod n p)
                                             (div_mod.div m p))
                                            p)))
                                       (logic.rewrite_r nat.nat
                                        (nat.times (div_mod.div n p)
                                         (div_mod.div m p))
                                        (λ
                                           (__ : sttfa.etap (sttfa.p nat.nat)
                                           ),
                                           logic.eq nat.nat
                                           (nat.times p
                                            (nat.plus
                                             (nat.times p
                                              (nat.times (div_mod.div n p)
                                               (div_mod.div m p)))
                                             (nat.plus
                                              (nat.times (div_mod.div n p)
                                               (div_mod.mod m p))
                                              (nat.times (div_mod.div m p)
                                               (div_mod.mod n p)))))
                                           (nat.plus
                                            (nat.times
                                             (nat.plus (nat.times p __)
                                              (nat.times (div_mod.div n p)
                                               (div_mod.mod m p)))
                                             p)
                                            (nat.times
                                             (nat.times (div_mod.mod n p)
                                              (div_mod.div m p))
                                             p)))
                                        (logic.rewrite_r nat.nat
                                         (nat.times p
                                          (nat.plus
                                           (nat.times p
                                            (nat.times (div_mod.div n p)
                                             (div_mod.div m p)))
                                           (nat.times (div_mod.div n p)
                                            (div_mod.mod m p))))
                                         (λ
                                            (
                                            __ : sttfa.etap (sttfa.p nat.nat)
                                            ),
                                            logic.eq nat.nat
                                            (nat.times p
                                             (nat.plus
                                              (nat.times p
                                               (nat.times (div_mod.div n p)
                                                (div_mod.div m p)))
                                              (nat.plus
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p))
                                               (nat.times (div_mod.div m p)
                                                (div_mod.mod n p)))))
                                            (nat.plus __
                                             (nat.times
                                              (nat.times (div_mod.mod n p)
                                               (div_mod.div m p))
                                              p)))
                                         (logic.rewrite_r nat.nat
                                          (nat.times (div_mod.div m p)
                                           (div_mod.mod n p))
                                          (λ
                                             (
                                             __ : sttfa.etap
                                                  (sttfa.p nat.nat)
                                             ),
                                             logic.eq nat.nat
                                             (nat.times p
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.plus
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))
                                                (nat.times (div_mod.div m p)
                                                 (div_mod.mod n p)))))
                                             (nat.plus
                                              (nat.times p
                                               (nat.plus
                                                (nat.times p
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.div m p)))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))))
                                              (nat.times __ p)))
                                          (logic.rewrite_r nat.nat
                                           (nat.times p
                                            (nat.times (div_mod.div m p)
                                             (div_mod.mod n p)))
                                           (λ
                                              (
                                              __ : sttfa.etap
                                                   (sttfa.p nat.nat)
                                              ),
                                              logic.eq nat.nat
                                              (nat.times p
                                               (nat.plus
                                                (nat.times p
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.div m p)))
                                                (nat.plus
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.mod m p))
                                                 (nat.times (div_mod.div m p)
                                                  (div_mod.mod n p)))))
                                              (nat.plus
                                               (nat.times p
                                                (nat.plus
                                                 (nat.times p
                                                  (nat.times
                                                   (div_mod.div n p)
                                                   (div_mod.div m p)))
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.mod m p))))
                                               __))
                                           (logic.rewrite_r nat.nat
                                            (nat.plus
                                             (nat.times p
                                              (nat.times (div_mod.div m p)
                                               (div_mod.mod n p)))
                                             (nat.times p
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p)))))
                                            (λ
                                               (
                                               __ : sttfa.etap
                                                    (sttfa.p nat.nat)
                                               ),
                                               logic.eq nat.nat
                                               (nat.times p
                                                (nat.plus
                                                 (nat.times p
                                                  (nat.times
                                                   (div_mod.div n p)
                                                   (div_mod.div m p)))
                                                 (nat.plus
                                                  (nat.times
                                                   (div_mod.div n p)
                                                   (div_mod.mod m p))
                                                  (nat.times
                                                   (div_mod.div m p)
                                                   (div_mod.mod n p)))))
                                               __)
                                            (logic.rewrite_l nat.nat
                                             (nat.times p
                                              (nat.plus
                                               (nat.times (div_mod.div m p)
                                                (div_mod.mod n p))
                                               (nat.plus
                                                (nat.times p
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.div m p)))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p)))))
                                             (λ
                                                (
                                                __ : sttfa.etap
                                                     (sttfa.p nat.nat)
                                                ),
                                                logic.eq nat.nat
                                                (nat.times p
                                                 (nat.plus
                                                  (nat.times p
                                                   (nat.times
                                                    (div_mod.div n p)
                                                    (div_mod.div m p)))
                                                  (nat.plus
                                                   (nat.times
                                                    (div_mod.div n p)
                                                    (div_mod.mod m p))
                                                   (nat.times
                                                    (div_mod.div m p)
                                                    (div_mod.mod n p)))))
                                                __)
                                             (logic.rewrite_r nat.nat
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.plus
                                                (nat.times (div_mod.div m p)
                                                 (div_mod.mod n p))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))))
                                              (λ
                                                 (
                                                 __ : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                 ),
                                                 logic.eq nat.nat
                                                 (nat.times p
                                                  (nat.plus
                                                   (nat.times p
                                                    (nat.times
                                                     (div_mod.div n p)
                                                     (div_mod.div m p)))
                                                   (nat.plus
                                                    (nat.times
                                                     (div_mod.div n p)
                                                     (div_mod.mod m p))
                                                    (nat.times
                                                     (div_mod.div m p)
                                                     (div_mod.mod n p)))))
                                                 (nat.times p __))
                                              (logic.rewrite_r nat.nat
                                               (nat.plus
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))
                                                (nat.times (div_mod.div m p)
                                                 (div_mod.mod n p)))
                                               (λ
                                                  (
                                                  __ : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                  ),
                                                  logic.eq nat.nat
                                                  (nat.times p
                                                   (nat.plus
                                                    (nat.times p
                                                     (nat.times
                                                      (div_mod.div n p)
                                                      (div_mod.div m p)))
                                                    (nat.plus
                                                     (nat.times
                                                      (div_mod.div n p)
                                                      (div_mod.mod m p))
                                                     (nat.times
                                                      (div_mod.div m p)
                                                      (div_mod.mod n p)))))
                                                  (nat.times p
                                                   (nat.plus
                                                    (nat.times p
                                                     (nat.times
                                                      (div_mod.div n p)
                                                      (div_mod.div m p)))
                                                    __)))
                                               (logic.refl nat.nat
                                                (nat.times p
                                                 (nat.plus
                                                  (nat.times p
                                                   (nat.times
                                                    (div_mod.div n p)
                                                    (div_mod.div m p)))
                                                  (nat.plus
                                                   (nat.times
                                                    (div_mod.div n p)
                                                    (div_mod.mod m p))
                                                   (nat.times
                                                    (div_mod.div m p)
                                                    (div_mod.mod n p))))))
                                               (nat.plus
                                                (nat.times (div_mod.div m p)
                                                 (div_mod.mod n p))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p)))
                                               (nat.commutative_plus
                                                (nat.times (div_mod.div m p)
                                                 (div_mod.mod n p))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))))
                                              (nat.plus
                                               (nat.times (div_mod.div m p)
                                                (div_mod.mod n p))
                                               (nat.plus
                                                (nat.times p
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.div m p)))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p))))
                                              (let_clause_73 n m p posp
                                               (nat.times (div_mod.div m p)
                                                (div_mod.mod n p))
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p))))
                                             (nat.plus
                                              (nat.times p
                                               (nat.times (div_mod.div m p)
                                                (div_mod.mod n p)))
                                              (nat.times p
                                               (nat.plus
                                                (nat.times p
                                                 (nat.times (div_mod.div n p)
                                                  (div_mod.div m p)))
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.mod m p)))))
                                             (nat.distributive_times_plus p
                                              (nat.times (div_mod.div m p)
                                               (div_mod.mod n p))
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p)))))
                                            (nat.plus
                                             (nat.times p
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p))))
                                             (nat.times p
                                              (nat.times (div_mod.div m p)
                                               (div_mod.mod n p))))
                                            (nat.commutative_plus
                                             (nat.times p
                                              (nat.plus
                                               (nat.times p
                                                (nat.times (div_mod.div n p)
                                                 (div_mod.div m p)))
                                               (nat.times (div_mod.div n p)
                                                (div_mod.mod m p))))
                                             (nat.times p
                                              (nat.times (div_mod.div m p)
                                               (div_mod.mod n p)))))
                                           (nat.times
                                            (nat.times (div_mod.div m p)
                                             (div_mod.mod n p))
                                            p)
                                           (nat.commutative_times
                                            (nat.times (div_mod.div m p)
                                             (div_mod.mod n p))
                                            p))
                                          (nat.times (div_mod.mod n p)
                                           (div_mod.div m p))
                                          (nat.commutative_times
                                           (div_mod.mod n p)
                                           (div_mod.div m p)))
                                         (nat.times
                                          (nat.plus
                                           (nat.times p
                                            (nat.times (div_mod.div n p)
                                             (div_mod.div m p)))
                                           (nat.times (div_mod.div n p)
                                            (div_mod.mod m p)))
                                          p)
                                         (nat.commutative_times
                                          (nat.plus
                                           (nat.times p
                                            (nat.times (div_mod.div n p)
                                             (div_mod.div m p)))
                                           (nat.times (div_mod.div n p)
                                            (div_mod.mod m p)))
                                          p))
                                        (nat.times (div_mod.div m p)
                                         (div_mod.div n p))
                                        (nat.commutative_times
                                         (div_mod.div m p) (div_mod.div n p)))
                                       (nat.times (div_mod.div m p)
                                        (nat.times p (div_mod.div n p)))
                                       (nat.times_times (div_mod.div m p) p
                                        (div_mod.div n p)))
                                      (nat.times
                                       (nat.times p (div_mod.div n p))
                                       (div_mod.div m p))
                                      (nat.commutative_times
                                       (nat.times p (div_mod.div n p))
                                       (div_mod.div m p)))
                                     (nat.times (div_mod.div n p) p)
                                     (nat.commutative_times (div_mod.div n p)
                                      p))
                                    (nat.plus
                                     (nat.times (div_mod.div m p)
                                      (div_mod.mod n p))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p)))
                                    (nat.commutative_plus
                                     (nat.times (div_mod.div m p)
                                      (div_mod.mod n p))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p))))
                                   (nat.plus
                                    (nat.times (div_mod.div m p)
                                     (div_mod.mod n p))
                                    (nat.plus
                                     (nat.times p
                                      (nat.times (div_mod.div n p)
                                       (div_mod.div m p)))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p))))
                                   (let_clause_73 n m p posp
                                    (nat.times (div_mod.div m p)
                                     (div_mod.mod n p))
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p))))
                                  (nat.plus
                                   (nat.times p
                                    (nat.times (div_mod.div m p)
                                     (div_mod.mod n p)))
                                   (nat.times p
                                    (nat.plus
                                     (nat.times p
                                      (nat.times (div_mod.div n p)
                                       (div_mod.div m p)))
                                     (nat.times (div_mod.div n p)
                                      (div_mod.mod m p)))))
                                  (nat.distributive_times_plus p
                                   (nat.times (div_mod.div m p)
                                    (div_mod.mod n p))
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p)))))
                                 (nat.plus
                                  (nat.times p
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p))))
                                  (nat.times p
                                   (nat.times (div_mod.div m p)
                                    (div_mod.mod n p))))
                                 (nat.commutative_plus
                                  (nat.times p
                                   (nat.plus
                                    (nat.times p
                                     (nat.times (div_mod.div n p)
                                      (div_mod.div m p)))
                                    (nat.times (div_mod.div n p)
                                     (div_mod.mod m p))))
                                  (nat.times p
                                   (nat.times (div_mod.div m p)
                                    (div_mod.mod n p)))))
                                (nat.times (div_mod.mod n p)
                                 (div_mod.div m p))
                                (nat.commutative_times (div_mod.mod n p)
                                 (div_mod.div m p)))
                               (nat.times (div_mod.mod n p)
                                (nat.times p (div_mod.div m p)))
                               (nat.times_times (div_mod.mod n p) p
                                (div_mod.div m p)))
                              (nat.times (div_mod.div m p) p)
                              (nat.commutative_times (div_mod.div m p) p))
                             (nat.plus
                              (nat.times p
                               (nat.times p
                                (nat.times (div_mod.div n p)
                                 (div_mod.div m p))))
                              (nat.times p
                               (nat.times (div_mod.div n p) (div_mod.mod m p))))
                             (nat.distributive_times_plus p
                              (nat.times p
                               (nat.times (div_mod.div n p) (div_mod.div m p)))
                              (nat.times (div_mod.div n p) (div_mod.mod m p))))
                            (nat.times
                             (nat.times (div_mod.div n p) (div_mod.mod m p))
                             p)
                            (nat.commutative_times
                             (nat.times (div_mod.div n p) (div_mod.mod m p))
                             p))
                           (nat.times
                            (nat.times p
                             (nat.times (div_mod.div n p) (div_mod.div m p)))
                            p)
                           (nat.commutative_times
                            (nat.times p
                             (nat.times (div_mod.div n p) (div_mod.div m p)))
                            p))
                          (nat.times (div_mod.div m p) (div_mod.div n p))
                          (nat.commutative_times (div_mod.div m p)
                           (div_mod.div n p)))
                         (nat.times (div_mod.div m p)
                          (nat.times p (div_mod.div n p)))
                         (nat.times_times (div_mod.div m p) p
                          (div_mod.div n p)))
                        (nat.times (nat.times p (div_mod.div n p))
                         (div_mod.div m p))
                        (nat.commutative_times
                         (nat.times p (div_mod.div n p)) (div_mod.div m p)))
                       (nat.times (div_mod.div n p) p)
                       (nat.commutative_times (div_mod.div n p) p))
                      (nat.times
                       (nat.plus
                        (nat.plus
                         (nat.times (nat.times (div_mod.div n p) p)
                          (div_mod.div m p))
                         (nat.times (div_mod.div n p) (div_mod.mod m p)))
                        (nat.times (div_mod.mod n p) (div_mod.div m p)))
                       p)
                      (nat.distributive_times_plus_r p
                       (nat.plus
                        (nat.times (nat.times (div_mod.div n p) p)
                         (div_mod.div m p))
                        (nat.times (div_mod.div n p) (div_mod.mod m p)))
                       (nat.times (div_mod.mod n p) (div_mod.div m p))))
                     (nat.times (div_mod.div n p)
                      (nat.times (div_mod.mod m p) p))
                     (nat.associative_times (div_mod.div n p)
                      (div_mod.mod m p) p))
                    (nat.times p (div_mod.mod m p))
                    (nat.commutative_times p (div_mod.mod m p)))
                   (nat.times (nat.times (div_mod.div n p) p)
                    (div_mod.mod m p))
                   (nat.associative_times (div_mod.div n p) p
                    (div_mod.mod m p)))
                  (nat.times (nat.times (div_mod.div n p) p)
                   (nat.times (div_mod.div m p) p))
                  (nat.associative_times (nat.times (div_mod.div n p) p)
                   (div_mod.div m p) p))
                 (logic.refl nat.nat
                  (nat.times (div_mod.mod n p) (div_mod.mod m p))))));
symbol congruent_times
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall nat.nat
              (λ (m1 : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.forall nat.nat
                 (λ (p : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.impl (nat.lt nat.O p)
                    (sttfa.impl (congruent n n1 p)
                     (sttfa.impl (congruent m m1 p)
                      (congruent (nat.times n m) (nat.times n1 m1) p)))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (n1 : sttfa.etap (sttfa.p nat.nat)),
            λ (m1 : sttfa.etap (sttfa.p nat.nat)),
              λ (p : sttfa.etap (sttfa.p nat.nat)),
                λ (posp : sttfa.eps (nat.lt nat.O p)),
                  λ (Hcongn : sttfa.eps (congruent n n1 p)),
                    λ (Hcongm : sttfa.eps (congruent m m1 p)),
                      logic.eq_ind_r nat.nat
                      (div_mod.mod
                       (nat.times (div_mod.mod n p) (div_mod.mod m p)) p)
                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat x (div_mod.mod (nat.times n1 m1) p))
                      (logic.eq_ind_r nat.nat (div_mod.mod n1 p)
                       (λ (x : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat
                          (div_mod.mod (nat.times x (div_mod.mod m p)) p)
                          (div_mod.mod (nat.times n1 m1) p))
                       (logic.eq_ind_r nat.nat (div_mod.mod m1 p)
                        (λ (x : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (div_mod.mod (nat.times (div_mod.mod n1 p) x) p)
                           (div_mod.mod (nat.times n1 m1) p))
                        (logic.sym_eq nat.nat
                         (div_mod.mod (nat.times n1 m1) p)
                         (div_mod.mod
                          (nat.times (div_mod.mod n1 p) (div_mod.mod m1 p)) p)
                         (mod_times n1 m1 p posp))
                        (div_mod.mod m p) Hcongm)
                       (div_mod.mod n p) Hcongn)
                      (div_mod.mod (nat.times n m) p)
                      (mod_times n m p posp);
