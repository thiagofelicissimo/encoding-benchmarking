require tests.bigops as bigops;
require tests.bool as bool;
require tests.exp as exp;
require tests.logic as logic;
require tests.nat as nat;
require tests.sttfa as sttfa;
symbol exp_pi_l
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (a : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat nat.nat)
           (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              logic.eq nat.nat
              (nat.times (exp.exp a n)
               (bigops.bigop nat.nat n
                (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                (nat.S nat.O) nat.times
                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
              (bigops.bigop nat.nat n
               (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
               (nat.S nat.O) nat.times
               (λ (i : sttfa.etap (sttfa.p nat.nat)), nat.times a (f i)))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (a : sttfa.etap (sttfa.p nat.nat)),
          λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
            nat.nat_ind
            (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
               logic.eq nat.nat
               (nat.times (exp.exp a _x_365)
                (bigops.bigop nat.nat _x_365
                 (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                 (nat.S nat.O) nat.times
                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
               (bigops.bigop nat.nat _x_365
                (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                (nat.S nat.O) nat.times
                (λ (i : sttfa.etap (sttfa.p nat.nat)), nat.times a (f i))))
            (bigops.sym_eq_bigop_O nat.nat
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
                logic.eq nat.nat
                (nat.times (exp.exp a nat.O)
                 (bigops.bigop nat.nat nat.O
                  (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                  (nat.S nat.O) nat.times
                  (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                (y (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                 (nat.S nat.O) nat.times
                 (λ (i : sttfa.etap (sttfa.p nat.nat)), nat.times a (f i))))
             (bigops.sym_eq_bigop_body_O nat.nat
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
                 logic.eq nat.nat
                 (nat.times (exp.exp a nat.O)
                  (bigops.bigop nat.nat nat.O
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                   (nat.S nat.O) nat.times
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                 (y (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                  (nat.S nat.O) nat.times
                  (λ (i : sttfa.etap (sttfa.p nat.nat)), nat.times a (f i))))
              (nat.eq_times_body_O
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                  logic.eq nat.nat
                  (nat.times (exp.exp a nat.O)
                   (bigops.bigop nat.nat nat.O
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                    (nat.S nat.O) nat.times
                    (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                  (nat.S (y (nat.S nat.O))))
               (nat.eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
                nat.times_body
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                   logic.eq nat.nat
                   (nat.times (exp.exp a nat.O)
                    (bigops.bigop nat.nat nat.O
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                     (nat.S nat.O) nat.times
                     (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                   (nat.S (y (nat.S nat.O))))
                (nat.eq_times nat.O
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                    logic.eq nat.nat
                    (nat.times (exp.exp a nat.O)
                     (bigops.bigop nat.nat nat.O
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                      (nat.S nat.O) nat.times
                      (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                    (nat.S (y (nat.S nat.O))))
                 (nat.eq_plus_body_O
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                     logic.eq nat.nat
                     (nat.times (exp.exp a nat.O)
                      (bigops.bigop nat.nat nat.O
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                     (nat.S (y (nat.times nat.O (nat.S nat.O)))))
                  (nat.eq_filter_nat_type_O (sttfa.arrow nat.nat nat.nat)
                   nat.plus_body
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                      ),
                      logic.eq nat.nat
                      (nat.times (exp.exp a nat.O)
                       (bigops.bigop nat.nat nat.O
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                        (nat.S nat.O) nat.times
                        (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                      (nat.S (y (nat.times nat.O (nat.S nat.O)))))
                   (nat.eq_plus nat.O
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))
                       ),
                       logic.eq nat.nat
                       (nat.times (exp.exp a nat.O)
                        (bigops.bigop nat.nat nat.O
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                         (nat.S nat.O) nat.times
                         (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                       (nat.S (y (nat.times nat.O (nat.S nat.O)))))
                    (nat.eq_plus_body_S nat.O
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                        ),
                        logic.eq nat.nat
                        (nat.times (exp.exp a nat.O)
                         (bigops.bigop nat.nat nat.O
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                          (nat.S nat.O) nat.times
                          (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                        (y (nat.times nat.O (nat.S nat.O))))
                     (nat.eq_filter_nat_type_S (sttfa.arrow nat.nat nat.nat)
                      nat.plus_body nat.O
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat.nat nat.nat))
                         ),
                         logic.eq nat.nat
                         (nat.times (exp.exp a nat.O)
                          (bigops.bigop nat.nat nat.O
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                           (nat.S nat.O) nat.times
                           (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                         (y (nat.times nat.O (nat.S nat.O))))
                      (nat.eq_plus (nat.S nat.O)
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat.nat nat.nat))
                          ),
                          logic.eq nat.nat
                          (nat.times (exp.exp a nat.O)
                           (bigops.bigop nat.nat nat.O
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                            (nat.S nat.O) nat.times
                            (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                          (y (nat.times nat.O (nat.S nat.O))))
                       (nat.eq_times_body_S nat.O
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat.nat nat.nat))
                           ),
                           logic.eq nat.nat
                           (nat.times (exp.exp a nat.O)
                            (bigops.bigop nat.nat nat.O
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                bool.true)
                             (nat.S nat.O) nat.times
                             (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                           (y (nat.S nat.O)))
                        (nat.eq_filter_nat_type_S
                         (sttfa.arrow nat.nat nat.nat) nat.times_body nat.O
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p (sttfa.arrow nat.nat nat.nat))
                            ),
                            logic.eq nat.nat
                            (nat.times (exp.exp a nat.O)
                             (bigops.bigop nat.nat nat.O
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 bool.true)
                              (nat.S nat.O) nat.times
                              (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                            (y (nat.S nat.O)))
                         (nat.eq_times (nat.S nat.O)
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat.nat nat.nat))
                             ),
                             logic.eq nat.nat
                             (nat.times (exp.exp a nat.O)
                              (bigops.bigop nat.nat nat.O
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  bool.true)
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                             (y (nat.S nat.O)))
                          (nat.eq_match_nat_type_O nat.nat (nat.S nat.O)
                           (λ (k : sttfa.etap (sttfa.p nat.nat)),
                              bool.match_bool_type nat.nat
                              (nat.times (nat.times a (f k))
                               (bigops.bigop nat.nat k
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   bool.true)
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   nat.times a (f i))))
                              (bigops.bigop nat.nat k
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  bool.true)
                               (nat.S nat.O) nat.times
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  nat.times a (f i)))
                              bool.true)
                           (λ (y : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat
                              (nat.times (exp.exp a nat.O)
                               (bigops.bigop nat.nat nat.O
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   bool.true)
                                (nat.S nat.O) nat.times
                                (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                              (nat.times (nat.S nat.O) y))
                           (exp.eq_exp_body_O a
                            (λ (y : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat
                               (nat.times (exp.exp a nat.O)
                                (bigops.bigop nat.nat nat.O
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    bool.true)
                                 (nat.S nat.O) nat.times
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                               (nat.times y
                                ((λ
                                    (
                                    p : sttfa.etap
                                        (sttfa.p
                                         (sttfa.arrow nat.nat bool.bool))
                                    ),
                                    λ (nil : sttfa.etap (sttfa.p nat.nat)),
                                      λ
                                        (
                                        op : sttfa.etap
                                             (sttfa.p
                                              (sttfa.arrow nat.nat
                                               (sttfa.arrow nat.nat nat.nat)))
                                        ),
                                        λ
                                          (
                                          f0 : sttfa.etap
                                               (sttfa.p
                                                (sttfa.arrow nat.nat nat.nat))
                                          ),
                                          nat.match_nat_type nat.nat nil
                                          (λ
                                             (
                                             k : sttfa.etap (sttfa.p nat.nat)
                                             ),
                                             bool.match_bool_type nat.nat
                                             (op (f0 k)
                                              (bigops.bigop nat.nat k p nil
                                               op f0))
                                             (bigops.bigop nat.nat k p nil op
                                              f0)
                                             (p k))
                                          nat.O)
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    bool.true)
                                 (nat.S nat.O) nat.times
                                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                    nat.times a (f i)))))
                            (nat.eq_filter_nat_type_O nat.nat
                             (exp.exp_body a)
                             (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (nat.times (exp.exp a nat.O)
                                 (bigops.bigop nat.nat nat.O
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     bool.true)
                                  (nat.S nat.O) nat.times
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)), f i)))
                                (nat.times y
                                 ((λ
                                     (
                                     p : sttfa.etap
                                         (sttfa.p
                                          (sttfa.arrow nat.nat bool.bool))
                                     ),
                                     λ (nil : sttfa.etap (sttfa.p nat.nat)),
                                       λ
                                         (
                                         op : sttfa.etap
                                              (sttfa.p
                                               (sttfa.arrow nat.nat
                                                (sttfa.arrow nat.nat nat.nat)))
                                         ),
                                         λ
                                           (
                                           f0 : sttfa.etap
                                                (sttfa.p
                                                 (sttfa.arrow nat.nat nat.nat))
                                           ),
                                           nat.match_nat_type nat.nat nil
                                           (λ
                                              (
                                              k : sttfa.etap
                                                  (sttfa.p nat.nat)
                                              ),
                                              bool.match_bool_type nat.nat
                                              (op (f0 k)
                                               (bigops.bigop nat.nat k p nil
                                                op f0))
                                              (bigops.bigop nat.nat k p nil
                                               op f0)
                                              (p k))
                                           nat.O)
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     bool.true)
                                  (nat.S nat.O) nat.times
                                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                     nat.times a (f i)))))
                             (exp.eq_exp a nat.O
                              (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (nat.times (exp.exp a nat.O)
                                  (bigops.bigop nat.nat nat.O
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      bool.true)
                                   (nat.S nat.O) nat.times
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      f i)))
                                 (nat.times y
                                  ((λ
                                      (
                                      p : sttfa.etap
                                          (sttfa.p
                                           (sttfa.arrow nat.nat bool.bool))
                                      ),
                                      λ
                                        (nil : sttfa.etap (sttfa.p nat.nat)),
                                        λ
                                          (
                                          op : sttfa.etap
                                               (sttfa.p
                                                (sttfa.arrow nat.nat
                                                 (sttfa.arrow nat.nat nat.nat)))
                                          ),
                                          λ
                                            (
                                            f0 : sttfa.etap
                                                 (sttfa.p
                                                  (sttfa.arrow nat.nat
                                                   nat.nat))
                                            ),
                                            nat.match_nat_type nat.nat nil
                                            (λ
                                               (
                                               k : sttfa.etap
                                                   (sttfa.p nat.nat)
                                               ),
                                               bool.match_bool_type nat.nat
                                               (op (f0 k)
                                                (bigops.bigop nat.nat k p nil
                                                 op f0))
                                               (bigops.bigop nat.nat k p nil
                                                op f0)
                                               (p k))
                                            nat.O)
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      bool.true)
                                   (nat.S nat.O) nat.times
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      nat.times a (f i)))))
                              (nat.sym_eq_match_nat_type_O nat.nat
                               (nat.S nat.O)
                               (λ (k : sttfa.etap (sttfa.p nat.nat)),
                                  bool.match_bool_type nat.nat
                                  (nat.times (nat.times a (f k))
                                   (bigops.bigop nat.nat k
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       bool.true)
                                    (nat.S nat.O) nat.times
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       nat.times a (f i))))
                                  (bigops.bigop nat.nat k
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      bool.true)
                                   (nat.S nat.O) nat.times
                                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                      nat.times a (f i)))
                                  bool.true)
                               (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat
                                  (nat.times (exp.exp a nat.O)
                                   (bigops.bigop nat.nat nat.O
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       bool.true)
                                    (nat.S nat.O) nat.times
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       f i)))
                                  (nat.times (exp.exp a nat.O) y))
                               (bigops.eq_bigop_body_O nat.nat
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
                                            (sttfa.arrow nat.nat nat.nat)
                                            nat.nat)))))
                                   ),
                                   logic.eq nat.nat
                                   (nat.times (exp.exp a nat.O)
                                    (bigops.bigop nat.nat nat.O
                                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                        bool.true)
                                     (nat.S nat.O) nat.times
                                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                        f i)))
                                   (nat.times (exp.exp a nat.O)
                                    (y
                                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                        bool.true)
                                     (nat.S nat.O) nat.times
                                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                        f i))))
                                (bigops.eq_bigop_O nat.nat
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
                                             (sttfa.arrow nat.nat nat.nat)
                                             nat.nat)))))
                                    ),
                                    logic.eq nat.nat
                                    (nat.times (exp.exp a nat.O)
                                     (bigops.bigop nat.nat nat.O
                                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                         bool.true)
                                      (nat.S nat.O) nat.times
                                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                         f i)))
                                    (nat.times (exp.exp a nat.O)
                                     (y
                                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                         bool.true)
                                      (nat.S nat.O) nat.times
                                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                         f i))))
                                 (logic.refl nat.nat
                                  (nat.times (exp.exp a nat.O)
                                   (bigops.bigop nat.nat nat.O
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       bool.true)
                                    (nat.S nat.O) nat.times
                                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                       f i)))))))))))))))))))))))))
            (λ (i : sttfa.etap (sttfa.p nat.nat)),
               λ
                 (
                 Hind : sttfa.eps
                        (logic.eq nat.nat
                         (nat.times (exp.exp a i)
                          (bigops.bigop nat.nat i
                           (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                           (nat.S nat.O) nat.times
                           (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                         (bigops.bigop nat.nat i
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                          (nat.S nat.O) nat.times
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                             nat.times a (f i0))))
                 ),
                 logic.eq_ind_r nat.nat
                 (nat.times (f i)
                  (bigops.bigop nat.nat i
                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                   (nat.S nat.O) nat.times
                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                 (λ (x : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat (nat.times (exp.exp a (nat.S i)) x)
                    (bigops.bigop nat.nat (nat.S i)
                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                     (nat.S nat.O) nat.times
                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                        nat.times a (f i0))))
                 (logic.eq_ind_r nat.nat
                  (nat.times (nat.times a (f i))
                   (bigops.bigop nat.nat i
                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                    (nat.S nat.O) nat.times
                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                       nat.times a (f i0))))
                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat
                     (nat.times (exp.exp a (nat.S i))
                      (nat.times (f i)
                       (bigops.bigop nat.nat i
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                        (nat.S nat.O) nat.times
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                     x)
                  (logic.eq_ind nat.nat
                   (nat.times (exp.exp a i)
                    (bigops.bigop nat.nat i
                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                     (nat.S nat.O) nat.times
                     (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                   (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                      logic.eq nat.nat
                      (nat.times (exp.exp a (nat.S i))
                       (nat.times (f i)
                        (bigops.bigop nat.nat i
                         (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                         (nat.S nat.O) nat.times
                         (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                      (nat.times (nat.times a (f i)) x_1))
                   (logic.eq_ind nat.nat
                    (nat.times (nat.times (exp.exp a (nat.S i)) (f i))
                     (bigops.bigop nat.nat i
                      (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                      (nat.S nat.O) nat.times
                      (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                    (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat x_1
                       (nat.times (nat.times a (f i))
                        (nat.times (exp.exp a i)
                         (bigops.bigop nat.nat i
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                          (nat.S nat.O) nat.times
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))))
                    (logic.eq_ind nat.nat
                     (nat.times (nat.times (nat.times a (f i)) (exp.exp a i))
                      (bigops.bigop nat.nat i
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                     (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (nat.times (nat.times (exp.exp a (nat.S i)) (f i))
                         (bigops.bigop nat.nat i
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                          (nat.S nat.O) nat.times
                          (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0)))
                        x_1)
                     (logic.eq_f2 nat.nat nat.nat nat.nat nat.times
                      (nat.times (exp.exp a (nat.S i)) (f i))
                      (nat.times (nat.times a (f i)) (exp.exp a i))
                      (bigops.bigop nat.nat i
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                      (bigops.bigop nat.nat i
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                      (exp.sym_eq_exp a (nat.S i)
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat (nat.times y (f i))
                          (nat.times (nat.times a (f i)) (exp.exp a i)))
                       (nat.sym_eq_filter_nat_type_S nat.nat (exp.exp_body a)
                        i
                        (λ (y : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat (nat.times y (f i))
                           (nat.times (nat.times a (f i)) (exp.exp a i)))
                        (exp.sym_eq_exp_body_S a i
                         (λ (y : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat (nat.times y (f i))
                            (nat.times (nat.times a (f i)) (exp.exp a i)))
                         (logic.rewrite_r nat.nat (nat.times a (exp.exp a i))
                          (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                             logic.eq nat.nat (nat.times __ (f i))
                             (nat.times (nat.times a (f i)) (exp.exp a i)))
                          (logic.rewrite_r nat.nat
                           (nat.times (f i) (nat.times a (exp.exp a i)))
                           (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat __
                              (nat.times (nat.times a (f i)) (exp.exp a i)))
                           (logic.rewrite_r nat.nat
                            (nat.times a (nat.times (f i) (exp.exp a i)))
                            (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat __
                               (nat.times (nat.times a (f i)) (exp.exp a i)))
                            (logic.rewrite_r nat.nat
                             (nat.times (exp.exp a i) (nat.times a (f i)))
                             (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (nat.times a (nat.times (f i) (exp.exp a i)))
                                __)
                             (logic.rewrite_r nat.nat
                              (nat.times a (nat.times (exp.exp a i) (f i)))
                              (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (nat.times a (nat.times (f i) (exp.exp a i)))
                                 __)
                              (logic.rewrite_r nat.nat
                               (nat.times (f i) (exp.exp a i))
                               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat
                                  (nat.times a
                                   (nat.times (f i) (exp.exp a i)))
                                  (nat.times a __))
                               (logic.refl nat.nat
                                (nat.times a (nat.times (f i) (exp.exp a i))))
                               (nat.times (exp.exp a i) (f i))
                               (nat.commutative_times (exp.exp a i) (f i)))
                              (nat.times (exp.exp a i) (nat.times a (f i)))
                              (nat.times_times (exp.exp a i) a (f i)))
                             (nat.times (nat.times a (f i)) (exp.exp a i))
                             (nat.commutative_times (nat.times a (f i))
                              (exp.exp a i)))
                            (nat.times (f i) (nat.times a (exp.exp a i)))
                            (nat.times_times (f i) a (exp.exp a i)))
                           (nat.times (nat.times a (exp.exp a i)) (f i))
                           (nat.commutative_times (nat.times a (exp.exp a i))
                            (f i)))
                          (nat.times (exp.exp a i) a)
                          (nat.commutative_times (exp.exp a i) a)))))
                      (logic.refl nat.nat
                       (bigops.bigop nat.nat i
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                        (nat.S nat.O) nat.times
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                     (nat.times (nat.times a (f i))
                      (nat.times (exp.exp a i)
                       (bigops.bigop nat.nat i
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                        (nat.S nat.O) nat.times
                        (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                     (nat.associative_times (nat.times a (f i)) (exp.exp a i)
                      (bigops.bigop nat.nat i
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                    (nat.times (exp.exp a (nat.S i))
                     (nat.times (f i)
                      (bigops.bigop nat.nat i
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                       (nat.S nat.O) nat.times
                       (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                    (nat.associative_times (exp.exp a (nat.S i)) (f i)
                     (bigops.bigop nat.nat i
                      (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                      (nat.S nat.O) nat.times
                      (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))))
                   (bigops.bigop nat.nat i
                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                    (nat.S nat.O) nat.times
                    (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                       nat.times a (f i0)))
                   Hind)
                  (bigops.bigop nat.nat (nat.S i)
                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                   (nat.S nat.O) nat.times
                   (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                      nat.times a (f i0)))
                  (bigops.bigop_Strue nat.nat i
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)), bool.true)
                   (nat.S nat.O) nat.times
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                      nat.times a (f __))
                   (logic.refl bool.bool bool.true)))
                 (bigops.bigop nat.nat (nat.S i)
                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)), bool.true)
                  (nat.S nat.O) nat.times
                  (λ (i0 : sttfa.etap (sttfa.p nat.nat)), f i0))
                 (bigops.bigop_Strue nat.nat i
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)), bool.true)
                  (nat.S nat.O) nat.times f (logic.refl bool.bool bool.true)))
            n;
symbol exp_pi_bc
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (a : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (b : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (c : sttfa.etap (sttfa.p nat.nat)),
              sttfa.forall (sttfa.arrow nat.nat nat.nat)
              (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
                 logic.eq nat.nat
                 (nat.times (exp.exp a (nat.minus c b))
                  (bigops.bigop nat.nat (nat.minus c b)
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                   (nat.S nat.O) nat.times
                   (λ (i : sttfa.etap (sttfa.p nat.nat)), f (nat.plus i b))))
                 (bigops.bigop nat.nat (nat.minus c b)
                  (λ (i : sttfa.etap (sttfa.p nat.nat)), bool.true)
                  (nat.S nat.O) nat.times
                  (λ (i : sttfa.etap (sttfa.p nat.nat)),
                     nat.times a (f (nat.plus i b)))))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat.nat)),
        λ (b : sttfa.etap (sttfa.p nat.nat)),
          λ (c : sttfa.etap (sttfa.p nat.nat)),
            λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              exp_pi_l (nat.minus c b) a
              (λ (__ : sttfa.etap (sttfa.p nat.nat)), f (nat.plus __ b));
