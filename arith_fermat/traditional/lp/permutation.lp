require tests.sttfa as sttfa;
require tests.connectives as connectives;
require tests.relations as relations;
require tests.bool as bool;
require tests.leibniz as leibniz;
require tests.logic as logic;
require tests.nat as nat;
symbol injn
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
      (sttfa.arrow nat.nat sttfa.bool)))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          sttfa.forall nat.nat
          (λ (i : sttfa.etap (sttfa.p nat.nat)),
             sttfa.forall nat.nat
             (λ (j : sttfa.etap (sttfa.p nat.nat)),
                sttfa.impl (nat.le i n)
                (sttfa.impl (nat.le j n)
                 (sttfa.impl (logic.eq nat.nat (f i) (f j))
                  (logic.eq nat.nat i j)))));
symbol injn_Sn_n
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (injn f (nat.S n)) (injn f n))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (H : sttfa.eps (injn f (nat.S n))),
            λ (i : sttfa.etap (sttfa.p nat.nat)),
              λ (j : sttfa.etap (sttfa.p nat.nat)),
                λ (lei : sttfa.eps (nat.le i n)),
                  λ (lej : sttfa.eps (nat.le j n)),
                    λ (eqf : sttfa.eps (logic.eq nat.nat (f i) (f j))),
                      H i j (nat.le_S i n lei) (nat.le_S j n lej)
                      (logic.rewrite_l nat.nat (f i)
                       (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat (f i) __)
                       (logic.refl nat.nat (f i)) (f j) eqf);
symbol permut
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
      (sttfa.arrow nat.nat sttfa.bool)))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          connectives.And
          (sttfa.forall nat.nat
           (λ (i : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.le i m) (nat.le (f i) m)))
          (injn f m);
symbol transpose
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow nat.nat (sttfa.arrow nat.nat (sttfa.arrow nat.nat nat.nat))))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            bool.match_bool_type nat.nat j
            (bool.match_bool_type nat.nat i n (nat.eqb n j)) (nat.eqb n i);
symbol transpose_i_j_i
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (i : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (j : sttfa.etap (sttfa.p nat.nat)),
           logic.eq nat.nat (transpose i j i) j)))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          logic.eq_ind_r bool.bool bool.true
          (λ (x : sttfa.etap (sttfa.p bool.bool)),
             logic.eq nat.nat
             (bool.match_bool_type nat.nat j
              (bool.match_bool_type nat.nat i i (nat.eqb i j)) x)
             j)
          (bool.eq_match_bool_type_true nat.nat j
           (bool.match_bool_type nat.nat i i (nat.eqb i j))
           (λ (y : sttfa.etap (sttfa.p nat.nat)),
              logic.eq nat.nat
              (bool.match_bool_type nat.nat j
               (bool.match_bool_type nat.nat i i (nat.eqb i j)) bool.true)
              y)
           (logic.refl nat.nat
            (bool.match_bool_type nat.nat j
             (bool.match_bool_type nat.nat i i (nat.eqb i j)) bool.true)))
          (nat.eqb i i) (nat.eqb_n_n i);
symbol transpose_i_j_j
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (i : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (j : sttfa.etap (sttfa.p nat.nat)),
           logic.eq nat.nat (transpose i j j) i)))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          connectives.match_Or_prop
          (logic.eq bool.bool (nat.eqb j i) bool.true)
          (logic.eq bool.bool (nat.eqb j i) bool.false)
          (logic.eq nat.nat
           (bool.match_bool_type nat.nat j
            (bool.match_bool_type nat.nat i j (nat.eqb j j)) (nat.eqb j i))
           i)
          (λ (Hc : sttfa.eps (logic.eq bool.bool (nat.eqb j i) bool.true)),
             logic.eq_ind_r bool.bool bool.true
             (λ (x : sttfa.etap (sttfa.p bool.bool)),
                logic.eq nat.nat
                (bool.match_bool_type nat.nat j
                 (bool.match_bool_type nat.nat i j (nat.eqb j j)) x)
                i)
             (bool.sym_eq_match_bool_type_true nat.nat j
              (bool.match_bool_type nat.nat i j (nat.eqb j j))
              (λ (y : sttfa.etap (sttfa.p nat.nat)), logic.eq nat.nat y i)
              (logic.eq_ind_r nat.nat i
               (λ (x : sttfa.etap (sttfa.p nat.nat)), logic.eq nat.nat x i)
               (logic.refl nat.nat i) j (nat.eqb_true_to_eq j i Hc)))
             (nat.eqb j i) Hc)
          (λ (Hc : sttfa.eps (logic.eq bool.bool (nat.eqb j i) bool.false)),
             logic.eq_ind_r bool.bool bool.false
             (λ (x : sttfa.etap (sttfa.p bool.bool)),
                logic.eq nat.nat
                (bool.match_bool_type nat.nat j
                 (bool.match_bool_type nat.nat i j (nat.eqb j j)) x)
                i)
             (logic.eq_ind_r bool.bool bool.true
              (λ (x : sttfa.etap (sttfa.p bool.bool)),
                 logic.eq nat.nat
                 (bool.match_bool_type nat.nat j
                  (bool.match_bool_type nat.nat i j x) bool.false)
                 i)
              (bool.sym_eq_match_bool_type_false nat.nat j
               (bool.match_bool_type nat.nat i j bool.true)
               (λ (y : sttfa.etap (sttfa.p nat.nat)), logic.eq nat.nat y i)
               (bool.eq_match_bool_type_true nat.nat i j
                (λ (y : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat
                   (bool.match_bool_type nat.nat i j bool.true) y)
                (bool.eq_match_bool_type_false nat.nat j
                 (bool.match_bool_type nat.nat i j bool.true)
                 (λ (y : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat
                    (bool.match_bool_type nat.nat i j bool.true) y)
                 (bool.eq_match_bool_type_false nat.nat j
                  (bool.match_bool_type nat.nat i j bool.true)
                  (λ (y : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat y
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i j bool.true) bool.false))
                  (logic.refl nat.nat
                   (bool.match_bool_type nat.nat j
                    (bool.match_bool_type nat.nat i j bool.true) bool.false))))))
              (nat.eqb j j) (nat.eqb_n_n j))
             (nat.eqb j i) Hc)
          (bool.true_or_false (nat.eqb j i));
symbol transpose_i_j_j_i
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (i : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (j : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (n : sttfa.etap (sttfa.p nat.nat)),
              logic.eq nat.nat (transpose i j n)
              (transpose j i n)))))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            connectives.match_Or_prop
            (logic.eq bool.bool (nat.eqb n i) bool.true)
            (logic.eq bool.bool (nat.eqb n i) bool.false)
            (logic.eq nat.nat
             (bool.match_bool_type nat.nat j
              (bool.match_bool_type nat.nat i n (nat.eqb n j)) (nat.eqb n i))
             (bool.match_bool_type nat.nat i
              (bool.match_bool_type nat.nat j n (nat.eqb n i)) (nat.eqb n j)))
            (λ
               (Hni : sttfa.eps (logic.eq bool.bool (nat.eqb n i) bool.true)),
               logic.eq_ind_r bool.bool bool.true
               (λ (x : sttfa.etap (sttfa.p bool.bool)),
                  logic.eq nat.nat
                  (bool.match_bool_type nat.nat j
                   (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                  (bool.match_bool_type nat.nat i
                   (bool.match_bool_type nat.nat j n x) (nat.eqb n j)))
               (connectives.match_Or_prop
                (logic.eq bool.bool (nat.eqb n j) bool.true)
                (logic.eq bool.bool (nat.eqb n j) bool.false)
                (logic.eq nat.nat
                 (bool.match_bool_type nat.nat j
                  (bool.match_bool_type nat.nat i n (nat.eqb n j)) bool.true)
                 (bool.match_bool_type nat.nat i
                  (bool.match_bool_type nat.nat j n bool.true) (nat.eqb n j)))
                (λ
                   (
                   Hnj : sttfa.eps
                         (logic.eq bool.bool (nat.eqb n j) bool.true)
                   ),
                   logic.eq_ind_r bool.bool bool.true
                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                      logic.eq nat.nat
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n x) bool.true)
                      (bool.match_bool_type nat.nat i
                       (bool.match_bool_type nat.nat j n bool.true) x))
                   (bool.sym_eq_match_bool_type_true nat.nat j
                    (bool.match_bool_type nat.nat i n bool.true)
                    (λ (y : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat y
                       (bool.match_bool_type nat.nat i
                        (bool.match_bool_type nat.nat j n bool.true)
                        bool.true))
                    (bool.sym_eq_match_bool_type_true nat.nat i
                     (bool.match_bool_type nat.nat j n bool.true)
                     (λ (y : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat j y)
                     (logic.eq_ind nat.nat n
                      (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat j x_1)
                      (logic.eq_ind nat.nat n
                       (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat x_1 n)
                       (logic.refl nat.nat n) j (nat.eqb_true_to_eq n j Hnj))
                      i (nat.eqb_true_to_eq n i Hni))))
                   (nat.eqb n j) Hnj)
                (λ
                   (
                   Hnj : sttfa.eps
                         (logic.eq bool.bool (nat.eqb n j) bool.false)
                   ),
                   logic.eq_ind_r bool.bool bool.false
                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                      logic.eq nat.nat
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n x) bool.true)
                      (bool.match_bool_type nat.nat i
                       (bool.match_bool_type nat.nat j n bool.true) x))
                   (bool.sym_eq_match_bool_type_false nat.nat i n
                    (λ (y : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat
                       (bool.match_bool_type nat.nat j y bool.true)
                       (bool.match_bool_type nat.nat i
                        (bool.match_bool_type nat.nat j n bool.true)
                        bool.false))
                    (bool.sym_eq_match_bool_type_false nat.nat i
                     (bool.match_bool_type nat.nat j n bool.true)
                     (λ (y : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (bool.match_bool_type nat.nat j n bool.true) y)
                     (bool.sym_eq_match_bool_type_true nat.nat j n
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat j n bool.true) y)
                      (bool.sym_eq_match_bool_type_true nat.nat j n
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat y j)
                       (logic.refl nat.nat j)))))
                   (nat.eqb n j) Hnj)
                (bool.true_or_false (nat.eqb n j)))
               (nat.eqb n i) Hni)
            (λ
               (Hni : sttfa.eps (logic.eq bool.bool (nat.eqb n i) bool.false)
               ),
               logic.eq_ind_r bool.bool bool.false
               (λ (x : sttfa.etap (sttfa.p bool.bool)),
                  logic.eq nat.nat
                  (bool.match_bool_type nat.nat j
                   (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                  (bool.match_bool_type nat.nat i
                   (bool.match_bool_type nat.nat j n x) (nat.eqb n j)))
               (connectives.match_Or_prop
                (logic.eq bool.bool (nat.eqb n j) bool.true)
                (logic.eq bool.bool (nat.eqb n j) bool.false)
                (logic.eq nat.nat
                 (bool.match_bool_type nat.nat j
                  (bool.match_bool_type nat.nat i n (nat.eqb n j)) bool.false)
                 (bool.match_bool_type nat.nat i
                  (bool.match_bool_type nat.nat j n bool.false) (nat.eqb n j)))
                (λ
                   (
                   Hnj : sttfa.eps
                         (logic.eq bool.bool (nat.eqb n j) bool.true)
                   ),
                   logic.eq_ind_r bool.bool bool.true
                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                      logic.eq nat.nat
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n x) bool.false)
                      (bool.match_bool_type nat.nat i
                       (bool.match_bool_type nat.nat j n bool.false) x))
                   (bool.sym_eq_match_bool_type_false nat.nat j
                    (bool.match_bool_type nat.nat i n bool.true)
                    (λ (y : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat y
                       (bool.match_bool_type nat.nat i
                        (bool.match_bool_type nat.nat j n bool.false)
                        bool.true))
                    (bool.sym_eq_match_bool_type_false nat.nat j n
                     (λ (y : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (bool.match_bool_type nat.nat i n bool.true)
                        (bool.match_bool_type nat.nat i y bool.true))
                     (bool.sym_eq_match_bool_type_true nat.nat i n
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat i n bool.true) y)
                      (bool.sym_eq_match_bool_type_true nat.nat i n
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat y i)
                       (logic.refl nat.nat i)))))
                   (nat.eqb n j) Hnj)
                (λ
                   (
                   Hnj : sttfa.eps
                         (logic.eq bool.bool (nat.eqb n j) bool.false)
                   ),
                   logic.eq_ind_r bool.bool bool.false
                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                      logic.eq nat.nat
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n x) bool.false)
                      (bool.match_bool_type nat.nat i
                       (bool.match_bool_type nat.nat j n bool.false) x))
                   (bool.sym_eq_match_bool_type_false nat.nat i n
                    (λ (y : sttfa.etap (sttfa.p nat.nat)),
                       logic.eq nat.nat
                       (bool.match_bool_type nat.nat j y bool.false)
                       (bool.match_bool_type nat.nat i
                        (bool.match_bool_type nat.nat j n bool.false)
                        bool.false))
                    (bool.sym_eq_match_bool_type_false nat.nat j n
                     (λ (y : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (bool.match_bool_type nat.nat j n bool.false)
                        (bool.match_bool_type nat.nat i y bool.false))
                     (bool.sym_eq_match_bool_type_false nat.nat j n
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat y
                         (bool.match_bool_type nat.nat i n bool.false))
                      (bool.sym_eq_match_bool_type_false nat.nat i n
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat n y)
                       (logic.refl nat.nat n)))))
                   (nat.eqb n j) Hnj)
                (bool.true_or_false (nat.eqb n j)))
               (nat.eqb n i) Hni)
            (bool.true_or_false (nat.eqb n i));
symbol transpose_transpose
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (i : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (j : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (n : sttfa.etap (sttfa.p nat.nat)),
              logic.eq nat.nat
              (transpose i j (transpose i j n)) n))))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            connectives.match_Or_prop
            (logic.eq bool.bool (nat.eqb n i) bool.true)
            (logic.eq bool.bool (nat.eqb n i) bool.false)
            (logic.eq nat.nat
             (bool.match_bool_type nat.nat j
              (bool.match_bool_type nat.nat i
               (bool.match_bool_type nat.nat j
                (bool.match_bool_type nat.nat i n (nat.eqb n j))
                (nat.eqb n i))
               (nat.eqb
                (bool.match_bool_type nat.nat j
                 (bool.match_bool_type nat.nat i n (nat.eqb n j))
                 (nat.eqb n i))
                j))
              (nat.eqb
               (bool.match_bool_type nat.nat j
                (bool.match_bool_type nat.nat i n (nat.eqb n j))
                (nat.eqb n i))
               i))
             n)
            (λ
               (Hni : sttfa.eps (logic.eq bool.bool (nat.eqb n i) bool.true)),
               logic.eq_ind_r bool.bool bool.true
               (λ (x : sttfa.etap (sttfa.p bool.bool)),
                  logic.eq nat.nat
                  (bool.match_bool_type nat.nat j
                   (bool.match_bool_type nat.nat i
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                    (nat.eqb
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                     j))
                   (nat.eqb
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                    i))
                  n)
               (bool.sym_eq_match_bool_type_true nat.nat j
                (bool.match_bool_type nat.nat i n (nat.eqb n j))
                (λ (y : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat
                   (bool.match_bool_type nat.nat j
                    (bool.match_bool_type nat.nat i
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i n (nat.eqb n j))
                      bool.true)
                     (nat.eqb
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n (nat.eqb n j))
                       bool.true)
                      j))
                    (nat.eqb y i))
                   n)
                (bool.sym_eq_match_bool_type_true nat.nat j
                 (bool.match_bool_type nat.nat i n (nat.eqb n j))
                 (λ (y : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n (nat.eqb n j))
                       bool.true)
                      (nat.eqb y j))
                     (nat.eqb j i))
                    n)
                 (bool.sym_eq_match_bool_type_true nat.nat j
                  (bool.match_bool_type nat.nat i n (nat.eqb n j))
                  (λ (y : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i y (nat.eqb j j))
                      (nat.eqb j i))
                     n)
                  (connectives.match_Or_prop
                   (logic.eq bool.bool (nat.eqb j i) bool.true)
                   (logic.eq bool.bool (nat.eqb j i) bool.false)
                   (logic.eq nat.nat
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i j (nat.eqb j j))
                     (nat.eqb j i))
                    n)
                   (λ
                      (
                      Hji : sttfa.eps
                            (logic.eq bool.bool (nat.eqb j i) bool.true)
                      ),
                      logic.eq_ind_r bool.bool bool.true
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat j
                          (bool.match_bool_type nat.nat i j (nat.eqb j j)) x)
                         n)
                      (bool.sym_eq_match_bool_type_true nat.nat j
                       (bool.match_bool_type nat.nat i j (nat.eqb j j))
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat y n)
                       (logic.eq_ind_r nat.nat i
                        (λ (x : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat j x)
                        (nat.eqb_true_to_eq j i Hji) n
                        (nat.eqb_true_to_eq n i Hni)))
                      (nat.eqb j i) Hji)
                   (λ
                      (
                      Hji : sttfa.eps
                            (logic.eq bool.bool (nat.eqb j i) bool.false)
                      ),
                      logic.eq_ind_r bool.bool bool.false
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat j
                          (bool.match_bool_type nat.nat i j (nat.eqb j j)) x)
                         n)
                      (bool.sym_eq_match_bool_type_false nat.nat j
                       (bool.match_bool_type nat.nat i j (nat.eqb j j))
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat y n)
                       (logic.eq_ind_r bool.bool bool.true
                        (λ (x : sttfa.etap (sttfa.p bool.bool)),
                           logic.eq nat.nat
                           (bool.match_bool_type nat.nat i j x) n)
                        (bool.sym_eq_match_bool_type_true nat.nat i j
                         (λ (y : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat y n)
                         (logic.sym_eq nat.nat n i
                          (nat.eqb_true_to_eq n i Hni)))
                        (nat.eqb j j) (nat.eqb_n_n j)))
                      (nat.eqb j i) Hji)
                   (bool.true_or_false (nat.eqb j i))))))
               (nat.eqb n i) Hni)
            (λ
               (Hni : sttfa.eps (logic.eq bool.bool (nat.eqb n i) bool.false)
               ),
               logic.eq_ind_r bool.bool bool.false
               (λ (x : sttfa.etap (sttfa.p bool.bool)),
                  logic.eq nat.nat
                  (bool.match_bool_type nat.nat j
                   (bool.match_bool_type nat.nat i
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                    (nat.eqb
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                     j))
                   (nat.eqb
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i n (nat.eqb n j)) x)
                    i))
                  n)
               (bool.sym_eq_match_bool_type_false nat.nat j
                (bool.match_bool_type nat.nat i n (nat.eqb n j))
                (λ (y : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat
                   (bool.match_bool_type nat.nat j
                    (bool.match_bool_type nat.nat i
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i n (nat.eqb n j))
                      bool.false)
                     (nat.eqb
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n (nat.eqb n j))
                       bool.false)
                      j))
                    (nat.eqb y i))
                   n)
                (bool.sym_eq_match_bool_type_false nat.nat j
                 (bool.match_bool_type nat.nat i n (nat.eqb n j))
                 (λ (y : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i
                      (bool.match_bool_type nat.nat j
                       (bool.match_bool_type nat.nat i n (nat.eqb n j))
                       bool.false)
                      (nat.eqb y j))
                     (nat.eqb
                      (bool.match_bool_type nat.nat i n (nat.eqb n j)) i))
                    n)
                 (bool.sym_eq_match_bool_type_false nat.nat j
                  (bool.match_bool_type nat.nat i n (nat.eqb n j))
                  (λ (y : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat
                     (bool.match_bool_type nat.nat j
                      (bool.match_bool_type nat.nat i y
                       (nat.eqb
                        (bool.match_bool_type nat.nat i n (nat.eqb n j)) j))
                      (nat.eqb
                       (bool.match_bool_type nat.nat i n (nat.eqb n j)) i))
                     n)
                  (connectives.match_Or_prop
                   (logic.eq bool.bool (nat.eqb n j) bool.true)
                   (logic.eq bool.bool (nat.eqb n j) bool.false)
                   (logic.eq nat.nat
                    (bool.match_bool_type nat.nat j
                     (bool.match_bool_type nat.nat i
                      (bool.match_bool_type nat.nat i n (nat.eqb n j))
                      (nat.eqb
                       (bool.match_bool_type nat.nat i n (nat.eqb n j)) j))
                     (nat.eqb
                      (bool.match_bool_type nat.nat i n (nat.eqb n j)) i))
                    n)
                   (λ
                      (
                      Hnj : sttfa.eps
                            (logic.eq bool.bool (nat.eqb n j) bool.true)
                      ),
                      logic.eq_ind_r bool.bool bool.true
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat j
                          (bool.match_bool_type nat.nat i
                           (bool.match_bool_type nat.nat i n x)
                           (nat.eqb (bool.match_bool_type nat.nat i n x) j))
                          (nat.eqb (bool.match_bool_type nat.nat i n x) i))
                         n)
                      (bool.sym_eq_match_bool_type_true nat.nat i n
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat
                          (bool.match_bool_type nat.nat j
                           (bool.match_bool_type nat.nat i
                            (bool.match_bool_type nat.nat i n bool.true)
                            (nat.eqb
                             (bool.match_bool_type nat.nat i n bool.true) j))
                           (nat.eqb y i))
                          n)
                       (bool.sym_eq_match_bool_type_true nat.nat i n
                        (λ (y : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (bool.match_bool_type nat.nat j
                            (bool.match_bool_type nat.nat i
                             (bool.match_bool_type nat.nat i n bool.true)
                             (nat.eqb y j))
                            (nat.eqb i i))
                           n)
                        (bool.sym_eq_match_bool_type_true nat.nat i n
                         (λ (y : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat
                            (bool.match_bool_type nat.nat j
                             (bool.match_bool_type nat.nat i y (nat.eqb i j))
                             (nat.eqb i i))
                            n)
                         (logic.eq_ind_r bool.bool bool.true
                          (λ (x : sttfa.etap (sttfa.p bool.bool)),
                             logic.eq nat.nat
                             (bool.match_bool_type nat.nat j
                              (bool.match_bool_type nat.nat i i (nat.eqb i j))
                              x)
                             n)
                          (bool.sym_eq_match_bool_type_true nat.nat j
                           (bool.match_bool_type nat.nat i i (nat.eqb i j))
                           (λ (y : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat y n)
                           (logic.sym_eq nat.nat n j
                            (nat.eqb_true_to_eq n j Hnj)))
                          (nat.eqb i i) (nat.eqb_n_n i)))))
                      (nat.eqb n j) Hnj)
                   (λ
                      (
                      Hnj : sttfa.eps
                            (logic.eq bool.bool (nat.eqb n j) bool.false)
                      ),
                      logic.eq_ind_r bool.bool bool.false
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat j
                          (bool.match_bool_type nat.nat i
                           (bool.match_bool_type nat.nat i n x)
                           (nat.eqb (bool.match_bool_type nat.nat i n x) j))
                          (nat.eqb (bool.match_bool_type nat.nat i n x) i))
                         n)
                      (bool.sym_eq_match_bool_type_false nat.nat i n
                       (λ (y : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat
                          (bool.match_bool_type nat.nat j
                           (bool.match_bool_type nat.nat i
                            (bool.match_bool_type nat.nat i n bool.false)
                            (nat.eqb
                             (bool.match_bool_type nat.nat i n bool.false) j))
                           (nat.eqb y i))
                          n)
                       (bool.sym_eq_match_bool_type_false nat.nat i n
                        (λ (y : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (bool.match_bool_type nat.nat j
                            (bool.match_bool_type nat.nat i
                             (bool.match_bool_type nat.nat i n bool.false)
                             (nat.eqb y j))
                            (nat.eqb n i))
                           n)
                        (bool.sym_eq_match_bool_type_false nat.nat i n
                         (λ (y : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat
                            (bool.match_bool_type nat.nat j
                             (bool.match_bool_type nat.nat i y (nat.eqb n j))
                             (nat.eqb n i))
                            n)
                         (logic.eq_ind_r bool.bool bool.false
                          (λ (x : sttfa.etap (sttfa.p bool.bool)),
                             logic.eq nat.nat
                             (bool.match_bool_type nat.nat j
                              (bool.match_bool_type nat.nat i n (nat.eqb n j))
                              x)
                             n)
                          (logic.eq_ind_r bool.bool bool.false
                           (λ (x : sttfa.etap (sttfa.p bool.bool)),
                              logic.eq nat.nat
                              (bool.match_bool_type nat.nat j
                               (bool.match_bool_type nat.nat i n x)
                               bool.false)
                              n)
                           (bool.eq_match_bool_type_false nat.nat i n
                            (λ (y : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat
                               (bool.match_bool_type nat.nat j
                                (bool.match_bool_type nat.nat i n bool.false)
                                bool.false)
                               y)
                            (bool.eq_match_bool_type_false nat.nat j
                             (bool.match_bool_type nat.nat i n bool.false)
                             (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                logic.eq nat.nat
                                (bool.match_bool_type nat.nat j
                                 (bool.match_bool_type nat.nat i n bool.false)
                                 bool.false)
                                y)
                             (logic.refl nat.nat
                              (bool.match_bool_type nat.nat j
                               (bool.match_bool_type nat.nat i n bool.false)
                               bool.false))))
                           (nat.eqb n j) Hnj)
                          (nat.eqb n i) Hni))))
                      (nat.eqb n j) Hnj)
                   (bool.true_or_false (nat.eqb n j))))))
               (nat.eqb n i) Hni)
            (bool.true_or_false (nat.eqb n i));
symbol injective_transpose
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (i : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (j : sttfa.etap (sttfa.p nat.nat)),
           relations.injective_ nat.nat nat.nat (transpose i j))))
  ≔ λ (i : sttfa.etap (sttfa.p nat.nat)),
        λ (j : sttfa.etap (sttfa.p nat.nat)),
          λ (x : sttfa.etap (sttfa.p nat.nat)),
            λ (y : sttfa.etap (sttfa.p nat.nat)),
              λ
                (
                auto : sttfa.eps
                       (logic.eq nat.nat (transpose i j x)
                        (transpose i j y))
                ),
                logic.rewrite_r nat.nat y
                (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                   logic.eq nat.nat __ y)
                (logic.refl nat.nat y) x
                (logic.rewrite_l nat.nat
                 (transpose i j (transpose i j x))
                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                    logic.eq nat.nat __ y)
                 (logic.rewrite_r nat.nat (transpose i j y)
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                     logic.eq nat.nat (transpose i j __) y)
                  (transpose_transpose i j y)
                  (transpose i j x) auto)
                 x (transpose_transpose i j x));
symbol permut_S_to_permut_transpose
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (permut f (nat.S m))
           (permut
            (λ (n : sttfa.etap (sttfa.p nat.nat)),
               transpose (f (nat.S m)) (nat.S m) (f n))
            m))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          λ (_clearme : sttfa.eps (permut f (nat.S m))),
            connectives.match_And_prop
            (sttfa.forall nat.nat
             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                sttfa.impl (nat.le i (nat.S m)) (nat.le (f i) (nat.S m))))
            (injn f (nat.S m))
            (permut
             (λ (n : sttfa.etap (sttfa.p nat.nat)),
                transpose (f (nat.S m)) (nat.S m) (f n))
             m)
            (λ
               (
               permf1 : sttfa.eps
                        (sttfa.forall nat.nat
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            sttfa.impl (nat.le i (nat.S m))
                            (nat.le (f i) (nat.S m))))
               ),
               λ (permf2 : sttfa.eps (injn f (nat.S m))),
                 connectives.conj
                 (sttfa.forall nat.nat
                  (λ (x : sttfa.etap (sttfa.p nat.nat)),
                     sttfa.impl (nat.le x m)
                     (nat.le
                      (transpose (f (nat.S m)) (nat.S m) (f x)) m)))
                 (injn
                  (λ (n : sttfa.etap (sttfa.p nat.nat)),
                     transpose (f (nat.S m)) (nat.S m) (f n))
                  m)
                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                    λ (leim : sttfa.eps (nat.le i m)),
                      logic.eq_ind_r bool.bool bool.false
                      (λ (x : sttfa.etap (sttfa.p bool.bool)),
                         nat.le
                         (bool.match_bool_type nat.nat (nat.S m)
                          (bool.match_bool_type nat.nat (f (nat.S m)) (f i)
                           (nat.eqb (f i) (nat.S m)))
                          x)
                         m)
                      (bool.sym_eq_match_bool_type_false nat.nat (nat.S m)
                       (bool.match_bool_type nat.nat (f (nat.S m)) (f i)
                        (nat.eqb (f i) (nat.S m)))
                       (λ (y : sttfa.etap (sttfa.p nat.nat)), nat.le y m)
                       (connectives.match_Or_prop (nat.lt (f i) (nat.S m))
                        (logic.eq nat.nat (f i) (nat.S m))
                        (nat.le
                         (bool.match_bool_type nat.nat (f (nat.S m)) (f i)
                          (nat.eqb (f i) (nat.S m)))
                         m)
                        (λ (Hfi : sttfa.eps (nat.lt (f i) (nat.S m))),
                           logic.eq_ind_r bool.bool bool.false
                           (λ (x : sttfa.etap (sttfa.p bool.bool)),
                              nat.le
                              (bool.match_bool_type nat.nat (f (nat.S m))
                               (f i) x)
                              m)
                           (bool.sym_eq_match_bool_type_false nat.nat
                            (f (nat.S m)) (f i)
                            (λ (y : sttfa.etap (sttfa.p nat.nat)),
                               nat.le y m)
                            (nat.le_S_S_to_le (f i) m Hfi))
                           (nat.eqb (f i) (nat.S m))
                           (nat.not_eq_to_eqb_false (f i) (nat.S m)
                            (nat.lt_to_not_eq (f i) (nat.S m) Hfi)))
                        (λ
                           (
                           Hfi : sttfa.eps (logic.eq nat.nat (f i) (nat.S m))
                           ),
                           logic.eq_ind_r bool.bool bool.true
                           (λ (x : sttfa.etap (sttfa.p bool.bool)),
                              nat.le
                              (bool.match_bool_type nat.nat (f (nat.S m))
                               (f i) x)
                              m)
                           (bool.sym_eq_match_bool_type_true nat.nat
                            (f (nat.S m)) (f i)
                            (λ (y : sttfa.etap (sttfa.p nat.nat)),
                               nat.le y m)
                            (connectives.match_Or_prop
                             (nat.lt (f (nat.S m)) (nat.S m))
                             (logic.eq nat.nat (f (nat.S m)) (nat.S m))
                             (nat.le (f (nat.S m)) m)
                             (λ
                                (
                                H : sttfa.eps
                                    (nat.lt (f (nat.S m)) (nat.S m))
                                ), nat.le_S_S_to_le (f (nat.S m)) m H)
                             (λ
                                (
                                H : sttfa.eps
                                    (logic.eq nat.nat (f (nat.S m)) (nat.S m))
                                ),
                                connectives.falsity (nat.le (f (nat.S m)) m)
                                (logic.absurd (logic.eq nat.nat i (nat.S m))
                                 (permf2 i (nat.S m) (nat.le_S i m leim)
                                  (nat.le_n (nat.S m))
                                  (logic.rewrite_l nat.nat (f i)
                                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                      logic.eq nat.nat (f i) (f __))
                                   (logic.rewrite_r nat.nat (f i)
                                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                       logic.eq nat.nat (f i) __)
                                    (logic.refl nat.nat (f i)) (f (f i))
                                    (logic.rewrite_r nat.nat (nat.S m)
                                     (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                        logic.eq nat.nat (f (f i)) __)
                                     (logic.rewrite_r nat.nat (nat.S m)
                                      (λ
                                         (__ : sttfa.etap (sttfa.p nat.nat)),
                                         logic.eq nat.nat (f __) (nat.S m))
                                      H (f i) Hfi)
                                     (f i) Hfi))
                                   (nat.S m) Hfi))
                                 (logic.not_to_not
                                  (logic.eq nat.nat i (nat.S m))
                                  (nat.le (nat.S m) m)
                                  (λ
                                     (
                                     auto : sttfa.eps
                                            (logic.eq nat.nat i (nat.S m))
                                     ),
                                     logic.eq_coerc (nat.le i m)
                                     (nat.le (nat.S m) m) leim
                                     (logic.rewrite_l nat.nat i
                                      (λ
                                         (__ : sttfa.etap (sttfa.p nat.nat)),
                                         logic.eq sttfa.bool (nat.le i m)
                                         (nat.le __ m))
                                      (logic.refl sttfa.bool (nat.le i m))
                                      (nat.S m) auto))
                                  (nat.lt_to_not_le m (nat.S m)
                                   (nat.le_n (nat.S m))))))
                             (nat.le_to_or_lt_eq (f (nat.S m)) (nat.S m)
                              (permf1 (nat.S m) (nat.le_n (nat.S m))))))
                           (nat.eqb (f i) (nat.S m))
                           (nat.eq_to_eqb_true (f i) (nat.S m) Hfi))
                        (nat.le_to_or_lt_eq (f i) (nat.S m)
                         (permf1 i (nat.le_S i m leim)))))
                      (nat.eqb (f i) (f (nat.S m)))
                      (nat.not_eq_to_eqb_false (f i) (f (nat.S m))
                       (connectives.nmk
                        (logic.eq nat.nat (f i) (f (nat.S m)))
                        (λ
                           (
                           H : sttfa.eps
                               (logic.eq nat.nat (f i) (f (nat.S m)))
                           ),
                           logic.absurd (logic.eq nat.nat i (nat.S m))
                           (permf2 i (nat.S m) (nat.le_S i m leim)
                            (nat.le_n (nat.S m)) H)
                           (nat.lt_to_not_eq i (nat.S m)
                            (nat.le_S_S i m leim))))))
                 (λ (a : sttfa.etap (sttfa.p nat.nat)),
                    λ (b : sttfa.etap (sttfa.p nat.nat)),
                      λ (leam : sttfa.eps (nat.le a m)),
                        λ (lebm : sttfa.eps (nat.le b m)),
                          λ
                            (
                            H : sttfa.eps
                                (logic.eq nat.nat
                                 (transpose (f (nat.S m))
                                  (nat.S m) (f a))
                                 (transpose (f (nat.S m))
                                  (nat.S m) (f b)))
                            ),
                            permf2 a b (nat.le_S a m leam)
                            (nat.le_S b m lebm)
                            (injective_transpose (f (nat.S m))
                             (nat.S m) (f a) (f b) H)))
            _clearme;
symbol bijn
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
      (sttfa.arrow nat.nat sttfa.bool)))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          sttfa.forall nat.nat
          (λ (m : sttfa.etap (sttfa.p nat.nat)),
             sttfa.impl (nat.le m n)
             (connectives.ex nat.nat
              (λ (p : sttfa.etap (sttfa.p nat.nat)),
                 connectives.And (nat.le p n) (logic.eq nat.nat (f p) m))));
symbol eq_to_bijn
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall nat.nat
           (λ (n : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl
              (sttfa.forall nat.nat
               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.impl (nat.le i n) (logic.eq nat.nat (f i) (g i))))
              (sttfa.impl (bijn f n) (bijn g n))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            λ
              (
              H : sttfa.eps
                  (sttfa.forall nat.nat
                   (λ (i : sttfa.etap (sttfa.p nat.nat)),
                      sttfa.impl (nat.le i n) (logic.eq nat.nat (f i) (g i))))
              ),
              λ (bijf : sttfa.eps (bijn f n)),
                λ (i : sttfa.etap (sttfa.p nat.nat)),
                  λ (lein : sttfa.eps (nat.le i n)),
                    connectives.match_ex_prop nat.nat
                    (λ (p : sttfa.etap (sttfa.p nat.nat)),
                       connectives.And (nat.le p n)
                       (logic.eq nat.nat (f p) i))
                    (connectives.ex nat.nat
                     (λ (p : sttfa.etap (sttfa.p nat.nat)),
                        connectives.And (nat.le p n)
                        (logic.eq nat.nat (g p) i)))
                    (λ (a : sttfa.etap (sttfa.p nat.nat)),
                       λ
                         (
                         _clearme : sttfa.eps
                                    (connectives.And (nat.le a n)
                                     (logic.eq nat.nat (f a) i))
                         ),
                         connectives.match_And_prop (nat.le a n)
                         (logic.eq nat.nat (f a) i)
                         (connectives.ex nat.nat
                          (λ (p : sttfa.etap (sttfa.p nat.nat)),
                             connectives.And (nat.le p n)
                             (logic.eq nat.nat (g p) i)))
                         (λ (lean : sttfa.eps (nat.le a n)),
                            λ (fa : sttfa.eps (logic.eq nat.nat (f a) i)),
                              connectives.ex_intro nat.nat
                              (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                 connectives.And (nat.le x n)
                                 (logic.eq nat.nat (g x) i))
                              a
                              (connectives.conj (nat.le a n)
                               (logic.eq nat.nat (g a) i) lean
                               (logic.eq_ind nat.nat (f a)
                                (λ (x_1 : sttfa.etap (sttfa.p nat.nat)),
                                   logic.eq nat.nat (g a) x_1)
                                (logic.sym_eq nat.nat (f a) (g a) (H a lean))
                                i fa)))
                         _clearme)
                    (bijf i lein);
symbol bijn_n_Sn
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (bijn f n)
           (sttfa.impl (logic.eq nat.nat (f (nat.S n)) (nat.S n))
            (bijn f (nat.S n))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (bijf : sttfa.eps (bijn f n)),
            λ (fS : sttfa.eps (logic.eq nat.nat (f (nat.S n)) (nat.S n))),
              λ (i : sttfa.etap (sttfa.p nat.nat)),
                λ (lein : sttfa.eps (nat.le i (nat.S n))),
                  connectives.match_Or_prop (nat.lt i (nat.S n))
                  (logic.eq nat.nat i (nat.S n))
                  (connectives.ex nat.nat
                   (λ (p : sttfa.etap (sttfa.p nat.nat)),
                      connectives.And (nat.le p (nat.S n))
                      (logic.eq nat.nat (f p) i)))
                  (λ (Hi : sttfa.eps (nat.lt i (nat.S n))),
                     connectives.match_ex_prop nat.nat
                     (λ (p : sttfa.etap (sttfa.p nat.nat)),
                        connectives.And (nat.le p n)
                        (logic.eq nat.nat (f p) i))
                     (connectives.ex nat.nat
                      (λ (p : sttfa.etap (sttfa.p nat.nat)),
                         connectives.And (nat.le p (nat.S n))
                         (logic.eq nat.nat (f p) i)))
                     (λ (a : sttfa.etap (sttfa.p nat.nat)),
                        λ
                          (
                          _clearme : sttfa.eps
                                     (connectives.And (nat.le a n)
                                      (logic.eq nat.nat (f a) i))
                          ),
                          connectives.match_And_prop (nat.le a n)
                          (logic.eq nat.nat (f a) i)
                          (connectives.ex nat.nat
                           (λ (p : sttfa.etap (sttfa.p nat.nat)),
                              connectives.And (nat.le p (nat.S n))
                              (logic.eq nat.nat (f p) i)))
                          (λ (lean : sttfa.eps (nat.le a n)),
                             λ (fa : sttfa.eps (logic.eq nat.nat (f a) i)),
                               connectives.ex_intro nat.nat
                               (λ (x : sttfa.etap (sttfa.p nat.nat)),
                                  connectives.And (nat.le x (nat.S n))
                                  (logic.eq nat.nat (f x) i))
                               a
                               (connectives.conj (nat.le a (nat.S n))
                                (logic.eq nat.nat (f a) i)
                                (nat.le_S a n lean)
                                (logic.rewrite_r nat.nat i
                                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat __ i)
                                 (logic.refl nat.nat i) (f a) fa)))
                          _clearme)
                     (bijf i (nat.le_S_S_to_le i n Hi)))
                  (λ (Hi : sttfa.eps (logic.eq nat.nat i (nat.S n))),
                     connectives.ex_intro nat.nat
                     (λ (x : sttfa.etap (sttfa.p nat.nat)),
                        connectives.And (nat.le x (nat.S n))
                        (logic.eq nat.nat (f x) i))
                     i
                     (connectives.conj (nat.le i (nat.S n))
                      (logic.eq nat.nat (f i) i)
                      (logic.eq_coerc (nat.le i i) (nat.le i (nat.S n))
                       (nat.le_n i)
                       (logic.rewrite_l nat.nat i
                        (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq sttfa.bool (nat.le i i) (nat.le i __))
                        (logic.refl sttfa.bool (nat.le i i)) (nat.S n) Hi))
                      (logic.rewrite_r nat.nat i
                       (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                          logic.eq nat.nat __ i)
                       (logic.refl nat.nat i) (f i)
                       (logic.rewrite_r nat.nat (nat.S n)
                        (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat (f i) __)
                        (logic.rewrite_r nat.nat (nat.S n)
                         (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat (f __) (nat.S n))
                         fS i Hi)
                        i Hi))))
                  (nat.le_to_or_lt_eq i (nat.S n) lein);
symbol bijn_fg
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.forall nat.nat
           (λ (n : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (bijn f n)
              (sttfa.impl (bijn g n)
               (bijn
                (λ (p : sttfa.etap (sttfa.p nat.nat)), f (g p)) n))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (g : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
          λ (n : sttfa.etap (sttfa.p nat.nat)),
            λ (bijf : sttfa.eps (bijn f n)),
              λ (bijg : sttfa.eps (bijn g n)),
                λ (i : sttfa.etap (sttfa.p nat.nat)),
                  λ (lein : sttfa.eps (nat.le i n)),
                    connectives.match_ex_prop nat.nat
                    (λ (p : sttfa.etap (sttfa.p nat.nat)),
                       connectives.And (nat.le p n)
                       (logic.eq nat.nat (f p) i))
                    (connectives.ex nat.nat
                     (λ (p : sttfa.etap (sttfa.p nat.nat)),
                        connectives.And (nat.le p n)
                        (logic.eq nat.nat (f (g p)) i)))
                    (λ (a : sttfa.etap (sttfa.p nat.nat)),
                       λ
                         (
                         _clearme : sttfa.eps
                                    (connectives.And (nat.le a n)
                                     (logic.eq nat.nat (f a) i))
                         ),
                         connectives.match_And_prop (nat.le a n)
                         (logic.eq nat.nat (f a) i)
                         (connectives.ex nat.nat
                          (λ (p : sttfa.etap (sttfa.p nat.nat)),
                             connectives.And (nat.le p n)
                             (logic.eq nat.nat (f (g p)) i)))
                         (λ (lean : sttfa.eps (nat.le a n)),
                            λ (ga : sttfa.eps (logic.eq nat.nat (f a) i)),
                              connectives.match_ex_prop nat.nat
                              (λ (p : sttfa.etap (sttfa.p nat.nat)),
                                 connectives.And (nat.le p n)
                                 (logic.eq nat.nat (g p) a))
                              (connectives.ex nat.nat
                               (λ (p : sttfa.etap (sttfa.p nat.nat)),
                                  connectives.And (nat.le p n)
                                  (logic.eq nat.nat (f (g p)) i)))
                              (λ (b : sttfa.etap (sttfa.p nat.nat)),
                                 λ
                                   (
                                   _clearme0 : sttfa.eps
                                               (connectives.And (nat.le b n)
                                                (logic.eq nat.nat (g b) a))
                                   ),
                                   connectives.match_And_prop (nat.le b n)
                                   (logic.eq nat.nat (g b) a)
                                   (connectives.ex nat.nat
                                    (λ (p : sttfa.etap (sttfa.p nat.nat)),
                                       connectives.And (nat.le p n)
                                       (logic.eq nat.nat (f (g p)) i)))
                                   (λ (lebn : sttfa.eps (nat.le b n)),
                                      λ
                                        (
                                        gb : sttfa.eps
                                             (logic.eq nat.nat (g b) a)
                                        ),
                                        connectives.ex_intro nat.nat
                                        (λ
                                           (x : sttfa.etap (sttfa.p nat.nat)),
                                           connectives.And (nat.le x n)
                                           (logic.eq nat.nat (f (g x)) i))
                                        b
                                        (connectives.conj (nat.le b n)
                                         (logic.eq nat.nat (f (g b)) i) lebn
                                         (logic.rewrite_r nat.nat a
                                          (λ
                                             (
                                             __ : sttfa.etap
                                                  (sttfa.p nat.nat)
                                             ), logic.eq nat.nat (f __) i)
                                          (logic.rewrite_r nat.nat i
                                           (λ
                                              (
                                              __ : sttfa.etap
                                                   (sttfa.p nat.nat)
                                              ), logic.eq nat.nat __ i)
                                           (logic.refl nat.nat i) (f a) ga)
                                          (g b) gb)))
                                   _clearme0)
                              (bijg a lean))
                         _clearme)
                    (bijf i lein);
symbol bijn_transpose
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall nat.nat
        (λ (i : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (j : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.le i n)
              (sttfa.impl (nat.le j n)
               (bijn (transpose i j) n))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        λ (i : sttfa.etap (sttfa.p nat.nat)),
          λ (j : sttfa.etap (sttfa.p nat.nat)),
            λ (lein : sttfa.eps (nat.le i n)),
              λ (lejn : sttfa.eps (nat.le j n)),
                λ (a : sttfa.etap (sttfa.p nat.nat)),
                  λ (lean : sttfa.eps (nat.le a n)),
                    connectives.match_Or_prop
                    (logic.eq bool.bool (nat.eqb a i) bool.true)
                    (logic.eq bool.bool (nat.eqb a i) bool.false)
                    (connectives.ex nat.nat
                     (λ (p : sttfa.etap (sttfa.p nat.nat)),
                        connectives.And (nat.le p n)
                        (logic.eq nat.nat (transpose i j p) a)))
                    (λ
                       (
                       Hi : sttfa.eps
                            (logic.eq bool.bool (nat.eqb a i) bool.true)
                       ),
                       connectives.ex_intro nat.nat
                       (λ (x : sttfa.etap (sttfa.p nat.nat)),
                          connectives.And (nat.le x n)
                          (logic.eq nat.nat (transpose i j x) a))
                       j
                       (connectives.conj (nat.le j n)
                        (logic.eq nat.nat (transpose i j j) a)
                        lejn
                        (logic.eq_ind_r nat.nat i
                         (λ (x : sttfa.etap (sttfa.p nat.nat)),
                            logic.eq nat.nat x a)
                         (logic.sym_eq nat.nat a i
                          (nat.eqb_true_to_eq a i Hi))
                         (transpose i j j)
                         (transpose_i_j_j i j))))
                    (λ
                       (
                       Hi : sttfa.eps
                            (logic.eq bool.bool (nat.eqb a i) bool.false)
                       ),
                       connectives.match_Or_prop
                       (logic.eq bool.bool (nat.eqb a j) bool.true)
                       (logic.eq bool.bool (nat.eqb a j) bool.false)
                       (connectives.ex nat.nat
                        (λ (p : sttfa.etap (sttfa.p nat.nat)),
                           connectives.And (nat.le p n)
                           (logic.eq nat.nat (transpose i j p) a)))
                       (λ
                          (
                          Hj : sttfa.eps
                               (logic.eq bool.bool (nat.eqb a j) bool.true)
                          ),
                          connectives.ex_intro nat.nat
                          (λ (x : sttfa.etap (sttfa.p nat.nat)),
                             connectives.And (nat.le x n)
                             (logic.eq nat.nat (transpose i j x)
                              a))
                          i
                          (connectives.conj (nat.le i n)
                           (logic.eq nat.nat (transpose i j i) a)
                           lein
                           (logic.eq_ind_r nat.nat j
                            (λ (x : sttfa.etap (sttfa.p nat.nat)),
                               logic.eq nat.nat x a)
                            (logic.sym_eq nat.nat a j
                             (nat.eqb_true_to_eq a j Hj))
                            (transpose i j i)
                            (transpose_i_j_i i j))))
                       (λ
                          (
                          Hj : sttfa.eps
                               (logic.eq bool.bool (nat.eqb a j) bool.false)
                          ),
                          connectives.ex_intro nat.nat
                          (λ (x : sttfa.etap (sttfa.p nat.nat)),
                             connectives.And (nat.le x n)
                             (logic.eq nat.nat (transpose i j x)
                              a))
                          a
                          (connectives.conj (nat.le a n)
                           (logic.eq nat.nat (transpose i j a) a)
                           lean
                           (logic.eq_ind_r bool.bool bool.false
                            (λ (x : sttfa.etap (sttfa.p bool.bool)),
                               logic.eq nat.nat
                               (bool.match_bool_type nat.nat j
                                (bool.match_bool_type nat.nat i a
                                 (nat.eqb a j))
                                x)
                               a)
                            (logic.eq_ind_r bool.bool bool.false
                             (λ (x : sttfa.etap (sttfa.p bool.bool)),
                                logic.eq nat.nat
                                (bool.match_bool_type nat.nat j
                                 (bool.match_bool_type nat.nat i a x)
                                 bool.false)
                                a)
                             (bool.eq_match_bool_type_false nat.nat i a
                              (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                 logic.eq nat.nat
                                 (bool.match_bool_type nat.nat j
                                  (bool.match_bool_type nat.nat i a
                                   bool.false)
                                  bool.false)
                                 y)
                              (bool.eq_match_bool_type_false nat.nat j
                               (bool.match_bool_type nat.nat i a bool.false)
                               (λ (y : sttfa.etap (sttfa.p nat.nat)),
                                  logic.eq nat.nat
                                  (bool.match_bool_type nat.nat j
                                   (bool.match_bool_type nat.nat i a
                                    bool.false)
                                   bool.false)
                                  y)
                               (logic.refl nat.nat
                                (bool.match_bool_type nat.nat j
                                 (bool.match_bool_type nat.nat i a bool.false)
                                 bool.false))))
                             (nat.eqb a j) Hj)
                            (nat.eqb a i) Hi)))
                       (bool.true_or_false (nat.eqb a j)))
                    (bool.true_or_false (nat.eqb a i));
symbol permut_to_bijn
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        sttfa.forall (sttfa.arrow nat.nat nat.nat)
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           sttfa.impl (permut f n) (bijn f n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        nat.nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall (sttfa.arrow nat.nat nat.nat)
           (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
              sttfa.impl (permut f _x_365)
              (bijn f _x_365)))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ
             (
             _clearme : sttfa.eps
                        (connectives.And
                         (sttfa.forall nat.nat
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl (nat.le i nat.O) (nat.le (f i) nat.O)))
                         (sttfa.forall nat.nat
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.forall nat.nat
                             (λ (j : sttfa.etap (sttfa.p nat.nat)),
                                sttfa.impl (nat.le i nat.O)
                                (sttfa.impl (nat.le j nat.O)
                                 (sttfa.impl (logic.eq nat.nat (f i) (f j))
                                  (logic.eq nat.nat i j)))))))
             ),
             connectives.match_And_prop
             (sttfa.forall nat.nat
              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.le i nat.O) (nat.le (f i) nat.O)))
             (sttfa.forall nat.nat
              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.forall nat.nat
                 (λ (j : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.impl (nat.le i nat.O)
                    (sttfa.impl (nat.le j nat.O)
                     (sttfa.impl (logic.eq nat.nat (f i) (f j))
                      (logic.eq nat.nat i j))))))
             (sttfa.forall nat.nat
              (λ (m : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (nat.le m nat.O)
                 (connectives.ex nat.nat
                  (λ (p : sttfa.etap (sttfa.p nat.nat)),
                     connectives.And (nat.le p nat.O)
                     (logic.eq nat.nat (f p) m)))))
             (λ
                (
                H : sttfa.eps
                    (sttfa.forall nat.nat
                     (λ (i : sttfa.etap (sttfa.p nat.nat)),
                        sttfa.impl (nat.le i nat.O) (nat.le (f i) nat.O)))
                ),
                λ
                  (
                  H1 : sttfa.eps
                       (sttfa.forall nat.nat
                        (λ (i : sttfa.etap (sttfa.p nat.nat)),
                           sttfa.forall nat.nat
                           (λ (j : sttfa.etap (sttfa.p nat.nat)),
                              sttfa.impl (nat.le i nat.O)
                              (sttfa.impl (nat.le j nat.O)
                               (sttfa.impl (logic.eq nat.nat (f i) (f j))
                                (logic.eq nat.nat i j))))))
                  ),
                  λ (m : sttfa.etap (sttfa.p nat.nat)),
                    λ (lem0 : sttfa.eps (nat.le m nat.O)),
                      connectives.ex_intro nat.nat
                      (λ (x : sttfa.etap (sttfa.p nat.nat)),
                         connectives.And (nat.le x nat.O)
                         (logic.eq nat.nat (f x) m))
                      nat.O
                      (connectives.conj (nat.le nat.O nat.O)
                       (logic.eq nat.nat (f nat.O) m) (nat.le_O_n nat.O)
                       (nat.le_n_O_elim m lem0 (logic.eq nat.nat (f nat.O))
                        (logic.sym_eq nat.nat nat.O (f nat.O)
                         (nat.le_n_O_to_eq (f nat.O)
                          (H nat.O (nat.le_O_n nat.O)))))))
             _clearme)
        (λ (m : sttfa.etap (sttfa.p nat.nat)),
           λ
             (
             Hind : sttfa.eps
                    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
                     (λ
                        (
                        f : sttfa.etap
                            (sttfa.p (sttfa.arrow nat.nat nat.nat))
                        ),
                        sttfa.impl (permut f m)
                        (bijn f m)))
             ),
             λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
               λ (permf : sttfa.eps (permut f (nat.S m))),
                 eq_to_bijn
                 (λ (p : sttfa.etap (sttfa.p nat.nat)),
                    transpose (f (nat.S m)) (nat.S m)
                    (transpose (f (nat.S m)) (nat.S m) (f p)))
                 f (nat.S m)
                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                    λ (lei : sttfa.eps (nat.le i (nat.S m))),
                      transpose_transpose (f (nat.S m)) (nat.S m)
                      (f i))
                 (bijn_fg
                  (transpose (f (nat.S m)) (nat.S m))
                  (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                     transpose (f (nat.S m)) (nat.S m) (f __))
                  (nat.S m)
                  (connectives.match_And_prop
                   (sttfa.forall nat.nat
                    (λ (i : sttfa.etap (sttfa.p nat.nat)),
                       sttfa.impl (nat.le i (nat.S m))
                       (nat.le (f i) (nat.S m))))
                   (injn f (nat.S m))
                   (bijn
                    (transpose (f (nat.S m)) (nat.S m)) (
                    nat.S m))
                   (λ
                      (
                      lef : sttfa.eps
                            (sttfa.forall nat.nat
                             (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                sttfa.impl (nat.le i (nat.S m))
                                (nat.le (f i) (nat.S m))))
                      ),
                      λ (__ : sttfa.eps (injn f (nat.S m))),
                        bijn_transpose (nat.S m) (f (nat.S m))
                        (nat.S m) (lef (nat.S m) (nat.le_n (nat.S m)))
                        (nat.le_n (nat.S m)))
                   permf)
                  (bijn_n_Sn
                   (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                      transpose (f (nat.S m)) (nat.S m) (f __))
                   m
                   (Hind
                    (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                       transpose (f (nat.S m)) (nat.S m) (f __))
                    (permut_S_to_permut_transpose f m permf))
                   (logic.eq_ind_r bool.bool bool.true
                    (λ (x : sttfa.etap (sttfa.p bool.bool)),
                       logic.eq nat.nat
                       (bool.match_bool_type nat.nat (nat.S m)
                        (bool.match_bool_type nat.nat (f (nat.S m))
                         (f (nat.S m)) (nat.eqb (f (nat.S m)) (nat.S m)))
                        x)
                       (nat.S m))
                    (bool.eq_match_bool_type_true nat.nat (nat.S m)
                     (bool.match_bool_type nat.nat (f (nat.S m))
                      (f (nat.S m)) (nat.eqb (f (nat.S m)) (nat.S m)))
                     (λ (y : sttfa.etap (sttfa.p nat.nat)),
                        logic.eq nat.nat
                        (bool.match_bool_type nat.nat (nat.S m)
                         (bool.match_bool_type nat.nat (f (nat.S m))
                          (f (nat.S m)) (nat.eqb (f (nat.S m)) (nat.S m)))
                         bool.true)
                        y)
                     (logic.refl nat.nat
                      (bool.match_bool_type nat.nat (nat.S m)
                       (bool.match_bool_type nat.nat (f (nat.S m))
                        (f (nat.S m)) (nat.eqb (f (nat.S m)) (nat.S m)))
                       bool.true)))
                    (nat.eqb (f (nat.S m)) (f (nat.S m)))
                    (nat.eqb_n_n (f (nat.S m)))))))
        n;
constant symbol invert_permut
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow nat.nat
      (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
       (sttfa.arrow nat.nat nat.nat))));
constant symbol invert_permut_body
  : sttfa.etap
    (sttfa.p
     (sttfa.arrow nat.nat
      (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
       (sttfa.arrow nat.nat nat.nat))));
constant symbol axiom_invert_permut
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut n)
        (nat.filter_nat_type
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow nat.nat nat.nat))
         invert_permut_body n)));
symbol eq_invert_permut
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut n)
        (nat.filter_nat_type
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow nat.nat nat.nat))
         invert_permut_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut n)
        (nat.filter_nat_type
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow nat.nat nat.nat))
         invert_permut_body n)
        (axiom_invert_permut n);
symbol sym_eq_invert_permut
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (nat.filter_nat_type
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow nat.nat nat.nat))
         invert_permut_body n)
        (invert_permut n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.sym_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut n)
        (nat.filter_nat_type
         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
          (sttfa.arrow nat.nat nat.nat))
         invert_permut_body n)
        (eq_invert_permut n);
constant symbol axiom_invert_permut_body_O
  : sttfa.eps
    (connectives.equal
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat) (sttfa.arrow nat.nat nat.nat))
     (invert_permut_body nat.O)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          bool.match_bool_type nat.nat nat.O nat.O (nat.eqb m (f nat.O))));
symbol eq_invert_permut_body_O
  : sttfa.eps
    (leibniz.leibniz
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat) (sttfa.arrow nat.nat nat.nat))
     (invert_permut_body nat.O)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          bool.match_bool_type nat.nat nat.O nat.O (nat.eqb m (f nat.O))))
  ≔ connectives.equal_leibniz
      (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
       (sttfa.arrow nat.nat nat.nat))
      (invert_permut_body nat.O)
      (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
         λ (m : sttfa.etap (sttfa.p nat.nat)),
           bool.match_bool_type nat.nat nat.O nat.O (nat.eqb m (f nat.O)))
      axiom_invert_permut_body_O;
symbol sym_eq_invert_permut_body_O
  : sttfa.eps
    (leibniz.leibniz
     (sttfa.arrow (sttfa.arrow nat.nat nat.nat) (sttfa.arrow nat.nat nat.nat))
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (m : sttfa.etap (sttfa.p nat.nat)),
          bool.match_bool_type nat.nat nat.O nat.O (nat.eqb m (f nat.O)))
     (invert_permut_body nat.O))
  ≔ leibniz.sym_leibniz
      (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
       (sttfa.arrow nat.nat nat.nat))
      (invert_permut_body nat.O)
      (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
         λ (m : sttfa.etap (sttfa.p nat.nat)),
           bool.match_bool_type nat.nat nat.O nat.O (nat.eqb m (f nat.O)))
      eq_invert_permut_body_O;
constant symbol axiom_invert_permut_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut_body (nat.S n))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ (m : sttfa.etap (sttfa.p nat.nat)),
             bool.match_bool_type nat.nat (nat.S n)
             (invert_permut n f m) (nat.eqb m (f (nat.S n))))));
symbol eq_invert_permut_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut_body (nat.S n))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ (m : sttfa.etap (sttfa.p nat.nat)),
             bool.match_bool_type nat.nat (nat.S n)
             (invert_permut n f m) (nat.eqb m (f (nat.S n))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        connectives.equal_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut_body (nat.S n))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ (m : sttfa.etap (sttfa.p nat.nat)),
             bool.match_bool_type nat.nat (nat.S n)
             (invert_permut n f m) (nat.eqb m (f (nat.S n))))
        (axiom_invert_permut_body_S n);
symbol sym_eq_invert_permut_body_S
  : sttfa.eps
    (sttfa.forall nat.nat
     (λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ (m : sttfa.etap (sttfa.p nat.nat)),
             bool.match_bool_type nat.nat (nat.S n)
             (invert_permut n f m) (nat.eqb m (f (nat.S n))))
        (invert_permut_body (nat.S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat.nat)),
        leibniz.sym_leibniz
        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
         (sttfa.arrow nat.nat nat.nat))
        (invert_permut_body (nat.S n))
        (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
           λ (m : sttfa.etap (sttfa.p nat.nat)),
             bool.match_bool_type nat.nat (nat.S n)
             (invert_permut n f m) (nat.eqb m (f (nat.S n))))
        (eq_invert_permut_body_S n);
symbol invert_permut_f
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (m : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.le m n)
              (sttfa.impl (injn f n)
               (logic.eq nat.nat (invert_permut n f (f m)) m))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (m : sttfa.etap (sttfa.p nat.nat)),
            λ (lenm : sttfa.eps (nat.le m n)),
              nat.le_ind m
              (λ (x_417 : sttfa.etap (sttfa.p nat.nat)),
                 sttfa.impl (injn f x_417)
                 (logic.eq nat.nat (invert_permut x_417 f (f m))
                  m))
              (nat.match_nat_prop
               (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.impl (injn f __)
                  (logic.eq nat.nat (invert_permut __ f (f __))
                   __))
               (sym_eq_invert_permut nat.O
                (λ
                   (
                   y : sttfa.etap
                       (sttfa.p
                        (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                         (sttfa.arrow nat.nat nat.nat)))
                   ),
                   sttfa.impl (injn f nat.O)
                   (logic.eq nat.nat (y f (f nat.O)) nat.O))
                (nat.sym_eq_filter_nat_type_O
                 (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                  (sttfa.arrow nat.nat nat.nat))
                 invert_permut_body
                 (λ
                    (
                    y : sttfa.etap
                        (sttfa.p
                         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                          (sttfa.arrow nat.nat nat.nat)))
                    ),
                    sttfa.impl (injn f nat.O)
                    (logic.eq nat.nat (y f (f nat.O)) nat.O))
                 (sym_eq_invert_permut_body_O
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                           (sttfa.arrow nat.nat nat.nat)))
                     ),
                     sttfa.impl (injn f nat.O)
                     (logic.eq nat.nat (y f (f nat.O)) nat.O))
                  (logic.eq_ind_r bool.bool bool.true
                   (λ (x : sttfa.etap (sttfa.p bool.bool)),
                      sttfa.impl
                      (sttfa.forall nat.nat
                       (λ (i : sttfa.etap (sttfa.p nat.nat)),
                          sttfa.forall nat.nat
                          (λ (j : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl (nat.le i nat.O)
                             (sttfa.impl (nat.le j nat.O)
                              (sttfa.impl (logic.eq nat.nat (f i) (f j))
                               (logic.eq nat.nat i j))))))
                      (logic.eq nat.nat
                       (bool.match_bool_type nat.nat nat.O nat.O x) nat.O))
                   (λ
                      (
                      auto : sttfa.eps
                             (sttfa.forall nat.nat
                              (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                 sttfa.forall nat.nat
                                 (λ (j : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.le i nat.O)
                                    (sttfa.impl (nat.le j nat.O)
                                     (sttfa.impl
                                      (logic.eq nat.nat (f i) (f j))
                                      (logic.eq nat.nat i j))))))
                      ),
                      bool.eq_match_bool_type_true nat.nat nat.O nat.O
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         logic.eq nat.nat
                         (bool.match_bool_type nat.nat nat.O nat.O bool.true)
                         y)
                      (logic.refl nat.nat
                       (bool.match_bool_type nat.nat nat.O nat.O bool.true)))
                   (nat.eqb (f nat.O) (f nat.O)) (nat.eqb_n_n (f nat.O))))))
               (λ (a : sttfa.etap (sttfa.p nat.nat)),
                  sym_eq_invert_permut (nat.S a)
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                           (sttfa.arrow nat.nat nat.nat)))
                     ),
                     sttfa.impl (injn f (nat.S a))
                     (logic.eq nat.nat (y f (f (nat.S a))) (nat.S a)))
                  (nat.sym_eq_filter_nat_type_S
                   (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                    (sttfa.arrow nat.nat nat.nat))
                   invert_permut_body a
                   (λ
                      (
                      y : sttfa.etap
                          (sttfa.p
                           (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                            (sttfa.arrow nat.nat nat.nat)))
                      ),
                      sttfa.impl (injn f (nat.S a))
                      (logic.eq nat.nat (y f (f (nat.S a))) (nat.S a)))
                   (sym_eq_invert_permut_body_S a
                    (λ
                       (
                       y : sttfa.etap
                           (sttfa.p
                            (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                             (sttfa.arrow nat.nat nat.nat)))
                       ),
                       sttfa.impl (injn f (nat.S a))
                       (logic.eq nat.nat (y f (f (nat.S a))) (nat.S a)))
                    (logic.eq_ind_r bool.bool bool.true
                     (λ (x : sttfa.etap (sttfa.p bool.bool)),
                        sttfa.impl
                        (sttfa.forall nat.nat
                         (λ (i : sttfa.etap (sttfa.p nat.nat)),
                            sttfa.forall nat.nat
                            (λ (j : sttfa.etap (sttfa.p nat.nat)),
                               sttfa.impl (nat.le i (nat.S a))
                               (sttfa.impl (nat.le j (nat.S a))
                                (sttfa.impl (logic.eq nat.nat (f i) (f j))
                                 (logic.eq nat.nat i j))))))
                        (logic.eq nat.nat
                         (bool.match_bool_type nat.nat (nat.S a)
                          (invert_permut a f (f (nat.S a))) x)
                         (nat.S a)))
                     (λ
                        (
                        auto : sttfa.eps
                               (sttfa.forall nat.nat
                                (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                   sttfa.forall nat.nat
                                   (λ (j : sttfa.etap (sttfa.p nat.nat)),
                                      sttfa.impl (nat.le i (nat.S a))
                                      (sttfa.impl (nat.le j (nat.S a))
                                       (sttfa.impl
                                        (logic.eq nat.nat (f i) (f j))
                                        (logic.eq nat.nat i j))))))
                        ),
                        bool.eq_match_bool_type_true nat.nat (nat.S a)
                        (invert_permut a f (f (nat.S a)))
                        (λ (y : sttfa.etap (sttfa.p nat.nat)),
                           logic.eq nat.nat
                           (bool.match_bool_type nat.nat (nat.S a)
                            (invert_permut a f (f (nat.S a)))
                            bool.true)
                           y)
                        (logic.refl nat.nat
                         (bool.match_bool_type nat.nat (nat.S a)
                          (invert_permut a f (f (nat.S a)))
                          bool.true)))
                     (nat.eqb (f (nat.S a)) (f (nat.S a)))
                     (nat.eqb_n_n (f (nat.S a)))))))
               m)
              (λ (m0 : sttfa.etap (sttfa.p nat.nat)),
                 sym_eq_invert_permut (nat.S m0)
                 (λ
                    (
                    y : sttfa.etap
                        (sttfa.p
                         (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                          (sttfa.arrow nat.nat nat.nat)))
                    ),
                    sttfa.impl (nat.le m m0)
                    (sttfa.impl
                     (sttfa.impl (injn f m0)
                      (logic.eq nat.nat
                       (invert_permut m0 f (f m)) m))
                     (sttfa.impl (injn f (nat.S m0))
                      (logic.eq nat.nat (y f (f m)) m))))
                 (nat.sym_eq_filter_nat_type_S
                  (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                   (sttfa.arrow nat.nat nat.nat))
                  invert_permut_body m0
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                           (sttfa.arrow nat.nat nat.nat)))
                     ),
                     sttfa.impl (nat.le m m0)
                     (sttfa.impl
                      (sttfa.impl (injn f m0)
                       (logic.eq nat.nat
                        (invert_permut m0 f (f m)) m))
                      (sttfa.impl (injn f (nat.S m0))
                       (logic.eq nat.nat (y f (f m)) m))))
                  (sym_eq_invert_permut_body_S m0
                   (λ
                      (
                      y : sttfa.etap
                          (sttfa.p
                           (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                            (sttfa.arrow nat.nat nat.nat)))
                      ),
                      sttfa.impl (nat.le m m0)
                      (sttfa.impl
                       (sttfa.impl (injn f m0)
                        (logic.eq nat.nat
                         (invert_permut m0 f (f m)) m))
                       (sttfa.impl (injn f (nat.S m0))
                        (logic.eq nat.nat (y f (f m)) m))))
                   (λ (lem : sttfa.eps (nat.le m m0)),
                      λ
                        (
                        H : sttfa.eps
                            (sttfa.impl (injn f m0)
                             (logic.eq nat.nat
                              (invert_permut m0 f (f m)) m))
                        ),
                        λ (H1 : sttfa.eps (injn f (nat.S m0))),
                          logic.eq_ind_r bool.bool bool.false
                          (λ (x : sttfa.etap (sttfa.p bool.bool)),
                             logic.eq nat.nat
                             (bool.match_bool_type nat.nat (nat.S m0)
                              (invert_permut m0 f (f m)) x)
                             m)
                          (bool.sym_eq_match_bool_type_false nat.nat
                           (nat.S m0) (invert_permut m0 f (f m))
                           (λ (y : sttfa.etap (sttfa.p nat.nat)),
                              logic.eq nat.nat y m)
                           (H (injn_Sn_n f m0 H1)))
                          (nat.eqb (f m) (f (nat.S m0)))
                          (nat.not_eq_to_eqb_false (f m) (f (nat.S m0))
                           (connectives.nmk
                            (logic.eq nat.nat (f m) (f (nat.S m0)))
                            (λ
                               (
                               eqf : sttfa.eps
                                     (logic.eq nat.nat (f m) (f (nat.S m0)))
                               ),
                               logic.absurd (logic.eq nat.nat m (nat.S m0))
                               (H1 m (nat.S m0) (nat.le_S m m0 lem)
                                (nat.le_n (nat.S m0))
                                (logic.rewrite_l nat.nat (f m)
                                 (λ (__ : sttfa.etap (sttfa.p nat.nat)),
                                    logic.eq nat.nat (f m) __)
                                 (logic.refl nat.nat (f m)) (f (nat.S m0))
                                 eqf))
                               (nat.lt_to_not_eq m (nat.S m0)
                                (nat.le_S_S m m0 lem)))))))))
              n lenm;
symbol let_clause_1063
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (permut f n)
           (sttfa.forall nat.nat
            (λ (i : sttfa.etap (sttfa.p nat.nat)),
               sttfa.forall nat.nat
               (λ (j : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.impl (nat.le i n)
                  (sttfa.impl (nat.le j n)
                   (sttfa.forall nat.nat
                    (λ (a : sttfa.etap (sttfa.p nat.nat)),
                       sttfa.impl
                       (connectives.And (nat.le a n)
                        (logic.eq nat.nat (f a) i))
                       (sttfa.impl (nat.le a n)
                        (sttfa.impl (logic.eq nat.nat (f a) i)
                         (sttfa.forall nat.nat
                          (λ (b : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl
                             (connectives.And (nat.le b n)
                              (logic.eq nat.nat (f b) j))
                             (sttfa.impl (nat.le b n)
                              (sttfa.impl (logic.eq nat.nat (f b) j)
                               (sttfa.impl
                                (sttfa.forall nat.nat
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.le i0 n)
                                    (nat.le (f i0) n)))
                                (sttfa.impl (injn f n)
                                 (sttfa.impl (logic.eq nat.nat a b)
                                  (logic.eq nat.nat (f a) j)))))))))))))))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (permf : sttfa.eps (permut f n)),
            λ (i : sttfa.etap (sttfa.p nat.nat)),
              λ (j : sttfa.etap (sttfa.p nat.nat)),
                λ (lein : sttfa.eps (nat.le i n)),
                  λ (lejn : sttfa.eps (nat.le j n)),
                    λ (a : sttfa.etap (sttfa.p nat.nat)),
                      λ
                        (
                        _clearme : sttfa.eps
                                   (connectives.And (nat.le a n)
                                    (logic.eq nat.nat (f a) i))
                        ),
                        λ (lean : sttfa.eps (nat.le a n)),
                          λ (fa : sttfa.eps (logic.eq nat.nat (f a) i)),
                            λ (b : sttfa.etap (sttfa.p nat.nat)),
                              λ
                                (
                                _clearme0 : sttfa.eps
                                            (connectives.And (nat.le b n)
                                             (logic.eq nat.nat (f b) j))
                                ),
                                λ (lebn : sttfa.eps (nat.le b n)),
                                  λ
                                    (
                                    fb : sttfa.eps (logic.eq nat.nat (f b) j)
                                    ),
                                    λ
                                      (
                                      __ : sttfa.eps
                                           (sttfa.forall nat.nat
                                            (λ
                                               (
                                               i0 : sttfa.etap
                                                    (sttfa.p nat.nat)
                                               ),
                                               sttfa.impl (nat.le i0 n)
                                               (nat.le (f i0) n)))
                                      ),
                                      λ
                                        (
                                        injf : sttfa.eps
                                               (injn f n)
                                        ),
                                        λ
                                          (
                                          auto : sttfa.eps
                                                 (logic.eq nat.nat a b)
                                          ),
                                          logic.rewrite_r nat.nat b
                                          (λ
                                             (
                                             __1 : sttfa.etap
                                                   (sttfa.p nat.nat)
                                             ), logic.eq nat.nat (f __1) j)
                                          fb a auto;
symbol let_clause_1068
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (permut f n)
           (sttfa.forall nat.nat
            (λ (i : sttfa.etap (sttfa.p nat.nat)),
               sttfa.forall nat.nat
               (λ (j : sttfa.etap (sttfa.p nat.nat)),
                  sttfa.impl (nat.le i n)
                  (sttfa.impl (nat.le j n)
                   (sttfa.forall nat.nat
                    (λ (a : sttfa.etap (sttfa.p nat.nat)),
                       sttfa.impl
                       (connectives.And (nat.le a n)
                        (logic.eq nat.nat (f a) i))
                       (sttfa.impl (nat.le a n)
                        (sttfa.impl (logic.eq nat.nat (f a) i)
                         (sttfa.forall nat.nat
                          (λ (b : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl
                             (connectives.And (nat.le b n)
                              (logic.eq nat.nat (f b) j))
                             (sttfa.impl (nat.le b n)
                              (sttfa.impl (logic.eq nat.nat (f b) j)
                               (sttfa.impl
                                (sttfa.forall nat.nat
                                 (λ (i0 : sttfa.etap (sttfa.p nat.nat)),
                                    sttfa.impl (nat.le i0 n)
                                    (nat.le (f i0) n)))
                                (sttfa.impl (injn f n)
                                 (sttfa.impl (logic.eq nat.nat a b)
                                  (logic.eq nat.nat (f a) i)))))))))))))))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (permf : sttfa.eps (permut f n)),
            λ (i : sttfa.etap (sttfa.p nat.nat)),
              λ (j : sttfa.etap (sttfa.p nat.nat)),
                λ (lein : sttfa.eps (nat.le i n)),
                  λ (lejn : sttfa.eps (nat.le j n)),
                    λ (a : sttfa.etap (sttfa.p nat.nat)),
                      λ
                        (
                        _clearme : sttfa.eps
                                   (connectives.And (nat.le a n)
                                    (logic.eq nat.nat (f a) i))
                        ),
                        λ (lean : sttfa.eps (nat.le a n)),
                          λ (fa : sttfa.eps (logic.eq nat.nat (f a) i)),
                            λ (b : sttfa.etap (sttfa.p nat.nat)),
                              λ
                                (
                                _clearme0 : sttfa.eps
                                            (connectives.And (nat.le b n)
                                             (logic.eq nat.nat (f b) j))
                                ),
                                λ (lebn : sttfa.eps (nat.le b n)),
                                  λ
                                    (
                                    fb : sttfa.eps (logic.eq nat.nat (f b) j)
                                    ),
                                    λ
                                      (
                                      __ : sttfa.eps
                                           (sttfa.forall nat.nat
                                            (λ
                                               (
                                               i0 : sttfa.etap
                                                    (sttfa.p nat.nat)
                                               ),
                                               sttfa.impl (nat.le i0 n)
                                               (nat.le (f i0) n)))
                                      ),
                                      λ
                                        (
                                        injf : sttfa.eps
                                               (injn f n)
                                        ),
                                        λ
                                          (
                                          auto : sttfa.eps
                                                 (logic.eq nat.nat a b)
                                          ),
                                          logic.rewrite_l nat.nat j
                                          (λ
                                             (
                                             __1 : sttfa.etap
                                                   (sttfa.p nat.nat)
                                             ), logic.eq nat.nat (f a) __1)
                                          (let_clause_1063 f n
                                           permf i j lein lejn a _clearme
                                           lean fa b _clearme0 lebn fb __
                                           injf auto)
                                          i
                                          (logic.rewrite_l nat.nat (f a)
                                           (λ
                                              (
                                              __1 : sttfa.etap
                                                    (sttfa.p nat.nat)
                                              ), logic.eq nat.nat __1 i)
                                           fa j
                                           (let_clause_1063 f n
                                            permf i j lein lejn a _clearme
                                            lean fa b _clearme0 lebn fb __
                                            injf auto));
symbol injective_invert_permut
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (permut f n)
           (injn (invert_permut n f) n))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (permf : sttfa.eps (permut f n)),
            λ (i : sttfa.etap (sttfa.p nat.nat)),
              λ (j : sttfa.etap (sttfa.p nat.nat)),
                λ (lein : sttfa.eps (nat.le i n)),
                  λ (lejn : sttfa.eps (nat.le j n)),
                    connectives.match_ex_prop nat.nat
                    (λ (p : sttfa.etap (sttfa.p nat.nat)),
                       connectives.And (nat.le p n)
                       (logic.eq nat.nat (f p) i))
                    (sttfa.impl
                     (logic.eq nat.nat (invert_permut n f i)
                      (invert_permut n f j))
                     (logic.eq nat.nat i j))
                    (λ (a : sttfa.etap (sttfa.p nat.nat)),
                       λ
                         (
                         _clearme : sttfa.eps
                                    (connectives.And (nat.le a n)
                                     (logic.eq nat.nat (f a) i))
                         ),
                         connectives.match_And_prop (nat.le a n)
                         (logic.eq nat.nat (f a) i)
                         (sttfa.impl
                          (logic.eq nat.nat (invert_permut n f i)
                           (invert_permut n f j))
                          (logic.eq nat.nat i j))
                         (λ (lean : sttfa.eps (nat.le a n)),
                            λ (fa : sttfa.eps (logic.eq nat.nat (f a) i)),
                              connectives.match_ex_prop nat.nat
                              (λ (p : sttfa.etap (sttfa.p nat.nat)),
                                 connectives.And (nat.le p n)
                                 (logic.eq nat.nat (f p) j))
                              (sttfa.impl
                               (logic.eq nat.nat
                                (invert_permut n f i)
                                (invert_permut n f j))
                               (logic.eq nat.nat i j))
                              (λ (b : sttfa.etap (sttfa.p nat.nat)),
                                 λ
                                   (
                                   _clearme0 : sttfa.eps
                                               (connectives.And (nat.le b n)
                                                (logic.eq nat.nat (f b) j))
                                   ),
                                   connectives.match_And_prop (nat.le b n)
                                   (logic.eq nat.nat (f b) j)
                                   (sttfa.impl
                                    (logic.eq nat.nat
                                     (invert_permut n f i)
                                     (invert_permut n f j))
                                    (logic.eq nat.nat i j))
                                   (λ (lebn : sttfa.eps (nat.le b n)),
                                      λ
                                        (
                                        fb : sttfa.eps
                                             (logic.eq nat.nat (f b) j)
                                        ),
                                        connectives.match_And_prop
                                        (sttfa.forall nat.nat
                                         (λ
                                            (
                                            i1 : sttfa.etap (sttfa.p nat.nat)
                                            ),
                                            sttfa.impl (nat.le i1 n)
                                            (nat.le (f i1) n)))
                                        (injn f n)
                                        (sttfa.impl
                                         (logic.eq nat.nat
                                          (invert_permut n f i)
                                          (invert_permut n f j))
                                         (logic.eq nat.nat i j))
                                        (λ
                                           (
                                           __ : sttfa.eps
                                                (sttfa.forall nat.nat
                                                 (λ
                                                    (
                                                    i0 : sttfa.etap
                                                         (sttfa.p nat.nat)
                                                    ),
                                                    sttfa.impl (nat.le i0 n)
                                                    (nat.le (f i0) n)))
                                           ),
                                           λ
                                             (
                                             injf : sttfa.eps
                                                    (injn f n)
                                             ),
                                             logic.eq_ind nat.nat (f a)
                                             (λ
                                                (
                                                x_1 : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                ),
                                                sttfa.impl
                                                (logic.eq nat.nat
                                                 (invert_permut n
                                                  f x_1)
                                                 (invert_permut n
                                                  f j))
                                                (logic.eq nat.nat x_1 j))
                                             (logic.eq_ind nat.nat (f b)
                                              (λ
                                                 (
                                                 x_1 : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                 ),
                                                 sttfa.impl
                                                 (logic.eq nat.nat
                                                  (invert_permut
                                                   n f (f a))
                                                  (invert_permut
                                                   n f x_1))
                                                 (logic.eq nat.nat (f a) x_1))
                                              (logic.eq_ind_r nat.nat a
                                               (λ
                                                  (
                                                  x : sttfa.etap
                                                      (sttfa.p nat.nat)
                                                  ),
                                                  sttfa.impl
                                                  (logic.eq nat.nat x
                                                   (invert_permut
                                                    n f (f b)))
                                                  (logic.eq nat.nat (f a)
                                                   (f b)))
                                               (logic.eq_ind_r nat.nat b
                                                (λ
                                                   (
                                                   x : sttfa.etap
                                                       (sttfa.p nat.nat)
                                                   ),
                                                   sttfa.impl
                                                   (logic.eq nat.nat a x)
                                                   (logic.eq nat.nat (f a)
                                                    (f b)))
                                                (λ
                                                   (
                                                   auto : sttfa.eps
                                                          (logic.eq nat.nat a
                                                           b)
                                                   ),
                                                   logic.rewrite_r nat.nat i
                                                   (λ
                                                      (
                                                      __1 : sttfa.etap
                                                            (sttfa.p nat.nat)
                                                      ),
                                                      logic.eq nat.nat __1
                                                      (f b))
                                                   (logic.rewrite_l nat.nat a
                                                    (λ
                                                       (
                                                       __1 : sttfa.etap
                                                             (sttfa.p nat.nat)
                                                       ),
                                                       logic.eq nat.nat i
                                                       (f __1))
                                                    (logic.rewrite_r nat.nat
                                                     i
                                                     (λ
                                                        (
                                                        __1 : sttfa.etap
                                                              (sttfa.p
                                                               nat.nat)
                                                        ),
                                                        logic.eq nat.nat i
                                                        __1)
                                                     (logic.refl nat.nat i)
                                                     (f a)
                                                     (let_clause_1068
                                                      f n permf i j lein lejn
                                                      a _clearme lean fa b
                                                      _clearme0 lebn fb __
                                                      injf auto))
                                                    b auto)
                                                   (f a)
                                                   (let_clause_1068
                                                    f n permf i j lein lejn a
                                                    _clearme lean fa b
                                                    _clearme0 lebn fb __ injf
                                                    auto))
                                                (invert_permut n
                                                 f (f b))
                                                (invert_permut_f
                                                 f n b lebn injf))
                                               (invert_permut n f
                                                (f a))
                                               (invert_permut_f f
                                                n a lean injf))
                                              j fb)
                                             i fa)
                                        permf)
                                   _clearme0)
                              (permut_to_bijn n f permf j lejn))
                         _clearme)
                    (permut_to_bijn n f permf i lein);
symbol permut_invert_permut
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.impl (permut f n)
           (permut (invert_permut n f) n))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (permf : sttfa.eps (permut f n)),
            connectives.conj
            (sttfa.forall nat.nat
             (λ (x : sttfa.etap (sttfa.p nat.nat)),
                sttfa.impl (nat.le x n)
                (nat.le (invert_permut n f x) n)))
            (injn (invert_permut n f) n)
            (λ (i : sttfa.etap (sttfa.p nat.nat)),
               λ (lein : sttfa.eps (nat.le i n)),
                 nat.nat_ind
                 (λ (_x_365 : sttfa.etap (sttfa.p nat.nat)),
                    nat.le (invert_permut _x_365 f i) _x_365)
                 (sym_eq_invert_permut nat.O
                  (λ
                     (
                     y : sttfa.etap
                         (sttfa.p
                          (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                           (sttfa.arrow nat.nat nat.nat)))
                     ), nat.le (y f i) nat.O)
                  (nat.sym_eq_filter_nat_type_O
                   (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                    (sttfa.arrow nat.nat nat.nat))
                   invert_permut_body
                   (λ
                      (
                      y : sttfa.etap
                          (sttfa.p
                           (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                            (sttfa.arrow nat.nat nat.nat)))
                      ), nat.le (y f i) nat.O)
                   (sym_eq_invert_permut_body_O
                    (λ
                       (
                       y : sttfa.etap
                           (sttfa.p
                            (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                             (sttfa.arrow nat.nat nat.nat)))
                       ), nat.le (y f i) nat.O)
                    (bool.match_bool_prop
                     (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                        nat.le (bool.match_bool_type nat.nat nat.O nat.O __)
                        nat.O)
                     (bool.eq_match_bool_type_true nat.nat nat.O nat.O
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         nat.le
                         (bool.match_bool_type nat.nat nat.O nat.O bool.true)
                         y)
                      (nat.le_n
                       (bool.match_bool_type nat.nat nat.O nat.O bool.true)))
                     (bool.eq_match_bool_type_false nat.nat nat.O nat.O
                      (λ (y : sttfa.etap (sttfa.p nat.nat)),
                         nat.le
                         (bool.match_bool_type nat.nat nat.O nat.O bool.false)
                         y)
                      (nat.le_n
                       (bool.match_bool_type nat.nat nat.O nat.O bool.false)))
                     (nat.eqb i (f nat.O))))))
                 (λ (n1 : sttfa.etap (sttfa.p nat.nat)),
                    sym_eq_invert_permut (nat.S n1)
                    (λ
                       (
                       y : sttfa.etap
                           (sttfa.p
                            (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                             (sttfa.arrow nat.nat nat.nat)))
                       ),
                       sttfa.impl
                       (nat.le (invert_permut n1 f i) n1)
                       (nat.le (y f i) (nat.S n1)))
                    (nat.sym_eq_filter_nat_type_S
                     (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                      (sttfa.arrow nat.nat nat.nat))
                     invert_permut_body n1
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p
                             (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                              (sttfa.arrow nat.nat nat.nat)))
                        ),
                        sttfa.impl
                        (nat.le (invert_permut n1 f i) n1)
                        (nat.le (y f i) (nat.S n1)))
                     (sym_eq_invert_permut_body_S n1
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p
                              (sttfa.arrow (sttfa.arrow nat.nat nat.nat)
                               (sttfa.arrow nat.nat nat.nat)))
                         ),
                         sttfa.impl
                         (nat.le (invert_permut n1 f i) n1)
                         (nat.le (y f i) (nat.S n1)))
                      (λ
                         (
                         Hind : sttfa.eps
                                (nat.le (invert_permut n1 f i) n1)
                         ),
                         bool.match_bool_prop
                         (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                            nat.le
                            (bool.match_bool_type nat.nat (nat.S n1)
                             (invert_permut n1 f i) __)
                            (nat.S n1))
                         (bool.eq_match_bool_type_true nat.nat (nat.S n1)
                          (invert_permut n1 f i)
                          (λ (y : sttfa.etap (sttfa.p nat.nat)),
                             nat.le
                             (bool.match_bool_type nat.nat (nat.S n1)
                              (invert_permut n1 f i) bool.true)
                             y)
                          (nat.le_n
                           (bool.match_bool_type nat.nat (nat.S n1)
                            (invert_permut n1 f i) bool.true)))
                         (bool.sym_eq_match_bool_type_false nat.nat
                          (nat.S n1) (invert_permut n1 f i)
                          (λ (y : sttfa.etap (sttfa.p nat.nat)),
                             nat.le y (nat.S n1))
                          (nat.le_S (invert_permut n1 f i) n1
                           Hind))
                         (nat.eqb i (f (nat.S n1)))))))
                 n)
            (injective_invert_permut f n permf);
symbol f_invert_permut
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat.nat nat.nat)
     (λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        sttfa.forall nat.nat
        (λ (n : sttfa.etap (sttfa.p nat.nat)),
           sttfa.forall nat.nat
           (λ (m : sttfa.etap (sttfa.p nat.nat)),
              sttfa.impl (nat.le m n)
              (sttfa.impl (permut f n)
               (logic.eq nat.nat (f (invert_permut n f m)) m))))))
  ≔ λ (f : sttfa.etap (sttfa.p (sttfa.arrow nat.nat nat.nat))),
        λ (n : sttfa.etap (sttfa.p nat.nat)),
          λ (m : sttfa.etap (sttfa.p nat.nat)),
            λ (lemn : sttfa.eps (nat.le m n)),
              λ (permf : sttfa.eps (permut f n)),
                connectives.match_And_prop
                (sttfa.forall nat.nat
                 (λ (i : sttfa.etap (sttfa.p nat.nat)),
                    sttfa.impl (nat.le i n)
                    (nat.le (invert_permut n f i) n)))
                (injn (invert_permut n f) n)
                (logic.eq nat.nat (f (invert_permut n f m)) m)
                (λ
                   (
                   Hle : sttfa.eps
                         (sttfa.forall nat.nat
                          (λ (i : sttfa.etap (sttfa.p nat.nat)),
                             sttfa.impl (nat.le i n)
                             (nat.le (invert_permut n f i) n)))
                   ),
                   λ
                     (
                     Hinj : sttfa.eps
                            (injn (invert_permut n f)
                             n)
                     ),
                     connectives.match_And_prop
                     (sttfa.forall nat.nat
                      (λ (i : sttfa.etap (sttfa.p nat.nat)),
                         sttfa.impl (nat.le i n) (nat.le (f i) n)))
                     (injn f n)
                     (logic.eq nat.nat (f (invert_permut n f m))
                      m)
                     (λ
                        (
                        lef : sttfa.eps
                              (sttfa.forall nat.nat
                               (λ (i : sttfa.etap (sttfa.p nat.nat)),
                                  sttfa.impl (nat.le i n) (nat.le (f i) n)))
                        ),
                        λ (injf : sttfa.eps (injn f n)),
                          injective_invert_permut f n permf
                          (f (invert_permut n f m)) m
                          (lef (invert_permut n f m) (Hle m lemn))
                          lemn
                          (invert_permut_f f n
                           (invert_permut n f m) (Hle m lemn)
                           injf))
                     permf)
                (permut_invert_permut f n permf);
