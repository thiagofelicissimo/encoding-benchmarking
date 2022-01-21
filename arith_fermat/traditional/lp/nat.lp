require tests.sttfa as sttfa;
require tests.connectives as connectives;
require tests.bool as bool;
require tests.leibniz as leibniz;
require tests.logic as logic;
require tests.relations as relations;
constant symbol nat : sttfa.{|type|};
constant symbol O : sttfa.etap (sttfa.p nat);
constant symbol S : sttfa.etap (sttfa.p (sttfa.arrow nat nat));
constant symbol match_nat_prop
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat sttfa.bool)
     (λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
        sttfa.impl (return O)
        (sttfa.impl
         (sttfa.forall nat
          (λ (n : sttfa.etap (sttfa.p nat)), return (S n)))
         (sttfa.forall nat
          (λ (z : sttfa.etap (sttfa.p nat)), return z)))));
constant symbol match_nat_type
  : sttfa.etap
    (sttfa.forallK
     (λ (return : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow return
         (sttfa.arrow (sttfa.arrow nat return)
          (sttfa.arrow nat return)))));
constant symbol axiom_match_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              connectives.equal return_type
              (match_nat_type return_type case_O case_S O) case_O))));
symbol eq_match_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              leibniz.leibniz return_type
              (match_nat_type return_type case_O case_S O) case_O))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (case_O : sttfa.etap (sttfa.p return_type)),
          λ
            (case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
            connectives.equal_leibniz return_type
            (match_nat_type return_type case_O case_S O) case_O
            (axiom_match_nat_type_O return_type case_O case_S);
symbol sym_eq_match_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              leibniz.leibniz return_type case_O
              (match_nat_type return_type case_O case_S O)))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (case_O : sttfa.etap (sttfa.p return_type)),
          λ
            (case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
            leibniz.sym_leibniz return_type
            (match_nat_type return_type case_O case_S O) case_O
            (eq_match_nat_type_O return_type case_O case_S);
constant symbol axiom_match_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              sttfa.forall nat
              (λ (n : sttfa.etap (sttfa.p nat)),
                 connectives.equal return_type
                 (match_nat_type return_type case_O case_S (S n))
                 (case_S n))))));
symbol eq_match_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              sttfa.forall nat
              (λ (n : sttfa.etap (sttfa.p nat)),
                 leibniz.leibniz return_type
                 (match_nat_type return_type case_O case_S (S n))
                 (case_S n))))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (case_O : sttfa.etap (sttfa.p return_type)),
          λ
            (case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
            λ (n : sttfa.etap (sttfa.p nat)),
              connectives.equal_leibniz return_type
              (match_nat_type return_type case_O case_S (S n))
              (case_S n) (axiom_match_nat_type_S return_type case_O case_S n);
symbol sym_eq_match_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall return_type
        (λ (case_O : sttfa.etap (sttfa.p return_type)),
           sttfa.forall (sttfa.arrow nat return_type)
           (λ
              (
              case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))
              ),
              sttfa.forall nat
              (λ (n : sttfa.etap (sttfa.p nat)),
                 leibniz.leibniz return_type (case_S n)
                 (match_nat_type return_type case_O case_S (S n)))))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (case_O : sttfa.etap (sttfa.p return_type)),
          λ
            (case_S : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
            λ (n : sttfa.etap (sttfa.p nat)),
              leibniz.sym_leibniz return_type
              (match_nat_type return_type case_O case_S (S n))
              (case_S n)
              (eq_match_nat_type_S return_type case_O case_S n);
constant symbol filter_nat_type
  : sttfa.etap
    (sttfa.forallK
     (λ (return : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow (sttfa.arrow nat return)
         (sttfa.arrow nat return))));
constant symbol axiom_filter_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           connectives.equal return_type
           (filter_nat_type return_type return O) (return O))));
symbol eq_filter_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           leibniz.leibniz return_type
           (filter_nat_type return_type return O) (return O))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
          connectives.equal_leibniz return_type
          (filter_nat_type return_type return O) (return O)
          (axiom_filter_nat_type_O return_type return);
symbol sym_eq_filter_nat_type_O
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           leibniz.leibniz return_type (return O)
           (filter_nat_type return_type return O))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
          leibniz.sym_leibniz return_type
          (filter_nat_type return_type return O) (return O)
          (eq_filter_nat_type_O return_type return);
constant symbol axiom_filter_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              connectives.equal return_type
              (filter_nat_type return_type return (S n))
              (return (S n))))));
symbol eq_filter_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              leibniz.leibniz return_type
              (filter_nat_type return_type return (S n))
              (return (S n))))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
          λ (n : sttfa.etap (sttfa.p nat)),
            connectives.equal_leibniz return_type
            (filter_nat_type return_type return (S n))
            (return (S n)) (axiom_filter_nat_type_S return_type return n);
symbol sym_eq_filter_nat_type_S
  : sttfa.eps
    (sttfa.forallP
     (λ (return_type : sttfa.{|type|}),
        sttfa.forall (sttfa.arrow nat return_type)
        (λ
           (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              leibniz.leibniz return_type (return (S n))
              (filter_nat_type return_type return (S n))))))
  ≔ λ (return_type : sttfa.{|type|}),
        λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat return_type))),
          λ (n : sttfa.etap (sttfa.p nat)),
            leibniz.sym_leibniz return_type
            (filter_nat_type return_type return (S n))
            (return (S n))
            (eq_filter_nat_type_S return_type return n);
constant symbol nat_ind
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat sttfa.bool)
     (λ (Q : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
        sttfa.impl (Q O)
        (sttfa.impl
         (sttfa.forall nat
          (λ (x : sttfa.etap (sttfa.p nat)),
             sttfa.impl (Q x) (Q (S x))))
         (sttfa.forall nat (λ (x : sttfa.etap (sttfa.p nat)), Q x)))));
symbol pred : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_type nat O
        (λ (p : sttfa.etap (sttfa.p nat)), p) n;
symbol not_zero : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_type sttfa.bool connectives.False
        (λ (p : sttfa.etap (sttfa.p nat)), connectives.True) n;
constant symbol le
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat sttfa.bool)));
constant symbol le_n
  : sttfa.eps
    (sttfa.forall nat (λ (n : sttfa.etap (sttfa.p nat)), le n n));
constant symbol le_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m) (le n (S m)))));
constant symbol match_le_prop
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall (sttfa.arrow nat sttfa.bool)
        (λ (return : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
           sttfa.impl (return n)
           (sttfa.impl
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)), return (S m)))
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                sttfa.impl (le n m) (return m)))))));
constant symbol le_ind
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall (sttfa.arrow nat sttfa.bool)
        (λ (Q : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
           sttfa.impl (Q n)
           (sttfa.impl
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                sttfa.impl (le n m) (sttfa.impl (Q m) (Q (S m)))))
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                sttfa.impl (le n m) (Q m)))))));
symbol lt
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat sttfa.bool)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)), le (S n) m;
constant symbol plus
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol plus_body
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol axiom_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat) (plus n)
        (filter_nat_type (sttfa.arrow nat nat) plus_body n)));
symbol eq_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat) (plus n)
        (filter_nat_type (sttfa.arrow nat nat) plus_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat) (plus n)
        (filter_nat_type (sttfa.arrow nat nat) plus_body n)
        (axiom_plus n);
symbol sym_eq_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (filter_nat_type (sttfa.arrow nat nat) plus_body n)
        (plus n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat) (plus n)
        (filter_nat_type (sttfa.arrow nat nat) plus_body n)
        (eq_plus n);
constant symbol axiom_plus_body_O
  : sttfa.eps
    (connectives.equal (sttfa.arrow nat nat) (plus_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), m));
symbol eq_plus_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat) (plus_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), m))
  ≔ connectives.equal_leibniz (sttfa.arrow nat nat)
      (plus_body O) (λ (m : sttfa.etap (sttfa.p nat)), m)
      axiom_plus_body_O;
symbol sym_eq_plus_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat)
     (λ (m : sttfa.etap (sttfa.p nat)), m) (plus_body O))
  ≔ leibniz.sym_leibniz (sttfa.arrow nat nat) (plus_body O)
      (λ (m : sttfa.etap (sttfa.p nat)), m) eq_plus_body_O;
constant symbol axiom_plus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat)
        (plus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), S (plus n m))));
symbol eq_plus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (plus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), S (plus n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat)
        (plus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), S (plus n m))
        (axiom_plus_body_S n);
symbol sym_eq_plus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (λ (m : sttfa.etap (sttfa.p nat)), S (plus n m))
        (plus_body (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat)
        (plus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), S (plus n m))
        (eq_plus_body_S n);
constant symbol times
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol times_body
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol axiom_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat) (times n)
        (filter_nat_type (sttfa.arrow nat nat) times_body n)));
symbol eq_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat) (times n)
        (filter_nat_type (sttfa.arrow nat nat) times_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat) (times n)
        (filter_nat_type (sttfa.arrow nat nat) times_body n)
        (axiom_times n);
symbol sym_eq_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (filter_nat_type (sttfa.arrow nat nat) times_body n)
        (times n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat) (times n)
        (filter_nat_type (sttfa.arrow nat nat) times_body n)
        (eq_times n);
constant symbol axiom_times_body_O
  : sttfa.eps
    (connectives.equal (sttfa.arrow nat nat) (times_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), O));
symbol eq_times_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat) (times_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), O))
  ≔ connectives.equal_leibniz (sttfa.arrow nat nat)
      (times_body O) (λ (m : sttfa.etap (sttfa.p nat)), O)
      axiom_times_body_O;
symbol sym_eq_times_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat)
     (λ (m : sttfa.etap (sttfa.p nat)), O) (times_body O))
  ≔ leibniz.sym_leibniz (sttfa.arrow nat nat)
      (times_body O) (λ (m : sttfa.etap (sttfa.p nat)), O)
      eq_times_body_O;
constant symbol axiom_times_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat)
        (times_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), plus m (times n m))));
symbol eq_times_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (times_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), plus m (times n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat)
        (times_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), plus m (times n m))
        (axiom_times_body_S n);
symbol sym_eq_times_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (λ (m : sttfa.etap (sttfa.p nat)), plus m (times n m))
        (times_body (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat)
        (times_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)), plus m (times n m))
        (eq_times_body_S n);
constant symbol minus
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol minus_body
  : sttfa.etap (sttfa.p (sttfa.arrow nat (sttfa.arrow nat nat)));
constant symbol axiom_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat) (minus n)
        (filter_nat_type (sttfa.arrow nat nat) minus_body n)));
symbol eq_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat) (minus n)
        (filter_nat_type (sttfa.arrow nat nat) minus_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat) (minus n)
        (filter_nat_type (sttfa.arrow nat nat) minus_body n)
        (axiom_minus n);
symbol sym_eq_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (filter_nat_type (sttfa.arrow nat nat) minus_body n)
        (minus n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat) (minus n)
        (filter_nat_type (sttfa.arrow nat nat) minus_body n)
        (eq_minus n);
constant symbol axiom_minus_body_O
  : sttfa.eps
    (connectives.equal (sttfa.arrow nat nat) (minus_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), O));
symbol eq_minus_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat) (minus_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), O))
  ≔ connectives.equal_leibniz (sttfa.arrow nat nat)
      (minus_body O) (λ (m : sttfa.etap (sttfa.p nat)), O)
      axiom_minus_body_O;
symbol sym_eq_minus_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat nat)
     (λ (m : sttfa.etap (sttfa.p nat)), O) (minus_body O))
  ≔ leibniz.sym_leibniz (sttfa.arrow nat nat)
      (minus_body O) (λ (m : sttfa.etap (sttfa.p nat)), O)
      eq_minus_body_O;
constant symbol axiom_minus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat nat)
        (minus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type nat (S n)
           (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m)));
symbol eq_minus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (minus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type nat (S n)
           (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat nat)
        (minus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type nat (S n)
           (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m)
        (axiom_minus_body_S n);
symbol sym_eq_minus_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat nat)
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type nat (S n)
           (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m)
        (minus_body (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat nat)
        (minus_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type nat (S n)
           (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m)
        (eq_minus_body_S n);
symbol nat_case
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall (sttfa.arrow nat sttfa.bool)
        (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
           sttfa.impl (sttfa.impl (logic.eq nat n O) (P O))
           (sttfa.impl
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                sttfa.impl (logic.eq nat n (S m)) (P (S m))))
            (P n)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
          nat_ind
          (λ (_x_365 : sttfa.etap (sttfa.p nat)),
             sttfa.impl
             (sttfa.impl (logic.eq nat _x_365 O) (P O))
             (sttfa.impl
              (sttfa.forall nat
               (λ (m : sttfa.etap (sttfa.p nat)),
                  sttfa.impl (logic.eq nat _x_365 (S m))
                  (P (S m))))
              (P _x_365)))
          (λ
             (
             auto : sttfa.eps
                    (sttfa.impl (logic.eq nat O O) (P O))
             ),
             λ
               (
               auto' : sttfa.eps
                       (sttfa.forall nat
                        (λ (m : sttfa.etap (sttfa.p nat)),
                           sttfa.impl (logic.eq nat O (S m))
                           (P (S m))))
               ), auto (logic.refl nat O))
          (λ (x_366 : sttfa.etap (sttfa.p nat)),
             λ
               (
               _x_368 : sttfa.eps
                        (sttfa.impl
                         (sttfa.impl (logic.eq nat x_366 O) (P O))
                         (sttfa.impl
                          (sttfa.forall nat
                           (λ (m : sttfa.etap (sttfa.p nat)),
                              sttfa.impl (logic.eq nat x_366 (S m))
                              (P (S m))))
                          (P x_366)))
               ),
               λ
                 (
                 auto : sttfa.eps
                        (sttfa.impl (logic.eq nat (S x_366) O)
                         (P O))
                 ),
                 λ
                   (
                   auto' : sttfa.eps
                           (sttfa.forall nat
                            (λ (m : sttfa.etap (sttfa.p nat)),
                               sttfa.impl
                               (logic.eq nat (S x_366) (S m))
                               (P (S m))))
                   ), auto' x_366 (logic.refl nat (S x_366)))
          n;
symbol nat_elim2
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat (sttfa.arrow nat sttfa.bool))
     (λ
        (
        R : sttfa.etap
            (sttfa.p (sttfa.arrow nat (sttfa.arrow nat sttfa.bool)))
        ),
        sttfa.impl
        (sttfa.forall nat
         (λ (n : sttfa.etap (sttfa.p nat)), R O n))
        (sttfa.impl
         (sttfa.forall nat
          (λ (n : sttfa.etap (sttfa.p nat)), R (S n) O))
         (sttfa.impl
          (sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (m : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (R n m) (R (S n) (S m)))))
          (sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (m : sttfa.etap (sttfa.p nat)), R n m)))))))
  ≔ λ
        (
        R : sttfa.etap
            (sttfa.p (sttfa.arrow nat (sttfa.arrow nat sttfa.bool)))
        ),
        λ
          (
          ROn : sttfa.eps
                (sttfa.forall nat
                 (λ (n : sttfa.etap (sttfa.p nat)), R O n))
          ),
          λ
            (
            RSO : sttfa.eps
                  (sttfa.forall nat
                   (λ (n : sttfa.etap (sttfa.p nat)), R (S n) O))
            ),
            λ
              (
              RSS : sttfa.eps
                    (sttfa.forall nat
                     (λ (n : sttfa.etap (sttfa.p nat)),
                        sttfa.forall nat
                        (λ (m : sttfa.etap (sttfa.p nat)),
                           sttfa.impl (R n m) (R (S n) (S m)))))
              ),
              λ (n : sttfa.etap (sttfa.p nat)),
                nat_ind
                (λ (_x_365 : sttfa.etap (sttfa.p nat)),
                   sttfa.forall nat
                   (λ (m : sttfa.etap (sttfa.p nat)), R _x_365 m))
                (λ (m : sttfa.etap (sttfa.p nat)), ROn m)
                (λ (n0 : sttfa.etap (sttfa.p nat)),
                   λ
                     (
                     Rn0m : sttfa.eps
                            (sttfa.forall nat
                             (λ (m : sttfa.etap (sttfa.p nat)), R n0 m))
                     ),
                     λ (m : sttfa.etap (sttfa.p nat)),
                       match_nat_prop
                       (λ (__ : sttfa.etap (sttfa.p nat)),
                          R (S n0) __)
                       (RSO n0)
                       (λ (auto : sttfa.etap (sttfa.p nat)),
                          RSS n0 auto (Rn0m auto))
                       m)
                n;
symbol le_gen
  : sttfa.eps
    (sttfa.forall (sttfa.arrow nat sttfa.bool)
     (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
        sttfa.forall nat
        (λ (n : sttfa.etap (sttfa.p nat)),
           sttfa.impl
           (sttfa.forall nat
            (λ (i : sttfa.etap (sttfa.p nat)),
               sttfa.impl (le i n) (P i)))
           (P n))))
  ≔ λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
        λ (n : sttfa.etap (sttfa.p nat)),
          λ
            (
            auto : sttfa.eps
                   (sttfa.forall nat
                    (λ (i : sttfa.etap (sttfa.p nat)),
                       sttfa.impl (le i n) (P i)))
            ), auto n (le_n n);
symbol pred_Sn
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat n (pred (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        sym_eq_match_nat_type_S nat O
        (λ (p : sttfa.etap (sttfa.p nat)), p) n
        (λ (y : sttfa.etap (sttfa.p nat)), logic.eq nat n y)
        (logic.refl nat n);
symbol injective_S : sttfa.eps (relations.injective_ nat nat S)
  ≔ λ (x : sttfa.etap (sttfa.p nat)),
        λ (y : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (logic.eq nat (S x) (S y))),
            logic.rewrite_l nat y
            (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat __ y)
            (logic.refl nat y) x
            (logic.rewrite_r nat (pred (S x))
             (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat y __)
             (logic.rewrite_r nat (S y)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat y (pred __))
              (pred_Sn y) (S x) auto)
             x (pred_Sn x));
symbol S_pred
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.impl (lt O n) (logic.eq nat (S (pred n)) n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (posn : sttfa.eps (lt O n)),
          match_le_prop (S O)
          (λ (__ : sttfa.etap (sttfa.p nat)),
             logic.eq nat (S (pred __)) __)
          (logic.rewrite_l nat O
           (λ (__ : sttfa.etap (sttfa.p nat)),
              logic.eq nat (S __) (S O))
           (logic.refl nat (S O)) (pred (S O))
           (pred_Sn O))
          (λ (m : sttfa.etap (sttfa.p nat)),
             logic.rewrite_l nat m
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat (S __) (S m))
             (logic.refl nat (S m)) (pred (S m))
             (pred_Sn m))
          n posn;
symbol plus_O_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat n (plus O n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        sym_eq_plus O
        (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
           logic.eq nat n (y n))
        (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
         plus_body
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat n (y n))
         (sym_eq_plus_body_O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat n (y n))
          (logic.refl nat n)));
symbol plus_n_O
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat n (plus n O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           logic.eq nat _x_365 (plus _x_365 O))
        (sym_eq_plus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat O (y O))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          plus_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat O (y O))
          (sym_eq_plus_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat O (y O))
           (logic.refl nat O))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (logic.eq nat x_366 (plus x_366 O))
             ),
             sym_eq_plus (S x_366)
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (S x_366) (y O))
             (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
              plus_body x_366
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 logic.eq nat (S x_366) (y O))
              (sym_eq_plus_body_S x_366
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (S x_366) (y O))
               (logic.rewrite_l nat x_366
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (S x_366) (S __))
                (logic.refl nat (S x_366)) (plus x_366 O)
                _x_368))))
        n;
symbol plus_n_Sm
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat (S (plus n m)) (plus n (S m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              logic.eq nat (S (plus _x_365 m))
              (plus _x_365 (S m))))
        (λ (m : sttfa.etap (sttfa.p nat)),
           sym_eq_plus O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (S (y m)) (plus O (S m)))
           (sym_eq_plus O
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat
               (S
                (filter_nat_type (sttfa.arrow nat nat)
                 plus_body O m))
               (y (S m)))
            (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
             plus_body
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat
                (S
                 (filter_nat_type (sttfa.arrow nat nat)
                  plus_body O m))
                (y (S m)))
             (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
              plus_body
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 logic.eq nat (S (y m))
                 (plus_body O (S m)))
              (sym_eq_plus_body_O
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (S (y m))
                  (plus_body O (S m)))
               (sym_eq_plus_body_O
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat (S m) (y (S m)))
                (logic.refl nat (S m))))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (m : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (S (plus x_366 m))
                          (plus x_366 (S m))))
             ),
             λ (m : sttfa.etap (sttfa.p nat)),
               sym_eq_plus (S x_366)
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (S (y m))
                  (plus (S x_366) (S m)))
               (sym_eq_plus (S x_366)
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat
                   (S
                    (filter_nat_type (sttfa.arrow nat nat)
                     plus_body (S x_366) m))
                   (y (S m)))
                (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                 plus_body x_366
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat
                    (S
                     (filter_nat_type (sttfa.arrow nat nat)
                      plus_body (S x_366) m))
                    (y (S m)))
                 (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                  plus_body x_366
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat (S (y m))
                     (plus_body (S x_366) (S m)))
                  (sym_eq_plus_body_S x_366
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      logic.eq nat (S (y m))
                      (plus_body (S x_366) (S m)))
                   (sym_eq_plus_body_S x_366
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       logic.eq nat (S (S (plus x_366 m)))
                       (y (S m)))
                    (logic.rewrite_r nat (plus x_366 (S m))
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq nat (S __)
                        (S (plus x_366 (S m))))
                     (logic.rewrite_r nat
                      (plus x_366 (S (S m)))
                      (λ (__ : sttfa.etap (sttfa.p nat)),
                         logic.eq nat __
                         (S (plus x_366 (S m))))
                      (logic.rewrite_r nat
                       (plus x_366 (S (S m)))
                       (λ (__ : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (plus x_366 (S (S m)))
                          __)
                       (logic.refl nat (plus x_366 (S (S m))))
                       (S (plus x_366 (S m))) (_x_368 (S m)))
                      (S (plus x_366 (S m))) (_x_368 (S m)))
                     (S (plus x_366 m)) (_x_368 m))))))))
        n;
symbol commutative_plus
  : sttfa.eps (relations.{|commutative|} nat plus)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (y : sttfa.etap (sttfa.p nat)),
              logic.eq nat (plus _x_365 y) (plus y _x_365)))
        (λ (y : sttfa.etap (sttfa.p nat)),
           sym_eq_plus O
           (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (z y) (plus y O))
           (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
            plus_body
            (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (z y) (plus y O))
            (sym_eq_plus_body_O
             (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (z y) (plus y O))
             (logic.rewrite_l nat y
              (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat y __)
              (logic.refl nat y) (plus y O) (plus_n_O y)))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (plus x_366 y)
                          (plus y x_366)))
             ),
             λ (y : sttfa.etap (sttfa.p nat)),
               sym_eq_plus (S x_366)
               (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (z y) (plus y (S x_366)))
               (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                plus_body x_366
                (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat (z y) (plus y (S x_366)))
                (sym_eq_plus_body_S x_366
                 (λ
                    (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (z y) (plus y (S x_366)))
                 (logic.rewrite_r nat (plus x_366 (S y))
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq nat __ (plus y (S x_366)))
                  (logic.rewrite_r nat (plus y (S x_366))
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq nat __ (plus y (S x_366)))
                   (logic.refl nat (plus y (S x_366)))
                   (plus x_366 (S y))
                   (logic.rewrite_l nat (S (plus x_366 y))
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq nat __ (plus y (S x_366)))
                    (logic.rewrite_r nat (plus y x_366)
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq nat (S __)
                        (plus y (S x_366)))
                     (plus_n_Sm y x_366) (plus x_366 y) (_x_368 y))
                    (plus x_366 (S y)) (plus_n_Sm x_366 y)))
                  (S (plus x_366 y)) (plus_n_Sm x_366 y)))))
        n;
symbol associative_plus
  : sttfa.eps (relations.{|associative|} nat plus)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (y : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (z : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (plus (plus _x_365 y) z)
                 (plus _x_365 (plus y z)))))
        (λ (y : sttfa.etap (sttfa.p nat)),
           λ (z : sttfa.etap (sttfa.p nat)),
             sym_eq_plus O
             (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (plus (plus O y) z)
                (x (plus y z)))
             (sym_eq_plus O
              (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 logic.eq nat (plus (x y) z)
                 (filter_nat_type (sttfa.arrow nat nat)
                  plus_body O (plus y z)))
              (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
               plus_body
               (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (plus (x y) z)
                  (filter_nat_type (sttfa.arrow nat nat)
                   plus_body O (plus y z)))
               (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                plus_body
                (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat (plus (plus_body O y) z)
                   (x (plus y z)))
                (sym_eq_plus_body_O
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (plus (plus_body O y) z)
                    (x (plus y z)))
                 (sym_eq_plus_body_O
                  (λ
                     (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat (plus (x y) z) (plus y z))
                  (logic.refl nat (plus y z))))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (z : sttfa.etap (sttfa.p nat)),
                             logic.eq nat (plus (plus x_366 y) z)
                             (plus x_366 (plus y z)))))
             ),
             λ (y : sttfa.etap (sttfa.p nat)),
               λ (z : sttfa.etap (sttfa.p nat)),
                 sym_eq_plus (S x_366)
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (plus (plus (S x_366) y) z)
                    (x (plus y z)))
                 (sym_eq_plus (S x_366)
                  (λ
                     (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat (plus (x y) z)
                     (filter_nat_type (sttfa.arrow nat nat)
                      plus_body (S x_366) (plus y z)))
                  (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                   plus_body x_366
                   (λ
                      (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      logic.eq nat (plus (x y) z)
                      (filter_nat_type (sttfa.arrow nat nat)
                       plus_body (S x_366) (plus y z)))
                   (sym_eq_filter_nat_type_S
                    (sttfa.arrow nat nat) plus_body x_366
                    (λ
                       (
                       x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       logic.eq nat
                       (plus (plus_body (S x_366) y) z)
                       (x (plus y z)))
                    (sym_eq_plus_body_S x_366
                     (λ
                        (
                        x : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        logic.eq nat
                        (plus (plus_body (S x_366) y) z)
                        (x (plus y z)))
                     (sym_eq_plus_body_S x_366
                      (λ
                         (
                         x : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         logic.eq nat (plus (x y) z)
                         (S (plus x_366 (plus y z))))
                      (sym_eq_plus (S (plus x_366 y))
                       (λ
                          (
                          x : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ),
                          logic.eq nat (x z)
                          (S (plus x_366 (plus y z))))
                       (sym_eq_filter_nat_type_S
                        (sttfa.arrow nat nat) plus_body
                        (plus x_366 y)
                        (λ
                           (
                           x : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ),
                           logic.eq nat (x z)
                           (S (plus x_366 (plus y z))))
                        (sym_eq_plus_body_S (plus x_366 y)
                         (λ
                            (
                            x : sttfa.etap
                                (sttfa.p (sttfa.arrow nat nat))
                            ),
                            logic.eq nat (x z)
                            (S (plus x_366 (plus y z))))
                         (logic.rewrite_r nat
                          (plus x_366 (plus y z))
                          (λ (__ : sttfa.etap (sttfa.p nat)),
                             logic.eq nat (S __)
                             (S (plus x_366 (plus y z))))
                          (logic.refl nat
                           (S (plus x_366 (plus y z))))
                          (plus (plus x_366 y) z) (_x_368 y z)))))))))))
        n;
symbol assoc_plus1
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (b : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (c : sttfa.etap (sttfa.p nat)),
              logic.eq nat (plus c (plus b a))
              (plus (plus b c) a)))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            logic.rewrite_r nat (plus a b)
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq nat (plus c __) (plus (plus b c) a))
            (logic.rewrite_r nat (plus a (plus b c))
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat (plus c (plus a b)) __)
             (logic.rewrite_r nat (plus a (plus b c))
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat __ (plus a (plus b c)))
              (logic.refl nat (plus a (plus b c)))
              (plus c (plus a b))
              (logic.rewrite_l nat (plus (plus a b) c)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (plus c (plus a b)) __)
               (commutative_plus c (plus a b))
               (plus a (plus b c)) (associative_plus a b c)))
             (plus (plus b c) a)
             (commutative_plus (plus b c) a))
            (plus b a) (commutative_plus b a);
symbol injective_plus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        relations.injective_ nat nat
        (λ (m : sttfa.etap (sttfa.p nat)), plus n m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           relations.injective_ nat nat
           (λ (m : sttfa.etap (sttfa.p nat)), plus _x_365 m))
        (sym_eq_plus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            relations.injective_ nat nat
            (λ (m : sttfa.etap (sttfa.p nat)), y m))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          plus_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             relations.injective_ nat nat
             (λ (m : sttfa.etap (sttfa.p nat)), y m))
          (sym_eq_plus_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              relations.injective_ nat nat
              (λ (m : sttfa.etap (sttfa.p nat)), y m))
           (λ (x : sttfa.etap (sttfa.p nat)),
              λ (y : sttfa.etap (sttfa.p nat)),
                λ (auto : sttfa.eps (logic.eq nat x y)),
                  logic.rewrite_l nat x
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq nat x __)
                  (logic.refl nat x) y auto))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (x : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (y : sttfa.etap (sttfa.p nat)),
                             sttfa.impl
                             (logic.eq nat (plus x_366 x)
                              (plus x_366 y))
                             (logic.eq nat x y))))
             ),
             sym_eq_plus (S x_366)
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                relations.injective_ nat nat
                (λ (m : sttfa.etap (sttfa.p nat)), y m))
             (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
              plus_body x_366
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 relations.injective_ nat nat
                 (λ (m : sttfa.etap (sttfa.p nat)), y m))
              (sym_eq_plus_body_S x_366
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  relations.injective_ nat nat
                  (λ (m : sttfa.etap (sttfa.p nat)), y m))
               (λ (x : sttfa.etap (sttfa.p nat)),
                  λ (y : sttfa.etap (sttfa.p nat)),
                    λ
                      (
                      auto : sttfa.eps
                             (logic.eq nat (S (plus x_366 x))
                              (S (plus x_366 y)))
                      ),
                      _x_368 x y
                      (injective_S (plus x_366 x) (plus x_366 y)
                       (logic.rewrite_r nat (plus x_366 (S x))
                        (λ (__ : sttfa.etap (sttfa.p nat)),
                           logic.eq nat __ (S (plus x_366 y)))
                        (logic.rewrite_r nat (plus x_366 (S y))
                         (λ (__ : sttfa.etap (sttfa.p nat)),
                            logic.eq nat (plus x_366 (S x)) __)
                         (logic.rewrite_l nat (plus x_366 (S x))
                          (λ (__ : sttfa.etap (sttfa.p nat)),
                             logic.eq nat (plus x_366 (S x)) __)
                          (logic.refl nat (plus x_366 (S x)))
                          (plus x_366 (S y))
                          (logic.rewrite_l nat (S (plus x_366 y))
                           (λ (__ : sttfa.etap (sttfa.p nat)),
                              logic.eq nat (plus x_366 (S x)) __)
                           (logic.rewrite_l nat
                            (S (plus x_366 x))
                            (λ (__ : sttfa.etap (sttfa.p nat)),
                               logic.eq nat __ (S (plus x_366 y)))
                            auto (plus x_366 (S x))
                            (plus_n_Sm x_366 x))
                           (plus x_366 (S y)) (plus_n_Sm x_366 y)))
                         (S (plus x_366 y)) (plus_n_Sm x_366 y))
                        (S (plus x_366 x)) (plus_n_Sm x_366 x)))))))
        n;
symbol times_Sn_m
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat (plus m (times n m))
           (times (S n) m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          sym_eq_times (S n)
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat (plus m (times n m)) (y m))
          (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
           times_body n
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (plus m (times n m)) (y m))
           (sym_eq_times_body_S n
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (plus m (times n m)) (y m))
            (logic.refl nat (plus m (times n m)))));
symbol times_O_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat O (times O n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        sym_eq_times O
        (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
           logic.eq nat O (y n))
        (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
         times_body
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat O (y n))
         (sym_eq_times_body_O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat O (y n))
          (logic.refl nat O)));
symbol times_n_O
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat O (times n O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           logic.eq nat O (times _x_365 O))
        (logic.rewrite_l nat O
         (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat O __)
         (logic.refl nat O) (times O O)
         (times_O_n O))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (logic.eq nat O (times x_366 O))
             ),
             logic.rewrite_l nat (plus O (times x_366 O))
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat O __)
             (logic.rewrite_l nat O
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat O (plus O __))
              (logic.rewrite_l nat O
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat O __)
               (logic.refl nat O) (plus O O)
               (plus_O_n O))
              (times x_366 O) _x_368)
             (times (S x_366) O) (times_Sn_m x_366 O))
        n;
symbol times_n_Sm
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat (plus n (times n m))
           (times n (S m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              logic.eq nat (plus _x_365 (times _x_365 m))
              (times _x_365 (S m))))
        (sym_eq_times O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (m : sttfa.etap (sttfa.p nat)),
               logic.eq nat (plus O (times O m))
               (y (S m))))
         (sym_eq_times O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                logic.eq nat (plus O (y m))
                (filter_nat_type (sttfa.arrow nat nat)
                 times_body O (S m))))
          (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
           times_body
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (m : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (plus O (y m))
                 (filter_nat_type (sttfa.arrow nat nat)
                  times_body O (S m))))
           (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
            times_body
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.forall nat
               (λ (m : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (plus O (times_body O m))
                  (y (S m))))
            (sym_eq_times_body_O
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.forall nat
                (λ (m : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (plus O (times_body O m))
                   (y (S m))))
             (sym_eq_times_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.forall nat
                 (λ (m : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (plus O (y m)) O))
              (sym_eq_plus O
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.forall nat
                  (λ (m : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (y O) O))
               (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                plus_body
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.forall nat
                   (λ (m : sttfa.etap (sttfa.p nat)),
                      logic.eq nat (y O) O))
                (sym_eq_plus_body_O
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.forall nat
                    (λ (m : sttfa.etap (sttfa.p nat)),
                       logic.eq nat (y O) O))
                 (λ (_m : sttfa.etap (sttfa.p nat)),
                    logic.refl nat O))))))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (m : sttfa.etap (sttfa.p nat)),
                          logic.eq nat
                          (plus x_366 (times x_366 m))
                          (times x_366 (S m))))
             ),
             λ (m : sttfa.etap (sttfa.p nat)),
               sym_eq_times (S x_366)
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat
                  (plus (S x_366) (times (S x_366) m))
                  (y (S m)))
               (sym_eq_times (S x_366)
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat (plus (S x_366) (y m))
                   (filter_nat_type (sttfa.arrow nat nat)
                    times_body (S x_366) (S m)))
                (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                 times_body x_366
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (plus (S x_366) (y m))
                    (filter_nat_type (sttfa.arrow nat nat)
                     times_body (S x_366) (S m)))
                 (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                  times_body x_366
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat
                     (plus (S x_366) (times_body (S x_366) m))
                     (y (S m)))
                  (sym_eq_times_body_S x_366
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      logic.eq nat
                      (plus (S x_366)
                       (times_body (S x_366) m))
                      (y (S m)))
                   (sym_eq_times_body_S x_366
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       logic.eq nat (plus (S x_366) (y m))
                       (plus (S m) (times x_366 (S m))))
                    (sym_eq_plus (S x_366)
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        logic.eq nat (y (plus m (times x_366 m)))
                        (plus (S m) (times x_366 (S m))))
                     (sym_eq_filter_nat_type_S
                      (sttfa.arrow nat nat) plus_body x_366
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         logic.eq nat
                         (y (plus m (times x_366 m)))
                         (plus (S m) (times x_366 (S m))))
                      (sym_eq_plus_body_S x_366
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ),
                          logic.eq nat
                          (y (plus m (times x_366 m)))
                          (plus (S m) (times x_366 (S m))))
                       (sym_eq_plus (S m)
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ),
                           logic.eq nat
                           (S
                            (plus x_366 (plus m (times x_366 m))))
                           (y (times x_366 (S m))))
                        (sym_eq_filter_nat_type_S
                         (sttfa.arrow nat nat) plus_body m
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p (sttfa.arrow nat nat))
                            ),
                            logic.eq nat
                            (S
                             (plus x_366 (plus m (times x_366 m))))
                            (y (times x_366 (S m))))
                         (sym_eq_plus_body_S m
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat nat))
                             ),
                             logic.eq nat
                             (S
                              (plus x_366
                               (plus m (times x_366 m))))
                             (y (times x_366 (S m))))
                          (logic.rewrite_r nat
                           (plus x_366
                            (S (plus m (times x_366 m))))
                           (λ (__ : sttfa.etap (sttfa.p nat)),
                              logic.eq nat __
                              (S (plus m (times x_366 (S m)))))
                           (logic.rewrite_r nat
                            (plus m (S (times x_366 m)))
                            (λ (__ : sttfa.etap (sttfa.p nat)),
                               logic.eq nat (plus x_366 __)
                               (S
                                (plus m (times x_366 (S m)))))
                            (logic.rewrite_l nat
                             (plus x_366 (times x_366 m))
                             (λ (__ : sttfa.etap (sttfa.p nat)),
                                logic.eq nat
                                (plus x_366
                                 (plus m (S (times x_366 m))))
                                (S (plus m __)))
                             (logic.rewrite_r nat
                              (plus x_366
                               (plus m (times x_366 m)))
                              (λ (__ : sttfa.etap (sttfa.p nat)),
                                 logic.eq nat
                                 (plus x_366
                                  (plus m (S (times x_366 m))))
                                 (S __))
                              (logic.rewrite_r nat
                               (plus x_366
                                (S (plus m (times x_366 m))))
                               (λ (__ : sttfa.etap (sttfa.p nat)),
                                  logic.eq nat
                                  (plus x_366
                                   (plus m (S (times x_366 m))))
                                  __)
                               (logic.rewrite_r nat
                                (plus m (S (times x_366 m)))
                                (λ (__ : sttfa.etap (sttfa.p nat)),
                                   logic.eq nat
                                   (plus x_366
                                    (plus m (S (times x_366 m))))
                                   (plus x_366 __))
                                (logic.refl nat
                                 (plus x_366
                                  (plus m (S (times x_366 m)))))
                                (S (plus m (times x_366 m)))
                                (plus_n_Sm m (times x_366 m)))
                               (S
                                (plus x_366
                                 (plus m (times x_366 m))))
                               (plus_n_Sm x_366
                                (plus m (times x_366 m))))
                              (plus m
                               (plus x_366 (times x_366 m)))
                              (logic.rewrite_l nat
                               (plus (plus x_366 m)
                                (times x_366 m))
                               (λ (__ : sttfa.etap (sttfa.p nat)),
                                  logic.eq nat
                                  (plus m
                                   (plus x_366 (times x_366 m)))
                                  __)
                               (assoc_plus1 (times x_366 m) x_366 m)
                               (plus x_366
                                (plus m (times x_366 m)))
                               (associative_plus x_366 m
                                (times x_366 m))))
                             (times x_366 (S m)) (_x_368 m))
                            (S (plus m (times x_366 m)))
                            (plus_n_Sm m (times x_366 m)))
                           (S
                            (plus x_366 (plus m (times x_366 m))))
                           (plus_n_Sm x_366
                            (plus m (times x_366 m))))))))))))))))
        n;
symbol commutative_times
  : sttfa.eps (relations.{|commutative|} nat times)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (y : sttfa.etap (sttfa.p nat)),
              logic.eq nat (times _x_365 y) (times y _x_365)))
        (sym_eq_times O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (z : sttfa.etap (sttfa.p nat)),
               logic.eq nat (y z) (times z O)))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          times_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (z : sttfa.etap (sttfa.p nat)),
                logic.eq nat (y z) (times z O)))
          (sym_eq_times_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (z : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (y z) (times z O)))
           (λ (y : sttfa.etap (sttfa.p nat)),
              logic.rewrite_l nat O
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat O __)
              (logic.refl nat O) (times y O)
              (times_n_O y)))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (times x_366 y)
                          (times y x_366)))
             ),
             λ (y : sttfa.etap (sttfa.p nat)),
               sym_eq_times (S x_366)
               (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  logic.eq nat (z y) (times y (S x_366)))
               (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                times_body x_366
                (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   logic.eq nat (z y) (times y (S x_366)))
                (sym_eq_times_body_S x_366
                 (λ
                    (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (z y) (times y (S x_366)))
                 (logic.rewrite_l nat (plus y (times y x_366))
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (plus y (times x_366 y)) __)
                  (logic.rewrite_l nat (times x_366 y)
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq nat (plus y (times x_366 y))
                      (plus y __))
                   (logic.refl nat (plus y (times x_366 y)))
                   (times y x_366) (_x_368 y))
                  (times y (S x_366)) (times_n_Sm y x_366)))))
        n;
symbol distributive_times_plus
  : sttfa.eps (relations.distributive nat times plus)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (y : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (z : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (times _x_365 (plus y z))
                 (plus (times _x_365 y) (times _x_365 z)))))
        (sym_eq_times O
         (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (y : sttfa.etap (sttfa.p nat)),
               sttfa.forall nat
               (λ (z : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (times O (plus y z))
                  (plus (times O y) (x z)))))
         (sym_eq_times O
          (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (y : sttfa.etap (sttfa.p nat)),
                sttfa.forall nat
                (λ (z : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (times O (plus y z))
                   (plus (x y)
                    (filter_nat_type (sttfa.arrow nat nat)
                     times_body O z)))))
          (sym_eq_times O
           (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (y : sttfa.etap (sttfa.p nat)),
                 sttfa.forall nat
                 (λ (z : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (x (plus y z))
                    (plus
                     (filter_nat_type (sttfa.arrow nat nat)
                      times_body O y)
                     (filter_nat_type (sttfa.arrow nat nat)
                      times_body O z)))))
           (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
            times_body
            (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.forall nat
               (λ (y : sttfa.etap (sttfa.p nat)),
                  sttfa.forall nat
                  (λ (z : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (x (plus y z))
                     (plus
                      (filter_nat_type (sttfa.arrow nat nat)
                       times_body O y)
                      (filter_nat_type (sttfa.arrow nat nat)
                       times_body O z)))))
            (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
             times_body
             (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.forall nat
                (λ (y : sttfa.etap (sttfa.p nat)),
                   sttfa.forall nat
                   (λ (z : sttfa.etap (sttfa.p nat)),
                      logic.eq nat (times_body O (plus y z))
                      (plus (x y)
                       (filter_nat_type (sttfa.arrow nat nat)
                        times_body O z)))))
             (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
              times_body
              (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.forall nat
                 (λ (y : sttfa.etap (sttfa.p nat)),
                    sttfa.forall nat
                    (λ (z : sttfa.etap (sttfa.p nat)),
                       logic.eq nat (times_body O (plus y z))
                       (plus (times_body O y) (x z)))))
              (sym_eq_times_body_O
               (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.forall nat
                  (λ (y : sttfa.etap (sttfa.p nat)),
                     sttfa.forall nat
                     (λ (z : sttfa.etap (sttfa.p nat)),
                        logic.eq nat
                        (times_body O (plus y z))
                        (plus (times_body O y) (x z)))))
               (sym_eq_times_body_O
                (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.forall nat
                   (λ (y : sttfa.etap (sttfa.p nat)),
                      sttfa.forall nat
                      (λ (z : sttfa.etap (sttfa.p nat)),
                         logic.eq nat
                         (times_body O (plus y z))
                         (plus (x y) O))))
                (sym_eq_times_body_O
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.forall nat
                    (λ (y : sttfa.etap (sttfa.p nat)),
                       sttfa.forall nat
                       (λ (z : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (x (plus y z))
                          (plus O O))))
                 (sym_eq_plus O
                  (λ
                     (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.forall nat
                     (λ (y : sttfa.etap (sttfa.p nat)),
                        sttfa.forall nat
                        (λ (z : sttfa.etap (sttfa.p nat)),
                           logic.eq nat O (x O))))
                  (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                   plus_body
                   (λ
                      (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      sttfa.forall nat
                      (λ (y : sttfa.etap (sttfa.p nat)),
                         sttfa.forall nat
                         (λ (z : sttfa.etap (sttfa.p nat)),
                            logic.eq nat O (x O))))
                   (sym_eq_plus_body_O
                    (λ
                       (
                       x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (z : sttfa.etap (sttfa.p nat)),
                             logic.eq nat O (x O))))
                    (λ (_y : sttfa.etap (sttfa.p nat)),
                       λ (_z : sttfa.etap (sttfa.p nat)),
                         logic.refl nat O)))))))))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (z : sttfa.etap (sttfa.p nat)),
                             logic.eq nat
                             (times x_366 (plus y z))
                             (plus (times x_366 y)
                              (times x_366 z)))))
             ),
             λ (y : sttfa.etap (sttfa.p nat)),
               λ (z : sttfa.etap (sttfa.p nat)),
                 sym_eq_times (S x_366)
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat (times (S x_366) (plus y z))
                    (plus (times (S x_366) y) (x z)))
                 (sym_eq_times (S x_366)
                  (λ
                     (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat
                     (times (S x_366) (plus y z))
                     (plus (x y)
                      (filter_nat_type (sttfa.arrow nat nat)
                       times_body (S x_366) z)))
                  (sym_eq_times (S x_366)
                   (λ
                      (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      logic.eq nat (x (plus y z))
                      (plus
                       (filter_nat_type (sttfa.arrow nat nat)
                        times_body (S x_366) y)
                       (filter_nat_type (sttfa.arrow nat nat)
                        times_body (S x_366) z)))
                   (sym_eq_filter_nat_type_S
                    (sttfa.arrow nat nat) times_body x_366
                    (λ
                       (
                       x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       logic.eq nat (x (plus y z))
                       (plus
                        (filter_nat_type (sttfa.arrow nat nat)
                         times_body (S x_366) y)
                        (filter_nat_type (sttfa.arrow nat nat)
                         times_body (S x_366) z)))
                    (sym_eq_filter_nat_type_S
                     (sttfa.arrow nat nat) times_body x_366
                     (λ
                        (
                        x : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        logic.eq nat
                        (times_body (S x_366) (plus y z))
                        (plus (x y)
                         (filter_nat_type (sttfa.arrow nat nat)
                          times_body (S x_366) z)))
                     (sym_eq_filter_nat_type_S
                      (sttfa.arrow nat nat) times_body x_366
                      (λ
                         (
                         x : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         logic.eq nat
                         (times_body (S x_366) (plus y z))
                         (plus (times_body (S x_366) y) (x z)))
                      (sym_eq_times_body_S x_366
                       (λ
                          (
                          x : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ),
                          logic.eq nat
                          (times_body (S x_366) (plus y z))
                          (plus (times_body (S x_366) y) (x z)))
                       (sym_eq_times_body_S x_366
                        (λ
                           (
                           x : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ),
                           logic.eq nat
                           (times_body (S x_366) (plus y z))
                           (plus (x y) (plus z (times x_366 z))))
                        (sym_eq_times_body_S x_366
                         (λ
                            (
                            x : sttfa.etap
                                (sttfa.p (sttfa.arrow nat nat))
                            ),
                            logic.eq nat (x (plus y z))
                            (plus (plus y (times x_366 y))
                             (plus z (times x_366 z))))
                         (logic.rewrite_r nat
                          (plus y
                           (plus z (times x_366 (plus y z))))
                          (λ (__ : sttfa.etap (sttfa.p nat)),
                             logic.eq nat __
                             (plus (plus y (times x_366 y))
                              (plus z (times x_366 z))))
                          (logic.rewrite_r nat
                           (plus y
                            (plus (times x_366 y)
                             (plus z (times x_366 z))))
                           (λ (__ : sttfa.etap (sttfa.p nat)),
                              logic.eq nat
                              (plus y
                               (plus z (times x_366 (plus y z))))
                              __)
                           (logic.rewrite_r nat
                            (plus z
                             (plus (times x_366 y)
                              (times x_366 z)))
                            (λ (__ : sttfa.etap (sttfa.p nat)),
                               logic.eq nat
                               (plus y
                                (plus z (times x_366 (plus y z))))
                               (plus y __))
                            (logic.rewrite_l nat
                             (times x_366 (plus y z))
                             (λ (__ : sttfa.etap (sttfa.p nat)),
                                logic.eq nat
                                (plus y
                                 (plus z (times x_366 (plus y z))))
                                (plus y (plus z __)))
                             (logic.refl nat
                              (plus y
                               (plus z (times x_366 (plus y z)))))
                             (plus (times x_366 y)
                              (times x_366 z))
                             (_x_368 y z))
                            (plus (times x_366 y)
                             (plus z (times x_366 z)))
                            (logic.rewrite_l nat
                             (plus (plus z (times x_366 y))
                              (times x_366 z))
                             (λ (__ : sttfa.etap (sttfa.p nat)),
                                logic.eq nat
                                (plus (times x_366 y)
                                 (plus z (times x_366 z)))
                                __)
                             (assoc_plus1 (times x_366 z) z
                              (times x_366 y))
                             (plus z
                              (plus (times x_366 y)
                               (times x_366 z)))
                             (associative_plus z (times x_366 y)
                              (times x_366 z))))
                           (plus (plus y (times x_366 y))
                            (plus z (times x_366 z)))
                           (associative_plus y (times x_366 y)
                            (plus z (times x_366 z))))
                          (plus (plus y z)
                           (times x_366 (plus y z)))
                          (associative_plus y z
                           (times x_366 (plus y z)))))))))))))
        n;
symbol distributive_times_plus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (b : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (c : sttfa.etap (sttfa.p nat)),
              logic.eq nat (times (plus b c) a)
              (plus (times b a) (times c a))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            logic.rewrite_r nat (times a (plus b c))
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq nat __ (plus (times b a) (times c a)))
            (logic.rewrite_r nat (times a b)
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat (times a (plus b c))
                (plus __ (times c a)))
             (logic.rewrite_r nat (times a c)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (times a (plus b c))
                 (plus (times a b) __))
              (logic.rewrite_l nat (times a (plus b c))
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (times a (plus b c)) __)
               (logic.refl nat (times a (plus b c)))
               (plus (times a b) (times a c))
               (distributive_times_plus a b c))
              (times c a) (commutative_times c a))
             (times b a) (commutative_times b a))
            (times (plus b c) a)
            (commutative_times (plus b c) a);
symbol associative_times
  : sttfa.eps (relations.{|associative|} nat times)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (y : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (z : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (times (times _x_365 y) z)
                 (times _x_365 (times y z)))))
        (sym_eq_times O
         (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (y : sttfa.etap (sttfa.p nat)),
               sttfa.forall nat
               (λ (z : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (times (times O y) z)
                  (x (times y z)))))
         (sym_eq_times O
          (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (y : sttfa.etap (sttfa.p nat)),
                sttfa.forall nat
                (λ (z : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (times (x y) z)
                   (filter_nat_type (sttfa.arrow nat nat)
                    times_body O (times y z)))))
          (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
           times_body
           (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (y : sttfa.etap (sttfa.p nat)),
                 sttfa.forall nat
                 (λ (z : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (times (x y) z)
                    (filter_nat_type (sttfa.arrow nat nat)
                     times_body O (times y z)))))
           (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
            times_body
            (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.forall nat
               (λ (y : sttfa.etap (sttfa.p nat)),
                  sttfa.forall nat
                  (λ (z : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (times (times_body O y) z)
                     (x (times y z)))))
            (sym_eq_times_body_O
             (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.forall nat
                (λ (y : sttfa.etap (sttfa.p nat)),
                   sttfa.forall nat
                   (λ (z : sttfa.etap (sttfa.p nat)),
                      logic.eq nat (times (times_body O y) z)
                      (x (times y z)))))
             (sym_eq_times_body_O
              (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.forall nat
                 (λ (y : sttfa.etap (sttfa.p nat)),
                    sttfa.forall nat
                    (λ (z : sttfa.etap (sttfa.p nat)),
                       logic.eq nat (times (x y) z) O)))
              (sym_eq_times O
               (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.forall nat
                  (λ (y : sttfa.etap (sttfa.p nat)),
                     sttfa.forall nat
                     (λ (z : sttfa.etap (sttfa.p nat)),
                        logic.eq nat (x z) O)))
               (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                times_body
                (λ (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.forall nat
                   (λ (y : sttfa.etap (sttfa.p nat)),
                      sttfa.forall nat
                      (λ (z : sttfa.etap (sttfa.p nat)),
                         logic.eq nat (x z) O)))
                (sym_eq_times_body_O
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.forall nat
                    (λ (y : sttfa.etap (sttfa.p nat)),
                       sttfa.forall nat
                       (λ (z : sttfa.etap (sttfa.p nat)),
                          logic.eq nat (x z) O)))
                 (λ (_y : sttfa.etap (sttfa.p nat)),
                    λ (_z : sttfa.etap (sttfa.p nat)),
                      logic.refl nat O))))))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (z : sttfa.etap (sttfa.p nat)),
                             logic.eq nat
                             (times (times x_366 y) z)
                             (times x_366 (times y z)))))
             ),
             λ (y : sttfa.etap (sttfa.p nat)),
               λ (z : sttfa.etap (sttfa.p nat)),
                 sym_eq_times (S x_366)
                 (λ
                    (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    logic.eq nat
                    (times (times (S x_366) y) z)
                    (x (times y z)))
                 (sym_eq_times (S x_366)
                  (λ
                     (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     logic.eq nat (times (x y) z)
                     (filter_nat_type (sttfa.arrow nat nat)
                      times_body (S x_366) (times y z)))
                  (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                   times_body x_366
                   (λ
                      (x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      logic.eq nat (times (x y) z)
                      (filter_nat_type (sttfa.arrow nat nat)
                       times_body (S x_366) (times y z)))
                   (sym_eq_filter_nat_type_S
                    (sttfa.arrow nat nat) times_body x_366
                    (λ
                       (
                       x : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       logic.eq nat
                       (times (times_body (S x_366) y) z)
                       (x (times y z)))
                    (sym_eq_times_body_S x_366
                     (λ
                        (
                        x : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        logic.eq nat
                        (times (times_body (S x_366) y) z)
                        (x (times y z)))
                     (sym_eq_times_body_S x_366
                      (λ
                         (
                         x : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         logic.eq nat (times (x y) z)
                         (plus (times y z)
                          (times x_366 (times y z))))
                      (logic.rewrite_r nat
                       (plus (times y z)
                        (times x_366 (times y z)))
                       (λ (__ : sttfa.etap (sttfa.p nat)),
                          logic.eq nat __
                          (plus (times y z)
                           (times x_366 (times y z))))
                       (logic.refl nat
                        (plus (times y z)
                         (times x_366 (times y z))))
                       (times (plus y (times x_366 y)) z)
                       (logic.rewrite_l nat
                        (times (times x_366 y) z)
                        (λ (__ : sttfa.etap (sttfa.p nat)),
                           logic.eq nat
                           (times (plus y (times x_366 y)) z)
                           (plus (times y z) __))
                        (distributive_times_plus_r z y
                         (times x_366 y))
                        (times x_366 (times y z)) (_x_368 y z)))))))))
        n;
symbol times_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (x : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (y : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (z : sttfa.etap (sttfa.p nat)),
              logic.eq nat (times x (times y z))
              (times y (times x z))))))
  ≔ λ (x : sttfa.etap (sttfa.p nat)),
        λ (y : sttfa.etap (sttfa.p nat)),
          λ (z : sttfa.etap (sttfa.p nat)),
            logic.rewrite_r nat (times y (times x z))
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq nat __ (times y (times x z)))
            (logic.refl nat (times y (times x z)))
            (times x (times y z))
            (logic.rewrite_l nat (times (times x y) z)
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat __ (times y (times x z)))
             (logic.rewrite_l nat (times y x)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (times __ z)
                 (times y (times x z)))
              (associative_times y x z) (times x y)
              (commutative_times y x))
             (times x (times y z)) (associative_times x y z));
symbol times_n_1
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat n (times n (S O))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        logic.rewrite_l nat (plus n (times n O))
        (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat n __)
        (logic.rewrite_l nat O
         (λ (__ : sttfa.etap (sttfa.p nat)),
            logic.eq nat n (plus n __))
         (logic.rewrite_l nat n
          (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat n __)
          (logic.refl nat n) (plus n O) (plus_n_O n))
         (times n O) (times_n_O n))
        (times n (S O)) (times_n_Sm n O);
symbol minus_S_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat (minus (S n) (S m)) (minus n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          eq_match_nat_type_S nat (S n)
          (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m
          (λ (y : sttfa.etap (sttfa.p nat)),
             logic.eq nat (minus (S n) (S m)) y)
          (eq_minus_body_S n
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (minus (S n) (S m)) (y (S m)))
           (eq_filter_nat_type_S (sttfa.arrow nat nat)
            minus_body n
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (minus (S n) (S m)) (y (S m)))
            (eq_minus (S n)
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (minus (S n) (S m))
                (y (S m)))
             (logic.refl nat (minus (S n) (S m))))));
symbol minus_O_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat O (minus O n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_prop
        (λ (__ : sttfa.etap (sttfa.p nat)),
           logic.eq nat O (minus O __))
        (sym_eq_minus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat O (y O))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          minus_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat O (y O))
          (sym_eq_minus_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat O (y O))
           (logic.refl nat O))))
        (sym_eq_minus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (n0 : sttfa.etap (sttfa.p nat)),
               logic.eq nat O (y (S n0))))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          minus_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (n0 : sttfa.etap (sttfa.p nat)),
                logic.eq nat O (y (S n0))))
          (sym_eq_minus_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (n0 : sttfa.etap (sttfa.p nat)),
                 logic.eq nat O (y (S n0))))
           (λ (auto : sttfa.etap (sttfa.p nat)),
              logic.refl nat O))))
        n;
symbol minus_n_O
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat n (minus n O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_prop
        (λ (__ : sttfa.etap (sttfa.p nat)),
           logic.eq nat __ (minus __ O))
        (logic.rewrite_l nat O
         (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat O __)
         (logic.refl nat O) (minus O O)
         (minus_O_n O))
        (λ (auto : sttfa.etap (sttfa.p nat)),
           sym_eq_minus (S auto)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (S auto) (y O))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
            minus_body auto
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (S auto) (y O))
            (sym_eq_minus_body_S auto
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (S auto) (y O))
             (sym_eq_match_nat_type_O nat (S auto)
              (λ (q : sttfa.etap (sttfa.p nat)), minus auto q)
              (λ (y : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (S auto) y)
              (logic.refl nat (S auto))))))
        n;
symbol minus_n_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq nat O (minus n n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           logic.eq nat O (minus _x_365 _x_365))
        (logic.rewrite_l nat O
         (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat O __)
         (logic.refl nat O) (minus O O)
         (minus_O_n O))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (logic.eq nat O (minus x_366 x_366))
             ),
             logic.rewrite_r nat (minus x_366 x_366)
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat O __)
             (logic.rewrite_l nat O
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat O __)
              (logic.refl nat O) (minus x_366 x_366) _x_368)
             (minus (S x_366) (S x_366))
             (minus_S_S x_366 x_366))
        n;
symbol eq_minus_S_pred
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat (minus n (S m))
           (pred (minus n m)))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           logic.eq nat (minus __ (S _0))
           (pred (minus __ _0)))
      (λ (_n : sttfa.etap (sttfa.p nat)),
         sym_eq_minus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat (minus O (S _n)) (pred (y _n)))
         (sym_eq_minus O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat (y (S _n))
             (pred
              (filter_nat_type (sttfa.arrow nat nat)
               minus_body O _n)))
          (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
           minus_body
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (y (S _n))
              (pred
               (filter_nat_type (sttfa.arrow nat nat)
                minus_body O _n)))
           (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
            minus_body
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (minus_body O (S _n))
               (pred (y _n)))
            (sym_eq_minus_body_O
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (minus_body O (S _n))
                (pred (y _n)))
             (sym_eq_minus_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 logic.eq nat (y (S _n))
                 (match_nat_type nat O
                  (λ (p : sttfa.etap (sttfa.p nat)), p) O))
              (sym_eq_match_nat_type_O nat O
               (λ (p : sttfa.etap (sttfa.p nat)), p)
               (λ (y : sttfa.etap (sttfa.p nat)),
                  logic.eq nat O y)
               (logic.refl nat O))))))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         sym_eq_minus (S n)
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            logic.eq nat (minus (S n) (S O))
            (pred (y O)))
         (sym_eq_minus (S n)
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             logic.eq nat (y (S O))
             (pred
              (filter_nat_type (sttfa.arrow nat nat)
               minus_body (S n) O)))
          (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
           minus_body n
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              logic.eq nat (y (S O))
              (pred
               (filter_nat_type (sttfa.arrow nat nat)
                minus_body (S n) O)))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
            minus_body n
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               logic.eq nat (minus_body (S n) (S O))
               (pred (y O)))
            (sym_eq_minus_body_S n
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                logic.eq nat (minus_body (S n) (S O))
                (pred (y O)))
             (sym_eq_minus_body_S n
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 logic.eq nat (y (S O))
                 (pred
                  (match_nat_type nat (S n)
                   (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                   O)))
              (sym_eq_match_nat_type_S nat (S n)
               (λ (q : sttfa.etap (sttfa.p nat)), minus n q) O
               (λ (y : sttfa.etap (sttfa.p nat)),
                  logic.eq nat y
                  (match_nat_type nat O
                   (λ (p : sttfa.etap (sttfa.p nat)), p)
                   (match_nat_type nat (S n)
                    (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                    O)))
               (sym_eq_match_nat_type_O nat (S n)
                (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                (λ (y : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (minus n O)
                   (match_nat_type nat O
                    (λ (p : sttfa.etap (sttfa.p nat)), p) y))
                (sym_eq_match_nat_type_S nat O
                 (λ (q : sttfa.etap (sttfa.p nat)), q) n
                 (λ (y : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (minus n O) y)
                 (logic.rewrite_l nat n
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq nat __ n)
                  (logic.refl nat n) (minus n O)
                  (minus_n_O n)))))))))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           sym_eq_minus (S n)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.impl
              (logic.eq nat (minus n (S m))
               (pred (minus n m)))
              (logic.eq nat (minus (S n) (S (S m)))
               (pred (y (S m)))))
           (sym_eq_minus (S n)
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.impl
               (logic.eq nat (minus n (S m))
                (pred (minus n m)))
               (logic.eq nat (y (S (S m)))
                (pred
                 (filter_nat_type (sttfa.arrow nat nat)
                  minus_body (S n) (S m)))))
            (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
             minus_body n
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.impl
                (logic.eq nat (minus n (S m))
                 (pred (minus n m)))
                (logic.eq nat (y (S (S m)))
                 (pred
                  (filter_nat_type (sttfa.arrow nat nat)
                   minus_body (S n) (S m)))))
             (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
              minus_body n
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.impl
                 (logic.eq nat (minus n (S m))
                  (pred (minus n m)))
                 (logic.eq nat
                  (minus_body (S n) (S (S m)))
                  (pred (y (S m)))))
              (sym_eq_minus_body_S n
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.impl
                  (logic.eq nat (minus n (S m))
                   (pred (minus n m)))
                  (logic.eq nat
                   (minus_body (S n) (S (S m)))
                   (pred (y (S m)))))
               (sym_eq_minus_body_S n
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.impl
                   (logic.eq nat (minus n (S m))
                    (pred (minus n m)))
                   (logic.eq nat (y (S (S m)))
                    (pred
                     (match_nat_type nat (S n)
                      (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                      (S m)))))
                (sym_eq_match_nat_type_S nat (S n)
                 (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                 (S m)
                 (λ (y : sttfa.etap (sttfa.p nat)),
                    sttfa.impl
                    (logic.eq nat (minus n (S m))
                     (pred (minus n m)))
                    (logic.eq nat y
                     (match_nat_type nat O
                      (λ (p : sttfa.etap (sttfa.p nat)), p)
                      (match_nat_type nat (S n)
                       (λ (q : sttfa.etap (sttfa.p nat)), minus n q)
                       (S m)))))
                 (sym_eq_match_nat_type_S nat (S n)
                  (λ (q : sttfa.etap (sttfa.p nat)), minus n q) m
                  (λ (y : sttfa.etap (sttfa.p nat)),
                     sttfa.impl
                     (logic.eq nat (minus n (S m))
                      (pred (minus n m)))
                     (logic.eq nat (minus n (S m))
                      (match_nat_type nat O
                       (λ (p : sttfa.etap (sttfa.p nat)), p) y)))
                  (λ
                     (
                     auto : sttfa.eps
                            (logic.eq nat (minus n (S m))
                             (match_nat_type nat O
                              (λ (p : sttfa.etap (sttfa.p nat)), p)
                              (minus n m)))
                     ),
                     logic.rewrite_r nat
                     (match_nat_type nat O
                      (λ (p : sttfa.etap (sttfa.p nat)), p)
                      (minus n m))
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq nat __
                        (match_nat_type nat O
                         (λ (p : sttfa.etap (sttfa.p nat)), p)
                         (minus n m)))
                     (logic.refl nat
                      (match_nat_type nat O
                       (λ (p : sttfa.etap (sttfa.p nat)), p)
                       (minus n m)))
                     (minus n (S m)) auto)))))))));
symbol not_eq_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (logic.eq nat n m))
           (connectives.Not (logic.eq nat (S n) (S m))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (connectives.Not (logic.eq nat n m))),
            logic.not_to_not (logic.eq nat (S n) (S m))
            (logic.eq nat n m)
            (λ (auto' : sttfa.eps (logic.eq nat (S n) (S m))),
               logic.rewrite_l nat m
               (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat __ m)
               (logic.refl nat m) n
               (logic.rewrite_r nat (pred (S n))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq nat m __)
                (logic.rewrite_r nat (S m)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq nat m (pred __))
                 (pred_Sn m) (S n) auto')
                n (pred_Sn n)))
            auto;
symbol not_eq_O_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.Not (logic.eq nat O (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.nmk (logic.eq nat O (S n))
        (λ (eqOS : sttfa.eps (logic.eq nat O (S n))),
           eq_match_nat_type_O sttfa.bool connectives.False
           (λ (p : sttfa.etap (sttfa.p nat)), connectives.True)
           (λ (y : sttfa.etap (sttfa.p sttfa.bool)), y)
           (logic.eq_ind_r nat (S n)
            (λ (x : sttfa.etap (sttfa.p nat)), not_zero x)
            (sym_eq_match_nat_type_S sttfa.bool connectives.False
             (λ (p : sttfa.etap (sttfa.p nat)), connectives.True) n
             (λ (y : sttfa.etap (sttfa.p sttfa.bool)), y) connectives.I)
            O eqOS));
symbol lt_to_not_zero
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt n m) (not_zero m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (Hlt : sttfa.eps (lt n m)),
            le_ind (S n)
            (λ (x_417 : sttfa.etap (sttfa.p nat)), not_zero x_417)
            (sym_eq_match_nat_type_S sttfa.bool connectives.False
             (λ (p : sttfa.etap (sttfa.p nat)), connectives.True) n
             (λ (y : sttfa.etap (sttfa.p sttfa.bool)), y) connectives.I)
            (λ (m0 : sttfa.etap (sttfa.p nat)),
               λ (_x_419 : sttfa.eps (le (S n) m0)),
                 λ (_x_421 : sttfa.eps (not_zero m0)),
                   sym_eq_match_nat_type_S sttfa.bool connectives.False
                   (λ (p : sttfa.etap (sttfa.p nat)), connectives.True)
                   m0 (λ (y : sttfa.etap (sttfa.p sttfa.bool)), y)
                   connectives.I)
            m Hlt;
symbol le_S_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m) (le (S n) (S m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (lenm : sttfa.eps (le n m)),
            le_ind n
            (λ (x_417 : sttfa.etap (sttfa.p nat)),
               le (S n) (S x_417))
            (le_n (S n))
            (λ (m0 : sttfa.etap (sttfa.p nat)),
               λ (_x_419 : sttfa.eps (le n m0)),
                 λ (_x_421 : sttfa.eps (le (S n) (S m0))),
                   le_S (S n) (S m0) _x_421)
            m lenm;
symbol le_O_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)), le O n))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind (le O) (le_n O)
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ (_x_368 : sttfa.eps (le O x_366)),
             le_S O x_366 _x_368)
        n;
symbol le_n_Sn
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)), le n (S n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)), le_S n n (le_n n);
symbol transitive_le : sttfa.eps (relations.transitive nat le)
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            λ (leab : sttfa.eps (le a b)),
              λ (lebc : sttfa.eps (le b c)),
                le_ind b
                (λ (x_417 : sttfa.etap (sttfa.p nat)), le a x_417)
                leab
                (λ (m : sttfa.etap (sttfa.p nat)),
                   λ (_x_419 : sttfa.eps (le b m)),
                     λ (_x_421 : sttfa.eps (le a m)),
                       le_S a m _x_421)
                c lebc;
symbol le_pred_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)), le (pred n) n))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           le (pred _x_365) _x_365)
        (eq_match_nat_type_O nat O
         (λ (p : sttfa.etap (sttfa.p nat)), p)
         (λ (y : sttfa.etap (sttfa.p nat)),
            le
            (match_nat_type nat O
             (λ (p : sttfa.etap (sttfa.p nat)), p) O)
            y)
         (le_n (pred O)))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ (_x_368 : sttfa.eps (le (pred x_366) x_366)),
             eq_match_nat_type_S nat O
             (λ (p : sttfa.etap (sttfa.p nat)), p) x_366
             (λ (y : sttfa.etap (sttfa.p nat)),
                le (pred (S x_366)) (S y))
             (le_n_Sn (pred (S x_366))))
        n;
symbol monotonic_pred
  : sttfa.eps (relations.monotonic nat le pred)
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (lenm : sttfa.eps (le n m)),
            le_ind n
            (λ (x_417 : sttfa.etap (sttfa.p nat)),
               le (pred n) (pred x_417))
            (le_n (pred n))
            (λ (m0 : sttfa.etap (sttfa.p nat)),
               λ (_x_419 : sttfa.eps (le n m0)),
                 λ (_x_421 : sttfa.eps (le (pred n) (pred m0))),
                   transitive_le (pred n) n (pred (S m0))
                   (le_pred_n n)
                   (sym_eq_match_nat_type_S nat O
                    (λ (p : sttfa.etap (sttfa.p nat)), p) m0
                    (λ (y : sttfa.etap (sttfa.p nat)), le n y)
                    _x_419))
            m lenm;
symbol le_S_S_to_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le (S n) (S m)) (le n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (le (S n) (S m))),
            eq_match_nat_type_S nat O
            (λ (p : sttfa.etap (sttfa.p nat)), p) m
            (λ (y : sttfa.etap (sttfa.p nat)), le n y)
            (eq_match_nat_type_S nat O
             (λ (p : sttfa.etap (sttfa.p nat)), p) n
             (λ (y : sttfa.etap (sttfa.p nat)),
                le y
                (match_nat_type nat O
                 (λ (p : sttfa.etap (sttfa.p nat)), p) (S m)))
             (monotonic_pred (S n) (S m) auto));
symbol monotonic_le_plus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        relations.monotonic nat le
        (λ (m : sttfa.etap (sttfa.p nat)), plus n m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (a : sttfa.etap (sttfa.p nat)),
          λ (b : sttfa.etap (sttfa.p nat)),
            nat_ind
            (λ (_x_365 : sttfa.etap (sttfa.p nat)),
               sttfa.impl (le a b)
               (le (plus _x_365 a) (plus _x_365 b)))
            (sym_eq_plus O
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.impl (le a b) (le (plus O a) (y b)))
             (sym_eq_plus O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.impl (le a b)
                 (le (y a)
                  (filter_nat_type (sttfa.arrow nat nat)
                   plus_body O b)))
              (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
               plus_body
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.impl (le a b)
                  (le (y a)
                   (filter_nat_type (sttfa.arrow nat nat)
                    plus_body O b)))
               (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                plus_body
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.impl (le a b)
                   (le (plus_body O a) (y b)))
                (sym_eq_plus_body_O
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.impl (le a b)
                    (le (plus_body O a) (y b)))
                 (sym_eq_plus_body_O
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.impl (le a b) (le (y a) b))
                  (λ (auto : sttfa.eps (le a b)), auto)))))))
            (λ (m : sttfa.etap (sttfa.p nat)),
               λ
                 (
                 H : sttfa.eps
                     (sttfa.impl (le a b)
                      (le (plus m a) (plus m b)))
                 ),
                 λ (leab : sttfa.eps (le a b)),
                   sym_eq_plus (S m)
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ), le (plus (S m) a) (y b))
                   (sym_eq_plus (S m)
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       le (y a)
                       (filter_nat_type (sttfa.arrow nat nat)
                        plus_body (S m) b))
                    (sym_eq_filter_nat_type_S
                     (sttfa.arrow nat nat) plus_body m
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        le (y a)
                        (filter_nat_type (sttfa.arrow nat nat)
                         plus_body (S m) b))
                     (sym_eq_filter_nat_type_S
                      (sttfa.arrow nat nat) plus_body m
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ), le (plus_body (S m) a) (y b))
                      (sym_eq_plus_body_S m
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ), le (plus_body (S m) a) (y b))
                       (sym_eq_plus_body_S m
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ), le (y a) (S (plus m b)))
                        (le_S_S (plus m a) (plus m b) (H leab))))))))
            n;
symbol monotonic_le_plus_l
  : sttfa.eps
    (sttfa.forall nat
     (λ (m : sttfa.etap (sttfa.p nat)),
        relations.monotonic nat le
        (λ (n : sttfa.etap (sttfa.p nat)), plus n m)))
  ≔ λ (m : sttfa.etap (sttfa.p nat)),
        λ (x : sttfa.etap (sttfa.p nat)),
          λ (y : sttfa.etap (sttfa.p nat)),
            λ (auto : sttfa.eps (le x y)),
              logic.eq_coerc (le (plus m x) (plus m y))
              (le (plus x m) (plus y m))
              (monotonic_le_plus_r m x y auto)
              (logic.rewrite_r nat (plus m x)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool (le (plus m x) (plus m y))
                  (le __ (plus y m)))
               (logic.rewrite_r nat (plus m y)
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (le (plus m x) (plus m y))
                   (le (plus m x) __))
                (logic.refl sttfa.bool (le (plus m x) (plus m y)))
                (plus y m) (commutative_plus y m))
               (plus x m) (commutative_plus x m));
symbol le_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n1 : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n2 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m1 : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (m2 : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (le n1 n2)
                 (sttfa.impl (le m1 m2)
                  (le (plus n1 m1) (plus n2 m2))))))))
  ≔ λ (n1 : sttfa.etap (sttfa.p nat)),
        λ (n2 : sttfa.etap (sttfa.p nat)),
          λ (m1 : sttfa.etap (sttfa.p nat)),
            λ (m2 : sttfa.etap (sttfa.p nat)),
              λ (len : sttfa.eps (le n1 n2)),
                λ (lem : sttfa.eps (le m1 m2)),
                  transitive_le (plus n1 m1) (plus n1 m2)
                  (plus n2 m2) (monotonic_le_plus_r n1 m1 m2 lem)
                  (monotonic_le_plus_l m2 n1 n2 len);
symbol le_plus_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)), le m (plus n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          logic.eq_coerc (le (plus O m) (plus n m))
          (le m (plus n m))
          (monotonic_le_plus_l m O n (le_O_n n))
          (logic.rewrite_l nat m
           (λ (__ : sttfa.etap (sttfa.p nat)),
              logic.eq sttfa.bool (le __ (plus n m))
              (le m (plus n m)))
           (logic.refl sttfa.bool (le m (plus n m)))
           (plus O m) (plus_O_n m));
symbol le_plus_b
  : sttfa.eps
    (sttfa.forall nat
     (λ (b : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le (plus n b) m) (le n m)))))
  ≔ λ (b : sttfa.etap (sttfa.p nat)),
        λ (n : sttfa.etap (sttfa.p nat)),
          λ (m : sttfa.etap (sttfa.p nat)),
            λ (auto : sttfa.eps (le (plus n b) m)),
              transitive_le n (plus n b) m
              (logic.eq_coerc (le n (plus b n))
               (le n (plus n b)) (le_plus_n b n)
               (logic.rewrite_r nat (plus b n)
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (le n (plus b n))
                   (le n __))
                (logic.refl sttfa.bool (le n (plus b n)))
                (plus n b) (commutative_plus n b)))
              auto;
symbol le_plus_n_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)), le m (plus m n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          logic.eq_coerc (le m (plus n m)) (le m (plus m n))
          (le_plus_n n m)
          (logic.rewrite_r nat (plus n m)
           (λ (__ : sttfa.etap (sttfa.p nat)),
              logic.eq sttfa.bool (le m (plus n m)) (le m __))
           (logic.refl sttfa.bool (le m (plus n m))) (plus m n)
           (commutative_plus m n));
symbol le_plus_to_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le (plus a n) (plus a m)) (le n m)))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (m : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (le (plus _x_365 n) (plus _x_365 m))
                 (le n m))))
        (λ (n : sttfa.etap (sttfa.p nat)),
           λ (m : sttfa.etap (sttfa.p nat)),
             sym_eq_plus O
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.impl (le (plus O n) (y m)) (le n m))
             (sym_eq_plus O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.impl
                 (le (y n)
                  (filter_nat_type (sttfa.arrow nat nat)
                   plus_body O m))
                 (le n m))
              (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
               plus_body
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.impl
                  (le (y n)
                   (filter_nat_type (sttfa.arrow nat nat)
                    plus_body O m))
                  (le n m))
               (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                plus_body
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.impl (le (plus_body O n) (y m))
                   (le n m))
                (sym_eq_plus_body_O
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.impl (le (plus_body O n) (y m))
                    (le n m))
                 (sym_eq_plus_body_O
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.impl (le (y n) m) (le n m))
                  (λ (auto : sttfa.eps (le n m)), auto)))))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.forall nat
                       (λ (n : sttfa.etap (sttfa.p nat)),
                          sttfa.forall nat
                          (λ (m : sttfa.etap (sttfa.p nat)),
                             sttfa.impl
                             (le (plus x_366 n) (plus x_366 m))
                             (le n m))))
             ),
             λ (n : sttfa.etap (sttfa.p nat)),
               λ (m : sttfa.etap (sttfa.p nat)),
                 sym_eq_plus (S x_366)
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.impl (le (plus (S x_366) n) (y m))
                    (le n m))
                 (sym_eq_plus (S x_366)
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.impl
                     (le (y n)
                      (filter_nat_type (sttfa.arrow nat nat)
                       plus_body (S x_366) m))
                     (le n m))
                  (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                   plus_body x_366
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      sttfa.impl
                      (le (y n)
                       (filter_nat_type (sttfa.arrow nat nat)
                        plus_body (S x_366) m))
                      (le n m))
                   (sym_eq_filter_nat_type_S
                    (sttfa.arrow nat nat) plus_body x_366
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       sttfa.impl
                       (le (plus_body (S x_366) n) (y m))
                       (le n m))
                    (sym_eq_plus_body_S x_366
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        sttfa.impl
                        (le (plus_body (S x_366) n) (y m))
                        (le n m))
                     (sym_eq_plus_body_S x_366
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         sttfa.impl (le (y n) (S (plus x_366 m)))
                         (le n m))
                      (λ
                         (
                         auto : sttfa.eps
                                (le (S (plus x_366 n))
                                 (S (plus x_366 m)))
                         ),
                         logic.eq_coerc
                         (le (pred (S n)) (pred (S m)))
                         (le n m)
                         (monotonic_pred (S n) (S m)
                          (_x_368 (S n) (S m)
                           (logic.eq_coerc
                            (le (S (plus x_366 n))
                             (S (plus x_366 m)))
                            (le (plus x_366 (S n))
                             (plus x_366 (S m)))
                            auto
                            (logic.rewrite_r nat
                             (plus x_366 (S n))
                             (λ (__ : sttfa.etap (sttfa.p nat)),
                                logic.eq sttfa.bool
                                (le __ (S (plus x_366 m)))
                                (le (plus x_366 (S n))
                                 (plus x_366 (S m))))
                             (logic.rewrite_r nat
                              (plus x_366 (S m))
                              (λ (__ : sttfa.etap (sttfa.p nat)),
                                 logic.eq sttfa.bool
                                 (le (plus x_366 (S n)) __)
                                 (le (plus x_366 (S n))
                                  (plus x_366 (S m))))
                              (logic.refl sttfa.bool
                               (le (plus x_366 (S n))
                                (plus x_366 (S m))))
                              (S (plus x_366 m))
                              (plus_n_Sm x_366 m))
                             (S (plus x_366 n))
                             (plus_n_Sm x_366 n)))))
                         (logic.rewrite_l nat n
                          (λ (__ : sttfa.etap (sttfa.p nat)),
                             logic.eq sttfa.bool
                             (le __ (pred (S m))) (le n m))
                          (logic.rewrite_l nat m
                           (λ (__ : sttfa.etap (sttfa.p nat)),
                              logic.eq sttfa.bool (le n __) (le n m))
                           (logic.refl sttfa.bool (le n m))
                           (pred (S m)) (pred_Sn m))
                          (pred (S n)) (pred_Sn n)))))))))
        a;
symbol le_plus_to_le_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le (plus n a) (plus m a)) (le n m)))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (n : sttfa.etap (sttfa.p nat)),
          λ (m : sttfa.etap (sttfa.p nat)),
            λ (auto : sttfa.eps (le (plus n a) (plus m a))),
              le_plus_to_le a n m
              (logic.eq_coerc (le (plus n a) (plus m a))
               (le (plus a n) (plus a m)) auto
               (logic.rewrite_r nat (plus a n)
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (le __ (plus m a))
                   (le (plus a n) (plus a m)))
                (logic.rewrite_r nat (plus a m)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (le (plus a n) __)
                    (le (plus a n) (plus a m)))
                 (logic.refl sttfa.bool
                  (le (plus a n) (plus a m)))
                 (plus m a) (commutative_plus m a))
                (plus n a) (commutative_plus n a)));
symbol monotonic_le_times_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        relations.monotonic nat le
        (λ (m : sttfa.etap (sttfa.p nat)), times n m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (x : sttfa.etap (sttfa.p nat)),
          λ (y : sttfa.etap (sttfa.p nat)),
            λ (lexy : sttfa.eps (le x y)),
              nat_ind
              (λ (_x_365 : sttfa.etap (sttfa.p nat)),
                 le (times _x_365 x) (times _x_365 y))
              (sym_eq_times O
               (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  le (times O x) (z y))
               (sym_eq_times O
                (λ (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   le (z x)
                   (filter_nat_type (sttfa.arrow nat nat)
                    times_body O y))
                (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                 times_body
                 (λ
                    (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    le (z x)
                    (filter_nat_type (sttfa.arrow nat nat)
                     times_body O y))
                 (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
                  times_body
                  (λ
                     (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     le (times_body O x) (z y))
                  (sym_eq_times_body_O
                   (λ
                      (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ), le (times_body O x) (z y))
                   (sym_eq_times_body_O
                    (λ
                       (
                       z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ), le (z x) O)
                    (le_O_n O)))))))
              (λ (a : sttfa.etap (sttfa.p nat)),
                 λ
                   (lea : sttfa.eps (le (times a x) (times a y))),
                   sym_eq_times (S a)
                   (λ
                      (z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ), le (times (S a) x) (z y))
                   (sym_eq_times (S a)
                    (λ
                       (
                       z : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       le (z x)
                       (filter_nat_type (sttfa.arrow nat nat)
                        times_body (S a) y))
                    (sym_eq_filter_nat_type_S
                     (sttfa.arrow nat nat) times_body a
                     (λ
                        (
                        z : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        le (z x)
                        (filter_nat_type (sttfa.arrow nat nat)
                         times_body (S a) y))
                     (sym_eq_filter_nat_type_S
                      (sttfa.arrow nat nat) times_body a
                      (λ
                         (
                         z : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ), le (times_body (S a) x) (z y))
                      (sym_eq_times_body_S a
                       (λ
                          (
                          z : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ), le (times_body (S a) x) (z y))
                       (sym_eq_times_body_S a
                        (λ
                           (
                           z : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ), le (z x) (plus y (times a y)))
                        (le_plus x y (times a x) (times a y) lexy
                         lea)))))))
              n;
symbol le_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n1 : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n2 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m1 : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (m2 : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (le n1 n2)
                 (sttfa.impl (le m1 m2)
                  (le (times n1 m1) (times n2 m2))))))))
  ≔ λ (n1 : sttfa.etap (sttfa.p nat)),
        λ (n2 : sttfa.etap (sttfa.p nat)),
          λ (m1 : sttfa.etap (sttfa.p nat)),
            λ (m2 : sttfa.etap (sttfa.p nat)),
              λ (len : sttfa.eps (le n1 n2)),
                λ (lem : sttfa.eps (le m1 m2)),
                  transitive_le (times n1 m1) (times n1 m2)
                  (times n2 m2) (monotonic_le_times_r n1 m1 m2 lem)
                  (logic.eq_coerc
                   (le (times m2 n1) (times m2 n2))
                   (le (times n1 m2) (times n2 m2))
                   (monotonic_le_times_r m2 n1 n2 len)
                   (logic.rewrite_r nat (times n1 m2)
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq sttfa.bool (le __ (times m2 n2))
                       (le (times n1 m2) (times n2 m2)))
                    (logic.rewrite_r nat (times n2 m2)
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq sttfa.bool (le (times n1 m2) __)
                        (le (times n1 m2) (times n2 m2)))
                     (logic.refl sttfa.bool
                      (le (times n1 m2) (times n2 m2)))
                     (times m2 n2) (commutative_times m2 n2))
                    (times m2 n1) (commutative_times m2 n1)));
symbol le_plus_minus_m_m
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           le n (plus (minus n m) m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (m : sttfa.etap (sttfa.p nat)),
              le _x_365 (plus (minus _x_365 m) m)))
        (sym_eq_minus O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
            sttfa.forall nat
            (λ (m : sttfa.etap (sttfa.p nat)),
               le O (plus (y m) m)))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat nat)
          minus_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
             sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)),
                le O (plus (y m) m)))
          (sym_eq_minus_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.forall nat
              (λ (m : sttfa.etap (sttfa.p nat)),
                 le O (plus (y m) m)))
           (λ (m : sttfa.etap (sttfa.p nat)), le_plus_n_r m O))))
        (λ (a : sttfa.etap (sttfa.p nat)),
           λ
             (
             Hind : sttfa.eps
                    (sttfa.forall nat
                     (λ (m : sttfa.etap (sttfa.p nat)),
                        le a (plus (minus a m) m)))
             ),
             λ (m : sttfa.etap (sttfa.p nat)),
               match_nat_prop
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  le (S a) (plus (minus (S a) __) __))
               (sym_eq_minus (S a)
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   le (S a) (plus (y O) O))
                (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                 minus_body a
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    le (S a) (plus (y O) O))
                 (sym_eq_minus_body_S a
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     le (S a) (plus (y O) O))
                  (sym_eq_match_nat_type_O nat (S a)
                   (λ (q : sttfa.etap (sttfa.p nat)), minus a q)
                   (λ (y : sttfa.etap (sttfa.p nat)),
                      le (S a) (plus y O))
                   (le_plus_n_r O (S a))))))
               (λ (n0 : sttfa.etap (sttfa.p nat)),
                  sym_eq_minus (S a)
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     le (S a) (plus (y (S n0)) (S n0)))
                  (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                   minus_body a
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      le (S a) (plus (y (S n0)) (S n0)))
                   (sym_eq_minus_body_S a
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       le (S a) (plus (y (S n0)) (S n0)))
                    (sym_eq_match_nat_type_S nat (S a)
                     (λ (q : sttfa.etap (sttfa.p nat)), minus a q)
                     n0
                     (λ (y : sttfa.etap (sttfa.p nat)),
                        le (S a) (plus y (S n0)))
                     (logic.eq_coerc
                      (le (S a)
                       (S (plus (minus a n0) n0)))
                      (le (S a)
                       (plus (minus a n0) (S n0)))
                      (le_S_S a (plus (minus a n0) n0) (Hind n0))
                      (logic.rewrite_r nat
                       (plus (minus a n0) (S n0))
                       (λ (__ : sttfa.etap (sttfa.p nat)),
                          logic.eq sttfa.bool (le (S a) __)
                          (le (S a)
                           (plus (minus a n0) (S n0))))
                       (logic.refl sttfa.bool
                        (le (S a)
                         (plus (minus a n0) (S n0))))
                       (S (plus (minus a n0) n0))
                       (plus_n_Sm (minus a n0) n0)))))))
               m)
        n;
symbol le_plus_to_minus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (b : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (c : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le (plus a b) c) (le a (minus c b))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            λ (H : sttfa.eps (le (plus a b) c)),
              le_plus_to_le_r b a (minus c b)
              (transitive_le (plus a b) c
               (plus (minus c b) b) H (le_plus_minus_m_m c b));
symbol lt_to_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (x : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (y : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt x y) (le x y))))
  ≔ λ (x : sttfa.etap (sttfa.p nat)),
        λ (y : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (lt x y)),
            le_plus_b (S O) x y
            (logic.eq_coerc (le (S x) y)
             (le (plus x (S O)) y) auto
             (logic.rewrite_r nat (plus x (S O))
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le __ y)
                 (le (plus x (S O)) y))
              (logic.refl sttfa.bool (le (plus x (S O)) y))
              (S x)
              (logic.rewrite_r nat (plus x O)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (S __) (plus x (S O)))
               (plus_n_Sm x O) x (plus_n_O x))));
symbol transitive_lt : sttfa.eps (relations.transitive nat lt)
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            λ (ltab : sttfa.eps (lt a b)),
              λ (ltbc : sttfa.eps (lt b c)),
                le_ind (S b)
                (λ (x_417 : sttfa.etap (sttfa.p nat)), lt a x_417)
                (le_S (S a) b ltab)
                (λ (m : sttfa.etap (sttfa.p nat)),
                   λ (_x_419 : sttfa.eps (le (S b) m)),
                     λ (_x_421 : sttfa.eps (lt a m)),
                       le_S (S a) m _x_421)
                c ltbc;
symbol lt_to_le_to_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (lt n m) (sttfa.impl (le m p) (lt n p))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (H : sttfa.eps (lt n m)),
              λ (H1 : sttfa.eps (le m p)),
                le_ind m
                (λ (x_417 : sttfa.etap (sttfa.p nat)), lt n x_417) H
                (λ (m0 : sttfa.etap (sttfa.p nat)),
                   λ (_x_419 : sttfa.eps (le m m0)),
                     λ (_x_421 : sttfa.eps (lt n m0)),
                       transitive_lt n m0 (S m0) _x_421
                       (logic.eq_coerc
                        (le (S m0) (plus O (S m0)))
                        (le (S m0) (S m0))
                        (le_plus_n O (S m0))
                        (logic.rewrite_l nat (S m0)
                         (λ (__ : sttfa.etap (sttfa.p nat)),
                            logic.eq sttfa.bool (le (S m0) __)
                            (le (S m0) (S m0)))
                         (logic.refl sttfa.bool
                          (le (S m0) (S m0)))
                         (plus O (S m0))
                         (plus_O_n (S m0)))))
                p H1;
symbol le_to_lt_to_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le n m) (sttfa.impl (lt m p) (lt n p))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (H : sttfa.eps (le n m)),
              le_ind n
              (λ (x_417 : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (lt x_417 p) (lt n p))
              (λ (auto : sttfa.eps (lt n p)), auto)
              (λ (m0 : sttfa.etap (sttfa.p nat)),
                 λ (_x_419 : sttfa.eps (le n m0)),
                   λ
                     (
                     _x_421 : sttfa.eps
                              (sttfa.impl (lt m0 p) (lt n p))
                     ),
                     λ (auto : sttfa.eps (lt (S m0) p)),
                       _x_421
                       (transitive_lt m0 (S m0) p
                        (logic.eq_coerc
                         (le (S m0) (plus O (S m0)))
                         (le (S m0) (S m0))
                         (le_plus_n O (S m0))
                         (logic.rewrite_l nat (S m0)
                          (λ (__ : sttfa.etap (sttfa.p nat)),
                             logic.eq sttfa.bool (le (S m0) __)
                             (le (S m0) (S m0)))
                          (logic.refl sttfa.bool
                           (le (S m0) (S m0)))
                          (plus O (S m0))
                          (plus_O_n (S m0))))
                        auto))
              m H;
symbol lt_S_to_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt (S n) m) (lt n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (lt (S n) m)),
            transitive_lt n (S n) m
            (logic.eq_coerc (le (S n) (plus O (S n)))
             (le (S n) (S n)) (le_plus_n O (S n))
             (logic.rewrite_l nat (S n)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le (S n) __)
                 (le (S n) (S n)))
              (logic.refl sttfa.bool (le (S n) (S n)))
              (plus O (S n)) (plus_O_n (S n))))
            auto;
symbol ltn_to_ltO
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt n m) (lt O m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (lt n m)),
            lt_to_le_to_lt O (S n) m
            (logic.eq_coerc (le (S O) (plus n (S O)))
             (le (S O) (S n)) (le_plus_n n (S O))
             (logic.rewrite_l nat (S n)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le (S O) __)
                 (le (S O) (S n)))
              (logic.refl sttfa.bool (le (S O) (S n)))
              (plus n (S O))
              (logic.rewrite_r nat (plus n O)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (S __) (plus n (S O)))
               (plus_n_Sm n O) n (plus_n_O n))))
            auto;
symbol lt_O_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)), lt O (S n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        ltn_to_ltO n (S n)
        (logic.eq_coerc (le (S n) (plus O (S n)))
         (le (S n) (S n)) (le_plus_n O (S n))
         (logic.rewrite_l nat (S n)
          (λ (__ : sttfa.etap (sttfa.p nat)),
             logic.eq sttfa.bool (le (S n) __)
             (le (S n) (S n)))
          (logic.refl sttfa.bool (le (S n) (S n)))
          (plus O (S n)) (plus_O_n (S n))));
symbol monotonic_lt_plus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        relations.monotonic nat lt
        (λ (m : sttfa.etap (sttfa.p nat)), plus n m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (x : sttfa.etap (sttfa.p nat)),
          λ (y : sttfa.etap (sttfa.p nat)),
            λ (auto : sttfa.eps (lt x y)),
              logic.eq_coerc (le (plus n (S x)) (plus n y))
              (le (S (plus n x)) (plus n y))
              (monotonic_le_plus_r n (S x) y auto)
              (logic.rewrite_r nat (plus n (S x))
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool
                  (le (plus n (S x)) (plus n y))
                  (le __ (plus n y)))
               (logic.refl sttfa.bool
                (le (plus n (S x)) (plus n y)))
               (S (plus n x)) (plus_n_Sm n x));
symbol monotonic_lt_plus_l
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        relations.monotonic nat lt
        (λ (m : sttfa.etap (sttfa.p nat)), plus m n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (x : sttfa.etap (sttfa.p nat)),
          λ (y : sttfa.etap (sttfa.p nat)),
            λ (auto : sttfa.eps (lt x y)),
              logic.eq_coerc (le (plus n (S x)) (plus n y))
              (le (S (plus x n)) (plus y n))
              (monotonic_le_plus_r n (S x) y auto)
              (logic.rewrite_r nat (plus n x)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool
                  (le (plus n (S x)) (plus n y))
                  (le (S __) (plus y n)))
               (logic.rewrite_r nat (plus n (S x))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool
                   (le (plus n (S x)) (plus n y))
                   (le __ (plus y n)))
                (logic.rewrite_r nat (plus n y)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool
                    (le (plus n (S x)) (plus n y))
                    (le (plus n (S x)) __))
                 (logic.refl sttfa.bool
                  (le (plus n (S x)) (plus n y)))
                 (plus y n) (commutative_plus y n))
                (S (plus n x)) (plus_n_Sm n x))
               (plus x n) (commutative_plus x n));
symbol monotonic_lt_times_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (c : sttfa.etap (sttfa.p nat)),
        sttfa.impl (lt O c)
        (relations.monotonic nat lt
         (λ (t : sttfa.etap (sttfa.p nat)), times c t))))
  ≔ λ (c : sttfa.etap (sttfa.p nat)),
        λ (posc : sttfa.eps (lt O c)),
          λ (n : sttfa.etap (sttfa.p nat)),
            λ (m : sttfa.etap (sttfa.p nat)),
              λ (ltnm : sttfa.eps (lt n m)),
                le_ind (S n)
                (λ (x_417 : sttfa.etap (sttfa.p nat)),
                   lt (times c n) (times c x_417))
                (logic.eq_coerc
                 (le (S (plus O (times c n)))
                  (plus c (times c n)))
                 (le (S (times c n)) (times c (S n)))
                 (monotonic_lt_plus_l (times c n) O c posc)
                 (logic.rewrite_r nat
                  (plus O (S (times c n)))
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool
                     (le __ (plus c (times c n)))
                     (le (S (times c n)) (times c (S n))))
                  (logic.rewrite_l nat (plus c (times c n))
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq sttfa.bool
                      (le (plus O (S (times c n)))
                       (plus c (times c n)))
                      (le (S (times c n)) __))
                   (logic.rewrite_l nat (S (times c n))
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq sttfa.bool
                       (le __ (plus c (times c n)))
                       (le (S (times c n))
                        (plus c (times c n))))
                    (logic.refl sttfa.bool
                     (le (S (times c n))
                      (plus c (times c n))))
                    (plus O (S (times c n)))
                    (plus_O_n (S (times c n))))
                   (times c (S n)) (times_n_Sm c n))
                  (S (plus O (times c n)))
                  (plus_n_Sm O (times c n))))
                (λ (a : sttfa.etap (sttfa.p nat)),
                   λ (__ : sttfa.eps (le (S n) a)),
                     λ
                       (
                       lt1 : sttfa.eps
                             (le (S (times c n)) (times c a))
                       ),
                       transitive_le (S (times c n))
                       (times c a) (times c (S a)) lt1
                       (logic.eq_coerc
                        (le (times c a) (plus (times c a) c))
                        (le (times c a) (times c (S a)))
                        (le_plus_n_r c (times c a))
                        (logic.rewrite_l nat (plus c (times c a))
                         (λ (__1 : sttfa.etap (sttfa.p nat)),
                            logic.eq sttfa.bool
                            (le (times c a)
                             (plus (times c a) c))
                            (le (times c a) __1))
                         (logic.rewrite_r nat
                          (plus c (times c a))
                          (λ (__1 : sttfa.etap (sttfa.p nat)),
                             logic.eq sttfa.bool (le (times c a) __1)
                             (le (times c a)
                              (plus c (times c a))))
                          (logic.refl sttfa.bool
                           (le (times c a)
                            (plus c (times c a))))
                          (plus (times c a) c)
                          (commutative_plus (times c a) c))
                         (times c (S a)) (times_n_Sm c a))))
                m ltnm;
symbol monotonic_lt_times_l
  : sttfa.eps
    (sttfa.forall nat
     (λ (c : sttfa.etap (sttfa.p nat)),
        sttfa.impl (lt O c)
        (relations.monotonic nat lt
         (λ (t : sttfa.etap (sttfa.p nat)), times t c))))
  ≔ λ (c : sttfa.etap (sttfa.p nat)),
        λ (auto : sttfa.eps (lt O c)),
          λ (x : sttfa.etap (sttfa.p nat)),
            λ (y : sttfa.etap (sttfa.p nat)),
              λ (auto' : sttfa.eps (lt x y)),
                logic.eq_coerc
                (le (S (times c x)) (times c y))
                (le (S (times x c)) (times y c))
                (monotonic_lt_times_r c auto x y auto')
                (logic.rewrite_r nat (times c x)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool
                    (le (S (times c x)) (times c y))
                    (le (S __) (times y c)))
                 (logic.rewrite_r nat (times c y)
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool
                     (le (S (times c x)) (times c y))
                     (le (S (times c x)) __))
                  (logic.refl sttfa.bool
                   (le (S (times c x)) (times c y)))
                  (times y c) (commutative_times y c))
                 (times x c) (commutative_times x c));
symbol lt_to_le_to_lt_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (q : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (lt n m)
                 (sttfa.impl (le p q)
                  (sttfa.impl (lt O q)
                   (lt (times n p) (times m q)))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (q : sttfa.etap (sttfa.p nat)),
              λ (ltnm : sttfa.eps (lt n m)),
                λ (lepq : sttfa.eps (le p q)),
                  λ (posq : sttfa.eps (lt O q)),
                    le_to_lt_to_lt (times n p) (times n q)
                    (times m q) (monotonic_le_times_r n p q lepq)
                    (monotonic_lt_times_l q posq n m ltnm);
symbol lt_times
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.forall nat
              (λ (q : sttfa.etap (sttfa.p nat)),
                 sttfa.impl (lt n m)
                 (sttfa.impl (lt p q)
                  (lt (times n p) (times m q))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (q : sttfa.etap (sttfa.p nat)),
              λ (ltnm : sttfa.eps (lt n m)),
                λ (ltpq : sttfa.eps (lt p q)),
                  lt_to_le_to_lt_times n m p q ltnm
                  (lt_to_le p q ltpq) (ltn_to_ltO p q ltpq);
symbol lt_plus_to_minus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (b : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (c : sttfa.etap (sttfa.p nat)),
              sttfa.impl (lt (plus a b) c) (lt a (minus c b))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            λ (H : sttfa.eps (lt (plus a b) c)),
              le_plus_to_minus_r (S a) b c
              (sym_eq_plus (S a)
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  le (y b) c)
               (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                plus_body a
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   le (y b) c)
                (sym_eq_plus_body_S a
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    le (y b) c)
                 H)));
symbol lt_plus_Sn_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (x : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              lt a (plus (plus a x) (S n))))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (x : sttfa.etap (sttfa.p nat)),
          λ (n : sttfa.etap (sttfa.p nat)),
            logic.eq_coerc
            (le (S a) (S (plus (plus a x) n)))
            (le (S a) (plus (plus a x) (S n)))
            (le_S_S a (plus (plus a x) n)
             (logic.eq_coerc (le a (plus a (plus x n)))
              (le a (plus (plus a x) n))
              (le_plus_n_r (plus x n) a)
              (logic.rewrite_r nat (plus n (plus a x))
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool (le a (plus a (plus x n)))
                  (le a __))
               (logic.rewrite_r nat (plus a (plus n x))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (le a (plus a (plus x n)))
                   (le a __))
                (logic.rewrite_r nat (plus x n)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool
                    (le a (plus a (plus x n)))
                    (le a (plus a __)))
                 (logic.refl sttfa.bool
                  (le a (plus a (plus x n))))
                 (plus n x) (commutative_plus n x))
                (plus n (plus a x))
                (logic.rewrite_l nat (plus (plus a n) x)
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (plus n (plus a x)) __)
                 (assoc_plus1 x a n) (plus a (plus n x))
                 (associative_plus a n x)))
               (plus (plus a x) n)
               (commutative_plus (plus a x) n))))
            (logic.rewrite_r nat (plus a (plus x (S n)))
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq sttfa.bool
                (le (S a) (S (plus (plus a x) n)))
                (le (S a) __))
             (logic.rewrite_r nat (plus (plus a x) (S n))
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le (S a) __)
                 (le (S a) (plus a (plus x (S n)))))
              (logic.rewrite_r nat (plus a (plus x (S n)))
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool (le (S a) __)
                  (le (S a) (plus a (plus x (S n)))))
               (logic.refl sttfa.bool
                (le (S a) (plus a (plus x (S n)))))
               (plus (plus a x) (S n))
               (associative_plus a x (S n)))
              (S (plus (plus a x) n))
              (plus_n_Sm (plus a x) n))
             (plus (plus a x) (S n))
             (associative_plus a x (S n)));
symbol not_le_Sn_O
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.Not (le (S n) O)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.nmk (le (S n) O)
        (λ (Hlen0 : sttfa.eps (le (S n) O)),
           eq_match_nat_type_O sttfa.bool connectives.False
           (λ (p : sttfa.etap (sttfa.p nat)), connectives.True)
           (λ (y : sttfa.etap (sttfa.p sttfa.bool)), y)
           (lt_to_not_zero n O Hlen0));
symbol not_le_to_not_le_S_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (le n m))
           (connectives.Not (le (S n) (S m))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (connectives.Not (le n m))),
            logic.not_to_not (le (S n) (S m)) (le n m)
            (λ (auto' : sttfa.eps (le (S n) (S m))),
               logic.eq_coerc
               (le (pred (S n)) (pred (S m)))
               (le n m) (monotonic_pred (S n) (S m) auto')
               (logic.rewrite_l nat n
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (le __ (pred (S m)))
                   (le n m))
                (logic.rewrite_l nat m
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (le n __) (le n m))
                 (logic.refl sttfa.bool (le n m)) (pred (S m))
                 (pred_Sn m))
                (pred (S n)) (pred_Sn n)))
            auto;
symbol not_le_S_S_to_not_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (le (S n) (S m)))
           (connectives.Not (le n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ
            (auto : sttfa.eps (connectives.Not (le (S n) (S m)))),
            logic.not_to_not (le n m) (le (S n) (S m))
            (λ (auto' : sttfa.eps (le n m)), le_S_S n m auto') auto;
symbol not_le_Sn_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.Not (le (S n) n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           connectives.Not (le (S _x_365) _x_365))
        (not_le_Sn_O O)
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (connectives.Not (le (S x_366) x_366))
             ), not_le_to_not_le_S_S (S x_366) x_366 _x_368)
        n;
symbol lt_to_not_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt n m) (connectives.Not (le m n)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (Hltnm : sttfa.eps (lt n m)),
            le_ind (S n)
            (λ (x_417 : sttfa.etap (sttfa.p nat)),
               connectives.Not (le x_417 n))
            (not_le_Sn_n n)
            (λ (m0 : sttfa.etap (sttfa.p nat)),
               λ (_x_419 : sttfa.eps (le (S n) m0)),
                 λ (_x_421 : sttfa.eps (connectives.Not (le m0 n))),
                   logic.not_to_not (le (S m0) n) (le m0 n)
                   (λ (auto : sttfa.eps (le (S m0) n)),
                      lt_to_le m0 n auto)
                   _x_421)
            m Hltnm;
symbol not_le_to_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (le n m)) (lt m n))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (le __ _0)) (lt _0 __))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (abs : sttfa.eps (connectives.Not (le O n))),
           connectives.falsity (lt n O)
           (logic.absurd (le O n)
            (logic.eq_coerc (le O (plus n O))
             (le O n) (le_plus_n n O)
             (logic.rewrite_l nat n
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le O __) (le O n))
              (logic.refl sttfa.bool (le O n)) (plus n O)
              (plus_n_O n)))
            abs))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (auto : sttfa.eps (connectives.Not (le (S n) O))),
           lt_O_S n)
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           λ
             (
             Hind : sttfa.eps
                    (sttfa.impl (connectives.Not (le n m)) (lt m n))
             ),
             λ
               (
               HnotleSS : sttfa.eps
                          (connectives.Not (le (S n) (S m)))
               ),
               le_S_S (S m) n
               (Hind (not_le_S_S_to_not_le n m HnotleSS)));
symbol not_lt_to_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (lt n m)) (le m n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (H : sttfa.eps (connectives.Not (lt n m))),
            le_S_S_to_le m n
            (not_le_to_lt (S n) m
             (logic.not_to_not (le (S n) m) (lt n m)
              (λ (auto : sttfa.eps (le (S n) m)), auto) H));
symbol le_to_not_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m) (connectives.Not (lt m n)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (H : sttfa.eps (le n m)),
            lt_to_not_le n (S m)
            (le_to_lt_to_lt n m (S m) H
             (logic.eq_coerc (le (S m) (plus O (S m)))
              (le (S m) (S m)) (le_plus_n O (S m))
              (logic.rewrite_l nat (S m)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool (le (S m) __)
                  (le (S m) (S m)))
               (logic.refl sttfa.bool (le (S m) (S m)))
               (plus O (S m)) (plus_O_n (S m)))));
symbol decidable_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)), logic.decidable (le n m))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           logic.decidable (le __ _0))
      (λ (n : sttfa.etap (sttfa.p nat)),
         connectives.or_introl (le O n)
         (connectives.Not (le O n)) (le_O_n n))
      (λ (n : sttfa.etap (sttfa.p nat)),
         connectives.or_intror (le (S n) O)
         (connectives.Not (le (S n) O)) (not_le_Sn_O n))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           λ (_clearme : sttfa.eps (logic.decidable (le n m))),
             connectives.match_Or_prop (le n m)
             (connectives.Not (le n m))
             (logic.decidable (le (S n) (S m)))
             (λ (auto : sttfa.eps (le n m)),
                connectives.or_introl (le (S n) (S m))
                (connectives.Not (le (S n) (S m)))
                (le_S_S n m auto))
             (λ (auto : sttfa.eps (connectives.Not (le n m))),
                connectives.or_intror (le (S n) (S m))
                (connectives.Not (le (S n) (S m)))
                (not_le_to_not_le_S_S n m auto))
             _clearme);
symbol decidable_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)), logic.decidable (lt n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)), decidable_le (S n) m;
symbol le_to_or_lt_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m)
           (connectives.Or (lt n m) (logic.eq nat n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (lenm : sttfa.eps (le n m)),
            le_ind n
            (λ (x_417 : sttfa.etap (sttfa.p nat)),
               connectives.Or (lt n x_417) (logic.eq nat n x_417))
            (relations.RC_reflexive nat lt n)
            (λ (m0 : sttfa.etap (sttfa.p nat)),
               λ (_x_419 : sttfa.eps (le n m0)),
                 λ
                   (
                   _x_421 : sttfa.eps
                            (connectives.Or (lt n m0)
                             (logic.eq nat n m0))
                   ),
                   connectives.or_introl (lt n (S m0))
                   (logic.eq nat n (S m0))
                   (le_to_lt_to_lt n m0 (S m0) _x_419
                    (logic.eq_coerc
                     (le (S m0) (plus O (S m0)))
                     (le (S m0) (S m0))
                     (le_plus_n O (S m0))
                     (logic.rewrite_l nat (S m0)
                      (λ (__ : sttfa.etap (sttfa.p nat)),
                         logic.eq sttfa.bool (le (S m0) __)
                         (le (S m0) (S m0)))
                      (logic.refl sttfa.bool (le (S m0) (S m0)))
                      (plus O (S m0)) (plus_O_n (S m0))))))
            m lenm;
symbol lt_O_n_elim
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.impl (lt O n)
        (sttfa.forall (sttfa.arrow nat sttfa.bool)
         (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
            sttfa.impl
            (sttfa.forall nat
             (λ (m : sttfa.etap (sttfa.p nat)), P (S m)))
            (P n)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt O _x_365)
           (sttfa.forall (sttfa.arrow nat sttfa.bool)
            (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
               sttfa.impl
               (sttfa.forall nat
                (λ (m : sttfa.etap (sttfa.p nat)), P (S m)))
               (P _x_365))))
        (λ (abs : sttfa.eps (lt O O)),
           connectives.falsity
           (sttfa.forall (sttfa.arrow nat sttfa.bool)
            (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
               sttfa.impl
               (sttfa.forall nat
                (λ (m : sttfa.etap (sttfa.p nat)), P (S m)))
               (P O)))
           (logic.absurd (le (S O) O) abs
            (not_le_Sn_O O)))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           λ
             (
             _x_368 : sttfa.eps
                      (sttfa.impl (lt O x_366)
                       (sttfa.forall (sttfa.arrow nat sttfa.bool)
                        (λ
                           (
                           P : sttfa.etap
                               (sttfa.p (sttfa.arrow nat sttfa.bool))
                           ),
                           sttfa.impl
                           (sttfa.forall nat
                            (λ (m : sttfa.etap (sttfa.p nat)),
                               P (S m)))
                           (P x_366))))
             ),
             λ (auto : sttfa.eps (lt O (S x_366))),
               λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
                 λ
                   (
                   auto' : sttfa.eps
                           (sttfa.forall nat
                            (λ (m : sttfa.etap (sttfa.p nat)),
                               P (S m)))
                   ), auto' x_366)
        n;
symbol le_n_O_elim
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.impl (le n O)
        (sttfa.forall (sttfa.arrow nat sttfa.bool)
         (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
            sttfa.impl (P O) (P n)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_prop
        (λ (__ : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le __ O)
           (sttfa.forall (sttfa.arrow nat sttfa.bool)
            (λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
               sttfa.impl (P O) (P __))))
        (λ (auto : sttfa.eps (le O O)),
           λ (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
             λ (auto' : sttfa.eps (P O)), auto')
        (λ (a : sttfa.etap (sttfa.p nat)),
           λ (abs : sttfa.eps (le (S a) O)),
             connectives.falsity
             (sttfa.forall (sttfa.arrow nat sttfa.bool)
              (λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow nat sttfa.bool))),
                 sttfa.impl (P O) (P (S a))))
             (logic.absurd (le (S a) O) abs (not_le_Sn_O a)))
        n;
symbol lt_to_not_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (lt n m) (connectives.Not (logic.eq nat n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (H : sttfa.eps (lt n m)),
            logic.not_to_not (logic.eq nat n m) connectives.False
            (λ (auto : sttfa.eps (logic.eq nat n m)),
               logic.absurd (le (S n) n)
               (logic.eq_coerc (le (S n) m) (le (S n) n) H
                (logic.rewrite_l nat n
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (le (S n) __)
                    (le (S n) n))
                 (logic.refl sttfa.bool (le (S n) n)) m auto))
               (not_le_Sn_n n))
            (connectives.nmk connectives.False
             (λ (auto : sttfa.eps connectives.False), auto));
symbol le_n_O_to_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.impl (le n O) (logic.eq nat O n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        match_nat_prop
        (λ (__ : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le __ O) (logic.eq nat O __))
        (λ (auto : sttfa.eps (le O O)), logic.refl nat O)
        (λ (a : sttfa.etap (sttfa.p nat)),
           λ (abs : sttfa.eps (le (S a) O)),
             connectives.falsity (logic.eq nat O (S a))
             (logic.absurd (le (S a) O) abs (not_le_Sn_O a)))
        n;
symbol le_to_le_to_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m)
           (sttfa.impl (le m n) (logic.eq nat n m)))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le __ _0)
           (sttfa.impl (le _0 __) (logic.eq nat __ _0)))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (auto : sttfa.eps (le O n)),
           λ (auto' : sttfa.eps (le n O)),
             logic.sym_eq nat n O
             (logic.sym_eq nat O n
              (logic.eq_coerc (logic.eq nat O n)
               (logic.eq nat O n) (le_n_O_to_eq n auto')
               (logic.refl sttfa.bool (logic.eq nat O n)))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (auto : sttfa.eps (le (S n) O)),
           λ (auto' : sttfa.eps (le O (S n))),
             logic.sym_eq nat O (S n)
             (le_n_O_to_eq (S n) auto))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           λ
             (
             auto : sttfa.eps
                    (sttfa.impl (le n m)
                     (sttfa.impl (le m n) (logic.eq nat n m)))
             ),
             λ (auto' : sttfa.eps (le (S n) (S m))),
               λ (auto'' : sttfa.eps (le (S m) (S n))),
                 logic.eq_f nat nat S n m
                 (auto
                  (logic.eq_coerc
                   (le (pred (S n)) (pred (S m)))
                   (le n m)
                   (monotonic_pred (S n) (S m) auto')
                   (logic.rewrite_l nat n
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq sttfa.bool (le __ (pred (S m)))
                       (le n m))
                    (logic.rewrite_l nat m
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq sttfa.bool (le n __) (le n m))
                     (logic.refl sttfa.bool (le n m))
                     (pred (S m)) (pred_Sn m))
                    (pred (S n)) (pred_Sn n)))
                  (logic.eq_coerc
                   (le (pred (S m)) (pred (S n)))
                   (le m n)
                   (monotonic_pred (S m) (S n) auto'')
                   (logic.rewrite_l nat m
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq sttfa.bool (le __ (pred (S n)))
                       (le m n))
                    (logic.rewrite_l nat n
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq sttfa.bool (le m __) (le m n))
                     (logic.refl sttfa.bool (le m n))
                     (pred (S n)) (pred_Sn n))
                    (pred (S m)) (pred_Sn m)))));
symbol plus_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (m : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (n : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le m n)
              (logic.eq nat (plus (minus n m) p)
               (minus (plus n p) m))))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le __ _0)
              (logic.eq nat (plus (minus _0 __) p)
               (minus (plus _0 p) __))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (p : sttfa.etap (sttfa.p nat)),
           λ (auto : sttfa.eps (le O n)),
             logic.rewrite_l nat n
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat (plus __ p)
                (minus (plus n p) O))
             (logic.rewrite_l nat (plus n p)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (plus n p) __)
              (logic.refl nat (plus n p))
              (minus (plus n p) O) (minus_n_O (plus n p)))
             (minus n O) (minus_n_O n))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (p : sttfa.etap (sttfa.p nat)),
           λ (abs : sttfa.eps (le (S n) O)),
             connectives.falsity
             (logic.eq nat (plus (minus O (S n)) p)
              (minus (plus O p) (S n)))
             (logic.absurd (le (S n) O) abs (not_le_Sn_O n)))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           sym_eq_minus (S m)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.impl
              (sttfa.forall nat
               (λ (p : sttfa.etap (sttfa.p nat)),
                  sttfa.impl (le n m)
                  (logic.eq nat (plus (minus m n) p)
                   (minus (plus m p) n))))
              (sttfa.forall nat
               (λ (p : sttfa.etap (sttfa.p nat)),
                  sttfa.impl (le (S n) (S m))
                  (logic.eq nat (plus (y (S n)) p)
                   (minus (plus (S m) p) (S n))))))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
            minus_body m
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.impl
               (sttfa.forall nat
                (λ (p : sttfa.etap (sttfa.p nat)),
                   sttfa.impl (le n m)
                   (logic.eq nat (plus (minus m n) p)
                    (minus (plus m p) n))))
               (sttfa.forall nat
                (λ (p : sttfa.etap (sttfa.p nat)),
                   sttfa.impl (le (S n) (S m))
                   (logic.eq nat (plus (y (S n)) p)
                    (minus (plus (S m) p) (S n))))))
            (sym_eq_minus_body_S m
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.impl
                (sttfa.forall nat
                 (λ (p : sttfa.etap (sttfa.p nat)),
                    sttfa.impl (le n m)
                    (logic.eq nat (plus (minus m n) p)
                     (minus (plus m p) n))))
                (sttfa.forall nat
                 (λ (p : sttfa.etap (sttfa.p nat)),
                    sttfa.impl (le (S n) (S m))
                    (logic.eq nat (plus (y (S n)) p)
                     (minus (plus (S m) p) (S n))))))
             (λ
                (
                auto : sttfa.eps
                       (sttfa.forall nat
                        (λ (p : sttfa.etap (sttfa.p nat)),
                           sttfa.impl (le n m)
                           (logic.eq nat (plus (minus m n) p)
                            (minus (plus m p) n))))
                ),
                λ (p : sttfa.etap (sttfa.p nat)),
                  sym_eq_match_nat_type_S nat (S m)
                  (λ (q : sttfa.etap (sttfa.p nat)), minus m q) n
                  (λ (y : sttfa.etap (sttfa.p nat)),
                     sttfa.impl (le (S n) (S m))
                     (logic.eq nat (plus y p)
                      (minus (plus (S m) p) (S n))))
                  (sym_eq_minus (plus (S m) p)
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      sttfa.impl (le (S n) (S m))
                      (logic.eq nat (plus (minus m n) p)
                       (y (S n))))
                   (sym_eq_plus (S m)
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       sttfa.impl (le (S n) (S m))
                       (logic.eq nat (plus (minus m n) p)
                        (filter_nat_type (sttfa.arrow nat nat)
                         minus_body (y p) (S n))))
                    (sym_eq_filter_nat_type_S
                     (sttfa.arrow nat nat) plus_body m
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        sttfa.impl (le (S n) (S m))
                        (logic.eq nat (plus (minus m n) p)
                         (filter_nat_type (sttfa.arrow nat nat)
                          minus_body (y p) (S n))))
                     (sym_eq_plus_body_S m
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         sttfa.impl (le (S n) (S m))
                         (logic.eq nat (plus (minus m n) p)
                          (filter_nat_type (sttfa.arrow nat nat)
                           minus_body (y p) (S n))))
                      (sym_eq_filter_nat_type_S
                       (sttfa.arrow nat nat) minus_body
                       (plus m p)
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ),
                          sttfa.impl (le (S n) (S m))
                          (logic.eq nat (plus (minus m n) p)
                           (y (S n))))
                       (eq_plus_body_S m
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ),
                           sttfa.impl (le (S n) (S m))
                           (logic.eq nat (plus (minus m n) p)
                            (minus_body (y p) (S n))))
                        (eq_filter_nat_type_S
                         (sttfa.arrow nat nat) plus_body m
                         (λ
                            (
                            y : sttfa.etap
                                (sttfa.p (sttfa.arrow nat nat))
                            ),
                            sttfa.impl (le (S n) (S m))
                            (logic.eq nat (plus (minus m n) p)
                             (minus_body (y p) (S n))))
                         (eq_plus (S m)
                          (λ
                             (
                             y : sttfa.etap
                                 (sttfa.p (sttfa.arrow nat nat))
                             ),
                             sttfa.impl (le (S n) (S m))
                             (logic.eq nat (plus (minus m n) p)
                              (minus_body (y p) (S n))))
                          (sym_eq_plus (S m)
                           (λ
                              (
                              y : sttfa.etap
                                  (sttfa.p (sttfa.arrow nat nat))
                              ),
                              sttfa.impl (le (S n) (S m))
                              (logic.eq nat (plus (minus m n) p)
                               (minus_body (y p) (S n))))
                           (sym_eq_filter_nat_type_S
                            (sttfa.arrow nat nat) plus_body m
                            (λ
                               (
                               y : sttfa.etap
                                   (sttfa.p (sttfa.arrow nat nat))
                               ),
                               sttfa.impl (le (S n) (S m))
                               (logic.eq nat (plus (minus m n) p)
                                (minus_body (y p) (S n))))
                            (sym_eq_plus_body_S m
                             (λ
                                (
                                y : sttfa.etap
                                    (sttfa.p (sttfa.arrow nat nat))
                                ),
                                sttfa.impl (le (S n) (S m))
                                (logic.eq nat
                                 (plus (minus m n) p)
                                 (minus_body (y p) (S n))))
                             (sym_eq_minus_body_S (plus m p)
                              (λ
                                 (
                                 y : sttfa.etap
                                     (sttfa.p (sttfa.arrow nat nat))
                                 ),
                                 sttfa.impl (le (S n) (S m))
                                 (logic.eq nat
                                  (plus (minus m n) p) (y (S n))))
                              (sym_eq_match_nat_type_S nat
                               (S (plus m p))
                               (λ (q : sttfa.etap (sttfa.p nat)),
                                  minus (plus m p) q)
                               n
                               (λ (y : sttfa.etap (sttfa.p nat)),
                                  sttfa.impl (le (S n) (S m))
                                  (logic.eq nat
                                   (plus (minus m n) p) y))
                               (λ
                                  (
                                  auto' : sttfa.eps
                                          (le (S n) (S m))
                                  ),
                                  auto p
                                  (logic.eq_coerc
                                   (le (pred (S n))
                                    (pred (S m)))
                                   (le n m)
                                   (monotonic_pred (S n) (S m)
                                    auto')
                                   (logic.rewrite_l nat n
                                    (λ (__ : sttfa.etap (sttfa.p nat)),
                                       logic.eq sttfa.bool
                                       (le __ (pred (S m)))
                                       (le n m))
                                    (logic.rewrite_l nat m
                                     (λ (__ : sttfa.etap (sttfa.p nat)),
                                        logic.eq sttfa.bool (le n __)
                                        (le n m))
                                     (logic.refl sttfa.bool (le n m))
                                     (pred (S m)) (pred_Sn m))
                                    (pred (S n)) (pred_Sn n)))))))))))))))))))));
symbol minus_plus_m_m
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           logic.eq nat n (minus (plus n m) m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          logic.eq_coerc
          (logic.eq nat (plus (minus m m) n)
           (minus (plus m n) m))
          (logic.eq nat n (minus (plus n m) m))
          (plus_minus m m n (le_n m))
          (logic.rewrite_l nat O
           (λ (__ : sttfa.etap (sttfa.p nat)),
              logic.eq sttfa.bool
              (logic.eq nat (plus __ n) (minus (plus m n) m))
              (logic.eq nat n (minus (plus n m) m)))
           (logic.rewrite_l nat n
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq sttfa.bool
               (logic.eq nat __ (minus (plus m n) m))
               (logic.eq nat n (minus (plus n m) m)))
            (logic.rewrite_r nat (plus n m)
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq sttfa.bool (logic.eq nat n (minus __ m))
                (logic.eq nat n (minus (plus n m) m)))
             (logic.refl sttfa.bool
              (logic.eq nat n (minus (plus n m) m)))
             (plus m n) (commutative_plus m n))
            (plus O n) (plus_O_n n))
           (minus m m) (minus_n_n m));
symbol plus_minus_m_m
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le m n)
           (logic.eq nat n (plus (minus n m) m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (lemn : sttfa.eps (le m n)),
            logic.sym_eq nat (plus (minus n m) m) n
            (logic.eq_coerc
             (logic.eq nat (plus (minus n m) m)
              (minus (plus n m) m))
             (logic.eq nat (plus (minus n m) m) n)
             (plus_minus m n m lemn)
             (logic.rewrite_r nat (plus m (minus n m))
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool
                 (logic.eq nat (plus (minus n m) m)
                  (minus (plus n m) m))
                 (logic.eq nat __ n))
              (logic.rewrite_r nat (plus m (minus n m))
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool
                  (logic.eq nat __ (minus (plus n m) m))
                  (logic.eq nat (plus m (minus n m)) n))
               (logic.rewrite_l nat n
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool
                   (logic.eq nat (plus m (minus n m)) __)
                   (logic.eq nat (plus m (minus n m)) n))
                (logic.refl sttfa.bool
                 (logic.eq nat (plus m (minus n m)) n))
                (minus (plus n m) m) (minus_plus_m_m n m))
               (plus (minus n m) m)
               (commutative_plus (minus n m) m))
              (plus (minus n m) m)
              (commutative_plus (minus n m) m)));
symbol minus_to_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le m n)
              (sttfa.impl (logic.eq nat (minus n m) p)
               (logic.eq nat n (plus m p)))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (lemn : sttfa.eps (le m n)),
              λ (eqp : sttfa.eps (logic.eq nat (minus n m) p)),
                logic.eq_coerc
                (logic.eq nat n (plus (minus n m) m))
                (logic.eq nat n (plus m p))
                (plus_minus_m_m n m lemn)
                (logic.rewrite_r nat (plus m (minus n m))
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (logic.eq nat n __)
                    (logic.eq nat n (plus m p)))
                 (logic.rewrite_r nat p
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool (logic.eq nat n (plus m __))
                     (logic.eq nat n (plus m p)))
                  (logic.refl sttfa.bool (logic.eq nat n (plus m p)))
                  (minus n m) eqp)
                 (plus (minus n m) m)
                 (commutative_plus (minus n m) m));
symbol plus_to_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (logic.eq nat n (plus m p))
              (logic.eq nat (minus n m) p)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (eqp : sttfa.eps (logic.eq nat n (plus m p))),
              logic.sym_eq nat p (minus n m)
              (logic.eq_coerc
               (logic.eq nat p (minus (plus p m) m))
               (logic.eq nat p (minus n m)) (minus_plus_m_m p m)
               (logic.rewrite_r nat (plus m p)
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool (logic.eq nat p (minus __ m))
                   (logic.eq nat p (minus n m)))
                (logic.rewrite_l nat n
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (logic.eq nat p (minus __ m))
                    (logic.eq nat p (minus n m)))
                 (logic.refl sttfa.bool (logic.eq nat p (minus n m)))
                 (plus m p) eqp)
                (plus p m) (commutative_plus p m)));
symbol monotonic_le_minus_l
  : sttfa.eps
    (sttfa.forall nat
     (λ (p : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (q : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le q p)
              (le (minus q n) (minus p n))))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le _0 __)
              (le (minus _0 n) (minus __ n))))
      (λ (p : sttfa.etap (sttfa.p nat)),
         λ (q : sttfa.etap (sttfa.p nat)),
           λ (lePO : sttfa.eps (le p O)),
             le_n_O_elim p lePO
             (λ (__ : sttfa.etap (sttfa.p nat)),
                le (minus __ q) (minus O q))
             (le_n (minus O q)))
      (λ (p : sttfa.etap (sttfa.p nat)),
         λ (q : sttfa.etap (sttfa.p nat)),
           sym_eq_minus (S p)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
              sttfa.impl (le O (S p))
              (le (minus O q) (y q)))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
            minus_body p
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
               sttfa.impl (le O (S p))
               (le (minus O q) (y q)))
            (sym_eq_minus_body_S p
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                sttfa.impl (le O (S p))
                (le (minus O q) (y q)))
             (eq_plus_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                 sttfa.impl (le O (S p))
                 (le (minus O q)
                  (y
                   (match_nat_type nat (S p)
                    (λ (q0 : sttfa.etap (sttfa.p nat)), minus p q0)
                    q))))
              (eq_filter_nat_type_O (sttfa.arrow nat nat)
               plus_body
               (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                  sttfa.impl (le O (S p))
                  (le (minus O q)
                   (y
                    (match_nat_type nat (S p)
                     (λ (q0 : sttfa.etap (sttfa.p nat)), minus p q0)
                     q))))
               (eq_plus O
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.impl (le O (S p))
                   (le (minus O q)
                    (y
                     (match_nat_type nat (S p)
                      (λ (q0 : sttfa.etap (sttfa.p nat)), minus p q0)
                      q))))
                (eq_minus_body_O
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.impl (le O (S p))
                    (le (minus O q)
                     (plus
                      (y
                       (match_nat_type nat (S p)
                        (λ (q0 : sttfa.etap (sttfa.p nat)),
                           minus p q0)
                        q))
                      (match_nat_type nat (S p)
                       (λ (q0 : sttfa.etap (sttfa.p nat)),
                          minus p q0)
                       q))))
                 (eq_filter_nat_type_O (sttfa.arrow nat nat)
                  minus_body
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.impl (le O (S p))
                     (le (minus O q)
                      (plus
                       (y
                        (match_nat_type nat (S p)
                         (λ (q0 : sttfa.etap (sttfa.p nat)),
                            minus p q0)
                         q))
                       (match_nat_type nat (S p)
                        (λ (q0 : sttfa.etap (sttfa.p nat)),
                           minus p q0)
                        q))))
                  (eq_minus O
                   (λ
                      (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                      ),
                      sttfa.impl (le O (S p))
                      (le (minus O q)
                       (plus
                        (y
                         (match_nat_type nat (S p)
                          (λ (q0 : sttfa.etap (sttfa.p nat)),
                             minus p q0)
                          q))
                        (match_nat_type nat (S p)
                         (λ (q0 : sttfa.etap (sttfa.p nat)),
                            minus p q0)
                         q))))
                   (eq_minus_body_O
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       sttfa.impl (le O (S p))
                       (le (minus O q)
                        (plus
                         (minus (y q)
                          (match_nat_type nat (S p)
                           (λ (q0 : sttfa.etap (sttfa.p nat)),
                              minus p q0)
                           q))
                         (match_nat_type nat (S p)
                          (λ (q0 : sttfa.etap (sttfa.p nat)),
                             minus p q0)
                          q))))
                    (eq_filter_nat_type_O (sttfa.arrow nat nat)
                     minus_body
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        sttfa.impl (le O (S p))
                        (le (minus O q)
                         (plus
                          (minus (y q)
                           (match_nat_type nat (S p)
                            (λ (q0 : sttfa.etap (sttfa.p nat)),
                               minus p q0)
                            q))
                          (match_nat_type nat (S p)
                           (λ (q0 : sttfa.etap (sttfa.p nat)),
                              minus p q0)
                           q))))
                     (eq_minus O
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         sttfa.impl (le O (S p))
                         (le (minus O q)
                          (plus
                           (minus (y q)
                            (match_nat_type nat (S p)
                             (λ (q0 : sttfa.etap (sttfa.p nat)),
                                minus p q0)
                             q))
                           (match_nat_type nat (S p)
                            (λ (q0 : sttfa.etap (sttfa.p nat)),
                               minus p q0)
                            q))))
                      (λ (auto : sttfa.eps (le O (S p))),
                         le_plus_minus_m_m (minus O q)
                         (match_nat_type nat (S p)
                          (λ (q0 : sttfa.etap (sttfa.p nat)),
                             minus p q0)
                          q))))))))))))))
      (λ (p : sttfa.etap (sttfa.p nat)),
         λ (q : sttfa.etap (sttfa.p nat)),
           λ
             (
             Hind : sttfa.eps
                    (sttfa.forall nat
                     (λ (n0 : sttfa.etap (sttfa.p nat)),
                        sttfa.impl (le q p)
                        (le (minus q n0) (minus p n0))))
             ),
             λ (n : sttfa.etap (sttfa.p nat)),
               match_nat_prop
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  sttfa.impl (le (S q) (S p))
                  (le (minus (S q) __) (minus (S p) __)))
               (sym_eq_minus (S q)
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.impl (le (S q) (S p))
                   (le (y O) (minus (S p) O)))
                (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                 minus_body q
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.impl (le (S q) (S p))
                    (le (y O) (minus (S p) O)))
                 (sym_eq_minus_body_S q
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.impl (le (S q) (S p))
                     (le (y O) (minus (S p) O)))
                  (sym_eq_match_nat_type_O nat (S q)
                   (λ (z : sttfa.etap (sttfa.p nat)), minus q z)
                   (λ (y : sttfa.etap (sttfa.p nat)),
                      sttfa.impl (le (S q) (S p))
                      (le y (minus (S p) O)))
                   (sym_eq_minus (S p)
                    (λ
                       (
                       y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))
                       ),
                       sttfa.impl (le (S q) (S p))
                       (le (S q) (y O)))
                    (sym_eq_filter_nat_type_S
                     (sttfa.arrow nat nat) minus_body p
                     (λ
                        (
                        y : sttfa.etap
                            (sttfa.p (sttfa.arrow nat nat))
                        ),
                        sttfa.impl (le (S q) (S p))
                        (le (S q) (y O)))
                     (sym_eq_minus_body_S p
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         sttfa.impl (le (S q) (S p))
                         (le (S q) (y O)))
                      (sym_eq_match_nat_type_O nat (S p)
                       (λ (q0 : sttfa.etap (sttfa.p nat)),
                          minus p q0)
                       (λ (y : sttfa.etap (sttfa.p nat)),
                          sttfa.impl (le (S q) (S p))
                          (le (S q) y))
                       (λ (auto : sttfa.eps (le (S q) (S p))),
                          auto)))))))))
               (sym_eq_minus (S q)
                (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                   sttfa.forall nat
                   (λ (a : sttfa.etap (sttfa.p nat)),
                      sttfa.impl (le (S q) (S p))
                      (le (y (S a)) (minus (S p) (S a)))))
                (sym_eq_filter_nat_type_S (sttfa.arrow nat nat)
                 minus_body q
                 (λ
                    (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                    sttfa.forall nat
                    (λ (a : sttfa.etap (sttfa.p nat)),
                       sttfa.impl (le (S q) (S p))
                       (le (y (S a)) (minus (S p) (S a)))))
                 (sym_eq_minus_body_S q
                  (λ
                     (y : sttfa.etap (sttfa.p (sttfa.arrow nat nat))),
                     sttfa.forall nat
                     (λ (a : sttfa.etap (sttfa.p nat)),
                        sttfa.impl (le (S q) (S p))
                        (le (y (S a)) (minus (S p) (S a)))))
                  (λ (a : sttfa.etap (sttfa.p nat)),
                     sym_eq_match_nat_type_S nat (S q)
                     (λ (z : sttfa.etap (sttfa.p nat)), minus q z) a
                     (λ (y : sttfa.etap (sttfa.p nat)),
                        sttfa.impl (le (S q) (S p))
                        (le y (minus (S p) (S a))))
                     (sym_eq_minus (S p)
                      (λ
                         (
                         y : sttfa.etap
                             (sttfa.p (sttfa.arrow nat nat))
                         ),
                         sttfa.impl (le (S q) (S p))
                         (le (minus q a) (y (S a))))
                      (sym_eq_filter_nat_type_S
                       (sttfa.arrow nat nat) minus_body p
                       (λ
                          (
                          y : sttfa.etap
                              (sttfa.p (sttfa.arrow nat nat))
                          ),
                          sttfa.impl (le (S q) (S p))
                          (le (minus q a) (y (S a))))
                       (sym_eq_minus_body_S p
                        (λ
                           (
                           y : sttfa.etap
                               (sttfa.p (sttfa.arrow nat nat))
                           ),
                           sttfa.impl (le (S q) (S p))
                           (le (minus q a) (y (S a))))
                        (sym_eq_match_nat_type_S nat (S p)
                         (λ (q0 : sttfa.etap (sttfa.p nat)),
                            minus p q0)
                         a
                         (λ (y : sttfa.etap (sttfa.p nat)),
                            sttfa.impl (le (S q) (S p))
                            (le (minus q a) y))
                         (λ (leSS : sttfa.eps (le (S q) (S p))),
                            Hind a
                            (logic.eq_coerc
                             (le (pred (S q))
                              (pred (S p)))
                             (le q p)
                             (monotonic_pred (S q) (S p) leSS)
                             (logic.rewrite_l nat q
                              (λ (__ : sttfa.etap (sttfa.p nat)),
                                 logic.eq sttfa.bool
                                 (le __ (pred (S p)))
                                 (le q p))
                              (logic.rewrite_l nat p
                               (λ (__ : sttfa.etap (sttfa.p nat)),
                                  logic.eq sttfa.bool (le q __)
                                  (le q p))
                               (logic.refl sttfa.bool (le q p))
                               (pred (S p)) (pred_Sn p))
                              (pred (S q)) (pred_Sn q))))))))))))
               n);
symbol le_plus_to_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le n (plus p m)) (le (minus n m) p)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (lep : sttfa.eps (le n (plus p m))),
              logic.eq_coerc
              (le (minus n m) (minus (plus p m) m))
              (le (minus n m) p)
              (monotonic_le_minus_l (plus p m) n m lep)
              (logic.rewrite_l nat p
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq sttfa.bool (le (minus n m) __)
                  (le (minus n m) p))
               (logic.refl sttfa.bool (le (minus n m) p))
               (minus (plus p m) m) (minus_plus_m_m p m));
symbol monotonic_le_minus_r
  : sttfa.eps
    (sttfa.forall nat
     (λ (p : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (q : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (n : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le q p)
              (le (minus n p) (minus n q))))))
  ≔ λ (p : sttfa.etap (sttfa.p nat)),
        λ (q : sttfa.etap (sttfa.p nat)),
          λ (n : sttfa.etap (sttfa.p nat)),
            λ (lepq : sttfa.eps (le q p)),
              le_plus_to_minus n p (minus n q)
              (transitive_le n (plus (minus n q) q)
               (plus (minus n q) p) (le_plus_minus_m_m n q)
               (monotonic_le_plus_r (minus n q) q p lepq));
symbol minus_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (x : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (y : sttfa.etap (sttfa.p nat)), le (minus x y) x)))
  ≔ λ (x : sttfa.etap (sttfa.p nat)),
        λ (y : sttfa.etap (sttfa.p nat)),
          logic.eq_coerc
          (le (minus x y) (minus (plus x y) y))
          (le (minus x y) x)
          (monotonic_le_minus_l (plus x y) x y (le_plus_n_r y x))
          (logic.rewrite_l nat x
           (λ (__ : sttfa.etap (sttfa.p nat)),
              logic.eq sttfa.bool (le (minus x y) __)
              (le (minus x y) x))
           (logic.refl sttfa.bool (le (minus x y) x))
           (minus (plus x y) y) (minus_plus_m_m x y));
symbol not_eq_to_le_to_lt
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (logic.eq nat n m))
           (sttfa.impl (le n m) (lt n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (Hneq : sttfa.eps (connectives.Not (logic.eq nat n m))),
            λ (Hle : sttfa.eps (le n m)),
              connectives.match_Or_prop (lt n m) (logic.eq nat n m)
              (lt n m) (λ (auto : sttfa.eps (lt n m)), auto)
              (λ (Heq : sttfa.eps (logic.eq nat n m)),
                 not_le_to_lt m n
                 (logic.not_to_not (le m n) (logic.eq nat n m)
                  (λ (auto : sttfa.eps (le m n)),
                     logic.rewrite_l nat n
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq nat n __)
                     (logic.refl nat n) m Heq)
                  Hneq))
              (le_to_or_lt_eq n m Hle);
symbol eq_minus_O
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m) (logic.eq nat (minus n m) O))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (lenm : sttfa.eps (le n m)),
            le_n_O_elim (minus n m)
            (logic.eq_coerc (le (minus n m) (minus n n))
             (le (minus n m) O)
             (monotonic_le_minus_r m n n lenm)
             (logic.rewrite_l nat O
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool (le (minus n m) __)
                 (le (minus n m) O))
              (logic.refl sttfa.bool (le (minus n m) O))
              (minus n n) (minus_n_n n)))
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq nat __ O)
            (logic.refl nat O);
symbol distributive_times_minus
  : sttfa.eps (relations.distributive nat times minus)
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            connectives.match_Or_prop (lt b c)
            (connectives.Not (lt b c))
            (logic.eq nat (times a (minus b c))
             (minus (times a b) (times a c)))
            (λ (Hbc : sttfa.eps (lt b c)),
               logic.eq_ind_r nat O
               (λ (x : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (times a x)
                  (minus (times a b) (times a c)))
               (logic.eq_ind_r nat O
                (λ (x : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (times a O) x)
                (logic.rewrite_l nat O
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq nat __ O)
                 (logic.refl nat O) (times a O)
                 (times_n_O a))
                (minus (times a b) (times a c))
                (eq_minus_O (times a b) (times a c)
                 (monotonic_le_times_r a b c (lt_to_le b c Hbc))))
               (minus b c) (eq_minus_O b c (lt_to_le b c Hbc)))
            (λ (Hbc : sttfa.eps (connectives.Not (lt b c))),
               logic.sym_eq nat
               (minus (times a b) (times a c))
               (times a (minus b c))
               (logic.eq_coerc
                (logic.eq nat (minus (times a b) (times a c))
                 (times a (minus b c)))
                (logic.eq nat (minus (times a b) (times a c))
                 (times a (minus b c)))
                (plus_to_minus (times a b) (times a c)
                 (times a (minus b c))
                 (logic.eq_ind nat
                  (times a (plus c (minus b c)))
                  (λ (x_1 : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (times a b) x_1)
                  (logic.eq_f nat nat (times a) b
                   (plus c (minus b c))
                   (logic.eq_coerc
                    (logic.eq nat b (plus (minus b c) c))
                    (logic.eq nat b (plus c (minus b c)))
                    (plus_minus_m_m b c (not_lt_to_le b c Hbc))
                    (logic.rewrite_r nat (plus c (minus b c))
                     (λ (__ : sttfa.etap (sttfa.p nat)),
                        logic.eq sttfa.bool (logic.eq nat b __)
                        (logic.eq nat b (plus c (minus b c))))
                     (logic.refl sttfa.bool
                      (logic.eq nat b (plus c (minus b c))))
                     (plus (minus b c) c)
                     (commutative_plus (minus b c) c))))
                  (plus (times a c) (times a (minus b c)))
                  (distributive_times_plus a c (minus b c))))
                (logic.refl sttfa.bool
                 (logic.eq nat
                  (minus (times a b) (times a c))
                  (times a (minus b c))))))
            (decidable_lt b c);
symbol minus_plus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              logic.eq nat (minus (minus n m) p)
              (minus n (plus m p))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            connectives.match_Or_prop (le (plus m p) n)
            (connectives.Not (le (plus m p) n))
            (logic.eq nat (minus (minus n m) p)
             (minus n (plus m p)))
            (λ (Hlt : sttfa.eps (le (plus m p) n)),
               plus_to_minus (minus n m) p
               (minus n (plus m p))
               (plus_to_minus n m
                (plus p (minus n (plus m p)))
                (logic.eq_ind nat
                 (plus (plus m p) (minus n (plus m p)))
                 (λ (x_1 : sttfa.etap (sttfa.p nat)),
                    logic.eq nat n x_1)
                 (minus_to_plus n (plus m p)
                  (minus n (plus m p)) Hlt
                  (logic.refl nat (minus n (plus m p))))
                 (plus m (plus p (minus n (plus m p))))
                 (associative_plus m p (minus n (plus m p))))))
            (λ
               (Hlt : sttfa.eps (connectives.Not (le (plus m p) n))),
               logic.eq_ind_r nat O
               (λ (x : sttfa.etap (sttfa.p nat)),
                  logic.eq nat x (minus n (plus m p)))
               (logic.sym_eq nat (minus n (plus m p)) O
                (logic.eq_coerc
                 (logic.eq nat (minus n (plus m p)) O)
                 (logic.eq nat (minus n (plus m p)) O)
                 (eq_minus_O n (plus m p)
                  (transitive_le n (S n) (plus m p)
                   (le_n_Sn n) (not_le_to_lt (plus m p) n Hlt)))
                 (logic.refl sttfa.bool
                  (logic.eq nat (minus n (plus m p)) O))))
               (minus (minus n m) p)
               (eq_minus_O (minus n m) p
                (logic.eq_coerc
                 (le (minus n m) (minus (plus p m) m))
                 (le (minus n m) p)
                 (monotonic_le_minus_l (plus p m) n m
                  (logic.eq_coerc (le n (plus m p))
                   (le n (plus p m))
                   (transitive_le n (S n) (plus m p)
                    (le_n_Sn n) (not_le_to_lt (plus m p) n Hlt))
                   (logic.rewrite_r nat (plus m p)
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq sttfa.bool (le n (plus m p))
                       (le n __))
                    (logic.refl sttfa.bool (le n (plus m p)))
                    (plus p m) (commutative_plus p m))))
                 (logic.rewrite_l nat p
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool (le (minus n m) __)
                     (le (minus n m) p))
                  (logic.refl sttfa.bool (le (minus n m) p))
                  (minus (plus p m) m) (minus_plus_m_m p m)))))
            (decidable_le (plus m p) n);
symbol minus_minus
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (p : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le p m)
              (sttfa.impl (le m n)
               (logic.eq nat (plus p (minus n m))
                (minus n (minus m p))))))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (p : sttfa.etap (sttfa.p nat)),
            λ (lepm : sttfa.eps (le p m)),
              λ (lemn : sttfa.eps (le m n)),
                logic.sym_eq nat (minus n (minus m p))
                (plus p (minus n m))
                (plus_to_minus n (minus m p)
                 (plus p (minus n m))
                 (logic.eq_ind nat
                  (plus (plus (minus m p) p) (minus n m))
                  (λ (x_1 : sttfa.etap (sttfa.p nat)),
                     logic.eq nat n x_1)
                  (logic.eq_ind nat m
                   (λ (x_1 : sttfa.etap (sttfa.p nat)),
                      logic.eq nat n (plus x_1 (minus n m)))
                   (logic.eq_ind nat (plus (minus n m) m)
                    (λ (x_1 : sttfa.etap (sttfa.p nat)),
                       logic.eq nat n x_1)
                    (logic.eq_ind nat n
                     (λ (x_1 : sttfa.etap (sttfa.p nat)),
                        logic.eq nat n x_1)
                     (logic.refl nat n) (plus (minus n m) m)
                     (plus_minus_m_m n m lemn))
                    (plus m (minus n m))
                    (commutative_plus (minus n m) m))
                   (plus (minus m p) p) (plus_minus_m_m m p lepm))
                  (plus (minus m p) (plus p (minus n m)))
                  (associative_plus (minus m p) p (minus n m))));
symbol minus_minus_comm
  : sttfa.eps
    (sttfa.forall nat
     (λ (a : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (b : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (c : sttfa.etap (sttfa.p nat)),
              logic.eq nat (minus (minus a b) c)
              (minus (minus a c) b)))))
  ≔ λ (a : sttfa.etap (sttfa.p nat)),
        λ (b : sttfa.etap (sttfa.p nat)),
          λ (c : sttfa.etap (sttfa.p nat)),
            le_to_le_to_eq (minus (minus a b) c)
            (minus (minus a c) b)
            (logic.eq_coerc
             (le (minus (minus a b) c)
              (minus (plus (minus (minus a c) b) c) c))
             (le (minus (minus a b) c)
              (minus (minus a c) b))
             (monotonic_le_minus_l
              (plus (minus (minus a c) b) c) (minus a b) c
              (logic.eq_coerc
               (le (minus a b)
                (plus (minus (minus a b) c) c))
               (le (minus a b)
                (plus (minus (minus a c) b) c))
               (le_plus_minus_m_m (minus a b) c)
               (logic.rewrite_r nat (minus a (plus b c))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool
                   (le (minus a b) (plus __ c))
                   (le (minus a b)
                    (plus (minus (minus a c) b) c)))
                (logic.rewrite_r nat
                 (plus c (minus a (plus b c)))
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (le (minus a b) __)
                    (le (minus a b)
                     (plus (minus (minus a c) b) c)))
                 (logic.rewrite_r nat
                  (plus c (minus (minus a c) b))
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool
                     (le (minus a b)
                      (plus c (minus a (plus b c))))
                     (le (minus a b) __))
                  (logic.rewrite_l nat (minus (minus a c) b)
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq sttfa.bool
                      (le (minus a b) (plus c __))
                      (le (minus a b)
                       (plus c (minus (minus a c) b))))
                   (logic.refl sttfa.bool
                    (le (minus a b)
                     (plus c (minus (minus a c) b))))
                   (minus a (plus b c))
                   (logic.rewrite_l nat (plus c b)
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq nat (minus (minus a c) b)
                       (minus a __))
                    (minus_plus a c b) (plus b c)
                    (commutative_plus c b)))
                  (plus (minus (minus a c) b) c)
                  (commutative_plus (minus (minus a c) b) c))
                 (plus (minus a (plus b c)) c)
                 (commutative_plus (minus a (plus b c)) c))
                (minus (minus a b) c) (minus_plus a b c))))
             (logic.rewrite_l nat (minus (minus a c) b)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool
                 (le (minus (minus a b) c) __)
                 (le (minus (minus a b) c)
                  (minus (minus a c) b)))
              (logic.refl sttfa.bool
               (le (minus (minus a b) c)
                (minus (minus a c) b)))
              (minus (plus (minus (minus a c) b) c) c)
              (minus_plus_m_m (minus (minus a c) b) c)))
            (logic.eq_coerc
             (le (minus (minus a c) b)
              (minus (plus (minus (minus a b) c) b) b))
             (le (minus (minus a c) b)
              (minus (minus a b) c))
             (monotonic_le_minus_l
              (plus (minus (minus a b) c) b) (minus a c) b
              (logic.eq_coerc
               (le (minus a c)
                (plus (minus (minus a c) b) b))
               (le (minus a c)
                (plus (minus (minus a b) c) b))
               (le_plus_minus_m_m (minus a c) b)
               (logic.rewrite_r nat (minus a (plus c b))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq sttfa.bool
                   (le (minus a c) (plus __ b))
                   (le (minus a c)
                    (plus (minus (minus a b) c) b)))
                (logic.rewrite_r nat
                 (plus b (minus a (plus c b)))
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq sttfa.bool (le (minus a c) __)
                    (le (minus a c)
                     (plus (minus (minus a b) c) b)))
                 (logic.rewrite_r nat
                  (plus b (minus (minus a b) c))
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq sttfa.bool
                     (le (minus a c)
                      (plus b (minus a (plus c b))))
                     (le (minus a c) __))
                  (logic.rewrite_l nat (minus (minus a b) c)
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq sttfa.bool
                      (le (minus a c) (plus b __))
                      (le (minus a c)
                       (plus b (minus (minus a b) c))))
                   (logic.refl sttfa.bool
                    (le (minus a c)
                     (plus b (minus (minus a b) c))))
                   (minus a (plus c b))
                   (logic.rewrite_l nat (plus b c)
                    (λ (__ : sttfa.etap (sttfa.p nat)),
                       logic.eq nat (minus (minus a b) c)
                       (minus a __))
                    (minus_plus a b c) (plus c b)
                    (commutative_plus b c)))
                  (plus (minus (minus a b) c) b)
                  (commutative_plus (minus (minus a b) c) b))
                 (plus (minus a (plus c b)) b)
                 (commutative_plus (minus a (plus c b)) b))
                (minus (minus a c) b) (minus_plus a c b))))
             (logic.rewrite_l nat (minus (minus a b) c)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq sttfa.bool
                 (le (minus (minus a c) b) __)
                 (le (minus (minus a c) b)
                  (minus (minus a b) c)))
              (logic.refl sttfa.bool
               (le (minus (minus a c) b)
                (minus (minus a b) c)))
              (minus (plus (minus (minus a b) c) b) b)
              (minus_plus_m_m (minus (minus a b) c) b)));
symbol minus_le_minus_minus_comm
  : sttfa.eps
    (sttfa.forall nat
     (λ (b : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (c : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (a : sttfa.etap (sttfa.p nat)),
              sttfa.impl (le c b)
              (logic.eq nat (minus a (minus b c))
               (minus (plus a c) b))))))
  ≔ λ (b : sttfa.etap (sttfa.p nat)),
        λ (c : sttfa.etap (sttfa.p nat)),
          λ (a : sttfa.etap (sttfa.p nat)),
            λ (H : sttfa.eps (le c b)),
              logic.eq_ind_r nat (plus (minus b c) c)
              (λ (x : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (minus a (minus b c))
                 (minus (plus a c) x))
              (logic.rewrite_r nat (plus c a)
               (λ (__ : sttfa.etap (sttfa.p nat)),
                  logic.eq nat (minus a (minus b c))
                  (minus __ (plus (minus b c) c)))
               (logic.rewrite_r nat (plus c (minus b c))
                (λ (__ : sttfa.etap (sttfa.p nat)),
                   logic.eq nat (minus a (minus b c))
                   (minus (plus c a) __))
                (logic.rewrite_l nat
                 (minus (minus (plus c a) c) (minus b c))
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq nat (minus a (minus b c)) __)
                 (logic.rewrite_r nat (minus (plus c a) c)
                  (λ (__ : sttfa.etap (sttfa.p nat)),
                     logic.eq nat (minus __ (minus b c))
                     (minus (minus (plus c a) c) (minus b c)))
                  (logic.refl nat
                   (minus (minus (plus c a) c) (minus b c)))
                  a
                  (logic.rewrite_l nat (plus a c)
                   (λ (__ : sttfa.etap (sttfa.p nat)),
                      logic.eq nat a (minus __ c))
                   (minus_plus_m_m a c) (plus c a)
                   (commutative_plus a c)))
                 (minus (plus c a) (plus c (minus b c)))
                 (minus_plus (plus c a) c (minus b c)))
                (plus (minus b c) c)
                (commutative_plus (minus b c) c))
               (plus a c) (commutative_plus a c))
              b (plus_minus_m_m b c H);
symbol minus_plus_plus_l
  : sttfa.eps
    (sttfa.forall nat
     (λ (x : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (y : sttfa.etap (sttfa.p nat)),
           sttfa.forall nat
           (λ (h : sttfa.etap (sttfa.p nat)),
              logic.eq nat (minus (plus x h) (plus y h))
              (minus x y)))))
  ≔ λ (x : sttfa.etap (sttfa.p nat)),
        λ (y : sttfa.etap (sttfa.p nat)),
          λ (h : sttfa.etap (sttfa.p nat)),
            logic.rewrite_l nat
            (minus (minus (plus x h) y) h)
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq nat __ (minus x y))
            (logic.rewrite_r nat (minus x y)
             (λ (__ : sttfa.etap (sttfa.p nat)),
                logic.eq nat __ (minus x y))
             (logic.refl nat (minus x y))
             (minus (minus (plus x h) y) h)
             (logic.rewrite_r nat (minus (plus x h) h)
              (λ (__ : sttfa.etap (sttfa.p nat)),
                 logic.eq nat (minus (minus (plus x h) y) h)
                 (minus __ y))
              (minus_minus_comm (plus x h) y h) x
              (minus_plus_m_m x h)))
            (minus (plus x h) (plus y h))
            (minus_plus (plus x h) y h);
constant symbol eqb
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat bool.bool)));
constant symbol eqb_body
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat bool.bool)));
constant symbol axiom_eqb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat bool.bool) (eqb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) eqb_body n)));
symbol eq_eqb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool) (eqb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) eqb_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat bool.bool) (eqb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) eqb_body n)
        (axiom_eqb n);
symbol sym_eq_eqb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (filter_nat_type (sttfa.arrow nat bool.bool) eqb_body n)
        (eqb n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat bool.bool) (eqb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) eqb_body n)
        (eq_eqb n);
constant symbol axiom_eqb_body_O
  : sttfa.eps
    (connectives.equal (sttfa.arrow nat bool.bool) (eqb_body O)
     (λ (m : sttfa.etap (sttfa.p nat)),
        match_nat_type bool.bool bool.true
        (λ (q : sttfa.etap (sttfa.p nat)), bool.false) m));
symbol eq_eqb_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat bool.bool) (eqb_body O)
     (λ (m : sttfa.etap (sttfa.p nat)),
        match_nat_type bool.bool bool.true
        (λ (q : sttfa.etap (sttfa.p nat)), bool.false) m))
  ≔ connectives.equal_leibniz (sttfa.arrow nat bool.bool)
      (eqb_body O)
      (λ (m : sttfa.etap (sttfa.p nat)),
         match_nat_type bool.bool bool.true
         (λ (q : sttfa.etap (sttfa.p nat)), bool.false) m)
      axiom_eqb_body_O;
symbol sym_eq_eqb_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat bool.bool)
     (λ (m : sttfa.etap (sttfa.p nat)),
        match_nat_type bool.bool bool.true
        (λ (q : sttfa.etap (sttfa.p nat)), bool.false) m)
     (eqb_body O))
  ≔ leibniz.sym_leibniz (sttfa.arrow nat bool.bool)
      (eqb_body O)
      (λ (m : sttfa.etap (sttfa.p nat)),
         match_nat_type bool.bool bool.true
         (λ (q : sttfa.etap (sttfa.p nat)), bool.false) m)
      eq_eqb_body_O;
constant symbol axiom_eqb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat bool.bool)
        (eqb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m)));
symbol eq_eqb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (eqb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat bool.bool)
        (eqb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m)
        (axiom_eqb_body_S n);
symbol sym_eq_eqb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m)
        (eqb_body (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat bool.bool)
        (eqb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m)
        (eq_eqb_body_S n);
symbol eqb_elim
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
              sttfa.impl (sttfa.impl (logic.eq nat n m) (P bool.true))
              (sttfa.impl
               (sttfa.impl (connectives.Not (logic.eq nat n m))
                (P bool.false))
               (P (eqb n m)))))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
              sttfa.impl (sttfa.impl (logic.eq nat __ _0) (P bool.true))
              (sttfa.impl
               (sttfa.impl (connectives.Not (logic.eq nat __ _0))
                (P bool.false))
               (P (eqb __ _0)))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         match_nat_prop
         (λ (__ : sttfa.etap (sttfa.p nat)),
            sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               sttfa.impl
               (sttfa.impl (logic.eq nat O __) (P bool.true))
               (sttfa.impl
                (sttfa.impl (connectives.Not (logic.eq nat O __))
                 (P bool.false))
                (P (eqb O __)))))
         (sym_eq_eqb O
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
             sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
             (λ
                (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
                sttfa.impl
                (sttfa.impl (logic.eq nat O O) (P bool.true))
                (sttfa.impl
                 (sttfa.impl (connectives.Not (logic.eq nat O O))
                  (P bool.false))
                 (P (y O)))))
          (sym_eq_filter_nat_type_O (sttfa.arrow nat bool.bool)
           eqb_body
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
              (λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                 ),
                 sttfa.impl
                 (sttfa.impl (logic.eq nat O O) (P bool.true))
                 (sttfa.impl
                  (sttfa.impl
                   (connectives.Not (logic.eq nat O O))
                   (P bool.false))
                  (P (y O)))))
           (sym_eq_eqb_body_O
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
               sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (logic.eq nat O O) (P bool.true))
                  (sttfa.impl
                   (sttfa.impl
                    (connectives.Not (logic.eq nat O O))
                    (P bool.false))
                   (P (y O)))))
            (sym_eq_match_nat_type_O bool.bool bool.true
             (λ (q : sttfa.etap (sttfa.p nat)), bool.false)
             (λ (y : sttfa.etap (sttfa.p bool.bool)),
                sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl
                   (sttfa.impl (logic.eq nat O O) (P bool.true))
                   (sttfa.impl
                    (sttfa.impl
                     (connectives.Not (logic.eq nat O O))
                     (P bool.false))
                    (P y))))
             (λ
                (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
                λ
                  (
                  auto : sttfa.eps
                         (sttfa.impl (logic.eq nat O O)
                          (P bool.true))
                  ),
                  λ
                    (
                    auto' : sttfa.eps
                            (sttfa.impl
                             (connectives.Not (logic.eq nat O O))
                             (P bool.false))
                    ), auto (logic.refl nat O))))))
         (λ (auto : sttfa.etap (sttfa.p nat)),
            sym_eq_eqb O
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
               sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (logic.eq nat O (S auto))
                   (P bool.true))
                  (sttfa.impl
                   (sttfa.impl
                    (connectives.Not (logic.eq nat O (S auto)))
                    (P bool.false))
                   (P (y (S auto))))))
            (sym_eq_filter_nat_type_O (sttfa.arrow nat bool.bool)
             eqb_body
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
                sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl
                   (sttfa.impl (logic.eq nat O (S auto))
                    (P bool.true))
                   (sttfa.impl
                    (sttfa.impl
                     (connectives.Not (logic.eq nat O (S auto)))
                     (P bool.false))
                    (P (y (S auto))))))
             (sym_eq_eqb_body_O
              (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
                 sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                 (λ
                    (
                    P : sttfa.etap
                        (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                    ),
                    sttfa.impl
                    (sttfa.impl (logic.eq nat O (S auto))
                     (P bool.true))
                    (sttfa.impl
                     (sttfa.impl
                      (connectives.Not (logic.eq nat O (S auto)))
                      (P bool.false))
                     (P (y (S auto))))))
              (sym_eq_match_nat_type_S bool.bool bool.true
               (λ (q : sttfa.etap (sttfa.p nat)), bool.false) auto
               (λ (y : sttfa.etap (sttfa.p bool.bool)),
                  sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                  (λ
                     (
                     P : sttfa.etap
                         (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                     ),
                     sttfa.impl
                     (sttfa.impl (logic.eq nat O (S auto))
                      (P bool.true))
                     (sttfa.impl
                      (sttfa.impl
                       (connectives.Not (logic.eq nat O (S auto)))
                       (P bool.false))
                      (P y))))
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  λ
                    (
                    auto' : sttfa.eps
                            (sttfa.impl (logic.eq nat O (S auto))
                             (P bool.true))
                    ),
                    λ
                      (
                      auto'' : sttfa.eps
                               (sttfa.impl
                                (connectives.Not
                                 (logic.eq nat O (S auto)))
                                (P bool.false))
                      ), auto'' (not_eq_O_S auto))))))
         n)
      (λ (n : sttfa.etap (sttfa.p nat)),
         sym_eq_eqb (S n)
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
            sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               sttfa.impl
               (sttfa.impl (logic.eq nat (S n) O) (P bool.true))
               (sttfa.impl
                (sttfa.impl
                 (connectives.Not (logic.eq nat (S n) O))
                 (P bool.false))
                (P (y O)))))
         (sym_eq_filter_nat_type_S (sttfa.arrow nat bool.bool)
          eqb_body n
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
             sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
             (λ
                (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
                sttfa.impl
                (sttfa.impl (logic.eq nat (S n) O) (P bool.true))
                (sttfa.impl
                 (sttfa.impl
                  (connectives.Not (logic.eq nat (S n) O))
                  (P bool.false))
                 (P (y O)))))
          (sym_eq_eqb_body_S n
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
              (λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                 ),
                 sttfa.impl
                 (sttfa.impl (logic.eq nat (S n) O) (P bool.true))
                 (sttfa.impl
                  (sttfa.impl
                   (connectives.Not (logic.eq nat (S n) O))
                   (P bool.false))
                  (P (y O)))))
           (sym_eq_match_nat_type_O bool.bool bool.false
            (λ (q : sttfa.etap (sttfa.p nat)), eqb n q)
            (λ (y : sttfa.etap (sttfa.p bool.bool)),
               sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (logic.eq nat (S n) O)
                   (P bool.true))
                  (sttfa.impl
                   (sttfa.impl
                    (connectives.Not (logic.eq nat (S n) O))
                    (P bool.false))
                   (P y))))
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               λ
                 (
                 auto : sttfa.eps
                        (sttfa.impl (logic.eq nat (S n) O)
                         (P bool.true))
                 ),
                 λ
                   (
                   auto' : sttfa.eps
                           (sttfa.impl
                            (connectives.Not
                             (logic.eq nat (S n) O))
                            (P bool.false))
                   ),
                   auto'
                   (logic.sym_not_eq nat O (S n)
                    (not_eq_O_S n)))))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           sym_eq_eqb (S n)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.impl
              (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (logic.eq nat n m) (P bool.true))
                  (sttfa.impl
                   (sttfa.impl (connectives.Not (logic.eq nat n m))
                    (P bool.false))
                   (P (eqb n m)))))
              (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (logic.eq nat (S n) (S m))
                   (P bool.true))
                  (sttfa.impl
                   (sttfa.impl
                    (connectives.Not (logic.eq nat (S n) (S m)))
                    (P bool.false))
                   (P (y (S m)))))))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat bool.bool)
            eqb_body n
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
               sttfa.impl
               (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl
                   (sttfa.impl (logic.eq nat n m) (P bool.true))
                   (sttfa.impl
                    (sttfa.impl (connectives.Not (logic.eq nat n m))
                     (P bool.false))
                    (P (eqb n m)))))
               (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl
                   (sttfa.impl (logic.eq nat (S n) (S m))
                    (P bool.true))
                   (sttfa.impl
                    (sttfa.impl
                     (connectives.Not (logic.eq nat (S n) (S m)))
                     (P bool.false))
                    (P (y (S m)))))))
            (sym_eq_eqb_body_S n
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
                sttfa.impl
                (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                 (λ
                    (
                    P : sttfa.etap
                        (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                    ),
                    sttfa.impl
                    (sttfa.impl (logic.eq nat n m) (P bool.true))
                    (sttfa.impl
                     (sttfa.impl (connectives.Not (logic.eq nat n m))
                      (P bool.false))
                     (P (eqb n m)))))
                (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                 (λ
                    (
                    P : sttfa.etap
                        (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                    ),
                    sttfa.impl
                    (sttfa.impl (logic.eq nat (S n) (S m))
                     (P bool.true))
                    (sttfa.impl
                     (sttfa.impl
                      (connectives.Not (logic.eq nat (S n) (S m)))
                      (P bool.false))
                     (P (y (S m)))))))
             (sym_eq_match_nat_type_S bool.bool bool.false
              (λ (q : sttfa.etap (sttfa.p nat)), eqb n q) m
              (λ (y : sttfa.etap (sttfa.p bool.bool)),
                 sttfa.impl
                 (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                  (λ
                     (
                     P : sttfa.etap
                         (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                     ),
                     sttfa.impl
                     (sttfa.impl (logic.eq nat n m) (P bool.true))
                     (sttfa.impl
                      (sttfa.impl (connectives.Not (logic.eq nat n m))
                       (P bool.false))
                      (P (eqb n m)))))
                 (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                  (λ
                     (
                     P : sttfa.etap
                         (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                     ),
                     sttfa.impl
                     (sttfa.impl (logic.eq nat (S n) (S m))
                      (P bool.true))
                     (sttfa.impl
                      (sttfa.impl
                       (connectives.Not
                        (logic.eq nat (S n) (S m)))
                       (P bool.false))
                      (P y)))))
              (λ
                 (
                 auto : sttfa.eps
                        (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                         (λ
                            (
                            P : sttfa.etap
                                (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                            ),
                            sttfa.impl
                            (sttfa.impl (logic.eq nat n m) (P bool.true))
                            (sttfa.impl
                             (sttfa.impl
                              (connectives.Not (logic.eq nat n m))
                              (P bool.false))
                             (P (eqb n m)))))
                 ),
                 λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   λ
                     (
                     auto' : sttfa.eps
                             (sttfa.impl
                              (logic.eq nat (S n) (S m))
                              (P bool.true))
                     ),
                     λ
                       (
                       auto'' : sttfa.eps
                                (sttfa.impl
                                 (connectives.Not
                                  (logic.eq nat (S n) (S m)))
                                 (P bool.false))
                       ),
                       auto P
                       (λ (auto''' : sttfa.eps (logic.eq nat n m)),
                          auto'
                          (logic.rewrite_l nat n
                           (λ (__ : sttfa.etap (sttfa.p nat)),
                              logic.eq nat (S n) (S __))
                           (logic.refl nat (S n)) m auto'''))
                       (λ
                          (
                          auto''' : sttfa.eps
                                    (connectives.Not (logic.eq nat n m))
                          ), auto'' (not_eq_S n m auto''')))))));
symbol eqb_n_n
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        logic.eq bool.bool (eqb n n) bool.true))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        nat_ind
        (λ (_x_365 : sttfa.etap (sttfa.p nat)),
           logic.eq bool.bool (eqb _x_365 _x_365) bool.true)
        (sym_eq_eqb O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
            logic.eq bool.bool (y O) bool.true)
         (sym_eq_filter_nat_type_O (sttfa.arrow nat bool.bool)
          eqb_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
             logic.eq bool.bool (y O) bool.true)
          (sym_eq_eqb_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              logic.eq bool.bool (y O) bool.true)
           (sym_eq_match_nat_type_O bool.bool bool.true
            (λ (q : sttfa.etap (sttfa.p nat)), bool.false)
            (λ (y : sttfa.etap (sttfa.p bool.bool)),
               logic.eq bool.bool y bool.true)
            (logic.refl bool.bool bool.true)))))
        (λ (x_366 : sttfa.etap (sttfa.p nat)),
           sym_eq_eqb (S x_366)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.impl (logic.eq bool.bool (eqb x_366 x_366) bool.true)
              (logic.eq bool.bool (y (S x_366)) bool.true))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat bool.bool)
            eqb_body x_366
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
               sttfa.impl
               (logic.eq bool.bool (eqb x_366 x_366) bool.true)
               (logic.eq bool.bool (y (S x_366)) bool.true))
            (sym_eq_eqb_body_S x_366
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
                sttfa.impl
                (logic.eq bool.bool (eqb x_366 x_366) bool.true)
                (logic.eq bool.bool (y (S x_366)) bool.true))
             (sym_eq_match_nat_type_S bool.bool bool.false
              (λ (q : sttfa.etap (sttfa.p nat)), eqb x_366 q) x_366
              (λ (y : sttfa.etap (sttfa.p bool.bool)),
                 sttfa.impl
                 (logic.eq bool.bool (eqb x_366 x_366) bool.true)
                 (logic.eq bool.bool y bool.true))
              (λ
                 (
                 _x_368 : sttfa.eps
                          (logic.eq bool.bool (eqb x_366 x_366) bool.true)
                 ),
                 logic.rewrite_r bool.bool bool.true
                 (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                    logic.eq bool.bool __ bool.true)
                 (logic.refl bool.bool bool.true) (eqb x_366 x_366)
                 _x_368)))))
        n;
symbol eqb_true_to_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (logic.eq bool.bool (eqb n m) bool.true)
           (logic.eq nat n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          eqb_elim n m
          (λ (__ : sttfa.etap (sttfa.p bool.bool)),
             sttfa.impl (logic.eq bool.bool __ bool.true)
             (logic.eq nat n m))
          (λ (auto : sttfa.eps (logic.eq nat n m)),
             λ (auto' : sttfa.eps (logic.eq bool.bool bool.true bool.true)),
               logic.rewrite_l nat n
               (λ (__ : sttfa.etap (sttfa.p nat)), logic.eq nat n __)
               (logic.refl nat n) m auto)
          (λ (__ : sttfa.eps (connectives.Not (logic.eq nat n m))),
             λ (abs : sttfa.eps (logic.eq bool.bool bool.false bool.true)),
               connectives.falsity (logic.eq nat n m)
               (logic.absurd (logic.eq bool.bool bool.true bool.false)
                (logic.rewrite_r bool.bool bool.true
                 (λ (__1 : sttfa.etap (sttfa.p bool.bool)),
                    logic.eq bool.bool bool.true __1)
                 (logic.refl bool.bool bool.true) bool.false abs)
                bool.not_eq_true_false));
symbol eqb_false_to_not_eq
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (logic.eq bool.bool (eqb n m) bool.false)
           (connectives.Not (logic.eq nat n m)))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          eqb_elim n m
          (λ (__ : sttfa.etap (sttfa.p bool.bool)),
             sttfa.impl (logic.eq bool.bool __ bool.false)
             (connectives.Not (logic.eq nat n m)))
          (λ (auto : sttfa.eps (logic.eq nat n m)),
             λ
               (auto' : sttfa.eps (logic.eq bool.bool bool.true bool.false)),
               logic.not_to_not (logic.eq nat n m)
               (logic.eq bool.bool bool.true bool.false)
               (λ (auto'' : sttfa.eps (logic.eq nat n m)),
                  logic.rewrite_l bool.bool bool.true
                  (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                     logic.eq bool.bool bool.true __)
                  (logic.refl bool.bool bool.true) bool.false auto')
               bool.not_eq_true_false)
          (λ (auto : sttfa.eps (connectives.Not (logic.eq nat n m))),
             λ
               (auto' : sttfa.eps (logic.eq bool.bool bool.false bool.false)),
               auto);
symbol eq_to_eqb_true
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (logic.eq nat n m)
           (logic.eq bool.bool (eqb n m) bool.true))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (auto : sttfa.eps (logic.eq nat n m)),
            logic.rewrite_l nat n
            (λ (__ : sttfa.etap (sttfa.p nat)),
               logic.eq bool.bool (eqb n __) bool.true)
            (logic.rewrite_r bool.bool bool.true
             (λ (__ : sttfa.etap (sttfa.p bool.bool)),
                logic.eq bool.bool __ bool.true)
             (logic.refl bool.bool bool.true) (eqb n n) (eqb_n_n n))
            m auto;
symbol not_eq_to_eqb_false
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (logic.eq nat n m))
           (logic.eq bool.bool (eqb n m) bool.false))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          λ (noteq : sttfa.eps (connectives.Not (logic.eq nat n m))),
            eqb_elim n m
            (λ (__ : sttfa.etap (sttfa.p bool.bool)),
               logic.eq bool.bool __ bool.false)
            (λ (Heq : sttfa.eps (logic.eq nat n m)),
               connectives.falsity (logic.eq bool.bool bool.true bool.false)
               (logic.absurd (logic.eq nat n m)
                (logic.rewrite_l nat n
                 (λ (__ : sttfa.etap (sttfa.p nat)),
                    logic.eq nat n __)
                 (logic.refl nat n) m Heq)
                noteq))
            (λ (auto : sttfa.eps (connectives.Not (logic.eq nat n m))),
               logic.refl bool.bool bool.false);
constant symbol leb
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat bool.bool)));
constant symbol leb_body
  : sttfa.etap
    (sttfa.p (sttfa.arrow nat (sttfa.arrow nat bool.bool)));
constant symbol axiom_leb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat bool.bool) (leb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) leb_body n)));
symbol eq_leb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool) (leb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) leb_body n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat bool.bool) (leb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) leb_body n)
        (axiom_leb n);
symbol sym_eq_leb
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (filter_nat_type (sttfa.arrow nat bool.bool) leb_body n)
        (leb n)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat bool.bool) (leb n)
        (filter_nat_type (sttfa.arrow nat bool.bool) leb_body n)
        (eq_leb n);
constant symbol axiom_leb_body_O
  : sttfa.eps
    (connectives.equal (sttfa.arrow nat bool.bool) (leb_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), bool.true));
symbol eq_leb_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat bool.bool) (leb_body O)
     (λ (m : sttfa.etap (sttfa.p nat)), bool.true))
  ≔ connectives.equal_leibniz (sttfa.arrow nat bool.bool)
      (leb_body O) (λ (m : sttfa.etap (sttfa.p nat)), bool.true)
      axiom_leb_body_O;
symbol sym_eq_leb_body_O
  : sttfa.eps
    (leibniz.leibniz (sttfa.arrow nat bool.bool)
     (λ (m : sttfa.etap (sttfa.p nat)), bool.true) (leb_body O))
  ≔ leibniz.sym_leibniz (sttfa.arrow nat bool.bool)
      (leb_body O) (λ (m : sttfa.etap (sttfa.p nat)), bool.true)
      eq_leb_body_O;
constant symbol axiom_leb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal (sttfa.arrow nat bool.bool)
        (leb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m)));
symbol eq_leb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (leb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m)))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        connectives.equal_leibniz (sttfa.arrow nat bool.bool)
        (leb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m)
        (axiom_leb_body_S n);
symbol sym_eq_leb_body_S
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.leibniz (sttfa.arrow nat bool.bool)
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m)
        (leb_body (S n))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        leibniz.sym_leibniz (sttfa.arrow nat bool.bool)
        (leb_body (S n))
        (λ (m : sttfa.etap (sttfa.p nat)),
           match_nat_type bool.bool bool.false
           (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m)
        (eq_leb_body_S n);
symbol leb_elim
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
              sttfa.impl (sttfa.impl (le n m) (P bool.true))
              (sttfa.impl
               (sttfa.impl (connectives.Not (le n m)) (P bool.false))
               (P (leb n m)))))))
  ≔ nat_elim2
      (λ (__ : sttfa.etap (sttfa.p nat)),
         λ (_0 : sttfa.etap (sttfa.p nat)),
           sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
              sttfa.impl (sttfa.impl (le __ _0) (P bool.true))
              (sttfa.impl
               (sttfa.impl (connectives.Not (le __ _0)) (P bool.false))
               (P (leb __ _0)))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         sym_eq_leb O
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
            sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               sttfa.impl (sttfa.impl (le O n) (P bool.true))
               (sttfa.impl
                (sttfa.impl (connectives.Not (le O n)) (P bool.false))
                (P (y n)))))
         (sym_eq_filter_nat_type_O (sttfa.arrow nat bool.bool)
          leb_body
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
             sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
             (λ
                (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
                sttfa.impl (sttfa.impl (le O n) (P bool.true))
                (sttfa.impl
                 (sttfa.impl (connectives.Not (le O n))
                  (P bool.false))
                 (P (y n)))))
          (sym_eq_leb_body_O
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
              (λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                 ),
                 sttfa.impl (sttfa.impl (le O n) (P bool.true))
                 (sttfa.impl
                  (sttfa.impl (connectives.Not (le O n))
                   (P bool.false))
                  (P (y n)))))
           (λ (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
              λ
                (auto : sttfa.eps (sttfa.impl (le O n) (P bool.true))
                ),
                λ
                  (
                  auto' : sttfa.eps
                          (sttfa.impl (connectives.Not (le O n))
                           (P bool.false))
                  ), auto (le_O_n n)))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         sym_eq_leb (S n)
         (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
            sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               sttfa.impl (sttfa.impl (le (S n) O) (P bool.true))
               (sttfa.impl
                (sttfa.impl (connectives.Not (le (S n) O))
                 (P bool.false))
                (P (y O)))))
         (sym_eq_filter_nat_type_S (sttfa.arrow nat bool.bool)
          leb_body n
          (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
             sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
             (λ
                (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
                sttfa.impl
                (sttfa.impl (le (S n) O) (P bool.true))
                (sttfa.impl
                 (sttfa.impl (connectives.Not (le (S n) O))
                  (P bool.false))
                 (P (y O)))))
          (sym_eq_leb_body_S n
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
              (λ
                 (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                 ),
                 sttfa.impl
                 (sttfa.impl (le (S n) O) (P bool.true))
                 (sttfa.impl
                  (sttfa.impl (connectives.Not (le (S n) O))
                   (P bool.false))
                  (P (y O)))))
           (sym_eq_match_nat_type_O bool.bool bool.false
            (λ (q : sttfa.etap (sttfa.p nat)), leb n q)
            (λ (y : sttfa.etap (sttfa.p bool.bool)),
               sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (le (S n) O) (P bool.true))
                  (sttfa.impl
                   (sttfa.impl (connectives.Not (le (S n) O))
                    (P bool.false))
                   (P y))))
            (λ
               (P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))),
               λ
                 (
                 auto : sttfa.eps
                        (sttfa.impl (le (S n) O) (P bool.true))
                 ),
                 λ
                   (
                   auto' : sttfa.eps
                           (sttfa.impl
                            (connectives.Not (le (S n) O))
                            (P bool.false))
                   ), auto' (not_le_Sn_O n))))))
      (λ (n : sttfa.etap (sttfa.p nat)),
         λ (m : sttfa.etap (sttfa.p nat)),
           sym_eq_leb (S n)
           (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
              sttfa.impl
              (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl (sttfa.impl (le n m) (P bool.true))
                  (sttfa.impl
                   (sttfa.impl (connectives.Not (le n m)) (P bool.false))
                   (P (leb n m)))))
              (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
               (λ
                  (
                  P : sttfa.etap (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                  ),
                  sttfa.impl
                  (sttfa.impl (le (S n) (S m)) (P bool.true))
                  (sttfa.impl
                   (sttfa.impl (connectives.Not (le (S n) (S m)))
                    (P bool.false))
                   (P (y (S m)))))))
           (sym_eq_filter_nat_type_S (sttfa.arrow nat bool.bool)
            leb_body n
            (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
               sttfa.impl
               (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl (sttfa.impl (le n m) (P bool.true))
                   (sttfa.impl
                    (sttfa.impl (connectives.Not (le n m)) (P bool.false))
                    (P (leb n m)))))
               (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                (λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   sttfa.impl
                   (sttfa.impl (le (S n) (S m)) (P bool.true))
                   (sttfa.impl
                    (sttfa.impl
                     (connectives.Not (le (S n) (S m)))
                     (P bool.false))
                    (P (y (S m)))))))
            (sym_eq_leb_body_S n
             (λ (y : sttfa.etap (sttfa.p (sttfa.arrow nat bool.bool))),
                sttfa.impl
                (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                 (λ
                    (
                    P : sttfa.etap
                        (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                    ),
                    sttfa.impl (sttfa.impl (le n m) (P bool.true))
                    (sttfa.impl
                     (sttfa.impl (connectives.Not (le n m))
                      (P bool.false))
                     (P (leb n m)))))
                (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                 (λ
                    (
                    P : sttfa.etap
                        (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                    ),
                    sttfa.impl
                    (sttfa.impl (le (S n) (S m)) (P bool.true))
                    (sttfa.impl
                     (sttfa.impl
                      (connectives.Not (le (S n) (S m)))
                      (P bool.false))
                     (P (y (S m)))))))
             (sym_eq_match_nat_type_S bool.bool bool.false
              (λ (q : sttfa.etap (sttfa.p nat)), leb n q) m
              (λ (y : sttfa.etap (sttfa.p bool.bool)),
                 sttfa.impl
                 (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                  (λ
                     (
                     P : sttfa.etap
                         (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                     ),
                     sttfa.impl (sttfa.impl (le n m) (P bool.true))
                     (sttfa.impl
                      (sttfa.impl (connectives.Not (le n m))
                       (P bool.false))
                      (P (leb n m)))))
                 (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                  (λ
                     (
                     P : sttfa.etap
                         (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                     ),
                     sttfa.impl
                     (sttfa.impl (le (S n) (S m)) (P bool.true))
                     (sttfa.impl
                      (sttfa.impl
                       (connectives.Not (le (S n) (S m)))
                       (P bool.false))
                      (P y)))))
              (λ
                 (
                 Hind : sttfa.eps
                        (sttfa.forall (sttfa.arrow bool.bool sttfa.bool)
                         (λ
                            (
                            P : sttfa.etap
                                (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                            ),
                            sttfa.impl
                            (sttfa.impl (le n m) (P bool.true))
                            (sttfa.impl
                             (sttfa.impl (connectives.Not (le n m))
                              (P bool.false))
                             (P (leb n m)))))
                 ),
                 λ
                   (
                   P : sttfa.etap
                       (sttfa.p (sttfa.arrow bool.bool sttfa.bool))
                   ),
                   λ
                     (
                     Pt : sttfa.eps
                          (sttfa.impl (le (S n) (S m))
                           (P bool.true))
                     ),
                     λ
                       (
                       Pf : sttfa.eps
                            (sttfa.impl
                             (connectives.Not (le (S n) (S m)))
                             (P bool.false))
                       ),
                       Hind P
                       (λ (lenm : sttfa.eps (le n m)),
                          Pt (le_S_S n m lenm))
                       (λ
                          (nlenm : sttfa.eps (connectives.Not (le n m))),
                          Pf (not_le_to_not_le_S_S n m nlenm)))))));
symbol leb_true_to_le
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (logic.eq bool.bool (leb n m) bool.true)
           (le n m))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          leb_elim n m
          (λ (__ : sttfa.etap (sttfa.p bool.bool)),
             sttfa.impl (logic.eq bool.bool __ bool.true) (le n m))
          (λ (auto : sttfa.eps (le n m)),
             λ (auto' : sttfa.eps (logic.eq bool.bool bool.true bool.true)),
               auto)
          (λ (__ : sttfa.eps (connectives.Not (le n m))),
             λ (abs : sttfa.eps (logic.eq bool.bool bool.false bool.true)),
               connectives.falsity (le n m)
               (logic.absurd (logic.eq bool.bool bool.true bool.false)
                (logic.rewrite_r bool.bool bool.true
                 (λ (__1 : sttfa.etap (sttfa.p bool.bool)),
                    logic.eq bool.bool bool.true __1)
                 (logic.refl bool.bool bool.true) bool.false abs)
                bool.not_eq_true_false));
symbol le_to_leb_true
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (le n m)
           (logic.eq bool.bool (leb n m) bool.true))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          leb_elim n m
          (λ (__ : sttfa.etap (sttfa.p bool.bool)),
             sttfa.impl (le n m) (logic.eq bool.bool __ bool.true))
          (λ (auto : sttfa.eps (le n m)),
             λ (auto' : sttfa.eps (le n m)),
               logic.refl bool.bool bool.true)
          (λ (H : sttfa.eps (connectives.Not (le n m))),
             λ (H1 : sttfa.eps (le n m)),
               connectives.falsity (logic.eq bool.bool bool.false bool.true)
               (logic.absurd (le n m) H1 H));
symbol not_le_to_leb_false
  : sttfa.eps
    (sttfa.forall nat
     (λ (n : sttfa.etap (sttfa.p nat)),
        sttfa.forall nat
        (λ (m : sttfa.etap (sttfa.p nat)),
           sttfa.impl (connectives.Not (le n m))
           (logic.eq bool.bool (leb n m) bool.false))))
  ≔ λ (n : sttfa.etap (sttfa.p nat)),
        λ (m : sttfa.etap (sttfa.p nat)),
          leb_elim n m
          (λ (__ : sttfa.etap (sttfa.p bool.bool)),
             sttfa.impl (connectives.Not (le n m))
             (logic.eq bool.bool __ bool.false))
          (λ (H : sttfa.eps (le n m)),
             λ (H1 : sttfa.eps (connectives.Not (le n m))),
               connectives.falsity (logic.eq bool.bool bool.true bool.false)
               (logic.absurd (le n m) H H1))
          (λ (auto : sttfa.eps (connectives.Not (le n m))),
             λ (auto' : sttfa.eps (connectives.Not (le n m))),
               logic.refl bool.bool bool.false);
