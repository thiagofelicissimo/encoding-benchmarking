require tests.connectives as connectives;
require tests.leibniz as leibniz;
require tests.logic as logic;
require tests.relations as relations;
require tests.sttfa as sttfa;
constant symbol bool : sttfa.{|type|};
constant symbol true : sttfa.etap (sttfa.p bool);
constant symbol false : sttfa.etap (sttfa.p bool);
constant symbol match_bool_prop
  : sttfa.eps
    (sttfa.forall (sttfa.arrow bool sttfa.bool)
     (λ (return : sttfa.etap (sttfa.p (sttfa.arrow bool sttfa.bool))),
        sttfa.impl (return true)
        (sttfa.impl (return false)
         (sttfa.forall bool
          (λ (z : sttfa.etap (sttfa.p bool)), return z)))));
constant symbol match_bool_type
  : sttfa.etap
    (sttfa.forallK
     (λ (return : sttfa.{|type|}),
        sttfa.p
        (sttfa.arrow return
         (sttfa.arrow return (sttfa.arrow bool return)))));
constant symbol axiom_match_bool_type_true
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              connectives.equal return
              (match_bool_type return case_true case_false true)
              case_true))));
symbol eq_match_bool_type_true
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              leibniz.leibniz return
              (match_bool_type return case_true case_false true)
              case_true))))
  ≔ λ (return : sttfa.{|type|}),
        λ (case_true : sttfa.etap (sttfa.p return)),
          λ (case_false : sttfa.etap (sttfa.p return)),
            connectives.equal_leibniz return
            (match_bool_type return case_true case_false true)
            case_true
            (axiom_match_bool_type_true return case_true case_false);
constant symbol axiom_match_bool_type_false
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              connectives.equal return
              (match_bool_type return case_true case_false false)
              case_false))));
symbol eq_match_bool_type_false
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              leibniz.leibniz return
              (match_bool_type return case_true case_false false)
              case_false))))
  ≔ λ (return : sttfa.{|type|}),
        λ (case_true : sttfa.etap (sttfa.p return)),
          λ (case_false : sttfa.etap (sttfa.p return)),
            connectives.equal_leibniz return
            (match_bool_type return case_true case_false false)
            case_false
            (axiom_match_bool_type_false return case_true case_false);
symbol sym_eq_match_bool_type_true
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              leibniz.leibniz return case_true
              (match_bool_type return case_true case_false true)))))
  ≔ λ (return : sttfa.{|type|}),
        λ (case_true : sttfa.etap (sttfa.p return)),
          λ (case_false : sttfa.etap (sttfa.p return)),
            leibniz.sym_leibniz return
            (match_bool_type return case_true case_false true)
            case_true
            (eq_match_bool_type_true return case_true case_false);
symbol sym_eq_match_bool_type_false
  : sttfa.eps
    (sttfa.forallP
     (λ (return : sttfa.{|type|}),
        sttfa.forall return
        (λ (case_true : sttfa.etap (sttfa.p return)),
           sttfa.forall return
           (λ (case_false : sttfa.etap (sttfa.p return)),
              leibniz.leibniz return case_false
              (match_bool_type return case_true case_false false)))))
  ≔ λ (return : sttfa.{|type|}),
        λ (case_true : sttfa.etap (sttfa.p return)),
          λ (case_false : sttfa.etap (sttfa.p return)),
            leibniz.sym_leibniz return
            (match_bool_type return case_true case_false false)
            case_false
            (eq_match_bool_type_false return case_true case_false);
symbol bool_discr
  : sttfa.eps
    (sttfa.forall bool
     (λ (x : sttfa.etap (sttfa.p bool)),
        sttfa.forall bool
        (λ (y : sttfa.etap (sttfa.p bool)),
           sttfa.impl (logic.eq bool x y)
           (match_bool_type sttfa.bool
            (match_bool_type sttfa.bool
             (sttfa.forall sttfa.bool
              (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
             (sttfa.forall sttfa.bool
              (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
             y)
            (match_bool_type sttfa.bool
             (sttfa.forall sttfa.bool
              (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
             (sttfa.forall sttfa.bool
              (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
             y)
            x))))
  ≔ λ (x : sttfa.etap (sttfa.p bool)),
        λ (y : sttfa.etap (sttfa.p bool)),
          λ (Deq : sttfa.eps (logic.eq bool x y)),
            logic.eq_ind bool x
            (λ (x_13 : sttfa.etap (sttfa.p bool)),
               match_bool_type sttfa.bool
               (match_bool_type sttfa.bool
                (sttfa.forall sttfa.bool
                 (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
                (sttfa.forall sttfa.bool
                 (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
                x_13)
               (match_bool_type sttfa.bool
                (sttfa.forall sttfa.bool
                 (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
                (sttfa.forall sttfa.bool
                 (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
                x_13)
               x)
            (match_bool_prop
             (λ (__ : sttfa.etap (sttfa.p bool)),
                match_bool_type sttfa.bool
                (match_bool_type sttfa.bool
                 (sttfa.forall sttfa.bool
                  (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
                 (sttfa.forall sttfa.bool
                  (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
                 __)
                (match_bool_type sttfa.bool
                 (sttfa.forall sttfa.bool
                  (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
                 (sttfa.forall sttfa.bool
                  (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
                 __)
                __)
             (sym_eq_match_bool_type_true sttfa.bool
              (match_bool_type sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               true)
              (match_bool_type sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               true)
              (λ (x0 : sttfa.etap (sttfa.p sttfa.bool)), x0)
              (sym_eq_match_bool_type_true sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               (λ (x0 : sttfa.etap (sttfa.p sttfa.bool)), x0)
               (λ (P : sttfa.etap (sttfa.p sttfa.bool)),
                  λ (DH : sttfa.eps P), DH)))
             (sym_eq_match_bool_type_false sttfa.bool
              (match_bool_type sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               false)
              (match_bool_type sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               false)
              (λ (x0 : sttfa.etap (sttfa.p sttfa.bool)), x0)
              (sym_eq_match_bool_type_false sttfa.bool
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
               (sttfa.forall sttfa.bool
                (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
               (λ (x0 : sttfa.etap (sttfa.p sttfa.bool)), x0)
               (λ (P : sttfa.etap (sttfa.p sttfa.bool)),
                  λ (DH : sttfa.eps P), DH)))
             x)
            y Deq;
symbol not_eq_true_false
  : sttfa.eps (connectives.Not (logic.eq bool true false))
  ≔ connectives.nmk (logic.eq bool true false)
      (λ (Heq : sttfa.eps (logic.eq bool true false)),
         eq_match_bool_type_false sttfa.bool
         (sttfa.forall sttfa.bool
          (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
         (sttfa.forall sttfa.bool
          (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
         (λ (x : sttfa.etap (sttfa.p sttfa.bool)), x)
         (eq_match_bool_type_true sttfa.bool
          (match_bool_type sttfa.bool
           (sttfa.forall sttfa.bool
            (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
           (sttfa.forall sttfa.bool
            (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
           false)
          (match_bool_type sttfa.bool
           (sttfa.forall sttfa.bool
            (λ (P : sttfa.etap (sttfa.p sttfa.bool)), P))
           (sttfa.forall sttfa.bool
            (λ (P : sttfa.etap (sttfa.p sttfa.bool)), sttfa.impl P P))
           false)
          (λ (x : sttfa.etap (sttfa.p sttfa.bool)), x)
          (bool_discr true false Heq))
         connectives.False);
symbol notb : sttfa.etap (sttfa.p (sttfa.arrow bool bool))
  ≔ λ (b : sttfa.etap (sttfa.p bool)),
        match_bool_type bool false true b;
symbol andb
  : sttfa.etap
    (sttfa.p (sttfa.arrow bool (sttfa.arrow bool bool)))
  ≔ λ (b1 : sttfa.etap (sttfa.p bool)),
        λ (b2 : sttfa.etap (sttfa.p bool)),
          match_bool_type bool b2 false b1;
symbol andb_true_l
  : sttfa.eps
    (sttfa.forall bool
     (λ (b1 : sttfa.etap (sttfa.p bool)),
        sttfa.forall bool
        (λ (b2 : sttfa.etap (sttfa.p bool)),
           sttfa.impl (logic.eq bool (andb b1 b2) true)
           (logic.eq bool b1 true))))
  ≔ λ (b1 : sttfa.etap (sttfa.p bool)),
        match_bool_prop
        (λ (__ : sttfa.etap (sttfa.p bool)),
           sttfa.forall bool
           (λ (b2 : sttfa.etap (sttfa.p bool)),
              sttfa.impl (logic.eq bool (andb __ b2) true)
              (logic.eq bool __ true)))
        (λ (b2 : sttfa.etap (sttfa.p bool)),
           sym_eq_match_bool_type_true bool b2 false
           (λ (x : sttfa.etap (sttfa.p bool)),
              sttfa.impl (logic.eq bool x true)
              (logic.eq bool true true))
           (λ (auto : sttfa.eps (logic.eq bool b2 true)),
              logic.rewrite_l bool b2
              (λ (__ : sttfa.etap (sttfa.p bool)),
                 logic.eq bool __ true)
              (logic.rewrite_l bool b2
               (λ (__ : sttfa.etap (sttfa.p bool)),
                  logic.eq bool b2 __)
               (logic.refl bool b2) true auto)
              true auto))
        (λ (_b2 : sttfa.etap (sttfa.p bool)),
           sym_eq_match_bool_type_false bool _b2 false
           (λ (x : sttfa.etap (sttfa.p bool)),
              sttfa.impl (logic.eq bool x true)
              (logic.eq bool false true))
           (λ (auto : sttfa.eps (logic.eq bool false true)),
              logic.rewrite_r bool true
              (λ (__ : sttfa.etap (sttfa.p bool)),
                 logic.eq bool __ true)
              (logic.refl bool true) false auto))
        b1;
symbol andb_true_r
  : sttfa.eps
    (sttfa.forall bool
     (λ (b1 : sttfa.etap (sttfa.p bool)),
        sttfa.forall bool
        (λ (b2 : sttfa.etap (sttfa.p bool)),
           sttfa.impl (logic.eq bool (andb b1 b2) true)
           (logic.eq bool b2 true))))
  ≔ λ (b1 : sttfa.etap (sttfa.p bool)),
        λ (b2 : sttfa.etap (sttfa.p bool)),
          match_bool_prop
          (λ (__ : sttfa.etap (sttfa.p bool)),
             sttfa.impl (logic.eq bool (andb __ b2) true)
             (logic.eq bool b2 true))
          (sym_eq_match_bool_type_true bool b2 false
           (λ (x : sttfa.etap (sttfa.p bool)),
              sttfa.impl (logic.eq bool x true)
              (logic.eq bool b2 true))
           (λ (auto : sttfa.eps (logic.eq bool b2 true)),
              logic.rewrite_l bool b2
              (λ (__ : sttfa.etap (sttfa.p bool)),
                 logic.eq bool b2 __)
              (logic.refl bool b2) true auto))
          (sym_eq_match_bool_type_false bool b2 false
           (λ (x : sttfa.etap (sttfa.p bool)),
              sttfa.impl (logic.eq bool x true)
              (logic.eq bool b2 true))
           (match_bool_prop
            (λ (__ : sttfa.etap (sttfa.p bool)),
               sttfa.impl (logic.eq bool false true)
               (logic.eq bool __ true))
            (λ (auto : sttfa.eps (logic.eq bool false true)),
               logic.refl bool true)
            (λ (auto : sttfa.eps (logic.eq bool false true)),
               logic.rewrite_r bool true
               (λ (__ : sttfa.etap (sttfa.p bool)),
                  logic.eq bool __ true)
               (logic.refl bool true) false auto)
            b2))
          b1;
symbol true_or_false
  : sttfa.eps
    (sttfa.forall bool
     (λ (b : sttfa.etap (sttfa.p bool)),
        connectives.Or (logic.eq bool b true)
        (logic.eq bool b false)))
  ≔ λ (b : sttfa.etap (sttfa.p bool)),
        match_bool_prop
        (λ (__ : sttfa.etap (sttfa.p bool)),
           connectives.Or (logic.eq bool __ true)
           (logic.eq bool __ false))
        (connectives.or_introl (logic.eq bool true true)
         (logic.eq bool true false)
         (logic.refl bool true))
        (relations.RC_reflexive bool
         (λ (__ : sttfa.etap (sttfa.p bool)),
            λ (_0 : sttfa.etap (sttfa.p bool)),
              logic.eq bool false true)
         false)
        b;
