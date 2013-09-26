% Domain   : Syntactic
% Problem  : There can be 4 distinct choice operators on type $o
% Refs     : [Bro11] Brown (2011), Email to Geoff Sutcliffe
% Source   : [Bro11]
% Names    : CHOICE4 [Bro11]
% Status   : Satisfiable
% Comments : THF0 syntax
thf(eps1,type,(eps1 : (($o > $o) > $o))).
thf(choiceax1,axiom,(! [P : ($o > $o)] : ((? [X : $o] : (P @ X)) => (P @ (eps1 @ P))))).
thf(eps2,type,(eps2 : (($o > $o) > $o))).
thf(choiceax2,axiom,(! [P : ($o > $o)] : ((? [X : $o] : (P @ X)) => (P @ (eps2 @ P))))).
thf(eps3,type,(eps3 : (($o > $o) > $o))).
thf(choiceax3,axiom,(! [P : ($o > $o)] : ((? [X : $o] : (P @ X)) => (P @ (eps3 @ P))))).
thf(eps4,type,(eps4 : (($o > $o) > $o))).
thf(choiceax4,axiom,(! [P : ($o > $o)] : ((? [X : $o] : (P @ X)) => (P @ (eps4 @ P))))).
thf(choiceax12,axiom,eps1 != eps2).
thf(choiceax13,axiom,eps1 != eps3).
thf(choiceax14,axiom,eps1 != eps4).
thf(choiceax23,axiom,eps2 != eps3).
thf(choiceax24,axiom,eps2 != eps4).
thf(choiceax34,axiom,eps3 != eps4).

