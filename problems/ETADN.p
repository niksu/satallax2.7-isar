% Domain   : Syntactic
% Problem  : The eta double negation problem
% Refs     : [Bro11] Brown E. (2011), Email to Geoff Sutcliffe
% Source   : [Bro11]
% Names    : ETADN [Bro11]
% Status   : Theorem
% Comments : THF0 syntax
%          : This higher-order problem is immediately solved if one removes double negations embedded inside terms
%            and eta-normalizes.  Otherwise, search may be required.
thf(p,type,(p : (($o > $o) > ($o > $o) > $o))).
thf(f,type,(f : ($o > $o))).
thf(g,type,(g : ($o > $o))).
thf(pfg,axiom,((p @ ( ^ [X: $o] : (f @ (~ (~ (X)))))) @ g)).
thf(pfgc,conjecture,((p @ f) @ ( ^ [X: $o] : (g @ (~ (~ (X))))))).

