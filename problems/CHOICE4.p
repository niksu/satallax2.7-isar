% Domain   : Syntactic
% Problem  : Skolemization using the choice operator @+
% English  : For every total relation r on individuals,
%            the choice operator @+ can be used to define a corresponding function.
% Refs     : [Bro11] Brown (2011), Email to Geoff Sutcliffe
% Source   : [Bro11]
% Names    : CHOICE4 [Bro11]
% Status   : Theorem
% Comments : THF syntax (not THF0 syntax due to use of @+).
%          : This is similar to SYN996^1 and SYO508^1, but with the solution given (using @+).
thf(r,type,(r : ($i > ($i > $o)))).
thf(rtotal,axiom,! [X : $i] : (? [Y : $i] : (r @ X @ Y))).
thf(skolem,conjecture,! [X : $i] : (r @ X @ (@+ [Y : $i] : (r @ X @ Y)))).
