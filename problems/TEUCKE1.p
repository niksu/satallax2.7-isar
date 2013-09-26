% Domain   : Syntactic
% Problem  : Teucke's Example
% Refs     : [Bro11] Brown E. (2011), Email to Geoff Sutcliffe
% Source   : [Bro11]
% Names    : TEUCKE1 [Bro11]
% Status   : Unsatisfiable
% Comments : THF0 syntax
%          : Andreas Teucke created this first-order example to demonstrate
%            that sometimes analytic cut sneaks into Satallax proofs.
thf(p,type,(p : ($i > $o))).
thf(s,type,(s : $i)).
thf(t,type,(t : $i)).
thf(u,type,(u : $i)).
thf(pst,axiom,((p @ s) | (p @ t))).
thf(puv,axiom,((~ (p @ u)) | (~ (p @ t)))).
thf(st,axiom,(s = t)).
thf(tu,axiom,(t = u)).
