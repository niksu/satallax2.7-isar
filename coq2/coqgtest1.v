Require Export stt4.

Parameter f:set>set. (* 1 1 1 *)
Parameter g:set>set. (* 1 1 1 *)

Axiom a:forall (x:set), f x = g x.

Conjecture c0 : f = f.

Conjecture c1 : f = g.

Conjecture c2 : g = f.