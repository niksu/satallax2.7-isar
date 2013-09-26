(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 - September 2011 (-nois version) ***)

(*** Moving just what I need to here from the Coq library, redefining connectives to avoid inductive props. ***)

Require Export stt1.

(** * Axioms of simple type theory *)

(** We include an epsilon operator (Eps) as a form of the axiom of choice. *)

Axiom Eps : forall (A : SType), ((A>prop)>A). (* 1 1 *)

Axiom EpsR : forall (A : SType), forall P:A>prop, forall x:A, P x -> P (Eps A P). (* 1 2 *)

(** Propositional extensionality: Equivalent propositions are equal. **)

Axiom prop_ext : forall A B:prop, (A -> B) -> (B -> A) -> A = B. (* 1 0 0 *)

(** Functional extensionality: Equivalent functions are equal. **)

Axiom func_ext : forall (A B:SType) (f g : A > B), (forall x, f x = g x) -> f = g. (* 2 *)
