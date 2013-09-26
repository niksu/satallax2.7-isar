(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 - September 2011 (-nois version) ***)

(*** Moving just what I need to here from the Coq library, redefining connectives to avoid inductive props. ***)

Require Export stt0.

(** * Definitions of logical constants. *)

(** ** Russell-Prawitz Definitions of false, true, negation, conjunction, disjunction and existential quantification. ***)

Definition False : prop := forall P:prop, P.

Lemma FalseE : forall P : prop, False -> P.
exact (fun P H => H P).
Qed.

Lemma imp_false_dup : forall (X:prop), (X -> X -> False) -> X -> False.
exact (fun (X : prop) (H : X -> X -> False) (x : X) => H x x).
Qed.

Definition True : prop := forall P:prop, P -> P.

Theorem TrueI : True.
exact (fun P p => p).
Qed.

Definition not : prop>prop := fun A:prop => A -> False.

Notation "~ x" := (not x) (at level 75, right associativity).

Theorem notI : forall A:prop, (A -> False) -> not A.
exact (fun A H a => H a).
Qed.

Theorem notE : forall A:prop, not A -> A -> False.
exact (fun A H a => H a).
Qed.

Definition and : prop>prop>prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.

Notation "A /\ B" := (and A B) (at level 80).

Theorem andI : forall (A B : prop), A -> B -> and A B.
exact (fun A B a b P H => H a b).
Qed.

Theorem andEL : forall (A B : prop), and A B -> A.
exact (fun A B H => H A (fun a b => a)).
Qed.

Theorem andER : forall (A B : prop), and A B -> B.
exact (fun A B H => H B (fun a b => b)).
Qed.

Definition or : prop>prop>prop := fun (A B : prop) => forall P:prop, (A -> P) -> (B -> P) -> P.

Notation "A \/ B" := (or A B) (at level 85).

Theorem orIL : forall (A B : prop), A -> or A B.
exact (fun A B a P H1 H2 => H1 a).
Qed.

Theorem orIR : forall (A B : prop), B -> or A B.
exact (fun A B b P H1 H2 => H2 b).
Qed.

Theorem orE : forall (A B C:prop), (A -> C) -> (B -> C) -> or A B -> C.
exact (fun A B C H1 H2 H3 => H3 C H1 H2).
Qed.

Definition iff : prop>prop>prop := fun (A B:prop) => (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) (at level 95).

Theorem iffEL : forall A B:prop, iff A B -> A -> B.
exact (fun A B => andEL (A -> B) (B -> A)).
Qed.

Theorem iffER : forall A B:prop, iff A B -> B -> A.
exact (fun A B => andER (A -> B) (B -> A)).
Qed.

Theorem iffI : forall A B:prop, (A -> B) -> (B -> A) -> iff A B.
exact (fun A B => andI (A -> B) (B -> A)).
Qed.

Definition ex (A : SType) : (A>prop)>prop := fun P:A>prop => forall Q:prop, (forall x, P x -> Q) -> Q.

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity).
Notation "'exists' x : A , p" := (ex _ (fun x:A => p))
  (at level 200, x ident, right associativity,
    format "'[' 'exists'  '/  ' x : A ,  '/  ' p ']'").

Definition eq (A : SType) : A>A>prop := fun (x y : A) => forall Q:A > prop, Q x -> Q y.

Notation "x = y" := (eq _ x y) (at level 70).
Notation "x <> y" := (~ x = y) (at level 70).

Theorem exE (A:SType) : forall P:A>prop, forall Q:prop, (forall x:A, P x -> Q) -> ex A P -> Q.
exact (fun P Q H1 H2 => H2 Q H1).
Qed.

Theorem exI A : forall P:A>prop, forall x:A, P x -> ex A P.
exact (fun P x H1 Q H2 => H2 x H1).
Qed.

Theorem eqE (A : SType) : forall x y:A, forall q:A>prop, q x -> eq A x y -> q y.
exact (fun x y q H1 H2 => H2 q H1).
Qed.

Theorem eqE' (A : SType) : forall x:A, forall q:A>prop, q x -> forall y:A, eq A x y -> q y.
exact (fun x q H1 y H2 => H2 q H1).
Qed.

Theorem eqI (A : SType) : forall x:A, eq A x x.
exact (fun x q H => H).
Qed.

Definition exu (A:SType) : (A>prop)>prop := fun P:A>prop => and (ex A P) (forall x y:A, P x -> P y -> eq A x y).

Notation "'exists!' x , p" := (exu _ (fun x => p))
  (at level 200, x ident, right associativity).
Notation "'exists!' x : A , p" := (exu _ (fun x:A => p))
  (at level 200, x ident, right associativity,
    format "'[' 'exists!'  '/  ' x : A ,  '/  ' p ']'").

Theorem exuE1 (A:SType) : forall P:A>prop, exu A P -> ex A P.
exact (fun P => andEL (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuE2 (A : SType) : forall P:A>prop, exu A P -> forall x y:A, P x -> P y -> eq A x y.
exact (fun P => andER (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuI (A : SType) : forall P:A>prop, ex A P -> (forall x y:A, P x -> P y -> eq A x y) -> exu A P.
exact (fun P => andI (ex A P) (forall x y:A, P x -> P y -> eq A x y)).
Qed.

Theorem exuEa (A : SType) : forall P:A>prop, exu A P -> ex A (fun x:A => and (P x) (forall y:A, P y -> eq A y x)).
exact (fun P H1 => H1 (ex A (fun x : A => and (P x) (forall y : A, P y -> eq A y x))) (fun H2 H3 => H2 (ex A (fun x : A => and (P x) (forall y : A, P y -> eq A y x))) (fun x H4 => exI A (fun z => and (P z) (forall y, P y -> eq A y z)) x (andI (P x) (forall y:A, P y -> eq A y x) H4 (fun y H5 => H3 y x H5 H4))))).
Qed.

Theorem eq_sym (A : SType) : forall x y:A, eq A x y -> eq A y x.
exact (fun x y H => H (fun y => eq A y x) (eqI A x)).
Qed.

Theorem eq_trans (A : SType) : forall x y z:A, eq A x y -> eq A y z -> eq A x z.
exact (fun x y z H1 H2 => H2 (fun z => eq A x z) H1).
Qed.

Theorem eqEr (A : SType) : forall x y:A, forall q:A>prop, q x -> eq A y x -> q y.
exact (fun x y q H1 H2 => eq_sym A y x H2 q H1).
Qed.

Theorem eqEr' (A : SType) : forall x:A, forall q:A>prop, q x -> forall y:A, eq A y x -> q y.
exact (fun x q H1 y H2 => eq_sym A y x H2 q H1).
Qed.

Theorem eq_symtrans1 (A : SType) : forall x y z:A, eq A x y -> eq A z y -> eq A x z.
exact (fun x y z H1 H2 => eq_trans A x y z H1 (eq_sym A z y H2)).
Qed.

Theorem eq_symtrans2 (A : SType) : forall x y z:A, eq A y x -> eq A y z -> eq A x z.
exact (fun x y z H1 H2 => eq_trans A x y z (eq_sym A y x H1) H2).
Qed.

Theorem exuIa (A : SType) : forall P:A>prop, ex A (fun x:A => and (P x) (forall y:A, P y -> eq A y x)) -> exu A P.
exact (fun P H1 => H1 (exu A P) (fun x H2 => H2 (exu A P) (fun H3 H4 => exuI A P (exI A P x H3) (fun z y H5 H6 => eq_symtrans1 A z x y (H4 z H5) (H4 y H6))))).
Qed.
