(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 - September 2011 (-nois version) ***)

(** * Simple Types **)

Parameter setT : Type. (** set is the base type of sets. **)

(** Simple types are constructed from setT and Prop using simple function types. **)

Inductive STypeP : Type -> Prop :=
  setP : STypeP setT
| PropP : STypeP Prop
| SarP : forall A B:Type, STypeP A -> STypeP B -> STypeP (A -> B).

Record SType : Type := mk_SType {
 Scarrier :> Type;                           (*** Coercion ***)
 Sinh : STypeP Scarrier               (*** inhabitation assumption ***)
}.

Definition prop : SType := mk_SType Prop PropP.
Definition set : SType := mk_SType setT setP.

(** Simple types are closed under simple function types. We use A>B as the notation for function types as simple types. *)

Definition Sar (A B:SType) : SType := mk_SType (A -> B) (SarP A B (Sinh A) (Sinh B)).

Notation "A > B" := (Sar A B) (at level 70, right associativity).

(*** nat and Snfun (simple type of nary functions) ***)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.

Fixpoint Snfun (A:SType) n (B:SType) : SType :=
 match n with
  | O => B
  | S n => Sar A (Snfun A n B)
 end.

Notation "A ^ n --> B" := (Snfun A n B) (at level 20).

Fixpoint Snfun_K (A : SType) {B : SType} (b : B) (n : nat) : A ^ n --> B :=
match n with
| O => b
| S n => fun _ => Snfun_K A b n
end.

Fixpoint Snfun_comp {A B C : SType} (f : B -> C) (n : nat) : (A ^ n --> B) -> A ^ n --> C :=
match n with
| O => fun b => f b
| S n => fun g => fun x:A => Snfun_comp f n (g x)
end.

Fixpoint Snfun_comp2 {A B C : SType} (f : B -> B -> C) (n : nat) : (A ^ n --> B) -> (A ^ n --> B) -> A ^ n --> C :=
match n with
| O => fun b b' => f b b'
| S n => fun g h => fun x:A => Snfun_comp2 f n (g x) (h x)
end.

Fixpoint Snfun_unfoldR {A B : SType} (n : nat) : (A ^ (S n) --> B) -> A ^ n --> (A > B) :=
match n with
| O => fun g => g
| S n => fun g x => Snfun_unfoldR n (g x)
end.

(*** length indexed lists (lists carrying length) ***)

Inductive ilist (A : Type) : nat -> Type :=
| ilist_nl : ilist A O
| ilist_cns : forall n, A -> ilist A n -> ilist A (S n).

Implicit Arguments ilist_nl [A].
Implicit Arguments ilist_cns [A n].

Notation "s :: t" := (ilist_cns s t) (at level 60, right associativity).

(*** Idea for ilist_hd and tl from Chlipala http://adam.chlipala.net/cpdt/html/MoreDep.html ***)
Definition ilist_hd {A : SType} {n : nat} (al : ilist A (S n)) : A :=
match al in (ilist _ n') return match n' with O => (forall p:prop, p -> p) | S n'' => A end with
| ilist_nl => (fun p:prop => fun H:p => H)
| ilist_cns n' a ar => a
end.

Definition ilist_tl {A : SType} {n : nat} (al : ilist A (S n)) : ilist A n :=
match al in (ilist _ n') return match n' with O => (forall p:prop, p -> p) | S n'' => ilist A n'' end with
| ilist_nl => (fun p:prop => fun H:p => H)
| ilist_cns n' a ar => ar
end.

Fixpoint Snfun_ilist_Ap {A B : SType} {n : nat} : forall (f : A ^ n --> B) (al : ilist A n), B :=
match n with
| O => fun b _ => b
| S n => fun f al => Snfun_ilist_Ap (f (ilist_hd al)) (ilist_tl al)
end.

Fixpoint Snfun_ilist_Curry {A B : SType} {n : nat} : (ilist A n -> B) -> A ^ n --> B :=
match n with
| O => fun f => f ilist_nl
| S n => fun f a => Snfun_ilist_Curry (fun al => f (ilist_cns a al))
end.

Lemma Snfun_ilist_Curry_Ap {A B:SType} {n:nat} (f : ilist A n -> B) (al : ilist A n) :
forall q:B -> Prop, q (Snfun_ilist_Ap (Snfun_ilist_Curry f) al) -> q (f al).
Admitted.
 
Lemma Snfun_ilist_Ap_K {A B : SType} (b : B) (n : nat) : forall (al : ilist A n), forall q:B>prop, q (Snfun_ilist_Ap (Snfun_K A b n) al) -> q b.
induction n.
intros al q H. exact H.
intros al. simpl. apply IHn.
Defined.

Lemma Snfun_ilist_Ap_comp {A B C : SType} (f : B -> C) (n : nat) (g : A ^ n --> B) (al:ilist A n) :
 forall q:C>prop, q (Snfun_ilist_Ap (Snfun_comp f n g) al) -> q (f (Snfun_ilist_Ap g al)).
revert g.
induction n.
intros g q H. exact H.
intros g. simpl. apply (IHn (ilist_tl al) (g (ilist_hd al))).
Defined.

Lemma Snfun_ilist_Ap_comp2 {A B C : SType} (f : B -> B -> C) (n : nat) : forall (g h : A ^ n --> B),
 forall al:ilist A n, forall q:C>prop, q (Snfun_ilist_Ap (Snfun_comp2 f n g h) al) -> q (f (Snfun_ilist_Ap g al) (Snfun_ilist_Ap h al)).
induction n.
intros g h al q H. exact H.
intros g h al. simpl. apply IHn.
Defined.

(*** Fin ***)

Inductive Fin : nat -> Type :=
| Fin_O : forall {n}, Fin (S n)
| Fin_S : forall {n}, Fin n -> Fin (S n).

Fixpoint Fin_nat {n:nat} (k:Fin n) : nat :=
match k with
| Fin_O n' => O
| Fin_S n' k' => S (Fin_nat k')
end.

Definition Fin0E (k : Fin O) (A:Type) : A :=
match k in Fin n return match n with O => A | S _ => forall p:prop, p -> p end with
| Fin_O _ => (fun p:prop => fun H:p => H)
| Fin_S _ _ => (fun p:prop => fun H:p => H)
end.

Lemma Fin_Inv' (n : nat) (k : Fin n) :
 match n as z return Fin z -> Prop with
 | O => fun k => forall p:Prop, p
 | S n' => fun k => (forall p:Prop, (forall k', (forall q:Fin (S n') -> Prop, q k -> q (Fin_S k')) -> p) -> ((forall q:Fin (S n') -> Prop, q k -> q Fin_O) -> p) -> p) end k.
destruct k as [n|n k].
intros p _ H. apply H. intros q H'. exact H'.
intros p H _. apply (H k). intros q H'. exact H'.
Defined.

Lemma Fin_Inv (n : nat) (k : Fin (S n)) :
 forall p:Prop, (forall k':Fin n, (forall q:Fin (S n) -> Prop, q k -> q (Fin_S k')) -> p)
             -> ((forall q:Fin (S n) -> Prop, q k -> q Fin_O) -> p)
             -> p.
exact (Fin_Inv' (S n) k).
Defined.

Lemma Fin_Inv_T' (n : nat) (k : Fin n) :
 match n as z return Fin z -> Type with
 | O => fun k => forall p:Type, p
 | S n' => fun k => (forall p:Type, (forall k', (forall q:Fin (S n') -> Type, q k -> q (Fin_S k')) -> p) -> ((forall q:Fin (S n') -> Type, q k -> q Fin_O) -> p) -> p) end k.
destruct k as [n|n k].
intros p _ H. apply H. intros q H'. exact H'.
intros p H _. apply (H k). intros q H'. exact H'.
Defined.

Lemma Fin_Inv_T (n : nat) (k : Fin (S n)) :
 forall p:Type, (forall k':Fin n, (forall q:Fin (S n) -> Type, q k -> q (Fin_S k')) -> p)
             -> ((forall q:Fin (S n) -> Type, q k -> q Fin_O) -> p)
             -> p.
exact (Fin_Inv_T' (S n) k).
Defined.

(*** Projections ***)
Fixpoint Snfun_P {A : SType} {n : nat} (k : Fin n) : A ^ n --> A :=
match k in Fin n' return A ^ n' --> A with
| Fin_O n' => fun a => Snfun_K A a n'
| Fin_S n' k' => fun _ => Snfun_P k'
end.

Fixpoint ilist_P {A : SType} {n : nat} (k : Fin n) : ilist A n -> A :=
match n as z return Fin z -> ilist A z -> A with
| O => fun k xn => Fin_Inv_T' O k A
| S n' =>  fun k xn => Fin_Inv_T n' k A (fun k' _ => ilist_P k' (ilist_tl xn)) (fun _ => ilist_hd xn)
end k.

(***
Fixpoint kth {A : Type} {n : nat} : forall (xk : X n) (a : seq A n), A :=
match n with
| O => fun xk a => match (Fin0E xk) with end
| S n' => fun xk a =>
  match (proj1_sig xk) as k' return lt k' (S n') -> A with
  | O => fun _ => hd a
  | S k' => fun u => kth (x n' k' u) (tl a)
  end
  (proj2_sig xk)
end.
***)

