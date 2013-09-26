(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 - Oct 2011 ***)

Require Export stt2.

Theorem Inh (A:SType) : forall (P:prop), (forall x:A, P) -> P.
exact (fun P u => u (Eps A (fun _ => False))).
Qed.

(*** Diaconescu proof of excluded middle from choice. ***)
Lemma classic : forall P:prop, P \/ ~ P.
exact (fun P =>
EpsR prop (fun x : prop => x \/ P) True (orIL True P TrueI) 
  (P \/ ~ P)
  (fun H1 =>
   EpsR prop (fun x : prop => ~ x \/ P) False
     (orIL (~ False) P (fun H : False => H)) (P \/ ~ P)
     (fun H2 =>
      orIR P (~ P)
        (fun H3 : P =>
         H2 (func_ext prop prop (fun x : prop => x \/ P) (fun x : prop => ~ x \/ P)
             (fun x : prop =>
              prop_ext (x \/ P) (~ x \/ P)
                   (fun H4 : x \/ P => orIR (~ x) P H3)
                   (fun H4 : ~ x \/ P => orIR x P H3)) (fun s : prop > prop => Eps prop s) H1)))
     (fun H2 : P => orIL P (~ P) H2)) (fun H1 : P => orIL P (~ P) H1)).
Qed.

Lemma NNPP : forall p:prop, ~ ~ p -> p.
exact (fun (p : prop) (H1 : ~ ~ p) =>
classic p p (fun H2 : p => H2) (fun H2 : ~ p => H1 H2 p)).
Qed.

Theorem prop_deg : forall X:prop, X = True \/ X = False.
exact (fun X : prop =>
classic X (X = True \/ X = False)
  (fun H1 : X =>
   orIL (X = True) (X = False)
     (prop_ext X True (fun _ : X => TrueI) (fun _ : True => H1)))
  (fun H1 : ~ X =>
   orIR (X = True) (X = False) (prop_ext X False H1 (fun H2 : False => H2 X)))).
Qed.

(*** Logical Identities ***)
(*** Used to delete double negations ***)
Theorem eq_neg_neg_id : eq (prop>prop) (fun x:prop => ~~x) (fun x:prop => x).
exact (func_ext prop prop (fun x : prop => ~ ~ x) (fun x : prop => x)
  (fun x : prop =>
   prop_ext (~ ~ x) x
   (NNPP x) (fun (u : x) (v : ~ x) => v u))).
Qed.

Theorem eq_true : True = ~False.
exact (prop_ext True (~ False)
  (fun (_ : True) (H : False) => H)
  (fun _ : ~ False => TrueI)).
Qed.

Theorem eq_and_nor : and = (fun (x y:prop) => ~(~x \/ ~y)).
exact
(func_ext prop (prop > prop) and (fun x y : prop => ~ (~ x \/ ~ y))
  (fun x : prop =>
   func_ext prop prop (and x) (fun y : prop => ~ (~ x \/ ~ y))
     (fun y : prop =>
      prop_ext (x /\ y) (~ (~ x \/ ~ y))
           (fun (H1 : x /\ y) (H2 : ~ x \/ ~ y) =>
            H1 False
              (fun (H3 : x) (H4 : y) =>
               H2 False (fun H5 : ~ x => H5 H3) (fun H5 : ~ y => H5 H4)))
           (fun H1 : ~ (~ x \/ ~ y) =>
            classic x (x /\ y)
              (fun v : x =>
               classic y (x /\ y) (fun w : y => andI x y v w)
                 (fun w : ~ y => H1 (orIR (~ x) (~ y) w) (x /\ y)))
              (fun v : ~ x => H1 (orIL (~ x) (~ y) v) (x /\ y)))))).
Qed.

Theorem eq_or_nand : or = (fun (x y:prop) => ~(~x /\ ~y)).
exact
(func_ext prop (prop > prop) or (fun x y : prop => ~ (~ x /\ ~ y))
  (fun x : prop =>
   func_ext prop prop (or x) (fun y : prop => ~ (~ x /\ ~ y))
     (fun y : prop =>
      prop_ext (x \/ y) (~ (~ x /\ ~ y))
           (fun (H1 : x \/ y) (H2 : ~ x /\ ~ y) =>
            H2 False (fun (H3 : ~ x) (H4 : ~ y) => H1 False H3 H4))
           (fun H1 : ~ (~ x /\ ~ y) =>
            classic x (x \/ y) (fun H2 : x => orIL x y H2)
              (fun H2 : ~ x =>
               classic y (x \/ y) (fun H3 : y => orIR x y H3)
                 (fun H3 : ~ y => H1 (andI (~ x) (~ y) H2 H3) (x \/ y))))))).
Qed.

Theorem eq_or_imp : or = (fun (x y:prop) => ~ x -> y).
exact
(func_ext prop (prop > prop) or (fun x y : prop => ~ x -> y)
  (fun x : prop =>
   func_ext prop prop (or x) (fun y : prop => ~ x -> y)
     (fun y : prop =>
      prop_ext (x \/ y) (~ x -> y)
           (fun (H1 : x \/ y) (H2 : ~ x) =>
            H1 y (fun H3 : x => H2 H3 y) (fun H3 : y => H3))
           (fun H1 : ~ x -> y =>
            classic x (x \/ y) (fun H3 : x => orIL x y H3)
              (fun H2 : ~ x => orIR x y (H1 H2)))))).
Qed.

Theorem eq_and_imp : and = (fun (x y:prop) => ~ (x -> ~ y)).
exact
(func_ext prop (prop > prop) and (fun x y : prop => ~ (x -> ~ y))
  (fun x : prop =>
   func_ext prop prop (and x) (fun y : prop => ~ (x -> ~ y))
     (fun y : prop =>
      prop_ext (x /\ y) (~ (x -> ~ y))
           (fun (H1 : x /\ y) (H2 : x -> ~ y) =>
            H1 False (fun (H3 : x) (H4 : y) => H2 H3 H4))
           (fun H1 : ~ (x -> ~ y) =>
            classic x (x /\ y)
              (fun H2 : x =>
               classic y (x /\ y) (fun H3 : y => andI x y H2 H3)
                 (fun H3 : ~ y => H1 (fun _ : x => H3) (x /\ y)))
              (fun H2 : ~ x => H1 (fun H3 : x => H2 H3 (~ y)) (x /\ y)))))).
Qed.

Theorem eq_imp_or : eq (prop>prop>prop) (fun (x y:prop) => (x -> y)) (fun (x y:prop) => (~x \/ y)).
exact (func_ext prop (prop > prop) (fun x y : prop => x -> y) (fun x y : prop => ~ x \/ y)
  (fun x : prop =>
   func_ext prop prop (fun y : prop => x -> y) (fun y : prop => ~ x \/ y)
     (fun y : prop =>
      prop_ext (x -> y) (~ x \/ y)
           (fun H1 : x -> y =>
            classic x (~ x \/ y) (fun H2 : x => orIR (~ x) y (H1 H2))
              (fun H2 : ~ x => orIL (~ x) y H2))
           (fun H1 : ~ x \/ y =>
            H1 (x -> y) (fun (H2 : ~ x) (H3 : x) => H2 H3 y)
              (fun (H2 : y) (_ : x) => H2))))).
Qed.

Theorem eq_iff : eq (prop>prop>prop) (fun s t => s <-> t) (fun s t => s = t).
exact
(func_ext prop (prop > prop) (fun s t : prop => s <-> t) (fun s t : prop => s = t)
  (fun x : prop =>
   func_ext prop prop (fun t : prop => x <-> t) (fun t : prop => x = t)
     (fun y : prop =>
      prop_ext (x <-> y) (x = y)
           (fun H1 : x <-> y => prop_ext x y (iffEL x y H1) (iffER x y H1))
           (fun H1 : x = y =>
            H1 (fun y0 : prop => x <-> y0)
              (andI (x -> x) (x -> x) (fun H2 : x => H2) (fun H2 : x => H2)))))).
Qed.

Theorem eq_sym_eq (A : SType) : eq (A>A>prop) (fun (s t:A) => s = t) (fun (s t:A) => t = s).
exact (func_ext A (A > prop) (fun s t : A => s = t) (fun s t : A => t = s)
  (fun x : A =>
   func_ext A prop (fun t : A => x = t) (fun t : A => t = x)
     (fun y : A => prop_ext (x = y) (y = x) (eq_sym A x y) (eq_sym A y x)))).
Qed.

Theorem eq_forall_nexists (A : SType) : eq ((A>prop)>prop) (fun (f:A > prop) => forall x, f x) (fun (f:A > prop) => ~exists x, ~f x).
exact (func_ext (A > prop) prop (fun f : A > prop => forall x : A, f x)
  (fun f : A > prop => ~ (exists x:A, ~ f x))
  (fun f : A > prop =>
   prop_ext (forall x : A, f x) (~ (exists x:A, ~ f x))
     (fun (u : forall x : A, f x) (v : exists x:A, ~ f x) =>
      v False (fun (x : A) (w : ~ f x) => w (u x)))
     (fun (u : ~ (exists x:A, ~ f x)) (x : A) =>
      NNPP (f x) (fun v : ~ f x => u (exI A (fun z : A => ~ f z) x v))))).
Qed.

Theorem eq_exists_nforall (A : SType) : eq ((A>prop)>prop) (fun (f:A > prop) => exists x, f x) (fun (f:A > prop) => ~forall x, ~f x).
exact (func_ext (A > prop) prop (fun f : A > prop => exists x:A, f x)
  (fun f : A > prop => ~ (forall x : A, ~ f x))
  (fun f : A > prop =>
   prop_ext (exists x:A, f x) (~ (forall x : A, ~ f x))
     (fun (u : exists x:A, f x) (v : forall x : A, ~ f x) =>
      u False (fun (x : A) (w : f x) => v x w))
     (fun u : ~ (forall x : A, ~ f x) =>
      NNPP (exists x:A, f x)
        (fun v : ~ (exists x:A, f x) =>
         u (fun (x : A) (w : f x) => v (exI A f x w)))))).
Qed.

Theorem eq_leib1 (A : SType) : eq (A>A>prop) (fun (s t:A) => forall (p: A > prop), p s -> p t) (fun (s t: A ) => s = t).
exact (func_ext A (A > prop) (fun s t : A => forall p : A > prop, p s -> p t)
  (fun s t : A => s = t)
  (fun x : A =>
   func_ext A prop (fun t : A => forall p : A > prop, p x -> p t)
     (fun t : A => x = t)
     (fun y : A =>
      prop_ext (forall p : A > prop, p x -> p y) (x = y)
        (fun H : forall p : A > prop, p x -> p y =>
         H (fun z : A => x = z) (eqI A x))
        (fun (xy : x = y) (p : A > prop) (px : p x) =>
         xy (fun z : A => p z) px)))).
Qed.

Theorem eq_leib2 (A : SType) : eq (A>A>prop) (fun (s t:A) => forall (p: A > prop), ~ p s -> ~ p t) (fun (s t: A ) => s = t).
exact (func_ext A (A > prop) (fun s t : A => forall p : A > prop, ~ p s -> ~ p t)
  (fun s t : A => s = t)
  (fun x : A =>
   func_ext A prop (fun t : A => forall p : A > prop, ~ p x -> ~ p t)
     (fun t : A => x = t)
     (fun y : A =>
      prop_ext (forall p : A > prop, ~ p x -> ~ p y) (x = y)
        (fun H : forall p : A > prop, ~ p x -> ~ p y =>
         NNPP (x = y)
           (H (fun z : A => x <> z) (fun H1 : x <> x => H1 (eqI A x))))
        (fun (xy : x = y) (p : A > prop) (px : ~ p x) =>
         xy (fun z : A => ~ p z) px)))).
Qed. 

Theorem eq_leib3 (A : SType) : eq (A>A>prop) (fun (s t:A) => forall (r: A > A > prop), (forall x, r x x) -> r s t) (fun (s t: A ) => s = t).
exact (func_ext A (A > prop)
  (fun s t : A => forall r : A > A > prop, (forall x : A, r x x) -> r s t)
  (fun s t : A => s = t)
  (fun x : A =>
   func_ext A prop
     (fun t : A => forall r : A > A > prop, (forall x : A, r x x) -> r x t)
     (fun t : A => x = t)
     (fun y : A =>
      prop_ext (forall r : A > A > prop, (forall x : A, r x x) -> r x y)
        (x = y)
        (fun H : forall r : A > A > prop, (forall x : A, r x x) -> r x y =>
         H (fun x y : A => x = y) (eqI A))
        (fun (xy : x = y) (r : A > A > prop) (rxx : forall x : A, r x x) =>
         xy (fun y : A => r x y) (rxx x))))).
Qed. 

Theorem eq_leib4 (A : SType) : eq (A>A>prop) (fun (s t:A) => forall (r: A > A > prop),~ r s t -> ~ (forall x, r x x) ) (fun (s t: A ) => s = t).
exact (func_ext A (A > prop)
  (fun s t : A => forall r : A > A > prop, ~ r s t -> ~ (forall x : A, r x x))
  (fun s t : A => s = t)
  (fun x : A =>
   func_ext A prop
     (fun t : A =>
      forall r : A > A > prop, ~ r x t -> ~ (forall x : A, r x x))
     (fun t : A => x = t)
     (fun y : A =>
      prop_ext (forall r : A > A > prop, ~ r x y -> ~ (forall x : A, r x x))
        (x = y)
        (fun H : forall r : A > A > prop, ~ r x y -> ~ (forall x : A, r x x) =>
         NNPP (x = y)
           (fun H1 : x <> y => H (fun s t : A => s = t) H1 (eqI A)))
        (fun xy : x = y =>
         xy
           (fun y0 : A =>
            forall r : A > A > prop, ~ r x y0 -> ~ (forall x : A, r x x))
           (fun (r : A > A > prop) (rxx : ~ r x x) (H : forall x : A, r x x) =>
            rxx (H x)))))).
Qed. 

Lemma TRef (A:SType) : forall x:A, x <> x -> False.
exact (fun x H => H (eqI A x)).
Qed.

Lemma TImp : forall X Y:prop , (X -> Y) -> (~X -> False) -> (Y -> False) -> False.
exact (fun (X Y : prop) (H : X -> Y) (R1 : ~ X -> False) (R2 : Y -> False) =>
R1 (fun x : X => R2 (H x))).
Qed.

Lemma TNAnd : forall X Y:prop , ~(X /\ Y) -> (~X -> False) -> (~Y -> False) -> False.
exact (fun (X Y : prop) (H : ~ (X /\ Y)) (R1 : ~ X -> False) (R2 : ~ Y -> False) =>
R1 (fun x : X => R2 (fun y : Y => H (andI X Y x y)))).
Qed.

Lemma TAnd : forall X Y:prop , (X /\ Y) -> (X -> Y -> False) -> False.
exact (fun (X Y : prop) (H : X /\ Y) (R : X -> Y -> False) => H False R).
Qed.

Lemma TOr : forall X Y:prop , (X \/ Y) -> (X -> False) -> (Y-> False) -> False.
exact (fun (X Y : prop) (H : X \/ Y) (R : X -> False) (R1 : Y -> False) => H False R R1).
Qed.

Lemma TNOr : forall X Y:prop , ~(X \/ Y) -> (~X -> ~Y -> False) -> False.
exact (fun (X Y : prop) (H : ~ (X \/ Y)) (R : ~ X -> ~ Y -> False) =>
R (fun H' : X => H (orIL X Y H')) (fun H' : Y => H (orIR X Y H'))).
Qed.

Lemma TNImp : forall X Y:prop , ~(X -> Y) -> (X -> ~Y -> False) -> False.
exact (fun (X Y : prop) (H : ~ (X -> Y)) (R : X -> ~ Y -> False) =>
H (fun x : X => R x (fun y : Y => H (fun _ : X => y)) Y)).
Qed.

Lemma TAll (A : SType) : forall (p:A > prop) , (forall x:A, p x) -> forall y:A, (p y -> False) -> False.
exact (fun (p : A > prop) (H : forall x : A, p x) 
  (y : A) (R : p y -> False) => R (H y)).
Qed.

Lemma TNAll (A : SType) : forall (p:A > prop) , ~(forall x:A, p x) -> (forall y:A, ~p y -> False) -> False.
exact (fun (p : A > prop) (H : ~ (forall x : A, p x))
  (R : forall y : A, ~ p y -> False) =>
H
  (fun x : A =>
   classic (p x) (p x) (fun a : p x => a) (fun a : ~ p x => R x a (p x)))).
Qed.

Lemma TEx (A : SType) : forall (p:A > prop) , (exists x:A, p x) -> (forall y:A, p y -> False) -> False.
exact (fun (p : A > prop) (H : exists x:A, p x)
  (R : forall y : A, p y -> False) =>
H False (fun (x : A) (H1 : p x) => R x H1)).
Qed.

Lemma TNEx (A : SType) : forall (p:A > prop) , ~(exists x:A, p x) -> forall y:A, (~p y -> False) -> False.
exact (fun (p : A > prop) (H : ~ (exists x:A, p x)) 
  (y : A) (R : ~ p y -> False) =>
R (fun py : p y => H (exI A (fun x : A => p x) y py))).
Qed.

Lemma TBQ : forall X Y:prop , (X = Y) -> (X -> Y -> False) -> ( ~X -> ~Y -> False) -> False.
exact (fun (X Y : prop) (H : X = Y) =>
H (fun Y0 : prop => (X -> Y0 -> False) -> (~ X -> ~ Y0 -> False) -> False)
  (fun (H1 : X -> X -> False) (H2 : ~ X -> ~ X -> False) =>
   H2 (fun y : X => H1 y y) (fun y : X => H1 y y))).
Qed.

Lemma TBE : forall X Y:prop , (X <> Y) -> (X -> ~Y -> False) -> ( ~X -> Y -> False) -> False.
exact (fun (X Y : prop) (H : X <> Y) (R1 : X -> ~ Y -> False) (R2 : ~ X -> Y -> False) =>
H
  (prop_ext X Y (fun x : X => NNPP Y (fun H' : ~ Y => R1 x H'))
     (fun y : Y => NNPP X (fun H' : ~ X => R2 H' y)))).
Qed.

Lemma TIff : forall X Y:prop , (X <-> Y) -> (X -> Y -> False) -> ( ~X -> ~Y -> False) -> False.
exact (fun (X Y : prop) (H : X <-> Y) (R1 : X -> Y -> False) (R2 : ~ X -> ~ Y -> False) =>
H False
  (fun (H1 : X -> Y) (H2 : Y -> X) =>
   R2 (fun x : X => R1 x (H1 x)) (fun y : Y => R1 (H2 y) y))).
Qed.

Lemma TNIff : forall X Y:prop , ~(X <-> Y) -> (X -> ~Y -> False) -> ( ~X -> Y -> False) -> False.
exact (fun (X Y : prop) (H : ~ (X <-> Y)) (R1 : X -> ~ Y -> False)
  (R2 : ~ X -> Y -> False) =>
H
  (andI (X -> Y) (Y -> X) (fun x : X => NNPP Y (R1 x))
     (fun y : Y => NNPP X (fun nx : ~ X => R2 nx y)))).
Qed.

Lemma TFQ (A B: SType) : forall (s t:A > B) , 
(s = t) -> ((forall x:A, s x = t x) -> False) -> False.
exact (fun (s t : A > B) (H : s = t) =>
H (fun t0 : A > B => ((forall x : A, s x = t0 x) -> False) -> False)
  (fun R : (forall x : A, s x = s x) -> False => R (fun x : A => eqI B (s x)))).
Qed.

Lemma TFE (A B: SType) : forall (s t:A > B) , 
(s <> t) -> (~(forall x:A, s x = t x) -> False) -> False.
exact (fun (s t : A > B) (H : s <> t)
  (R : ~ (forall x : A, s x = t x) -> False) =>
R (fun H' : forall x : A, s x = t x => H (func_ext A B s t H'))).
Qed.

Lemma TCon (A : SType) : forall (s t u v:A) ,
 (s = t) -> (u <> v) -> 
( s <> u -> t <> u -> False) -> 
( s <> v -> t <> v -> False) -> False.
exact (fun (s t u v : A) (H1 : s = t) (H2 : u <> v) =>
H1
  (fun t0 : A =>
   (s <> u -> t0 <> u -> False) -> (s <> v -> t0 <> v -> False) -> False)
  (fun (R1 : s <> u -> s <> u -> False) (R2 : s <> v -> s <> v -> False) =>
   imp_false_dup (s <> u) R1
     (fun H3 : s = u =>
      imp_false_dup (s <> v) R2
        (fun H4 : s = v => H2 (eq_symtrans2 A u s v H3 H4))))).
Qed.

Lemma Ttrans (A : SType) : forall (s u t :A), 
(s=t) -> (t=u) -> ((s=u) -> False) -> False.
exact (fun (s u t : A) (H1 : s = t) (H2 : t = u) (R1 : s = u -> False) =>
R1 (eq_trans A s t u H1 H2)).
Qed.

Lemma TDec (A B: SType) : forall (s t:A) (p q:A > B),
p s <> q t -> (p <> q -> False) -> ( s <> t -> False) ->  False.
exact (fun (s t : A) (p q : A > B) (H1 : p s <> q t)
  (H2 : p <> q -> False) (H3 : s <> t -> False) =>
H2
  (fun H2' : p = q =>
   H3
     (fun H3' : s = t =>
      H1
        (H2' (fun q : A > B => p s = q t)
           (H3' (fun t : A => p s = p t) (eqI B (p s))))))).
Qed.

Lemma TMat (A : SType) : forall (s t:A) (p q:A > prop),
p s -> ~ q t -> ( p <> q -> False ) -> ( s <> t -> False)-> False.
exact (fun (s t : A) (p q : A > prop) (H1a : p s) 
  (H1b : ~ q t) (H2 : p <> q -> False) (H3 : s <> t -> False) =>
H2
  (fun H2' : p = q =>
   H3
     (fun H3' : s = t =>
      H1b (H2' (fun q : A > prop => q t) (H3' p H1a))))).
Qed.

Lemma TEps (A:SType) : forall (p:A>prop) , ((forall x, ~ p x) -> False) -> (p (Eps A p) -> False) -> False.
exact (fun (p : A > prop) (H1 : (forall x : A, ~ p x) -> False)
  (H2 : p (Eps A p) -> False) =>
H1 (fun (x : A) (H3 : p x) => H2 (EpsR A p x H3))).
Qed.

Lemma TEps' (A:SType) : forall (eps: (A>prop)>A) (p:A>prop) , (forall (q:A>prop) (y:A), q y -> q (eps q)) -> ((forall x , ~ p x) -> False) -> (p (eps p) -> False) -> False.
exact (fun (eps : (A > prop) > A) (p : A > prop)
  (H1 : forall (q : A > prop) (y : A), q y -> q (eps q)) => fun H =>
  fun (H2 : p (eps p) -> False) => H (fun (x : A) (px : p x) => H2 (H1 p x px))).
Qed.

Lemma TEps'' (A:SType) : forall (eps: (A>prop)>A) (p:A>prop) ,  (forall (q:A>prop), ~ (forall (y:A),~ q y) -> q (eps q)) -> ((forall x , ~ p x) -> False) -> (p (eps p) -> False) -> False.
exact (fun (eps : (A > prop) > A) (p : A > prop)
  (H1 : forall q : A > prop, ~ (forall y : A, ~ q y) -> q (eps q))
  => fun H => fun (H2 : p (eps p) -> False) =>
  H (fun (x : A) (px : p x) => H2 (H1 p (fun H3 : forall y : A, ~ p y => H3 x px)))).
Qed.

Lemma TEps''' (A:SType) : forall (eps: (A>prop)>A) (p:A>prop) ,  (forall (q:A>prop), (exists y:A , q y) -> q (eps q)) -> ((forall x , ~ p x) -> False) -> (p (eps p) -> False) -> False.
exact (fun (eps : (A > prop) > A) (p : A > prop)
  (H1 : forall q : A > prop, (exists y:A, q y) -> q (eps q)) =>
  fun H => fun (H2 : p (eps p) -> False) =>
  H (fun (x : A) (px : p x) => H2 (H1 p (exI A (fun y : A => p y) x px)))).
Qed.

Lemma TRew (A : SType) : forall (s t:A) (q:A>prop), s = t -> q s -> (q t -> False) -> False.
exact (fun s t q H1 H2 H3 => H3 (H1 q H2)).
Qed.

Lemma TRewr (A : SType) : forall (s t:A) (q:A>prop), s = t -> q t -> (q s -> False) -> False.
exact (fun s t q H1 H2 H3 => H3 (eqEr A t s q H2 H1)).
Qed.

(*** If: Dec 2011 ***)
Definition If (A : SType) : prop>A>A>A := (fun p x y => Eps A (fun z => p /\ z = x \/ ~p /\ z = y)).

Lemma If_correct (A : SType) : forall p:prop, forall x y:A,
p /\ If A p x y = x \/ ~p /\ If A p x y = y.
exact (fun (p : prop) (x y : A) =>
classic p (p /\ If A p x y = x \/ ~ p /\ If A p x y = y)
  (fun H1 : p =>
   EpsR A (fun z : A => p /\ z = x \/ ~ p /\ z = y) x
     (orIL (p /\ x = x) (~ p /\ x = y) (andI p (x = x) H1 (eqI A x))))
  (fun H1 : ~ p =>
   EpsR A (fun z : A => p /\ z = x \/ ~ p /\ z = y) y
     (orIR (p /\ y = x) (~ p /\ y = y) (andI (~ p) (y = y) H1 (eqI A y))))).
Qed.

Lemma If_0 (A : SType) : forall p:prop, forall x y:A,
~ p -> If A p x y = y.
exact (fun (p : prop) (x y : A) (H1 : ~ p) =>
If_correct A p x y (If A p x y = y)
  (fun H2 : p /\ If A p x y = x =>
   H2 (If A p x y = y)
     (fun (H3 : p) (_ : If A p x y = x) => H1 H3 (If A p x y = y)))
  (fun H2 : ~ p /\ If A p x y = y =>
   H2 (If A p x y = y) (fun (_ : ~ p) (H4 : If A p x y = y) => H4))).
Qed.

Lemma If_1 (A : SType) : forall p:prop, forall x y:A,
p -> If A p x y = x.
exact (fun (p : prop) (x y : A) (H1 : p) =>
If_correct A p x y (If A p x y = x)
  (fun H2 : p /\ If A p x y = x =>
   H2 (If A p x y = x) (fun (_ : p) (H4 : If A p x y = x) => H4))
  (fun H2 : ~ p /\ If A p x y = y =>
   H2 (If A p x y = x)
     (fun (H3 : ~ p) (_ : If A p x y = y) => H3 H1 (If A p x y = x)))).
Qed.

