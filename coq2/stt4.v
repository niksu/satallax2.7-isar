(*** Chad E Brown, Oct 2011, Knaster Tarski ***)
Require Export stt3.

(*** Polymorphic Unary Version ***)
Definition lfp (A : SType) : ((A>prop)>A>prop) > A>prop :=
fun F z => forall p:A > prop, (forall w:A, F p w -> p w) -> p z.

Definition gfp (A : SType) : ((A>prop)>A>prop) > A>prop :=
fun F z => exists p:A > prop, (forall w:A, p w -> F p w) /\ p z.

(*** Polymorphic Binary Version ***)
Definition lfp2 (A B : SType) : ((A>B>prop)>A>B>prop) > A>B>prop :=
fun F z z' => forall p:A>B>prop, (forall w:A, forall w':B, F p w w' -> p w w') -> p z z'.

Definition gfp2 (A B : SType) : ((A>B>prop)>A>B>prop) > A>B>prop :=
fun F z z' => exists p:A>B>prop, (forall w:A, forall w':B, p w w' -> F p w w') /\ p z z'.

(*** Concrete Theorems ***)

Lemma lfp_t (A:SType) : forall (F : (A > prop) > (A > prop)),
(forall X X':A > prop, (forall z:A, X z -> X' z) -> forall z:A, F X z -> F X' z)
->
let Y := lfp A F in
(F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, Y z -> X z.
exact (fun (F : (A > prop) > A > prop)
  (H1 : forall X X' : A > prop,
        (forall z : A, X z -> X' z) -> forall z : A, F X z -> F X' z) =>
let Y := lfp A F in
let H2 :=
  fun (z : A) (H2 : F Y z) (p : A > prop) (H3 : forall w : A, F p w -> p w) =>
  H3 z
    (H1 Y p
       (fun (u : A) (H4 : Y u) =>
        H4 (fun u0 : A => p u0) H3) z H2) in
andI (F Y = Y) (forall X : A > prop, F X = X -> forall z : A, Y z -> X z)
  (func_ext A prop (F Y) Y
     (fun z : A =>
      prop_ext (F Y z) (Y z) (H2 z)
        (fun H3 : Y z => H3 (F Y) (H1 (F Y) Y H2))))
  (fun (X : A > prop) (H3 : F X = X) (z : A) (H4 : Y z) =>
   H4 X
     (eq_sym (A > prop) (F X) X H3 (fun s : A > prop => forall w : A, s w -> X w)
        (fun (w : A) (H5 : X w) => H5)))).
Qed.

Lemma gfp_t (A:SType) : forall (F : (A > prop) > (A > prop)),
(forall X X':A > prop, (forall z:A, X z -> X' z) -> forall z:A, F X z -> F X' z)
->
let Y := gfp A F in
(F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, X z -> Y z.
exact (fun (F : (A > prop) > A > prop)
  (H1 : forall X X' : A > prop,
        (forall z : A, X z -> X' z) -> forall z : A, F X z -> F X' z) =>
let Y := gfp A F in
let H2 :=
  fun (z : A) (H2 : Y z) =>
  H2 (F Y z)
    (fun (p : A > prop) (H3 : (forall w : A, p w -> F p w) /\ p z) =>
     H3 (F Y z)
       (fun (H4 : forall w : A, p w -> F p w) (H5 : p z) =>
        H1 p Y
          (fun (u : A) (H6 : p u) =>
           exI (A > prop)
             (fun p0 : A > prop => (forall w : A, p0 w -> F p0 w) /\ p0 u) p
             (andI (forall w : A, p w -> F p w) (p u) H4 H6)) z 
          (H4 z H5))) in
andI (F Y = Y) (forall X : A > prop, F X = X -> forall z : A, X z -> Y z)
  (func_ext A prop (F Y) Y
     (fun z : A =>
      prop_ext (F Y z) (Y z)
        (fun H3 : F Y z =>
         exI (A > prop) (fun p : A > prop => (forall w : A, p w -> F p w) /\ p z)
           (F Y)
           (andI (forall w : A, F Y w -> F (F Y) w) 
              (F Y z) (H1 Y (F Y) H2) H3)) (H2 z)))
  (fun (X : A > prop) (H3 : F X = X) (z : A) (H4 : X z) =>
   exI (A > prop) (fun p : A > prop => (forall w : A, p w -> F p w) /\ p z) X
     (andI (forall w : A, X w -> F X w) (X z)
        (eq_sym (A > prop) (F X) X H3
           (fun s : A > prop => forall w : A, X w -> s w)
           (fun (w : A) (H5 : X w) => H5)) H4))).
Qed.

Lemma lfp2_t (A B:SType) : forall (F : (A>B>prop) > (A>B>prop)),
(forall X X':A>B>prop, (forall z:A, forall z':B, X z z' -> X' z z') -> forall z:A, forall z':B, F X z z' -> F X' z z')
->
let Y := lfp2 A B F in
(F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, Y z z' -> X z z'.
exact (fun (F : (A > B > prop) > A > B > prop)
  (H1 : forall X X' : A > B > prop,
        (forall (z : A) (z' : B), X z z' -> X' z z') ->
        forall (z : A) (z' : B), F X z z' -> F X' z z') =>
let Y := lfp2 A B F in
let H2 :=
  fun (z : A) (z' : B) (H2 : F Y z z') (p : A > B > prop)
    (H3 : forall (w : A) (w' : B), F p w w' -> p w w') =>
  H3 z z'
    (H1 Y p
       (fun (u : A) (u' : B) (H4 : Y u u') =>
        H4 (fun (u0 : A) (u'0 : B) => p u0 u'0)
            H3) z z' H2) in
andI (F Y = Y)
  (forall X : A > B > prop, F X = X -> forall (z : A) (z' : B), Y z z' -> X z z')
  (func_ext A (B > prop) (F Y) Y
     (fun z : A =>
      func_ext B prop (F Y z) (Y z)
        (fun z' : B =>
         prop_ext (F Y z z') (Y z z') (H2 z z')
           (fun H3 : Y z z' => H3 (F Y) (H1 (F Y) Y H2)))))
  (fun (X : A > B > prop) (H3 : F X = X) (z : A) (z' : B) (H4 : Y z z') =>
   H4 X
     (eq_sym (A > B > prop) (F X) X H3
        (fun s : A > B > prop => forall (w : A) (w' : B), s w w' -> X w w')
        (fun (w : A) (w' : B) (H5 : X w w') => H5)))).
Qed.

Lemma gfp2_t (A B:SType) : forall (F : (A>B>prop) > (A>B>prop)),
(forall X X':A>B>prop, (forall z:A, forall z':B, X z z' -> X' z z') -> forall z:A, forall z':B, F X z z' -> F X' z z')
->
let Y := gfp2 A B F in
(F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, X z z' -> Y z z'.
exact (fun (F : (A > B > prop) > A > B > prop)
  (H1 : forall X X' : A > B > prop,
        (forall (z : A) (z' : B), X z z' -> X' z z') ->
        forall (z : A) (z' : B), F X z z' -> F X' z z') =>
let Y := gfp2 A B F in
let H2 :=
  fun (z : A) (z' : B) (H2 : Y z z') =>
  H2 (F Y z z')
    (fun (p : A > B > prop)
       (H3 : (forall (w : A) (w' : B), p w w' -> F p w w') /\ p z z') =>
     H3 (F Y z z')
       (fun (H4 : forall (w : A) (w' : B), p w w' -> F p w w') (H5 : p z z') =>
        H1 p Y
          (fun (u : A) (u' : B) (H6 : p u u') =>
           exI (A > B > prop)
             (fun p0 : A > B > prop =>
              (forall (w : A) (w' : B), p0 w w' -> F p0 w w') /\ p0 u u') p
             (andI (forall (w : A) (w' : B), p w w' -> F p w w') 
                (p u u') H4 H6)) z z' (H4 z z' H5))) in
andI (F Y = Y)
  (forall X : A > B > prop, F X = X -> forall (z : A) (z' : B), X z z' -> Y z z')
  (func_ext A (B > prop) (F Y) Y
     (fun z : A =>
      func_ext B prop (F Y z) (Y z)
        (fun z' : B =>
         prop_ext (F Y z z') (Y z z')
           (fun H3 : F Y z z' =>
            exI (A > B > prop)
              (fun p : A > B > prop =>
               (forall (w : A) (w' : B), p w w' -> F p w w') /\ p z z') 
              (F Y)
              (andI (forall (w : A) (w' : B), F Y w w' -> F (F Y) w w')
                 (F Y z z') (H1 Y (F Y) H2) H3)) (H2 z z'))))
  (fun (X : A > B > prop) (H3 : F X = X) (z : A) (z' : B) (H4 : X z z') =>
   exI (A > B > prop)
     (fun p : A > B > prop =>
      (forall (w : A) (w' : B), p w w' -> F p w w') /\ p z z') X
     (andI (forall (w : A) (w' : B), X w w' -> F X w w') 
        (X z z')
        (eq_sym (A > B > prop) (F X) X H3
           (fun s : A > B > prop => forall (w : A) (w' : B), X w w' -> s w w')
           (fun (w : A) (w' : B) (H5 : X w w') => H5)) H4))).
Qed.

(*** Abstract Theorems ***)
Lemma lfpe_t (A:SType) : forall (F : (A > prop) > (A > prop)),
(forall X X':A > prop, (forall z:A, X z -> X' z) -> forall z:A, F X z -> F X' z)
->
exists Y, (F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, Y z -> X z.
exact (fun F H =>
          (exI (A>prop) (fun Y => (F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, Y z -> X z)
               (lfp A F)
               (lfp_t A F H))).
Qed.

Lemma gfpe_t (A:SType) : forall (F : (A > prop) > (A > prop)),
(forall X X':A > prop, (forall z:A, X z -> X' z) -> forall z:A, F X z -> F X' z)
->
exists Y, (F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, X z -> Y z.
exact (fun F H =>
          (exI (A>prop) (fun Y => (F Y = Y) /\ forall X:A > prop, F X = X -> forall z:A, X z -> Y z)
               (gfp A F)
               (gfp_t A F H))).
Qed.

Lemma fpe_t (A:SType) : forall (F : (A > prop) > (A > prop)),
(forall X X':A > prop, (forall z:A, X z -> X' z) -> forall z:A, F X z -> F X' z)
->
exists Y, (F Y = Y).
exact (fun (F : (A > prop) > A > prop)
  (H1 : forall X X' : A > prop,
        (forall z : A, X z -> X' z) -> forall z : A, F X z -> F X' z) =>
exI (A > prop) (fun Y : A > prop => F Y = Y) (lfp A F)
  (lfp_t A F H1 (F (lfp A F) = lfp A F)
     (fun (H2 : F (lfp A F) = lfp A F)
        (_ : forall X : A > prop, F X = X -> forall z : A, lfp A F z -> X z) =>
      H2))).
Qed.

Lemma lfp2e_t (A B:SType) : forall (F : (A>B>prop) > (A>B>prop)),
(forall X X':A>B>prop, (forall z:A, forall z':B, X z z' -> X' z z') -> forall z:A, forall z':B, F X z z' -> F X' z z')
->
exists Y, (F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, Y z z' -> X z z'.
exact (fun F H =>
          (exI (A>B>prop) (fun Y => (F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, Y z z' -> X z z')
               (lfp2 A B F)
               (lfp2_t A B F H))).
Qed.

Lemma gfp2e_t (A B:SType) : forall (F : (A>B>prop) > (A>B>prop)),
(forall X X':A>B>prop, (forall z:A, forall z':B, X z z' -> X' z z') -> forall z:A, forall z':B, F X z z' -> F X' z z')
->
exists Y, (F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, X z z' -> Y z z'.
exact (fun F H =>
          (exI (A>B>prop) (fun Y => (F Y = Y) /\ forall X:A>B>prop, F X = X -> forall z:A, forall z':B, X z z' -> Y z z')
               (gfp2 A B F)
               (gfp2_t A B F H))).
Qed.

Lemma fp2 (A B:SType) : forall (F : (A>B>prop) > (A>B>prop)),
(forall X X':A>B>prop, (forall z:A, forall z':B, X z z' -> X' z z') -> forall z:A, forall z':B, F X z z' -> F X' z z')
->
exists Y, (F Y = Y).
exact (fun (F : (A > B > prop) > A > B > prop)
  (H1 : forall X X' : A > B > prop,
        (forall (z : A) (z' : B), X z z' -> X' z z') ->
        forall (z : A) (z' : B), F X z z' -> F X' z z') =>
exI (A > B > prop) (fun Y : A > B > prop => F Y = Y) (lfp2 A B F)
  (lfp2_t A B F H1 (F (lfp2 A B F) = lfp2 A B F)
     (fun (H2 : F (lfp2 A B F) = lfp2 A B F)
        (_ : forall X : A > B > prop,
             F X = X -> forall (z : A) (z' : B), lfp2 A B F z z' -> X z z') =>
      H2))).
Qed.
