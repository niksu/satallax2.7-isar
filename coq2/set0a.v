Require Export stt4.

(** * membership and subset for set theory **)

(** In is the membership relation on set.  We use x :e y as notation to mean "x is a member of y" and x /:e y as notation for "x is not a member of y." **)

Parameter In:set>set>prop. (* 16 0 0 *)

Notation "x ':e' y" := (In x y) (at level 70).
Notation "x '/:e' y" := (~(In x y)) (at level 70).

(** Subq is the subset relation on set.  We use X c= Y as notation to mean "X is a subset of Y" and X /c= Y as notation for "X is not a subset of Y." **)

Definition Subq : set>set>prop :=
fun X Y => forall x:set, x :e X -> x :e Y.

Notation "X 'c=' Y" := (Subq X Y) (at level 70).
Notation "X '/c=' Y" := (~(Subq X Y)) (at level 70).

