Load basics.

(* sequential composition *)

Variable ParComp : D -> D -> D.
Notation "A | B" := (ParComp A B) (at level 16).

Axiom ParCommutativity :
  forall p q : D,
  p | q = q | p.

Axiom ParAssociativity :
  forall p q r : D,
  (p | q) | r = p | (q | r).

Hint Resolve ParAssociativity.
