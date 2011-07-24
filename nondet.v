Load basics.

Variable Nondet : D->D->D.
Notation "p 'nondet' q" := (Nondet p q) (at level 17).


Axiom NondetDefinition:
  forall p q r : D,
  p ref p nondet q  /\ q ref p nondet q
  /\ forall r':D, p ref r' /\ q ref r' -> p nondet q ref r'.
(* 
This axiom automatically implies that R is semilattice
*)

Hint Resolve NondetDefinition.


Lemma NondetCommutativity:
  forall p q : D, p nondet q = q nondet p.
Proof.
(* TODO *)
Admitted.



Lemma NondetIncreasing:
  forall p q : D, p ref p nondet q.
Proof.
(* TODO *)
Admitted.


Lemma NondetIdempotent:
  forall p : D, p nondet p = p.
Proof.


(* TODO *)
Admitted.