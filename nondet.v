Load basics.

Variable Nondet : D -> D -> D.
Notation "p 'nondet' q" := (Nondet p q) (at level 17).


Axiom NondetDefinition:
  forall p q : D,
  p ref p nondet q  /\ q ref p nondet q
  /\ forall r':D, p ref r' /\ q ref r' -> p nondet q ref r'.
(* 
This axiom together with totality of nondet operation 
automatically implies that R is semilattice
*)

Hint Resolve NondetDefinition.



Lemma NondetIdempotent:
  forall p : D, p nondet p = p.
Proof.
intuition.
assert (p nondet p ref p).
  apply NondetDefinition with (p := p) (q := p).
  auto.
assert (p ref p nondet p).
  apply NondetDefinition with (p := p) (q := p).
  auto.
Qed.


Lemma NondetCommutativity:
  forall p q : D, p nondet q = q nondet p.
Proof.
intuition.
assert (p nondet q ref q nondet p).
  apply NondetDefinition with (p:=p) (q:=q).
Admitted.


Lemma NondetIncreasing:
  forall p q : D, p ref p nondet q.
Proof.
(* TODO *)
Admitted.

*)


