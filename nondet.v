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


Hint Extern 10 (_ ref _) => apply NondetDefinition.
(* so when we see 'x ref y' we try to apply NondetDefinition *)


Lemma NondetIdempotency:
  forall p : D, p nondet p = p.
Proof.
auto.
Qed.

Hint Rewrite NondetIdempotency.

Lemma NondetCommutativity:
  forall p q : D, p nondet q = q nondet p.
Proof.
auto.
Qed.


Definition NondetLeftDistributivity :=
  forall p q q' : D,
  p; (q nondet q') = p;q nondet p;q'.

Definition NondetRightDistributivity :=
  forall q q' r : D,
  (q nondet q'); r = q;r nondet q';r.

Hint Unfold NondetLeftDistributivity NondetRightDistributivity.


Definition HoareNondet :=
  forall p q q' r : D,
  [p]q[r] ->
  [p]q'[r] ->
  [p](q nondet q')[r].

Hint Unfold HoareNondet.


Theorem LDHN: NondetLeftDistributivity -> HoareNondet.
Proof.
intro LD.
autounfold; autounfold.
intuition.
rewrite LD.
auto.
Qed.


Definition PlotkinNondet :=
  forall p q q' r : D,
  (PlotkinReduction p q r \/ PlotkinReduction p q' r) -> 
    PlotkinReduction p (q nondet q') r.

Hint Unfold PlotkinNondet.

Theorem LDPN: NondetLeftDistributivity -> PlotkinNondet.
Proof.
intro LD.
autounfold; autounfold.
intuition.
eauto.
eauto.
Qed.


Definition MilnerNondet :=
  forall p q q' r : D,
    (MilnerTransition p q r /\ MilnerTransition p q' r) ->
      MilnerTransition p (q nondet q') r.

Hint Unfold MilnerNondet.

Theorem RDMN: NondetRightDistributivity -> MilnerNondet.
Proof.
intro RD.
autounfold; autounfold.
intuition.
rewrite RD.
auto.
Qed.


Definition TestGenerationNondet :=
  forall p q q' r : D,
    (TestGeneration p q r \/ TestGeneration p q' r) ->
      TestGeneration p (q nondet q') r.

Hint Unfold TestGenerationNondet.

Theorem RDTG: NondetRightDistributivity -> TestGenerationNondet.
Proof.
intro RD.
autounfold; autounfold.
intuition.
eauto.
eauto.
Qed.


(* TODO: Theorems 7, 8 *)


