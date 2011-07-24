Load basics.

Variable eps : D.

Definition SkipLaw :=
  forall p : D,
  p; eps = p /\ p = eps; p.

Definition NullityForHoare :=
  forall p : D,
  [p] eps [p].

Theorem SkipImpliesNullityForHoare : SkipLaw -> NullityForHoare.
Proof.
unfold SkipLaw.
unfold NullityForHoare.
unfold HoareTriple.
intuition.
assert (p; eps = p).
  apply H.
rewrite H0.
trivial.
Qed.
