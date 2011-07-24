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
intro SL.
unfold NullityForHoare.
unfold HoareTriple.
intuition.
assert (TMP : p; eps = p).
  apply SL.
rewrite TMP.
trivial.
Qed.
