Load basics.

Variable eps : D.

Definition SkipLaw :=
  forall p : D,
  p; eps = p /\ p = eps; p.

Definition NullityForHoare :=
  forall p : D,
  [p] eps [p].

Definition NullityForPlotkin :=
  forall p : D,
  PlotkinReduction p eps p.

Definition NullityForMilner :=
  forall p : D,
  MilnerTransition p eps p.

Definition NullityForTest :=
  forall p : D,
  TestGeneration p eps p.

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

Theorem SkipImpliesNullityForPlotkin : SkipLaw -> NullityForPlotkin.
Proof.
intro SL.
unfold NullityForPlotkin.
unfold PlotkinReduction.
intuition.
assert (TMP : p ; eps = p).
apply SL.
rewrite TMP.
trivial.
Qed.

Theorem SkipImpliesNullityForTest : SkipLaw -> NullityForTest.
Proof.
intro SL.
unfold NullityForTest.
unfold TestGeneration.
intuition.
assert (TMP : eps ; p = p).
symmetry.
apply SL.
rewrite TMP.
trivial.
Qed.

Theorem SkipImpliesNullityForMilner : SkipLaw -> NullityForMilner.
Proof.
intro SL.
unfold NullityForMilner.
unfold MilnerTransition.
intuition.
assert (TMP : eps ; p = p).
symmetry.
apply SL.
rewrite TMP.
trivial.
Qed.

