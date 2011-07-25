Load basics.


Axiom ParAssociativity :
  forall p q r : D,
  (p | q) | r = p | (q | r).

Hint Resolve ParAssociativity.


Definition ExchangeLaw :=
  forall p p' q q' : D,
  (p | p') ; (q | q') ref (p ; q) | (p' ; q').

Definition ParallelForHoare :=
  forall p p' q q' r r': D,
  [p]q[r] /\ [p']q'[r'] -> [p|p']q|q'[r|r'].

Definition ParallelForMilner :=
  forall p p' q q' r r': D,
  MilnerTransition p q r /\ MilnerTransition p' q' r' -> MilnerTransition (p|p') (q|q') (r|r').

Theorem ExchangeImpliesParallelForHoare: ExchangeLaw -> ParallelForHoare.
Proof.
intros EL.
unfold ParallelForHoare.
unfold HoareTriple.
intuition.
assert (TMP: (p | p') ; (q | q') ref (p ; q) | (p' ; q')).
apply EL.
apply Transitivity with (y := (p ; q) | (p' ; q')).
intuition.
Qed.

Theorem ExchangeImpliesParallelForMilner: ExchangeLaw -> ParallelForMilner.
Proof.
intros EL.
unfold ParallelForMilner.
unfold MilnerTransition.
intuition.
assert (TMP: (q | q') ; (r | r') ref (q ; r) | (q' ; r')).
apply EL.
apply Transitivity with (y := q; r | q'; r').
auto.
Qed.

Theorem ParallelForHoareImpliesExchange: ParallelForHoare -> ExchangeLaw.
Proof.
intros PH.
unfold ParallelForHoare.
unfold HoareTriple.
unfold ExchangeLaw.
intuition.
apply PH.
auto.
Qed.

Theorem ParallelForMilnerImpliesExchange: ParallelForMilner -> ExchangeLaw.
Proof.
intros PM.
unfold ParallelForMilner.
unfold MilnerTransition.
unfold ExchangeLaw.
intuition.
apply PM.
auto.
Qed.