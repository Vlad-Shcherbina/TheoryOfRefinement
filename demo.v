Load basics.

Definition ExchangeLaw :=
  forall p p' q q' : D,
  (p | p') ; (q | q') ⊑ (p ; q) | (p' ; q').

Definition ParallelRuleForMilner :=
  forall p p' q q' r r': D,
  MilnerTransition p q r /\ MilnerTransition p' q' r' 
  -> MilnerTransition (p|p') (q|q') (r|r').

Hint Unfold ParallelRuleForMilner.

Theorem T: 
  ExchangeLaw 
  -> ParallelRuleForMilner.
Proof.
intro.
unfold ParallelRuleForMilner.
intro; intro; intro; 
intro; intro; intro.
unfold MilnerTransition.
intro.
apply Transitivity with 
  (y := q; r | q'; r').
split.
  apply H.
  apply ParMonotonicity.
    apply H0.
    apply H0.
Qed.




Theorem T2:
  ExchangeLaw -> ParallelRuleForMilner.
Proof.
autounfold.
intuition.
eauto.
Qed.














