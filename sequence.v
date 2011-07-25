Load basics.


Definition AssociativityLaw :=
  forall p q r : basics.D,
  (p; q); r = p; (q; r).


Definition SequenceRule (triple : D->D->D->Prop) :=
  forall p q s q' r : D,
  triple p q s ->
  triple s q' r ->
  triple p (q;q') r.

Hint Unfold  SequenceRule.

Theorem ASH : AssociativityLaw -> SequenceRule HoareTriple.
Proof.
intro Assoc.
autounfold.
intuition.
rewrite <- Assoc.
eauto.
Qed.

Print ASH.


Theorem ASP: AssociativityLaw -> SequenceRule PlotkinReduction.
Proof.
intro Assoc.
autounfold.
intuition.
rewrite <- Assoc.
apply Transitivity with (y := s;q').
auto.
Qed.


Theorem ASM: AssociativityLaw -> SequenceRule MilnerTransition.
Proof.
intro Assoc.
autounfold.
intuition.
rewrite Assoc.
eauto.
Qed.


Theorem AST: AssociativityLaw -> SequenceRule TestGeneration.
Proof.
intro Assoc.
autounfold.
intuition.
rewrite Assoc.
eauto.
Qed.

Theorem SHSPA : SequenceRule HoareTriple /\ SequenceRule PlotkinReduction ->
 AssociativityLaw.
Proof.
unfold SequenceRule, HoareTriple, PlotkinReduction, AssociativityLaw.
intros.
elim H.
intros.
intuition.
clear H2.
clear H3.
apply AntiSymmetry.
apply H1 with (p; q).
apply Reflexivity.
apply Reflexivity.
apply H0 with (p; q).
apply Reflexivity.
apply Reflexivity.
Qed.

Theorem SMSTA : SequenceRule MilnerTransition /\ SequenceRule TestGeneration ->
 AssociativityLaw.
Proof.
unfold SequenceRule, TestGeneration, MilnerTransition, AssociativityLaw.
intros.
elim H.
intros.
intuition.
clear H2.
clear H3.
apply AntiSymmetry.
apply H0 with (q; r).
apply Reflexivity.
apply Reflexivity.
apply H1 with (q; r).
apply Reflexivity.
apply Reflexivity.
Qed.