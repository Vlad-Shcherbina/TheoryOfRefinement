Load basics.

Definition AssociativityLaw :=
  forall p q r : D,
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



(* TODO for other triples*)



Theorem SHA : SequenceRule HoareTriple -> AssociativityLaw.
Proof.
unfold SequenceRule, HoareTriple.

(* TODO *)

