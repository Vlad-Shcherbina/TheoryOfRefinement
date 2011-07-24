Load basics.


Definition AssociativityLaw :=
  forall p q r : basics.D,
  (p; q); r = p; (q; r).


Definition SequenceRule (triple : D->D->D->Prop) :=
  forall p q s q' r : D,
  triple p q s ->
  triple s q' r ->
  triple p (q;q') r.



Theorem ASH : AssociativityLaw -> SequenceRule HoareTriple.
Proof.
unfold AssociativityLaw, SequenceRule, HoareTriple.
intro Assoc.
intuition.
rewrite <- Assoc.
eauto.
Qed.

Print ASH.


Theorem ASP: AssociativityLaw -> SequenceRule PlotkinReduction.
Proof.
unfold AssociativityLaw, SequenceRule, PlotkinReduction.
intro Assoc.
intuition.
rewrite <- Assoc.
apply Transitivity with (y := s;q').
auto.
Qed.


Theorem ASM: AssociativityLaw -> SequenceRule MilnerTransition.
Proof.
unfold AssociativityLaw, SequenceRule, MilnerTransition.
intro Assoc.
intuition.
rewrite Assoc.
eauto.
Qed.


Theorem AST: AssociativityLaw -> SequenceRule TestGeneration.
Proof.
unfold AssociativityLaw, SequenceRule, TestGeneration.
intro Assoc.
intuition.
rewrite Assoc.
eauto.
Qed.



(* TODO for other triples*)



Theorem SHA : SequenceRule HoareTriple -> AssociativityLaw.
Proof.
unfold SequenceRule, HoareTriple.

(* TODO *)

