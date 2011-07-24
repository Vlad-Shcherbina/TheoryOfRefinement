(*
Some outdated stuff we don't need to prove anyway
*)


Load basics.

Definition MonotonicityLaw := 
  forall p q p' q' : basics.D, 
  p ref p' -> q ref q' ->
  (p; q) ref (p'; q').

Definition RuleOfConsequence := 
  forall p q r p_ r' : D,
  R p_ p ->
  R r r' ->
  [p]q[r] ->
  [p_]q[r'].




Theorem T1 : MonotonicityLaw -> RuleOfConsequence.
Proof.
unfold RuleOfConsequence.
unfold HoareTriple.
intros.
apply Transitivity with (y:=r).
intuition.
apply Transitivity with (y:= SeqComp p q).
intuition.
Qed.


(* RuleOfConsequence implies half of monotonicity law *)

Theorem T2 : RuleOfConsequence -> 
  (forall p p' q : D, p ref p' -> p; q ref p'; q).
Proof.
unfold RuleOfConsequence.
intro RoC.
intros.
apply RoC with (p := p') (r := p'; q) (r' := p'; q).
trivial.
trivial.
apply Reflexivity.
Qed.

Print Assumptions T2.