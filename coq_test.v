
(* programs, designs, specifications *)
Variable D : Set.


(* refinement relationship *)
Variable R : D -> D -> Prop.
Notation "A 'ref' B" := (R A B) (at level 20, right associativity).

Axiom Transitivity : forall x y z : D,  R x y /\ R y z -> R x z.
Axiom Reflexivity : forall x : D, x ref x.
Axiom AntiSymmetry : forall x y : D, R x y -> R y x -> x = y.

Hint Resolve Transitivity Reflexivity AntiSymmetry.


(* sequential composition *)

Variable SeqComp : D -> D -> D.
Notation "A ; B" := (SeqComp A B) (at level 15, right associativity).


Definition HoareTriple (p q r : D) := R (SeqComp p q) r.
Notation "[ A ] B [ C ]" := (HoareTriple A B C) (at level 20).
(* square brackets because of syntactic limitations *)



Definition MonotonicityLaw := 
  forall p q p' q' : D, 
  p ref p' -> R q q' ->
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
