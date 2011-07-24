Module basics.

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
Notation "A ; B" := (SeqComp A B) (at level 15).


Axiom Monotonicity :
  forall p q p' q' : basics.D,
  p ref p' -> q ref q' ->
  (p; q) ref (p'; q').

Hint Resolve Monotonicity.


(* triples *)

Definition HoareTriple (p q r : D) := R (SeqComp p q) r.
Notation "[ A ] B [ C ]" := (HoareTriple A B C) (at level 20).
(* square brackets because of syntactic limitations *)

Definition PlotkinReduction (p q r : D) := r ref p; q.
Definition MilnerTransition (p q r : D) := q; r ref p.
Definition TestGeneration (p q r : D) := p ref q; r.
(* no sugar for these triples because it's ugly anyway *)

End basics.
Export basics.