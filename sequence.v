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
apply Transitivity with(y:=(p;q);q').
split.
  rewrite Assoc.
  trivial.

  apply Transitivity with (y:=s;q').
  auto.
Qed.

(* TODO for other triples*)



Theorem SHA : SequenceRule HoareTriple -> AssociativityLaw.
Proof.
unfold SequenceRule, HoareTriple.

(* TODO *)

