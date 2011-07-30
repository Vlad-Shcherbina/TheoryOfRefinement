Load basics.

Variable wp : D -> D -> D.

Definition WP_definition :=
  forall q r : D,
  [wp q r]q[r] /\
    forall p' : D, [p']q[r] -> p' ref wp q r.


Definition AdjointnessLaw :=
  forall p q r :D,
  p ref wp q r <-> p;q ref r.


Hint Unfold WP_definition AdjointnessLaw.

Theorem ALWPD : AdjointnessLaw -> WP_definition.
Proof.
intro AL.
autounfold.
intuition.
  apply AL.
  trivial.
  
  apply AL.
  trivial.
Qed.

Theorem WPDAL : WP_definition -> AdjointnessLaw.
Proof.
intro WPD.
autounfold.
intuition.
apply Transitivity with (wp q r;q).
intuition.
apply WPD.
apply WPD.
trivial.
Qed.



(*
Definition WP1 :=
  forall p q r : D,
  p ref wp q r -> 
*)