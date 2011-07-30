Load basics.

Variable wp : D -> D -> D.

Definition WP_definition :=
  forall q r : D,
  [wp q r]q[r] /\
    forall p' : D, [p']q[r] -> p' ref wp q r.


Definition AdjointnessLaw :=
  forall p q r :D,
  p ref wp q r <-> p;q ref r.


Definition WP1 :=
  forall p q r : D,
  (wp q r); q ref r.

Definition WP2 :=
  forall p q r : D,
  p ref wp q (p;q).


Hint Unfold WP_definition AdjointnessLaw WP1 WP2.

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





Theorem WPAWP12 : AdjointnessLaw -> WP1 /\ WP2.
Proof.
intro AL.
autounfold.
intuition.
  apply ALWPD.
  assumption.

  apply ALWPD.
    assumption.
    auto.
Qed.


