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

Theorem WP12WPA : WP1 /\ WP2 -> AdjointnessLaw.
Proof.
intuition.
autounfold.
intuition.
eauto.
apply Transitivity with (wp q (p; q)).
intuition.

admit. (* TODO!!!!!!!!!!!! *)
Qed.


Theorem WPMon : 
  WP_definition ->
  forall q q' r r' : D,
  q' ref q -> r ref r' -> wp q r ref wp q' r'.
Proof.
intro WPD.
intuition.
apply WPDAL.
assumption.
apply Transitivity with (r).
intuition.
apply Transitivity with (wp q r; q).
intuition.
apply WPD.
Qed.


Theorem StepWiseWP :
  AssociativityLaw ->
  WP_definition ->
  forall q q' r : D,
  wp q (wp q' r) ref wp (q; q') r.
Proof.
intro Assoc.
intro WPD.
intuition.
assert (wp1:WP1).
  apply WPAWP12.
  apply WPDAL.
  assumption.
apply WPD.
autounfold.
rewrite <- Assoc.
apply Transitivity with ((wp q' r); q').
auto.
Qed.


Theorem WP_Seq :
  AssociativityLaw ->
  WP_definition ->
  forall q r s : D,
  wp q r ref wp (q;s) (r;s).
Proof.
intro Assoc.
intro WPD.
intuition.
apply WPDAL.
assumption.
rewrite <- Assoc.
apply Monotonicity.
  apply WPD.
  trivial.
Qed.
