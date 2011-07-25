Load basics.

Definition LeftLocalityLaw :=
  forall s p q : D, (s | p); q ref s | (p; q).

Definition RightLocalityLaw :=
  forall s p q : D, p; (q | s) ref (p; q) | s.

Definition HoareFrameRule :=
  forall p q r s : D, [ p ] q [ r ] -> [p | s] q [r | s].

Definition MilnerFrameRule :=
  forall p q r s : D, MilnerTransition p q r ->
    MilnerTransition (p | s) q (r | s).

Theorem LLHF : LeftLocalityLaw -> HoareFrameRule.
Proof.
unfold LeftLocalityLaw, HoareFrameRule, HoareTriple.
intros.
replace (p | s) with (s | p).
assert (TMP : (s | p); q ref s | (p; q)).
apply H.
assert (T1: s|p;q ref s|r).
apply ParMonotonicity.
apply Reflexivity.
exact H0.
replace (r | s) with (s | r).
apply Transitivity with (s | p; q).
split.
exact TMP.
exact T1.
apply ParCommutativity.
apply ParCommutativity.
Qed.

Theorem RLMF : RightLocalityLaw -> MilnerFrameRule.
unfold RightLocalityLaw, MilnerFrameRule, MilnerTransition.
intros.
assert (TMP : q;(r|s) ref (q;r)|s).
apply H.
assert (T1: (q;r)|s ref p|s).
apply ParMonotonicity.
exact H0.
apply Reflexivity.
replace (r | s) with (s | r).
apply Transitivity with (q; r | s).
split.
replace (s | r) with (r | s).
exact TMP.
apply ParCommutativity.
exact T1.
apply ParCommutativity.
Proof.

Theorem HFLL : HoareFrameRule -> LeftLocalityLaw.
Proof.
unfold LeftLocalityLaw, HoareFrameRule, HoareTriple.
intros.
assert (TMP : (s|p);q ref (p;q)|s).
replace (s | p) with (p | s).
apply H.
apply Reflexivity.
apply ParCommutativity.
replace (s | p; q) with (p; q | s).
exact TMP.
apply ParCommutativity.
Qed.

Theorem MFRL : MilnerFrameRule -> RightLocalityLaw.
Proof.
unfold RightLocalityLaw, MilnerFrameRule, MilnerTransition.
intros.
assert (TMP : p;(q|s) ref (p;q)|s).
replace (s | p) with (p | s).
apply H.
apply Reflexivity.
apply ParCommutativity.
replace (s | p; q) with (p; q | s).
exact TMP.
apply ParCommutativity.
Qed.