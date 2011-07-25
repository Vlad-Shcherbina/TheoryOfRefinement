Load basics.

Variable wp : D -> D -> D.

Axiom WP_definition:
  forall q r : D,
  [wp q r]q[r] /\
    forall p' : D, [p']q[r] -> p' ref wp q r.


