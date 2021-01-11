Require Import Utf8.

Parameter G:Set.

Parameter f:G → G → G.

Definition unit(e:G):=
 ∀a:G,f e a = a ∧ f a e = a.
 
Parameter e1 e2:G.

Goal unit e1 ∧ unit e2 → e1 = e2.
Proof.
intro.
destruct H.
red in H,H0.
specialize(H e2).
specialize(H0 e1).
destruct H,H0.
rewrite<-H.
rewrite H2.
reflexivity.
Qed.