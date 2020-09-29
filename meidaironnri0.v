Require Import Utf8 PropExtensionality.

Section a.

Variable a b c:Prop.

Goal True.
Proof.
clear a b c.
exact I.
Qed.

Goal False->a.
Proof.
clear b c.
intro.
exfalso.
clear a.
assumption.
Qed.

Goal a->a.
Proof.
clear b c.
intro.
assumption.
Qed.

Goal(a->b)->(b->a)->a<->b.
Proof.
clear c.
intros.
split.
clear H0.
assumption.
clear H.
assumption.
Qed.

Goal(a->b)->(b->c)->a->c.
Proof.
intros.
apply H0.
clear H0 c.
apply H.
clear H b.
assumption.
Qed.

Goal a/\b->a.
Proof.
clear c.
intro.
destruct H.
clear H0 b.
assumption.
Qed.

Goal a/\b->b.
Proof.
clear c.
intro.
destruct H.
clear H a.
assumption.
Qed.

Goal a/\b->b/\a.
Proof.
clear c.
intro.
destruct H.
split.
clear H a.
assumption.
clear b H0.
assumption.
Qed.

Goal a->a\/b.
Proof.
clear c.
intro.
left.
clear b.
assumption.
Qed.

Goal b->a\/b.
Proof.
clear c.
intro.
right.
clear a.
assumption.
Qed.

Goal a\/b->b\/a.
Proof.
clear c.
intro.
destruct H.
right.
clear b.
assumption.
left.
clear a.
assumption.
Qed.

Goal a\/b->(a->c)->(b->c)->c.
Proof.
intros.
destruct H.
clear H1 b.
apply H0.
all:clear H0.
clear c.
assumption.
clear a.
apply H1.
clear H1 c.
assumption.
Qed.

Goal a->~~a.
Proof.
clear b c.
intro.
intro.
specialize(H0 H).
clear H a.
assumption.
Qed.

Goal ~~~a->~a.
Proof.
clear b c.
intro.
intro.
apply H.
clear H.
intro.
specialize(H H0).
clear H0 a.
assumption.
Qed.

Goal a<->a.
Proof.
clear b c.
split.
intro.
assumption.
intro.
assumption.
Qed.

Goal a<->b->b<->a.
Proof.
clear c.
intro.
destruct H.
split.
clear H.
intro.
apply H0.
all:clear H0.
clear a.
assumption.
intro.
apply H.
clear H b.
assumption.
Qed.

Goal a<->b->b<->c->a<->c.
Proof.
intros.
destruct H,H0.
split.
clear H1 H2.
intro.
apply H0.
all:clear H0.
clear c.
apply H.
all:clear H.
clear b.
assumption.
intro.
apply H1.
clear H1 a.
apply H2.
clear H2 b.
assumption.
Qed.

Goal~(a\/b)<->~a/\~b.
Proof.
clear c.
split.
intro.
split.
intro.
apply H.
left.
assumption.
intro.
apply H.
right.
assumption.
intro.
intro.
destruct H.
destruct H0.
apply H.
assumption.
contradiction.
Qed.

Goal~a\/~b->~(a/\b).
Proof.
clear c.
intro.
intro.
destruct H0.
destruct H.
apply H.
assumption.
apply H.
assumption.
Qed.

Goal~~(~(a/\b)->~a\/~b).
Proof.
clear c.
intro.
apply H.
intro.
clear H0.
left.
intro.
apply H.
clear H.
intro.
right.
intro.
apply H.
clear H.
split.
assumption.
assumption.
Qed.

Goal a/\b->~(~a\/~b).
Proof.
clear c.
intro.
intro.
destruct H.
destruct H0.
contradiction.
contradiction.
Qed.

Goal~~(~(~a\/~b)->a/\b).
Proof.
clear c.
intro.
apply H.
intro.
exfalso.
apply H0.
left.
intro.
apply H0.
right.
intro.
clear H0.
apply H.
intro.
split.
assumption.
assumption.
Qed.

Goal a\/b->~(~a/\~b).
Proof.
clear c.
intro.
intro.
destruct H0.
destruct H.
contradiction.
contradiction.
Qed.

Goal~~(~(~a/\~b)->a\/b).
Proof.
clear c.
intro.
apply H.
intro.
exfalso.
apply H0.
split.
intro.
apply H.
intro.
left.
assumption.
intro.
apply H.
intro.
right.
assumption.
Qed.

Goal~~(a\/~a).
Proof.
clear b c.
intro.
apply H.
right.
intro.
apply H.
clear H.
left.
assumption.
Qed.

Goal~~(~~a->a).
Proof.
clear b c.
intro.
apply H.
intro.
exfalso.
apply H0.
clear H0.
intro.
apply H.
clear H.
intro.
clear H.
assumption.
Qed.

Goal~~((a->b)\/(b->a)).
Proof.
clear c.
intro.
apply H.
left.
intro.
exfalso.
apply H.
clear H.
right.
intro.
clear H b.
assumption.
Qed.

Goal~~((a->b)\/(b->c)).
Proof.
intro.
apply H.
right.
intro.
exfalso.
apply H.
clear H.
left.
intro.
clear a c H.
assumption.
Qed.

Goal~~(((a->b)->a)->a).
Proof.
clear c.
intro.
apply H.
intro.
apply H0.
clear H0.
intro.
exfalso.
apply H.
clear H.
intro.
clear H b.
assumption.
Qed.

Goal~~((a->b)->~a\/b).
Proof.
clear c.
intro.
apply H.
intro.
clear H0.
left.
intro.
apply H.
clear H.
intro.
right.
apply H.
clear H b.
assumption.
Qed.

Goal~~(a\/(a->b)).
Proof.
clear c.
intro.
apply H.
right.
intro.
exfalso.
apply H.
clear H.
left.
clear b.
assumption.
Qed.

Goal~~((~a->~b)->b->a).
Proof.
clear c.
intro.
apply H.
intros.
contradict H1.
apply H0.
clear H0.
intro.
apply H.
clear H.
intros.
clear b H H1.
assumption.
Qed.

End a.

Definition A:=forall a:Prop,a\/~a.

Definition B:=forall a:Prop,~~a->a.

Definition C:=forall a b:Prop,(a->b)\/(b->a).

Definition D:=forall a b c:Prop,(a->b)\/(b->c).

Goal A=B.
Proof.
apply propositional_extensionality.
split.
intro.
unfold B.
intros.
unfold A in H.
specialize(H a).
destruct H.
clear H0.
assumption.
specialize(H0 H).
clear H.
exfalso.
clear a.
assumption.
intro.
unfold A.
intro.
unfold B in H.
apply H.
clear H.
intro.
apply H.
right.
intro.
apply H.
clear H.
left.
assumption.
Qed.

Goal B=D.
Proof.
apply propositional_extensionality.
unfold B,D.
split.
intros.
apply H.
intro.
apply H0.
right.
intro.
contradict H0.
left.
intro.
assumption.
intros.
specialize(H(True)(a)(False)).
destruct H.
apply H.
exact I.
contradiction.
Qed.


Goal B=C.
Proof.
apply propositional_extensionality.
unfold B,C.
split.
intros.
apply H.
clear H.
intro.
apply H.
left.
intro.
exfalso.
apply H.
right.
intro.
assumption.
intros.
specialize(H(a)(False)).
tauto.


Goal A=C.
Proof.
apply propositional_extensionality.
split.
intro.
unfold C.
intros.
unfold A in H.
specialize(H a).
destruct H.
right.
intro.
clear H0 b.
assumption.
left.
intro.
specialize(H H0).
contradiction.
unfold C,A.
intros.
specialize(H (~a) (False)).
tauto.

Section a.

Variable A:forall a,a\/~a.

Goal ~~a->a.
Proof.
clear b c.
intro.
specialize(A a).
destruct A.
all:clear A.
clear H.
assumption.
specialize(H H0).
clear H0.
exfalso.
clear a.
assumption.
Qed.

Goal(a->b)\/(b->a).
Proof.
clear c.
specialize(








