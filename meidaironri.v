Require Import Utf8.

Goal Type.
Proof.
exact Type.
Qed.

Goal forall a,
a->a.
Proof.
intros.
assumption.
Qed.

Goal True.
Proof.
split.
Qed.

Goal forall a,
False->a.
Proof.
intros.
contradiction.
Qed.

Goal forall a:Prop,
a->a.
Proof.
intros.
assumption.
Qed.

Goal forall a b c:Prop,
(a->b)->(b->c)->a->c.
Proof.
intros.
exact(H0(H H1)).
Qed.

Goal forall a b:Prop,(a->b)->(b->a)->a<->b.
Proof.
intros.
split.
assumption.
assumption.
Qed.

Goal forall a,a<->a.
Proof.
split.
trivial.
trivial.
Qed.

Goal forall a b,a<->b->b<->a.
Proof.
intros.
destruct H.
split.
assumption.
assumption.
Qed.

Goal forall a b c,a<->b->b<->c->a<->c.
Proof.
intros.
destruct H,H0.
split.
intro.
exact(H0(H H3)).
intro.
exact(H1(H2 H3)).
Qed.

Goal forall a b,
a/\b->a.
Proof.
intros.
apply H.
Qed.

Goal forall a b,
a/\b->b.
Proof.
intros.
apply H.
Qed.

Goal forall a b,
a/\b->b/\a.
Proof.
intros.
destruct H.
split.
assumption.
assumption.
Qed.

Goal forall a b:Prop,
a->a\/b.
Proof.
intros.
left.
assumption.
Qed.

Goal forall a b:Prop,
b->a\/b.
Proof.
intros.
right.
assumption.
Qed.

Goal forall a b c:Prop,
a\/b->(a->c)->(b->c)->c.
Proof.
intros.
destruct H.
exact(H0 H).
exact(H1 H).
Qed.

Goal forall a b,
a\/b->b\/a.
Proof.
intros.
destruct H.
right.
assumption.
left.
assumption.
Qed.

Goal forall a:Prop,
a->~~a.
Proof.
intros.
intro.
exact(H0 H).
Qed.

Goal forall a,
~~~a->~a.
Proof.
intros.
intro.
apply H.
intro.
exact(H1 H0).
Qed.

Goal forall a,
~~(~~a->a).
Proof.
intros.
intro.
apply H.
intro.
exfalso.
apply H0.
intro.
apply H.
trivial.
Qed.

Goal forall a b,
a\/b->~a->b.
Proof.
intros.
destruct H.
contradiction.
assumption.
Qed.

Goal forall a b,
~a\/b->a->b.
Proof.
intros.
destruct H.
contradiction.
assumption.
Qed.

Goal forall a b:Prop,
~~((a->b)->~a\/b).
Proof.
intros.
intro.
apply H.
intro.
left.
intro.
apply H.
right.
exact(H0 H1).
Qed.

Goal forall a b,
~a\/~b->~(a/\b).
Proof.
intros.
intro.
destruct H0.
destruct H.
contradiction.
contradiction.
Qed.


Goal forall a b,
~~(~(a/\b)->~a\/~b).
Proof.
intros.
intro.
apply H.
intro.
left.
contradict H.
intro.
right.
contradict H0.
split.
assumption.
assumption.
Qed.

Goal forall a,
~~(a\/~a).
Proof.
intros.
intro.
apply H.
right.
contradict H.
left.
assumption.
Qed.

Goal forall a b:Prop,
~~(a\/(a->b)).
Proof.
intros.
intro.
apply H.
right.
intro.
contradict H.
left.
assumption.
Qed.

Goal forall a b:Prop,
(a\/(a->b)->b)->b.
Proof.
intros.
apply H.
right.
intro.
apply H.
left.
assumption.
Qed.

Goal forall a b:Prop,
~~(((a->b)->a)->a).
Proof.
intros.
intro.
apply H.
intro.
apply H0.
intro.
contradict H.
intro.
assumption.
Qed.


Goal(forall a,a\/~a)<->
forall a b c:Prop,(a->b)\/(b->c).
Proof.
split.
intros.
specialize(H b).
destruct H.
left.
trivial.
right.
intro.
contradiction.
intros.
specialize(H True a False).
destruct H.
left.
apply H.
split.
right.
assumption.
Qed.

Goal(forall a,a\/~a)<->
forall a,~~a->a.
Proof.
split.
intros.
specialize(H a).
destruct H.
assumption.
contradiction.
intros.
apply H.
intro.
apply H0.
right.
contradict H0.
left.
assumption.
Qed.

Goal(forall a,a\/~a)<->
forall a b:Prop,((a->b)->a)->a.
Proof.
split.
intros.
destruct(H a).
assumption.
apply H0.
intro.
contradiction.
intros.
specialize(H(a\/~a)(~a)).
apply H.
intro.
right.
intro.
destruct H0.
left.
assumption.
assumption.
Qed.

Goal(forall a b:Prop,((a->b)->a)->a)<->
forall a b c:Prop,(a->b)\/(b->c).
Proof.
split.
intros.
specialize(H((a->b)\/(b->c))c).
apply H.
intro.
right.
intro.
apply H0.
left.
trivial.
intros.
specialize(H True a False).
destruct H.
apply H.
split.
apply H0.
intro.
contradiction.
Qed.

Goal(forall a,~~a->a)<->
forall a b:Prop,((a->b)->a)->a.
Proof.
split.
intros.
apply H.
intro.
apply H1.
apply H0.
intro.
contradiction.
intros.
specialize(H a(~a)).
apply H.
intro.
contradict H0.
intro.
exact((H1 H0)H0).
Qed.

Goal(forall a,~~a->a)<->
forall a b c:Prop,(a->b)\/(b->c).
Proof.
split.
intros.
apply H.
intro.
apply H0.
right.
intro.
contradict H0.
left.
trivial.
intros.
specialize(H True a False).
destruct H.
apply H.
split.
contradiction.
Qed.






