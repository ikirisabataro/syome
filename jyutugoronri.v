Require Import Utf8 Classical.

Goal forall U(P:U->Prop)t,
all P->P t.
Proof.
intros.
specialize(H t).
assumption.
Qed.

Goal forall U(P:U->Prop)t,
P t->ex P.
Proof.
intros.
exists t.
assumption.
Qed.

Goal forall U(P:U->Prop),
(forall x,P x)->forall y,P y.
Proof.
intros.
specialize(H y).
assumption.
Qed.

Goal forall U(P:U->Prop),
(exists x,P x)->exists y,P y.
Proof.
intros.
destruct H.
exists x.
assumption.
Qed.

Goal forall U(P:U->Prop),
~ex P<->forall x,~P x.
Proof.
intros.
split.
intros.
intro.
apply H.
clear H.
exists x.
assumption.
intro.
intro.
destruct H0.
specialize(H x).
apply H.
assumption.
Qed.

Goal forall U(P:U->Prop),
(exists x,~P x)->~all P.
Proof.
intros.
intro.
destruct H.
apply H.
clear H.
unfold all in H0.
specialize(H0 x).
assumption.
Qed.

Goal forall U(P:U->Prop),
~all P->exists x,~P x.
Proof.
intros.
apply NNPP.
intro.
apply H.
clear H.
intro.
apply NNPP.
intro.
apply H0.
clear H0.
exists x.
assumption.
Qed.

Goal forall U(P Q:U->Prop),
all P/\all Q<->forall x,P x/\Q x.
Proof.
intros.
split.
intros.
destruct H.
specialize(H x).
specialize(H0 x).
split.
assumption.
assumption.
intro.
split.
intro.
specialize(H x).
destruct H.
assumption.
intro.
specialize(H x).
destruct H.
assumption.
Qed.

Goal forall U(P Q:U->Prop),
ex P\/ex Q<->exists x,P x\/Q x.
Proof.
intros.
split.
intro.
destruct H.
destruct H.
exists x.
left.
assumption.
destruct H.
exists x.
right.
assumption.
intro.
destruct H.
destruct H.
left.
exists x.
assumption.
right.
exists x.
assumption.
Qed.

Goal forall U x,
x=x:>U.
Proof.
intros.
reflexivity.
Qed.

Goal forall U(x y:U),
x=y->y=x.
Proof.
intros.
case H.
reflexivity.
Qed.

Goal forall U(x y z:U),
x=y->y=z->x=z.
Proof.
intros.
case H0.
assumption.
Qed.

Goal forall U V(f:U->V)x y,
x=y->f x=f y.
Proof.
intros.
case H.
reflexivity.
Qed.

Goal forall U(P:U->Prop)(Q:Prop),
(ex P->Q)<->forall x,P x->Q.
Proof.
intros.
split.
intros.
apply H.
clear H.
exists x.
assumption.
intros.
destruct H0.
specialize(H x).
apply(H H0).
Qed.

Goal forall U(P:U->Prop)(Q:Prop),
(exists x,P x->Q)->all P->Q.
Proof.
intros.
destruct H.
apply H.
clear H Q.
specialize(H0 x).
assumption.
Qed.

Goal forall U(P:U->Prop)(Q:Prop),
U->(all P->Q)->exists x,P x->Q.
Proof.
intros.
apply NNPP.
intro.
apply H0.
exists X.
intro.
clear X H1.
apply H.
clear H.
intro.
apply NNPP.
intro.
apply H0.
clear H0.
exists x.
intro.
contradiction.
Qed.



Goal forall U(P Q:U->Prop),
all P\/all Q<->forall x y,P x\/Q y.
Proof.
intros.
split.
intros.
destruct H.
speintros.cialize(H x).
left.
assumption.
specialize(H y).
right.
assumption.
intro.