Require Import Utf8 Classical.

Example hansya U R:=
forall a:U,R a a:Prop.

Example hihansya U R:=
forall a:U,~R a a:Prop.

Example taisyo U R:=
forall a b:U,R a b->R b a.

Example hantaisyo U R:=
forall a b:U,R a b->R b a->a=b:Prop.

Example sui U(R:U->U->Prop):=
forall a b c,R a b->R b c->R a c.

Example hikakukano U R:=
forall a b:U,R a b\/R b a:Prop.

Example hitaisyo U(R:U->U->Prop):=
forall a b,R a b->~R b a.

Goal forall U(R1 R2:U->U->Prop),
hantaisyo U R1->
(forall a b,R2 a b->R1 a b/\a<>b)->
hitaisyo U R2.
Proof.
intros.
unfold hitaisyo.
intros.
intro.
assert(H3:=H0 a b).
specialize(H0 b a).
specialize(H0 H2).
clear H2.
specialize(H3 H1).
clear H1 R2.
destruct H0,H3.
apply H3.
clear H1 H3.
unfold hantaisyo in H.
specialize(H a b).
specialize(H H2 H0).
clear R1 H0 H2.
case H.
clear b H.
reflexivity.
Qed.

Goal forall U(R1 R2:U->U->Prop),
sui U R1->
hantaisyo U R1->
(forall a b,R2 a b<->R1 a b/\a<>b)->
sui U R2.
Proof.
intros.
unfold sui.
intros.
assert(H4:=H1 a b).
assert(H5:=H1 b c).
specialize(H1 a c).
destruct H1,H4,H5.
clear H1 H7 H8.
apply H6.
clear H6.
specialize(H4 H2).
clear H2.
specialize(H5 H3).
clear H3 R2.
destruct H4,H5.
clear H2.
unfold sui in H.
specialize(H a b c).
specialize(H H1 H3).
unfold hantaisyo in H0.
specialize(H0 a b).
split.
clear b H0 H1 H3 H4.
assumption.
clear H.
intro.
apply H4.
clear H4.
subst.
specialize(H0 H1 H3).
clear R1 H1 H3.
case H0.
clear b H0.
reflexivity.
Qed.

Goal forall U(R1 R2:U->U->Prop),
(forall a b,R2 a b->R1 a b/\a<>b)->
hihansya U R2.
Proof.
intros.
unfold hihansya.
intros.
intro.
specialize(H a a).
specialize(H H0).
clear H0 R2.
destruct H.
clear R1 H.
apply H0.
clear H0.
reflexivity.
Qed.

Goal forall U(R1 R2:U->U->Prop),
(forall a b,R1 a b\/a=b->R2 a b)->
hansya U R2.
Proof.
intros.
unfold hansya.
intro.
specialize(H a a).
apply H.
clear R2 H.
right.
clear R1.
reflexivity.
Qed.

Goal forall U(R1 R2:U->U->Prop),
hitaisyo U R1->
(forall a b,R2 a b->R1 a b\/a=b)->
hantaisyo U R2.
Proof.
intros.
unfold hantaisyo.
intros.
assert(H3:=H0 a b).
specialize(H0 b a).
specialize(H0 H2).
clear H2.
specialize(H3 H1).
clear H1 R2.
destruct H0.
destruct H3.
unfold hitaisyo in H.
specialize(H a b).
apply H in H1.
all:clear H.
specialize(H1 H0).
clear H0 R1.
exfalso.
clear U a b.
assumption.
clear R1 H0.
case H1.
clear b H1.
reflexivity.
clear R1 H3.
case H0.
clear a H0.
reflexivity.
Qed.

Goal forall U(R1 R2:U->U->Prop),
sui U R1->
(forall a b,R2 a b<->R1 a b\/a=b)->
sui U R2.
Proof.
intros.
unfold sui.
intros.
assert(H3:=H0 a b).
assert(H4:=H0 b c).
specialize(H0 a c).
destruct H0,H3,H4.
clear H0 H6 H7.
specialize(H3 H1).
clear H1.
specialize(H4 H2).
clear H2.
apply H5.
clear H5 R2.
unfold sui in H.
specialize(H a b c).
destruct H3.
destruct H4.
specialize(H H0 H1).
clear H0 H1 b.
left.
assumption.
all:clear H.
subst.
left.
assumption.
destruct H4.
subst.
left.
assumption.
right.
clear R1.
subst.
reflexivity.
Qed.

Goal forall U R,
sui U R->
hihansya U R->
hitaisyo U R.
Proof.
intros.
unfold hitaisyo.
intros.
intro.
unfold sui in H.
specialize(H a b a).
specialize(H H1 H2).
clear H1 H2 b.
unfold hihansya in H0.
specialize(H0 a).
specialize(H0 H).
clear U R a H.
assumption.
Qed.

Goal forall U R,
hitaisyo U R->
hihansya U R.
Proof.
intros.
unfold hihansya.
intro.
intro.
unfold hitaisyo in H.
specialize(H a a).
specialize(H H0).
specialize(H H0).
clear U R a H0.
assumption.
Qed.

Goal forall U R,
sui U R->
taisyo U R->
(forall a,exists b,R a b)->
hansya U R.
Proof.
intros.
unfold hansya.
intro.
specialize(H0 a).
destruct H0.
unfold sui in H.
unfold taisyo in X.
specialize(X a x).
specialize(X H0).
specialize(H a x a).
specialize(H H0 X).
clear x X H0.
assumption.
Qed.

Goal forall U(R1 R2:U->U->Prop),
(forall a b,R1 a b->R2 a b\/a=b)<->
forall a b,R1 a b/\a<>b->R2 a b.
Proof.
intros.
split.
intros.
destruct H0.
specialize(H a b).
specialize(H H0).
clear H0 R1.
destruct H.
clear H1.
assumption.
exfalso.
specialize(H1 H).
clear H a b R2 U.
assumption.
intros.
specialize(H a b).
assert(a=b\/a<>b).
apply classic.
destruct H1.
right.
clear H0 H R1 R2.
case H1.
clear H1 b.
reflexivity.
left.
apply H.
clear H R2.
split.
clear H1.
assumption.
intro.
specialize(H1 H).
clear H H0 a b R1 U.
assumption.
Qed.

Goal forall U R,
hikakukano U R->
hansya U R.
Proof.
intros.
unfold hansya.
intro.
unfold hikakukano in H.
specialize(H a a).
destruct H.
assumption.
assumption.
Qed.

Example saidaigen U(R:U->U->Prop)a:=
forall x,R x a.

Goal forall U(R:U->U->Prop)a b,
hantaisyo U R->
saidaigen U R a->
saidaigen U R b->
a=b.
Proof.
intros.
unfold hantaisyo in H.
specialize(H a b).
unfold saidaigen in H0.
unfold saidaigen in H1.
specialize(H0 b).
specialize(H1 a).
specialize(H H1 H0).
clear H0 H1 R.
case H.
clear b H.
reflexivity.
Qed.

Example saisyogen U(R:U->U->Prop)a:=
forall x,R a x.

Goal forall U(R:U->U->Prop)a b,
hantaisyo U R->
saisyogen U R a->
saisyogen U R b->
a=b.
Proof.
intros.
unfold hantaisyo in H.
specialize(H a b).
unfold saisyogen in H0.
unfold saisyogen in H1.
specialize(H0 b).
specialize(H1 a).
specialize(H H0 H1).
clear H0 H1 R.
case H.
clear b H.
reflexivity.
Qed.

Example kyokudaigen U(R:U->U->Prop)a:=
forall x,R a x->a=x.

Goal forall U(R:U->U->Prop)a,
hantaisyo U R->
saidaigen U R a->
kyokudaigen U R a.
Proof.
intros.
unfold kyokudaigen.
intros.
unfold saidaigen in H0.
specialize(H0 x).
unfold hantaisyo in H.
specialize(H a x).
specialize(H H1 H0).
case H.
clear R x H0 H1 H.
reflexivity.
Qed.

Example kyokusyogen U(R:U->U->Prop)a:=
forall x,R x a->x=a.

Goal forall U(R:U->U->Prop)a,
hantaisyo U R->
saisyogen U R a->
kyokusyogen U R a.
Proof.
intros.
unfold kyokusyogen.
intros.
unfold saisyogen in H0.
specialize(H0 x).
unfold hantaisyo in H.
specialize(H x a).
specialize(H H1 H0).
case H.
clear R a H0 H1 H.
reflexivity.
Qed.

Goal forall U(R:U->U->Prop)a b,
saidaigen U R a->
kyokudaigen U R b->
a=b.
Proof.
intros.
unfold saidaigen in H.
specialize(H b).
unfold kyokudaigen in H0.
specialize(H0 a).
specialize(H0 H).
case H0.
clear a H H0 R.
reflexivity.
Qed.

Goal forall U(R:U->U->Prop)a b,
saisyogen U R a->
kyokusyogen U R b->
a=b.
Proof.
intros.
unfold saisyogen in H.
specialize(H b).
unfold kyokusyogen in H0.
specialize(H0 a).
specialize(H0 H).
case H0.
clear b H H0 R.
reflexivity.
Qed.

Goal forall U(R:U->U->Prop),
hikakukano U R->
forall a,
kyokudaigen U R a->
saidaigen U R a.
Proof.
intros.
unfold saidaigen.
intro.
unfold kyokudaigen in H0.
specialize(H0 x).
unfold hikakukano in H.
specialize(H a x).
destruct H.
specialize(H0 H).
subst.
assumption.
clear H0.
assumption.
Qed.

Goal forall U(R:U->U->Prop),
hikakukano U R->
forall a,
kyokusyogen U R a->
saisyogen U R a.
Proof.
intros.
unfold saisyogen.
intro.
unfold kyokusyogen in H0.
specialize(H0 x).
unfold hikakukano in H.
specialize(H a x).
destruct H.
clear H0.
assumption.
specialize(H0 H).
subst.
assumption.
Qed.