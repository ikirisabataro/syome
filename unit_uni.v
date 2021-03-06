Require Import Utf8 ssreflect ssrfun Classical FinFun Bool.

Set Implicit Arguments.

Unset Strict Implicit.

Unset Printing Implicit Defensive.

Module a. 

Section a.

Variable G:Type.

Variable f:G → G → G.

Definition unit e:=
 ∀a,f e a = a ∧ f a e = a.
 
Variable e1 e2:G.

Goal unit e1 ∧ unit e2 → e1 = e2.
Proof.
intro.
destruct H.
red in H,H0.
specialize(H e2).
specialize(H0 e1).
destruct H,H0.
clear H1 H0.
congruence.
Qed.

End a.

End a.

Module l. 

Section a.

Variable U:Type.

Variable f:U → U → U.

Variable e1 e2:U.

Hypothesis left:∀a,f e1 a = a.

Hypothesis right:∀a,f a e2 = a.

Goal e1 = e2.
Proof.
specialize(left e2).
specialize(right e1).
congruence.
Qed.

End a.

End l.

Module d.

Section a.

Variable G:Type.

Variable f:G → G → G.
 
Hypothesis aso:
 ∀a b c,f a (f b c) = f (f a b) c.
 
Variable e:G.
 
Hypothesis unit:∀a,f e a = a ∧ f a e = a.
 
Definition inv a b:=
 f a b = e ∧ f b a = e.
 
Goal ∀a b1 b2,
 inv a b1 ∧ inv a b2 → b1 = b2.
Proof.
intros.
destruct H.
red in H,H0.
destruct H,H0.
destruct(unit b1).
destruct(unit b2).
clear H4 H6 H2 unit.
rewrite <-H3.
rewrite<-H5.
clear H3 H5.
rewrite<-H1.
rewrite<-aso,<-aso.
f_equal.
rewrite<-H in H0.
congruence.
Qed.

End a.

End d.

Module g.

Section a.

Variable G:Type.

Variable f:G → G → G.
 
Hypothesis aso:
 ∀a b c,f a (f b c) = f (f a b) c.

Definition epi a:=∀b c,f a b = f a c → b = c.

Goal ∀x y,epi x → epi y → epi(f x y).
Proof.
intros.
red.
intros.
red in H,H0.
apply H0.
apply H.
repeat rewrite aso.
apply H1.
Qed.

End a.

End g.

Module k.
 
Section a.

Variable U:Type.

Variable f :U → U → U.

Definition op (f:U → U → U) a b := f b a.

Goal op(op f) = f.
Proof.
unfold op at 2.
unfold op.
split.
Qed.

End a.

End k.

Module j.
 
Section a.

Variable U:Type.

Definition aso f:=
 ∀a b c:U,f a (f b c) = f (f a b) c.

Definition op (f:U → U → U) a b := f b a.

Variable f:U → U → U.

Goal aso f → aso(op f).
Proof.
intro.
red.
intros.
cbv.
red in H.
rewrite H.
split.
Qed.

End a.

End j.

Module n.
 
Section a.

Variable U:Type.

Definition op (f:U → U → U) a b := f b a.

Definition left f (e:U) :=
 ∀a:U,f e a = a.
 
Definition right f (e:U) :=
 ∀a:U,f a e = a.
 
Variable f:U → U → U.

Goal left (op f) = right f.
Proof.
cbv.
split.
Qed.

End a.

End n.

Module b.

Section a.

Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Definition is_id(id:∀{a},hom a a):=
 ∀a b (f:hom a b),comp id f = f ∧ comp f id = f.
 
Variable id1 id2:∀a,hom a a.
 
Hypothesis H1:is_id id1.

Hypothesis H2:is_id id2.

Goal ∀a,id1 a = id2 a.
Proof.
intro.
red in H1 ,H2.
specialize(H1 (id2 a)).
destruct H1.
specialize(H2(id1 a)).
destruct H2.
clear H1 H2.
rewrite H in H4.
auto.
Qed.

End a.

End b.

Module c.

Section a.
 
Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Definition is_id x id:=
 ∀ a b (f:hom a x)(g:hom x b),
  comp f id = f ∧ comp id g = g.
 
Variable a:U.
 
Variable id1 id2:hom a a.
 
Hypothesis H1:is_id id1.

Hypothesis H2:is_id id2.

Goal id1 = id2.
Proof.
red in H1,H2.
specialize(H1 id2 id2).
specialize(H2 id1 id1).
destruct H1,H2.
clear H1 H2 H H4.
congruence.
Qed.

End a.

End c.

Module e.

Section a.

Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Variable id:∀{a},hom a a.

Hypothesis ID:
 ∀a b (f:hom a b),comp id f = f ∧ comp f id = f.

Definition inv a b (f:hom a b)(g:hom b a):=
 comp f g = id ∧ comp g f = id.
 
Hypothesis aso:
 ∀a b c d (f:hom a b)(g:hom b c)(h:hom c d),
  comp f (comp g h) = comp (comp f g) h.  

Variable a b:U.

Variable f:hom a b.

Variable g1 g2:hom b a.

Goal inv f g1 → inv f g2 → g1 = g2.
Proof.
intros.
red in H,H0.
destruct H,H0.
destruct(ID g1),(ID g2).
clear ID.
rewrite<-H3.
rewrite <-H5.
clear H3 H5 H4 H6.
rewrite<-H1.
repeat rewrite <-aso.
rewrite H H0.
reflexivity.
Qed.

End a.

End e.

Goal ∀(A B C D:Type)(f:A → B)(g:B → C)(h:C → D),
 f\;g\;h = (f\;g)\;h.
Proof.
intros.
cbv.
split.
Qed.

Goal ∀(A B C:Type)(f:A → B)(g:B → C),
 Injective f → Injective g → Injective(f\;g).
Proof.
intros.
red.
intros.
red in H,H0.
cbv in H1.
eapply H.
eapply H0.
auto.
Qed.

Goal ∀(A B C:Type)(f:A → B)(g:B → C),
 Surjective f → Surjective g → Surjective(f\;g).
Proof.
intros.
red.
intro.
red in H,H0.
cbv.
specialize(H0 y).
destruct H0.
destruct(H x).
exists x0.
rewrite H1.
auto.
Qed.

Goal ∀(A B C:Type)(f:A → B)(g:B → C),
 Injective(f\;g) → Injective f.
Proof.
intros.
red.
intros.
red in H.
cbv in H.
apply H.
f_equal.
auto.
Qed.

Goal ∀(A B C:Type)(f:A → B)(g:B → C),
 Surjective(f\;g) → Surjective g.
Proof.
intros.
red.
intros.
red in H.
cbv in H.
destruct(H y).
exists (f x).
auto.
Qed.

Module f.

Section a.

Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Hypothesis aso:
 ∀a b c d (f:hom a b)(g:hom b c)(h:hom c d),
  comp f (comp g h) = comp (comp f g) h.
  
Definition mono a b (f:hom a b):=
 ∀c (g h:hom c a),comp g f = comp h f → g = h.
  
Goal ∀a b c (f:hom a b)(g:hom b c),
 mono f → mono g → mono(comp f g).
Proof.
intros.
red.
intros.
rename g0 into h1,h into h2,c0 into x.
red in H,H0.
specialize(H x h1 h2).
specialize(H0 x (comp h1 f)(comp h2 f)).
apply H.
apply H0.
clear H H0.
congruence.
Qed.

Goal ∀a b c (f:hom a b)(g:hom b c),
 mono(comp f g) → mono f.
Proof.
intros.
red.
intros.
rename g0 into h1,h into h2.
red in H.
specialize(H c0 h1 h2).
apply H.
repeat rewrite aso.
rewrite H0.
split.
Qed.

End a.

End f.

Module i.
 
Section a.

Variable U:Type.

Variable f :U → U → U.

Definition op (f:U → U → U) a b := f b a.

Definition mono(f:U → U → U) a:=
 ∀b c,f b a = f c a → b = c.

Definition epi(f:U → U → U) a:=
 ∀b c,f a b = f a c → b = c.
 
Goal mono (op f) = epi f.
Proof.
cbv.
split.
Qed. 

End a.

End i.

Module m.

Section a.

Variable U:Type.

Variable R:U → U → Prop.

Definition op(R:U → U → Prop)(a b:U):=R b a.

Definition tran(R:U → U → Prop):=
 ∀a b c,R a b → R b c → R a c.
 
Goal tran R → tran(op R).
Proof.
intro.
red.
intros.
red.
red in H0,H1.
red in H.
eapply H.
apply H1.
apply H0.
Qed.

End a.

End m.

Module o.

Section a.

Variable U:Type.

Variable e:U.

Variable f:U → U → U.

Definition inv f (a b:U) :=
 f a b = e ∧ f b a = e.
 
Variable a b:U.

Definition op (f:U → U → U) a b := f b a.

Goal inv f a b → inv (op f) a b.
Proof.
cbv.
intro.
tauto.
Qed.

End a.

End o. 

Module p.

Section a.
 
Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Variable op:∀a b,hom a b → hom b a.

Definition Op (comp:∀{a b c},hom a b → hom b c → hom a c)
 a b c (f:hom a b) (g:hom b c) := op(comp(op g)(op f)).
 
Hypothesis H1:∀a b (f:hom a b),op(op f) = f.

Goal ∀a b c (f:hom a b) (g:hom b c),
 Op(Op comp) f g = comp f g.
Proof.
intros.
cbv.
repeat rewrite H1.
split.
Qed.

End a.

End p.

Module q.

Section a.
 
Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Variable op:∀a b,hom a b → hom b a.

Definition Op (comp:∀{a b c},hom a b → hom b c → hom a c)
 a b c (f:hom a b) (g:hom b c) := op(comp(op g)(op f)).
 
Hypothesis H1:∀a b (f:hom a b),op(op f) = f.

Definition aso(comp:∀{a b c},hom a b → hom b c → hom a c):=
 ∀a b c d (f:hom a b)(g:hom b c)(h:hom c d),
  comp f (comp g h) = comp (comp f g) h.
  
Goal aso comp → aso(Op comp).
Proof.
intro.
red.
intros.
cbv.
repeat rewrite H1.
red in H.
f_equal.
rewrite H.
split.
Qed.

End a.

End q.

Module r.

Section a.
 
Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀a b c,hom a b → hom b c → hom a c.

Variable op:∀a b,hom a b → hom b a.

Definition Op (comp:∀{a b c},hom a b → hom b c → hom a c)
 a b c (f:hom a b) (g:hom b c) := op(comp(op g)(op f)).
 
Hypothesis H1:∀a b (f:hom a b),op(op f) = f.

Goal ∀a b c(f:hom a b)(g:hom b c),
 Op comp(op g)(op f) = op(comp f g).
Proof.
intros.
cbv.
repeat rewrite H1.
split.
Qed.

End a.

End r.

Module s.

Section a.

Definition hom A B (fa:A → A → A) (fb:B → B → B) F :=
 ∀a1 a2,F(fa a1 a2) = fb(F a1)(F a2).
 
Variable A B C:Type.
 
Variable fa:A → A → A.

Variable fb:B → B → B.

Variable fc:C → C → C.

Variable F1:A → B.

Variable F2:B → C.

Goal hom fa fb F1 → hom fb fc F2 → hom fa fc (F1\;F2).
Proof.
intros.
red.
intros.
cbv.
red in H,H0.
specialize(H a1 a2).
specialize(H0(F1 a1)(F1 a2)).
rewrite <-H0.
rewrite <- H.
split.
Qed.

End a.

End s.

Module t.

Section a.

Definition unit(U:Type)(f:U → U → U)(e:U):=
 ∀a:U,f e a = a ∧ f a e = a.
 
Definition hom(A B:Type)(fa:A → A → A)(fb:B → B → B)(F:A → B):=
 ∀e:A,unit fa e → unit fb (F e).

Variable A B C:Type.
 
Variable fa:A → A → A.

Variable fb:B → B → B.

Variable fc:C → C → C.

Variable F1:A → B.

Variable F2:B → C.

Goal hom fa fb F1 → hom fb fc F2 → hom fa fc (F1\;F2).
Proof.
intros.
red.
intros.
red.
intros.
cbv.
red in H,H0,H1.
cbv in H,H0.
specialize(H e).
specialize(H H1).
specialize(H0 (F1 e)).
specialize(H0 H).
apply H0.
Qed.

End a.

End t.

Module u.

Section a.

Definition left(U1 U2:Type)(f:U1 → U2 → U2)(e:U1):=
 ∀a:U2,f e a = a.
 
Definition hom(A1 A2 B1 B2:Type)(fa:A1 → A2 → A2)
(fb:B1 → B2 → B2)
 (F:A1 → B1):=
  ∀e:A1,left fa e → left fb (F e).

Variable A1 A2 B1 B2 C1 C2:Type.
 
Variable fa:A1 → A2 → A2.

Variable fb:B1 → B2 → B2.

Variable fc:C1 → C2 → C2.

Variable F1:A1 → B1.

Variable F2:B1 → C1.

Goal hom fa fb F1 → hom fb fc F2 → hom fa fc (F1\;F2).
Proof.
intros.
red.
intros.
red.
intros.
cbv.
red in H,H0,H1.
cbv in H,H0.
specialize(H e).
specialize(H H1).
specialize(H0 (F1 e)).
specialize(H0 H).
apply H0.
Qed.

End a.

End u.

Goal ∀n:nat,0+n = n.
Proof.
intro.
simpl.
split.
Qed.

Goal ∀n:nat,n+0 = n.
Proof.
intro.
induction n.
simpl.
split.
simpl.
rewrite IHn.
split.
Qed.

Goal ∀n:nat,1*n = n.
Proof.
intro.
simpl.
auto.
Qed.

Goal ∀n:nat,n*1 = n.
Proof.
intro.
induction n.
simpl.
split.
simpl.
rewrite IHn.
split.
Qed.

Goal ∀a b c:nat,a+b+c = a+(b+c).
Proof.
intros.
induction a.
simpl.
split.
simpl.
rewrite IHa.
split.
Qed.

Goal ∀a:bool,false||a = a.
Proof.
intro.
simpl.
split.
Qed.

Goal ∀a:bool,a||false = a.
Proof.
intro.
destruct a.
simpl.
split.
simpl.
split.
Qed.

Module v.

Section a.

Variable U:Type.

Variable R:U → U → Prop.

Hypothesis antsym:∀x y:U,R x y → R y x → x = y.

Definition min(x:U):=∀a:U,R x a.

Variable x1 x2:U.

Goal min x1 → min x2 → x1 = x2.
Proof.
intros.
red in H,H0.
specialize(H x2).
specialize(H0 x1).
specialize(antsym H H0).
apply antsym.
Qed.

End a.

End v.

Module w.

Section a.

Variable U:Type.

Definition op(R:U → U → Prop)(a b:U):=R b a.

Definition min(R:U → U → Prop)(x:U):=
 ∀a:U,R x a.
 
Definition max(R:U → U → Prop)(x:U):=
 ∀a:U,R a x.
 
Variable R:U → U → Prop.

Variable x:U.

Goal min R x → max (op R) x.
Proof.
intro.
red.
intro.
red.
red in H.
apply H.
Qed.

End a.

End w.

Module x.

Section a.

Variable U1 U2:Type.

Definition op(R:U1 → U2 → Prop)(a:U2)(b:U1):=R b a.

Definition min(R:U → U → Prop)(x:U):=
 ∀a:U,R x a.
 
Definition max(R:U → U → Prop)(x:U):=
 ∀a:U,R a x.
 
Variable R:U → U → Prop.

Variable x:U.

Goal min R x → max (op R) x.
Proof.
intro.
red.
intro.
red.
red in H.
apply H.
Qed.

End a.

End w.

