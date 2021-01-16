Require Import Utf8 ssreflect ssrfun Classical.

Set Implicit Arguments.

Unset Strict Implicit.

Unset Printing Implicit Defensive.

Section a.

Variable G:Type.

Variable f:G → G → G.

Let unit(e:G):=
 ∀a:G,f e a = a ∧ f a e = a.
 
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

Section b.

Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀(a b c:U),hom a b → hom b c → hom a c.

Let is_id(id:∀{a:U},hom a a):=
 ∀(a b:U)(f:hom a b),comp id f = f ∧ comp f id = f.
 
Variable id1 id2:∀a:U,hom a a.
 
Variable H1:is_id id1.

Variable H2:is_id id2.

Goal ∀a:U,id1 a = id2 a.
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

End b.

Section c.
 
Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀(a b c:U),hom a b → hom b c → hom a c.

Let is_id(x:U)(id:hom x x):=
 ∀(a b:U)(f:hom a x)(g:hom x b),
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

End c.

Section d.

Variable G:Type.

Variable f:G → G → G.
 
Hypothesis asso:
 ∀a b c:G,f a (f b c) = f (f a b) c.
 
Variable e:G.
 
Hypothesis unit:∀a:G,f e a = a ∧ f a e = a.
 
Let inv(a b:G):=
 f a b = e ∧ f b a = e.
 
Goal ∀a b1 b2:G,
 inv a b1 ∧ inv a b2 → b1 = b2.
Proof.
intros.
destruct H.
red in H,H0.
destruct H,H0.
destruct(unit b1).
destruct(unit b2).
clear H4 H6 H2.
rewrite <-H3.
rewrite<-H5.
clear H3 H5.
rewrite<-H1.
rewrite<-asso,<-asso.
f_equal.
rewrite<-H in H0.
congruence.
Qed.

End d.

Section e.

Variable U:Type.

Variable hom:U → U → Type.

Variable comp:∀(a b c:U),hom a b → hom b c → hom a c.

Variable id:∀{a:U},hom a a.

Hypothesis ID:
 ∀(a b:U)(f:hom a b),comp id f = f ∧ comp f id = f.

Let inv(a b:U)(f:hom a b)(g:hom b a):=
 comp f g = id ∧ comp g f = id.
 
Hypothesis aso:
 ∀(a b c d:U)(f:hom a b)(g:hom b c)(h:hom c d),
  comp f (comp g h) = comp (comp f g) h.  

Variable a b:U.

Variable f:hom a b.

Variable g1 g2:hom b a.

Goal inv f g1 → inv f g2 → g1 = g2.
Proof.
intros.
red in H,H0.
destruct H,H0.
clear inv.
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

End e.
