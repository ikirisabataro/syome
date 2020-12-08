Require Import Utf8 ssreflect ssrfun.

Set Implicit Arguments.

Unset Strict Implicit.

Axiom NNPP:forall a,~~a->a.

Goal Type.
Proof.
exact Type.
Qed.

Goal Set.
Proof.
exact nat.
Qed.

Goal Prop.
Proof.
exact True.
Qed.

Definition imp a b:=a → b.

Definition ref U R:=∀x:U,R x x.

Goal ref imp.
Proof.
refine(λ(x:Type)(H:x),_).
exact H.
Qed.

Goal forall U(x:U),id x = x.
Proof.
refine(λ(U:Type)(x:U),_).
exact eq_refl.
Qed.

Definition tran U R:=∀x y z:U,R x y → R y z → R x z.

Goal tran imp.
Proof.
refine(λ(x y z:Type)(H:imp x y)(H0:imp y z)(H1:x),_:z).
exact(H0(H H1)).
Qed.

Goal tran imp.
Proof.
cbv.
refine(λ x y z:Type,_).
exact catcomp.
Qed.

Definition l_total A B R:=∀a:A,∃b:B,R a b.

Goal ∀U(R:U → U → Prop),ref R → l_total R.
Proof.
refine(λ(U:Type)(R:U → U → Prop)(H:ref R)(a:U),_).
refine(ex_intro _ a _).
exact(H a).
Qed.

Definition r_total A B R:=∀b:B,∃a:A,R a b.

Goal ∀U(R:U → U → Prop),ref R → r_total R.
Proof.
firstorder.
Qed.

Definition imp'(a b:Prop):=a → b.

Definition antsym U R:=∀x y:U,R x y → R y x → x = y.

Definition eqprop:=∀a b,a ↔ b → a = b.

Goal eqprop → antsym imp'.
Proof.
intro.
red.
intros.
red in H.
apply H.
red in H0,H1.
tauto.
Qed.

Definition em:=∀a,a∨¬a.

Definition nnpp:=∀a,¬¬a → a.

Goal em ↔ nnpp.
Proof.
split.
intro.
red.
intros.
red in H.
destruct(H a).
auto.
contradiction.
intro.
red.
intro.
red in H.
apply H.
intro.
apply H0.
right.
intro.
apply H0.
left.
auto.
Qed.

Definition pasu:=∀a b:Prop,((a → b) → a) → a.

Goal pasu ↔ nnpp.
Proof.
split.
intro.
red.
intros.
red in H.
specialize(H (a)(~a)).
apply H.
intro.
clear H.
exfalso.
apply H0.
intro.
apply H0.
apply H1.
auto.
intro.
red.
intros a b.
apply H.
intro.
apply H0.
intro.
apply H1.
intro.
apply H.
intro.
apply H0.
intro.
auto.
Qed.

Goal pasu ↔ em.
Proof.
split.
intro.
red.
intro.
red in H.
specialize(H(a\/~a)(~a)).
apply H.
intro.
right.
intro.
clear H.
destruct H0.
tauto.
auto.
intro.
red.
intros.
red in H.
specialize(H(a)).
destruct H.
auto.
apply H0.
intro.
contradiction.
Qed.

Definition total U R:=∀x y:U,R x y∨R y x.

Goal em → total imp'.
Proof.
intro.
red.
intros.
cbv.
red in H.
destruct(H x).
right.
auto.
left.
tauto.
Qed.

Goal ∀U(R:U → U → Prop),total R → ref R.
Proof.
intros.
red.
intro.
red in H.
specialize(H x x).
tauto.
Qed.

Definition iref U R:=∀x:U,R x x → False.

Goal ∀U(R:U → U → Type),U → ref R → ¬iref R.
Proof.
intros.
intro.
red in X0,H.
specialize(X0 X).
specialize(H X).
apply(H X0).
Qed.

Definition asym U R:=∀x y:U,R x y → R y x → False.

Goal ∀U(R:U → U → Type),asym R → iref R.
Proof.
intros.
red.
intros.
red in H.
specialize(H x x).
tauto.
Qed.

Goal ∀U(R:U → U → Type),asym R → antsym R.
Proof.
intros.
red.
intros.
red in H.
specialize(H x y).
tauto.
Qed.

Goal ∀U(R:U → U → Type),tran R → iref R → asym R.
Proof.
intros.
red.
intros.
red in X,H.
specialize(H x).
specialize(X x y x).
exact(H(X X0 X1)).
Qed.

Definition sym U R:=∀x y:U,R x y → R y x.

Goal ∀U(R:U → U → Prop),
 tran R → sym R → l_total R → ref R.
Proof.
intros.
red.
intro.
red in X,X0,H.
destruct(H x).
clear H.
specialize(X x x0 x).
specialize(X0 x x0).
exact(X H0(X0 H0)).
Qed.

Goal ∀U(R:U → U → Prop),
 tran R → sym R → r_total R → ref R.
Proof.
firstorder.
Qed.

Goal sym imp' → False.
Proof.
intro.
red in X.
specialize(X False True).
cbv in X.
tauto.
Qed.

Definition or a b:=a∨b.

Goal sym or.
Proof.
red.
intros.
red.
red in H.
tauto.
Qed.

Goal l_total or.
Proof.
red.
intro.
cbv.
exists True.
tauto.
Qed.

Goal ∀U(R:U → U → Prop),sym R → l_total R ↔ r_total R.
Proof.
intros.
red in X.
cbv.
split.
intros.
specialize(H b).
destruct H.
specialize(X b x).
exists x.
tauto.
firstorder.
destruct(H a).
firstorder.
Qed.

Goal ref or → False.
Proof.
intro.
red in X.
specialize(X False).
case X;auto.
Qed.

Goal ¬iref or.
Proof.
intro.
red in H.
specialize(H True).
apply H.
red.
tauto.
Qed.

Definition and a b:=a∧b.

Goal sym and.
Proof.
red.
cbv.
intros.
tauto.
Qed.

Goal ¬l_total and.
Proof.
intro.
red in H.
specialize(H False).
destruct H.
red in H.
destruct H.
auto.
Qed.

Goal tran and.
Proof.
red.
cbv.
intros.
destruct H,H0.
tauto.
Qed.

Goal eqprop → antsym and.
Proof.
cbv.
intros.
apply H.
destruct H0,H1.
split.
tauto.
tauto.
Qed.

Goal ¬iref and.
Proof.
intro.
cbv in H.
specialize(H True).
apply H.
tauto.
Qed.

Definition iff a b:=a ↔ b.

Goal ref iff.
Proof.
red.
intro.
red.
tauto.
Qed.

Goal ¬total iff.
Proof.
intro.
red in H.
unfold iff in H.
specialize(H False True).
destruct H.
destruct H.
apply H0.
split.
tauto.
Qed.

Goal tran iff.
Proof.
red.
intros.
red.
red in H,H0.
tauto.
Qed.

Goal eqprop → antsym iff.
Proof.
cbv.
intros.
apply H.
auto.
Qed.

Definition eq U x y:=x = y:>U.

Goal ∀U,ref(@eq U).
Proof.
intro.
red.
intro.
red.
split.
Qed.

Goal ¬∀U,total(@eq U).
Proof.
intro.
red in H.
cbv in H.
specialize(H Prop True False).
destruct H.
destruct H.
split.
rewrite H.
split.
Qed.

Goal ∀U,tran(@eq U).
Proof.
intro.
red.
intros.
red.
red in H,H0.
congruence.
Qed.

Goal ∀U,antsym(@eq U).
Proof.
intro.
red.
cbv.
intros.
auto.
Qed.

Definition max U R(a:U):=∀x:U,R x a.

Definition min U R(a:U):=∀x:U,R a x.

Goal max imp True.
Proof.
red.
intro.
red.
intro.
split.
Qed.

Goal min imp False.
Proof.
cbv.
intros.
case H.
Qed.

Goal max or True.
Proof.
cbv.
intro.
right.
split.
Qed.

Goal min or True.
Proof.
cbv.
intro.
left.
split.
Qed.

Goal ∀x,max and x → False.
Proof.
intros.
cbv in X.
specialize(X False).
destruct X.
auto.
Qed.

Definition uni U P:=∀ x1 x2:U,P x1 → P x2 → x1 = x2.

Goal ∀U(R:U → U → Type),antsym R → uni(max R).
Proof.
intros.
red.
intros.
red in H,X,X0.
specialize(H x1 x2).
specialize(X x2).
specialize(X0 x1).
auto.
Qed.

Goal ∀U(R:U → U → Type),antsym R → uni(min R).
Proof.
firstorder.
Qed.

Definition maximal U R(a:U):=∀x:U,R a x → a = x.

Definition minimal U R(a:U):=∀x:U,R x a → a = x.

Goal ∀U R(a:U),antsym R → max R a → maximal R a.
Proof.
intros.
red.
intros.
red in H,X.
specialize(H a x).
specialize(X x).
auto.
Qed.

Goal ∀U R(a:U),antsym R → min R a → minimal R a.
Proof.
firstorder.
Qed.

Goal ∀U R(a b:U),max R a → maximal R b → a = b.
Proof.
intros.
red in X,H.
specialize(H a).
specialize(X b).
firstorder.
Qed.

Goal ∀U R(a b:U),min R a → minimal R b → a = b.
Proof.
firstorder.
Qed.

Goal ∀U R(a:U),total R → maximal R a → max R a.
Proof.
intros.
red.
intro.
red in H,H0.
specialize(H a x).
destruct H.
specialize(H0 x).
specialize(H0 H).
subst.
auto.
auto.
Qed.

Goal ∀U R(a:U),total R → minimal R a → min R a.
Proof.
cbv.
firstorder.
case(H a x).
auto.
firstorder.
specialize(H0 x H1).
subst.
auto.
Qed.

Definition com U(f:U → U → U):=∀a b,f a b = f b a.

Definition aso U f:=
 ∀a b c:U,f a (f b c) = f (f a b) c.
 
Goal eqprop → com or.
Proof.
cbv.
intros.
apply H.
split.
tauto.
tauto.
Qed.

Goal eqprop → com and.
Proof.
cbv.
intros.
apply H.
split.
tauto.
tauto.
Qed.

Goal eqprop → aso or.
Proof.
cbv.
intros.
apply H.
split.
tauto.
tauto.
Qed.

Goal eqprop → com iff.
Proof.
cbv.
intros.
apply H.
split.
tauto.
tauto.
Qed.

Definition inj A B(f:A → B):=
 ∀a1 a2,f a1 = f a2 → a1 = a2.
 
Definition sur A B f:=∀b:B,∃a:A,f a = b.

Definition not a:=a → False.

Definition not' a:=¬a.

Goal nnpp → eqprop → inj not'.
Proof.
intro.
red.
intros.
apply H0.
cbv in H1.
split.
intro.
apply H.
intro.
red in H3.
rewrite <-H1 in H3.
auto.
intro.
apply H.
intro.
red in H3.
rewrite H1 in H3.
auto.
Qed.

Goal nnpp → eqprop → sur not'.
Proof.
intros.
red.
intro.
unfold not'.
exists(~b).
apply H0.
split.
intro.
apply H.
auto.
intro.
intro.
auto.
Qed.

Goal ∀U,inj(@id U).
Proof.
intro.
red.
intros.
cbv in H.
auto.
Qed.

Goal ∀U,sur(@id U).
Proof.
cbv.
intros.
exists b.
split.
Qed.

Goal inj S.
Proof.
red.
intros.
injection H.
auto.
Qed.

Goal ¬sur S.
Proof.
intro.
red in H.
specialize(H 0).
destruct H.
discriminate.
Qed.

Definition hmm1 A B fa fb (f:A → B):=
 ∀a,f (fa a) = fb (f a).

Definition hmm2 A B fa fb (f:A → B):=
 ∀a1 a2,f (fa a1 a2) = fb (f a1) (f a2).
 
Goal eqprop → hmm2 or and not.
Proof.
red.
intros.
apply H.
cbv.
split.
intro.
split.
intro.
apply H0.
auto.
tauto.
intros.
destruct H0.
destruct H1.
auto.
auto.
Qed.

Goal eqprop → nnpp → hmm2 and or not.
Proof.
intros.
red.
intros.
apply H;clear H.
cbv.
split.
intros.
apply H0.
intro.
apply H1.
left.
intro.
apply H1.
right.
intro.
apply H.
tauto.
intros.
destruct H1.
destruct H.
auto.
auto.
Qed.

Definition all U P:=∀x:U,P x.

Definition ex U P:=∃x:U,P x.

Definition comple U P(x:U):=P x → False.

Goal ∀U(P:U → Type),ex(comple P) → not(all P).
Proof.
intros.
red.
intro.
red in H,X.
destruct H.
red in H.
specialize(X x).
auto.
Qed.

Goal nnpp → ∀U(P:U → Prop),not(all P) → ex(comple P).
Proof.
intros.
red.
red in H0.
apply H.
intro.
apply H0.
red.
intro.
apply H.
intro.
apply H1.
exists x.
red.
apply H2.
Qed.

Goal ∀U(P:U → Prop),¬ex P → all(comple P).
Proof.
intros.
red.
intro.
red.
intro.
red in H.
apply H.
red.
exists x.
auto.
Qed.

Goal ∀U(P:U → Prop),all(comple P) → ¬ex P.
Proof.
intros.
intro.
red in X,H.
destruct H.
specialize(X x).
red in X.
auto.
Qed.

Definition union U P Q(x:U):=P x∨Q x.

Goal ∀U(A B:U → Prop),ex(union A B) ↔ ex A∨ex B.
Proof.
intros.
split.
intro.
red in H.
destruct H.
red in H.
destruct H.
left.
red.
exists x.
auto.
right.
firstorder.
intro.
red.
destruct H.
red in H.
destruct H.
exists x.
red.
tauto.
firstorder.
Qed.

Definition inter U P Q(x:U):=P x∧Q x.

Definition all' U(P:U → Prop):=∀x,P x.

Goal ∀U(A B:U → Prop),all'(inter A B) ↔ all' A∧all' B.
Proof.
intros.
split.
intro.
red in H.
split.
red.
intro.
specialize(H x).
red in H.
tauto.
firstorder.
intro.
red.
intro.
red.
destruct H.
red in H,H0.
firstorder.
Qed.

Definition inc U A B:=∀x:U,A x → B x.

Definition same U A B:=∀x:U,A x ↔ B x.

Goal ∀U,ref(@inc U).
Proof.
intro.
red.
intro.
red.
intros.
rename x into A.
auto.
Qed.

Goal ∀U,tran(@inc U).
Proof.
intro.
red.
intros.
red.
intros.
red in X,X0.
rename x into A.
rename y into B.
rename z into C.
specialize(X x0).
specialize(X0 x0).
auto.
Qed.

Definition eqset:=∀U(A B:U → Prop),same A B → A = B.

Definition inc' U(A B:U → Prop):=∀x:U,A x → B x.

Goal eqset → ∀U,antsym(@inc' U).
Proof.
intros.
red.
intros.
apply H.
red.
intro.
rename x into A.
rename y into B.
red in H0,H1.
split.
firstorder.
firstorder.
Qed.

Definition full U(x:U):=True.

Definition emp U(x:U):=False.

Goal ∀U,max(@inc U)(@full U).
Proof.
intro.
red.
intro.
red.
intros.
rename x into A.
red.
split.
Qed.

Goal ∀U,min(@inc U)(@emp U).
Proof.
intro.
red.
intro.
rename x into A.
red.
intros.
red in H.
tauto.
Qed.

Goal ∀U,ref(@same U).
Proof.
intro.
red.
intros.
red.
intro.
tauto.
Qed.

Definition exinj A B:=∃f:A → B,inj f.

Goal ref exinj.
Proof.
red.
intro.
red.
exists(@id x).
red.
intros.
cbv in H.
auto.
Qed.

Goal tran exinj.
Proof.
red.
intros.
red.
red in H,H0.
destruct H,H0.
red in H,H0.
rename x0 into f.
rename x1 into g.
exists(fun x=>g(f x)).
red.
intros.
specialize(H a1 a2).
apply H.
specialize(H0(f a1)(f a2)).
auto.
Qed.

Definition comp A B C(f:A → B)(g:B → C)x:=g(f x).

Goal ∀A B C D(f:A → B)(g:B → C)(h:C → D),
 comp f(comp g h) = comp(comp f g)h.
Proof.
intros.
cbv.
split.
Qed.

Goal ∀A B C D(f:A → B)(g:B → C)(h:C → D),
 f\;g\;h = (f\;g)\;h.
intros.
cbv.
split.
Qed.

Goal ∀U,aso(@comp U U U).
Proof.
intro.
red.
intros.
cbv.
split.
Qed.

Goal ∀A B C(f:A → B)(g:B → C),
 inj f → inj g → inj(comp f g).
Proof.
intros.
red.
intros.
red in H,H0.
unfold comp in H1.
specialize(H a1 a2).
apply H.
specialize(H0(f a1)(f a2)).
auto.
Qed.

Goal ∀A B C(f:A → B)(g:B → C),
 sur f → sur g → sur(comp f g).
Proof.
intros.
red.
intro.
unfold comp.
red in H,H0.
specialize(H0 b).
destruct H0.
specialize(H x).
destruct H.
exists x0.
congruence.
Qed.

Definition eqf A B(f g:A → B):=∀x,f x = g x.

Goal ∀A B,ref(@eqf A B).
Proof.
intros.
red.
intro.
red.
intro.
split.
Qed.

Goal ∀A B,tran(@eqf A B).
Proof.
intros.
red.
intros.
red.
intro.
red in H,H0.
rename x into f.
rename y into g.
rename z into h.
specialize(H x0).
specialize(H0 x0).
congruence.
Qed.

Goal ∀A B,sym(@eqf A B).
Proof.
intros.
red.
intros.
red.
intro.
red in H.
specialize(H x0).
firstorder.
Qed.

Definition l_nuet U f(e:U):=∀x:U,f e x = x.

Definition r_nuet U f(e:U):=∀x:U,f x e = x.

Definition nuet U f(e:U):=l_nuet f e∧r_nuet f e.

Goal ∀U f(e1 e2:U),l_nuet f e1 → r_nuet f e2 → e1 = e2.
Proof.
intros.
red in H,H0.
specialize(H e2).
specialize(H0 e1).
congruence.
Qed.

(*Definition cancel U f(e x y:U):=f x y = e.*)

Goal ∀U f(e a1 a2 b:U),
 aso f →
 nuet f e → 
 f a1 b = e → 
 f b a2 = e → 
 a1 = a2.
Proof.
intros.
red in H,H0.
destruct H0.
red in H0,H3.
specialize(H0 a2).
rewrite<-H0.
case H1.
case H.
rewrite H2.
specialize(H3 a1).
rewrite H3.
split.
Qed.

Inductive set:=sup:∀A,(A → set) → set.

Definition pair e1 e2:=
 sup(λ x,if x then e1 else e2).

Fixpoint Eqset e1 e2:=
 match e1,e2 with 
  |sup f,sup g =>
    ∀a,∃b,Eqset(f a)(g b)∧
    ∀b,∃a,Eqset(f a)(g b)
 end.
 
Definition In e1 e2:=
 match e2 with
  |sup f => ∃a,Eqset e1(f a)
 end.
 
Goal ∀a b:set,In a(pair a b).
Proof.
induction a.
destruct b.
red.
exists true.
simpl.
intro.
exists a.
split.
specialize(H a(s a)).
destruct H.
destruct x.
auto.
auto.
intro.
exists b.
specialize(H b(s b)).
destruct H.
destruct x.
auto.
auto.
Qed.

          
Definition empty:=



Definition l_inv U f e x':=nuet f e∧∀x:U,f x' x = e.

Definition r_inv U f e x':=nuet f e∧∀x:U,f x x' = e.



Definition inv U f(e x':U):=l_inv f e x'∧r_inv f e x'.

Goal ∀U f(e:U),aso f → uni(inv f e).
Proof.
intros.
red.
intros.
red in H,H0,H1.
destruct H0,H1.
red in H0,H2,H1,H3.
destruct H0,H2,H1,H3.
red in H0,H2,H1,H3.



Goal nuet f e -> aso f -> f x x'=e

Goal 


Definition cancel

Definition id'{U}x:=x:U.

Goal ∀A (f:A → A),comp id' f = id'.
Goal ∀U,@min(U->Type) (@inc U)(@emp U).

Goal ¬∀U,total(@inc' U).
Proof.
intro.

intro.
red in H.
unfold inc' in H.

specialize(H Prop).
red in H.

intros.
rename x into A.
rename y into B.
unfold inc'.
apply NNPP.
intro.
apply H0.
left.
intros.
apply NNPP.
intro.
apply H0.
right.
intros.
apply NNPP.
intro.
apply H0.
assert((forall x,A x)\/~forall x,A x).
apply H.
destruct H0.
right.
intros.
firstorder.
left.
intros.
apply NNPP.
intro.
apply H0.

assert(forall x,A x\/~A x).
intro.
apply H.
unfold inc'.
assert(inhabited U\/~inhabited U).
apply H.
destruct H1.
destruct H1.
specialize(H0 X).
destruct H0.
right.
intros.
auto.
red in H.
specialize(H(inc' A B)).
cbv in H.
destruct H.
left.
auto.
right.
red.
intros.
assert(~~A x).
intro.
apply H.
intros.
op),not(all P)->ex(not' P).

Goal ∀U,hmm1 (@all U) (@ex U) not. 



 
Goal forall a b,~(a\/b)<->~a/\~b.
tauto.
 


Goal eqprop → ∀(P:Prop)(p1 p2:P),p1 = p2.
intros.
red in H.

destruct P.
split.
specialize(H P P).
apply H.


Variant T1:=t1.

Variant T2:=t2.

Goal exists f:T1->T2,inj f.
exists(fun 



cbv.

intros.
apply H.

Goal eqprop->¬aso iff.
intro.
intro.
red in H0.
unfold iff in H0.
specialize(H0 True True False).
assert(False<->(False<->True)).
rewrite H0.
tauto.
destruct H1.


destruct H0.

destruct H.





Goal ∀U(P:U → Prop),
uni P ∧ (∃x:U,P x) ↔ exists! x:U,P x.
split.



Goal ~forall a b:Prop,(a->b)->b->a.
exact Unnamed_thm15.
Qed.

Print Unnamed_thm16.


Goal sym imp ->False.
exact Unnamed_thm15.

Goal forall U(R:U->U->Prop),
U->(forall x,R x x)->~forall x,R x x->False.
intros U R.
apply Unnamed_thm9.
