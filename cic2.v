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

Definition imp(a b:Prop):Prop:=a → b.

Definition ref(U:Type)(R:U → U → Prop):Prop:=
 ∀x:U,R x x.

Goal ref imp.
Proof.
easy.
Qed.

Definition tran(U:Type)(R:U → U → Prop):Prop:=
 ∀x y z:U,R x y → R y z → R x z.

Goal tran imp.
Proof.
firstorder.
Qed.

Definition l_total(A B:Type)(R:A → B → Prop):Prop:=
 ∀a:A,∃b:B,R a b.

Goal ∀(U:Type)(R:U → U → Prop),ref R → l_total R.
Proof.
firstorder.
Qed.

Definition r_total(A B:Type)(R:A → B → Prop):Prop:=
 ∀b:B,∃a:A,R a b.

Goal ∀(U:Type)(R:U → U → Prop),ref R → r_total R.
Proof.
firstorder.
Qed.

Definition antsym(U:Type)(R:U → U → Prop):Prop:=
 ∀x y:U,R x y → R y x → x = y.

Definition exaxiom(U:Type)(R:U → U → Prop):Prop:=
 ∀a b:U,R a b → a = b.

Goal exaxiom iff → antsym imp.
Proof.
firstorder.
Qed.

Definition em(a:Prop):Prop:=a∨¬a.

Definition nnpp(a:Prop):Prop:=¬¬a → a.

Goal ∀a,¬¬em a.
Proof.
firstorder.
Qed.

Goal (∀a:Prop,em a) ↔ ∀a:Prop,nnpp a.
Proof.
split;intros H a.
- specialize(H a).
  firstorder.
- apply H.
  firstorder.
Qed.

Definition pasu(a b:Prop):Prop:=((a → b) → a) → a.

Goal (∀a b:Prop,pasu a b) ↔ ∀ a:Prop,nnpp a.
Proof.
split;intros H a ?.
- specialize(H a(~a)).
  firstorder.
- apply H.
  firstorder.
Qed.

Goal (∀ a b:Prop,pasu a b) ↔ ∀a:Prop,em a.
Proof.
split.
- intros H a.
  specialize(H(a\/~a)(~a)).
  firstorder.
- intros H a ?.
  specialize(H a).
  firstorder.
Qed.

Goal ∀x:nat,S x ≠ x.
Proof.
auto.
Qed.

Goal ∀n m:nat,{n=m}+{n<>m}.
Proof.
induction n as[|n IHn].
destruct m as [|m].
- left.
  split.
- right.
  discriminate.
- destruct m as[|m]. 
  right.
  discriminate.
 destruct(IHn m).
 left.
 auto.
 right.
 intro.
 auto.
Qed.

Goal ∀n m:nat,n = m ∨ n ≠ m.
Proof.
induction n as [|? IHn];intros [];firstorder.
ecase IHn;[left|right];eauto.
Qed.

Goal ∀n m:nat,n = m ∨ n ≠ m.
Proof with eauto.
elim=>[|? IHn];intros []...
ecase IHn.
left...
right...
Qed.

Goal ∀x y:bool,x = y ∨ x ≠ y.
Proof.
intros[][];firstorder.
Qed.

Goal ∀x y:nat,em(x = y).
Proof with eauto.
red.
elim=>[|? IHx];intros []...
ecase IHx;[left|right]...
Qed.

Goal ∀x y:Empty_set,em(x = y).
Proof.
case.
Qed.

Goal ∀x y:unit,em(x = y).
Proof.
intros[][].
firstorder.
Qed.

Definition total(U:Type)(R:U → U → Prop):Prop:=
 ∀x y:U,R x y∨R y x.

Goal (∀a:Prop,em a) → total imp.
Proof.
intros H x.
specialize(H x).
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),total R → ref R.
Proof.
firstorder.
Qed.

Definition iref(U:Type)(R:U → U → Prop):Prop:=
 ∀x:U,¬R x x.

Goal ∀(U:Type)(R:U → U → Prop),U → ref R → ¬iref R.
Proof.
firstorder.
Qed.

Definition asym(U:Type)(R:U → U → Prop):Prop:=
 ∀x y:U,R x y → ¬R y x.

Goal ∀(U:Type)(R:U → U → Prop),asym R → iref R.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),asym R → antsym R.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),tran R → iref R → asym R.
Proof.
firstorder.
Qed.

Definition sym(U:Type)(R:U → U → Prop):Prop:=
 ∀x y:U,R x y → R y x.

Goal ∀(U:Type)(R:U → U → Prop),
 tran R → sym R → l_total R → ref R.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),
 tran R → sym R → r_total R → ref R.
Proof.
firstorder.
Qed.

Goal ¬sym imp.
Proof.
intro H.
specialize(H False True).
firstorder.
Qed.

Goal sym or.
Proof.
firstorder.
Qed.

Goal l_total or.
Proof.
intro.
exists True.
tauto.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),
 sym R → l_total R ↔ r_total R.
Proof.
split.
- intros H0 b.
  specialize(H0 b).
  firstorder.
- intros H0 a.
  specialize(H0 a).
  firstorder.
Qed.

Goal ¬ref or.
Proof.
intro H.
specialize(H False).
tauto.
Qed.

Goal ¬iref or.
Proof.
intro H.
specialize(H True).
tauto.
Qed.

Goal sym and.
Proof.
firstorder.
Qed.

Goal ¬l_total and.
Proof.
intro H.
specialize(H False).
firstorder.
Qed.

Goal tran and.
Proof.
firstorder.
Qed.

Goal exaxiom iff → antsym and.
Proof.
firstorder.
Qed.

Goal ¬iref and.
Proof.
intro H.
specialize(H True).
tauto.
Qed.

Goal ref iff.
Proof.
firstorder.
Qed.

Goal ¬total iff.
Proof.
intro H.
specialize(H False True).
tauto.
Qed.

Goal tran iff.
Proof.
firstorder.
Qed.

Goal exaxiom iff → antsym iff.
Proof.
firstorder.
Qed.

Goal ∀(U:Type),ref(@eq U).
Proof.
firstorder.
Qed.

Goal ¬∀(U:Type),total(@eq U).
Proof.
intro H.
destruct(H Prop True False)as[H0|H0].
- case H0. 
  split.
- rewrite H0.
  split.
Qed.

Goal ∀(U:Type),tran(@eq U).
Proof.
congruence.
Qed.

Goal ∀(U:Type),antsym(@eq U).
Proof.
firstorder.
Qed.

Definition max(U:Type)(R:U → U → Prop)(a:U):Prop:=
 ∀x:U,R x a.

Definition min(U:Type)(R:U → U → Prop)(a:U):Prop:=
 ∀x:U,R a x.

Goal max imp True.
Proof.
firstorder.
Qed.

Goal min imp False.
Proof.
firstorder.
Qed.

Goal max or True.
Proof.
firstorder.
Qed.

Goal min or True.
Proof.
firstorder.
Qed.

Goal ∀x,¬max and x.
Proof.
intros ? H.
specialize(H False).
tauto.
Qed.

Definition uni(U:Type)(P:U → Prop):Prop:=
 ∀ x1 x2:U,P x1 → P x2 → x1 = x2.

Goal ∀(U:Type)(R:U → U → Prop),antsym R → uni(max R).
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop),antsym R → uni(min R).
Proof.
firstorder.
Qed.

Definition maximal(U:Type)(R:U → U → Prop)(a:U):Prop:=
 ∀x:U,R a x → a = x.

Definition minimal(U:Type)(R:U → U → Prop)(a:U):Prop:=
 ∀x:U,R x a → a = x.

Goal ∀(U:Type)(R: U → U → Prop)(a:U),
 antsym R → max R a → maximal R a.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop)(a:U),
 antsym R → min R a → minimal R a.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop)(a b:U),
 max R a → maximal R b → a = b.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop)(a b:U),
 min R a → minimal R b → a = b.
Proof.
firstorder.
Qed.

Goal ∀(U:Type)(R:U → U → Prop)(a:U),
 total R → maximal R a → max R a.
Proof.
intros ? ? ? H H0 x.
edestruct H as[H1|].
specialize(H0 x).
specialize(H0 H1).
congruence.
assumption.
Qed.

Goal ∀(U:Type)(R:U → U → Prop)(a:U),
 total R → minimal R a → min R a.
Proof.
intros ? ? ? H H0 x.
edestruct H as [H1|].
specialize(H0 x).
specialize(H0 H1).
congruence.
assumption.
Qed.

Definition com(U:Type)(f:U → U → U):Prop:=
 ∀a b:U,f a b = f b a.

Definition aso(U:Type)(f:U → U → U):Prop:=
 ∀a b c:U,f a (f b c) = f (f a b) c.
 
Goal exaxiom iff → com or.
Proof.
firstorder.
Qed.

Goal exaxiom iff → com and.
Proof.
firstorder.
Qed.

Goal exaxiom iff → aso or.
Proof.
intros H ? ? ?.
apply H.
tauto.
Qed.

Goal exaxiom iff → com iff.
Proof.
firstorder.
Qed.

Definition inj(A B:Type)(f:A → B):Prop:=
 ∀a1 a2:A,f a1 = f a2 → a1 = a2.
 
Definition sur(A B:Type)(f:A → B):Prop:=
 ∀b:B,∃a:A,f a = b.

Goal (∀a:Prop,nnpp a) → exaxiom iff → inj not.
Proof.
intros H H0 ? ? H1.
apply H0.
firstorder.
- apply H.
  intro H3.
  case H1 in H3.
  auto.
- apply H.
  intro H3.
  rewrite H1 in H3.
  auto.
Qed.


Goal (∀a:Prop,nnpp a) → exaxiom iff → sur not.
Proof.
cbv.
intros.
exists(¬b).
apply H0.
firstorder.
apply H.
auto.
Qed.

Goal ∀(U:Type),inj(@id U).
Proof.
firstorder.
Qed.

Goal ∀(U:Type),sur(@id U).
Proof.
intros.
eexists.
split.
Qed.

Goal inj S.
Proof.
firstorder.
Qed.

Goal ¬sur S.
Proof.
intro H.
case(H 0).
discriminate.
Qed.

Definition hmm1(A B:Type)(fa:A → A)(fb:B → B)(f:A → B):Prop:=
 ∀a:A,f (fa a) = fb (f a).

Definition hmm2(A B:Type)(fa:A → A → A)(fb:B → B → B)
 (f:A → B):Prop:=
  ∀a1 a2:A,f (fa a1 a2) = fb (f a1) (f a2).
 
Goal exaxiom iff → hmm2 or and not.
Proof.
firstorder.
Qed.

Goal exaxiom iff → (∀a:Prop,nnpp a) → hmm2 and or not.
Proof.
intros H H0 ? ?.
apply H.
split.
intros.
apply H0.
tauto.
tauto.
Qed.

Definition comple(U:Type)(P:U → Prop)(x:U):Prop:=¬P x.

Goal ∀(U:Type)(P:U → Prop),ex(comple P) → ¬(all P).
Proof.
firstorder.
Qed.

Goal (∀a:Prop,nnpp a) → 
 ∀(U:Type)(P:U → Prop),¬(all P) → ex(comple P).
Proof.
intros H ? ? H0.
apply H.
intro.
apply H0.
intro.
apply H.
firstorder.
Qed.

(*Goal ∀U(P:U → Prop),¬ex P → all(comple P).
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
Qed.*)

Definition union(U:Type)(P Q:U → Prop)(x:U):Prop:=P x∨Q x.

Goal ∀(U:Type)(A B:U → Prop),ex(union A B) ↔ ex A∨ex B.
Proof.
firstorder.
Qed.

Definition inter(U:Type)(P Q:U → Prop)(x:U):Prop:=P x∧Q x.

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
