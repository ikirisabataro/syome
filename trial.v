Require Import Utf8 ssreflect.


Set Implicit Arguments.

Variant T1:=t1.

Variant T2:=t2.

Definition inj A B(f:A → B):=
 ∀a1 a2,f a1 = f a2 → a1 = a2.
 
Definition sur A B f:=∀b:B,∃a:A,f a = b.

Goal ∃f:T1 → T2,inj f∧sur f.
exists(λ x,t2).
split.
simpl.
red.
intros.
case a1.
case a2.
split.
red.
intro.
case b.
split.
exact t1.
split.
Qed.

Variant B:=b1|b2.

Variant B':=b1'|b2'.

Goal ∃f:B → B',inj f∧sur f.
exists(λ x,match x with b1=>b1'|b2=>b2' end).
split.
red.
intros.
assert(a1=b1\/a1=b2).
case a1.
left.
split.
right.
split.
assert(a2=b1\/a2=b2).
case a2.
tauto.
tauto.
destruct H0.
destruct H1.
congruence.
rewrite H0 in H.
rewrite H1 in H.
discriminate H.
destruct H1.
rewrite H0 in H.
rewrite H1 in H.
discriminate.
congruence.
red.
intro.
destruct b.
exists b1.
split.
exists b2.
split.
Qed.

Definition two U:=∀x y z:U,x=y\/y=z\/z=x.
Goal two bool.
red.
intros.
case x.
case y.
left.
split.
case z.
right.
right.
split.
right.
left.
split.
case y,z.
tauto.
tauto.
tauto.
tauto.
Qed.

Definition andi(P:Prop → Prop → Prop):Prop:=
 ∀a b:Prop,a → b → P a b.


Definition andel(P:Prop → Prop → Prop):Prop:=
 ∀a b:Prop,P a b → a.
 

Definition ander(P:Prop → Prop → Prop):Prop:=
 ∀a b:Prop,P a b → b.


Goal ∀(P:Prop → Prop → Prop)(a b:Prop),
 andi P → andel P → ander P → P a b ↔ a∧b.
Proof.
firstorder.
Qed.

Variant F:Type:=.

Variant

Check F.



Goal andi and/\andel and/\ander and.
split.
red.
tauto.
split.
red.
tauto.
red.
tauto.
Qed.

Variant And (a b:Prop):Prop:=Conj:a->b->And a b.

Goal forall a b,and a b<->And a b.
split.
intro.
destruct H.
split;auto.
intro.
destruct H.
tauto.
Qed.

Goal forall a b,a/\b->prod a b.
intros.
destruct H.
split.
auto.
auto.
Qed.

Goal forall a b:Prop,a*b->a/\b.
tauto.
Qed.

Goal ∀a b,a*b → b*a.
Proof.
intros ? ? [].
split.
assumption.
assumption.
Qed.



Goal exists f:Type->Prop,forall a b,a/\b->(f a)*(f b).
exists(λ x:Prop,x).
split.
Qed.
red.
intros.
apply H.
rewrite H.
auto.


Definition

Goal ∀U,two U → ∃f:bool → U,inj f∧sur f.
intros.
red in H.

left.
split.
left.
split.

Goal ∃f:bool → B,inj f.
Proof.
refine(let f:=λ x,if x then b1 else b2 in _).
exists f.
refine(λ(a1 a2:bool)(H:f a1 = f a2),_).
refine(if a1 then _ else _).
refine(if a2 then _ else _).
split.
assert(1=0).

subst.
discriminate.
Show Proof.



Abort.
Print f.
exists f.
refine(λ(a1 a2:bool),_).
refine(λ(H:g a1 = g a2),_).

ex_intro (λ f : bool → B, inj f ∧ sur f)
   (λ x : bool, if x then b1 else b2)
   (conj
      (λ (a1 a2 : bool) (H : (if a1 then b1 else b2) =
                             (if a2 then b1 else b2)),
         (if a1 as b
           return
             ((if b then b1 else b2) =
              (if a2 then b1 else b2) → 
              b = a2)
          then
           λ H0 : b1 = (if a2 then b1 else b2),
             (if a2 as b
               return
                 (b1 = (if b then b1 else b2)
                  → true = b)
              then λ _ : b1 = b1, eq_refl
              else
               λ H1 : b1 = b2,
                 let H2 : False :=
                   eq_ind b1
                     (λ e : B,
                        match e with
                        | b1 => True
                        | b2 => False
                        end) I b2 H1 in
                 False_ind (true = false) H2) H0
          else
           λ H0 : b2 = (if a2 then b1 else b2),
             (if a2 as b
               return
                 (b2 = (if b then b1 else b2)
                  → false = b)
              then
               λ H1 : b2 = b1,
                 let H2 : False :=
                   eq_ind b2
                     (λ e : B,
                        match e with
                        | b1 => False
                        | b2 => True
                        end) I b1 H1 in
                 False_ind (false = true) H2
              else λ _ : b2 = b2, eq_refl) H0) H)
      ?Goal))

Goal ∃f:bool → B,inj f∧sur f.
Proof.
exists(λ x,if x then b1 else b2).
split.
red.
intros.
destruct a1.
destruct a2.
split.
discriminate.
destruct a2.
discriminate.
split.

Show Proof.
assert


Goal ∃f:B → B',inj f∧sur f.
Proof.
exists(λ x,match x with b1=>b1'|b2=>b2' end).
split.
- red.
  intros a1 a2 H.
  assert(∀b:B,b=b1∨b=b2) as H0.
  { case;tauto. }
  destruct(H0 a1) as [H1|H1].
  destruct(H0 a2) as [H2|H2].
  + congruence.
  + rewrite H1,H2 in H.
    discriminate.
  + rewrite H1,H2 in H.
    discriminate.
  + congruence.
- intro.
  case b.
  + exists b1.
    split.
  + exists b2.
    split.
Qed.
  
  
a
case a1.
left.
split.
right.
split.
assert(a2=b1\/a2=b2).
case a2.
tauto.
tauto.
destruct H0.
destruct H1.
congruence.
rewrite H0 in H.
rewrite H1 in H.
discriminate H.
destruct H1.
rewrite H0 in H.
rewrite H1 in H.
discriminate.
congruence.
red.
intro.
destruct b.
exists b1.
split.
exists b2.
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
exists true.
intro.
exists a.
split.
- destruct(H a(s a)).
  destruct x;auto.
- intro.
  exists b.
  destruct(H b(s b)).
  destruct x;auto.
Qed.

Definition zseteq:=∀a b,Eqset a b → a = b.

Definition gaien U V(In:V → U → Prop):=
 ∀A B,(∀x,In x A ↔ In x B) → A = B.
 
Goal ref Eqset.
Proof.
red.
induction x.
intro.
exists a.
split.
- exact(H a).
- intro.
exists b.
exact(H b).
Qed.

Goal sym Eqset.
red.
double induction x y.
intros.
intro.
specialize(H a).
specialize(H A s).
red in H1.
s 


specialize(H0 a).
red in H0.
red.
intro.
red in H0.
revert x.
induction y.
intros.
induction x.
intro.
destruct H0.
induction y.
intro.
specialize(H1 a).
apply H1.

red.
intro.
intros.
intro.


firstorder.
intro.
red.
intro.
intro.
red in H.
destruct a.
destruct H.
induction (s x).
apply H0.
destruct H.
red in H0.
destruct H0.
specialize(H x).
unfold Eqset in H0.
destruct ( s x).
apply H.
red.
apply H0.


intro.
red in H.
destruct( a).
destruct H.
red in  H.

 
Goal zseteq → gaien In.
red.
intro.
induction A.
intros.
apply H.
specialize(H1 B).
destruct H1.
destruct B.
red.

intros.
apply H.
destruct(H0 A).
red.
induction A.

intros.
specialize(H0 B).
destruct H0.

destruct B.

intros.
red in H.
in

          
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
