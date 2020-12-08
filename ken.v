Require Import Utf8.

Set Implicit Arguments.

Unset Strict Implicit.

Module a.

Section a.

Variable Ob:Type.

Variable Hom:Ob → Ob → Type.

Variable comp:∀a b c,Hom a b → Hom b c → Hom a c.

Variable id:∀{a},Hom a a.

Definition comp_assoc:=

∀(a b c d:Ob)(f:Hom a b)(g:Hom b c)(h:Hom c d),

comp(comp f g)h = comp f(comp g h).

Definition unit_l:=∀(a b:Ob)(f:Hom a b),
comp id f = f.

Definition unit_r:=∀(a b:Ob)(f:Hom a b),
comp f id = f.

End a.

Print unit_r.

Goal forall(Ob:Type)(Hom:Ob->Ob->Type)
(comp:∀a b c,Hom a b → Hom b c → Hom a c)
(id1 id2:∀a,Hom a a),
unit_l comp id1->unit_r comp id1->
unit_l comp id2->unit_r comp id2->
id1=id2.
compute.
intros.



Print unit.

Definition comp_assoc(Ob:Type)(Hom:Ob → Ob → Type)

(comp:∀{a b c:Ob},Hom a b → Hom b c → Hom a c):=

∀(a b c d:Ob)(f:Hom a b)(g:Hom b c)(h:Hom c d),

comp(comp f g)h = comp f(comp g h).

Definition A a b:=a → b.

Definition B a b c(H:a → b)(H0:b → c)(H1:a):=H0(H H1).

Goal comp_assoc B.
red.
intros.
compute.
split.
Qed.


End a.

Module b.



Compute comp_assoc a.B.

Definition comp_assoc(Ob:Type)(Hom:Ob → Ob → Type)

(comp:∀{a b c:Ob},Hom a b → Hom b c → Hom a c):=

∀(a b c d:Ob)(f:Hom a b)(g:Hom b c)(h:Hom c d),

comp(comp f g)h = comp f(comp g h).


Definition assoc(U:Type)(f:U->U->U):=
forall a b c:U,f(f a b)c=f a(f b c).

Definition iscomp(Hom:Type)(dom cod:Hom->Type)
(comp:Hom->Hom->Hom):=
forall f g:Hom,cod f=dom g->dom(comp f g)=dom f.


Definition comp_asso(Ob:Type)(Hom:Ob → Ob → Type)
(comp:∀{a b c:Ob},Hom a b->Hom b c->Hom a c):=
∀(a b c d:Ob)(f:Hom a b)(g:Hom b c)(h:Hom c d),
@assoc Ob comp.

Definition aa:=
forall(f:Hom a b)

Compute @comp_assoc Prop(fun a b:Prop=>a->b)
(fun (a b c:Prop)(H:a->b)(H0:b->c)=>(fun x:a=>H0(H x))).

Goal ∀ (x x0 x1 x2 : Prop) (x3 : x → x0) 
         (x4 : x0 → x1) (x5 : x1 → x2),
         (λ x6 : x, x5 (x4 (x3 x6))) =
         (λ x6 : x, x5 (x4 (x3 x6))).
intros.
compute.
split.

Definition compable(Ob:Type)(Hom:Ob → Ob → Type → Prop)
(f g::=
cod f = dom g.



Compute @compable Prop(Prop->Prop)not not(fun not->True).