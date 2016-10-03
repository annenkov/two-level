import data.equiv
open equiv

constant is_fibrant' : Type → Prop

structure is_fibrant [class] (X : Type) := mk ::
  fib_internal : is_fibrant' X

constant equiv_is_fibrant {X Y : Type}(e : X ≃ Y)[fib : is_fibrant X] : is_fibrant Y

constant unit_is_fibrant' : is_fibrant' unit

constant pi_is_fibrant' {X : Type}{Y : X → Type}
  : is_fibrant X
  → (Π (x : X), is_fibrant (Y x))
  → is_fibrant' (Π (x : X), Y x)

constant sigma_is_fibrant' {X : Type}{Y : X → Type}
  : is_fibrant X
  → (Π (x : X), is_fibrant (Y x))
  → is_fibrant' (Σ (x : X), Y x)

constant prod_is_fibrant' {X Y : Type}
  : is_fibrant X -> is_fibrant Y -> is_fibrant' (X × Y)

constant fib_eq {X : Type}[is_fibrant X] : X → X → Type

namespace fib_eq
  notation x ~ y := fib_eq x y
  constant refl {X : Type}[is_fibrant X](x : X) : x ~ x
  constant elim {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x ~ y → Type}
                [Π (y : X)(p : x ~ y), is_fibrant (P y p)]
                (d : P x (refl x)) : Π (y : X)(p : x ~ y), P y p
  constant elim_β {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x ~ y → Type}
                [Π (y : X)(p : x ~ y), is_fibrant (P y p)]
                (d : P x (refl x)) : elim d x (refl x) ~ d
  definition idp [reducible] [constructor] {X : Type}[is_fibrant X] {a : X} := refl a
end fib_eq

constant fib_eq_is_fibrant' {X : Type}[is_fibrant X](x y : X) : is_fibrant' (fib_eq x y)

structure Fib := mk ::
  (pretype : Type)
  (fib : is_fibrant pretype)

attribute Fib.pretype [coercion]
attribute Fib.fib [instance]

constant fib_is_fibrant' : is_fibrant' Fib

-- instances

definition unit_is_fibrant [instance] : is_fibrant unit := is_fibrant.mk unit_is_fibrant'

definition pi_is_fibrant [instance] {X : Type}{Y : X → Type}
  [fibX : is_fibrant X] [fibY : Π (x : X), is_fibrant (Y x)] :
  is_fibrant (Π (x : X), Y x) :=
    is_fibrant.mk (pi_is_fibrant' fibX fibY)

definition sigma_is_fibrant [instance] {X : Type}{Y : X → Type}
  [fibX : is_fibrant X] [fibY : Π (x : X), is_fibrant (Y x)] :
  is_fibrant (Σ (x : X), Y x) :=
    is_fibrant.mk (sigma_is_fibrant' fibX fibY)

definition prod_is_fibrant [instance] {X Y : Type} 
  [fibX : is_fibrant X] [fibY : is_fibrant Y] :
  is_fibrant (X × Y) := is_fibrant.mk (prod_is_fibrant' fibX fibY)

definition fib_is_fibrant [instance] : is_fibrant Fib := is_fibrant.mk fib_is_fibrant'

definition fib_eq_is_fibrant [instance] {X : Type}[is_fibrant X](x y : X) :
                             is_fibrant (fib_eq x y) :=
 is_fibrant.mk (fib_eq_is_fibrant' x y)

-- basics

open prod

namespace fib_eq
  variables {X: Type}[is_fibrant X]
  variables {Y: Type}[is_fibrant Y]
  variables {Z: Type}[is_fibrant Z]

  attribute refl [refl]
  definition symm [symm] {x y : X} : x ~ y → y ~ x :=
    elim (refl x) y
  definition symm_β {x : X} : symm (refl x) ~ refl x :=
    elim_β (refl x)
  definition trans [trans] {x y z : X} : x ~ y → y ~ z → x ~ z := λ p,
    elim p z
  
  definition trans_β {x y : X}(p : x ~ y) : trans p (refl y) ~ p :=
    elim_β p

  definition trans' {x y z : X} (p : x ~ y) (q : y ~ z) : x ~ z := 
  (elim (elim idp z) y) p q  
  
  -- Alternative proof of transitivity using tactics.
  -- FIXME: check why it fails if we do induction of p only (probably, has something to do with levels)
  definition trans'' [trans] {x y z : X} (p: x ~ y) (q : y ~ z) : x ~ z :=
  -- by induction p using elim; exact q -- fails if we do induction on p only
  by induction p using elim; induction q using elim; apply idp  -- but works in case of double induction  

  definition subst [subst] {x y : X}{P : X → Type}[Π (x : X), is_fibrant (P x)]
                           (p : x ~ y)(d : P x) : P y :=
    elim d y p
  definition subst_β {x : X}{P : X → Type}[Π (x : X), is_fibrant (P x)](d : P x) :
                     subst (refl x) d ~ d :=
    elim_β d
  
  -- FIXME: simplification/rewriting needed to define beta rules
  eval trans' (refl _) (refl _) ~ refl _
  definition trans_β' {x : X} : trans' (refl x) (refl x) ~ (refl x) := sorry
  

  infixl ⬝ := trans

  definition symm_trans {x y : X}(p : x ~ y) : symm p ⬝ p ~ refl y :=
    let t := calc
         (symm (refl x) ⬝ refl x)
        ~ (refl x ⬝ refl x) : { !symm_β }
    ... ~ refl x : trans_β in
    elim t y p
  
  -- actions on paths

  definition ap {x y : X}  (f : X -> Y) : x ~ y -> f x ~ f y :=
    elim (refl _) _
  
  definition ap_β {x : X} (f : X -> Y) : ap f (refl x) ~ refl (f x) := elim_β (refl (f x))

  definition ap₂ {x x' : X} {y y' : Y} (f : X -> Y -> Z) (p : x ~ x') (q : y ~ y') : f x y ~ f x' y' :=
    (ap (λ x, f x y) p) ⬝ (ap (f x') q)
  
  variables {xx : X} {yy : Y}
  variables {ff : X -> Y -> Z}
  
  eval ap₂ ff (refl _) (refl _)
  check (elim (refl (ff xx yy)) xx)
  definition ap₂_β {x : X} {y : Y} (f : X -> Y -> Z) : ap₂ _ (refl x) (refl y) ~ refl (f x y) := sorry

  -- definition apd {x y : X} (p : x = y)
  
end fib_eq

open fib_eq

variables {A: Type}[is_fibrant A]
variables {B: Type}[is_fibrant B]
variables {C: Type}[is_fibrant C]


structure is_contr (X : Type)[is_fibrant X] := mk ::
  (center : X)
  (contraction : Π (x : X), center ~ x)

definition is_contr_equiv [instance] {X : Type}[is_fibrant X] :
  (Σ (c : X), Π (x : X), c ~ x) ≃ is_contr X := sorry

definition is_contr_is_fibrant [instance] (X : Type)[is_fibrant X] : is_fibrant (is_contr X) :=
  equiv_is_fibrant is_contr_equiv

definition is_trunc : Π (n : ℕ)(X : Type) [is_fibrant X], Type
| @is_trunc 0 X fib := is_contr X
| @is_trunc (nat.succ n) X fib := Π (x y : X), is_trunc n (x ~ y)

definition is_prop (X : Type) [is_fibrant X] := Π (x y : X), x ~ y

section truncated_types
  variables (X : Type)[is_fibrant X]

  definition is_contr_is_trunc :
    is_contr X → is_trunc 1 X :=
    assume c : is_contr X,
    let path (x y : X) : x ~ y :=
        symm (is_contr.contraction c x) ⬝ is_contr.contraction c y in
    let l (x y : X)(p : x ~ y) : path x y ~ p :=
        fib_eq.elim (!symm_trans) y p in
    λ x y, is_contr.mk (path x y) (l x y)

  definition inhab_is_contr_is_prop : (X → is_contr X) → is_trunc 1 X :=
    assume H x,
    have is_contr X, from H x,
    have is_trunc 1 X, from is_contr_is_trunc X this,
    this x

  definition is_prop_is_trunc : is_prop X → is_trunc 1 X :=
    assume p : is_prop X,
    have X → is_contr X, from λ x, is_contr.mk x (p x),
    show is_trunc 1 X, from inhab_is_contr_is_prop X this

  definition is_trunc_is_prop : is_trunc 1 X → is_prop X := λ t x y,
    is_contr.center (t x y)
end truncated_types

section singleton
  variables {X : Type}[is_fibrant X]
  definition singleton [reducible] (x : X) := Σ (y : X), y ~ x
  definition singleton_contr (x : X) : is_contr (singleton x) :=
    let l (y : X)(p : y ~ x) : ⟨x , refl x⟩ ~ ⟨y, p⟩ := elim !refl x p in
    is_contr.mk ⟨x, refl x⟩ (λt, match t with ⟨y, p⟩ := l y p end)
end singleton

section fib_equivalences
  variables {X Y : Type}(f : X → Y)[is_fibrant X][is_fibrant Y]

  definition fibre [reducible] (y : Y) := Σ (x : X), f x ~ y
  definition is_fib_equiv [reducible] [class] := Π (y : Y), is_contr (fibre f y)
end fib_equivalences

definition fib_equiv [reducible] (X Y : Type)[is_fibrant X][is_fibrant Y] : Type :=
  Σ (f : X → Y), is_fib_equiv f

definition id_is_fib_equiv {X : Type}[is_fibrant X] : is_fib_equiv (@id X) := singleton_contr

notation X `≃` Y := fib_equiv X Y

definition coerce {X Y : Fib} : X ~ Y → X → Y := elim id Y
definition coerce_is_fib_equiv [instance] {X Y : Fib}(p : X ~ Y) : is_fib_equiv (coerce p) :=
  have coerce (refl X) ~ id, from elim_β id,
  have is_fib_equiv (coerce (refl X)), from subst (symm this) id_is_fib_equiv,
  elim this Y p
definition coerce_fib_equiv {X Y : Fib}(p : X ~ Y) : X ≃ Y := ⟨ coerce p, _ ⟩

definition Univalence := Π {X Y : Fib}, is_fib_equiv (@coerce_fib_equiv X Y)
