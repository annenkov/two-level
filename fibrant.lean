import data.equiv

open eq

notation X `≃ₛ` Y := equiv X Y
constant is_fibrant' : Type → Prop

structure is_fibrant [class] (X : Type) := mk ::
  fib_internal : is_fibrant' X

constant equiv_is_fibrant {X Y : Type}(e : X ≃ₛ Y)[fib : is_fibrant X] : is_fibrant Y

constant unit_is_fibrant' : is_fibrant' unit
constant polyunit_is_fibrant' : is_fibrant' poly_unit

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

-- explicit universe level declaration allows to use tactics;
-- otherwise, proofs fail to unify level variables sometime
constant fib_eq.{u} {X : Type.{u}}[is_fibrant X] : X → X → Type.{u}

namespace fib_eq
  notation x ~ y := fib_eq x y
  constant refl {X : Type}[is_fibrant X](x : X) : x ~ x
  constant elim {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x ~ y → Type}
                [Π (y : X)(p : x ~ y), is_fibrant (P y p)]
                (d : P x (refl x)) : Π (y : X)(p : x ~ y), P y p
  constant elim_β {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x ~ y → Type}
                [Π (y : X)(p : x ~ y), is_fibrant (P y p)]
                (d : P x (refl x)) : elim d x (refl x) = d

  definition idp [reducible] [constructor] {X : Type}[is_fibrant X] {a : X} := refl a

  attribute elim_β [simp]
  attribute elim [recursor]
end fib_eq

constant fib_eq_is_fibrant' {X : Type}[is_fibrant X](x y : X) : is_fibrant' (fib_eq x y)

structure Fib : Type := mk ::
  (pretype : Type)
  (fib : is_fibrant pretype)

attribute Fib.pretype [coercion]
attribute Fib.fib [instance]

constant fib_is_fibrant' : is_fibrant' Fib

-- instances

definition unit_is_fibrant [instance] : is_fibrant unit := is_fibrant.mk unit_is_fibrant'
definition polyunit_is_fibrant [instance] : is_fibrant poly_unit := is_fibrant.mk polyunit_is_fibrant'

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
  open function

  variables {X: Fib}
  variables {Y: Fib}
  variables {Z: Fib}

  attribute refl [refl]
  definition symm [symm] {x y : X} : x ~ y → y ~ x :=
    elim (refl x) y
  definition symm_β [simp] {x : X} : symm (refl x) = refl x :=
    elim_β (refl x)
  definition trans [trans] {x y z : X} : x ~ y → y ~ z → x ~ z := λ p,
    elim p z

  definition trans_β [simp] {x y : X}(p : x ~ y) : trans p (refl y) = p :=
    elim_β p

  definition trans_β' [simp] {x : X} : trans (refl x) (refl x) = refl x := by simp

  definition trans' {x y z : X} (p : x ~ y) (q : y ~ z) : x ~ z :=
    (elim (elim idp z) y) p q

  -- Alternative proof of transitivity using tactics.
  definition trans'' {x y z : X} (p: x ~ y) (q : y ~ z) : x ~ z :=
  by induction p using elim; exact q

  definition subst [subst] {x y : X}{P : X → Type}[Π (x : X), is_fibrant (P x)]
                           (p : x ~ y)(d : P x) : P y :=
    elim d y p
  definition subst_β [simp] {x : X}{P : X → Type}[Π (x : X), is_fibrant (P x)](d : P x) :
                     subst (refl x) d = d :=
    elim_β d

  notation p ▹ d := subst p d

  infixl ⬝ := trans
  postfix ⁻¹ := symm

  definition symm_trans {x y : X} (p : x ~ y) : p⁻¹ ⬝ p ~ refl y :=
  by induction p using elim; simp

  definition symm_trans_β {x : X} : (refl x)⁻¹ ⬝ (refl x) = refl x := by simp

  definition assoc_trans {x y z t: X} (p : x ~ y) (q : y ~ z) (r : z ~ t) :
    (p ⬝ (q ⬝ r)) ~ ((p ⬝ q) ⬝ r) :=
  by induction r using elim; simp

  definition subst_trans {A : Fib } {a b c: A} {P : A → Fib}
    (p : a ~ b) (q : b ~ c) (u : P a) : #fib_eq q ▹ (p ▹ u) ~ p ⬝ q ▹ u :=
    by induction p using elim; induction q using elim; simp

  namespace ap
    -- action on paths

    definition ap {x y : X} (f : X -> Y) : x ~ y -> f x ~ f y :=
      elim (refl _) _

    definition ap_β [simp] {x : X} (f : X -> Y) : ap f (refl x) = refl (f x) := elim_β (refl (f x))

    definition ap_trans {x y z : X} (f : X → Y) (p : x ~ y) (q : y ~ z) :
      ap f (p ⬝ q) ~ (ap f p) ⬝ (ap f q) := by induction p using elim; induction q using elim; simp

    definition ap_symm {x y : X} (f : X → Y) (p : x ~ y) : ap f p⁻¹ ~ (ap f p)⁻¹ :=
      by induction p using elim; simp

    definition ap_compose {x y : X} (f : X → Y) (g : Y → Z) (p : x ~ y) : ap g (ap f p) ~ ap (g ∘ f) p :=
      by induction p using elim; simp

    definition ap_id {x y : X} (p : x ~ y) : ap id p ~ p := by induction p using elim; simp

    definition ap₂ [reducible] {x x' : X} {y y' : Y} (f : X -> Y -> Z)
      (p : x ~ x') (q : y ~ y') : f x y ~ f x' y' := (ap (λ x, f x y) p) ⬝ (ap (f x') q)

    definition ap₂_β {x : X} {y : Y} (f : X -> Y -> Z) : ap₂ _ (refl x) (refl y) = refl (f x y) :=
      by simp

    definition apd {P : X → Fib} (f : Π x, P x) {x y : X} (p : x ~ y) : p ▹ f x ~ f y :=
      by induction p using elim; rewrite subst_β

    definition apd_β {P : X → Fib} (f : Π x, P x) {x y : X} :
      apd f (refl x) = #eq.ops eq.symm (subst_β _) ▹ refl (f x) := elim_β _

  end ap

  definition eq_transport_l {a₁ a₂ a₃ : X} (p : a₁ ~ a₂) (q : a₁ ~ a₃) :
    p ▹ q ~ p⁻¹ ⬝ q :=
  by induction p using elim; induction q using elim; simp

  definition eq_transport_r {a₁ a₂ a₃ : X} (p : a₂ ~ a₃) (q : a₁ ~ a₂) :
    p ▹ q ~ q ⬝ p :=
  by induction p using elim; induction q using elim; simp

  definition strict_eq_fib_eq { x y : X} : x = y -> x ~ y :=
  eq.rec (refl _)

end fib_eq

open fib_eq

variables {A: Fib}
variables {B: Fib}
variables {C: Fib}


structure is_contr (X : Type)[is_fibrant X] := mk ::
  (center : X)
  (contraction : Π (x : X), center ~ x)

open sigma.ops is_contr

definition is_contr_equiv [instance] {X : Type}[is_fibrant X] :
  (Σ (c : X), Π (x : X), c ~ x) ≃ₛ is_contr X :=
  equiv.mk
    (λ a, is_contr.mk a.1 (λx, a.2 x))
    (λ a, ⟨center a,(λx, contraction a x)⟩)
    (λ a, by cases a; reflexivity)
    (λ a, by cases a; reflexivity)

definition is_contr_is_fibrant [instance] (X : Type)[is_fibrant X] : is_fibrant (is_contr X) :=
  equiv_is_fibrant is_contr_equiv

definition is_trunc : Π (n : ℕ)(X : Type) [is_fibrant X], Type
| @is_trunc 0 X fib := is_contr X
| @is_trunc (nat.succ n) X fib := Π (x y : X), is_trunc n (x ~ y)

definition is_prop (X : Type) [is_fibrant X] := Π (x y : X), x ~ y

section truncated_types
  variables (X : Fib)

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
  variables {X : Fib}
  definition singleton [reducible] (x : X) := Σ (y : X), y ~ x
  definition singleton_contr (x : X) : is_contr (singleton x) :=
    let l (y : X)(p : y ~ x) : ⟨x , refl x⟩ ~ ⟨y, p⟩ := elim !refl x p in
    is_contr.mk ⟨x, refl x⟩ (λt, match t with ⟨y, p⟩ := l y p end)
end singleton

section fib_equivalences
  variables {X Y : Type}(f : X → Y)[is_fibrant X][is_fibrant Y]

  definition fibre [reducible] (y : Y) := Σ (x : X), f x ~ y
  definition is_fib_equiv [reducible] [class] := Π (y : Y), is_contr (fibre f y)

  definition fib_equiv [reducible] (X Y : Type)[is_fibrant X][is_fibrant Y] : Type :=
    Σ (f : X → Y), is_fib_equiv f

  definition id_is_fib_equiv {X : Type}[is_fibrant X] : is_fib_equiv (@id X) := singleton_contr

  notation X `≃` Y := fib_equiv X Y

  definition coerce {X Y : Fib} : X ~ Y → X → Y := elim id Y
  definition coerce_is_fib_equiv [instance] {X Y : Fib}(p : X ~ Y) : is_fib_equiv (coerce p) :=
    begin
      induction p using elim,
      unfold coerce, rewrite elim_β,
      apply id_is_fib_equiv
    end

  definition coerce_fib_equiv {X Y : Fib}(p : X ~ Y) : X ≃ Y := ⟨ coerce p, _ ⟩

end fib_equivalences


definition Univalence := Π {X Y : Fib}, is_fib_equiv (@coerce_fib_equiv X Y)


definition fibreₛ [reducible] {X Y : Type} (f : X → Y) (y : Y) := Σ (x : X), f x = y

open sigma.ops

definition fibre_projection {X : Type}{Y : X → Type}(x : X)
  : fibreₛ (λ (p : Σ (x : X), Y x), p.1) x ≃ₛ Y x
  := begin
      unfold fibreₛ, esimp,
      refine (equiv.mk _ _ _ _),
           { intro, cases a with [a₁, a₂], cases a₂, cases a₁, assumption},
           { intros, apply (⟨⟨x,a⟩, rfl⟩) },
           { unfold function.left_inverse, intro y,
             cases y with [y₁, y₂], cases y₁ with [z₁, z₂], esimp,
             esimp at *, congruence, cases y₂, congruence },
           {apply (λ x, rfl)}
     end

-- ref:def:fibration
definition is_fibration.{u} {E B : Type.{max 1 u}} (p : E → B) :=
  Σ (F : B → Fib.{u}), Π (b : B), F b ≃ₛ fibreₛ p b

definition is_fibration_alt [reducible] {E B : Type} (p : E → B) :=
  Π (b : B), is_fibrant (fibreₛ p b)
