import data.equiv .facts

open eq

-- we use the isomorphism definition from the standard library
notation X `≃` Y := equiv X Y
constant is_fibrant' : Type → Prop

structure is_fibrant [class] (X : Type) := mk ::
  fib_internal : is_fibrant' X

constant equiv_is_fibrant {X Y : Type}(e : X ≃ Y)[fib : is_fibrant X] : is_fibrant Y

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

-- the inner equality (or path-equality) type (in the sense of HoTT)
namespace fib_eq
  infix ` =ᵒ `:28 := fib_eq
  constant reflo {X : Type}[is_fibrant X](x : X) : x =ᵒ x
  notation ` reflᵒ ` := reflo

  constant elimo {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x =ᵒ y → Type}
                [Π (y : X)(p : x =ᵒ y), is_fibrant (P y p)]
                (d : P x (reflᵒ x)) : Π (y : X)(p : x =ᵒ y), P y p
  notation ` elimᵒ ` := elimo

  constant elimo_β {X : Type}[is_fibrant X]{x : X}{P : Π (y : X), x =ᵒ y → Type}
                [Π (y : X)(p : x =ᵒ y), is_fibrant (P y p)]
                (d : P x (reflᵒ x)) : elimᵒ d x (reflᵒ x) = d

  notation ` elim_βᵒ ` := elimo_β

  definition idp [reducible] [constructor] {X : Type}[is_fibrant X] {a : X} := reflo a

  attribute elimo_β [simp]
  attribute elimo [recursor]
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

  attribute reflo [refl]
  definition symm [symm] {x y : X} : x =ᵒ y → y =ᵒ x :=
    elimᵒ (reflᵒ x) y
  definition symm_β [simp] {x : X} : symm (reflᵒ x) = reflᵒ x :=
    elim_βᵒ (reflᵒ x)
  definition trans [trans] {x y z : X} : x =ᵒ y → y =ᵒ z → x =ᵒ z := λ p,
    elimᵒ p z

  definition trans_β [simp] {x y : X}(p : x =ᵒ y) : trans p (reflᵒ y) = p :=
    elim_βᵒ p

  definition trans_β' [simp] {x : X} : trans (reflᵒ x) (reflᵒ x) = reflᵒ x := by simp

  definition trans' {x y z : X} (p : x =ᵒ y) (q : y =ᵒ z) : x =ᵒ z :=
    (elimᵒ (elimᵒ idp z) y) p q

  -- Alternative proof of transitivity using tactics.
  definition trans'' {x y z : X} (p: x =ᵒ y) (q : y =ᵒ z) : x =ᵒ z :=
  by induction p using elimo; exact q

  definition transport [subst] {x y : X}{P : X → Type}[Π (x : X), is_fibrant (P x)]
                           (p : x =ᵒ y)(d : P x) : P y :=
    elimᵒ d y p
  definition transport_β [simp] {x : X}{P : X → Type}[Π (x : X), is_fibrant (P x)](d : P x) :
                     transport (reflᵒ x) d = d :=
    elim_βᵒ d

  notation p ▹ d := transport p d

  infixl ⬝ := trans
  postfix ⁻¹ := symm

  definition symm_trans {x y : X} (p : x =ᵒ y) : p⁻¹ ⬝ p =ᵒ reflᵒ y :=
  by induction p using elimo; simp

  definition symm_trans_β {x : X} : (reflᵒ x)⁻¹ ⬝ (reflᵒ x) = reflᵒ x := by simp

  definition assoc_trans {x y z t: X} (p : x =ᵒ y) (q : y =ᵒ z) (r : z =ᵒ t) :
    (p ⬝ (q ⬝ r)) =ᵒ ((p ⬝ q) ⬝ r) :=
  by induction r using elimo; simp

  definition transport_trans {A : Fib } {a b c: A} {P : A → Fib}
    (p : a =ᵒ b) (q : b =ᵒ c) (u : P a) : #fib_eq q ▹ (p ▹ u) =ᵒ p ⬝ q ▹ u :=
    by induction p using elimo; induction q using elimo; simp

   definition eq_transport_l {a₁ a₂ a₃ : X} (p : a₁ =ᵒ a₂) (q : a₁ =ᵒ a₃) :
   p ▹ q =ᵒ p⁻¹ ⬝ q :=
   by induction p using elimo; induction q using elimo; simp

   definition eq_transport_r {a₁ a₂ a₃ : X} (p : a₂ =ᵒ a₃) (q : a₁ =ᵒ a₂) :
   p ▹ q =ᵒ q ⬝ p :=
   by induction p using elimo; induction q using elimo; simp

   definition to_fib_eq { x y : X } : x = y -> x =ᵒ y := eq.rec (reflᵒ _)

  namespace ap
    -- action on paths

    -- notation for the transport along the strict equality
    notation p `▹s` x := eq.rec_on p x


    definition ap {x y : X} (f : X -> Y) : x =ᵒ y -> f x =ᵒ f y :=
      elimᵒ (reflᵒ _) _

    definition ap_β [simp] {x : X} (f : X -> Y) : ap f (reflᵒ x) = reflᵒ (f x) := elim_βᵒ (reflᵒ (f x))

    definition ap_trans {x y z : X} (f : X → Y) (p : x =ᵒ y) (q : y =ᵒ z) :
      ap f (p ⬝ q) =ᵒ (ap f p) ⬝ (ap f q) := by induction p using elimo; induction q using elimo; simp

    definition ap_symm {x y : X} (f : X → Y) (p : x =ᵒ y) : ap f p⁻¹ =ᵒ (ap f p)⁻¹ :=
      by induction p using elimo; simp

    definition ap_compose {x y : X} (f : X → Y) (g : Y → Z) (p : x =ᵒ y) : ap g (ap f p) =ᵒ ap (g ∘ f) p :=
      by induction p using elimo; simp

    definition ap_id {x y : X} (p : x =ᵒ y) : ap id p =ᵒ p := by induction p using elimo; simp

    definition ap₂ [reducible] {x x' : X} {y y' : Y} (f : X -> Y -> Z)
      (p : x =ᵒ x') (q : y =ᵒ y') : f x y =ᵒ f x' y' := (ap (λ x, f x y) p) ⬝ (ap (f x') q)

    definition ap₂_β {x : X} {y : Y} (f : X -> Y -> Z) : ap₂ _ (reflᵒ x) (reflᵒ y) = reflᵒ (f x y) :=
      by simp

    definition apd {P : X → Fib} (f : Π x, P x) {x y : X} (p : x =ᵒ y) : p ▹ f x =ᵒ f y :=
      by induction p using elimo; rewrite transport_β

    definition apd_β {P : X → Fib} (f : Π x, P x) {x y : X} :
      apd f (reflᵒ x) = (eq.symm (transport_β _) ▹s reflᵒ (f x)) := elim_βᵒ _

    definition apd_β' {P : X → Fib} (f : Π x, P x) {x y : X} :
    ((transport_β (f x)) ▹s (apd f (reflᵒ x))) = reflᵒ (f x) :=
    by unfold apd; rewrite elimo_β; rewrite eq.transport_concat

  end ap

end fib_eq

open fib_eq

variables {A: Fib}
variables {B: Fib}
variables {C: Fib}


structure is_contr (X : Type)[is_fibrant X] := mk ::
  (center : X)
  (contraction : Π (x : X), center =ᵒ x)

open sigma.ops is_contr

definition is_contr_equiv [instance] {X : Type}[is_fibrant X] :
  (Σ (c : X), Π (x : X), c =ᵒ x) ≃ is_contr X :=
  equiv.mk
    (λ a, is_contr.mk a.1 (λx, a.2 x))
    (λ a, ⟨center a,(λx, contraction a x)⟩)
    (λ a, by cases a; reflexivity)
    (λ a, by cases a; reflexivity)

definition is_contr_is_fibrant [instance] (X : Type)[is_fibrant X] : is_fibrant (is_contr X) :=
  equiv_is_fibrant is_contr_equiv

definition is_trunc : Π (n : ℕ)(X : Type) [is_fibrant X], Type
| @is_trunc 0 X fib := is_contr X
| @is_trunc (nat.succ n) X fib := Π (x y : X), is_trunc n (x =ᵒ y)

definition is_prop (X : Type) [is_fibrant X] := Π (x y : X), x =ᵒ y

section truncated_types
  variables (X : Fib)

  definition is_contr_is_trunc :
    is_contr X → is_trunc 1 X :=
    assume c : is_contr X,
    let path (x y : X) : x =ᵒ y :=
        symm (is_contr.contraction c x) ⬝ is_contr.contraction c y in
    let l (x y : X)(p : x =ᵒ y) : path x y =ᵒ p :=
        elimᵒ (!symm_trans) y p in
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
  definition singleton [reducible] (x : X) := Σ (y : X), y =ᵒ x
  definition singleton_contr (x : X) : is_contr (singleton x) :=
    let l (y : X)(p : y =ᵒ x) : ⟨x , reflᵒ x⟩ =ᵒ ⟨y, p⟩ := elimᵒ !reflᵒ x p in
    is_contr.mk ⟨x, reflᵒ x⟩ (λt, match t with ⟨y, p⟩ := l y p end)
end singleton

section fib_equivalences
  variables {X Y : Type}(f : X → Y)[is_fibrant X][is_fibrant Y]

  definition fibre [reducible] (y : Y) := Σ (x : X), f x =ᵒ y
  definition is_fib_equiv [reducible] [class] := Π (y : Y), is_contr (fibre f y)

  definition fib_equiv [reducible] (X Y : Type)[is_fibrant X][is_fibrant Y] : Type :=
    Σ (f : X → Y), is_fib_equiv f

  definition id_is_fib_equiv {X : Type}[is_fibrant X] : is_fib_equiv (@id X) := singleton_contr

  notation X `≃` Y := fib_equiv X Y

  definition coerce {X Y : Fib} : X =ᵒ Y → X → Y := elimᵒ id Y
  definition coerce_is_fib_equiv [instance] {X Y : Fib}(p : X =ᵒ Y) : is_fib_equiv (coerce p) :=
    begin
      induction p using elimo,
      unfold coerce, rewrite elimo_β,
      apply id_is_fib_equiv
    end

  definition coerce_fib_equiv {X Y : Fib}(p : X =ᵒ Y) : X ≃ Y := ⟨ coerce p, _ ⟩

end fib_equivalences


definition Univalence := Π {X Y : Fib}, is_fib_equiv (@coerce_fib_equiv X Y)

-- (strict) fibre
definition fibreₛ [reducible] {X Y : Type} (f : X → Y) (y : Y) := Σ (x : X), f x = y

open sigma.ops

definition fibre_projection {X : Type}{Y : X → Type}(x : X)
  : fibreₛ (λ (p : Σ (x : X), Y x), p.1) x ≃ Y x
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
-- Definition 3.7
definition is_fibration [reducible] {E B : Type} (p : E → B) :=
  Π (b : B), is_fibrant (fibreₛ p b)

definition is_fibration_alt.{u} {E B : Type.{max 1 u}} (p : E → B) :=
  Σ (F : B → Fib.{u}), Π (b : B), F b ≃ fibreₛ p b
