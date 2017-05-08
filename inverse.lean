-- inverse categories
import algebra.category
import algebra.category.constructions
import open nat

open nat.le functor
open category category.ops eq.ops

definition nat_cat_op [instance] : category ℕ :=
  ⦃ category,
    hom := λ a b, a ≥ b,
    comp := λ a b c, @nat.le_trans c b a,
    ID := nat.le_refl,
    assoc := λ a b c d h g f, eq.refl _,
    id_left := λ a b f, eq.refl _,
    id_right := λ a b f, eq.refl _ ⦄

definition ℕop := Mk nat_cat_op

lemma hom_ℕop_id {C : Category} {x : ℕop} {f : x ⟶ x} : f = id := rfl

-- ref:def:inverse-category
-- Definition 3.8
namespace invcat
  open sigma.ops iff
  definition id_reflect {C D: Category} (φ : C ⇒ D) :=
    Π ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id

  definition id_reflect' {C D: Category} :=
  Π (φ : C ⇒ D) ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id

  -- definition if "refect identity" property specific to ℕop
  -- though it doesn't require for φ(f) to be identity we will show, that
  -- id_reflect(C,ℕop) and id_reflect_ℕop(C) are logically equivalent
  definition id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop) :=
    Π ⦃x y : C⦄ (f : x ⟶ y), φ x = φ y → (Σ (p : x = y), p ▹ f = id)

  -- have to pack functor with the property that it reflects identities,
  -- because functor itself is not a type class
  structure has_idreflect [class] (C D : Category) :=
    (φ : C ⇒ D)
    (reflecting_id : id_reflect φ)

  section id_reflect_ℕop_iff

  -- showing that id_reflect_ℕop φ ↔ id_reflect φ
  -- NOTE: (Danil) I couldn't find instance of iff for Type

  definition map_id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop):
    id_reflect_ℕop φ → id_reflect φ :=
    begin
      intros id_r_ℕop x y f s, cases s with [q, Heq], cases id_r_ℕop f q with [p₁, p₂],
      existsi p₁, cases p₁, esimp at *, apply p₂
    end

  definition map_ℕop_id_reflect {C : Category} (φ : C ⇒ ℕop):
    id_reflect φ → id_reflect_ℕop φ :=
    begin intros id_r x y f q,
    -- here we use the fact that any morphism x ⟶ x in ℕop only can be an identity morphism
    have f_is_id : q ▹ morphism φ f = id, from rfl,
    cases id_r f ⟨q,f_is_id⟩ with [p₁, p₂], existsi p₁, cases p₁, esimp at *, apply p₂
    end

  end id_reflect_ℕop_iff

  structure invcat [class] (C : Category) :=
    (reflecting_id_ℕop : has_idreflect C ℕop)

  open invcat function

  definition endomorphism_is_id {C : Category} [invC : invcat C] {c : C} (f : c ⟶ c) : f = id :=
  begin cases invC with H, cases H with [φ, id_r], apply (id_r f ⟨rfl,rfl⟩).2 end

  lemma idreflect_inj_hom {C : Category} {x y : C} [idr : has_idreflect C ℕop] (f : x ⟶ y) :
    (has_idreflect.φ C ℕop) x = (has_idreflect.φ C ℕop) y → x = y :=
    begin cases idr with [φ, idr_φ], esimp, intro  H, cases (idr_φ f ⟨H,rfl⟩), assumption end

end invcat

open invcat
open unit

definition triv_funct : Category_one ⇒ ℕop :=
  functor.mk (λ (x : unit), zero) (λ a b p, id) (λa, eq.refl _) (λa b c p q, eq.refl _)

definition triv_funct_id_reflect [instance] : has_idreflect Category_one ℕop :=
  has_idreflect.mk
    triv_funct
    begin
      intros x y f,
      cases x, cases y, intro p,
      existsi (eq.refl _),
      cases f, reflexivity
    end

definition triv_cat_inverse [instance] : invcat Category_one := invcat.mk _
