-- inverse categories

import algebra.category data.nat
import algebra.category.constructions

import .fibrant .finite

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
-- Definition 4.1
namespace invcat
  open sigma.ops iff
  definition id_reflect {C D: Category} (φ : C ⇒ D) :=
    Π ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id

  definition id_reflect' {C D: Category} :=
  Π (φ : C ⇒ D) ⦃x y : C⦄ (f : x ⟶ y), (Σ (q : φ x = φ y), q ▹ φ f = id) → Σ (p : x = y),  p ▹ f = id

  definition transport {A : Type} := @eq.rec_on A
  notation x ≡ y := eq x y

  definition id_reflect'' {C D: Category} :=
  Π (φ : C ⇒ D) {x y : C} (f : hom x y),
  (Σ (q : φ y ≡ φ x), transport q (φ f) ≡ id) → Σ (p : y ≡ x),
  @transport _ _ _ _ p f ≡ id


  -- definition if "refect identity" property specific to ℕop.
  -- Though this definition doesn't require for φ(f) to be an identity, we will show that
  -- id_reflect(C,ℕop) and id_reflect_ℕop(C) are logically equivalent
  definition id_reflect_ℕop {C : Category} (φ : C ⇒ ℕop) :=
    Π ⦃x y : C⦄ (f : x ⟶ y), φ x = φ y → (Σ (p : x = y), p ▹ f = id)

  definition id_reflect_ℕop' {C : Category} (φ : C ⇒ ℕop) :=
    Π {x y : C} (f : x ⟶ y),
    φ x ≡ φ y → (Σ (p : x ≡ y), transport p f ≡ id)

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

end invcat

-- some facts about inverse categories
section invcat_facts
  open invcat function sigma.ops

  definition endomorphism_is_id {C : Category} [invC : invcat C] {c : C} (f : c ⟶ c) : f = id :=
  begin cases invC with H, cases H with [φ, id_r], apply (id_r f ⟨rfl,rfl⟩).2 end

  lemma idreflect_inj_hom {C : Category} {x y : C} [idr : has_idreflect C ℕop] (f : x ⟶ y) :
    (has_idreflect.φ C ℕop) x = (has_idreflect.φ C ℕop) y → x = y :=
    begin cases idr with [φ, idr_φ], esimp, intro  H, cases (idr_φ f ⟨H,rfl⟩), assumption end

  definition has_le_ℕop [instance] : has_le ℕop := nat_has_le
  definition has_lt_ℕop [instance] : has_lt ℕop := nat_has_lt

  definition strict_order_ℕop [instance] : strict_order ℕop :=
    strict_order.mk nat.lt begin intros, refine (@lt.irrefl ℕ _ a a_1) end
    begin intros a b c, apply nat.lt_trans end

  definition weak_order_ℕop [instance] : weak_order ℕop :=
    weak_order.mk nat.le (@le.refl ℕ _) (λ a b c, @nat.le_trans a b c) (λ a b, nat.le_antisymm)

  definition no_incoming_non_id_arrows {C : Category.{1 1}}
    (z : C) {φ : C ⇒ ℕop} {max_rank : ∀ y, φ y ≤ φ z} {reflecting_id : id_reflect φ}
    : ¬ ∃ y : C, ∃ (f : y ⟶ z), y ≠ z :=
    begin intro H, cases H with [y, s], cases s with [f, y_ne_z], unfold id_reflect at *,
      have H : φ y ≥ φ z, from φ f,
      cases reflecting_id f ⟨le.antisymm (max_rank y) H, rfl⟩ with [p, Heq],
      apply y_ne_z, assumption
    end
end invcat_facts

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

structure subcat_obj (C : Category) (p : objects C → Prop) :=
  (obj : objects C)
  (prop : p obj)

open subcat_obj function
attribute subcat_obj.obj [coercion]


section subcategory
  variables {C : Category.{1 1}}
            {D : Category}

definition subcat [instance] (C : Category) (p : C → Prop) : category (subcat_obj C p) :=
  ⦃ category,
    hom := λ (a b : subcat_obj C p), obj a ⟶ obj b,
    comp := λ a b c, @comp _ _ _ _ _,
    ID := λ (a : subcat_obj C p), ID (obj a),
    assoc := λ a b c d h g f, assoc h g f,
    id_left := λ a b f, id_left f,
    id_right := λ a b f, id_right f ⦄

definition Subcat (C : Category) (p : C → Prop) : Category := Mk (subcat C p)


-- A subcategory of [C] with one object removed.
-- We also refer to this category as C'
definition C_without_z {C : Category.{1 1}}(z : C) : Category := Mk (subcat C (λ c, c ≠ z))

-- use apply tactic, as it allows to infer correct implicits
definition Functor_from_C' [reducible] (z : C) (X : C ⇒ D) : C_without_z z ⇒ D :=
 ⦃ functor,
   object := λ ob, X (obj ob),
   morphism := λ a b f, by apply X f,
   respect_id := λ a, by apply respect_id X (obj a),
   respect_comp := λ a b c g f, by apply @respect_comp _ _ X (obj a) (obj b) (obj c) _ _ ⦄

open eq.ops function
definition C_without_z_invcat [instance] (z : C) [invC : invcat C] : invcat (C_without_z z) :=
  begin
    unfold C_without_z, cases invC, cases reflecting_id_ℕop,
    refine invcat.mk (has_idreflect.mk _ _), apply Functor_from_C' z φ, intros x y f p,
    cases reflecting_id f p with [p1, p2],
    refine ⟨_,_⟩,
    { cases x, cases y, congruence, apply p1 },
    { cases x, cases y, esimp at *, induction p1 using eq.drec, esimp at *, apply p2}
  end

open equiv equiv.ops sigma sigma.ops

definition C_without_z_sigma_equiv {C : Category} (z : C) : C_without_z z ≃ Σ (c : C), c ≠ z :=
equiv.mk (λ c', ⟨obj c', prop c'⟩) (λc, mk c.1 c.2) begin intros, cases x, esimp, end begin intros, cases x, esimp end

definition C_without_z_is_obj_finite [instance] {n : ℕ} (z : C) [φ : objects C ≃ fin (nat.succ n)]
: objects (C_without_z z) ≃ fin n :=  (fincat.fincat_ob_remove_fin_equiv z) ∘ (C_without_z_sigma_equiv z)

end subcategory
