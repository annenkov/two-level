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


namespace invcat
  open sigma.ops
  -- have to pack functor with the property that it reflects identities,
  -- because functor itself is not a type class
  -- CAVEAT: this is not really "identity reflection" (because we don't
  -- require φ(f) to be an identity.), but for ℕop, this will be automatic.
  -- Maybe rename the property?
  structure has_idreflect [class] (C D : Category) :=
    (φ : C ⇒ D)
    (id_reflect : Π ⦃x y : C⦄, φ x = φ y → (Σ (p : x = y), Π (f : x ⟶ y), p ▹ f = id))  

  structure invcat [class] (C : Category):=
    (id_reflect_ℕop : has_idreflect C ℕop)

  open invcat function

  definition endomorphism_is_id {C : Category} [invC : invcat C] {c : C} (f : c ⟶ c) : f = id :=
  begin cases invC with H, cases H with [φ, id_r], apply (id_r rfl).2 end
  
  lemma idreflect_inj {C : Category} [idr : has_idreflect C ℕop] : injective (has_idreflect.φ C ℕop) := 
    begin cases idr with [φ, idr_φ], esimp, unfold injective, intros x y H, cases (idr_φ H), assumption end
end invcat

open invcat
open unit

definition triv_funct : Category_one ⇒ ℕop :=
  functor.mk (λ (x : unit), zero) (λ a b p, id) (λa, eq.refl _) (λa b c p q, eq.refl _)

definition triv_funct_id_reflect [instance] : has_idreflect Category_one ℕop :=
  has_idreflect.mk
    triv_funct
    begin
      intros x y Heq,
      cases x, cases y,      
      existsi (eq.refl _), intro f, 
      cases f, reflexivity
    end

definition triv_cat_inverse [instance] : invcat Category_one := invcat.mk _
