-- inverse categories
import algebra.category
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
  -- have to pack functor with the property that it reflects identities,
  -- because functor itself is not a type class
  structure has_idreflect [class] (C D : Category) :=
    (φ : C ⇒ D)
    (id_reflect : Π ⦃x y : C⦄ (f : x ⟶ y), φ x = φ y → (Σ (p : x = y), p ▹ f = id))

  structure invcat [class] (C : Category):=
    (id_reflect_ℕop : has_idreflect C ℕop)

end invcat

open invcat
open unit

definition trivial_cat [instance] : category unit :=
  ⦃ category,
    hom := λ a b, unit,
    comp := (λ a b c q p, ⋆),
    ID := id,
    assoc := λ a b c p q h g, eq.refl _,
    id_left := (λ a b f, unit.rec_on f (eq.refl _)),
    id_right :=(λ a b f, unit.rec_on f (eq.refl _))⦄

definition TrivCat := Mk trivial_cat

definition triv_funct : TrivCat ⇒ ℕop :=
  functor.mk (λ (x : unit), zero) (λ a b p, id) (λa, eq.refl _) (λa b c p q, eq.refl _)

definition triv_funct_id_reflect [instance] : has_idreflect TrivCat ℕop :=
  has_idreflect.mk
    triv_funct
    begin
      intros x y f Heq,
      cases x, cases y, cases f,
      existsi (eq.refl _), reflexivity
    end

definition triv_cat_inverse [instance] : invcat TrivCat := invcat.mk _
