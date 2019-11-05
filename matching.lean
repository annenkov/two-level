import algebra.category
import inverse limit fibrant finite

open sigma category eq.ops function

-- Lean's types are pretypes in our formalisation, so the category of types [Types_category] from the standard library is actually the category of pretypes.
definition Uₛ := category.Type_category

namespace reduced_coslice
  structure coslice_obs {ob : Type} (C : category ob) (a : ob) :=
  (to  : ob)
  (hom_to : hom a to)

  open coslice_obs

  structure red_coslice_obs {A : Type} (C : category A) (c : A) extends coslice_obs C c :=
  (rc_non_id_hom : Π (p : c = to), not (p ▹ hom_to = category.id))


  definition reduced_coslice {ob : Type} (C : category ob) (c : ob) : category (red_coslice_obs C c) :=
    ⦃ category,
      hom := λa b, Σ(g : hom (to a) (to b)), g ∘ hom_to a = hom_to b,
      comp := λ a b c g f,
        ⟨ (pr1 g ∘ pr1 f),
          (show (pr1 g ∘ pr1 f) ∘ hom_to a = hom_to c,
            proof
            calc
              (pr1 g ∘ pr1 f) ∘ hom_to a = pr1 g ∘ (pr1 f ∘ hom_to a): eq.symm !assoc
                ... = pr1 g ∘ hom_to b : {pr2 f}
                ... = hom_to c : {pr2 g}
            qed) ⟩,
      ID := (λ a, ⟨ id, !id_left ⟩),
      assoc := (λ a b c d h g f, dpair_eq !assoc    !proof_irrel),
      id_left := (λ a b f,       sigma.eq !id_left  !proof_irrel),
      id_right := (λ a b f,      sigma.eq !id_right !proof_irrel) ⦄

  -- ref:def:reduced-coslice
  -- Definition 3.7
  definition ReducedCoslice (C : Category) (c : C) := Mk (reduced_coslice C c)

  notation c `//` C := ReducedCoslice C c

  open functor

  definition forget (C : Category) (c : C) : (c // C) ⇒ C :=
    ⦃ functor,
      object := λ a, to a,
      morphism := λ a b f, pr1 f,
      respect_id := λa, eq.refl _,
      respect_comp := λ a b c f g, eq.refl _ ⦄

end reduced_coslice

open reduced_coslice
open invcat

open functor

-- ref:def:matching-object
-- Definition 3.11
namespace matching_object

  open poly_unit reduced_coslice.red_coslice_obs reduced_coslice.coslice_obs

  definition matching_object.{u} {C : Category.{1 1}} [invcat C] (X : C ⇒ Type_category.{u}) (z : C) :=
    --limit_obj (limit_in_pretype (X ∘f (forget C z)))
    Nat(𝟙, (X ∘f (forget C z)))

  definition matching_obj_map {C : Category.{1 1}} [invC : invcat C] (X : C ⇒ Type_category) (z : C) :
    X z → matching_object X z :=
    begin
      intros x, unfold matching_object, unfold forget, unfold functor.compose,
      refine natural_transformation.mk (λ a u, X (hom_to a) x) _,
      { intros, esimp, rewrite id_right, cases f with [f_hom, tr], apply funext, intro y,
        esimp at *,
        unfold red_coslice_obs.to_coslice_obs at *, rewrite -tr,
        apply eq.symm, apply happly (respect_comp X f_hom (hom_to a)) x }
    end
  open natural_transformation

  definition nat_map_matching_obj_map {C : Category.{1 1}} [invC : invcat C] (X : C ⇒ Type_category) (z : C) (x : X z) :
  natural_map (matching_obj_map X z x) = (λ a u, X (hom_to a) x) :=
  begin
    reflexivity
  end

end matching_object

namespace reedy
  universe variable u
  variables {C : Category.{1 1}} [invcat C]

  open matching_object

  -- ref:def:reedy-fibration
  -- Definition 3.12
  definition is_reedy_fibrant [class] (X : C ⇒ Uₛ) :=
    Π z, is_fibration_alt (matching_obj_map X z)
end reedy
