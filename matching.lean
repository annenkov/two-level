import algebra.category
import inverse limit fibrant

open sigma category eq.ops

namespace reduced_coslice
  structure coslice_obs {ob : Type} (C : category ob) (a : ob) := 
  (to  : ob)
  (hom_to : hom a to)

  open coslice_obs

  structure red_coslice_obs {A : Type} (C : category A) (c : A) extends coslice_obs C c :=   
  (rc_non_id_hom : Π (p : c = to), not (p ▹ hom_to = category.id))


  -- taken from commented out code in std library and modified
  -- coslice definition is the same, except type (category (coslice_obs C c))
  -- I couldn't find a way to parameterize the definition properly
  -- Could be some way to define reduced coslice as full subcategory of coslice
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
open invcat Fib

-- TODO: definition is exactly the same as for type_category
-- should be some way to avoid code repetition
definition fib_category : category Fib :=
  ⦃ category, 
    hom := λ a b, pretype a → pretype b,
    comp := λ a b c, function.comp ,
    ID := _,
    assoc := λ a b c d h g f, eq.symm (function.comp.assoc h g f),
    id_left := λ a b f,  function.comp.left_id f,
    id_right := λ a b f, function.comp.right_id f ⦄

definition FibCat := Mk fib_category

open functor

namespace matching_object
  
definition matching_object (C : Category) [invcat C] (X : C ⇒ FibCat) := 
  Π z, limit (X ∘f (forget C z))
end matching_object
