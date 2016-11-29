import fibrant matching inverse algebra.category limit fibrantlimits data.fin

open invcat category functor matching_object Fib sigma.ops

definition fib_category : category Fib :=
  ⦃ category,
    hom := λ a b, pretype a → pretype b,
    comp := λ a b c, function.comp ,
    ID := _,
    assoc := λ a b c d h g f, eq.symm (function.comp.assoc h g f),
    id_left := λ a b f,  function.comp.left_id f,
    id_right := λ a b f, function.comp.right_id f ⦄

definition FibCat := Mk fib_category

definition is_finite [class] (C : Category) := Σ n, C ≃ₛ fin n

structure subcat_obj (C : Category) (p : objects C → Prop) :=
  (obj : objects C)
  (prop : p obj)

open subcat_obj
attribute subcat_obj.obj [coercion]

definition subcat [instance] (C : Category) (p : C → Prop) : category (subcat_obj C p) :=
  ⦃ category,
    hom := λ (a b : subcat_obj C p), obj a ⟶ obj b,
    comp := λ a b c, @comp _ _ _ _ _,
    ID := λ (a : subcat_obj C p), ID (obj a),
    assoc := λ a b c d h g f, assoc h g f,
    id_left := λ a b f, id_left f,
    id_right := λ a b f, id_right f ⦄


open equiv equiv.ops

section reedy
  universe variable u
  variables {C : Category.{1 1}}

  definition is_reedy_fibrant (X : C ⇒ Type_category.{max 1 u}) [invcat C] := Π z,
    is_fibration_alt (matching_obj_map.{u} X z)

  open nat fin subcat_obj
    
  definition C_without_z (z : C) : Category := Mk (subcat C (λ c, c ≠ z))
  
  
  -- (Danil) I have to use apply tactic, as it allows to infer correct implicits
  definition Functor_from_C' (z : C) (X : C ⇒ Type_category) : C_without_z z ⇒ Type_category :=
  ⦃ functor,
    object := λ ob, X (obj ob),
    morphism := λ a b f, by apply X f,
    respect_id := λ a, by apply respect_id X (obj a),
    respect_comp := λ a b c g f, by apply @respect_comp _ _ X (obj a) (obj b) (obj c) _ _
  ⦄

  definition fibrant_limit [invC : invcat C] [finC : is_finite C] (X : C ⇒ Type_category.{max 1 u}) (rfib : is_reedy_fibrant.{u} X) :
    is_fibrant (cone_with_tip X poly_unit) :=
    begin
      cases finC with [n, φ],
      induction n with [n', IHn],
      { apply sorry},
      { esimp,
        -- choosing maximal element
        have H : Σ z, φ ∙ z = maxi, from ⟨inv_fun C maxi, right_inv _ _ _⟩,
        cases H with [z, z_max],
        -- removing z from C and showing that resulting category
        -- is still inverse and finite
        have invC' : invcat (C_without_z z), from sorry,
        have finC' : is_finite (C_without_z z), from sorry,

        -- using equivalences
        apply equiv_is_fibrant,
        apply (equiv.symm nat_unit_sigma_equiv.{u}),        
        have 
        Hequiv : let C' := (C_without_z z) in 
         (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y') ≃
         (Σ (c_z : X z) (c : (Π y : C', X y)), (Π (y : C') (f : z ⟶ y ), X f c_z = c y) ×
         (Π (y y' : C') (f : y ⟶ y'), X f (c y) = c y')), from sorry,
                
        -- have PullbackEquiv : 
        --   let L := cone_with_tip (Functor_from_C' z X) poly_unit,
        --       p := sorry,
        --       q := sorry
        --   in
        --      (Σ (c_z : X z) (d : L), p d  = q c_z) ≃ₛ ... , from sorry,
        apply sorry }
    end
end reedy
