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
            {D : Category}

  definition is_reedy_fibrant (X : C ⇒ Type_category.{max 1 u}) [invcat C] := 
    Π z, is_fibration_alt (matching_obj_map.{u} X z)

  open nat fin subcat_obj

  definition C_without_z (z : C) : Category := Mk (subcat C (λ c, c ≠ z))

  -- (Danil) I have to use apply tactic, as it allows to infer correct implicits
  definition Functor_from_C' [reducible] [unfold_full] (z : C) (X : C ⇒ D) : C_without_z z ⇒ D :=
  ⦃ functor,
    object := λ ob, X (obj ob),
    morphism := λ a b f, by apply X f,
    respect_id := λ a, by apply respect_id X (obj a),
    respect_comp := λ a b c g f, by apply @respect_comp _ _ X (obj a) (obj b) (obj c) _ _
  ⦄
  set_option pp.binder_types true
  open eq.ops
  definition C_without_z_invcat (z : C) [invC : invcat C]: invcat (C_without_z z) :=
    begin
      unfold C_without_z, cases invC, cases id_reflect_ℕop,
      refine invcat.mk (has_idreflect.mk _ _), apply Functor_from_C' z φ, intros,
      cases id_reflect f a with [p1, p2], 
      refine ⟨_,_⟩, 
      { cases x, cases y, congruence, apply p1 },
      { cases x, cases y, esimp at *, induction p1 using eq.drec, esimp at *, apply p2}
    end

  -- definition Functor_from_C'_reedy_fibrant (z : C) (X : C ⇒ Type_category) [invcat C] {rfibX : is_reedy_fibrant X} 
  --   : is_reedy_fibrant (Functor_from_C' z X)  := sorry

  open poly_unit
  open reduced_coslice
  open reduced_coslice.red_coslice_obs

  -- for any object "a" from z//C (which is an arrow z⟶y with extra property) we show that codomain y cannot be z
  -- we show it using definition of reduced coslice and fact that C is an inverse category
  definition reduced_coslice_ne (z : C) (a : z//C) [invC : invcat C] : to a ≠ z :=
  begin
    cases a with [y, c_hom_to, f_not_id], esimp at *,
    intro p, cases p,
    apply f_not_id rfl,
    cases invC, cases id_reflect_ℕop,
    apply (id_reflect c_hom_to rfl).2
  end

  -- map from limit of X restricted to C'
  definition map_L_to_Mz (z : C) (X : C ⇒ Type_category) [invC : invcat C]
    (L : cone_with_tip (Functor_from_C' z X) poly_unit) : matching_object X z :=
      match L with
      | natural_transformation.mk η NatSq :=
      -- refine allows to infer implicit argument for application of NatSq
      by refine natural_transformation.mk
        (λ a u, η (mk (to a) (reduced_coslice_ne z a)) poly_unit.star)
        (λ a b f, funext (λ u, happly (NatSq f.1) star))
  end

  definition singleton_contr_fiberₛ {E B : Type} {p : E → B} : (Σ b, fibreₛ p b) ≃ₛ E := 
  begin 
  refine equiv.mk (λ (p' : (Σ b, fibreₛ p b)), p'.2.1) (λ e, ⟨p e, ⟨e,rfl⟩⟩) _ (λx, rfl),
  unfold function.left_inverse, intros, cases x with [p1, p2], cases p2 with [p21,p22], 
  esimp, induction p22 using eq.drec, congruence
  end

  definition fibration_domain_is_fibrant {E : Type} {B : Fib} (p : E → B) (isfibr_p : is_fibration_alt p ):
    is_fibrant E :=
    begin 
      unfold is_fibration_alt at *, unfold fibreₛ at *,
      apply equiv_is_fibrant, apply singleton_contr_fiberₛ,
      have H : is_fibrant (Σ b, Σ x, p x = b), from _, apply H      
    end

  notation `Nat` `(` F `,` G `)` := F ⟹ G
  definition one_funct {C : Category} := const_funct_obj C Type_category poly_unit
  notation `𝟙` := one_funct

  definition fibrant_limit [invC : invcat C] [finC : is_finite C] (X : C ⇒ Type_category.{max 1 u}) (rfib : is_reedy_fibrant.{u} X) :
    is_fibrant Nat(𝟙,X) :=
    begin
      cases finC with [n, φ],
      revert φ, revert rfib, revert invC, revert X, revert C,
      induction n with [n', IHn],
      { apply sorry},
      { intros C X invC rfib φ, esimp,
        -- choosing maximal element
        have H : Σ z, φ ∙ z = maxi, from ⟨inv_fun C maxi, right_inv _ _ _⟩,
        cases H with [z, z_max],
        -- removing z from C and showing that resulting category
        -- is still inverse and finite
        have invC' : invcat (C_without_z z), from C_without_z_invcat z,
        have finC' : C_without_z z ≃ₛ fin n', from sorry,        

        -- using equivalences
        apply equiv_is_fibrant,
        apply (equiv.symm nat_unit_sigma_equiv.{u}),
        have Hq : Σ (q : X z → matching_object X z), is_fibration_alt q, 
                  from ⟨matching_obj_map X z, rfib z⟩, cases Hq with [q, fibration_q],
        have Hp : Σ (p : Nat(𝟙, Functor_from_C' z X) → matching_object X z), p = map_L_to_Mz z X, 
                  from ⟨map_L_to_Mz z X, rfl⟩, cases Hp with [p, p_eq],        
        apply equiv_is_fibrant, apply equiv.symm,
        
        calc
         (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y') 
             ≃ₛ (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)), (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
                (Π (y y' : C_without_z z) (f : y ⟶ y'), X f (c y) = c y')) : sorry
         ... ≃ₛ (Σ (d : Nat(𝟙,Functor_from_C' z X)) (c_z : X z), q c_z = p d) : sorry,
        
        have rfibX' : is_reedy_fibrant (Functor_from_C' z X), from sorry,
        assert isFibL: is_fibrant Nat(𝟙,Functor_from_C' z X), begin apply IHn, apply rfibX', apply finC' end,
        refine @fibration_domain_is_fibrant _ (mk _ isFibL) (λpb, pb.1) _, refine Pullback'_is_fibrant.{u} q p, apply fibration_q 
      }
    end
end reedy
