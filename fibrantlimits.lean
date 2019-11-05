import fibrant fibrantlimits_aux matching inverse algebra.category
       limit pullbacks finite
import data.fin

open invcat category functor matching_object Fib
     sigma.ops fincat natural_transformation eq

open equiv equiv.ops

namespace fiblimits
  universe variable u
  variables {C : Category.{1 1}}
            {D : Category}

  open subcat_obj reedy
  open sum nat fin function

  -- ref:thm:fibrant-limits
  -- Theorem 3.13
  definition fibrant_limit.{v}
    [invC : invcat C] [finC : is_obj_finite C]
    (X : C ⇒ Uₛ) (rfib : is_reedy_fibrant X) :
    is_fibrant (limit_obj (limit_in_pretype X)) :=
    begin
      cases finC with [n, ψ],
      revert ψ, revert rfib, revert invC, revert X, revert C,
      induction n with [n', IHn],
      { intros C X invC rfib ψ, apply equiv_is_fibrant.{v} (@fincat_0_limit_unit_equiv _ ψ X)⁻¹ },
      { intros C X invC rfib ψ, esimp,
        have inv_C : invcat C, from invC,
        cases invC, cases reflecting_id_ℕop with [φ, idrefl],
        -- choosing an element of C with maximal rank
        have H : Σ z, (Π (y : C), φ y ≤ φ z), from @max_fun_to_ℕ _ φ _ ψ,
        cases H with [z, z_max_φ],

        -- removing z from C and showing that the resulting category
        -- is still inverse and finite
        have invC' : invcat (C_without_z z), from C_without_z_invcat z,
        have finC' : C_without_z z ≃ₛ fin n', from @C_without_z_is_obj_finite _ _ _ _,


        -- using equivalences
        apply equiv_is_fibrant,
        apply equiv.symm nat_unit_sigma_equiv,

        let q := matching_obj_map X z,
        have fibration_q : (is_fibration_alt q), from rfib z,

        let p := map_L_to_Mz_alt z X,
        apply equiv_is_fibrant, apply equiv.symm,

        calc
                (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y')
             ≃ₛ (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
                 (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) × (Π (y y' : C_without_z z)
                 (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')) : limit_two_piece_limit_equiv ψ idrefl z_max_φ
                 /-- get a pullback of the span
                   [L --p--> matching_object M Z <<--q-- X z]
                   where L is the limit of X restricted to C_without_z
                   (so, L is Nat(𝟙,Functor_from_C' z X)) -/
         ... ≃ₛ (Σ (c_z : X z) d, p d = q c_z) : two_piece_limit_pullback_p_q_equiv
         ... ≃ₛ (Σ d (c_z : X z), p d = q c_z) : equiv.sigma_swap
         ... ≃ₛ (Σ d (c_z : X z), q c_z = p d) : by apply @sigma_congr₂; intros;
                                                     apply @sigma_congr₂; intros;
                                                     apply (iff_impl_equiv (iff.intro eq.symm eq.symm)),

        -- to show that this pullback is fibrant we use facts that q is a fibration (from Reedy fibrancy of X) and
        -- that L is fibrant (from IH)
        have rfibX' : is_reedy_fibrant (Functor_from_C' z X),
           from @Functor_from_C'_reedy_fibrant _ z X inv_C φ z_max_φ idrefl rfib ⟨_,ψ⟩,
        have isFibL: is_fibrant (lim_restricted X z),
           from @equiv_is_fibrant _ _ nat_unit_sigma_equiv (IHn _ _ _ _ _),
        refine @fibration_domain_is_fibrant _ (Fib.mk _ isFibL) (λpb, pb.1) _,
        refine Pullback'_is_fibrant q p, apply fibration_q
      }
    end
end fiblimits
