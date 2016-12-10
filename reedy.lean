import fibrant matching inverse algebra.category limit fibrantlimits data.fin finite

open invcat category functor matching_object Fib sigma.ops fincat natural_transformation eq

definition fib_category : category Fib :=
  ⦃ category,
    hom := λ a b, pretype a → pretype b,
    comp := λ a b c, function.comp ,
    ID := _,
    assoc := λ a b c d h g f, eq.symm (function.comp.assoc h g f),
    id_left := λ a b f,  function.comp.left_id f,
    id_right := λ a b f, function.comp.right_id f ⦄

definition FibCat := Mk fib_category

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

definition Subcat.{u v} (C : Category.{u v}) (p : C → Prop) : Category := Mk (subcat C p)

open equiv equiv.ops

section reedy
  universe variable u
  variables {C : Category.{1 1}}
            {D : Category}

  definition is_reedy_fibrant [class] (X : C ⇒ Type_category) [invcat C] :=
    Π z, is_fibration_alt (matching_obj_map X z)

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

  open eq.ops function
  definition C_without_z_invcat [instance] (z : C) [invC : invcat C] : invcat (C_without_z z) :=
    begin
      unfold C_without_z, cases invC, cases id_reflect_ℕop,
      refine invcat.mk (has_idreflect.mk _ _), apply Functor_from_C' z φ, intros,
      cases id_reflect f a with [p1, p2],
      refine ⟨_,_⟩,
      { cases x, cases y, congruence, apply p1 },
      { cases x, cases y, esimp at *, induction p1 using eq.drec, esimp at *, apply p2}
    end

  definition C_without_z_is_finite [instance] {n : ℕ} (z : C) [φ : objects C ≃ₛ fin (succ n)]
    {max_z : to_fun (fin (succ n)) z = maxi} : objects (C_without_z z) ≃ₛ fin n :=
    begin
      unfold C_without_z,
      cases φ with [f, g, l, r], esimp at *,
      have inj_f : injective f, from (injective_of_left_inverse l),
      unfold function.right_inverse at *, unfold function.left_inverse at *,
      refine equiv.mk _ _ _ _,
      { intro a, cases a with [c, p], esimp at *,
        have ne_maxi :  f c ≠ maxi, by refine (fincat_ne_maxi inj_f max_z p),
        apply lift_down (f c) ne_maxi },
      { intro i, unfold Mk, refine subcat_obj.mk (g (lift_succ i)) _, unfold ne, unfold not, intro a, rewrite -a at max_z,
        rewrite r at max_z, apply lift_succ_ne_max, assumption },
      { unfold function.left_inverse, intro, esimp, cases x with [c, p], congruence, esimp,
        have ne_maxi :  f c ≠ maxi, by refine (fincat_ne_maxi inj_f max_z p),
        rewrite lift_succ_lift_down_inverse, rewrite l },
      { unfold function.right_inverse, unfold function.left_inverse, intro, esimp,
        unfold lift_down, cases x, congruence, rewrite r}
    end

  definition no_incoming_non_id_arrows {n : ℕ} (z : C) {y : C} [φ : objects C ≃ₛ fin (nat.succ n)] [invC : invcat C]
    {max_z : to_fun (fin (nat.succ n)) z = maxi} : ¬ ∃ (f : y ⟶ z), y ≠ z :=
    begin cases invC, cases id_reflect_ℕop with [ψ, id_r], intro H, cases H with [f, p],
    assert H : to_fun (fin (succ n)) y ≠ to_fun (fin (succ n)) z,
      begin intro, apply p, apply injective_of_left_inverse (left_inv _ _), assumption end,
      rewrite max_z at H,
      have H' : to_fun (fin (succ n)) y < n, from lt_max_of_ne_max H,
      apply sorry
    end

  definition Functor_from_C'_reedy_fibrant (z : C) (X : C ⇒ Type_category) [invcat C] [rfibX : is_reedy_fibrant X]
    : is_reedy_fibrant (Functor_from_C' z X)  :=
      begin
        --cases rfibX,
        unfold is_reedy_fibrant at *, intro x,
        unfold is_fibration_alt at *, intro b,
        assert MO : matching_object X (obj x),
        begin
        apply sorry
        -- cases b with [η, NatSq],
        -- refine natural_transformation.mk _ _, intro o, esimp at *,
        end,
        assert isfibX' : is_fibrant (fibreₛ (matching_obj_map X (obj x)) MO), begin apply (rfibX x MO) end,
        assert MO_map : X x → matching_object X (obj x), begin apply sorry end,
        unfold fibreₛ, apply sorry
        --apply rfibX x MO,
      end

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
      -- match L with
      -- | natural_transformation.mk η NatSq :=
      -- refine allows to infer implicit argument for application of NatSq
      by cases L with [η, NatSq]; refine natural_transformation.mk
        (λ a u, η (mk (to a) (reduced_coslice_ne z a)) poly_unit.star)
        (λ a b f, begin apply funext, intro, cases x, refine happly (NatSq _) poly_unit.star end)
        --funext (λ u, happly (NatSq f.1) poly_unit.star))
  --end

  -- explicit representation of the limit of X restricted to category C without z
  definition lim_restricted [reducible] (X : C ⇒ Type_category) (z : C) [invC : invcat C]
  := Σ (c : Π y, (Functor_from_C' z X) y),
        Π (y y' : C_without_z z) (f : @hom (subcat_obj C _) _ y y'),
          ((Functor_from_C' z X) f) (c y) = c y'

  -- map from limit of X restricted to C' where we use explicit representation of limit L
  definition map_L_to_Mz_alt (z : C) (X : C ⇒ Type_category.{u}) [invC : invcat C]
  (L : lim_restricted X z) : matching_object X z :=
    match L with
    | ⟨η, NatSq⟩ :=
    by refine natural_transformation.mk
    (λ a u, η (mk _ (reduced_coslice_ne z a)))
    (λ a b f, funext (λ u, NatSq _ _ _))
  end

  definition lift_to_rc [reducible] {z : C} (y : C_without_z z) (f : z ⟶ obj y): z//C :=
    red_coslice_obs.mk (obj y) f (λ p a, prop y p⁻¹)

  definition singleton_contr_fiberₛ {E B : Type} {p : E → B} : (Σ b, fibreₛ p b) ≃ₛ E :=
  begin
  refine equiv.mk (λ (p' : (Σ b, fibreₛ p b)), p'.2.1) (λ e, ⟨p e, ⟨e,rfl⟩⟩) _ (λx, rfl),
  unfold function.left_inverse, intros, cases x with [p1, p2], cases p2 with [p21,p22],
  esimp, induction p22 using eq.drec, congruence
  end

  set_option formatter.hide_full_terms false
  -- set_option pp.binder_types true
  -- set_option pp.universes true
  -- set_option pp.notation true

  definition lemma1 [invC : invcat C] {X : C ⇒ Type_category} {z : C}
    {y : C_without_z z} {f : z ⟶ obj y}
    {c : Π y : C_without_z z, X (obj y) }
    { Heq' : ∀ (y y' : C_without_z z) (f : @hom (subcat_obj C _) _ y y'), morphism (Functor_from_C' z X) f (c y) = c y'} :
      natural_map (map_L_to_Mz_alt z X ⟨c,Heq'⟩) (lift_to_rc y f) poly_unit.star = c y :=
      begin unfold map_L_to_Mz_alt, unfold natural_map, cases y, esimp
      end

  definition map_from_span_p_q [invC : invcat C] [finC : is_finite C] (X : C ⇒ Type_category.{u}) (z : C)
  (w : Σ (c_z : X z) d, !map_L_to_Mz_alt d = !matching_obj_map c_z):
  ((Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
  (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
  (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')))
   :=
  begin
    cases w with [c_z, Hs], cases Hs with [d, Heq], unfold lim_restricted at d, cases d with [c, Heq'], existsi c_z, existsi c,
    have H: natural_map (!map_L_to_Mz_alt ⟨c, Heq'⟩) = natural_map (!matching_obj_map c_z), from natural_map_eq Heq,
     unfold map_L_to_Mz_alt at H, unfold natural_map at H, unfold matching_obj_map at H,
    split,
    { apply sorry },
    { apply sorry}
  end

  definition fibration_domain_is_fibrant {E : Type} {B : Fib} (p : E → B) [isfibr_p : is_fibration_alt p]:
    is_fibrant E := @equiv_is_fibrant (Σ b x, p x = b) _ singleton_contr_fiberₛ _

  definition fibrant_limit [invC : invcat C] [finC : is_finite C] (X : C ⇒ Type_category.{u}) (rfib : is_reedy_fibrant X) :
    is_fibrant Nat(𝟙,X) :=
    begin
      cases finC with [n, φ],
      revert φ, revert rfib, revert invC, revert X, revert C,
      induction n with [n', IHn],
      { apply sorry},
      { intros C X invC rfib φ, esimp,
        -- choosing maximal element
        have H : Σ z, @to_fun _ (fin (succ n')) φ z = maxi, from ⟨inv_fun C maxi, right_inv _ _ _⟩,
        cases H with [z, z_max],
        -- removing z from C and showing that resulting category
        -- is still inverse and finite
        have invC' : invcat (C_without_z z), from C_without_z_invcat z,
        have finC' : C_without_z z ≃ₛ fin n', from @C_without_z_is_finite _ _ _ _ z_max,

        -- using equivalences
        apply equiv_is_fibrant,
        apply equiv.symm nat_unit_sigma_equiv,
        have Hq : Σ (q : X z → matching_object X z), (is_fibration_alt q × q = matching_obj_map X z),
                  from ⟨matching_obj_map X z, (rfib z, rfl)⟩, cases Hq with [q, H'], cases H' with [fibration_q, q_eq],
        have Hp : Σ p, p = map_L_to_Mz_alt z X,
                  from ⟨map_L_to_Mz_alt z X, rfl⟩, cases Hp with [p, p_eq],
        apply equiv_is_fibrant, apply equiv.symm,

        calc
         (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y')
             ≃ₛ (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)), (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
             (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')) :
                begin refine equiv.mk _ _ _ _,
                { intro, cases a with [p1, p2], refine ⟨p1 z, ⟨λ y, p1 y,(λ y' f, p2 z y' f, λ y y' f, p2 y y' f)⟩⟩ },
                { intro, cases a with [c_z, p'], cases p' with [p2, p3], cases p3 with [l_z, l_y], refine ⟨_,λ y y' f, _⟩, intro y'',
                  have Heq : decidable (y'' = z), from @fincat.has_decidable_eq _ (⟨_,φ⟩) _ _,
                  cases Heq with [y_eq_z, y_ne_z],
                  { rewrite y_eq_z, assumption },
                  { refine p2 (mk y'' _), assumption },
                  intros,
                  -- now, we have 4 cases to consider: y=z, y≠z, y'=z, y'≠z
                  cases @fincat.has_decidable_eq C (⟨_,φ⟩) y  z with [y_eq_z, y_ne_z]:
                  cases @fincat.has_decidable_eq C (⟨_,φ⟩) y' z with [y'_eq_z, y'_ne_z],
                  { cases y_eq_z, cases y'_eq_z, esimp, rewrite (endomorphism_is_id f), refine happly (respect_id _ _) _},
                  { cases y_eq_z, esimp, apply l_z},
                  { cases y'_eq_z, esimp, exfalso, apply (@no_incoming_non_id_arrows _ n' z y φ), assumption, existsi f, assumption },
                  { esimp, apply l_y },
                },
                { unfold left_inverse, esimp, intros, cases x with [x, H], esimp, congruence, apply funext, intro y,
                cases @fincat.has_decidable_eq C (⟨_,φ⟩) y  z with [y_eq_z, y_ne_z],
                {cases y_eq_z, esimp }, {esimp }},
                { unfold right_inverse, unfold left_inverse, esimp, intro y, cases y with [c_z, Hs],
                esimp, cases Hs with [p1, p2], esimp, cases p2, esimp,
                cases (@has_decidable_eq C ⟨succ n', φ⟩ z z), esimp, congruence, apply sigma_eq_congr,
                refine ⟨_,_⟩,
                { apply funext, intro y',
                  cases @fincat.has_decidable_eq C (⟨_,φ⟩) y' z with [y'_eq_z, y'_ne_z], esimp,
                  cases y' with [y'', p'], esimp at *, exfalso, apply p', apply y'_eq_z,
                  esimp, cases y', congruence },
                { apply sorry  },
                 apply sorry},
                end
         -- ... ≃ₛ (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)) (d : Nat(𝟙,Functor_from_C' z X)),
         --                 Π (y : C_without_z z) f, X f c_z = c y) : sorry
         -- get a pullback of the span (L --p--> matching_object M Z <<--q-- X z)
         -- where L is limit of X restricted to C_without_z (so, L is Nat(𝟙,Functor_from_C' z X))
         ... ≃ₛ (Σ (c_z : X z) d, p d = q c_z) :
         begin
         refine @sigma_congr₂ _ _ _ _, intro c_z,
         refine equiv.mk _ _ sorry sorry,
         { intro w, refine ⟨_,_⟩, refine ⟨w.1, prod.pr2 w.2⟩, rewrite p_eq,
           unfold map_L_to_Mz_alt, rewrite q_eq,
           refine nat_trans_eq, unfold natural_map,
           apply funext, intro y, apply funext, intro u, unfold matching_obj_map,
           esimp, cases w with [c,p2], cases p2 with [p_l, p_r], esimp at *, symmetry,
           apply (p_l (subcat_obj.mk (to y) (reduced_coslice_ne z y)) (hom_to y)) },
         { apply sorry }
         end
         ... ≃ₛ (Σ d (c_z : X z), q c_z = p d) : sorry,

        -- to show that this pullback is fibrant we use facts that q is a fibration (from Reedy fibrancy of X) and
        -- that L is fibrant (from IH)
        have rfibX' : is_reedy_fibrant (Functor_from_C' z X), from sorry,
        assert isFibL: is_fibrant (lim_restricted X z),
          begin
          -- TODO: something in this proof causes the error with message about metavariables
          refine (@equiv_is_fibrant _ _ nat_unit_sigma_equiv _), apply IHn, apply rfibX', apply finC'
          end,
        refine @fibration_domain_is_fibrant _ (Fib.mk _ isFibL) (λpb, pb.1) _,
        refine Pullback'_is_fibrant q p, apply fibration_q
      }
    end
end reedy
