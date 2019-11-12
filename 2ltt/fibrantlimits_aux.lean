import .fibrant .matching .inverse algebra.category
       .limit .pullbacks .finite .matching_facts
import data.fin

open invcat category functor matching_object Fib
     sigma.ops fincat natural_transformation eq

universe variable u
variables {C : Category.{1 1}}
            {D : Category}

open subcat_obj reedy
open sum nat fin function equiv

definition max_fun_to_ℕ (φ : C → ℕ) {n : ℕ} [ψ : objects C ≃ₛ fin (nat.succ n)] :
Σ z, (Π c, φ c ≤ φ z) :=
begin
  generalize φ, clear φ, generalize ψ, clear ψ, generalize C, clear C,
  induction n with [n', IHn],
  intros,
  { cases ψ with [f,g,l,r], esimp at *,
    existsi g (fin.zero 0),
    intro, assert H : f c = zero, apply eq_of_veq, cases (f c) with [v, Hlt], esimp, cases v,
    reflexivity, cases Hlt with [a, Hle], exfalso,
    rewrite -(succ_le_zero_iff_false (succ a)), apply Hle, rewrite -l, rewrite H },
  { intros,
    have H : Σ z, @to_fun _ (fin (succ (nat.succ n'))) ψ z = maxi, from ⟨(inv_fun C maxi), !right_inv⟩,
    cases H with [z'', max_z],
    have ψ' : C_without_z z'' ≃ fin (succ n'), from (@C_without_z_is_obj_finite _ _ z'' _),
    have H : Π (φ : C_without_z z'' → ℕ),
             Σ (z : C_without_z z''), (Π c, φ c ≤ φ z),
    from IHn _ ψ',
    cases H (φ ∘ obj) with [z', Hmax],
    cases (@decidable_le (φ z'') (φ z')) with [z_le, z_ne_le],
    existsi z', intros,
    cases (@fincat.has_decidable_eq _ ⟨succ (succ n'), ψ⟩ c z'') with [c_eq_z, c_ne_z],
    { rewrite c_eq_z, assumption },
    { apply Hmax (mk _ c_ne_z) },
      existsi z'', intro, apply nat.le_of_eq_or_lt,
      cases (@fincat.has_decidable_eq _ ⟨succ (succ n'), ψ⟩ c z'') with [c_eq_z, c_ne_z],
      left, rewrite c_eq_z, right,
      have Hmax_c' : φ (obj (mk c c_ne_z)) ≤ φ (obj z'), from Hmax (mk c c_ne_z), esimp at *,
      have Hlt : φ z' < φ z'', from iff.elim_right (gt_iff_not_le _ _) z_ne_le,
      apply lt_of_le_of_lt Hmax_c' Hlt }
end

open invcat

definition Functor_from_C'_eq (X : C ⇒ Uₛ) (z : C) (x' : C_without_z z) :
  X (@obj _ _ x') = (object (Functor_from_C' z X) x') :=
  begin esimp end

  open poly_unit
  open reduced_coslice
  open reduced_coslice.red_coslice_obs

  -- for any object "a" from z//C (which is an arrow z⟶y with extra property) we show that codomain y cannot be z
  -- we show it using the definition of reduced coslice and the fact that C is an inverse category
  definition reduced_coslice_ne (z : C) (a : z//C) [invC : invcat C] : to a ≠ z :=
  begin
    cases a with [y, f, non_id_f], esimp at *,
    intro p, cases p,
    apply non_id_f rfl,
    cases invC, cases reflecting_id_ℕop,
    apply (reflecting_id f ⟨rfl,rfl⟩).2
  end

definition Functor_from_C'_reedy_fibrant (z : C) (X : C ⇒ Uₛ) [invC : invcat C]
  {φ : C ⇒ ℕop} {max_rank : ∀ x, φ x ≤ φ z} {reflecting_id : id_reflect φ}
  [rfibX : is_reedy_fibrant X] [finC : is_obj_finite C]
  : is_reedy_fibrant (Functor_from_C' z X)  :=
    begin
      let C' := C_without_z z,
      let X' := Functor_from_C' z X,
      unfold is_reedy_fibrant at *,
      unfold is_fibration_alt at *,
      intros x b,
      let Hequiv := (@MO_equiv C z x φ reflecting_id max_rank _ _ X),
      let MO := @to_fun _ _ Hequiv b,
      assert isfibX' : is_fibrant (fibreₛ (matching_obj_map X (obj x)) (@to_fun _ _ Hequiv b)), begin apply (rfibX x MO) end,
      assert Hfeq': (fibreₛ (matching_obj_map X (obj x)) MO) ≃ₛ (fibreₛ (matching_obj_map (Functor_from_C' z X) x) b),
      begin
        unfold fibreₛ, apply @sigma_congr₂, intros, esimp,
        apply iff_impl_equiv, refine iff.intro _ _,
        { intros p,
          calc
                matching_obj_map X' x a
              = @inv_fun _ _ Hequiv (matching_obj_map X (obj x) a) :
                  begin refine nat_trans_eq, apply funext, intro y, apply funext, intro uu,
                      cases y, cases uu, esimp end
          ... = @inv_fun _ _ Hequiv (@to_fun _ _ Hequiv b) : ap _ p
          ... = b : @left_inv _ _ _
          },
        { intros p,
          calc
               matching_obj_map X (obj x) a
               = Hequiv ∙ (matching_obj_map X' x a) :
               begin
                 unfold fn, refine nat_trans_eq, apply funext, intro y, apply funext, intro uu,
                cases uu, esimp at *,
                assert H : morphism X (hom_to y) a =
                natural_map ((@MO'_to_MO_map _ _ _ _ reflecting_id max_rank _ _ X)
                (matching_obj_map (Functor_from_C' z X) x a)) y star, unfold MO'_to_MO_map,
                rewrite natural_map_proj, cases y, esimp, cases x, esimp,
                apply H end
         ... = Hequiv ∙ b : ap _ p }
      end,
      apply equiv_is_fibrant Hfeq'
    end

-- map from limit of X restricted to C'
definition map_L_to_Mz (z : C) (X : C ⇒ Uₛ) [invC : invcat C]
  (L : cone_with_tip (Functor_from_C' z X) poly_unit) : matching_object X z :=
    by cases L with [η, NatSq]; refine natural_transformation.mk
      (λ a u, η (mk (to a) (reduced_coslice_ne z a)) poly_unit.star)
      (λ a b f, begin apply funext, intro, cases x, refine happly (NatSq _) poly_unit.star end)


-- explicit representation of the limit of X restricted to category C without z
definition lim_restricted [reducible] (X : C ⇒ Uₛ) (z : C) [invC : invcat C]
:= Σ (c : Π y, (Functor_from_C' z X) y),
      Π (y y' : C_without_z z) (f : @hom (subcat_obj C _) _ y y'),
        ((Functor_from_C' z X) f) (c y) = c y'

-- map from the limit of X restricted to C' where we use explicit representation of limit L
definition map_L_to_Mz_alt (z : C) (X : C ⇒ Uₛ.{u}) [invC : invcat C]
(L : lim_restricted X z) : matching_object X z :=
  match L with
  | ⟨η, NatSq⟩ :=
  by refine natural_transformation.mk
  (λ a u, η (mk _ (reduced_coslice_ne z a)))
  (λ a b f, funext (λ u, NatSq _ _ _))
end

open eq.ops

definition lift_to_rc [reducible] {z : C} (y : C_without_z z) (f : z ⟶ obj y): z//C :=
  red_coslice_obs.mk (obj y) f (λ p a, prop y p⁻¹)

definition singleton_contr_fiberₛ {E B : Type} {p : E → B} : (Σ b, fibreₛ p b) ≃ₛ E :=
begin
  refine equiv.mk (λ (p' : (Σ b, fibreₛ p b)), p'.2.1) (λ e, ⟨p e, ⟨e,rfl⟩⟩) _ (λx, rfl),
  unfold function.left_inverse, intros, cases x with [p1, p2], cases p2 with [p21,p22],
  esimp, induction p22 using eq.drec, congruence
end

definition two_piece_limit_pullback_p_q_equiv [invC : invcat C] (X : C ⇒ Uₛ.{u}) (z : C) :
(Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
(Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
(Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y'))
  ≃ₛ
(Σ (c_z : X z) d, !map_L_to_Mz_alt d = !matching_obj_map c_z)
 :=
begin
  refine @sigma_congr₂ _ _ _ _, intro c_z,
  refine equiv.mk _ _ _ _,
  { intro w, refine ⟨_,_⟩, refine ⟨w.1, prod.pr2 w.2⟩,
    unfold map_L_to_Mz_alt, refine nat_trans_eq, unfold natural_map,
    apply funext, intro y, apply funext, intro u, unfold matching_obj_map,
    esimp, cases w with [c,p2], cases p2 with [p_l, p_r], esimp at *, symmetry,
    apply (p_l (subcat_obj.mk (to y) (reduced_coslice_ne z y)) (hom_to y)) },
  { intro w,
    cases w  with [d, Heq], unfold lim_restricted at d, cases d with [c, Heq'], existsi c,
    split,
    { intros,
      assert H: natural_map (!map_L_to_Mz_alt ⟨c, Heq'⟩) (lift_to_rc y f) star  =
                natural_map (!matching_obj_map c_z) (lift_to_rc y f) star, begin rewrite Heq end,
      assert lemma1 : natural_map (map_L_to_Mz_alt z X ⟨c,Heq'⟩) (lift_to_rc y f) star = c y,
        begin unfold map_L_to_Mz_alt, unfold natural_map, cases y, esimp end,
      have lemma2 : (natural_map (matching_obj_map X z c_z)) (lift_to_rc y f) star = X f c_z, from rfl,
      symmetry,
      apply #eq.ops lemma1⁻¹ ⬝ H ⬝ lemma2 },
    { apply Heq'}},
  { intro w, cases w with [c, H], cases H with [p1,p2], apply sigma_eq_congr, existsi rfl, apply apd },
  { intro w, cases w with [c, H], apply sigma_eq_congr, refine ⟨_,_⟩, cases c with [p1,p2],
  apply sigma_eq_congr, existsi rfl, refine apd _ _, apply p2, reflexivity, apply proof_irrel  }
end

definition lim_two_pieces_eq
{ X : C ⇒ Uₛ}
{ z : C }
{ c_z : X z}
{ c : Π y, X (obj y) }
{a b : (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
(Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y')} : a = b :=
begin cases a, cases b, congruence end

definition limit_two_piece_limit_equiv [invC : invcat C] {n' : ℕ}
  (ψ : C ≃ₛ fin (succ n'))
  {z : C}
  {φ : C ⇒ ℕop}
  (reflecting_id : id_reflect φ)
  (max_rank : Πy, φ y ≤ φ z)
  (X : C ⇒ Uₛ.{u}) :
  (Σ (c : Π y, X y), Π y y' f, morphism X f (c y) = c y')
    ≃ₛ
  (Σ (c_z : X z) (c : (Π y : C_without_z z, X y)),
  (Π (y : C_without_z z) (f : z ⟶ obj y ), X f c_z = c y) ×
  (Π (y y' : C_without_z z) (f : @hom (subcat_obj _ _) _ y y'), (Functor_from_C' z X) f (c y) = c y'))
  := begin
     refine equiv.mk _ _ _ _,
              { intro, cases a with [p1, p2], refine ⟨p1 z, ⟨λ y, p1 y,(λ y' f, p2 z y' f, λ y y' f, p2 y y' f)⟩⟩ },
              { intro, cases a with [c_z, p'], cases p' with [p2, p3], cases p3 with [l_z, l_y], refine ⟨_,λ y y' f, _⟩, intro y'',
                have Heq : decidable (y'' = z), from @fincat.has_decidable_eq _ (⟨_,ψ⟩) _ _,
                cases Heq with [y_eq_z, y_ne_z],
                { rewrite y_eq_z, assumption },
                { refine p2 (mk y'' _), assumption },
                intros,
                -- now, we have 4 cases to consider: y=z, y≠z, y'=z, y'≠z
                generalize (@fincat.has_decidable_eq C ⟨_,ψ⟩ y  z),
                generalize (@fincat.has_decidable_eq C ⟨_,ψ⟩ y' z),
                intros deq_y deq_y',
                cases deq_y' with [y_eq_z, y_ne_z]:
                cases deq_y with [y'_eq_z, y'_ne_z],
                { cases y_eq_z, cases y'_eq_z, esimp, rewrite (endomorphism_is_id f), refine happly (respect_id _ _) _},
                { cases y_eq_z, esimp, apply l_z},
                { cases y'_eq_z, esimp, exfalso, apply (@no_incoming_non_id_arrows _ z φ max_rank _), existsi y, existsi f, assumption },
                { esimp, apply l_y },
              },

              { unfold left_inverse, esimp, intros, cases x with [x, H], esimp, congruence, apply funext, intro y,
                cases @fincat.has_decidable_eq C (⟨_,ψ⟩) y  z with [y_eq_z, y_ne_z],
              { cases y_eq_z, esimp }, {esimp }},

              { unfold right_inverse, unfold left_inverse, esimp, intro y, cases y with [c_z, Hs],
                esimp, cases Hs with [p1, p2], esimp, cases p2, esimp,
                cases (@has_decidable_eq C ⟨succ n', ψ⟩ z z) with [y_eq_z, y_ne_z], esimp, congruence,
                apply sigma_eq_congr,
                refine ⟨_,lim_two_pieces_eq⟩,
                { intros, apply reflecting_id, assumption },
                { apply funext, intro y',
                  cases @fincat.has_decidable_eq C (⟨_,ψ⟩) y' z with [y'_eq_z, y'_ne_z], esimp,
                  cases y' with [y'', p'], esimp at *, exfalso, apply p', apply y'_eq_z,
                  esimp, cases y', congruence },
                exfalso, apply y_ne_z, reflexivity
            }
         end

definition fibration_domain_is_fibrant {E : Type} {B : Fib} (p : E → B) [isfibr_p : is_fibration_alt p]:
  is_fibrant E := @equiv_is_fibrant (Σ b x, p x = b) _ singleton_contr_fiberₛ _

definition fincat_0_limit_unit_equiv [φ : C ≃ₛ fin 0 ] (X : C ⇒ Uₛ) : Nat(𝟙,X) ≃ₛ poly_unit :=
  begin
  cases φ with [f,g,l,r],
  refine equiv.mk (λ x, star) _ _ _,
  { intros, esimp, refine mk _ _, intros x, exfalso, apply (false_of_fin_zero (f x)),
    intros a b u, exfalso, apply (false_of_fin_zero (f a))},
  { unfold left_inverse, intro L, cases L, congruence, apply funext, intro x, exfalso, apply (false_of_fin_zero (f x))},
  { unfold right_inverse, unfold left_inverse, intro x, cases x, reflexivity }
  end
