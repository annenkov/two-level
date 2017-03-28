import fibrant data.fin data.equiv facts algebra.category facts

open nat equiv function fin eq.ops sum unit prod.ops function

-- facts about type family indexed by strict finite type

definition pi_fin0_unit_equiv {X : fin 0 → Type} : (Π i, X i) ≃ₛ unit :=
  equiv.mk (λ x, unit.star) (λ x i, fin.elim0 i)
  begin unfold left_inverse, intro, apply funext, intro, apply (elim0 x_1) end
  begin
  intro, cases x, reflexivity
  end

lemma pi_sum_fin_unit_equiv {n} {X : (unit + fin n) → Type} : (Π i, X i) ≃ₛ (X (inl ⋆) × Π i, X (inr i)) :=
  equiv.mk
    (λ x, (x (inl ⋆), λ y, x (inr y)))
    (λ p, λ z, sum.cases_on z (λ x1, unit.cases_on x1 p.1) (λ x2, p.2 x2))
  begin
    unfold left_inverse, esimp, intro, apply funext, intro i,
    cases i,
      { esimp, cases a, esimp },
      { esimp }
  end
  begin
    unfold right_inverse, unfold left_inverse, apply prod.eta
  end

definition pi_sum_fin_unit_equiv' {n} (Heq : fin n + unit ≃ₛ fin (nat.succ n))
      {X : fin (nat.succ n) → Type}
      : (Π i, X (Heq ∙ i)) ≃ₛ (X (Heq ∙ (inr ⋆)) × Π i, X (Heq ∙ (inl i))) :=
 equiv.mk
   (λ x, (x (inr ⋆), λ y, x (inl y)))
   (λ p, λ z, sum.cases_on z (λ x2, p.2 x2) (λ x1, unit.cases_on x1 p.1))
   begin
     unfold left_inverse, esimp, intro x, apply funext, intro i,
     cases i, esimp, cases a, esimp
   end
   begin
     unfold right_inverse, unfold left_inverse, apply prod.eta
   end

definition finite_cofibrant {n : ℕ} {X : fin n → Fib}
  : is_fibrant (Π i, X i) :=
  begin
    induction n with n IHn,
    { apply (equiv_is_fibrant (equiv.symm pi_fin0_unit_equiv)) },
    { have HeqFinSum : fin n + unit ≃ₛ fin (succ n), from (fin_sum_unit_equiv n),
      apply equiv_is_fibrant,
        apply pi_congr₁,
        apply equiv_is_fibrant, apply (equiv.symm (pi_sum_fin_unit_equiv' HeqFinSum))}
end

namespace fin

  definition lift_down {n : ℕ} (i : fin (nat.succ n)) (Hne : i ≠ maxi) : fin n := fin.mk (val i) (lt_max_of_ne_max Hne)

  definition lift_succ_lift_down_inverse {n : ℕ} {i : fin (nat.succ n)} {Hne : i ≠ maxi} :
    (lift_succ (lift_down i Hne)) = i :=
    begin cases i, esimp end

  open decidable equiv.ops

  -- inspired by Paolo Capriotti's Agda implementation

  definition fin_transpose {n} (i j k : fin n) : fin n :=
    match fin.has_decidable_eq _ i k with
    | inl _ := j
    | inr _ := match fin.has_decidable_eq _ j k with
               | inl _ := i
               | inr _ := k
               end
  end

  lemma fin_transpose_invol {n} {i j k : fin n} : fin_transpose i j (fin_transpose i j k) = k :=
    begin
      unfold fin_transpose,
      cases (fin.has_decidable_eq n i k) with [i_eq_k, i_ne_k]: esimp,
      cases (fin.has_decidable_eq n i j) with [i_eq_j, j_ne_k]: esimp, apply i_eq_j⁻¹ ⬝ i_eq_k,
      cases (fin.has_decidable_eq n j j) with [j_eq_j, j_ne_j]: esimp, assumption, apply absurd rfl j_ne_j,
      cases (fin.has_decidable_eq n j k) with [j_eq_k, j_ne_k]: esimp,
      cases (fin.has_decidable_eq n i i) with [i_eq_i, i_ne_i]: esimp, assumption,
      cases (fin.has_decidable_eq n j i) with [j_eq_i, j_ne_i]: esimp: apply absurd rfl i_ne_i,
      cases (fin.has_decidable_eq n i k) with [i_eq_k, i_ne_k]: esimp, rewrite i_eq_k at i_ne_k, apply absurd rfl i_ne_k,
      cases (fin.has_decidable_eq n j k) with [j_eq_k, j_ne_k]: esimp, apply absurd j_eq_k j_ne_k
      end

  definition fin_transpose_equiv [instance] {n} (i j : fin n) : fin n ≃ fin n:=
  equiv.mk (fin_transpose i j) (fin_transpose i j) (λ k, fin_transpose_invol) (λ k, fin_transpose_invol)

  definition fin_transpose_β₁ {n : ℕ} {i j : fin n} : fin_transpose i i j = j :=
  begin
    unfold fin_transpose,
    cases (fin.has_decidable_eq n i j) with [i_eq_j, i_ne_j]: esimp, apply i_eq_j
  end

  definition fin_transpose_β₂ {n : ℕ} {i j : fin n} : fin_transpose i j j = i :=
  begin
    unfold fin_transpose,
    cases (fin.has_decidable_eq n i j) with [i_eq_j, i_ne_j]: esimp, apply i_eq_j⁻¹,
    cases (fin.has_decidable_eq n j j) with [j_eq_j, j_ne_j]: esimp, apply absurd rfl j_ne_j
  end

  definition fin_transpose_inj {n : ℕ} {i j : fin n} : injective (fin_transpose i j) :=
  begin
    refine (injective_of_left_inverse (@left_inv (fin n) (fin n) (fin_transpose_equiv _ _)))
  end

  -- removing any element from fin is equivalent to removing maximal element
  -- we use transpositions defined above to prove this
  definition fin_remove_max_equiv [instance] {n : ℕ} (z : fin (nat.succ n)) :
    (Σ i : fin (nat.succ n), i ≠ z) ≃ (Σ i : fin (nat.succ n), i ≠ maxi) :=
    begin
    assert H : Π (x : fin (nat.succ n)), x = z ≃ (fin_transpose maxi z x = maxi),
    begin
    intros, refine equiv.mk (λ Heq, Heq⁻¹ ▹ fin_transpose_β₂) _ _ _,
    { intros, assert Heq : fin_transpose maxi z x = fin_transpose maxi z z, begin rewrite fin_transpose_β₂, assumption end,
      apply fin_transpose_inj, assumption },
    { unfold left_inverse, intro, esimp },
    { unfold right_inverse, intro, esimp }
    end,
    refine @sigma_congr _ _ _ _ (fin_transpose_equiv maxi z) (λ x, @pi_congr _ _ _ _ (H _) (λ y, equiv.refl _))
    end

  open sigma.ops

  -- removing maximal element gives us a set with smaller cardinality
  -- we use it as a base case to remove any element and get a set with smaller cardinality
  definition fin_remove_max [instance] {n : ℕ} : (Σ i : fin (nat.succ n), i ≠ maxi) ≃ fin n :=
    begin
      refine equiv.mk (λ j, lift_down _ j.2) (λi,⟨lift_succ i,lift_succ_ne_max⟩) _ _,
      { unfold left_inverse, intro j, cases j, congruence,
        rewrite lift_succ_lift_down_inverse },
      { unfold right_inverse, unfold left_inverse, intro i, cases i, unfold lift_down }
    end

  -- now we can remove any element from fin using equivalences defined above
  definition fin_remove_equiv {n : ℕ } (z : fin (nat.succ n))
    : (Σ i : fin (nat.succ n), i ≠ z) ≃ fin n := fin_remove_max ∘ (fin_remove_max_equiv z)
end fin

-- some facts about finite categories

namespace fincat
  universe variables u v
  variables {C C' : Category.{u v}}
  open category sigma.ops eq equiv.ops

  definition is_obj_finite [class] (C : Category) := Σ n, C ≃ fin n
  definition is_obj_finite_eq [finC : is_obj_finite C] := finC.2

  attribute is_obj_finite_eq [instance]

  definition fincat_ne_maxi {n : ℕ} {z : C} {f : C → fin (succ n)} (inj_f : injective f)
    (max_z : f z = maxi) {o : C} (p : o ≠ z) : f o ≠ (maxi : fin (succ n)) :=
    begin
      unfold ne, unfold not, intro,
      apply p, rewrite -max_z at a, apply inj_f a
  end

  definition eq_of_finN_eq [finC : is_obj_finite C] {c c' : C} : c = c' → to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' :=
    begin
      intro Heq, cases finC with [n, φ], esimp, apply (ap _ Heq)
    end

  definition finN_eq_of_eq [finC : is_obj_finite C] {c c' : C} : to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' → c = c' :=
    begin
      intro Heq, cases finC with [n, φ], cases φ with [f,g,l,r], esimp at *,
      apply (injective_of_left_inverse l), apply Heq
    end

  definition eq_iff_finN_eq [finC : is_obj_finite C] {c c' : C} :
    to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' ↔ c = c' := iff.intro finN_eq_of_eq eq_of_finN_eq

  definition has_decidable_eq [instance] [finC : is_obj_finite C] {c c' : C} : decidable (c = c') :=
    decidable_of_decidable_of_iff (fin.has_decidable_eq _ _ _) eq_iff_finN_eq

  definition fincat_ob_remove_fin_equiv {n : ℕ} (z : C) [φ : C ≃ fin (succ n)] : (Σ c, c ≠ z) ≃ fin n :=
    begin
    cases φ with [f,g,l,r], esimp at *,
    assert Hequiv: (Σ c, c ≠ z) ≃ Σ (i : fin (succ n)), i ≠ f z,
      begin refine equiv.mk _ _ _ _,
      intro j, cases j with [c, p_ne], existsi f c, intros, apply p_ne, apply (injective_of_left_inverse l), assumption,
      intro i, cases i with [i', p_ne], existsi g i', intros, apply p_ne, rewrite -a, apply (r i')⁻¹,
      unfold left_inverse, intro x, cases x with [c, p_ne], esimp, congruence, apply l,
      unfold right_inverse, unfold left_inverse, unfold injective_of_left_inverse, intro x,
      cases x with [i, p_ne], esimp, congruence, apply r end,
      apply (fin.fin_remove_equiv _) ∘ Hequiv
    end
end fincat
