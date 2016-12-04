import fibrant data.fin data.equiv facts algebra.category

open nat equiv function fin eq.ops sum unit prod.ops

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

definition lemma3 {n : ℕ} {X : fin n → Fib}
  : is_fibrant (Π i, X i) :=
  begin
    induction n with n IHn,
    { apply (equiv_is_fibrant (equiv.symm pi_fin0_unit_equiv)) },
    { have HeqFinSum : fin n + unit ≃ₛ fin (succ n), from (fin_sum_unit_equiv n),
      apply equiv_is_fibrant,
        apply pi_congr₁,
        apply equiv_is_fibrant, apply (equiv.symm (pi_sum_fin_unit_equiv' HeqFinSum))}
end

-- some facts about (essentially) finite catrgories

namespace fincat
  variables {C : Category}
  open category

  definition is_finite [class] (C : Category) := Σ n, C ≃ fin n

  definition lift_down {n : ℕ} (i : fin (succ n)) (Hne : i ≠ maxi) : fin n := fin.mk (val i) (lt_max_of_ne_max Hne)
  
  definition lift_succ_lift_down_inverse {n : ℕ} {i : fin (succ n)} {Hne : i ≠ maxi} : 
    (lift_succ (lift_down i Hne)) = i :=
    begin cases i, esimp end

  definition fincat_ne_maxi {n : ℕ} {z : C} {f : C → fin (succ n)} (inj_f : injective f)
    (max_z : f z = maxi) {o : C} (p : o ≠ z) : f o ≠ (maxi : fin (succ n)) :=
    begin 
      unfold ne, unfold not, intro,
      apply p, rewrite -max_z at a, apply inj_f a
  end

end fincat
