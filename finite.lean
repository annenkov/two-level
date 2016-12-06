import fibrant data.fin data.equiv facts algebra.category

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

-- some facts about (essentially) finite categories

namespace fincat
  universe variables u v
  variables {C C' : Category.{u v}}
  open category sigma.ops eq

  definition is_finite [class] (C : Category) := Σ n, C ≃ fin n
  definition is_finite_eq [finC : is_finite C] := finC.2

  attribute is_finite_eq [instance]

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

  definition eq_of_finN_eq [finC : is_finite C] {c c' : C} : c = c' → to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' :=
    begin
      intro Heq, cases finC with [n, φ], esimp, apply (ap _ Heq)
    end

  definition finN_eq_of_eq [finC : is_finite C] {c c' : C} : to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' → c = c' :=
    begin
      intro Heq, cases finC with [n, φ], cases φ with [f,g,l,r], esimp at *,
      apply (injective_of_left_inverse l), apply Heq
    end

  definition eq_iff_finN_eq [finC : is_finite C] {c c' : C} :
    to_fun (fin (finC.1)) c = to_fun (fin (finC.1)) c' ↔ c = c' := iff.intro finN_eq_of_eq eq_of_finN_eq

  definition has_decidable_eq [instance] [finC : is_finite C] {c c' : C} : decidable (c = c') :=
    decidable_of_decidable_of_iff (fin.has_decidable_eq _ _ _) eq_iff_finN_eq
end fincat
