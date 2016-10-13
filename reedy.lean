import fibrant data.fin data.equiv

open nat equiv function fin eq.ops sum equiv.ops unit prod.ops

definition fam_indexed_by_empty_equiv_unit {X : empty → Type}: (Π i, X i) ≃ unit :=
  equiv.mk (λ x, unit.star) (λ x, empty.rec X)
           begin unfold left_inverse, intro x, apply funext, intro i, cases i end
           begin
             intro, cases x, reflexivity
           end

definition fin_0_fam_equiv.{u} : (fin 0 → Type.{u}) ≃ (empty → Type.{u}) :=
  begin apply arrow_congr, apply fin_zero_equiv_empty, apply equiv.refl end

definition pi_fin0_unit_equiv {X : fin 0 → Type} : (Π i, X i) ≃ unit :=
  equiv.mk (λ x, unit.star) (λ x i, fin.elim0 i)
  begin unfold left_inverse, intro, apply funext, intro, apply (elim0 x_1) end
  begin
  intro, cases x, reflexivity
  end

lemma pi_sum_fin_unit_equiv {n} {X : (unit + fin n) → Type} : (Π i, X i) ≃ (X (inl ⋆) × Π i, X (inr i)) :=
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

definition pi_sum_fin_unit_equiv' {n} (Heq : fin n + unit ≃ fin (nat.succ n))
      {X : fin (nat.succ n) → Type}
      : (Π i, X (Heq ∙ i)) ≃ (X (Heq ∙ (inr ⋆)) × Π i, X (Heq ∙ (inl i))) :=
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

definition ap {A B : Type}(f : A → B){a a' : A}
              (p : a = a') : f a = f a' := p ▹ eq.refl _

definition apd {A : Type}{B : A → Type}(f : Π (a : A), B a)
               {a a' : A}(p : a = a') : p ▹ f a = f a' :=
  eq.drec (eq.refl _) p

definition naturality_subst {X Y : Type}{x x' : X}{P : Y → Type}
                            (f : X → Y)(p : x = x')(u : P (f x)) :
                            ap f p ▹ u = p ▹ u :=
  eq.drec (eq.refl _) p

definition pi_congr {A A' : Type} {B : A' → Type} (φ : equiv A A')
                       : (Π (a : A), B (φ ∙ a)) ≃ (Π (a : A'), B a) :=
  match φ with mk f g l r :=
  mk (λ k x', r x' ▹ k (g x'))
     (λ h x, h (f x))
     (λ k, funext (λ x,
       calc  r (f x) ▹ k (g (f x))
           = ap f (l x) ▹ k (g (f x)) : { proof_irrel (r (f x)) (ap f (l x)) }
       ... = l x ▹ k (g (f x)) : naturality_subst f (l x) (k (g (f x)))
       ... = k x : apd k (l x)
       ))
     (λ h, funext (λ x', apd h (r x')))
  end

definition lemma3 {n : ℕ}  {X : fin n → Type}
                  {fibX : Π i, is_fibrant (X i)}
           : is_fibrant (Π i, X i) :=
  begin
    induction n with n IHn,
    { apply (equiv_is_fibrant (equiv.symm pi_fin0_unit_equiv)) },

    { have HeqFinSum : fin n + unit ≃ fin (succ n), from (fin_sum_unit_equiv n),
      apply equiv_is_fibrant,
      { apply (pi_congr HeqFinSum) },
      { apply equiv_is_fibrant,
        { apply (equiv.symm (pi_sum_fin_unit_equiv' HeqFinSum)) },
        { apply @prod_is_fibrant, apply IHn, intro, apply fibX } }}
  end
