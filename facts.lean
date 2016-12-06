import data.equiv

open equiv equiv.ops eq eq.ops

-- some definitions and facts about equality and equivalence
-- which we could not find in standard library

namespace eq

  definition ap {A B : Type}(f : A → B){a a' : A}
    (p : a = a') : f a = f a' := p ▹ eq.refl _

  definition apd {A : Type}{B : A → Type}(f : Π (a : A), B a)
                 {a a' : A}(p : a = a') : p ▹ f a = f a' :=
    eq.drec (eq.refl _) p

  definition naturality_subst {X Y : Type}{x x' : X}{P : Y → Type}
    (f : X → Y)(p : x = x')(u : P (f x)) : ap f p ▹ u = p ▹ u :=
    eq.drec (eq.refl _) p

end eq

open eq

namespace equiv

  variables {A A' : Type}

  definition pi_congr₁ [instance] {F' : A'  → Type} [φ : A ≃ A']
    : (Π (a : A), F' (φ ∙ a)) ≃ (Π (a : A'), F' a) :=
    match φ with mk f g l r :=
      mk (λ k x', r x' ▹ k (g x'))
      (λ h x, h (f x))
      (λ k, funext (λ x,
      calc  r (f x) ▹ k (g (f x))
            = ap f (l x) ▹ k (g (f x)) : proof_irrel (r (f x)) (ap f (l x))
        ... = l x ▹ k (g (f x)) : naturality_subst f (l x) (k (g (f x)))
        ... = k x : apd k (l x)))
      (λ h, funext (λ x', apd h (r x')))
  end

  definition pi_congr₂ [instance] {F G : A → Type}  [φ : Π a, F a ≃ G a]
    : (Π (a : A), F a) ≃ (Π (a : A), G a) := equiv.mk sorry sorry sorry sorry

  definition pi_congr [instance] {F : A → Type} {F' : A' → Type} [φ : A ≃ A'] [φ' : Π a, F a ≃ F' (φ ∙ a)] :=
    equiv.trans (@pi_congr₂ _ _ _ φ') (@pi_congr₁ _ _ _ φ)

end equiv

namespace function
  definition happly {A B : Type} {f g : A → B} : f = g -> ∀ x, f x = g x :=
    begin
      intros H x, rewrite H
    end
end function
