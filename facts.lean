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

  open eq.ops sigma.ops
  definition sigma_eq_congr {A: Type} {F : A → Type} {a a': A} {b : F a} {b' : F a'} :
    (Σ (p : a = a'), ((p ▹ b) = b')) → ⟨ a, b ⟩ = ⟨a', b'⟩ :=
      begin intro p, cases p with [p₁, p₂], cases p₁, cases p₂, esimp end

  definition sigma_congr₁ [instance] {A B: Type} {F : B → Type} [φ : A ≃ B]:
  (Σ a : A, F (to_fun B a)) ≃ Σ b : B, F b :=
  equiv.mk
  (λ x , ⟨ _, x.2 ⟩ )
  (λ x,  ⟨ _, (eq.symm (right_inv A B _)) ▹ x.2⟩ )
  (λ x, begin
        cases x with [x₁, x₂],
        cases φ with [f, g, l, r], unfold function.right_inverse at *, unfold function.left_inverse at *, esimp,
        apply sigma_eq_congr, refine ⟨_,_⟩, apply l,
        calc
        (l x₁ ▹ #eq.ops ((r (f x₁))⁻¹ ▹ x₂))
            = #eq.ops (r (f x₁))⁻¹ ▹ x₂ : sorry --apd (λ p, eq.rec x₂ (eq.symm(r (f x₁)))) (l x₁)
        ... = x₂ : apd _ _
        end)
   begin
     intro x, cases x with [p₁, p₂],
     cases φ with [f, g, l, r], unfold function.right_inverse at *, unfold function.left_inverse at *,  esimp at *,
     apply sigma_eq_congr, refine ⟨_,_⟩, apply r,
     have H0 : #eq.ops r p₁ ▹ (r p₁)⁻¹ ▹ p₂ = r p₁ ▹ (λ x, (r p₁)⁻¹ ▹ p₂) p₂, from rfl,
     have H : #eq.ops r p₁ ▹ (r p₁)⁻¹ ▹ p₂ = @eq.rec _ _ (λa, F a) p₂ _ (r p₁)⁻¹, from apd _ _,
     have H' : #eq.ops (r p₁)⁻¹ ▹ p₂ = p₂, from apd _ _,
     calc #eq.ops r p₁ ▹ (r p₁)⁻¹ ▹ p₂
         = r p₁ ▹ (λ x, (r p₁)⁻¹ ▹ p₂) p₂ : rfl
     ... = #eq.ops (r p₁)⁻¹ ▹ p₂ : sorry --H
     ... = p₂ : sorry
   end

  definition sigma_congr₂ [instance] {A : Type} {F G : A → Type} [φ : Π a : A, F a ≃ G a] :
    (Σ a, F a) ≃ Σ a, G a :=
    equiv.mk sorry sorry sorry sorry

  definition sigma_congr {A B : Type} {F : A → Type} {G : B → Type}
    [φ : A ≃ B] [φ' : Π a : A, F a ≃ G (to_fun B a)] :
    (Σ a, F a) ≃ Σ a, G a := equiv.trans sigma_congr₂ sigma_congr₁

end equiv

namespace function
  definition happly {A B : Type} {f g : A → B} : f = g -> ∀ x, f x = g x :=
    begin
      intros H x, rewrite H
    end
end function
