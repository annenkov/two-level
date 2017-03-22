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

  definition transport_concat {A : Type } {a b c: A} (P : A → Type)
    (p : a = b) (q : b = c) (u : P a) : q ▹ (p ▹ u) = p ⬝ q ▹ u := begin cases p, cases q, reflexivity end

  definition concat_inv {A : Type } {a b : A} {P : A → Type}
    (p : a = b) (u : P a) : #eq.ops p ⬝ p⁻¹ ▹ u = u := by cases p; reflexivity

end eq

open eq

namespace equiv

  open eq.ops sigma.ops function

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
    : (Π (a : A), F a) ≃ (Π (a : A), G a) :=
    equiv.mk
      (λ x a, (φ a) ∙ x a)
      (λ x a, inv (x a))
      (λ x, funext (λ a, (left_inv _ (G a) _) ▹ rfl))
      (λ x, funext (λ a, (right_inv (F a) _ _) ▹ rfl))

  definition pi_congr [instance] {F : A → Type} {F' : A' → Type} [φ : A ≃ A'] [φ' : Π a, F a ≃ F' (φ ∙ a)] :=
    equiv.trans (@pi_congr₂ _ _ _ φ') (@pi_congr₁ _ _ _ φ)

  definition sigma_eq_congr {A: Type} {F : A → Type} {a a': A} {b : F a} {b' : F a'} :
    (Σ (p : a = a'), ((p ▹ b) = b')) → ⟨ a, b ⟩ = ⟨a', b'⟩ :=
      begin intro p, cases p with [p₁, p₂], cases p₁, cases p₂, esimp end

  definition sigma_congr₁ [instance] {A B: Type} {F : B → Type} [φ : A ≃ B]:
  (Σ a : A, F (φ ∙ a)) ≃ Σ b : B, F b :=
  equiv.mk
  (λ x , ⟨ φ ∙ x.1, x.2 ⟩ )
  (λ x,  ⟨ inv x.1, begin unfold fn, unfold inv, rewrite right_inv, apply x.2 end⟩ )
  (λ x, begin
        unfold fn at *,
        cases φ with [f, g, l, r], esimp at *, unfold fn,
        cases x with [x₁, x₂],
        unfold function.right_inverse at *, unfold function.left_inverse at *, unfold inv, esimp,
        apply sigma_eq_congr, refine ⟨l x₁,_⟩,
        calc
        (l x₁ ▹ ((r (f x₁))⁻¹ ▹ x₂))
            = (l x₁ ▹ (eq.symm (ap f (l x₁)) ▹ x₂)) : rfl
        ... = (l x₁ ▹ (eq.symm (l x₁) ▹ x₂)) : naturality_subst
        ... = ((l x₁ ⬝ (eq.symm (l x₁))) ▹ x₂) : transport_concat
        ... = x₂ : concat_inv (l x₁)
        end)
   begin
     intro x, cases x with [x₁, x₂],
     cases φ with [f, g, l, r], unfold function.right_inverse at *, unfold function.left_inverse at *,  esimp at *,
     apply sigma_eq_congr, refine ⟨_,_⟩, apply r,
     calc
      #eq.ops
      r x₁ ▹ (r x₁)⁻¹ ▹ x₂
         = r x₁ ⬝ (r x₁)⁻¹ ▹ x₂ : transport_concat
     ... = x₂ : concat_inv (r x₁)
   end

  definition sigma_congr₂ [instance] {A : Type} {F G : A → Type} [φ : Π a : A, F a ≃ G a] :
    (Σ a, F a) ≃ Σ a, G a :=
    equiv.mk
      (λ x, ⟨x.1, (φ x.1) ∙ x.2⟩)
      (λ x, ⟨x.1, inv x.2⟩)
      begin
        unfold left_inverse, intros,
        cases x with [p₁, p₂], esimp,
        congruence, unfold fn, unfold inv,
        rewrite left_inv
      end
      begin
        unfold right_inverse, unfold left_inverse, intros,
        cases x with [p₁, p₂], congruence, unfold fn, unfold inv,
        rewrite right_inv
      end

  definition sigma_congr {A B : Type} {F : A → Type} {G : B → Type}
    [φ : A ≃ B] [φ' : Π a : A, F a ≃ G (φ ∙ a)] :
    (Σ a, F a) ≃ Σ a, G a := equiv.trans sigma_congr₂ sigma_congr₁

  definition sigma_swap {A B : Type} {F : A → B → Type} :
    (Σ (a : A) (b : B), F a b) ≃ Σ (b : B) (a : A), F a b :=
    equiv.mk (λ x, ⟨x.2.1,⟨x.1,x.2.2⟩⟩)
             (λ x, ⟨x.2.1,⟨x.1,x.2.2⟩⟩)
             (λ x, by cases x with [p1,p2]; cases p2; reflexivity)
             (λ x, by cases x with [p1,p2]; cases p2; reflexivity)

  definition iff_impl_equiv {A B : Prop} (Hiff : A ↔ B) : A ≃ B :=
  match Hiff with
  | iff.intro f g := equiv.mk f g (λx, proof_irrel _ _) (λx, proof_irrel _ _)
  end

end equiv

namespace function
  definition happly {A B : Type} {f g : A → B} : f = g -> ∀ x, f x = g x :=
    begin
      intros H x, rewrite H
    end
end function
