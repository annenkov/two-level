import data.equiv

open eq equiv eq.ops

-- some definitions and facts about equality and equivalence
-- which we could find in standard library

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

  definition pi_congr {A A' : Type} {B : A' → Type} (φ : equiv A A')
    : (Π (a : A), B (φ ∙ a)) ≃ (Π (a : A'), B a) :=
    match φ with mk f g l r :=
      mk (λ k x', r x' ▹ k (g x'))
      (λ h x, h (f x))
      (λ k, funext (λ x,
      calc  r (f x) ▹ k (g (f x))
            = ap f (l x) ▹ k (g (f x)) : { proof_irrel (r (f x)) (ap f (l x)) }
        ... = l x ▹ k (g (f x)) : naturality_subst f (l x) (k (g (f x)))
        ... = k x : apd k (l x)))
      (λ h, funext (λ x', apd h (r x')))
  end
end equiv
