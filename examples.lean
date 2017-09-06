import .fibrant

namespace instance_inference

-- variables {A : Type} [is_fibrant A]
-- variables {B : Type} [is_fibrant B]
-- variables {C : Type} [is_fibrant C]

open fib_eq

variables {A : Fib} {B : Fib} {C : Fib} (P : A → Fib)

-- in this case, since we state an equivalence of the fibrant types
-- both sides must be fibrant. Lean infers that is is the case by using
-- prod_is_fibrant.
definition prod_assoc : A × (B × C) ≃ (A × B) × C := sorry

set_option pp.implicit true
set_option pp.notation false

-- check @prod_assoc

-- slightly more complicatied example, where Lean uses
-- prod_is_fibrant and pi_is_fibrant
definition prod_universal : (C → A × B) ≃ (C → A) × (C → B) := sorry

check @prod_universal

open  sigma.ops
definition total_space_proj : (Σ (a : A), P a) → A := λp, p.1

definition fibre_projection (a : A) :
fibre (total_space_proj P) a ≃ P a := sorry

-- check @fibre_projection

end instance_inference

namespace agdafail

  open fib_eq
  variables {A : Fib}  {Q : A → Type} [Π a, is_fibrant (Q a)]

  definition pi_eq (f : Π (a : A), Q a) : f ~ f := refl _

  check @pi_eq

end agdafail

namespace seimsimplicial

definition SST₃ :=
  Σ (X₀ : Type)                                   -- points
    (X₁ : X₀ → X₀ → Type),                      -- lines
      Π (x₀ x₁ x₂ : X₀),
        X₁ x₀ x₁ → X₁ x₁ x₂ → X₁ x₀ x₁ → Type  -- tringles

end seimsimplicial
