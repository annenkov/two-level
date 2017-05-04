import ..fibrant ..facts
/- Ported from the Lean HoTT library with some changes.
   Facts about sigma-types harder to port as they use more
   "generic" functionality from the HoTT library in comparison
   with product types.
-/
open sigma sigma.ops eq

namespace hsigma

  open fib_eq
  attribute elim_β [simp]
  attribute trans [reducible]

  variables {A : Fib}
  variables {B : Fib}
            {P Q : A → Fib}
            {P' Q' : B → Fib}
  variables {u v w : Σ (a: A), P a} {a a' : A} {b b₁ b₂ : P a} {b' : P a'}
            {u' v' w' : Σ (b : B), P' b}

  definition dpair_eq_dpair [reducible] (p : a ~ a') (q : p ▹ b ~ b') : ⟨a, b⟩ ~ ⟨a', b'⟩ :=
    begin
      induction p, rewrite subst_β at q,
      induction q, reflexivity
    end

  definition sigma_eq [reducible] (p : pr₁ u ~ pr₁ v) (q : p ▹ pr₂ u ~ pr₂ v) : u ~ v :=
    (sigma.cases_on u (λ x y, sigma.cases_on v (λ x1 y1, dpair_eq_dpair))) p q

  definition sigma_to_dpair_eq (u v : Σ a, P a) :
    u ~ v -> Σ (p : pr₁ u ~ pr₁ v), p ▹ (pr₂ u) ~ pr₂ v :=
      elim ⟨refl u.1, eq.rec (refl u.2) (eq.symm (subst_β u.2))⟩ _

/- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/
  open fib_eq.ap
  definition pathover_idp_of_eq {A : Fib} {B : A → Fib} {a : A} {b b' : B a} :
    b ~ b' → (refl a) ▹ b ~ b' :=  λ p, by induction p; rewrite subst_β

  definition ap_dpair (q : b₁ ~ b₂) :
  ap (sigma.mk a) q ~ dpair_eq_dpair idp (pathover_idp_of_eq q) :=
  begin
    induction q, unfold pathover_idp_of_eq, unfold dpair_eq_dpair,
    repeat rewrite elim_β, rewrite transport_concat
  end

end hsigma
