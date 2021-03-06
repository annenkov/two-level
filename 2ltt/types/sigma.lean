import ..fibrant ..facts
/- Ported from the Lean HoTT library with some changes.
   Facts about sigma-types harder to port in a way they are implemented.
   Proofs use more "generic" functionality from the HoTT library in comparison
   with product types.
-/
open sigma sigma.ops

namespace hsigma

  open fib_eq fib_eq.ap
  attribute elimo_β [simp]
  attribute trans [reducible]

  variables {A : Fib}
  variables {B : Fib}
            {P Q : A → Fib}
            {P' Q' : B → Fib}
  variables {u v w : Σ (a: A), P a} {a a' : A} {b b₁ b₂ : P a} {b' : P a'}
            {u' v' w' : Σ (b : B), P' b}

  definition dpair_eq_dpair [reducible] (p : a =ᵒ a') (q : p ▹ b =ᵒ b') : ⟨a, b⟩ =ᵒ ⟨a', b'⟩ :=
    begin
      induction p, rewrite transport_β at q,
      induction q, reflexivity
    end

  -- it is awkward to define such computation rules, because we have to
  -- manually use other computation rules in the statement itself
  -- But it seems, that it is sufficient to define computation rules for
  -- some base cases, and then just unfold definitions and use "simp" or
  -- rewrite explicitly.

  definition dpair_eq_dpair_β :
    @dpair_eq_dpair _ _ a a _ b idp (eq.symm (transport_β b) ▹s idp) = idp :=
    begin unfold dpair_eq_dpair, rewrite elimo_β,
    rewrite eq.transport_concat, simp end

  definition sigma_eq [reducible] (p : pr₁ u =ᵒ pr₁ v) (q : p ▹ pr₂ u =ᵒ pr₂ v) : u =ᵒ v :=
    (sigma.cases_on u (λ x y, sigma.cases_on v (λ x1 y1, dpair_eq_dpair))) p q

  definition sigma_to_dpair_eq (u v : Σ a, P a) :
    u =ᵒ v -> Σ (p : pr₁ u =ᵒ pr₁ v), p ▹ (pr₂ u) =ᵒ pr₂ v :=
      elimᵒ ⟨reflᵒ u.1, eq.rec (reflᵒ u.2) (eq.symm (transport_β u.2))⟩ _

  namespace fib_eq
    definition pathover_idp_of_eq [reducible] {A : Fib} {B : A → Fib} {a : A} {b b' : B a} :
      b =ᵒ b' → (reflᵒ a) ▹ b =ᵒ b' :=  λ p, by induction p; rewrite transport_β

    definition pathover_idp_of_eq_β {A : Fib} {B : A → Fib} {a : A} {b : B a} :
      @pathover_idp_of_eq A _ _ _ _ (reflᵒ b) = (eq.symm (transport_β b) ▹s idp) :=
      by simp

  end fib_eq

/- Applying dpair to one argument is the same as dpair_eq_dpair with reflexivity in the first place. -/

  open fib_eq.ap

  definition ap_dpair (q : b₁ =ᵒ b₂) :
  ap (sigma.mk a) q =ᵒ dpair_eq_dpair idp (fib_eq.pathover_idp_of_eq q) :=
  begin
    induction q, unfold fib_eq.pathover_idp_of_eq, unfold dpair_eq_dpair,
    repeat rewrite elimo_β, rewrite eq.transport_concat
  end

  -- proof of the same property as above, but using propositional computation rules for
  -- the definitions involved in the type
  definition ap_dpair' (q : b₁ =ᵒ b₂) :
    ap (sigma.mk a) q =ᵒ dpair_eq_dpair idp (fib_eq.pathover_idp_of_eq q) :=
    begin
    induction q, rewrite fib_eq.pathover_idp_of_eq_β, rewrite dpair_eq_dpair_β,
    rewrite ap_β
   end

end hsigma
