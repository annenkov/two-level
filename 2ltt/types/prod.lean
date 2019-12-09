import ..fibrant

open prod prod.ops
open fib_eq

/- Ported from the Lean HoTT library, trying to keep as close as possible
   to the original implementation.
   Changes while porting: change equality notation (from "=" to "~"),
   replace usages of "reflexivity" with "simp" tactic.
   The "simp" tactic allows to apply computation rules for fibrant equality, which doesn't
   hold judgementally.
   The "induction" tactic applies fib_eq.elim induction principle automatically, as it is
   marked with [recursor] attribute.
-/

namespace hprod

  open fib_eq.ap
  attribute trans [reducible]
  attribute ap [reducible]

  variables {A : Fib}
  variables {B : Fib}
  variables {u v w : A × B} {a a' : A} {b b' : B}
            {P Q : A → Fib}

  protected definition eta [unfold 3] (u : A × B) : (pr₁ u, pr₂ u) =ᵒ u :=
  by cases u; apply idp

  definition pair_eq {a a' : A} {b b' : B} : (a =ᵒ a') × (b =ᵒ b') -> (a,b) =ᵒ (a',b')
  | pair_eq (p, q) := ap₂ (λ x y, (x,y)) p q


  definition pair_eq' [reducible]  (pa : a =ᵒ a') (pb : b =ᵒ b') : (a, b) =ᵒ (a', b') :=
    ap₂ (λ x y, (x,y)) pa pb

  definition pair_eq'_β {a a' : A} : pair_eq' (reflᵒ a) (reflᵒ a') = reflᵒ (a,a') :=
  by unfold pair_eq'; apply ap₂_β

  definition prod_eq' (H₁ : u.1 =ᵒ v.1) (H₂ : u.2 =ᵒ v.2) : u =ᵒ v :=
  by cases u; cases v; exact pair_eq' H₁ H₂

  definition prod_eq [reducible] (p : pr₁ u =ᵒ pr₁ v) (q : pr₂ u =ᵒ pr₂ v) : u =ᵒ v :=
  (prod.cases_on u (λ x y, prod.cases_on v (λ x1 y1, pair_eq'))) p q

  definition prod_eq_β : prod_eq (reflᵒ (pr₁ u)) (reflᵒ (pr₂ u)) = reflᵒ u :=
  by cases u; unfold prod_eq; unfold pair_eq'; apply ap₂_β

  definition prod_eq_β' [simp] : prod_eq (reflᵒ a) (reflᵒ b) = reflᵒ (a,b) :=
  by unfold prod_eq; unfold pair_eq'; rewrite ap₂_β

  definition eq_pr1 [reducible] (p : u =ᵒ v) : u.1 =ᵒ v.1 :=
  ap pr1 p

  definition eq_pr2 [reducible] (p : u =ᵒ v) : u.2 =ᵒ v.2 :=
  ap pr2 p

  namespace ops
    postfix `..1`:(max+1) := eq_pr1
    postfix `..2`:(max+1) := eq_pr2
  end ops

  open ops

  protected definition ap_pr1 (p : u =ᵒ v) : ap pr1 p =ᵒ p..1 := idp
  protected definition ap_pr2 (p : u =ᵒ v) : ap pr2 p =ᵒ p..2 := idp

  open fib_eq.ap

  definition pair_prod_eq (p : u.1 =ᵒ v.1) (q : u.2 =ᵒ v.2) :
    ((prod_eq p q)..1, (prod_eq p q)..2) =ᵒ (p, q) :=
  by
    induction u; induction v; esimp at *;
    induction p; induction q;
    rewrite prod_eq_β'; repeat rewrite elimo_β

  /- Transport -/

  definition prod_transport (p : a =ᵒ a') (u : P a × Q a) :
    p ▹ u =ᵒ (p ▹ u.1, p ▹ u.2) :=
  by induction p; induction u; simp

end hprod
