import ..fibrant

open prod prod.ops
open fib_eq

/- Ported from the Lean HoTT library, trying to keep as close as possible
   to the original implementation.
   Changes while porting: change equality notation (from "=" to "~"),
   use "fib_eq.elim" for induction, replace usages of "reflexivity" with "simp" tactic.
   The "simp" tactic allows to apply computation rules for fibrant equality, which doesn't
   hold judgementally.
-/

namespace hprod

  open fib_eq.ap
  attribute trans [reducible]
  attribute ap [reducible]

  variables {A : Fib}
  variables {B : Fib}
  variables {u v w : A × B} {a a' : A} {b b' : B}
            {P Q : A → Fib}

  protected definition eta [unfold 3] (u : A × B) : (pr₁ u, pr₂ u) ~ u :=
  by cases u; apply idp

  definition pair_eq {a a' : A} {b b' : B} : (a ~ a') × (b ~ b') -> (a,b) ~ (a',b')
  | pair_eq (p, q) := ap₂ (λ x y, (x,y)) p q


  definition pair_eq' [reducible]  (pa : a ~ a') (pb : b ~ b') : (a, b) ~ (a', b') :=
    ap₂ (λ x y, (x,y)) pa pb

  definition pair_eq'_β {a a' : A} : pair_eq' (refl a) (refl a') = refl (a,a') :=
  by unfold pair_eq'; apply ap₂_β

  definition prod_eq' (H₁ : u.1 ~ v.1) (H₂ : u.2 ~ v.2) : u ~ v :=
  by cases u; cases v; exact pair_eq' H₁ H₂

  definition prod_eq [reducible] (p : pr₁ u ~ pr₁ v) (q : pr₂ u ~ pr₂ v) : u ~ v :=
  (prod.cases_on u (λ x y, prod.cases_on v (λ x1 y1, pair_eq'))) p q

  definition prod_eq_β : prod_eq (refl (pr₁ u)) (refl (pr₂ u)) = refl u :=
  by cases u; unfold prod_eq; unfold pair_eq'; apply ap₂_β

  definition prod_eq_β' [simp] : prod_eq (refl a) (refl b) = refl (a,b) :=
  by unfold prod_eq; unfold pair_eq'; rewrite ap₂_β

  definition eq_pr1 [reducible] (p : u ~ v) : u.1 ~ v.1 :=
  ap pr1 p

  definition eq_pr2 [reducible] (p : u ~ v) : u.2 ~ v.2 :=
  ap pr2 p

  namespace ops
    postfix `..1`:(max+1) := eq_pr1
    postfix `..2`:(max+1) := eq_pr2
  end ops

  open ops

  protected definition ap_pr1 (p : u ~ v) : ap pr1 p ~ p..1 := idp
  protected definition ap_pr2 (p : u ~ v) : ap pr2 p ~ p..2 := idp

  open fib_eq.ap

  definition pair_prod_eq (p : u.1 ~ v.1) (q : u.2 ~ v.2) :
    ((prod_eq p q)..1, (prod_eq p q)..2) ~ (p, q) :=
  by
    induction u; induction v; esimp at *;
    induction p using elim; induction q using elim;
    rewrite prod_eq_β'; repeat rewrite elim_β

  /- Transport -/

  definition prod_transport (p : a ~ a') (u : P a × Q a) :
    p ▹ u ~ (p ▹ u.1, p ▹ u.2) :=
  by induction p using elim; induction u; simp

end hprod
