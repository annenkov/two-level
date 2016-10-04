import ..fibrant

open prod prod.ops
open fib_eq

-- TODO: think about the namespace name
namespace hprod 

  variables {A: Type} [is_fibrant A]
  variables {B: Type} [is_fibrant B]
  variables {u v w : A × B} {a a' : A} {b b' : B}

  protected definition eta [unfold 3] (u : A × B) : (pr₁ u, pr₂ u) ~ u :=
  by cases u; apply idp

  definition pair_eq {a a' : A} {b b' : B} : (a ~ a') × (b ~ b') -> (a,b) ~ (a',b')
  | pair_eq (p, q) := ap₂ (λ x y, (x,y)) p q

  definition pair_eq' (pa : a ~ a') (pb : b ~ b') : (a, b) ~ (a', b') :=
  ap₂ (λ x y, (x,y)) pa pb
  
  definition prod_eq' (H₁ : u.1 ~ v.1) (H₂ : u.2 ~ v.2) : u ~ v :=
  by cases u; cases v; exact pair_eq' H₁ H₂

  definition prod_eq (p : pr₁ u ~ pr₁ v) (q : pr₂ u ~ pr₂ v) : u ~ v :=
  (prod.cases_on u (λ x y, prod.cases_on v (λ x1 y1, pair_eq'))) p q

  definition eq_pr1 [unfold 5] (p : u ~ v) : u.1 ~ v.1 :=
  ap pr1 p

  definition eq_pr2 [unfold 5] (p : u ~ v) : u.2 ~ v.2 :=
  ap pr2 p

  namespace ops
    postfix `..1`:(max+1) := eq_pr1
    postfix `..2`:(max+1) := eq_pr2
  end ops
  
  open ops

  protected definition ap_pr1 (p : u ~ v) : ap pr1 p ~ p..1 := idp
  protected definition ap_pr2 (p : u ~ v) : ap pr2 p ~ p..2 := idp

  -- FIXME: simplification needed before applying idp, because definitions of ap, prod_eq etc don't compute
  -- definition pair_prod_eq (p : u.1 ~ v.1) (q : u.2 ~ v.2) : ((prod_eq p q)..1, (prod_eq p q)..2) ~ (p, q) :=
  -- by induction u; induction v; esimp at *; induction p using elim; induction q using elim; state; apply idp
  
end hprod
