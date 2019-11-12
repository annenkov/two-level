import data.fin algebra.monotone algebra.category
open function nat fin

definition fin_strict_order [instance] (n : ℕ) : strict_order (fin n)
  := strict_order.mk (λ i i', val i < val i')
                     (λ i, lt.irrefl (val i))
                     (λ a b c, lt.trans)

structure delta_plus (n m : ℕ) :=
  (f : fin (succ n) -> fin (succ m))
  (mon : strictly_increasing f)

attribute delta_plus.f [coercion]

definition id_delta_plus (n : ℕ) : delta_plus n n :=
  delta_plus.mk id strictly_increasing_id

definition comp_delta_plus (n m p : ℕ)
  (f : delta_plus m p)(g : delta_plus n m) : delta_plus n p :=
  delta_plus.mk (f ∘ g)
                (strictly_increasing_comp_inc_inc (delta_plus.mon f) (delta_plus.mon g))

definition eq_delta_plus {n m : ℕ}
  {f g : delta_plus n m} (q : Π (i : fin (succ n)), f i = g i) : @eq (delta_plus n m) f g :=
  begin cases f, cases g, esimp at *, congruence, apply funext, apply q end

definition delta_plus_cat : category ℕ :=
  ⦃ category,
  hom := delta_plus,
  comp := comp_delta_plus,
  ID := id_delta_plus,
  assoc := λ a b c d h g f, eq_delta_plus (λ i, rfl),
  id_right := λ a b f, eq_delta_plus (λ i, rfl),
  id_left := λ a b f, eq_delta_plus (λ i, rfl) ⦄

definition delta_plus_Cat : Category := category.Mk delta_plus_cat

notation `Δ+` := delta_plus_Cat
