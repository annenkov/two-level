import fibrant limit data.equiv

section pullback

universe variable u
variables {A B C : Type.{max 1 u}}
          (f : A → C) (g : B → C)
          {isfib : is_fibration_alt f}

definition Pullback : Type :=
  Σ (a : A) (b : B) (c : C), (f a = c) × (g b = c)

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt
  (λ (pb : Pullback' f g), pb.1)
  := λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))

inductive pullback_category_ob : Type :=
| TR : pullback_category_ob
| BL : pullback_category_ob
| BR : pullback_category_ob

open pullback_category_ob
inductive pullback_category_hom : pullback_category_ob → pullback_category_ob → Type :=
| f1 : pullback_category_hom TR BR
| f2 : pullback_category_hom BL BR

check @function.comp

open sum

definition no_comp_pullback_hom {a b c : pullback_category_ob}
  : pullback_category_hom a b → pullback_category_hom b c → false :=
  begin intros f g, cases g: cases f end

definition pullback_category : category pullback_category_ob :=
⦃ category,
  hom := λ a b, pullback_category_hom a b + (a = b),
  comp := λ a b c f g,
     begin
       cases f with [f₁, f₂]: cases g with [g₁, g₂],
       { apply inl, exfalso, apply no_comp_pullback_hom g₁ f₁},
       { apply inl, rewrite g₂, assumption},
       { apply inl, rewrite -f₂, assumption},
       { apply inr, rewrite -f₂, assumption}
     end,
  ID := λ a, inr rfl ,
  assoc := λ a b c d h g f,
    begin
    induction h with rh ph: induction g with rg pg: induction f with rf pf:
    try cases pg: try cases pf: esimp: exfalso: apply no_comp_pullback_hom _ _
    end,
  id_left := λ a b f, _,
  id_right := λ a b f, _⦄

end pullback
