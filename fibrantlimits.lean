import fibrant limit data.equiv

section pullback

universe variable u
variables {A B C : Type.{max 1 u}}
          (f : A → C) (g : B → C)
          {isfib : is_fibration_alt f}

definition Pullback : Type :=
  Σ (a : A), Σ (b : B), Σ (c : C), (f a = c) × (g b = c)

definition Pullback' : Type := Σ (b : B), fibreₛ f (g b)

open sigma.ops
definition Pullback'_is_fibrant : is_fibration_alt
  (λ (pb : Pullback' f g), pb.1)
  := λ b, @equiv_is_fibrant _ _ (equiv.symm (fibre_projection b)) (isfib (g b))

end pullback
